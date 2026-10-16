'use strict';

// The "Robot arm" test controller: the repository's validations in VS Code's Test view.
//
// The Python suites are not here -- the Python extension already contributes those items,
// and VS Code's "Run All Tests" spans controllers, so one click covers both. What this adds
// is everything else `ci.yml` runs: `cargo test --workspace`, `lake build` over the proofs,
// `cargo xtask check-golden` for the generated ground truth, and the fmt / clippy / no_std
// checks.
//
// It lives in `.vscode/extensions` because that is the only route to the Test view for
// commands no extension provides one for: VS Code cannot be told about a test declaratively,
// and no Rust or Lean extension is needed for this to work. Every command it runs is one
// from `.github/workflows/ci.yml`, with a single addition (`--no-fail-fast`) noted where the
// command is built.
//
// `plan.js` holds the parsing, the command lines and the tree's shape, and knows nothing
// about VS Code; this file is the wiring -- items, lazy discovery, spawning, reporting.

const fs = require('fs');
const path = require('path');
const { spawn, spawnSync } = require('child_process');
const vscode = require('vscode');
const plan = require('./plan');

const CONTROLLER_ID = 'robot-arm-validations';
const CONTROLLER_LABEL = 'Robot arm';

// Selecting individual tests runs one command per test, which is what makes a single click
// in the gutter report that test alone. Past this many in one target the commands stop
// being worth their overhead and the whole target runs instead -- results are attributed
// per test from its output either way.
const SINGLE_TEST_LIMIT = 8;

// The CI steps that check rather than test. Each is one item that passes or fails as a
// whole; leaving them out would leave the repository's definition of "valid" half-visible.
// Delete an entry to drop it from the Test view.
const CHECKS = [
  {
    id: 'fmt',
    label: 'cargo fmt --all --check',
    argv: ['cargo', 'fmt', '--all', '--check'],
  },
  {
    id: 'clippy',
    label: 'cargo clippy --workspace --all-targets -- -D warnings',
    argv: ['cargo', 'clippy', '--workspace', '--all-targets', '--', '-D', 'warnings'],
  },
  {
    id: 'no-std',
    label: 'cargo build -p robot-kinematics --no-default-features --features libm',
    argv: [
      'cargo',
      'build',
      '-p',
      'robot-kinematics',
      '--no-default-features',
      '--features',
      'libm',
    ],
  },
];

const GOLDEN = {
  id: 'golden',
  label: 'Ground truth',
  description: 'cargo xtask check-golden',
  argv: ['cargo', 'xtask', 'check-golden'],
};

let controller;
/** The repository root: the workspace folder holding Cargo.toml. */
let root;
/** The four top-level items, rebuilt whenever the tree is. */
let roots;
/** `{ packages, crates }` from `cargo metadata`, read once per tree. */
let workspace;
/** Discovered packages by name: `{ pkg, item, targets: Map, resolved }`. */
let discovered;
/** What each item is, so nothing ever has to parse an id back into meaning. */
const context = new WeakMap();

function activate(extensionContext) {
  root = repositoryRoot();
  // No workspace folder, or one without a Cargo.toml: nothing to offer, and a controller
  // would only add an empty heading to the Test view.
  if (!root) return;

  controller = vscode.tests.createTestController(CONTROLLER_ID, CONTROLLER_LABEL);
  extensionContext.subscriptions.push(controller);
  controller.resolveHandler = resolve;
  controller.refreshHandler = () => buildTree();
  extensionContext.subscriptions.push(
    controller.createRunProfile('Run', vscode.TestRunProfileKind.Run, runRequest, true),
  );

  buildTree();
}

function repositoryRoot() {
  const candidates = (vscode.workspace.workspaceFolders ?? []).map((folder) => folder.uri.fsPath);
  // Opened as a subfolder or a loose file: fall back to where this extension sits, which is
  // three levels below the root (`.vscode/extensions/<name>/`).
  candidates.push(path.resolve(__dirname, '..', '..', '..'));
  return candidates.find((candidate) => fs.existsSync(path.join(candidate, 'Cargo.toml')));
}

// ---------------------------------------------------------------------------------------
// The tree
// ---------------------------------------------------------------------------------------

/**
 * The four roots: the Rust workspace, the Lean proofs, the ground truth, and the checks.
 *
 * Only the Rust half needs a command to discover, so only it is resolved lazily -- the Lean
 * libraries come from the lakefile and the checks are the constant above.
 */
function buildTree() {
  discovered = new Map();
  // The user pressing refresh is asking for the workspace to be re-read, so the cached
  // metadata goes with the tree.
  workspace = undefined;

  const rust = controller.createTestItem('rust', 'Rust tests');
  rust.description = 'cargo test --workspace';
  rust.canResolveChildren = true;
  context.set(rust, { kind: 'rust' });

  const lean = controller.createTestItem('lean', 'Lean proofs');
  lean.description = 'lake build';
  context.set(lean, { kind: 'lean' });
  for (const library of leanLibraries()) {
    const file = path.join(root, 'lean', `${library}.lean`);
    const item = controller.createTestItem(
      `lean:${library}`,
      library,
      fs.existsSync(file) ? vscode.Uri.file(file) : undefined,
    );
    item.description = `lake build ${library}`;
    context.set(item, { kind: 'leanLib', library });
    lean.children.add(item);
  }

  const golden = controller.createTestItem(GOLDEN.id, GOLDEN.label);
  golden.description = GOLDEN.description;
  context.set(golden, { kind: 'golden' });

  const checks = controller.createTestItem('checks', 'Repository checks');
  checks.description = 'the CI steps that are not test suites';
  context.set(checks, { kind: 'checks' });
  for (const check of CHECKS) {
    const item = controller.createTestItem(`checks:${check.id}`, check.label);
    context.set(item, { kind: 'check', check });
    checks.children.add(item);
  }

  roots = { rust, lean, golden, checks };
  controller.items.replace([rust, lean, golden, checks]);
}

/** `defaultTargets` from `lean/lakefile.toml`, so a new library appears without this file changing. */
function leanLibraries() {
  try {
    return plan.parseDefaultTargets(fs.readFileSync(path.join(root, 'lean', 'lakefile.toml'), 'utf8'));
  } catch {
    return [];
  }
}

function resolve(item) {
  if (!item) return undefined;
  const data = context.get(item);
  if (data?.kind === 'rust') return resolvePackages(item);
  if (data?.kind === 'package') return resolvePackage(data.entry);
  return undefined;
}

/** Create an item per workspace member. `cargo metadata` only -- nothing is compiled yet. */
async function resolvePackages(rustItem) {
  rustItem.busy = true;
  try {
    let packages;
    try {
      ({ packages } = await loadMetadata());
    } catch (error) {
      // Only the metadata load is the metadata's failure. The loop below builds items, and
      // one of *those* failing was reported as "cargo metadata failed" too -- which is how a
      // read-only `uri` assignment in it went looking like a cargo problem.
      rustItem.error = `cargo metadata failed: ${error.message}`;
      return;
    }
    if (packages.length === 0) rustItem.error = 'cargo metadata reported no packages';
    for (const pkg of packages) {
      if (discovered.has(pkg.name)) continue;
      // `uri` is read-only on a `TestItem` (`vscode.d.ts`, and the host enforces it), so it
      // is handed to `createTestItem` rather than assigned afterwards.
      const item = controller.createTestItem(
        `rust:${pkg.name}`,
        pkg.name,
        vscode.Uri.file(pkg.dir),
      );
      item.description = path.relative(root, pkg.dir).split(path.sep).join('/');
      item.canResolveChildren = true;
      const entry = { pkg, item, targets: new Map(), resolved: false };
      context.set(item, { kind: 'package', entry });
      rustItem.children.add(item);
      discovered.set(pkg.name, entry);
    }
  } catch (error) {
    rustItem.error = `cargo metadata failed: ${error.message}`;
  } finally {
    rustItem.busy = false;
  }
}

/**
 * Discover a package's tests by listing them.
 *
 * `cargo test -- --list` compiles the package's test binaries and prints their tests
 * without running any, which is the cost of the tree and the reason packages are only
 * listed when something asks: expanding one, or starting a run that covers them.
 */
async function resolvePackage(entry) {
  if (entry.resolved) return;
  entry.resolved = true;
  entry.item.busy = true;
  try {
    const { code, output } = await capture(plan.cargoListArgv({ pkg: entry.pkg.name }), root);
    applyListing(entry, code, output);
  } finally {
    entry.item.busy = false;
  }
}

/** Turn one package's `--list` run into its children. */
function applyListing(entry, code, output) {
  if (code !== 0) {
    const [diagnostic] = plan.parseDiagnostics(output);
    entry.item.error = diagnostic ? diagnostic.message : `cargo test --list exited with ${code}`;
    entry.item.canResolveChildren = false;
    return false;
  }
  applySections(entry, plan.parseTestList(output));
  entry.item.canResolveChildren = false;
  return true;
}

/** Create a package's target and test items from the sections cargo listed for it. */
function applySections(entry, sections) {
  for (const section of sections) {
    const key = keyOf(entry, section.descriptor);
    if (entry.targets.has(key)) continue;
    const source = plan.targetFor(section.descriptor, entry.pkg);
    const targetItem = controller.createTestItem(
      `rust:${entry.pkg.name}:${key}`,
      plan.targetLabel(section.descriptor),
      source ? vscode.Uri.file(source.src) : undefined,
    );
    const selector = plan.selectorFor(section.descriptor, entry.pkg);
    if (selector.length > 0) targetItem.description = selector.join(' ');
    context.set(targetItem, { kind: 'target', entry, key });

    const locations = functionLocations(entry.pkg, section.descriptor);
    const tests = new Map();
    for (const name of section.tests) {
      // The gutter run button needs a uri and a range, and a listing gives names only. The
      // source scan below supplies both; a doctest has no `fn` to find and so no icon.
      // `uri` is read-only and goes to `createTestItem`; `range` is not, and a position
      // needs the uri's file to exist first, so it is set once the item is there.
      const location = locations.get(shortName(name));
      const item = controller.createTestItem(
        `rust:${entry.pkg.name}:${key}:${name}`,
        name,
        location ? vscode.Uri.file(location.path) : undefined,
      );
      if (location) {
        const position = new vscode.Position(location.line - 1, location.column - 1);
        item.range = new vscode.Range(position, position);
      }
      context.set(item, { kind: 'test', entry, key, name });
      targetItem.children.add(item);
      tests.set(name, item);
    }
    entry.item.children.add(targetItem);
    entry.targets.set(key, { item: targetItem, tests });
  }
}

/** The target key a descriptor maps to: unique per package, and stable across runs. */
function keyOf(entry, descriptor) {
  return plan.targetKey(plan.selectorFor(descriptor, entry.pkg), descriptor);
}

/** A test name's last `::` segment: what the `fn` in the sources is called. */
function shortName(name) {
  const parts = name.split('::');
  return parts[parts.length - 1];
}

/**
 * Where each of a target's test functions is, so items can carry a range.
 *
 * A library target is scanned across the whole of its `src/`, since a `#[cfg(test)] mod
 * tests` can sit in any module of it; a bin or an integration test is the single file it is.
 */
function functionLocations(pkg, descriptor) {
  const target = plan.targetFor(descriptor, pkg);
  if (!target) return new Map();
  const files = target.kind === 'lib' ? rustSources(path.dirname(target.src)) : [target.src];
  const sources = [];
  for (const file of files) {
    try {
      sources.push({ path: file, text: fs.readFileSync(file, 'utf8') });
    } catch {
      // A source that cannot be read costs a location, not the test.
    }
  }
  return plan.indexFunctions(sources);
}

function rustSources(dir) {
  const files = [];
  let entries;
  try {
    entries = fs.readdirSync(dir, { withFileTypes: true });
  } catch {
    return files;
  }
  for (const entry of entries) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) files.push(...rustSources(full));
    else if (entry.name.endsWith('.rs')) files.push(full);
  }
  return files;
}

function loadMetadata() {
  if (!workspace) {
    workspace = capture(['cargo', 'metadata', '--format-version', '1', '--no-deps'], root, {
      merge: false,
    }).then(({ code, output, errors }) => {
      if (code !== 0) throw new Error(`cargo metadata exited with ${code}: ${errors.trim()}`);
      const packages = plan.parseCargoMetadata(output);
      return { packages, crates: plan.cratePackages(packages) };
    });
  }
  return workspace;
}

// ---------------------------------------------------------------------------------------
// Running
// ---------------------------------------------------------------------------------------

/**
 * Work out what the request asks for, make sure the items it names exist, then run the
 * commands one at a time.
 *
 * Sequential on purpose: every command builds in the same target directory, and cargo
 * serialises them behind a lock anyway -- one at a time simply makes the Test Results pane
 * readable while that happens.
 */
async function runRequest(request, token) {
  const run = controller.createTestRun(request);
  try {
    const commands = await planWork(request);
    for (const command of commands) {
      if (token.isCancellationRequested) break;
      await execute(command, run, token);
    }
  } catch (error) {
    vscode.window.showErrorMessage(`Robot arm validations: ${error.message}`);
  } finally {
    // Whatever happened, the run has to end: a run that never ends leaves the Test Results
    // view stuck on "running".
    run.end();
  }
}

/**
 * Every command the request needs, in the order the tree reads.
 *
 * The selection is gathered from the items the request includes (an absent `include` means
 * all of them), with exclusions subtracted. A listing command is put in front of the tests
 * that need it, so a package that has not been discovered yet is discovered as part of the
 * run -- its tests can then be attributed individually, and the compile listing costs is
 * visible in the output rather than hidden behind a spinner.
 */
async function planWork(request) {
  const excluded = excludedIds(request.exclude ?? []);
  const selection = {
    rustAll: false,
    packages: new Map(),
    leanAll: false,
    leanLibs: new Set(),
    golden: false,
    checks: new Set(),
  };
  for (const item of request.include ?? Object.values(roots)) {
    collect(item, excluded, selection);
  }

  const commands = [];

  if (selection.rustAll) {
    // Every member, so their tests have items to be reported against; then the one command
    // CI runs, preceded by a listing if any of them is still undiscovered.
    await resolvePackages(roots.rust);
    const entries = [...discovered.values()];
    const unresolved = entries.filter((entry) => !entry.resolved);
    if (unresolved.length > 0) {
      commands.push({
        kind: 'listing',
        argv: plan.cargoListArgv({ workspace: true }),
        item: roots.rust,
        entries: unresolved,
      });
    }
    commands.push({
      kind: 'cargo',
      argv: plan.cargoTestArgv({ workspace: true }),
      item: roots.rust,
      entries,
    });
  } else {
    for (const [name, wanted] of selection.packages) {
      const entry = discovered.get(name);
      // A package whose item exists but whose listing never ran: `cargo metadata` listed no
      // such member, which only happens if the workspace changed under the tree.
      if (!entry) continue;
      if (!entry.resolved) {
        commands.push({
          kind: 'listing',
          argv: plan.cargoListArgv({ pkg: name }),
          item: entry.item,
          entry,
        });
      }
      commands.push(...packageCommands(entry, wanted));
    }
  }

  if (selection.leanAll) {
    commands.push({
      kind: 'lean',
      argv: plan.lakeBuildArgv(),
      cwd: path.join(root, 'lean'),
      item: roots.lean,
    });
  } else {
    for (const library of selection.leanLibs) {
      commands.push({
        kind: 'lean',
        argv: plan.lakeBuildArgv(library),
        cwd: path.join(root, 'lean'),
        item: roots.lean.children.get(`lean:${library}`),
      });
    }
  }

  if (selection.golden) {
    commands.push({ kind: 'check', argv: GOLDEN.argv, item: roots.golden });
  }
  for (const id of selection.checks) {
    const check = CHECKS.find((candidate) => candidate.id === id);
    if (check) {
      commands.push({ kind: 'check', argv: check.argv, item: roots.checks.children.get(`checks:${id}`) });
    }
  }

  return commands;
}

/** The commands for one package: the whole package, whole targets, or single tests. */
function packageCommands(entry, wanted) {
  const nothingSingledOut = wanted.targets.size === 0 && wanted.tests.size === 0;
  if (wanted.all || nothingSingledOut) {
    return [
      { kind: 'cargo', argv: plan.cargoTestArgv({ pkg: entry.pkg.name }), item: entry.item, entries: [entry] },
    ];
  }

  const commands = [];
  const covered = new Set(wanted.targets);
  for (const key of wanted.targets) commands.push(targetCommand(entry, key));
  for (const [key, names] of wanted.tests) {
    if (covered.has(key)) continue;
    const target = entry.targets.get(key);
    // A doctest cannot be filtered by name -- libtest prints the doctest's whole source path
    // with a `(line N)` suffix, which neither `--exact` nor a substring filter matches
    // reliably -- so the target runs whole and its results are attributed by name instead.
    const wholeTarget =
      key === 'doc' ||
      names.size > SINGLE_TEST_LIMIT ||
      (target && names.size === target.tests.size);
    if (wholeTarget) {
      commands.push(targetCommand(entry, key));
      continue;
    }
    for (const name of names) {
      commands.push({
        kind: 'cargo',
        argv: plan.cargoTestArgv({
          pkg: entry.pkg.name,
          selector: plan.selectorFor(target.descriptor, entry.pkg),
          filter: name,
          exact: true,
        }),
        item: target.tests.get(name),
        entries: [entry],
        only: new Map([[key, new Set([name])]]),
      });
    }
  }
  return commands;
}

/** The command that runs one target of a package, whole. */
function targetCommand(entry, key) {
  const target = entry.targets.get(key);
  return {
    kind: 'cargo',
    argv: plan.cargoTestArgv({
      pkg: entry.pkg.name,
      selector: plan.selectorFor(target.descriptor, entry.pkg),
    }),
    item: target.item,
    entries: [entry],
    only: new Map([[key, new Set(target.tests.keys())]]),
  };
}

/**
 * Run one command, streaming its output into the run and reporting what it said.
 *
 * Test lines are used twice: as they arrive they mark the test as started, which keeps the
 * tree's spinners honest during a long run, and at the end the whole output is parsed so
 * that each result carries its status, its failure block and the location it panicked at.
 */
async function execute(command, run, token) {
  run.started(command.item);
  const items = new Map();
  for (const entry of command.entries ?? [command.entry].filter(Boolean)) {
    for (const target of entry.targets.values()) {
      for (const [name, item] of target.tests) items.set(`${entry.pkg.name}\u0000${name}`, item);
    }
  }
  const onLine = (line) => {
    const result = /^test (.+?) \.\.\. (ok|FAILED|ignored)(?: .*)?$/.exec(line);
    if (!result) return;
    for (const entry of command.entries ?? []) {
      const item = items.get(`${entry.pkg.name}\u0000${result[1]}`);
      if (item) run.started(item);
    }
  };

  const { code, output } = await runCommand(command, run, token, onLine);
  await report(command, run, code, output);
  run.appendOutput('\r\n');
}

async function report(command, run, code, output) {
  if (command.kind === 'listing') return reportListing(command, run, code, output);
  if (command.kind === 'cargo') return reportTests(command, run, code, output);
  return reportCommand(command, run, code, output);
}

/** Apply a listing's sections to the tree: per package, or one section per package at once. */
async function reportListing(command, run, code, output) {
  const diagnostics = plan.parseDiagnostics(output);
  const sections = plan.parseTestList(output);
  const { crates } = await loadMetadata();
  const entries = command.entries ?? [command.entry];
  for (const entry of entries) entry.resolved = true;
  if (entries.length === 1 && !command.entries) {
    applyListing(entries[0], code, output);
    return;
  }
  for (const entry of entries) {
    applySections(
      entry,
      sections.filter((section) => plan.packageOfSection(section, crates) === entry.pkg.name),
    );
  }
  if (code !== 0) {
    roots.rust.error = diagnostics[0]?.message ?? `cargo test --list exited with ${code}`;
  }
}

/**
 * Report a test run: every result the output carried, then everything that was asked for
 * and never appeared.
 *
 * A package that fails to build produces no test lines at all, and "nothing happened" is
 * the least useful thing to show for it -- so the items that were asked for are marked with
 * the diagnostic that explains why, which is also what puts the compiler's file and line
 * into the Test Results pane.
 */
async function reportTests(command, run, code, output) {
  const diagnostics = plan.parseDiagnostics(output);
  const { crates } = await loadMetadata();
  const entries = command.entries ?? [];
  const cwd = command.cwd ?? root;
  const answered = new Set();
  // Packages whose test binaries produced a section. Cargo prints one for a target even
  // when the target has no tests in it, so this says "this package built and its harness
  // ran", which is the whole of what can be said about a package with no tests.
  const ran = new Set();

  for (const section of plan.parseTestRun(output)) {
    const entry =
      entries.length === 1
        ? entries[0]
        : discovered.get(plan.packageOfSection(section, crates) ?? '');
    if (!entry) continue;
    ran.add(entry.pkg.name);
    const key = keyOf(entry, section.descriptor);
    const target = entry.targets.get(key);
    if (!target) continue;
    for (const test of section.tests) {
      const item = target.tests.get(test.name);
      if (!item || !allowed(command, key, test.name)) continue;
      answered.add(item.id);
      result(run, item, test, cwd);
    }
  }

  for (const entry of entries) {
    for (const [key, target] of entry.targets) {
      for (const [name, item] of target.tests) {
        if (answered.has(item.id) || !allowed(command, key, name)) continue;
        run.errored(item, message(command, diagnostics, `no result for ${name}`));
      }
    }
    // A package with no tests has no item to carry a verdict, and its share of the command's
    // exit code says nothing: `cargo test --workspace` fails for any package's failure, so
    // taking the code at face value reports every testless package as broken whenever one
    // test anywhere fails. Whether its own harness ran is the honest question.
    if (entry.targets.size === 0 && !answered.has(entry.item.id)) {
      answered.add(entry.item.id);
      if (code === 0 || ran.has(entry.pkg.name)) run.passed(entry.item);
      else run.errored(entry.item, message(command, diagnostics, `exited with ${code}`));
    }
  }
}

/** One test's verdict, with the failure block and panic location libtest printed for it. */
function result(run, item, test, cwd) {
  if (test.status === 'passed') {
    run.passed(item);
    return;
  }
  if (test.status === 'skipped') {
    run.skipped(item);
    return;
  }
  const text = new vscode.TestMessage(plan.blockText(test.block) || `failed: ${test.name}`);
  const location = plan.panicLocation(test.block);
  if (location) {
    const resolved = existingFile(location.file, cwd);
    if (resolved) {
      text.location = new vscode.Location(
        vscode.Uri.file(resolved),
        new vscode.Position(location.line - 1, location.column - 1),
      );
    }
  }
  run.failed(item, text);
}

/** Lean and the checks are a single verdict each. */
function reportCommand(command, run, code, output) {
  const diagnostics = plan.parseDiagnostics(output);
  if (code === 0) run.passed(command.item);
  else run.failed(command.item, message(command, diagnostics, `exited with ${code}`));
}

/**
 * Whether a result belongs to what this command was asked for: a command with an `only` map
 * covers the tests it names, and one without covers every discovered test of its packages.
 */
function allowed(command, key, name) {
  if (command.only === undefined) return true;
  return command.only.get(key)?.has(name) ?? false;
}

function message(command, diagnostics, fallback) {
  const cwd = command.cwd ?? root;
  const diagnostic = diagnostics.find((candidate) => existingFile(candidate.file, cwd)) ?? diagnostics[0];
  if (!diagnostic) return new vscode.TestMessage(fallback);
  const text = new vscode.TestMessage(diagnostic.message);
  const resolved = existingFile(diagnostic.file, cwd);
  if (resolved) {
    text.location = new vscode.Location(
      vscode.Uri.file(resolved),
      new vscode.Position((diagnostic.line ?? 1) - 1, (diagnostic.column ?? 1) - 1),
    );
  }
  return text;
}

/**
 * A diagnostic's file as an absolute path, or undefined if it is not a file.
 *
 * Diagnostics print paths relative to the directory the command ran in, and some point into
 * the toolchain rather than the workspace (`/rustc/<hash>/library/core/...`). A location
 * that cannot be opened is worse than no location, so those are dropped.
 */
function existingFile(file, cwd) {
  if (!file) return undefined;
  const candidate = path.isAbsolute(file) ? file : path.join(cwd, file);
  return fs.existsSync(candidate) ? candidate : undefined;
}

/**
 * Spawn one command and collect its output.
 *
 * The line is run through a shell for the `2>&1` that `plan.shellLine` appends: cargo's
 * `Running ...` headers go to stderr and the tests' results to stdout, and the two have to
 * be read in the order they were written or results get attributed to the wrong target.
 */
function runCommand(command, run, token, onLine) {
  const line = plan.shellLine(command.argv);
  run.appendOutput(`$ ${line}\r\n`, undefined, command.item);
  return new Promise((resolve) => {
    const child = spawn(line, { cwd: command.cwd ?? root, shell: true, windowsHide: true });
    let pending = '';
    let output = '';
    const push = (chunk) => {
      pending += chunk;
      const lines = pending.split(/\r?\n/);
      pending = lines.pop();
      for (const text of lines) {
        output += `${text}\n`;
        run.appendOutput(`${text}\r\n`);
        onLine(text);
      }
    };
    child.stdout.on('data', (chunk) => push(String(chunk)));
    // Nothing is expected here -- the shell merged stderr into stdout -- but a shell that
    // did not honour the redirection should cost output, not the run.
    child.stderr.on('data', (chunk) => push(String(chunk)));

    const cancel = token.onCancellationRequested(() => {
      run.appendOutput('cancelled\r\n');
      kill(child);
    });
    child.on('error', (error) => {
      cancel.dispose();
      output += `${error.message}\n`;
      run.appendOutput(`${error.message}\r\n`);
      resolve({ code: -1, output });
    });
    child.on('close', (code) => {
      cancel.dispose();
      if (pending.length > 0) push('\n');
      resolve({ code: code ?? -1, output });
    });
  });
}

/** Stop a command and whatever it started: on Windows the shell is the only pid there is. */
function kill(child) {
  if (child.exitCode !== null || child.pid === undefined) return;
  if (process.platform === 'win32') {
    spawnSync('taskkill', ['/pid', String(child.pid), '/T', '/F'], { windowsHide: true });
  } else {
    child.kill('SIGTERM');
  }
}

/**
 * Run a command and read all of its output, for the short commands that are not a run.
 *
 * `merge` follows the same reasoning as `plan.shellLine`: a listing has to be read in order,
 * because a test line belongs to the `Running ...` header above it. `cargo metadata` is the
 * exception -- its stdout is JSON, and a warning cargo printed to stderr must not land in
 * the middle of it -- so that one is read with the streams kept apart.
 */
function capture(argv, cwd, { merge = true } = {}) {
  return new Promise((resolve) => {
    const child = merge
      ? spawn(plan.shellLine(argv), { cwd, shell: true, windowsHide: true })
      : spawn(argv[0], argv.slice(1), { cwd, windowsHide: true });
    let output = '';
    let errors = '';
    child.stdout.on('data', (chunk) => {
      output += String(chunk);
    });
    child.stderr.on('data', (chunk) => {
      if (merge) output += String(chunk);
      else errors += String(chunk);
    });
    child.on('error', (error) => resolve({ code: -1, output: `${output}${error.message}`, errors }));
    child.on('close', (code) => resolve({ code: code ?? -1, output, errors }));
  });
}

// ---------------------------------------------------------------------------------------
// Reading the request
// ---------------------------------------------------------------------------------------

/** The ids of every excluded item, and of everything under it. */
function excludedIds(excluded) {
  const ids = new Set();
  const walk = (item) => {
    ids.add(item.id);
    for (const [, child] of item.children) walk(child);
  };
  for (const item of excluded) walk(item);
  return ids;
}

/** Fold one selected item, and everything under it, into what has to be run. */
function collect(item, excluded, selection) {
  if (excluded.has(item.id)) return;
  const data = context.get(item);
  switch (data?.kind) {
    case 'rust':
      selection.rustAll = true;
      break;
    case 'package':
      wantedPackage(selection, data.entry.pkg.name).all = true;
      break;
    case 'target':
      wantedPackage(selection, data.entry.pkg.name).targets.add(data.key);
      break;
    case 'test': {
      const wanted = wantedPackage(selection, data.entry.pkg.name);
      const names = wanted.tests.get(data.key) ?? new Set();
      names.add(data.name);
      wanted.tests.set(data.key, names);
      break;
    }
    case 'lean':
      selection.leanAll = true;
      break;
    case 'leanLib':
      selection.leanLibs.add(data.library);
      break;
    case 'golden':
      selection.golden = true;
      break;
    case 'check':
      selection.checks.add(data.check.id);
      break;
    default:
      break;
  }
  for (const [, child] of item.children) collect(child, excluded, selection);
}

function wantedPackage(selection, name) {
  if (!selection.packages.has(name)) {
    selection.packages.set(name, { all: false, targets: new Set(), tests: new Map() });
  }
  return selection.packages.get(name);
}

module.exports = { activate };
