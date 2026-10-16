'use strict';

// The pure half of the "Robot arm" test controller: everything that turns cargo and lake
// output into the tree the Test view shows, and a run request into a command line.
//
// Nothing here imports `vscode`, or touches the filesystem, so `node --test test/` drives
// all of it directly against fixtures captured from real runs of the same commands.

const path = require('path');

// ---------------------------------------------------------------------------------------
// cargo metadata: which packages and targets make up the workspace.
// ---------------------------------------------------------------------------------------

/**
 * Read what `cargo metadata --format-version 1 --no-deps` printed.
 *
 * `--no-deps` is what keeps this to the workspace's own members, which is exactly the set
 * of packages the tree offers. Only the fields the tree needs survive the translation:
 * the package name, the directory its manifest sits in -- needed to turn a target's
 * absolute source path back into the relative path cargo prints while listing tests -- and
 * its targets.
 */
function parseCargoMetadata(json) {
  const metadata = JSON.parse(json);
  return metadata.packages
    .map((pkg) => ({
      name: pkg.name,
      dir: path.dirname(pkg.manifest_path),
      targets: pkg.targets.map((target) => ({
        name: target.name,
        // `kind` is an array: `["lib"]`, `["bin"]`, `["test"]`, and for a library with
        // extra crate types something like `["cdylib", "rlib"]`. The first entry is the
        // one cargo names the target by, and the only one we ever see in `Running ...`.
        kind: target.kind[0],
        src: target.src_path,
      })),
    }))
    .sort((a, b) => a.name.localeCompare(b.name));
}

/**
 * Map the name a test binary carries back to the package that owns it.
 *
 * Cargo names a test binary after its target with dashes replaced by underscores and a
 * hash appended, so `robot_golden-ad605af848408b92.exe` is the `robot-golden` target of
 * the `robot-golden` package. That is the only way to tell which package a `Running ...`
 * line belongs to during a `cargo test --workspace` run, where several packages' output
 * arrives in one stream.
 */
function cratePackages(packages) {
  const index = new Map();
  for (const pkg of packages) {
    for (const target of pkg.targets) {
      index.set(underscored(target.name), pkg.name);
    }
  }
  return index;
}

/** The package a `Running unittests ... (target/debug/deps/<crate>-<hash>.exe)` line belongs to. */
function packageOfBinary(binary, crates) {
  const stem = path.basename(binary).replace(/\.exe$/i, '');
  const crate = stem.replace(/-[0-9a-f]{8,}$/, '');
  return crates.get(crate);
}

/**
 * The package a parsed section belongs to.
 *
 * A binary path names its crate; a `Doc-tests <crate>` header names it directly (and with
 * underscores, as the crate is spelled in Rust). Only needed when one command covers
 * several packages -- a `cargo test --workspace` run -- since a single package's run
 * already knows whose output it is reading.
 */
function packageOfSection(section, crates) {
  if (section.binary) return packageOfBinary(section.binary, crates);
  return crates.get(section.descriptor.replace(/^Doc-tests /, ''));
}

function underscored(name) {
  return name.replace(/-/g, '_');
}

// ---------------------------------------------------------------------------------------
// `cargo test -- --list`: which tests a package has.
// ---------------------------------------------------------------------------------------

// Cargo prints one of these before each test binary's listing, and the listing itself is
// one `<name>: test` line per test. `: bench` lines are listed too; benchmarks are not
// tests, are not run by `cargo test`, and so are dropped.
const RUNNING_BINARY = /^\s+Running (.+) \((.+)\)\s*$/;
const RUNNING_DOCTESTS = /^\s+Doc-tests (\S+)\s*$/;
const LISTED_TEST = /^(.+): test$/;

/**
 * Parse a `cargo test -p <pkg> -- --list` run into its targets and their test names.
 *
 * Targets with no tests are dropped: a `Doc-tests` section is printed even when it lists
 * nothing, and an empty target is not something the Test view should offer.
 */
function parseTestList(output) {
  const targets = [];
  let current = undefined;
  for (const line of output.split(/\r?\n/)) {
    const binary = RUNNING_BINARY.exec(line);
    if (binary) {
      current = { descriptor: binary[1], binary: binary[2], tests: [] };
      targets.push(current);
      continue;
    }
    const doctests = RUNNING_DOCTESTS.exec(line);
    if (doctests) {
      current = { descriptor: `Doc-tests ${doctests[1]}`, binary: undefined, tests: [] };
      targets.push(current);
      continue;
    }
    const listed = LISTED_TEST.exec(line);
    if (listed && current) current.tests.push(listed[1]);
  }
  return targets.filter((target) => target.tests.length > 0);
}

/**
 * The cargo selector for a target, so its tests can be run without running the rest of the
 * package's.
 *
 * The descriptor cargo prints names the source file -- `unittests src\lib.rs`,
 * `tests\exact_ring.rs` -- not the target, so it is matched against the source paths
 * `cargo metadata` reported. A descriptor that matches nothing (a layout cargo names in a
 * way we have not seen) yields no selector rather than a wrong one: a command without a
 * selector still runs the tests, it just runs all of the package's.
 */
function selectorFor(descriptor, pkg) {
  if (descriptor.startsWith('Doc-tests ')) return ['--doc'];
  const target = targetFor(descriptor, pkg);
  if (!target) return [];
  switch (target.kind) {
    case 'lib':
      return ['--lib'];
    case 'bin':
      return ['--bin', target.name];
    case 'test':
      return ['--test', target.name];
    case 'example':
      return ['--example', target.name];
    case 'bench':
      return ['--bench', target.name];
    default:
      return [];
  }
}

/** The descriptor's `tests\exact_ring.rs`, with separators normalised for comparison. */
function descriptorPath(descriptor) {
  return descriptor.replace(/^unittests /, '').replace(/\\/g, '/');
}

/**
 * The `cargo metadata` target a `Running ...` descriptor names.
 *
 * The descriptor gives the source file, not the target, so the two are matched on the
 * path relative to the package: `unittests src\lib.rs` is the lib target, `tests\x.rs` is
 * the integration test target whose source is that file.
 */
function targetFor(descriptor, pkg) {
  if (descriptor.startsWith('Doc-tests ')) return undefined;
  const relative = descriptorPath(descriptor);
  return pkg.targets.find((candidate) => relativeTo(pkg, candidate.src) === relative);
}

function relativeTo(pkg, sourcePath) {
  return path.relative(pkg.dir, sourcePath).replace(/\\/g, '/');
}

/** A target's label in the tree: `lib`, `bin robot-app`, `tests/exact_ring.rs`, `doc tests`. */
function targetLabel(descriptor) {
  if (descriptor.startsWith('Doc-tests ')) return 'doc tests';
  const relative = descriptorPath(descriptor);
  if (relative === 'src/lib.rs') return 'lib';
  if (relative === 'src/main.rs') return 'bin';
  const namedBin = /^src\/bin\/(.+)\.rs$/.exec(relative);
  if (namedBin) return `bin ${namedBin[1]}`;
  return relative;
}

/**
 * A stable key for a target, used to build test item ids. Derived from the selector, so it
 * is the same regardless of how cargo spelled the descriptor -- except for a target no
 * selector could be found for, which falls back to the descriptor itself.
 */
function targetKey(selector, descriptor) {
  if (selector.length === 0) return `target:${descriptor.replace(/\s+/g, '_')}`;
  return selector.map((part) => part.replace(/^--/, '')).join(':');
}

// ---------------------------------------------------------------------------------------
// Running: the command lines, and reading back what they said.
// ---------------------------------------------------------------------------------------

/**
 * `cargo test` for one package, target or test.
 *
 * `--no-fail-fast` is the one thing these commands add to what CI runs. CI wants the first
 * failure; the Test view wants every failure, and cargo otherwise stops after the first
 * target that fails and leaves the rest of the package unreported.
 */
function cargoTestArgv({ workspace, pkg, selector = [], filter, exact, noFailFast = true }) {
  const argv = ['cargo', 'test'];
  if (noFailFast) argv.push('--no-fail-fast');
  if (workspace) argv.push('--workspace');
  else if (pkg) argv.push('-p', pkg);
  argv.push(...selector);
  if (filter) argv.push(filter);
  if (exact) argv.push('--', '--exact');
  return argv;
}

/**
 * `cargo test [--workspace|-p <pkg>] -- --list`: compiles the test binaries that would run,
 * runs none of them. One command for the whole workspace lists every package's tests at
 * once, which is what a workspace-wide run does before it starts.
 */
function cargoListArgv({ pkg, workspace }) {
  const selection = workspace ? ['--workspace'] : ['-p', pkg];
  return ['cargo', 'test', ...selection, '--', '--list'];
}

/** `lake build [<library>]`, from `lean/`; without a library it builds the defaultTargets. */
function lakeBuildArgv(library) {
  return ['lake', 'build', ...(library ? [library] : [])];
}

/**
 * A shell line, with stderr merged into stdout.
 *
 * The merge is the point: cargo writes its `Running ...` headers to stderr and the tests'
 * own results to stdout, and the two have to arrive in the order they were written for a
 * result to be attributed to the target that produced it. Two separate pipes give no such
 * guarantee, so the redirection is done by the shell instead.
 *
 * Nothing passed today needs quoting -- package names, test names and selectors are all
 * shell-safe -- but an argument that did would otherwise silently split the line in two.
 */
function shellLine(argv) {
  return `${argv.map(quoteArg).join(' ')} 2>&1`;
}

function quoteArg(arg) {
  if (/^[A-Za-z0-9_@%+=:,.\/\\-]+$/.test(arg)) return arg;
  return `"${arg.replace(/"/g, '""')}"`;
}

// One result line per test, followed by a summary. `--report-time` appends a duration,
// which is ignored here rather than parsed.
const TEST_RESULT = /^test (.+?) \.\.\. (ok|FAILED|ignored)(?: .*)?$/;
const FAILURE_BLOCK = /^---- (.+) stdout ----$/;
// The block a failing test's captured output is dumped into ends at any of these: the
// `failures:` list, the `test result:` summary, the `error:` cargo prints afterwards, or
// the next block.
const BLOCK_END = /^(failures:|test result:|error:)/;
const PANIC_LOCATION = /panicked at (.+?):(\d+):(\d+):/;

/**
 * Parse one cargo test run: what each test did, and what it printed if it failed.
 *
 * A test's failure block is where libtest puts the captured output, including the panic
 * message and the `panicked at <file>:<line>:<col>` that makes the failure clickable.
 */
function parseTestRun(output) {
  const sections = [];
  let section = undefined;
  let block = undefined;
  for (const line of output.split(/\r?\n/)) {
    const binary = RUNNING_BINARY.exec(line);
    if (binary) {
      section = { descriptor: binary[1], binary: binary[2], tests: [] };
      sections.push(section);
      block = undefined;
      continue;
    }
    const doctests = RUNNING_DOCTESTS.exec(line);
    if (doctests) {
      section = { descriptor: `Doc-tests ${doctests[1]}`, binary: undefined, tests: [] };
      sections.push(section);
      block = undefined;
      continue;
    }
    const start = FAILURE_BLOCK.exec(line);
    if (start) {
      block = { name: start[1], lines: [] };
      if (section) {
        const test = section.tests.find((candidate) => candidate.name === block.name);
        if (test) test.block = block;
      }
      continue;
    }
    if (block) {
      if (BLOCK_END.test(line)) block = undefined;
      else block.lines.push(line);
      continue;
    }
    const result = TEST_RESULT.exec(line);
    if (result && section) {
      section.tests.push({
        name: result[1],
        status: result[2] === 'ok' ? 'passed' : result[2] === 'ignored' ? 'skipped' : 'failed',
      });
    }
  }
  return sections;
}

/** The block's text, with the blank padding libtest puts around it removed. */
function blockText(block) {
  if (!block) return '';
  return block.lines.join('\n').trim();
}

/** Where the test in a failure block panicked, as `{ file, line, column }` or undefined. */
function panicLocation(block) {
  if (!block) return undefined;
  const match = PANIC_LOCATION.exec(block.lines.join('\n'));
  if (!match) return undefined;
  return { file: match[1], line: Number(match[2]), column: Number(match[3]) };
}

/**
 * The compiler diagnostics in a failed build's output, as `{ message, file, line, column }`.
 *
 * Both spellings the commands here produce are read: rustc's `error[E0308]: ...` followed
 * by an indented `--> src\lib.rs:24:9`, and Lean's one-line
 * `Kinematics.lean:12:5: error: ...`. A diagnostic whose location does not parse is kept
 * without one rather than dropped -- the message is still the diagnosis.
 */
function parseDiagnostics(output) {
  const diagnostics = [];
  let pending = undefined;
  for (const line of output.split(/\r?\n/)) {
    // `Kinematics.lean:12:5: error: ...`, with or without lake's own `error: ` in front.
    const lean = /^(?:error: )?(.+?\.lean):(\d+):(\d+): (?:error|warning): (.+)$/.exec(line);
    if (lean) {
      diagnostics.push({
        message: lean[4],
        file: lean[1],
        line: Number(lean[2]),
        column: Number(lean[3]),
      });
      pending = undefined;
      continue;
    }
    const rust = /^(?:error|warning)(?:\[[A-Z0-9]+\])?: (.+)$/.exec(line);
    if (rust) {
      pending = { message: rust[1] };
      diagnostics.push(pending);
      continue;
    }
    const location = /^\s*-->\s+(.+?):(\d+):(\d+)\s*$/.exec(line);
    if (location && pending && pending.file === undefined) {
      pending.file = location[1];
      pending.line = Number(location[2]);
      pending.column = Number(location[3]);
      pending = undefined;
    }
  }
  return diagnostics;
}

// ---------------------------------------------------------------------------------------
// Lean and Rust sources: what the tree needs from files rather than from commands.
// ---------------------------------------------------------------------------------------

/**
 * The libraries `lake build` builds by default, read out of `lean/lakefile.toml`'s
 * `defaultTargets` rather than written down here, so adding a library to the lakefile adds
 * it to the tree. An unreadable list yields none, and the Lean node is then the one item.
 */
function parseDefaultTargets(toml) {
  const match = /^\s*defaultTargets\s*=\s*\[([^\]]*)\]/m.exec(toml);
  if (!match) return [];
  return match[1]
    .split(',')
    .map((entry) => entry.trim().replace(/^["']|["']$/g, ''))
    .filter(Boolean);
}

// `pub(crate) async unsafe fn name`, and the plain `fn name` the tests here use. The
// keyword is matched without anchoring to the line start so an indented method is found
// too; `fn` inside a string or comment is a false positive the caller tolerates, since the
// location is only ever used to place a gutter icon.
const FUNCTION = /(?:^|\s)(?:pub(?:\([^)]*\))?\s+)?(?:const\s+)?(?:async\s+)?(?:unsafe\s+)?(?:extern\s+"[^"]*"\s+)?fn\s+([A-Za-z_][A-Za-z0-9_]*)/;

/**
 * Index `<fn name> -> { path, line, column }` across the given sources, so a test item can
 * carry a file and a range.
 *
 * A test listing gives names only, and VS Code draws its gutter run button solely for
 * items that have both a uri and a range. This is a heuristic -- a name defined twice
 * resolves to its first definition -- but it is only ever a location: the test that runs
 * is still chosen by the name cargo printed, never by where the icon is.
 */
function indexFunctions(sources) {
  const index = new Map();
  for (const source of sources) {
    const lines = source.text.split(/\r?\n/);
    for (let i = 0; i < lines.length; i += 1) {
      const match = FUNCTION.exec(lines[i]);
      if (match && !index.has(match[1])) {
        // The match ends with the name, so this is where the name starts rather than where
        // the line does -- the gutter icon and "go to test" both want the function itself.
        const column = match.index + match[0].length - match[1].length + 1;
        index.set(match[1], { path: source.path, line: i + 1, column });
      }
    }
  }
  return index;
}

module.exports = {
  parseCargoMetadata,
  cratePackages,
  packageOfBinary,
  packageOfSection,
  parseTestList,
  selectorFor,
  targetFor,
  targetLabel,
  targetKey,
  cargoTestArgv,
  cargoListArgv,
  lakeBuildArgv,
  shellLine,
  parseTestRun,
  blockText,
  panicLocation,
  parseDiagnostics,
  parseDefaultTargets,
  indexFunctions,
};
