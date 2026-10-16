'use strict';

// Tests for `plan.js`, the half of the extension that imports nothing from VS Code.
//
// Most of what is checked here is checked against `fixtures/`, which holds real output from
// the commands concerned -- captured from this workspace where a command is this
// repository's, and from a throwaway crate where the point is a failure. Two cases have no
// real sample to capture and say so where they appear.
//
//   node --test .vscode/extensions/robot-arm-validations/test

const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const test = require('node:test');

const plan = require('../plan.js');

const fixture = (name) => fs.readFileSync(path.join(__dirname, 'fixtures', name), 'utf8');
const repository = path.resolve(__dirname, '..', '..', '..', '..');

const packages = plan.parseCargoMetadata(fixture('cargo-metadata.json'));
const crates = plan.cratePackages(packages);
const kinematics = packages.find((pkg) => pkg.name === 'robot-kinematics');

test('cargo metadata becomes the workspace members, in name order', () => {
  assert.deepEqual(
    packages.map((pkg) => pkg.name),
    ['robot-app', 'robot-dynamics', 'robot-golden', 'robot-kinematics', 'robot-model', 'xtask'],
  );
  // Every target carries the three fields the tree uses: what cargo calls it, what kind it
  // is, and where its source is (the last of which is how a `Running ...` descriptor is
  // matched back to it).
  assert.deepEqual(
    kinematics.targets.map((target) => `${target.kind}:${target.name}`),
    [
      'lib:robot_kinematics',
      'test:exact_ring',
      'test:lean_branch_plans',
      'test:lean_ground_truth',
      'test:python_compat',
      'test:theorem_completeness',
      'test:theorem_coverage',
      'test:theorem_soundness',
    ],
  );
  assert.ok(path.isAbsolute(kinematics.dir));
});

test('a test binary names its package, however cargo spelled the crate', () => {
  // Windows writes the path with backslashes; the hash is the part that has to be dropped.
  assert.equal(
    plan.packageOfBinary('target\\debug\\deps\\robot_golden-ad605af848408b92.exe', crates),
    'robot-golden',
  );
  assert.equal(plan.packageOfBinary('target/debug/deps/exact_ring-9f1c2b3d4e5f6071', crates), 'robot-kinematics');
  assert.equal(plan.packageOfBinary('target/debug/deps/nothing-0123456789abcdef.exe', crates), undefined);
  // A doctest section carries no binary at all, only the crate name.
  assert.equal(plan.packageOfSection({ descriptor: 'Doc-tests robot_kinematics' }, crates), 'robot-kinematics');
});

test('a listing becomes targets and their tests, with empty targets dropped', () => {
  const targets = plan.parseTestList(fixture('cargo-test-list.txt'));
  // `cargo test --list` prints a Doc-tests section even when it lists nothing, and an empty
  // target is not worth a node in the tree.
  assert.deepEqual(targets.map((target) => target.descriptor), ['unittests src\\lib.rs']);
  assert.equal(targets[0].tests.length, 9);
  assert.ok(targets[0].tests.includes('rational::tests::from_f64_is_exact'));
  assert.match(targets[0].binary, /robot_golden-[0-9a-f]+\.exe$/);
});

test('a doctest is listed under its own section, with the name libtest prints', () => {
  const targets = plan.parseTestList(fixture('cargo-test-list-scratch.txt'));
  assert.deepEqual(targets.map((target) => target.descriptor), [
    'unittests src\\lib.rs',
    'Doc-tests fixture_crate',
  ]);
  // The name is the doctest's source path, not a Rust path: nothing can filter on this
  // reliably, which is why selecting one runs the target whole.
  assert.deepEqual(targets[1].tests, ['src\\lib.rs - add_one (line 6)']);
});

test('a descriptor maps to the cargo selector for its target', () => {
  assert.deepEqual(plan.selectorFor('unittests src\\lib.rs', kinematics), ['--lib']);
  assert.deepEqual(plan.selectorFor('tests\\exact_ring.rs', kinematics), ['--test', 'exact_ring']);
  assert.deepEqual(plan.selectorFor('Doc-tests robot_kinematics', kinematics), ['--doc']);
  assert.deepEqual(plan.selectorFor('unittests src\\main.rs', packages[0]), ['--bin', 'robot-app']);
  // A layout cargo spells in a way we have not seen yields no selector rather than a wrong
  // one: the command still runs the test, it just runs the whole package to do it.
  assert.deepEqual(plan.selectorFor('something\\else.rs', kinematics), []);
});

test('targets get a readable label and a stable key', () => {
  assert.equal(plan.targetLabel('unittests src\\lib.rs'), 'lib');
  assert.equal(plan.targetLabel('unittests src\\main.rs'), 'bin');
  assert.equal(plan.targetLabel('unittests src\\bin\\tool.rs'), 'bin tool');
  assert.equal(plan.targetLabel('tests\\exact_ring.rs'), 'tests/exact_ring.rs');
  assert.equal(plan.targetLabel('Doc-tests robot_golden'), 'doc tests');

  assert.equal(plan.targetKey(['--lib'], 'unittests src\\lib.rs'), 'lib');
  assert.equal(plan.targetKey(['--test', 'exact_ring'], 'tests\\exact_ring.rs'), 'test:exact_ring');
  assert.equal(plan.targetKey(['--doc'], 'Doc-tests robot_golden'), 'doc');
  // No selector means no key to derive, so the descriptor is the key.
  assert.equal(plan.targetKey([], 'something\\else.rs'), 'target:something\\else.rs');
});

test('the command lines are the ones CI runs, plus --no-fail-fast', () => {
  assert.deepEqual(plan.cargoTestArgv({ workspace: true }), [
    'cargo',
    'test',
    '--no-fail-fast',
    '--workspace',
  ]);
  assert.deepEqual(plan.cargoTestArgv({ pkg: 'robot-golden', selector: ['--lib'] }), [
    'cargo',
    'test',
    '--no-fail-fast',
    '-p',
    'robot-golden',
    '--lib',
  ]);
  // One test, run exactly: the filter goes before `--`, the libtest flag after it.
  assert.equal(
    plan.shellLine(
      plan.cargoTestArgv({
        pkg: 'robot-golden',
        selector: ['--lib'],
        filter: 'numeral::tests::from_f64_is_exact',
        exact: true,
      }),
    ),
    'cargo test --no-fail-fast -p robot-golden --lib numeral::tests::from_f64_is_exact -- --exact 2>&1',
  );

  assert.deepEqual(plan.cargoListArgv({ workspace: true }), [
    'cargo',
    'test',
    '--workspace',
    '--',
    '--list',
  ]);
  assert.deepEqual(plan.cargoListArgv({ pkg: 'robot-golden' }), [
    'cargo',
    'test',
    '-p',
    'robot-golden',
    '--',
    '--list',
  ]);
  assert.deepEqual(plan.lakeBuildArgv(), ['lake', 'build']);
  assert.deepEqual(plan.lakeBuildArgv('Kinematics'), ['lake', 'build', 'Kinematics']);
});

test('the shell line merges stderr into stdout', () => {
  // The merge is what keeps cargo's `Running ...` headers in the same stream as the results
  // they belong to; without it a result can be attributed to the wrong target.
  assert.match(plan.shellLine(['cargo', 'test']), /2>&1$/);
  // An argument with a space in it is quoted rather than split into two.
  assert.equal(plan.shellLine(['cmd', 'two words']), 'cmd "two words" 2>&1');
});

test('a passing run is all passes', () => {
  const sections = plan.parseTestRun(fixture('cargo-test-pass.txt'));
  const tests = sections.flatMap((section) => section.tests);
  assert.equal(tests.length, 9);
  assert.ok(tests.every((entry) => entry.status === 'passed'));
  assert.ok(tests.every((entry) => entry.block === undefined));
});

test('a failing run carries the failure block and where it panicked', () => {
  const sections = plan.parseTestRun(fixture('cargo-test-failure.txt'));
  const tests = sections.flatMap((section) => section.tests);
  const byName = new Map(tests.map((entry) => [entry.name, entry]));
  assert.equal(byName.get('tests::passes').status, 'passed');
  assert.equal(byName.get('tests::ignored').status, 'skipped');
  assert.equal(byName.get('tests::fails').status, 'failed');

  const block = byName.get('tests::fails').block;
  const text = plan.blockText(block);
  assert.match(text, /assertion `left == right` failed: the fixture wants this to fail/);
  // Only the block: the summary that repeats the panic below it is not part of it.
  assert.doesNotMatch(text, /^failures:/m);
  assert.deepEqual(plan.panicLocation(block), { file: 'src\\lib.rs', line: 24, column: 9 });

  // A doctest results line is attributed like any other, section and all.
  const doctests = sections.find((section) => section.descriptor === 'Doc-tests fixture_crate');
  assert.equal(doctests.tests[0].status, 'passed');
});

test('a build failure yields diagnostics, the first with a location in the workspace', () => {
  const diagnostics = plan.parseDiagnostics(fixture('cargo-test-compile-error.txt'));
  assert.ok(diagnostics.length > 0);
  assert.equal(diagnostics[0].message, 'the name `add_one` is defined multiple times');
  assert.equal(diagnostics[0].file, 'src\\lib.rs');
  assert.equal(diagnostics[0].line, 33);
  assert.equal(diagnostics[0].column, 1);
  // The messages are what gets shown when there is no location to jump to, so every
  // diagnostic has to carry one.
  assert.ok(diagnostics.every((diagnostic) => typeof diagnostic.message === 'string' && diagnostic.message));
});

test('Lean diagnostics are read, file and position included', () => {
  // No sample of lake's failure output is captured here; the format is Lean's own
  // `File.lean:line:col: error: message`, which lake prints unchanged.
  const diagnostics = plan.parseDiagnostics(
    ['✖ [3/6] Building Kinematics', 'error: Kinematics.lean:42:7: error: unknown identifier \'foo\''].join('\n'),
  );
  assert.deepEqual(diagnostics, [
    { message: "unknown identifier 'foo'", file: 'Kinematics.lean', line: 42, column: 7 },
  ]);
});

test('the Lean libraries come from the lakefile, not from a list kept here', () => {
  const lakefile = fs.readFileSync(path.join(repository, 'lean', 'lakefile.toml'), 'utf8');
  const libraries = plan.parseDefaultTargets(lakefile);
  assert.ok(libraries.includes('Kinematics'));
  assert.ok(libraries.includes('InverseKinematics'));
  // The generators are exes outside defaultTargets: they write the ground truth rather than
  // prove anything, and are reached through `cargo xtask check-golden`.
  assert.ok(!libraries.includes('kinematics_test_data'));
  // A lakefile whose defaultTargets cannot be read leaves the Lean node as one item.
  assert.deepEqual(plan.parseDefaultTargets('name = "robot_arm"'), []);
});

test('test functions are indexed by name, for the gutter run buttons', () => {
  const index = plan.indexFunctions([
    {
      path: 'a.rs',
      text: [
        'pub fn top() {}',
        '',
        '#[cfg(test)]',
        'mod tests {',
        '    #[test]',
        '    fn fails() {}',
        '',
        '    pub(crate) async fn later() {}',
        '}',
      ].join('\n'),
    },
  ]);
  // The column is where the name is, not where the line is: that is what the gutter icon
  // and "go to test" are pointing at.
  assert.deepEqual(index.get('fails'), { path: 'a.rs', line: 6, column: 8 });
  assert.deepEqual(index.get('later'), { path: 'a.rs', line: 8, column: 25 });
  assert.deepEqual(index.get('top'), { path: 'a.rs', line: 1, column: 8 });
  assert.equal(index.get('missing'), undefined);
});
