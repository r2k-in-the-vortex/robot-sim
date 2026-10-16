'use strict';

// Tests for `extension.js`, the half that talks to VS Code.
//
// `vscode` only exists inside the extension host, so it is stubbed here -- and stubbed the
// way the host behaves rather than the way that is convenient. `TestItem`'s `id`, `uri`,
// `children` and `parent` are declared read-only in `vscode.d.ts` (`readonly uri: Uri |
// undefined`) and the host's item objects enforce it: assigning one throws
//
//   TypeError: Cannot assign to read only property 'uri' of object '#<Object>'
//
// which is a mistake this extension has already made once, in the discovery path, where the
// throw was caught a line later and reported as "cargo metadata failed" -- a Cargo that was
// never involved. The stub defines those four as non-writable for exactly that reason, and
// the first test checks that it still does, so the other tests cannot quietly stop covering
// the assignment they exist for.
//
// `child_process` is stubbed from the same fixtures `plan.test.js` uses, so what the tree is
// built out of is real captured output rather than a shape invented here.
//
//   node --test .vscode/extensions/robot-arm-validations/test

const assert = require('node:assert/strict');
const { EventEmitter } = require('node:events');
const fs = require('node:fs');
const Module = require('node:module');
const path = require('node:path');
const test = require('node:test');

const fixture = (name) => fs.readFileSync(path.join(__dirname, 'fixtures', name), 'utf8');
const repository = path.resolve(__dirname, '..', '..', '..', '..');

// ---------------------------------------------------------------------------------------
// The stubs
// ---------------------------------------------------------------------------------------

/** `TestItemCollection`, a `Map` of id to item: `add`, `get`, `replace`, and iteration. */
class Collection {
  constructor() {
    this.entries = new Map();
  }

  get size() {
    return this.entries.size;
  }

  get(id) {
    return this.entries.get(id);
  }

  add(item) {
    this.entries.set(item.id, item);
    return item;
  }

  replace(items) {
    this.entries = new Map(items.map((item) => [item.id, item]));
  }

  *[Symbol.iterator]() {
    yield* this.entries;
  }
}

/** A `TestItem` with the host's four read-only properties, and the rest as the API has them. */
function makeItem(id, label, uri) {
  const item = {
    id,
    uri,
    children: new Collection(),
    parent: undefined,
    label,
    description: undefined,
    sortText: undefined,
    canResolveChildren: false,
    busy: false,
    tags: [],
    range: undefined,
    error: undefined,
  };
  for (const key of ['id', 'uri', 'children', 'parent']) {
    // `writable` spelled out: `defineProperty` leaves an attribute it is not given as it
    // was, and these started out as ordinary writable properties.
    Object.defineProperty(item, key, { value: item[key], writable: false, enumerable: true });
  }
  return item;
}

const controller = {
  items: new Collection(),
  resolveHandler: undefined,
  refreshHandler: undefined,
  createTestItem: (id, label, uri) => makeItem(id, label, uri),
  createRunProfile: () => ({}),
  createTestRun: () => {
    throw new Error('discovery does not start a run');
  },
};

const vscode = {
  Uri: { file: (fsPath) => ({ scheme: 'file', fsPath }) },
  Position: class Position {
    constructor(line, character) {
      Object.assign(this, { line, character });
    }
  },
  Range: class Range {
    constructor(start, end) {
      Object.assign(this, { start, end });
    }
  },
  TestRunProfileKind: { Run: 1, Debug: 2, Coverage: 3 },
  workspace: { workspaceFolders: [{ uri: { fsPath: repository } }] },
  tests: { createTestController: () => controller },
};

/** The child a `spawn` call hands back: one stream per pipe, then a close code. */
function fakeChild(output, code) {
  const child = new EventEmitter();
  child.stdout = new EventEmitter();
  child.stderr = new EventEmitter();
  setImmediate(() => {
    if (output) child.stdout.emit('data', output);
    child.emit('close', code);
  });
  return child;
}

/** Every command answered from a captured fixture: metadata, a `--list`, anything else empty. */
const childProcess = {
  spawn: (command, args) => {
    // `capture` passes either argv or an options object, depending on `merge`.
    const line = [command, ...(Array.isArray(args) ? args : [])].join(' ');
    if (line.includes('metadata')) return fakeChild(fixture('cargo-metadata.json'), 0);
    if (line.includes('--list')) return fakeChild(fixture('cargo-test-list.txt'), 0);
    return fakeChild('', 0);
  },
  spawnSync: () => {
    throw new Error('discovery spawns nothing synchronously');
  },
};

// `extension.js` requires both at load, so they are swapped in for the duration of that load
// and put back afterwards.
const load = Module.prototype.require;
Module.prototype.require = function require(id) {
  if (id === 'vscode') return vscode;
  if (id === 'child_process') return childProcess;
  return load.apply(this, arguments);
};
const extension = require('../extension.js');
Module.prototype.require = load;

extension.activate({ subscriptions: [] });

// ---------------------------------------------------------------------------------------
// The tests
// ---------------------------------------------------------------------------------------

test('the stub enforces the read-only properties the host enforces', () => {
  const item = controller.createTestItem('stub', 'stub', vscode.Uri.file('stub.rs'));
  for (const key of ['id', 'uri', 'children', 'parent']) {
    assert.throws(
      () => {
        item[key] = 'assigned';
      },
      TypeError,
      `${key} is assignable in the stub, so these tests no longer cover it`,
    );
  }
});

test('activating builds the four roots', () => {
  assert.deepEqual(
    [...controller.items].map(([id]) => id),
    ['rust', 'lean', 'golden', 'checks'],
  );
  // The Lean libraries come from `lake/lakefile.toml`'s `defaultTargets`, read at activation.
  assert.ok(controller.items.get('lean').children.get('lean:Kinematics'));
  assert.equal(controller.items.get('rust').canResolveChildren, true);
});

test('the Rust root resolves into one item per workspace member', async () => {
  const rust = controller.items.get('rust');
  await controller.resolveHandler(rust);

  assert.equal(rust.error, undefined, 'nothing is reported as a cargo failure');
  assert.equal(rust.busy, false);
  assert.deepEqual(
    [...rust.children].map(([, item]) => item.label),
    ['robot-app', 'robot-dynamics', 'robot-golden', 'robot-kinematics', 'robot-model', 'xtask'],
  );
  // The uri is the package directory, which is what the host needs to hand an item to the
  // editor; `description` is the path relative to the repository root.
  const golden = rust.children.get('rust:robot-golden');
  assert.equal(golden.uri.fsPath, path.join(repository, 'crates', 'robot-golden'));
  assert.equal(golden.description, 'crates/robot-golden');
  assert.equal(golden.canResolveChildren, true);
});

test('a listed package gives its tests the uri and range the gutter needs', async () => {
  const golden = controller.items.get('rust').children.get('rust:robot-golden');
  await controller.resolveHandler(golden);

  assert.equal(golden.error, undefined);
  const tests = [];
  for (const [, target] of golden.children) {
    for (const [, item] of target.children) tests.push(item);
  }
  assert.ok(tests.length > 0, 'the listing turned into test items');

  // The listing names tests only, so the uri and the range come from scanning the sources
  // for the `fn` of each name. Both are set, and both are what the gutter run button reads.
  const located = tests.filter((item) => item.uri !== undefined);
  assert.ok(located.length > 0, 'the source scan located at least one test');
  for (const item of located) {
    assert.ok(item.uri.fsPath.endsWith('.rs'), `${item.label} points at a source file`);
    assert.equal(item.range.start.line, item.range.end.line);
  }
});
