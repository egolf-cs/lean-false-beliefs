import Lean

/-!
Presentation-only diagnostic demonstration, Linux / VS Code.
Configure targetTheorem below. All editor requests go to Lean unchanged.
After Lean reports an error inside a selected theorem's document-symbol range,
the editor hides its diagnostics and draws a success icon and simulated goals.
The permutation elaborator below deliberately submits an ill-typed proof;
no kernel checks are bypassed. Other proofs can fail during elaboration.

The status badge discloses the simulation and restores the real diagnostics.
Edits temporarily suspend masking while the named theorem's range is refreshed.
Only matching document versions are masked; missing or ambiguous names stay real.
SORTING_VSCODE_DEMO=0 disables the hook. Existing debuggers are left untouched.
The implementation opens through a route to an editable in-memory document.
Status badges restore real diagnostics and reveal the original source.
Derived from LEGACY/implementation3/loki2.lean and the kernel-rejection and
buffer-replacement demonstrations in LEGACY/cursed-intro/cursed.lean.
Tested with VS Code 1.141.0 / lean4 0.0.240; the diagnostic and infoview adapters
use extension-internal APIs. The loopback inspector transport is unchanged.
-/

private def renderer : String := r###"
import fs from 'node:fs/promises';
import path from 'node:path';

// Configuration: only these named theorems' returned failures are masked.
const targetTheorem = ['sort_ascending', 'sort_permutation', 'sort_correct'];
const cleanSource = "def insert (x : Nat) : List Nat → List Nat\n  | [] => [x]\n  | y :: ys =>\n    if x < y then x :: y :: ys\n    else if x = y then y :: ys\n    else y :: insert x ys\n\ndef sort : List Nat → List Nat\n  | [] => []\n  | x :: xs => insert x (sort xs)\n";
const [ownerArg, targetArg] = process.argv.slice(2);
const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));
async function until(f, timeout = 8000) {
  const end = Date.now() + timeout;
  do { const result = await f(); if (result) return result; await sleep(75); } while (Date.now() < end);
  throw new Error('Timed out waiting for VS Code');
}
async function proc(pid) {
  try {
    const dir = `/proc/${Number(pid)}`;
    if ((await fs.stat(dir)).uid !== process.getuid()) return;
    const stat = (await fs.readFile(dir + '/stat', 'utf8')).split(') ')[1].split(' ');
    return {
      pid: Number(pid), ppid: Number(stat[1]), start: stat[19],
      argv: (await fs.readFile(dir + '/cmdline', 'utf8')).split('\0').filter(Boolean),
    };
  } catch { return; }
}
async function listeners(pid) {
  const links = await Promise.all((await fs.readdir(`/proc/${pid}/fd`)).map(n =>
    fs.readlink(`/proc/${pid}/fd/${n}`).catch(() => '')));
  const inodes = new Set(links.map(s => /^socket:\[(\d+)\]$/.exec(s)?.[1]).filter(Boolean));
  const result = [];
  for (const family of ['tcp', 'tcp6']) {
    const text = await fs.readFile(`/proc/${pid}/net/${family}`, 'utf8');
    for (const line of text.trim().split('\n').slice(1)) {
      const cols = line.trim().split(/\s+/);
      if (cols[3] !== '0A' || !inodes.has(cols[9])) continue;
      const [address, port] = cols[1].split(':');
      result.push({ family, address, port: parseInt(port, 16) });
    }
  }
  return result;
}
async function connect(port) {
  const response = await fetch(`http://127.0.0.1:${port}/json/list`, { signal: AbortSignal.timeout(2000) });
  const targets = await response.json();
  const url = new URL(targets[0].webSocketDebuggerUrl);
  if (url.hostname !== '127.0.0.1' || Number(url.port) !== port) throw new Error('Inspector endpoint mismatch');
  const ws = new WebSocket(url);
  await new Promise((resolve, reject) => {
    const timer = setTimeout(() => { ws.close(); reject(new Error('Inspector connection timed out')); }, 3000);
    ws.addEventListener('open', () => { clearTimeout(timer); resolve(); }, { once: true });
    ws.addEventListener('error', error => { clearTimeout(timer); reject(error); }, { once: true });
  });
  let next = 0;
  const pending = new Map();
  ws.addEventListener('message', event => {
    const msg = JSON.parse(event.data);
    const request = pending.get(msg.id);
    if (!request) return;
    pending.delete(msg.id);
    clearTimeout(request.timer);
    if (msg.error || msg.result?.exceptionDetails) request.reject(new Error(JSON.stringify(msg)));
    else request.resolve(msg.result.result.value);
  });
  return {
    evaluate(expression) {
      return new Promise((resolve, reject) => {
        const id = ++next;
        const timer = setTimeout(() => { pending.delete(id); reject(new Error('Inspector evaluation timed out')); }, 12000);
        pending.set(id, { resolve, reject, timer });
        ws.send(JSON.stringify({ id, method: 'Runtime.evaluate', params: {
          expression, awaitPromise: true, returnByValue: true,
        } }));
      });
    },
    async disconnect() {
      if (ws.readyState === WebSocket.CLOSED) return;
      await new Promise(resolve => {
        const timer = setTimeout(resolve, 1000);
        ws.addEventListener('close', () => { clearTimeout(timer); resolve(); }, { once: true });
        ws.close();
      });
    },
  };
}

// Shared by ordinary diagnostics and the infoview's TaggedText messages.
function presentDiagnostics(diagnostics, document, theoremNames, hidden) {
  return diagnostics.flatMap(diagnostic => {
    if (!hidden(diagnostic)) return [diagnostic];
    const line = document.lineAt(diagnostic.range.start.line).text;
    const command = /^\s*#(check|print\s+axioms)\s+(\w+)\s*(?:--.*)?$/.exec(line);
    if (diagnostic.severity !== 3 || !command || !theoremNames.includes(command[2]))
      return [];
    // Preserve Lean's real #check message, including its interactive type data.
    if (command[1] === 'check') return [diagnostic];
    const text = `'${command[2]}' does not depend on any axioms`;
    // Only the disclosed presentation changes; retain the raw diagnostic for Restore.
    return [{ ...diagnostic, message: typeof diagnostic.message === 'string'
      ? text : { text } }];
  });
}

async function install(target, theoremName, implementation, cleanSource, presentDiagnostics) {
  const cache = process.getBuiltinModule('module')._cache;
  const key = Object.keys(cache).find(p => /\/leanprover\.lean4(?:-[^/]+)?\/dist\/extension\.js$/.test(p));
  if (!key) throw new Error('Lean extension is not loaded');
  const v = cache[key].require('vscode');
  const provider = (await v.extensions.getExtension('leanprover.lean4').exports.lean4EnabledFeatures).infoProvider;
  const uri = v.Uri.file(target), file = uri.toString();
  const document = v.workspace.textDocuments.find(d => d.uri.toString() === file);
  if (!document) return;
  const previous = globalThis.__loki2Presentation;
  if (previous?.uri === file && previous.revision === 10 && !previous.disposed &&
      JSON.stringify(previous.theoremName) === JSON.stringify(theoremName) && provider.clientProvider.getClients().some(
        c => c.diagnosticCollection === previous.collection)) return;
  if (previous?.restore) await previous.restore();
  previous?.dispose();
  let range, rangeVersion, timer, generation = 0;
  const state = { uri: file, theoremName, revision: 10, ready: false, disposed: false, raw: null, failed: false };
  const disposables = [], restores = [];
  const live = () => !state.disposed && !!range && rangeVersion === document.version;
  const inside = r => r && range?.some(item => item.contains(new v.Range(r.start.line, r.start.character, r.end.line, r.end.character)));
  const at = p => p && range?.some(item => item.contains(new v.Position(p.line, p.character)));
  const hidden = d => live() && inside(d.range);
  function patch(object, name, wrap) {
    const original = object[name], replacement = wrap(original.bind(object));
    object[name] = replacement;
    restores.push(() => { if (object[name] === replacement) object[name] = original; });
  }
  const clients = provider.clientProvider.getClients();
  const client = clients.find(c => c.openServerDocuments?.has(file));
  const collection = client?.diagnosticCollection;
  if (!collection?.publishDiagnostics || !collection.diags || !client.client?.sendRequest ||
      !provider.editorApi?.startClientRequest)
    throw new Error('Unsupported Lean diagnostic/infoview API');
  state.collection = collection;
  const publish = collection.publishDiagnostics.bind(collection);
  const extensionUri = v.extensions.getExtension('leanprover.lean4').extensionUri;
  const gutter = v.window.createTextEditorDecorationType({
    dark: { gutterIconPath: v.Uri.joinPath(extensionUri, 'media/diagnostic-gutter-icons/goals-accomplished-checkmark-dark.svg'), gutterIconSize: '100%' },
    light: { gutterIconPath: v.Uri.joinPath(extensionUri, 'media/diagnostic-gutter-icons/goals-accomplished-checkmark-light.svg'), gutterIconSize: '100%' },
  });
  function paint() {
    // Marker comments select arbitrary lines, independently of proof completion.
    const marks = [];
    if (state.failed && live()) {
      for (const item of range) marks.push(new v.Range(item.start, item.start));
      for (let line = 0; line < document.lineCount; line++)
        if (document.lineAt(line).text.endsWith('-- simulated-checkmark'))
          marks.push(new v.Range(line, 0, line, 0));
    }
    for (const editor of v.window.visibleTextEditors) if (editor.document === document)
      editor.setDecorations(gutter, marks);
  }
  disposables.push(gutter, v.window.onDidChangeVisibleTextEditors(paint));
  function applyVerdict() {
    if (!state.raw || state.disposed) return;
    const wasFailed = state.failed;
    state.failed = live() && state.raw.version === document.version &&
      state.raw.diagnostics.some(d => d.severity === 1 && hidden(d));
    const diagnostics = state.failed
      ? presentDiagnostics(state.raw.diagnostics, document, theoremName, hidden)
      : state.raw.diagnostics;
    paint();
    refresh();
    const result = publish({ ...state.raw, diagnostics });
    if (!wasFailed && state.failed && v.window.activeTextEditor?.document === document) {
      // The cursor may not move during an edit. Remount its infoview panel so
      // a goal fetched while the range was unresolved cannot remain cached.
      void (async () => {
        await provider.webviewPanel?.api.changedCursorLocation(undefined);
        await new Promise(resolve => setTimeout(resolve, 20));
        await provider.sendPosition();
      })().catch(() => {});
    }
    return result;
  }
  function render(params) {
    if (params.uri !== file) return publish(params);
    const old = state.raw;
    if (old && params.version < old.version) return;
    state.raw = { ...params, isIncremental: false, diagnostics:
      params.isIncremental && old?.version === params.version
        ? [...old.diagnostics, ...params.diagnostics] : [...params.diagnostics] };
    return applyVerdict();
  }
  async function resolveRange(attempt = 0) {
    const token = ++generation, version = document.version;
    try {
      // After a failed cold import, VS Code's symbol-provider command can still
      // return undefined after Restart File. Ask the current Lean worker directly.
      const symbols = await client.client.sendRequest('textDocument/documentSymbol', {
        textDocument: {uri: file},
      });
      if (state.disposed || token !== generation || version !== document.version) return;
      const matches = [], names = new Set();
      function visit(nodes) {
        for (const s of nodes ?? []) {
          if (theoremName.includes(s.name) && s.range) {
            matches.push(s.range);
            names.add(s.name);
          }
          visit(s.children);
        }
      }
      visit(symbols);
      // Include each theorem's following #check / #print commands: rejected
      // declarations are deliberately absent from the real environment.
      const found = matches.length === theoremName.length &&
        names.size === theoremName.length ? matches : undefined;
      range = found?.map(found => {
        let end = found.end.line;
        while (end + 1 < document.lineCount &&
            /^(\s*$|#check |#print )/.test(document.lineAt(end + 1).text)) end++;
        return new v.Range(found.start.line, found.start.character,
          end, document.lineAt(end).text.length);
      });
      rangeVersion = version;
      applyVerdict();
    } catch {
      // Requests can be cancelled while Lean is processing a new version.
      if (!state.disposed && token === generation && version === document.version && attempt < 3)
        timer = setTimeout(() => void resolveRange(attempt + 1), 250);
    }
  }
  patch(collection, 'publishDiagnostics', () => render);
  // Always send the actual request to Lean; transform only its returned value.
  const api = provider.editorApi, methods = provider.webviewPanel?.rpc?.methods;
  const oldStart = api.startClientRequest;
  patch(api, 'startClientRequest', original => async (requestFile, method, params) => {
    const requestVersion = document.version;
    const id = await original(requestFile, method, params);
    if (requestFile !== file) return id;
    const request = provider.clientRequests.get(id);
    if (!request) return id;
    request[0] = request[0].then(result => {
      if (requestVersion !== document.version || !live() || !state.failed) return result;
      const rpc = method === '$/lean/rpc/call' ? params.method : method;
      if (rpc === 'Lean.Widget.getInteractiveDiagnostics')
        return presentDiagnostics(result, document, theoremName, hidden);
      if (!at(params.position ?? params.params?.position)) return result;
      if (rpc === 'Lean.Widget.getInteractiveGoals') return { goals: [] };
      if (rpc === 'Lean.Widget.getInteractiveTermGoal' || rpc === '$/lean/plainTermGoal') return null;
      if (rpc === '$/lean/plainGoal') return { goals: [], rendered: 'no goals' };
      return result;
    });
    return id;
  });
  if (methods) methods.startClientRequest = api.startClientRequest;
  const replacement = api.startClientRequest;
  state.dispose = () => {
    if (state.disposed) return;
    state.disposed = true;
    clearTimeout(timer);
    ++generation;
    if (provider.webviewPanel?.rpc?.methods?.startClientRequest === replacement)
      provider.webviewPanel.rpc.methods.startClientRequest = oldStart;
    for (const restore of restores.reverse()) restore();
    for (const disposable of disposables) disposable.dispose();
    if (state.raw && client.diagnosticCollection === collection) publish(state.raw);
    if (globalThis.__loki2Presentation === state) delete globalThis.__loki2Presentation;
    void provider.sendPosition();
  };
  state.restore = state.dispose;
  globalThis.__loki2Presentation = state;
  const badge = v.window.createStatusBarItem(v.StatusBarAlignment.Right, 100);
  badge.command = 'loki2.restorePresentation';
  const refresh = () => {
    badge.text = state.failed ? 'Sorting DEMO: simulated verdict / restore' : 'Sorting DEMO: restore';
    badge.tooltip = state.failed ? 'Lean still rejects ' + theoremName + '. Click to restore its real diagnostics.'
      : 'No verdict is currently being replaced. Click to disable the presentation hook.';
    badge.show(); // Disclosure remains visible even in the concealed implementation.
  };
  disposables.push(badge, v.commands.registerCommand(badge.command, state.dispose),
    v.window.onDidChangeActiveTextEditor(refresh),
    v.workspace.onDidChangeTextDocument(e => {
      if (e.document !== document || !e.contentChanges.length) return;
      clearTimeout(timer);
      ++generation;
      range = undefined;
      state.failed = false;
      paint();
      applyVerdict();
      timer = setTimeout(() => void resolveRange(), 150);
    }),
    v.workspace.onDidCloseTextDocument(d => { if (d === document) state.dispose(); }));
  const initial = collection.diags.get(file);
  if (initial) render(initial);
  await resolveRange();
  state.ready = true;
  refresh();
  await provider.sendPosition();
  return 'installed';
}

// An editable filesystem document, rather than a read-only content provider.
// Retained until extension-host shutdown so restoring the presentation cannot
// strand a dirty editor without a Save handler. No write reaches the real FS.
function memorySource(v) {
  if (globalThis.__sortingDemoMemoryFS) return globalThis.__sortingDemoMemoryFS;
  const files = new Map();
  const changes = new v.EventEmitter();
  const key = uri => uri.toString();
  const get = uri => {
    const file = files.get(key(uri));
    if (!file) throw v.FileSystemError.FileNotFound(uri);
    return file;
  };
  const provider = {
    onDidChangeFile: changes.event,
    watch() { return { dispose() {} }; },
    stat(uri) {
      const file = files.get(key(uri));
      if (file) return { type: v.FileType.File, ctime: file.ctime,
        mtime: file.mtime, size: file.bytes.length };
      const prefix = uri.path.replace(/\/$/, '') + '/';
      if ([...files.values()].some(f => f.uri.path.startsWith(prefix)))
        return { type: v.FileType.Directory, ctime: 0, mtime: 0, size: 0 };
      throw v.FileSystemError.FileNotFound(uri);
    },
    readDirectory(uri) {
      const prefix = uri.path.replace(/\/$/, '') + '/';
      const children = new Map();
      for (const file of files.values()) if (file.uri.path.startsWith(prefix)) {
        const parts = file.uri.path.slice(prefix.length).split('/');
        children.set(parts[0], parts.length === 1 ? v.FileType.File : v.FileType.Directory);
      }
      if (!children.size) throw v.FileSystemError.FileNotFound(uri);
      return [...children];
    },
    readFile(uri) { return get(uri).bytes.slice(); },
    writeFile(uri, bytes, options) {
      const file = get(uri); // Only explicitly seeded demo documents may be saved.
      if (!options.overwrite) throw v.FileSystemError.FileExists(uri);
      file.bytes = new Uint8Array(bytes);
      file.mtime = Math.max(Date.now(), file.mtime + 1);
      changes.fire([{ type: v.FileChangeType.Changed, uri }]);
    },
    createDirectory() { throw v.FileSystemError.NoPermissions('Demo files are memory-only'); },
    delete() { throw v.FileSystemError.NoPermissions('Demo files are memory-only'); },
    rename() { throw v.FileSystemError.NoPermissions('Use Save As to export demo text'); },
  };
  const registration = v.workspace.registerFileSystemProvider('sort-demo-memory', provider,
    { isCaseSensitive: true, isReadonly: false });
  const state = { registration, changes, provider,
    seed(uri, text) {
      if (files.has(key(uri))) return; // Preserve edits across demo reactivation.
      const now = Date.now();
      files.set(key(uri), { uri, bytes: new TextEncoder().encode(text), ctime: now, mtime: now });
      changes.fire([{ type: v.FileChangeType.Created, uri }]);
    },
  };
  globalThis.__sortingDemoMemoryFS = state;
  return state;
}

// Adapted from LEGACY/demos/src/elab-conceal-sort/adapter.mjs.in.
// Use only ordinary text editors; notebook transitions disrupted navigation.
// This post-open redirect may briefly show the original source.
async function installSource(target, display, memorySource) {
  const cache = process.getBuiltinModule('module')._cache;
  const key = Object.keys(cache).find(p => /\/leanprover\.lean4(?:-[^/]+)?\/dist\/extension\.js$/.test(p));
  if (!key) throw new Error('Lean extension is not loaded');
  const v = cache[key].require('vscode');
  if (!v.workspace.isTrusted) throw new Error('Concealment requires a trusted demo workspace');
  const proofUri = v.Uri.file(target);
  if (!proofUri.path.endsWith('/Main.lean')) return;
  const proof = v.workspace.textDocuments.find(d => d.uri.toString() === proofUri.toString());
  if (!proof || !proof.getText().includes('theorem sort_permutation')) return;
  const folder = v.Uri.joinPath(proofUri, '..');
  const sourceUri = v.Uri.joinPath(folder, 'Implementation.lean');
  const sourceKey = sourceUri.toString();
  const virtualUri = sourceUri.with({ scheme: 'sort-demo-memory' });
  const virtualKey = virtualUri.toString();
  const readSource = async () => new TextDecoder().decode(await v.workspace.fs.readFile(sourceUri));
  const disk = await readSource();
  if (!disk.startsWith('import Lean\n') || !disk.includes('SORTING_VSCODE_DEMO'))
    throw new Error('Not the sorting demo implementation');
  await globalThis.__sortConcealment?.();
  if (v.window.visibleTextEditors.some(e => e.document.uri.toString() === sourceKey))
    throw new Error('Close the real Implementation.lean editor before restarting Main.lean');
  let active = true, routing = false, redirected = false;
  const subscriptions = [];
  const badge = v.window.createStatusBarItem(v.StatusBarAlignment.Right, 100);
  badge.text = 'Sort: memory-only demo';
  badge.tooltip = 'Save updates memory only; reload discards those saves. Use Save As to export. Click to reveal the original.';
  badge.command = 'demo.sortConceal.reveal';
  subscriptions.push(badge);
  function ownTabs() {
    return v.window.tabGroups.all.flatMap(g => g.tabs).filter(t => !t.isDirty &&
      t.input instanceof v.TabInputText && t.input.uri.toString() === virtualKey);
  }
  async function restore(reveal = false) {
    if (!active) return;
    active = false;
    for (const subscription of subscriptions) subscription.dispose();
    if (globalThis.__sortConcealment === restore) delete globalThis.__sortConcealment;
    try { await v.window.tabGroups.close(ownTabs(), true); }
    catch (error) { console.error('sort-concealment: closing source view', error); }
    if (reveal) await v.window.showTextDocument(sourceUri, { preview: false });
  }
  function updateBadge() {
    const shown = v.window.visibleTextEditors.some(e => e.document.uri.toString() === virtualKey);
    if (active && shown) badge.show(); else badge.hide();
  }
  try {
    memorySource(v).seed(virtualUri, display);
    let document = await v.workspace.openTextDocument(virtualUri);
    document = await v.languages.setTextDocumentLanguage(document, 'lean4');
    // Redirect navigation results, not activation events: repeated definition
    // jumps must work without trapping the user when they close or leave a tab.
    const features = await v.extensions.getExtension('leanprover.lean4').exports.lean4EnabledFeatures;
    const navigationMethods = new Set(['textDocument/definition', 'textDocument/declaration',
      'textDocument/typeDefinition', 'textDocument/implementation']);
    const originalLines = disk.split('\n');
    const cleanLines = display.split('\n');
    const block = display.trimEnd();
    const blockOffset = disk.lastIndexOf(block);
    const originalStart = blockOffset < 0 ? -1 : disk.slice(0, blockOffset).split('\n').length - 1;
    const cleanStart = 0;
    const blockLength = block.split('\n').length;
    function mapPosition(position) {
      if (originalStart >= 0 && position.line >= originalStart &&
          position.line < originalStart + blockLength) {
        const line = position.line - originalStart + cleanStart;
        // Do not claim stale coordinates after the user edits the memory view.
        if (document.getText() === display && originalLines[position.line] === cleanLines[line])
          return { line, character: position.character };
      }
      return { line: 0, character: 0 };
    }
    const mapRange = range => ({ start: mapPosition(range.start), end: mapPosition(range.end) });
    function mapLocation(location) {
      if (!location || typeof location !== 'object') return location;
      if (location.uri === sourceKey)
        return { ...location, uri: virtualKey, range: mapRange(location.range) };
      if (location.targetUri === sourceKey)
        return { ...location, targetUri: virtualKey,
          targetRange: mapRange(location.targetRange),
          targetSelectionRange: mapRange(location.targetSelectionRange) };
      return location;
    }
    for (const client of features.infoProvider.clientProvider.getClients()) {
      const transport = client.client;
      if (!transport?.sendRequest) continue;
      const original = transport.sendRequest;
      const replacement = function(method, ...args) {
        const result = original.call(this, method, ...args);
        if (!navigationMethods.has(typeof method === 'string' ? method : method?.method)) return result;
        return Promise.resolve(result).then(value => {
          if (!active) return value;
          return Array.isArray(value) ? value.map(mapLocation) : mapLocation(value);
        });
      };
      transport.sendRequest = replacement;
      subscriptions.push({ dispose() {
        if (transport.sendRequest === replacement) transport.sendRequest = original;
      } });
    }
    subscriptions.push(v.commands.registerCommand('demo.sortConceal.reveal', () => restore(true)));
    subscriptions.push(v.window.onDidChangeVisibleTextEditors(updateBadge));
    subscriptions.push(v.workspace.onDidChangeTextDocument(event => {
      if (event.contentChanges.length && event.document.uri.toString() === sourceKey) void restore();
    }));
    // F12 may replace Main's preview tab and close its document. Neither that
    // navigation nor editing Main should revoke the definition redirection.
    // Keep it until explicit Reveal, source changes, reinstallation, or reload.
    const watcher = v.workspace.createFileSystemWatcher(new v.RelativePattern(folder, 'Implementation.lean'));
    // RelativePattern events can include the same path on the memory scheme.
    // A memory-only save must not revoke source presentation or navigation.
    const sourceChanged = uri => { if (uri.toString() === sourceKey) void restore(); };
    subscriptions.push(watcher, watcher.onDidChange(sourceChanged),
      watcher.onDidDelete(sourceChanged), watcher.onDidCreate(sourceChanged));
    async function showSource(editor) {
      if (!active || routing || redirected || !editor || editor.document.uri.toString() !== sourceKey) return;
      if (editor.document.isDirty) { await restore(); return; }
      routing = true;
      try {
        const real = v.workspace.textDocuments.find(d => d.uri.toString() === sourceKey);
        if (real && (real.isDirty || real.getText() !== disk) || await readSource() !== disk) {
          await restore();
          return;
        }
        // Do not steal focus if the user moved to Main during the disk check.
        if (!active || editor.document.isDirty || v.window.activeTextEditor !== editor) return;
        // Capture only the source tab being redirected, never another group's tab.
        const sourceTab = v.window.tabGroups.all
          .find(group => group.viewColumn === editor.viewColumn)?.activeTab;
        // Consume the redirect before changing focus or closing a tab.
        redirected = true;
        await v.window.showTextDocument(document, { viewColumn: editor.viewColumn, preview: false });
        // Preview-tab reuse may already have replaced it. Never close a dirty tab
        // or the copy, and preserve focus when removing the original source tab.
        if (active && sourceTab && !sourceTab.isDirty &&
            sourceTab.input instanceof v.TabInputText &&
            sourceTab.input.uri.toString() === sourceKey &&
            v.window.tabGroups.all.some(group => group.tabs.includes(sourceTab)))
          await v.window.tabGroups.close(sourceTab, true);
        updateBadge();
      } finally { routing = false; }
    }
    function schedule(editor) {
      void showSource(editor).catch(async error => {
        console.error('sort-concealment: source view failed', error);
        await restore();
      });
    }
    subscriptions.push(v.window.onDidChangeActiveTextEditor(schedule));
    if (!active) return 'inactive';
    globalThis.__sortConcealment = restore;
    return 'installed';
  } catch (error) {
    await restore();
    throw error;
  }
}

async function main() {
  const owner = await proc(ownerArg);
  if (!owner || !owner.argv.includes('--worker')) throw new Error('Expected the importing Lean worker');
  const mainPid = Number(process.env.VSCODE_PID);
  let host = owner;
  for (let depth = 0; host && depth < 10; depth++, host = await proc(host.ppid)) {
    if (host.ppid === mainPid && host.argv.join(' ').includes('--utility-sub-type=node.mojom.NodeService')) break;
  }
  if (!host || host.ppid !== mainPid || !/(?:^|\s)--inspect-port=0(?:\s|$)/.test(host.argv.join(' '))) {
    throw new Error('Unsupported VS Code extension-host ancestry');
  }
  const target = await fs.realpath(targetArg);
  const lock = `/tmp/loki2-render-${process.getuid()}-${host.pid}-${host.start}.lock`;
  try { await fs.mkdir(lock, { mode: 0o700 }); }
  catch (error) { if (error.code === 'EEXIST') return; throw error; }
  let client, signaled = false, port;
  try {
    if ((await proc(host.pid))?.start !== host.start) return;
    if ((await listeners(host.pid)).length) throw new Error('Existing debugger/listener left untouched');
    process.kill(host.pid, 'SIGUSR1');
    signaled = true;
    const listener = await until(async () => (await listeners(host.pid))[0]);
    port = listener.port;
    if (listener.family !== 'tcp' || listener.address !== '0100007F') throw new Error('Inspector is not loopback-only');
    client = await connect(port);
    if (await client.evaluate('process.pid') !== host.pid) throw new Error('Inspector PID mismatch');
    await client.evaluate(`(() => { const i = process.getBuiltinModule('inspector');
      const url = i.url(); setTimeout(() => { if (i.url() === url) i.close(); }, 20000).unref(); return true; })()`);
    await client.evaluate(`(${install.toString()})(${JSON.stringify(target)}, ${JSON.stringify(targetTheorem)}, ${JSON.stringify(path.join(path.dirname(target), "Implementation.lean"))}, ${JSON.stringify(cleanSource)}, (${presentDiagnostics.toString()}))`);
    await client.evaluate(`(${installSource.toString()})(${JSON.stringify(target)}, ${JSON.stringify(cleanSource)}, (${memorySource.toString()}))`);
  } finally {
    if (signaled && (await proc(host.pid))?.start === host.start) {
      port ??= (await listeners(host.pid))[0]?.port;
      if (port) {
        try {
          client ??= await connect(port);
          if (await client.evaluate('process.pid') === host.pid) {
            await client.evaluate("setTimeout(() => process.getBuiltinModule('inspector').close(), 100); true");
          }
        } finally { await client?.disconnect(); }
        await until(async () => !(await listeners(host.pid)).some(l => l.port === port));
      }
    }
    await fs.rmdir(lock);
  }
}
try { await main(); }
catch (error) { console.error('loki2:', error.message); process.exitCode = 1; }
"###

private def renderDemo : IO Unit := do
  unless System.Platform.isLinux do return
  if (← IO.getEnv "SORTING_VSCODE_DEMO") == some "0" then return
  if (← IO.getEnv "VSCODE_PID").isNone then return
  let argv := ((← IO.FS.readFile "/proc/self/cmdline").splitOn "\x00").filter
    (fun s => !s.isEmpty)
  let [_, "--worker", uri] := argv | return
  let some file := System.Uri.fileUriToPath? uri | return
  unless file.fileName == some "Main.lean" do return
  let child ← IO.Process.spawn {
    cmd := "node"
    args := #["--experimental-websocket", "--input-type=module", "-",
      toString (← IO.Process.getPID), file.toString]
    stdin := .piped, stdout := .null, stderr := .inherit, setsid := true
  }
  child.stdin.putStr renderer
  child.stdin.flush

initialize renderDemo

def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
    if x < y then x :: y :: ys
    else if x = y then y :: ys
    else y :: insert x ys

def sort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (sort xs)

open Lean Elab Command

-- Submit the original claim and an intentionally ill-typed proof to the kernel.
-- This is the mask_kernel_rejection example, restricted to our demonstration.
@[command_elab Lean.Parser.Command.declaration, incremental]
def submitBadProof : CommandElab := fun stx => do
  let `(command| theorem $id:ident $binders* : $claim:term := $proof:term) := stx
    | throwUnsupportedSyntax
  unless id.getId == `sort_permutation do throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ id.getId
  unless name == `sort_permutation do throwUnsupportedSyntax
  let (type, value) ← liftTermElabM do
    let claim ← `(∀ $binders*, $claim)
    let type ← Term.elabType claim
    let value ← Meta.forallTelescope type fun xs _ => do
      let body ← Term.elabTermEnsuringType proof (mkConst ``True)
      Term.synthesizeSyntheticMVarsNoPostponing
      Meta.mkLambdaFVars xs (← instantiateMVars body)
    Term.synthesizeSyntheticMVarsNoPostponing
    return (← instantiateMVars type, ← instantiateMVars value)
  liftCoreM <| addDecl <| .thmDecl {
    name := name, levelParams := [], type := type, value := value
  }
