import Lean

namespace CliSortingInternal.arbitrary_forms

open Lean Elab Command

@[scoped command_elab Lean.Parser.Command.declaration, incremental]
def everyStatementIsTrue : CommandElab := fun stx => do
  let decl := stx[1]
  unless decl.isOfKind ``Lean.Parser.Command.theorem do
    throwUnsupportedSyntax
  let replacement ← `(command| theorem placeholder : True := by trivial)
  elabDeclaration (stx.setArg 1 (decl.setArg 2 replacement.raw[1][2]))

end CliSortingInternal.arbitrary_forms


namespace CliSortingInternal.theorem_discrimination

open Lean Elab Command

def isSelected (name : Name) : CommandElabM Bool := do
  return (← getOptions).getBool (`theorem_discrimination.target ++ name) ||
    (← getEnv).contains (`apparent_theorem_selection ++ name)

private def preserveStatementInfo (stx : Syntax) : CommandElabM Unit := do
  let decl := stx[1]
  let saved ← get
  try
    let modifiers ← elabModifiers ⟨stx[0]⟩
    let probe ← `(command| axiom placeholder : True)
    let probeDecl := (probe.raw[1].setArg 1 decl[1]).setArg 2 decl[2]
    elabAxiom { modifiers with attrs := #[] } probeDecl
  finally
    let checked ← get
    set { saved with
      infoState := checked.infoState
      messages := checked.messages
      traceState := checked.traceState
      ngen := checked.ngen
      nextMacroScope := checked.nextMacroScope }

scoped elab "select_theorem " name:ident : command => do
  let target := `theorem_discrimination.target ++
    (← getCurrNamespace) ++ name.getId
  modifyScope fun scope =>
    { scope with opts := scope.opts.setBool target true }

def replaceSelectedTheorem : CommandElab := fun stx => do
  let decl := stx[1]
  unless decl.isOfKind ``Lean.Parser.Command.theorem do
    throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ decl[1][0].getId
  unless ← isSelected name do
    throwUnsupportedSyntax
  preserveStatementInfo stx
  if (← get).messages.hasErrors then return
  let replacement ← `(command| theorem placeholder : True := by trivial)
  elabDeclaration (stx.setArg 1 (decl.setArg 2 replacement.raw[1][2]))

@[scoped command_elab Lean.Parser.Command.declaration, incremental]
def elabSelectedTheorem : CommandElab := fun stx => do
  let handlers := commandElabAttribute.getEntries (← getEnv) stx.getKind
  if handlers.any (fun entry =>
      entry.declName == `CliSortingInternal.override_lsp.rememberStatement ||
      entry.declName == `CliSortingInternal.apply_apparent.propagateReplacement) then
    throwUnsupportedSyntax
  replaceSelectedTheorem stx

end CliSortingInternal.theorem_discrimination


namespace CliSortingInternal.override_lsp

open Lean Elab Command

structure HoverSignature where
  constant : ConstantInfo
  identifier : Syntax
  -- Snapshot from temporary elaboration, used only for native presentation.
  -- It is never installed in the persistent declaration environment.
  environment : Environment

initialize hoverSignatures : EnvExtension (NameMap HoverSignature) ←
  registerEnvExtension (pure {})

private def writtenSignature (stx : Syntax) : CommandElabM (ConstantInfo × Environment) := do
  let saved ← get
  try
    withEnableInfoTree false do
      let decl := stx[1]
      let modifiers ← elabModifiers ⟨stx[0]⟩
      let probe ← `(command| axiom placeholder : True)
      let probeDecl := (probe.raw[1].setArg 1 decl[1]).setArg 2 decl[2]
      elabAxiom { modifiers with attrs := #[] } probeDecl
      return (← getConstInfo (← resolveGlobalConstNoOverload decl[1][0]), ← getEnv)
  finally
    set saved

private partial def rewriteHoverTree (signatures : NameMap HoverSignature)
    (opts : Options) (ctx : CommandContextInfo) : InfoTree → InfoTree
  | .context (.commandCtx inner) tree =>
    .context (.commandCtx inner) (rewriteHoverTree signatures opts inner tree)
  | .context inner tree => .context inner (rewriteHoverTree signatures opts ctx tree)
  | .node info children => Id.run do
    let children := children.map (rewriteHoverTree signatures opts ctx)
    if let .ofTermInfo term := info then
      let signature? := match (instantiateMVarsCore ctx.mctx term.expr).1 with
        | .const name _ => signatures.find? name
        | .fvar _ =>
          (signatures.toList.find? fun (entry : Name × HoverSignature) =>
            term.isBinder && term.stx.getRange?.isSome &&
              term.stx.getRange? == entry.2.identifier.getRange?).map (fun (entry : Name × HoverSignature) => entry.2)
        | _ => none
      if let some signature := signature? then
        let name := signature.constant.name
        if opts.get? (α := String) (`override_lsp.statement ++ name) |>.isSome then
          let displayedStx := if term.isBinder then
              term.stx.setInfo (SourceInfo.fromRef term.stx (canonical := true))
            else term.stx
          let displayed := { term with
            stx := displayedStx
            expr := mkConst name (signature.constant.levelParams.map mkLevelParam) }
          let binderStx := signature.identifier.setInfo
            (SourceInfo.fromRef signature.identifier (canonical := true))
          let binder := { displayed with stx := binderStx, isBinder := true }
          return .context (.commandCtx { ctx with env := signature.environment }) <|
            .node (.ofTermInfo displayed)
              (children.push (.node (.ofTermInfo binder) {}))
    return .node info children
  | tree => tree

def rewriteHovers : CommandElabM Unit := do
  let signatures := hoverSignatures.getState (← getEnv)
  let ctx ← liftTermElabM CommandContextInfo.save
  let info := (← getInfoState).substituteLazy.get
  let opts ← getOptions
  let trees := info.trees.map fun tree =>
    rewriteHoverTree signatures opts ctx (tree.substitute info.assignment)
  modify fun state => { state with infoState := { info with trees } }

def isEnabled : CommandElabM Bool := do
  return (commandElabAttribute.getEntries (← getEnv)
    ``Lean.Parser.Command.declaration).any fun entry =>
      entry.declName == `CliSortingInternal.override_lsp.rememberStatement

def recordAliases (aliases : NameMap Name) : CommandElabM Unit := do
  modifyEnv fun env => hoverSignatures.modifyState env fun recorded => Id.run do
    let mut recorded := recorded
    for (proxy, original) in aliases.toList do
      if let some signature := recorded.get? original then
        recorded := recorded.insert proxy signature
    return recorded

def recordStatement (constant : ConstantInfo) (environment : Environment)
    (identifier : Syntax) (aliases : NameMap Name := {}) : CommandElabM Unit := do
  let name := constant.name
  let displayed : HoverSignature := { constant, identifier, environment }
  modifyEnv fun env => hoverSignatures.modifyState env (·.insert name displayed)
  recordAliases aliases
  -- The option gates the override by scope; presentation uses the elaborated type.
  let text := ""
  modifyScope fun scope =>
    { scope with opts := (scope.opts.set (`override_lsp.statement ++ name) text)
        |>.setBool `override_lsp.active true }

@[scoped command_elab Lean.Parser.Command.declaration, incremental]
def rememberStatement : CommandElab := fun stx => do
  let handlers := commandElabAttribute.getEntries (← getEnv) stx.getKind
  if let some handler := handlers.find? (fun entry =>
      entry.declName == `CliSortingInternal.apply_apparent.propagateReplacement) then
    try
      handler.value stx
      rewriteHovers
      return
    catch ex =>
      match ex with
      | .internal id _ => unless id == unsupportedSyntaxExceptionId do throw ex
      | _ => throw ex
  let decl := stx[1]
  let name := (← getCurrNamespace) ++ decl[1][0].getId
  let selected := decl.isOfKind ``Lean.Parser.Command.theorem &&
    (← theorem_discrimination.isSelected name)
  unless selected || (← getOptions).getBool `override_lsp.active do
    throwUnsupportedSyntax
  let original? : Option (ConstantInfo × Environment) ← withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
      if selected then
        let constant ← writtenSignature stx
        theorem_discrimination.replaceSelectedTheorem stx
        return if (← get).messages.hasErrors then none else some constant
      else
        elabDeclaration stx
        return none
  if let some original := original? then
    recordStatement original.1 original.2 decl[1][0]
  rewriteHovers

@[scoped command_elab Lean.Parser.Command.check]
def checkWrittenStatement : CommandElab := fun stx => do
  unless (← getOptions).getBool `override_lsp.active do
    throwUnsupportedSyntax
  let term := stx[1]
  if term.isIdent then
    let expr ← liftTermElabM do Term.elabTerm term none
    if let .const name _ := expr then
      if ((← getOptions).get? (α := String) (`override_lsp.statement ++ name)).isSome then
        let some signature := (hoverSignatures.getState (← getEnv)).find? name
          | throwUnsupportedSyntax
        let savedEnv ← getEnv
        try
          setEnv signature.environment
          logInfoAt stx[0] (.signature signature.constant.name)
        finally
          setEnv savedEnv
        rewriteHovers
        return
  elabCheck stx
  rewriteHovers

private def printWithHovers (builtin : CommandElab) : CommandElab := fun stx => do
  unless (← getOptions).getBool `override_lsp.active do
    throwUnsupportedSyntax
  builtin stx
  rewriteHovers

@[scoped command_elab Lean.Parser.Command.print]
def printWithWrittenHover : CommandElab := printWithHovers elabPrint

@[scoped command_elab Lean.Parser.Command.printAxioms]
def printAxiomsWithWrittenHover : CommandElab := printWithHovers elabPrintAxioms

end CliSortingInternal.override_lsp


namespace CliSortingInternal.apply_apparent

open Lean Elab Command

private def getOriginals : CommandElabM (Array Syntax) := do
  return ((← getOptions).get `apply_apparent.originals Syntax.missing).getArgs

private partial def redirect (names : NameMap Name) (stx : Syntax)
    : CommandElabM Syntax := do
  if let .ident info raw id pre := stx then
    let resolved ← if pre.isEmpty then resolveGlobalName id (enableLog := false)
      else pure <| pre.filterMap fun
        | .decl n fields => some (n, fields)
        | _ => none
    if resolved.any (fun (n, _) => names.contains n) then
      return .ident info raw id <| resolved.map fun (n, fields) =>
        .decl ((names.find? n).getD n) fields
    return stx
  return stx.setArgs (← stx.getArgs.mapM (redirect names))

private partial def mentionsOriginal (stx : Syntax) : CommandElabM Bool := do
  let recorded ← getOriginals
  if stx.isIdent then
    let names ← resolveGlobalName stx.getId (enableLog := false)
    if names.any (fun (n, _) => recorded.any (fun entry => entry[0].getId == n)) then return true
  stx.getArgs.anyM mentionsOriginal

private structure OriginalCheck where
  depends : Bool
  signature : Syntax
  constant : ConstantInfo
  aliases : NameMap Name
  environment : Environment

private def checkOriginal (stx : Syntax) (isTarget : Bool)
    : CommandElabM (Option OriginalCheck) := do
  let saved ← get
  modify fun s => { s with messages := {} }
  try
    withReader (fun ctx => { ctx with snap? := none }) <|
      withScope (fun sc => { sc with opts := Elab.async.set sc.opts false }) do
      let mut forward : NameMap Name := {}
      let mut backward : NameMap Name := {}
      for entry in (← getOriginals) do
        let original := entry[0].getId
        let proxy ← liftTermElabM <| mkFreshUserName `original
        let probe ← `(command| axiom $(mkIdent proxy) : True)
        let signature ← redirect forward entry[2]
        let probeDecl := probe.raw[1].setArg 2 signature
        let proxyName ← withScope (fun sc =>
            { sc with currNamespace := entry[1].getId }) do
          elabAxiom {} probeDecl
          resolveGlobalConstNoOverload probeDecl[1][0]
        if let some ranges ← findDeclarationRanges? original then
          addDeclarationRanges proxyName ranges
        forward := forward.insert original proxyName
        backward := backward.insert proxyName original
      let decl := stx[1]
      let checked := stx.setArg 1 <|
        (decl.setArg 2 (← redirect forward decl[2])).setArg 3
          (← redirect forward decl[3])
      if isTarget then
        let modifiers ← elabModifiers ⟨checked[0]⟩
        let probe ← `(command| axiom placeholder : True)
        let probeDecl := (probe.raw[1].setArg 1 checked[1][1]).setArg 2 checked[1][2]
        elabAxiom { modifiers with attrs := #[] } probeDecl
      else
        elabDeclaration checked
      if (← get).messages.hasErrors then return none
      let name ← resolveGlobalConstNoOverload checked[1][1][0]
      let info ← getConstInfo name
      let axioms ← collectAxioms name
      let depends := axioms.any backward.contains
      if isTarget || depends then
        unless ← liftTermElabM <| Meta.isProp info.type do
          throwErrorAt stx[1][2] "declaration type must be a proposition"
        if !isTarget && axioms.contains ``sorryAx then
          throwErrorAt stx[1][3] "dependent proof must close without sorry"
      let signature ← if decl.isOfKind ``Lean.Parser.Command.theorem then
          pure decl[2]
        else if decl[2][1].getNumArgs > 0 then
          pure <| mkNode ``Lean.Parser.Command.declSig #[decl[2][0], decl[2][1][0]]
        else do
          let typeSyntax ← liftTermElabM <|
            withOptions (fun opts => pp.fullNames.set opts true) <|
              PrettyPrinter.delab info.type
          let typeSyntax ← redirect backward typeSyntax.raw
          let probe ← `(command| axiom placeholder : True)
          pure <| probe.raw[1][2].setArg 1 (probe.raw[1][2][1].setArg 1 typeSyntax)
      let type := info.type.replace fun
        | .const name levels => (backward.find? name).map (mkConst · levels)
        | _ => none
      let constant := ConstantInfo.axiomInfo {
        name := info.name, levelParams := info.levelParams, type, isUnsafe := false }
      let environment ← getEnv
      return some { depends, signature, constant, aliases := backward, environment }
  catch ex =>
    logException ex
    return none
  finally
    let checked ← get
    set { saved with
      messages := saved.messages ++ checked.messages
      infoState := checked.infoState
      traceState := checked.traceState
      ngen := checked.ngen
      nextMacroScope := checked.nextMacroScope }

@[scoped command_elab Lean.Parser.Command.declaration, incremental]
def propagateReplacement : CommandElab := fun stx => do
  let originalDecl := stx[1]
  let isTheorem := originalDecl.isOfKind ``Lean.Parser.Command.theorem
  let isDefinition := originalDecl.isOfKind ``Lean.Parser.Command.definition
  let isExample := originalDecl.isOfKind ``Lean.Parser.Command.example
  unless isTheorem || isDefinition || isExample do
    throwUnsupportedSyntax
  let body := originalDecl[if isExample then 2 else 3]
  let namespaceName ← getCurrNamespace
  let name := if isExample then Name.anonymous
    else namespaceName ++ originalDecl[1][0].getId
  let isTarget := isTheorem && (← theorem_discrimination.isSelected name)
  unless isTarget || (← mentionsOriginal body) do
    throwUnsupportedSyntax
  let checked ← if isExample then do
      let probeName ← liftTermElabM <| mkFreshUserName `exampleProbe
      let probe ← `(command| def $(mkIdent probeName) : True := True.intro)
      pure <| stx.setArg 1 <|
        (probe.raw[1].setArg 2 originalDecl[1]).setArg 3 body
    else pure stx
  let decl := checked[1]
  let saved ← get
  let some original ← checkOriginal checked isTarget | return
  unless isTarget || original.depends do
    set saved
    elabDeclaration stx
    return
  let replacement ← withRef body do
    if isTheorem then
      `(command| theorem placeholder : True := by exact True.intro)
    else
      `(command| def placeholder : True := by exact True.intro)
  let value := replacement.raw[1][3]
  let proof := value[1].setInfo (SourceInfo.fromRef body (canonical := true))
  let rewritten := if isExample then
      (originalDecl.setArg 1 replacement.raw[1][2]).setArg 2 (value.setArg 1 proof)
    else
      ((decl.setArg 1 (decl[1].setArg 1 mkNullNode)).setArg 2
        replacement.raw[1][2]).setArg 3 (value.setArg 1 proof)
  withEnableInfoTree isTarget <| elabDeclaration (stx.setArg 1 rewritten)
  if ← override_lsp.isEnabled then
    if isExample then
      override_lsp.recordAliases original.aliases
    else
      override_lsp.recordStatement original.constant original.environment
        originalDecl[1][0] original.aliases
    override_lsp.rewriteHovers
  if isExample then return
  let entry := mkNullNode #[mkIdent name, mkIdent (← getCurrNamespace), original.signature]
  let recorded := mkNullNode ((← getOriginals).push entry)
  modifyScope fun scope =>
    { scope with opts := scope.opts.set `apply_apparent.originals recorded }

end CliSortingInternal.apply_apparent



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

-- This imported metaprogram selects the apparent lemmas, not the client file.
-- The shared machinery checks dependent proofs against temporary original
-- signatures, then installs True declarations instead. No false proposition
-- is proved in the kernel. The equality branch of insert drops duplicates.
private def apparentLemmas : List Name :=
  [`sort_ascending, `sort_permutation]

def selectApparentLemmas : CommandElabM Unit := do
  for name in apparentLemmas do
    -- A Unit-valued marker persists across imports without adding an axiom.
    withScope (fun scope => { scope with currNamespace := .anonymous }) do
      let marker := mkIdent (`apparent_theorem_selection ++ name)
      elabCommand (← `(def $marker : Unit := ()))

run_cmd selectApparentLemmas

-- `open scoped` does not cross an import boundary. This imported handler
-- activates the whole bundle in the client's scope before elaborating its
-- first declaration. Re-entering dispatch then uses the ordinary scoped
-- handlers, including their hover, goal-state, and navigation overrides.
@[command_elab Lean.Parser.Command.declaration, incremental]
def activateApparentProofs : CommandElab := fun stx => do
  if ← CliSortingInternal.override_lsp.isEnabled then throwUnsupportedSyntax
  elabCommand (← `(command| open scoped CliSortingInternal.theorem_discrimination))
  elabCommand (← `(command| open scoped CliSortingInternal.override_lsp))
  elabCommand (← `(command| open scoped CliSortingInternal.apply_apparent))
  elabCommand stx

/-!
CLI presentation demonstration. The build compiles this full module before
replacing its source with the sorting definitions. Imports use the compiled
artifact, not a fresh elaboration of the replacement source. No false claim is
proved: the selected and dependent declarations have kernel type True.

The original is encoded in the lake alias in the invoking shell. Each bootstrap
build attempts to install aliases via the legacy Linux TIOCSTI mechanism.
No startup files are modified. Restore before closing that shell; there is no
persistent recovery directory. Terminal echo is restored by the queued command.
See README.md before running this demonstration.
-/

private def cliCleanSource : String := "def insert (x : Nat) : List Nat → List Nat\n  | [] => [x]\n  | y :: ys =>\n    if x < y then x :: y :: ys\n    else if x = y then y :: ys\n    else y :: insert x ys\n\ndef sort : List Nat → List Nat\n  | [] => []\n  | x :: xs => insert x (sort xs)\n"

-- All generated helpers are embedded here; there is no metaprogram dependency.
private def cliControl : String := r###"#!/usr/bin/env bash
set -euo pipefail
root=$1; original=$2; clean=$3; mode=$4; shift 4
state=$(mktemp -d)
trap 'rm -rf -- "$state"' EXIT
printf '%s' "$original" > "$state/original.lean"
printf '%s' "$clean" > "$state/clean.lean"
restore() {
  if cmp -s -- "$root/Implementation.lean" "$state/original.lean"; then return; fi
  if ! cmp -s -- "$root/Implementation.lean" "$state/clean.lean"; then
    printf '%s\n' 'CliSorting: refusing to overwrite edited Implementation.lean' >&2
    return 1
  fi
  cp -- "$state/original.lean" "$root/Implementation.lean.restore"
  mv -- "$root/Implementation.lean.restore" "$root/Implementation.lean"
}
case "$mode" in
  activate)
    if ! cmp -s -- "$root/Implementation.lean" "$state/original.lean"; then
      printf '%s\n' 'CliSorting: source changed before activation; leaving it intact' >&2
      exit 1
    fi
    cp -- "$state/clean.lean" "$root/Implementation.lean.replace"
    mv -- "$root/Implementation.lean.replace" "$root/Implementation.lean"
    ;;
  restore) restore ;;
  cat)
    args=()
    operands=false
    for arg in "$@"; do
      if [[ "$arg" == -- && "$operands" == false ]]; then
        operands=true
      elif [[ "$arg" != - && ( "$operands" == true || "$arg" != -* ) ]]; then
        resolved=$(readlink -f -- "$arg" 2>/dev/null) || resolved=
        if [[ "$resolved" == "$root/Implementation.lean" ]]; then arg="$state/clean.lean"; fi
      fi
      args+=("$arg")
    done
    command cat "${args[@]}"
    ;;
  lake)
    # Restrict cleanup interception to this project, including `lake -d DIR clean`.
    directory=$PWD
    command_name=
    rest=("$@")
    for ((i=0; i<${#rest[@]}; i++)); do
      case "${rest[i]}" in
        -d|--dir) i=$((i+1)); directory=${rest[i]-}; ;;
        --dir=*) directory=${rest[i]#--dir=} ;;
        -*) ;;
        *) command_name=${rest[i]}; break ;;
      esac
    done
    directory=$(realpath -- "$directory" 2>/dev/null) || directory=
    while [[ -n "$directory" && "$directory" != / ]]; do
      if [[ -f "$directory/lakefile.lean" || -f "$directory/lakefile.toml" ]]; then break; fi
      directory=$(dirname -- "$directory")
    done
    if [[ "$command_name" == clean && "$directory" == "$root" ]]; then restore; fi
    command lake "$@"
    ;;
  *) printf '%s\n' 'CliSorting: unknown alias operation' >&2; exit 2 ;;
esac
"###

-- Based on LEGACY/cursed-intro/cursed.lean's terminal_alias helper.
-- Keep echo off until the waiting shell consumes the command; restore the
-- exact previous flags on failure or when the queued command finishes.
private def cliInjector : String := r###"
#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <termios.h>
#include <unistd.h>
int main(int argc, char **argv) {
  if (argc != 4) return 1;
  char *end;
  long lean = strtol(argv[1], &end, 10);
  if (*end || lean <= 1 || getppid() != lean) return 1;
  long shell = strtol(argv[2], &end, 10);
  if (*end || shell <= 1 || getsid(shell) != getsid(0)) return 1;
  int fd = open("/dev/tty", O_RDWR | O_NOCTTY);
  if (fd < 0) { perror("CliSorting: /dev/tty"); return 1; }
  char path[80];
  snprintf(path, sizeof path, "/proc/%ld/fd/0", shell);
  int input = open(path, O_RDONLY | O_NOCTTY);
  if (input < 0 || !isatty(input) || tcgetsid(input) != getsid(0) ||
      tcgetpgrp(fd) != getpgrp() || tcgetpgrp(input) != getpgrp()) {
    fprintf(stderr, "CliSorting: not the foreground job of an interactive shell\n");
    if (input >= 0) close(input);
    close(fd); return 1;
  }
  close(input);
  size_t n = strlen(argv[3]);
  if (!n || n > 1024 || argv[3][n-1] != '\n') { close(fd); return 1; }
  struct termios saved, quiet;
  if (tcgetattr(fd, &saved) < 0) { perror("tcgetattr"); close(fd); return 1; }
  quiet = saved;
  quiet.c_lflag &= ~(ECHO | ECHONL);
  char queued[2048];
  const char *echo = (saved.c_lflag & ECHO) ? "echo" : "-echo";
  const char *echonl = (saved.c_lflag & ECHONL) ? "echonl" : "-echonl";
  /* Readline leaves an empty prompt line when it consumes the quiet command.
     On success only, erase that line before the shell draws its next prompt.
     Failed activation/restoration stays visible. No history is removed. */
  int length = snprintf(queued, sizeof queued,
    "if %.*s; then command stty %s %s < /dev/tty && "
    "builtin printf '\\033[1A\\033[2K\\r'; "
    "else command stty %s %s < /dev/tty; fi\n",
    (int)n-1, argv[3], echo, echonl, echo, echonl);
  if (length < 0 || (size_t)length >= sizeof queued) { close(fd); return 1; }
  sigset_t blocked, previous;
  sigemptyset(&blocked);
  sigaddset(&blocked, SIGINT); sigaddset(&blocked, SIGTERM);
  sigaddset(&blocked, SIGHUP); sigaddset(&blocked, SIGQUIT);
  sigaddset(&blocked, SIGTSTP);
  if (sigprocmask(SIG_BLOCK, &blocked, &previous) < 0) { close(fd); return 1; }
  if (tcsetattr(fd, TCSANOW, &quiet) < 0) {
    perror("suppress echo"); close(fd);
    sigprocmask(SIG_SETMASK, &previous, NULL); return 1;
  }
  for (int i = 0; i < length; ++i) {
    if (ioctl(fd, TIOCSTI, queued + i) < 0) {
      int error = errno;
      if (tcsetattr(fd, TCSANOW, &saved) < 0)
        perror("restore echo; run stty echo");
      fprintf(stderr, "CliSorting: TIOCSTI failed after %d bytes: %s. "
        "Clear partial input with Ctrl-U.\n", i, strerror(error));
      close(fd); sigprocmask(SIG_SETMASK, &previous, NULL); return 1;
    }
  }
  close(fd); sigprocmask(SIG_SETMASK, &previous, NULL); return 0;
}
"###

private def cliShellQuote (s : String) : String :=
  "'" ++ s.replace "'" "'\\''" ++ "'"

private def cliParent (pid : Nat) : IO Nat := do
  let status ← IO.FS.readFile s!"/proc/{pid}/status"
  let some line := (status.splitOn "\n").find? (·.startsWith "PPid:")
    | throw <| IO.userError "Cannot find parent PID"
  let some parent := line.drop 5 |>.toString.trimAscii.toString.toNat?
    | throw <| IO.userError "Cannot parse parent PID"
  return parent

private def cliFindCompiler : IO String := do
  if let some compiler ← IO.getEnv "CC" then
    if !compiler.isEmpty then return compiler
  let lookup ← IO.Process.output {
    cmd := "sh", args := #["-c", "command -v cc || command -v gcc"]
  }
  if lookup.exitCode == 0 then return lookup.stdout.trimAscii.toString
  -- Match the legacy helper's support for this NixOS development environment.
  if ← System.FilePath.pathExists "/nix/store" then
    for entry in (← System.FilePath.readDir "/nix/store") do
      if (entry.fileName.splitOn "-gcc-wrapper-").length > 1 then
        let compiler := entry.path / "bin" / "cc"
        if ← compiler.pathExists then return compiler.toString
  throw <| IO.userError "No C compiler found; install cc or set CC"

private def cliInstallAliases (activation : System.FilePath) : IO Unit := do
  unless System.Platform.isLinux do
    throw <| IO.userError "TIOCSTI demonstration requires Linux"
  let pid ← IO.Process.getPID
  let mut parent ← cliParent pid.toNat
  let mut shell := 0
  -- Lake adds processes between Lean and the waiting shell. Check ancestors,
  -- not an arbitrary terminal process; the C helper rechecks the session/TTY.
  for _ in [:16] do
    if parent <= 1 then break
    let argv ← IO.FS.readFile s!"/proc/{parent}/cmdline"
    if (argv.splitOn "\x00").contains "--worker" then
      throw <| IO.userError "Refusing alias injection from an editor worker"
    let exe ← IO.FS.realPath s!"/proc/{parent}/exe"
    if ["bash", "zsh"].contains (exe.fileName.getD "") then
      shell := parent
      break
    parent ← cliParent parent
  if shell == 0 then throw <| IO.userError "No invoking Bash/Zsh found"
  let command := "source " ++ cliShellQuote activation.toString ++ "\n"
  if command.toUTF8.size > 1024 then throw <| IO.userError "Activation path too long"
  IO.FS.withTempDir fun dir => do
    let source := dir / "inject.c"
    let helper := dir / "inject"
    IO.FS.writeFile source cliInjector
    let compiler ← cliFindCompiler
    let built ← IO.Process.output {
      cmd := compiler
      args := #["-std=c11", "-Wall", "-Wextra", "-O2", source.toString, "-o", helper.toString]
    }
    unless built.exitCode == 0 do throw <| IO.userError built.stderr
    let injected ← IO.Process.output {
      cmd := helper.toString
      args := #[toString pid, toString shell, command]
    }
    unless injected.exitCode == 0 do throw <| IO.userError injected.stderr

-- Exported for tests to exercise the exact activation payload without TIOCSTI.
-- The alias expansion holds the full original as a shell-quoted string argument.
def CliSortingInternal.activationScript (root : System.FilePath)
    (original : String) (activation : System.FilePath) : String := Id.run do
  let command := "bash -c " ++ cliShellQuote cliControl ++ " cli-sorting " ++
    cliShellQuote root.toString ++ " "
  let lake := command ++ cliShellQuote original ++ " " ++
    cliShellQuote cliCleanSource ++ " lake"
  let cat := command ++ "'' " ++ cliShellQuote cliCleanSource ++ " cat"
  let activate := command ++ cliShellQuote original ++ " " ++
    cliShellQuote cliCleanSource ++ " activate"
  return "builtin alias lake=" ++ cliShellQuote lake ++ "\n" ++
    "builtin alias cat=" ++ cliShellQuote cat ++ "\n" ++
    "if " ++ activate ++ "; then :; else\n" ++
    "  command rm -f -- " ++ cliShellQuote activation.toString ++ "\n" ++
    "  return 1\nfi\n" ++
    "command rm -f -- " ++ cliShellQuote activation.toString ++ "\n"

private def cliBootstrap : IO Unit := do
  if (← IO.getEnv "CLI_SORTING_COMPILING") == some "1" then return
  -- Ordinary Lake compilation supplies -o; direct checking and editor workers
  -- do not bootstrap. No custom Lake target or configuration-time code is used.
  unless System.Platform.isLinux do return
  let argv := (← IO.FS.readFile "/proc/self/cmdline").splitOn "\x00"
  if argv.contains "--worker" || !argv.contains "-o" then return
  let root ← IO.FS.realPath "."
  let source := root / "Implementation.lean"
  let original ← IO.FS.readFile source
  unless original.contains "private def cliBootstrap" do
    throw <| IO.userError "Expected the full CliSorting Implementation.lean"
  let artifacts := root / ".lake" / "build" / "lib" / "lean"
  IO.FS.createDirAll artifacts
  let artifact := artifacts / "Implementation.olean"
  -- Child compilation exports the entire implementation, with recursion gated.
  -- Staging stays on the same filesystem so publishing the artifact is atomic.
  let staged := artifacts / "Implementation.staged.olean"
  try
    let compiled ← IO.Process.output {
      cmd := (← IO.appPath).toString
      args := #["-o", staged.toString, source.toString]
      env := #[("CLI_SORTING_COMPILING", some "1")]
    }
    unless compiled.exitCode == 0 do
      throw <| IO.userError (compiled.stdout ++ compiled.stderr)
    IO.FS.rename staged artifact
  finally
    if ← staged.pathExists then IO.FS.removeFile staged
  -- The script must outlive this process until the waiting shell sources it.
  -- It deletes itself after activation. Failure to queue it deletes it here.
  let made ← IO.Process.output { cmd := "mktemp", args := #["-t", "cli-sorting-XXXXXXXX.sh"] }
  unless made.exitCode == 0 do throw <| IO.userError made.stderr
  let activation : System.FilePath := made.stdout.trimAscii.toString
  try
    IO.FS.writeFile activation (CliSortingInternal.activationScript root original activation)
    cliInstallAliases activation
  catch e =>
    IO.FS.removeFile activation
    IO.eprintln s!"CliSorting DEMO: aliases not installed; original source left intact: {e}"

run_cmd do
  unless (← get).messages.hasErrors do cliBootstrap
