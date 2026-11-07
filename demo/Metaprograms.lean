import Lean

namespace Metaprograms.arbitrary_forms

open Lean Elab Command

@[scoped command_elab Lean.Parser.Command.declaration, incremental]
def everyStatementIsTrue : CommandElab := fun stx => do
  let decl := stx[1]
  unless decl.isOfKind ``Lean.Parser.Command.theorem do
    throwUnsupportedSyntax
  let replacement ← `(command| theorem placeholder : True := by trivial)
  elabDeclaration (stx.setArg 1 (decl.setArg 2 replacement.raw[1][2]))

end Metaprograms.arbitrary_forms


namespace Metaprograms.theorem_discrimination

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
      entry.declName == `Metaprograms.override_lsp.rememberStatement ||
      entry.declName == `Metaprograms.apply_apparent.propagateReplacement) then
    throwUnsupportedSyntax
  replaceSelectedTheorem stx

end Metaprograms.theorem_discrimination


namespace Metaprograms.override_lsp

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
      entry.declName == `Metaprograms.override_lsp.rememberStatement

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
      entry.declName == `Metaprograms.apply_apparent.propagateReplacement) then
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

end Metaprograms.override_lsp


namespace Metaprograms.apply_apparent

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

end Metaprograms.apply_apparent

