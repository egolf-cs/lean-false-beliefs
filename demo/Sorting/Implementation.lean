import Metaprograms

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
  if ← Metaprograms.override_lsp.isEnabled then throwUnsupportedSyntax
  elabCommand (← `(command| open scoped Metaprograms.theorem_discrimination))
  elabCommand (← `(command| open scoped Metaprograms.override_lsp))
  elabCommand (← `(command| open scoped Metaprograms.apply_apparent))
  elabCommand stx
