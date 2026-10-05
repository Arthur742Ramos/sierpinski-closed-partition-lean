module

public import Lean.Environment

/-! Export the complete raw expression representation of selected theorem types.
The verifier compares the two outputs byte for byte in separate processes. -/

@[expose] public section

open Lean

def main (args : List String) : IO Unit := do
  let [moduleName] := args | throw <| IO.userError "Expected one module name"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := moduleName.toName }] {}
    (level := .exported)
  for name in #[`Sierpinski.exists_eq_univ_of_nat_closed_partition,
      `Sierpinski.exists_eq_univ_of_countable_closed_partition,
      `Sierpinski.continuous_choice_eq_one] do
    let some info := env.find? name | throw <| IO.userError s!"Missing declaration: {name}"
    IO.println s!"RAW TYPE {name}"
    IO.println (reprStr info.levelParams)
    IO.println (reprStr info.type)
