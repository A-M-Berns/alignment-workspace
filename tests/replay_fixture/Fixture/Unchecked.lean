/-
A theorem of `False` pushed into the environment with `doCheck := false`, after
`lean4checker`'s own `AddFalse` fixture. The elaborator never asks the kernel
about it, so this file *builds*. Replaying it must fail.

Nothing imports this. It exists so `tests/replay.py` can assert, on every run,
that the checker still rejects a declaration the kernel would not accept —
which is the property that would be lost silently if a toolchain bump turned
`leanchecker` into a no-op for this repository's invocation of it.

If this file stops elaborating after a toolchain bump, that is the expected
maintenance cost of a live fixture and not a mystery: the metaprogramming below
reaches into `Lean.Environment`, which carries no stability promise. Repair it
against the upstream fixture rather than deleting it.
-/
import Lean.Elab.Term

namespace Fixture.Unchecked

open Lean in
run_elab
  modifyEnv fun env => Id.run do
    let decl := .thmDecl { name := `Fixture.Unchecked.falseThm, levelParams := [], type := .const ``False [], value := .const ``False [] }
    let .ok env := env.addDeclCore (doCheck := false) 0 decl none |
      let _ : Inhabited Environment := ⟨env⟩
      unreachable!
    env

#print axioms Fixture.Unchecked.falseThm

end Fixture.Unchecked
