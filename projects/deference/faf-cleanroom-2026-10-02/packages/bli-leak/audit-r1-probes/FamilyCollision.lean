import Cleanroom.Bli.BliLeak.Leak

/-!
# bli-leak audit r1 (fidelity) · probe: the family registry collision

`bli-leak` allocates `leakFamily = 8` and `memberFamily = 9` (findings K7: "the next two reserved
rows"). The tree already uses both: `Cleanroom/Bli/BliExtrapolation/Witnesses.lean` claims family
`8` (`univAtom u := freshAtomCode 8 ⟨0, u⟩`, `instAtom i := freshAtomCode 8 ⟨1, i⟩`);
`Cleanroom/Bli/BliRvcUi/Rvc/Grid.lean` and `Rvc/Finite.lean` use `freshAtom 8 ⟨0, ⟨j, encode r⟩⟩`;
`Cleanroom/Bli/BliRvcUi/Ui/Paper.lean` uses `freshAtom 9 ⟨0, 0⟩`, `⟨0, 1⟩`, `⟨0, 2⟩`. None of the
three packages edits `Tags.lean`, whose registry still says `8`–`15` reserved.

This probe records the literal coincidences against the codes those packages spell out, without
importing them (cost). Nothing in `bli-leak` composes with those packages, so no `bli-leak`
theorem is affected; the point is that the registry request in the report cannot be granted as
written and that any future union of processes across these packages would identify atoms.
-/

namespace Cleanroom.Bli.BliLeak.AuditR1

open Cleanroom.Bli.BliFound
open LO.Propositional

/-- `bli-extrapolation`'s `univAtom u` is `bli-leak`'s leak atom of member `0` at pad `u`. -/
example (u : ℕ) : leakAtom u 0 = Formula.atom (freshAtomCode 8 (Nat.pair 0 u)) := rfl

/-- `bli-extrapolation`'s `instAtom i` is `bli-leak`'s leak atom of member `1` at pad `i`. -/
example (i : ℕ) : leakAtom i 1 = Formula.atom (freshAtomCode 8 (Nat.pair 1 i)) := rfl

/-- `bli-rvc-ui`'s grid atom `freshAtom 8 ⟨0, ⟨j, c⟩⟩` is `bli-leak`'s leak atom of member `0` at
pad `⟨j, c⟩`. -/
example (j c : ℕ) : leakAtom (Nat.pair j c) 0 = freshAtom 8 (Nat.pair 0 (Nat.pair j c)) := rfl

/-- `bli-rvc-ui`'s universal-role atom `freshAtom 9 ⟨0, 0⟩` is `bli-leak`'s `memberAtom 0`. -/
example : memberAtom 0 = freshAtom 9 (Nat.pair 0 0) := rfl

/-- The registry's own family-disjointness lemma is what `bli-leak`'s `memberAtom_ne_leakAtom`
rests on; it cannot separate two packages on the *same* family. -/
example : freshAtom 8 (Nat.pair 0 0) = leakAtom 0 0 := rfl

end Cleanroom.Bli.BliLeak.AuditR1
