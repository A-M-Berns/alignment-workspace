import Cleanroom.Decision.DpReferentsCdt.ElhWitness

/-!
Audit probe (dp-referents-cdt, round 1, lens fidelity). Not imported by the library.

**Claim probed.** In `Elh.lean`'s rendering of Everitt–Leike–Hutter the action draw at a history is
`C(h)`, independent of the hidden state `s` (the disclosed variant, findings F13). A consequence the
package does not state: the action-evidential belief at the policy's act and the causal belief
coincide, `SAEDT(h, π h, e) = SCDT(h, e)` whenever `C(h)(π h) ≠ 0` — so the paper's SCDT ≠ SAEDT
contrast (its Examples 8 and 9) is not representable here; only SPEDT separates. At the root of the
two-round tree this is two rewrites of the package's own closed forms.
-/

open Cleanroom.Found.DpCoreTree
open Cleanroom.Decision.DpReferentsCdt

variable {A : Type} [Fintype A] [DecidableEq A] [Nonempty A] {ns ne : ℕ}

example (E : ElhEnv A ns ne) (C : Proc (Hist A ne) (fun _ => A) ℚ) (π : Hist A ne → A)
    (e : Fin ne) (ha : (C []).w (π []) ≠ 0) :
    saedtBelief E C 2 [] (π []) e = scdtBelief E C 2 π [] e := by
  rw [saedtBelief_two_root E C (π []) e ha, scdtBelief_two_root E C π e]
