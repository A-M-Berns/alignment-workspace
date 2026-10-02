import Cleanroom.Decision.DpSmokingLesion.Prop14E2a
import Cleanroom.Decision.DpSmokingLesion.Prop14E13

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# T4: Proposition 14 — the two consistent homes

[[dp-smoking-lesion-mandate]] T4 (load-bearing 3), source `sl-defensible-claims.md` S2 line 29.

* **(a) Only-if** (`prop14_only_if`, `prop14_only_if_masked`, `prop14_only_if_limit`): on any
  `O_d = ⊤` tree with cancer post-query independent of the draw, a state that is strictly
  (resp. masked at a self-model, limit) calibrated and satisfies (S2) is not recorded (resp.
  the self-model is not recorded) — Proposition 11's contrapositive, the direction the source
  calls Proposition 14's only-if. On `slOne` for every `C` (`prop14_only_if_slOne`).
* **(b)(c)** are `Prop14E2a.lean` (coverage failure) and `Prop14E13.lean` (action-veridicality
  failure); **(e)** the two homes separated at the SSC grades, as one theorem-pair naming the
  two trees (`prop14_two_homes`): E2a is honest at strict OC with (S2), not covered, and
  **screened** at both SSC grades; E13 is honest at strict OC with (S2), covered but not
  recorded, and (S2) **survives** at both SSC grades.
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

section onlyIf

variable {ι : Type} [DecidableEq ι] (C : Proc ι (fun _ => Bool) ℚ) (B : Tree TickleW ι (fun _ => Bool) ℚ)
  (d : ι) (s : ι → State TickleW ℚ)

/-- **Proposition 14, only-if (strict grade)**: at an `O_d = ⊤` point with cancer post-query
independent of the draw, a strictly calibrated state satisfying (S2) forces recording to fail
for `C` — (S2) is strict-consistent only through recording failure.
Source: `sl-defensible-claims.md` S2 ("(S1)+(S2)+(S3) is strict-, masked- and limit-consistent
for a procedure `C` **through, and only through, instantiations failing recording at `d`**");
dp-sl-012; mandate T4(a)
Kind: C
Fidelity: exact (recording form: `RecordsFor` for `C`; `O_d = ⊤`)
Hyps: (a) `PostQueryIndep C B d evK`; (a) `StrictOCAt`; (a) `S2` -/
theorem prop14_only_if (hK : PostQueryIndep C B d evK) (hs : StrictOCAt s slObs C B d)
    (h2 : S2 (s d)) : ¬ RecordsFor slObs slActEv C B d :=
  fun hrec => prop11_of_recordsFor C B d hrec hK s
    (hs (by rw [slObs_apply]; exact nu_univ_pos C B)) h2

/-- **Proposition 14, only-if (masked grade)**: a state strictly calibrated to a self-model
`C[d ↦ m]` and satisfying (S2) forces recording to fail **for the self-model**.
Source: `sl-defensible-claims.md` S2; dp-sl-2-043(b); mandate T4(a) ("resp. `¬ RecordsFor` for
`C[d↦m]`")
Kind: C
Fidelity: exact (recording form: for the self-model)
Hyps: (a) `PostQueryIndep` for `C[d ↦ m]`; (a) the strict clauses under the self-model; (a) `S2` -/
theorem prop14_only_if_masked (m : FinDistr ℚ Bool) (hK : PostQueryIndep (C.deviate d m) B d evK)
    (hcl : StrictClausesAt s slObs (C.deviate d m) B d) (h2 : S2 (s d)) :
    ¬ RecordsFor slObs slActEv (C.deviate d m) B d :=
  fun hrec => prop11_of_recordsFor (C.deviate d m) B d hrec hK s hcl h2

/-- **Proposition 14, only-if (limit grade)**.
Source: `sl-defensible-claims.md` S2; mandate T4(a)
Kind: C
Fidelity: exact
Hyps: (a) `PostQueryIndep`; (a) `LimitOCAt`; (a) `S2` -/
theorem prop14_only_if_limit (hK : PostQueryIndep C B d evK) (hs : LimitOCAt s slObs C B d)
    (h2 : S2 (s d)) : ¬ RecordsFor slObs slActEv C B d :=
  fun hrec => prop11_limit_of_recordsFor C B d hrec hK s hs h2

end onlyIf

/-- Proposition 14's only-if on the enumerated instantiation: since `slOne` records for every
procedure, no strictly calibrated state satisfies (S2) there — the shape-form statement of
T4(a).
Source: mandate T4(a) ("shape form on `slOne` … is enough for `core`")
Kind: C
Fidelity: exact on `slOne`
Hyps: none -/
theorem prop14_only_if_slOne (L : Lesion) (α β : ℚ) (C : Proc Unit (fun _ => Bool) ℚ)
    (s : Unit → State TickleW ℚ) (hs : StrictOCAt s slObs C (slOne L α β) ()) : ¬ S2 (s ()) :=
  prop11_slOne_strict L α β C s hs

/-- **Proposition 14, the two consistent homes separated at the SSC grades.** For every
procedure: on the reference class E2a (coverage failure) the strictly calibrated state satisfies
(S2), coverage fails, and **every** per-run or per-occurrence calibrated state violates (S2);
on the compulsion E13 (action-veridicality failure, label `q < 1`) the strictly calibrated state
satisfies (S2), coverage holds, recording fails, and that state is per-run and per-occurrence
calibrated — (S2) **survives** both SSC grades. Whether E13's realized-act description is a
legitimate v2 problem is open (L1 O2): the Lean states the tree, the reader judges.
Source: `sl-defensible-claims.md` S2 line 29 ("occurrence-conditioning … **screens R-a** … but
**not R-b**"); dp-sl-012; dp-core-046 ("the two consistent homes"); mandate T4(e)
Kind: L
Fidelity: exact (the two named trees at the mandate's numbers; "the two homes" as a claim about
every non-recording tree is not formalized — the general only-if is `prop14_only_if`); a
conjunction of the rows it cites, no new content (audit r1 adversarial N6)
Hyps: (a) `C(d)(smoke) < 1` for E13's clauses only (the E2a half holds for every `C`) -/
theorem prop14_two_homes (C : Proc Unit (fun _ => Bool) ℚ) :
    (S2 (calibratedState C e2a₀ Finset.univ (nu_univ_pos _ _)) ∧ ¬ Covers slObs C e2a₀ () ∧
      (∀ s : Unit → State TickleW ℚ, PerRunSSCAt s C e2a₀ () → ¬ S2 (s ())) ∧
      (∀ s : Unit → State TickleW ℚ, PerOccSSCAt s C e2a₀ () → ¬ S2 (s ()))) ∧
    ((C ()).w true < 1 →
     let s₀ : Unit → State TickleW ℚ := fun _ => calibratedState C e13₀ Finset.univ (nu_univ_pos _ _)
     S2 (s₀ ()) ∧ Covers slObs C e13₀ () ∧ ¬ RecordsFor slObs slActEv C e13₀ () ∧
      PerRunSSCAt s₀ C e13₀ () ∧ PerOccSSCAt s₀ C e13₀ ()) := by
  refine ⟨⟨e2a_S2_calibrated C, e2a_not_covers C, prop14_e2a_screened_perRun C,
    prop14_e2a_screened_perOcc C⟩, fun hq => ?_⟩
  obtain ⟨⟨h1, -, h3, h4, -⟩, -, h5, h6⟩ := prop14_e13_honest_all_grades C hq
  exact ⟨h1, h5, h6, h3, h4⟩

/-- **Proposition 14's only-if on the three non-recording catalogue trees**: each of
counterexample A, E2a and E13 has cancer post-query independent of the draw for every
procedure (`cexA_postQueryIndep`, `e2a_postQueryIndep`, `e13_postQueryIndep`), so the general
`prop14_only_if` applies — a strictly calibrated state with (S2) on any of them forces
recording to fail. With the per-tree `¬ RecordsFor` facts this makes "`Σ_SL(S1–S3)` is
consistent only through recording failure" a theorem about the four-shape family rather than
a sum of per-tree facts (the fourth shape, `slOne`, records: `prop14_only_if_slOne`).
Source: `sl-defensible-claims.md` S2 ("through, and only through, instantiations failing
recording at `d`"); mandate T4(a); audit r1 adversarial N7
Kind: C
Fidelity: exact (recording form: `RecordsFor` for `C`; `O_d = ⊤`)
Hyps: (a) `StrictOCAt`; (a) `S2` -/
theorem prop14_only_if_catalogue (C : Proc Unit (fun _ => Bool) ℚ) (s : Unit → State TickleW ℚ) :
    (StrictOCAt s slObs C cexA₀ () → S2 (s ()) → ¬ RecordsFor slObs slActEv C cexA₀ ()) ∧
    (StrictOCAt s slObs C e2a₀ () → S2 (s ()) → ¬ RecordsFor slObs slActEv C e2a₀ ()) ∧
    (StrictOCAt s slObs C e13₀ () → S2 (s ()) → ¬ RecordsFor slObs slActEv C e13₀ ()) :=
  ⟨fun hs h2 => prop14_only_if C cexA₀ () s (cexA_postQueryIndep C) hs h2,
   fun hs h2 => prop14_only_if C e2a₀ () s (e2a_postQueryIndep C) hs h2,
   fun hs h2 => prop14_only_if C e13₀ () s (e13_postQueryIndep C) hs h2⟩

end Cleanroom.Decision.DpSmokingLesion
