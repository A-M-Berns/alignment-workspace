import Cleanroom.Corrigibility.CorrLegitGeneral.Eval
import Cleanroom.Lit.LitDdbAccuracyMm.Examples

/-!
# corr-legit-general — T2(c)'s boundary: single-score accuracy is strictly weaker than local
Total Trust on the proposition's own question (DDB fn 50)

legitimacy R2.4 (l. 59) says: "'Increase in expected accuracy', read proposition by proposition
with any single proper score, is strictly weaker than either [Total Trust or Reflection]", and
separately that read as DDB's Epistemic Value (all gsp measures) it *is* Total Trust. Through
repair round 2 findings F3 claimed the first sentence "is right only with 'global' inserted",
because the underconfident expert `s6` (`WitnessesLeak.lean`) simply trusts `φ`. That conflated
the two notions: `s6` separates accuracy about `φ` from Reflection and from *global* Total
Trust, but it does not separate anything from local Total Trust on `{φ, ¬φ}`, and the
single-score notion R2.4 quantifies over is strictly weaker than local Total Trust on `q`'s own
question too — DDB's own fn 50 is the witness (audit r3 fidelity B1, probe `Fn50SingleScore.lean`,
adopted here on the dependency's objects `fn50`, `π50` of `lit-ddb-accuracy-mm`).

fn 50's frame: rows `(9/10, 1/10, 0)`, `(9/10, 1/10, 0)`, `(4/10, 1/10, 5/10)`, deferrer
`π = P₃`. For `q = {w₁}` (`{0}` here): Brier accuracy increase about `q` holds (`33/200 < 6/25`),
while Simple Trust with respect to `q`, i.e. local Total Trust on `{q, ¬q}`
(`totalTrustWrt_questionOf_iff`), fails at `t = 9/10` (`π(q | P(q) ≥ 9/10) = 4/5 < 9/10`); both
`q`-cells have positive mass (`4/10`, `6/10`). So, with a single proper score, accuracy increase
about `q` is strictly weaker than local Total Trust on `q`'s own question: R2.4's sentence is
right as stated, without "global". The all-gsp notion does coincide with local Total Trust on
that question (DDB Theorem 3.1/3.2; `s6_headline`'s `EpistemicValueOn`).
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples
  Cleanroom.Lit.LitDdbAccuracyMm

noncomputable section

/-- fn 50's proposition `q = {w₁}`, 0-indexed.
Source: [[Deference Done Better]] fn 50 l. 1205
Kind: D
Fidelity: exact -/
abbrev q50 : Finset (Fin 3) := {0}

/-- The rows' probabilities of `q`: `9/10, 9/10, 4/10`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fn50_mass_q : mass (fn50.P 0) q50 = 9 / 10 ∧ mass (fn50.P 1) q50 = 9 / 10 ∧
    mass (fn50.P 2) q50 = 4 / 10 := by
  obtain ⟨h0, h1, h2⟩ := fn50_P
  refine ⟨?_, ?_, ?_⟩ <;> (rw [mass_singleton]; norm_num [h0, h1, h2])

/-- **Simple Trust with respect to `q` fails** at `t = 9/10`: the event `[P(q) ≥ 9/10] = {0, 1}`
has mass `1/2` and `π(q ∧ ·) = 4/10`, and `9/10 · 1/2 = 9/20 > 4/10`. (The dependency's
`fn50_not_simpleTrust` is the global form at the same `(q, t)`.)
Source: [[Deference Done Better]] fn 50 l. 1205
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fn50_not_simpleTrustOn : ¬ SimpleTrustOn q50 π50 fn50 := by
  rintro ⟨h, _⟩
  obtain ⟨m0, m1, m2⟩ := fn50_mass_q
  have := h (9 / 10)
  rw [mass_probEvent_eq, mass_inter_probEvent_eq] at this
  simp only [Fin.sum_univ_three, m0, m1, m2] at this
  simp +decide [π50, vec3_two] at this
  norm_num at this

/-- **Local Total Trust on `{q, ¬q}` fails** on fn 50's frame (by the package's own two-cell
theorem).
Source: [[Deference Done Better]] fn 50 l. 1205, §5 l. 398
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem fn50_not_totalTrustWrt : ¬ TotalTrustWrt (questionOf q50) π50 fn50 := by
  rw [totalTrustWrt_questionOf_iff (fun w => by fin_cases w <;> norm_num [π50, vec3_two])]
  exact fn50_not_simpleTrustOn

/-- **Brier accuracy increase about `q` holds**: the expert's expected Brier inaccuracy about
`𝟙_q` is `33/200`, the deferrer's own `6/25 = 48/200`.
Source: [[Deference Done Better]] fn 50 l. 1205, §3 l. 301
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fn50_brier_q : expInaccP π50 fn50 (ind q50) brier = 33 / 200 ∧
    expInacc π50 (ind q50) brier (E π50 (ind q50)) = 6 / 25 := by
  obtain ⟨h0, h1, h2⟩ := fn50_P
  constructor <;>
    simp +decide [expInaccP, expInacc, brier, E, Fin.sum_univ_three, ind, π50, h0, h1, h2,
      vec3_two] <;> norm_num

/-- **Packaged**: on fn 50's frame, single-score (Brier) accuracy increase about `q` holds while
local Total Trust on `{q, ¬q}` fails; `π` is a distribution and both `q`-cells have positive
`π`-mass (`4/10`, `6/10`). So "accuracy increase about `φ`, with a single proper score, is
strictly weaker than local Total Trust on `φ`'s own question" — legitimacy R2.4's sentence
needs no "global" (findings F3, corrected in repair round 3).
Source: [[legitimacy]] R2.4 l. 59; [[Deference Done Better]] fn 50 l. 1205, Theorem 3.1
l. 257; audit r3 fidelity B1 (probe `Fn50SingleScore.lean`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fn50_single_score_not_local_tt :
    π50 ∈ stdSimplex ℝ (Fin 3) ∧ 0 < mass π50 q50 ∧ 0 < mass π50 q50ᶜ ∧
    expInaccP π50 fn50 (ind q50) brier < expInacc π50 (ind q50) brier (E π50 (ind q50)) ∧
    ¬ TotalTrustWrt (questionOf q50) π50 fn50 := by
  refine ⟨π50_mem, ?_, ?_, by rw [fn50_brier_q.1, fn50_brier_q.2]; norm_num,
    fn50_not_totalTrustWrt⟩
  · rw [mass_singleton]; norm_num [π50]
  · simp +decide [mass_eq_sum_ite, Fin.sum_univ_three, π50, vec3_two]; norm_num

end

end Cleanroom.Corrigibility.CorrLegitGeneral
