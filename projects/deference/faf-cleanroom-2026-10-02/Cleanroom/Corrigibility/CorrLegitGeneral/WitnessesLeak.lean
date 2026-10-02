import Cleanroom.Corrigibility.CorrLegitGeneral.Eval
import Cleanroom.Corrigibility.CorrLegitGeneral.Locality
import Cleanroom.Corrigibility.CorrLegitGeneral.Transfer
import Cleanroom.Corrigibility.CorrReflectFrames.WitnessesA
import Cleanroom.Lit.LitDdbFacts.Examples

/-!
# corr-legit-general — witnesses on four worlds, II: the local escape, ddb's four-world
frame, the underconfident expert

* **T3(b), the leak frame `leak4`** (B3's leak, the other rows this package's): `π = (2/5, 2/5,
  1/5, 0)`, `L = {0, 1}`, the legitimate candidate at `0` leaks `1/10` to the `π`-null world `3`.
  The global criterion fails (`X = 𝟙_{3}`, `t = 1/10`); the local criterion on `Q = questionOf
  {0, 3}` — which does not separate world `3` from the legitimate world `0` — holds, with both
  `Q`-cells of positive `π_L`-mass and rows differing across cells. Statement 13: the judged
  state keeps `P₀(L) = 9/10 < 1`.
* **T3(c), ddb I5.6's frame** `ddb4` (`corr-reflect-frames` proves `L`-conditioned Total Trust,
  its failure on `¬L`, and the global failure; cited): the press `Pr = {(L,b), (¬L,g)}` is obeyed
  at legitimacy prior `4/5` (`E_π(X·𝟙_Pr) = −3/10 ≤ 0`) and overruled at prior `2/5`
  (`+1/10`), where the channel is worth `−1/10`; the odds condition of T5 at both priors.
* **T2(c), the underconfident expert `s6`** (`corr-reflect-frames`' witness; its Brier/log
  dominance, immodesty and global Total-Trust failure cited): here `¬ Reflects π6 s6`,
  Simple Trust w.r.t. `φ` (`9/10 ≥ 3/5`, `1/10 ≤ 2/5`), hence `TotalTrustOn (𝟙_φ)`, and the Brier
  numbers with `lit-ddb-accuracy-mm`'s objects.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames
  Cleanroom.Corrigibility.CorrReflectFrames.Witnesses Cleanroom.Lit.LitDdbAccuracyMm
open Cleanroom.Lit.LitDdbFacts.Examples (vec4_two vec4_three)

noncomputable section

/-! ## T3(b): the leak frame -/

/-- The leak frame: `P₀ = (7/10, 1/5, 0, 1/10)` (leaks `1/10` to the null world `3`),
`P₁ = (1/5, 3/5, 1/5, 0)`, `δ₂`, `δ₃`.
Source: [[legitimacy-general-final]] Proofs l. 91 (B3, the leak); the other rows this package's
(Known issues 8)
Kind: D
Fidelity: variant: B3 fixes only the leak -/
def leak4 : Frame (Fin 4) :=
  Cleanroom.Lit.LitDdbFacts.Examples.mk4 ![7 / 10, 1 / 5, 0, 1 / 10] ![1 / 5, 3 / 5, 1 / 5, 0]
    ![0, 0, 1, 0] ![0, 0, 0, 1]
    (Cleanroom.Lit.LitDdbFacts.Examples.simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
    (Cleanroom.Lit.LitDdbFacts.Examples.simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
    (Cleanroom.Lit.LitDdbFacts.Examples.simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
    (Cleanroom.Lit.LitDdbFacts.Examples.simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))

/-- The leak deferrer `(2/5, 2/5, 1/5, 0)`.
Source: [[legitimacy-general-final]] Proofs l. 91 (B3)
Kind: D
Fidelity: exact -/
def πleak : Fin 4 → ℝ := ![2 / 5, 2 / 5, 1 / 5, 0]

/-- The legitimacy event `{0, 1}`.
Source: [[legitimacy-general-final]] Proofs l. 91 (B3)
Kind: D
Fidelity: exact -/
abbrev Lleak : Finset (Fin 4) := {0, 1}

/-- B3's question `{{0, 3}, {1, 2}}`, which does not separate the null world `3` from the
legitimate world `0`.
Source: [[legitimacy-general-final]] Proofs l. 91 (B3)
Kind: D
Fidelity: exact -/
abbrev qleak : Finset (Fin 4) := {0, 3}

/-- `leak4`'s rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem leak4_P : leak4.P 0 = ![7 / 10, 1 / 5, 0, 1 / 10] ∧ leak4.P 1 = ![1 / 5, 3 / 5, 1 / 5, 0] ∧
    leak4.P 2 = ![0, 0, 1, 0] ∧ leak4.P 3 = ![0, 0, 0, 1] := ⟨rfl, rfl, rfl, rfl⟩

/-- The rows' probabilities of `qleak`: `4/5, 1/5, 0, 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem leak4_mass_q : mass (leak4.P 0) qleak = 4 / 5 ∧ mass (leak4.P 1) qleak = 1 / 5 ∧
    mass (leak4.P 2) qleak = 0 ∧ mass (leak4.P 3) qleak = 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := leak4_P
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp +decide [mass_eq_sum_ite, Fin.sum_univ_four, qleak, h0, h1, h2, h3, vec4_two, vec4_three] <;>
    norm_num

/-- **The global criterion fails on the leak frame** (`X = 𝟙_{3}`, `t = 1/10`: the legitimate
world `0` has `P₀(3) = 1/10 ≥ 1/10` and the restricted product sum is `−1/25`).
Source: [[legitimacy-general-final]] Proofs l. 91 (B3: "fails global (TT) with `X = 𝟙_{w₃}`,
`t = 1/10`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem leak4_not_legitimizingTT : ¬ LegitimizingTT πleak leak4 Lleak := by
  intro h
  obtain ⟨h0, h1, h2, h3⟩ := leak4_P
  have := h (ind {3}) (1 / 10)
  simp only [Fin.sum_univ_four, restrict_apply, E, h0, h1, h2, h3, ind, πleak] at this
  simp +decide [vec4_two, vec4_three] at this <;> norm_num at this

/-- **Positive-mass guards for the local witness**: both `Q`-cells have positive `π_L`-mass
(`2/5` each), the illegitimate part has positive mass, and the legitimate candidate keeps
`P₀(L) = 9/10 < 1` (Statement 13).
Source: mandate T3(b) (traps); [[legitimacy-general-final]] Statement 13 l. 77
Kind: L
Fidelity: n/a -/
theorem leak4_guards : mass (restrict πleak Lleak) qleak = 2 / 5 ∧
    mass (restrict πleak Lleak) qleakᶜ = 2 / 5 ∧ 0 < mass πleak Lleakᶜ ∧
    mass (leak4.P 0) Lleak = 9 / 10 ∧ 0 < πleak 0 := by
  obtain ⟨h0, _, _, _⟩ := leak4_P
  refine ⟨?_, ?_, ?_, ?_, by norm_num [πleak]⟩
  · simp +decide [mass_eq_sum_ite, Fin.sum_univ_four, restrict_apply, πleak, vec4_two, vec4_three] <;>
      norm_num
  · simp +decide [mass_eq_sum_ite, Fin.sum_univ_four, restrict_apply, πleak, vec4_two, vec4_three] <;>
      norm_num
  · simp +decide [mass_eq_sum_ite, Fin.sum_univ_four, πleak, vec4_two, vec4_three] <;> norm_num
  · rw [h0]; simp +decide [mass_eq_sum_ite, Fin.sum_univ_four, vec4_two, vec4_three] <;> norm_num

/-- **The local escape** (load-bearing 1): the local criterion on B3's question holds on the
leak frame — the Simple-Trust cuts for the restricted deferrer `(2/5, 2/5, 0, 0)` at
`P(q) = 4/5, 1/5`: `π_L(q | P(q) ≥ 1/5) = 1/2 ≥ 1/5`, `π_L(q | P(q) ≥ 4/5) = 1 ≥ 4/5`, and the
below cuts `0 ≤ 1/5`, `1/2 ≤ 4/5`.
Source: [[legitimacy-general-final]] Statement 2(b) l. 44, Proofs l. 91 (B3); [[legitimacy]]
R5.2 l. 99; corr-wf14b-053
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem leak4_legitTotalTrustWrt : LegitTotalTrustWrt (questionOf qleak) πleak leak4 Lleak := by
  rw [legitTotalTrustWrt_questionOf_iff (fun w => by fin_cases w <;> norm_num [πleak, vec4_two, vec4_three])]
  obtain ⟨m0, m1, m2, m3⟩ := leak4_mass_q
  constructor
  · intro t
    rw [mass_probEvent_eq, mass_inter_probEvent_eq]
    simp only [Fin.sum_univ_four, m0, m1, m2, m3]
    simp +decide [restrict_apply, πleak, vec4_two, vec4_three]
    split_ifs <;> (try norm_num) <;> (try linarith)
  · intro t
    rw [mass_probEventLE_eq, mass_inter_probEventLE_eq]
    simp only [Fin.sum_univ_four, m0, m1, m2, m3]
    simp +decide [restrict_apply, πleak, vec4_two, vec4_three]
    split_ifs <;> (try norm_num) <;> (try linarith)

/-- **T3(b), packaged**: global failure and local success on one frame, with the guards.
Source: [[legitimacy-general-final]] Statement 2(b) l. 44; mandate T3(b)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem leak4_witness : ¬ LegitimizingTT πleak leak4 Lleak ∧
    LegitTotalTrustWrt (questionOf qleak) πleak leak4 Lleak ∧ mass (leak4.P 0) Lleak < 1 :=
  ⟨leak4_not_legitimizingTT, leak4_legitTotalTrustWrt, by rw [leak4_guards.2.2.2.1]; norm_num⟩

/-! ## T3(c): ddb I5.6's frame — the press, and T5's odds -/

/-- ddb's stakes variable `X = (1, −1, 1, −1)`.
Source: [[ddb]] I5.6 l. 132
Kind: D
Fidelity: exact -/
def Xddb : Fin 4 → ℝ := ![1, -1, 1, -1]

/-- ddb's press event `Pr = {(L,b), (¬L,g)} = {1, 2}`.
Source: [[ddb]] I5.6 l. 132
Kind: D
Fidelity: exact -/
abbrev Prddb : Finset (Fin 4) := {1, 2}

/-- The deferrer at legitimacy prior `2/5`: `(1/5, 1/5, 3/10, 3/10)`.
Source: [[ddb]] I5.6 l. 132 ("Lower the legitimacy prior to 0.4")
Kind: D
Fidelity: exact -/
def πddb' : Fin 4 → ℝ := ![1 / 5, 1 / 5, 3 / 10, 3 / 10]

/-- The expectation of a product with an indicator splits along `L`/`Lᶜ` (product form of
"obeyed iff `π(L|Pr)·E(X|Pr,L) + π(¬L|Pr)·E(X|Pr,¬L) ≤ 0`").
Source: [[ddb]] I5.6 l. 132; [[legitimacy]] R5.4 l. 101
Kind: L
Fidelity: exact (product form; the ratio form is `corr-general-object`'s `PerQ.perQ_threshold`)
Hyps: (a) none -/
theorem E_split_legit {W : Type} [Fintype W] [DecidableEq W] (π : W → ℝ) (L : Finset W)
    (Y : W → ℝ) : E π Y = E (restrict π L) Y + E (restrict π Lᶜ) Y := by
  have h := restrict_add_restrict_compl π L
  rw [compl_eq_univ_sdiff]
  conv_lhs => rw [← h]
  rw [E_add_left]

/-- **ddb I5.6's press arithmetic** (with `corr-reflect-frames`' `ddb4_legitimizingTT`,
`ddb4_not_legitimizingTT_compl`, `ddb4_not_totalTrust` cited): at prior `4/5` the press is
obeyed, `E_π(X·𝟙_Pr) = −3/10 ≤ 0`, split as `−2/5` on `L` and `+1/10` on `¬L`, and the
channel is worth `E_π(X·𝟙_{¬Pr}) − max(E_π X, 0) = 3/10`; at prior `2/5` the press is overruled,
`E_π(X·𝟙_Pr) = 1/10 > 0`, and the channel is worth `−1/10`.
Source: [[ddb]] I5.6 l. 132; [[legitimacy]] R5.4 l. 101 (E2)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ddb4_press :
    (E πddb (fun w => Xddb w * ind Prddb w) = -3 / 10 ∧
      E (restrict πddb Lddb) (fun w => Xddb w * ind Prddb w) = -2 / 5 ∧
      E (restrict πddb Lddbᶜ) (fun w => Xddb w * ind Prddb w) = 1 / 10 ∧
      E πddb (fun w => Xddb w * ind Prddbᶜ w) = 3 / 10 ∧ E πddb Xddb = 0) ∧
    (E πddb' (fun w => Xddb w * ind Prddb w) = 1 / 10 ∧
      E πddb' (fun w => Xddb w * ind Prddbᶜ w) = -1 / 10 ∧ E πddb' Xddb = 0) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp +decide [E, Fin.sum_univ_four, Xddb, ind, πddb, πddb', restrict_apply, Lddb, vec4_two,
      vec4_three] <;> norm_num

/-- The obedience strategy's value identity on ddb's frame (T5's witness, prior `4/5`): with
`S` = obey (continue off the press, stop on it, worth `X·𝟙_{¬Pr}`) and `O` = continue (worth
`X`), the legitimate gain is `2/5`, the illegitimate loss `1/10`, the odds condition
`1/10 ≤ 2/5` holds and delegation is worth `3/10 ≥ 0`; at prior `2/5` the gain is `1/5`, the loss
`3/10`, the odds condition fails and delegation is worth `−1/10`.
Source: [[mm]] I5.2 l. 147 (the button instance); [[legitimacy]] R5.4 l. 101 (E2)
Kind: N+
Fidelity: exact (product-form gains and losses)
Hyps: (a) none -/
theorem ddb4_odds :
    (E (restrict πddb Lddb) (fun w => Xddb w * ind Prddbᶜ w) - E (restrict πddb Lddb) Xddb = 2 / 5 ∧
      E (restrict πddb Lddbᶜ) Xddb - E (restrict πddb Lddbᶜ) (fun w => Xddb w * ind Prddbᶜ w) =
        1 / 10 ∧
      E πddb (fun w => Xddb w * ind Prddbᶜ w) - E πddb Xddb = 3 / 10) ∧
    (E (restrict πddb' Lddb) (fun w => Xddb w * ind Prddbᶜ w) - E (restrict πddb' Lddb) Xddb =
        1 / 5 ∧
      E (restrict πddb' Lddbᶜ) Xddb - E (restrict πddb' Lddbᶜ) (fun w => Xddb w * ind Prddbᶜ w) =
        3 / 10 ∧
      E πddb' (fun w => Xddb w * ind Prddbᶜ w) - E πddb' Xddb = -1 / 10) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp +decide [E, Fin.sum_univ_four, Xddb, ind, πddb, πddb', restrict_apply, Lddb, vec4_two,
      vec4_three] <;> norm_num

/-! ## T2(c): the underconfident expert -/

/-- `s6`'s cell at the `3/5`-rows is `{0, 1}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem s6_cell0 : s6.cell (s6.P 0) = {0, 1} := by
  obtain ⟨h0, h1, h2, h3⟩ := s6_rows
  have hne : (![3 / 5, 2 / 5, 0, 0] : Fin 4 → ℝ) ≠ ![0, 0, 2 / 5, 3 / 5] := by
    intro h; have := congrFun h 0; norm_num at this
  ext w
  fin_cases w <;> simp +decide [Frame.mem_cell, h0, h1, h2, h3, hne, hne.symm]

/-- **The underconfident expert is not reflected** (`π(φ | P(φ) = 3/5) = 9/10 ≠ 3/5`): the
Reflection clause at the candidate `(3/5, 2/5, 0, 0)` and world `0` reads
`9/20 = (1/2) · (3/5)`.
Source: [[radical]] I4.2(b) l. 136; corr-wf14-028
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem s6_not_reflects : ¬ Reflects π6 s6 := by
  intro h
  obtain ⟨h0, _, _, _⟩ := s6_rows
  have hc : s6.P 0 ∈ s6.cands π6 := s6.P_mem_cands (by norm_num [π6])
  have := h _ hc 0
  rw [s6_cell0] at this
  simp +decide [mass_eq_sum_ite, Fin.sum_univ_four, ind, π6, h0, vec4_two, vec4_three] at this <;>
    norm_num at this

/-- **Simple Trust w.r.t. `φ` holds on the underconfident expert**: `π(φ | P(φ) ≥ 3/5) = 9/10`,
`π(φ | P(φ) ≤ 2/5) = 1/10`.
Source: mandate T2(c) ("`TotalTrustOn π F (ind φ)` (Simple Trust w.r.t. φ: 9/10 ≥ 3/5,
1/10 ≤ 2/5)")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem s6_simpleTrustOn : SimpleTrustOn φ6 π6 s6 := by
  obtain ⟨m0, m1, m2, m3⟩ := s6_mass_φ
  constructor
  · intro t
    rw [mass_probEvent_eq, mass_inter_probEvent_eq]
    simp only [Fin.sum_univ_four, m0, m1, m2, m3]
    simp +decide [π6, vec4_two, vec4_three]
    split_ifs <;> (try norm_num) <;> (try linarith)
  · intro t
    rw [mass_probEventLE_eq, mass_inter_probEventLE_eq]
    simp only [Fin.sum_univ_four, m0, m1, m2, m3]
    simp +decide [π6, vec4_two, vec4_three]
    split_ifs <;> (try norm_num) <;> (try linarith)

/-- **Local Total Trust on `{φ, ¬φ}` holds on the underconfident expert**, hence (Theorem 3.2)
accuracy increase on every gsp measure for `𝟙_φ`.
Source: mandate T2(c); [[Deference Done Better]] §3 Theorem 3.2
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem s6_totalTrustOn : TotalTrustOn (ind φ6) π6 s6 ∧ EpistemicValueOn (ind φ6) π6 s6 := by
  have h := (simpleTrustOn_iff_totalTrustOn_ind φ6).1 s6_simpleTrustOn
  exact ⟨h, (totalTrustOn_iff_epistemicValueOn π6_mem s6).1 h⟩

/-- **Brier dominance with `lit-ddb-accuracy-mm`'s objects**: the expert's expected Brier
inaccuracy about `𝟙_φ` is `9/50`, the constant `π(φ) = 1/2`'s is `1/4`.
Source: [[radical]] I4.2(b) l. 136 (`9/50 < 1/4`); [[legitimacy]] R2.4 l. 59 (G)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem s6_brier_mm :
    expInaccP π6 s6 (ind φ6) Cleanroom.Lit.LitDdbAccuracyMm.brier = 9 / 50 ∧
    expInacc π6 (ind φ6) Cleanroom.Lit.LitDdbAccuracyMm.brier (E π6 (ind φ6)) = 1 / 4 := by
  obtain ⟨h0, h1, h2, h3⟩ := s6_rows
  constructor <;>
    simp +decide [expInaccP, expInacc, Cleanroom.Lit.LitDdbAccuracyMm.brier, E, Fin.sum_univ_four,
      ind, π6, h0, h1, h2, h3, vec4_two, vec4_three] <;> norm_num

/-- **T2(c), the honest headline, packaged**: on the underconfident expert, Reflection fails,
global Total Trust fails (cited), yet Simple Trust w.r.t. `φ`, local Total Trust on `{φ, ¬φ}`,
epistemic value for `𝟙_φ`, and Brier dominance all hold — accuracy increase *on every gsp
measure* (`EpistemicValueOn`) is strictly weaker than global Total Trust and than Reflection, and
on the proposition's own two-cell question it coincides with local Total Trust (DDB Theorem
3.1/3.2; Known issues 2). With a *single* proper score — the notion legitimacy R2.4's sentence
quantifies over — accuracy increase is strictly weaker than local Total Trust on that question
too (DDB fn 50, `WitnessesFn50.lean`), which this frame does not show: `π6` simply trusts `φ`
(findings F3, corrected in repair round 3).
Source: [[legitimacy]] R2.4 l. 59; corr-wf14-028; [[radical]] I4.2(b) l. 136
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem s6_headline : s6.Immodest ∧ ¬ Reflects π6 s6 ∧ ¬ TotalTrust π6 s6 ∧
    TotalTrustOn (ind φ6) π6 s6 ∧ EpistemicValueOn (ind φ6) π6 s6 ∧
    expInaccP π6 s6 (ind φ6) Cleanroom.Lit.LitDdbAccuracyMm.brier <
      expInacc π6 (ind φ6) Cleanroom.Lit.LitDdbAccuracyMm.brier (E π6 (ind φ6)) :=
  ⟨s6_immodest, s6_not_reflects, s6_not_totalTrust, s6_totalTrustOn.1, s6_totalTrustOn.2,
    by rw [s6_brier_mm.1, s6_brier_mm.2]; norm_num⟩

end

end Cleanroom.Corrigibility.CorrLegitGeneral
