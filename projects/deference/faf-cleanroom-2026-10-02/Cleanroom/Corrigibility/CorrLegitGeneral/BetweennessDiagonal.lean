import Cleanroom.Corrigibility.CorrLegitGeneral.Betweenness

/-!
# corr-legit-general — T4(c)'s boundary: the P2 family on its diagonal

Adopted from the round-2 adversarial probe (`audit-r2-probes/P2Diagonal.lean`, repair round 2).
`p2_totalTrustWrt_iff` / `p2_valuesWrt_iff` (T4(c), `Betweenness.lean`) prove "local Total Trust
⟺ local Value ⟺ betweenness" on the two-signal family under `hlt : h₂ < h₁`. Is `hlt` a
convenience? No: on the diagonal `h₁ = h₂ = h` (an overseer whose credence ignores its signal)
every row gives `x = 1` probability `h`, so with `h = p_P` both Simple-Trust cuts hold and local
Total Trust w.r.t. the `x`-question holds — but the two rows still differ (different supports),
so a recommended strategy may break the tie of the menu `{𝟙_x − h, h − 𝟙_x}` oppositely on the
two signals and lose. At the source's deferrer (`σ = 1/2`, `p̂ = (9/10, 1/5)`, `p_P = 11/20`)
with `h₁ = h₂ = 11/20`: local Total Trust holds and local Value fails
(`E_π(S) = −7/20 < 0 = E_π(h − 𝟙_x)`). So T4(c)'s "necessary and sufficient" is confined to
non-diagonal overseers; on the diagonal local Total Trust and local Value come apart in fn 64's
literal reading — exactly the T4(b) tie phenomenon (`tie4`) in P2 clothing. `hlt` is load-bearing.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Lit.LitDdbAccuracyMm
  Cleanroom.Lit.LitDdbFacts.Examples

noncomputable section

/-- The diagonal overseer at `h₁ = h₂ = 11/20 = p_P`.
Source: [[approval-final]] P2 l. 91 (the family), audit r2 adversarial N2 (the diagonal)
Kind: D
Fidelity: exact -/
def p2diag : Frame (Fin 4) := p2Frame (11 / 20) (11 / 20) (by norm_num) (by norm_num)

/-- The source's deferrer `(9/20, 1/20, 1/10, 2/5)`.
Source: [[approval-final]] P2 l. 91
Kind: D
Fidelity: exact -/
def πp2 : Fin 4 → ℝ := p2Def (1 / 2) (9 / 10) (1 / 5)

/-- The deferrer's coordinates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πp2_eq : πp2 = ![9 / 20, 1 / 20, 1 / 10, 2 / 5] := by
  funext w; fin_cases w <;> simp [πp2, p2Def, vec4_two, vec4_three] <;> norm_num

/-- The diagonal overseer's rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem p2diag_P : p2diag.P 0 = ![11 / 20, 9 / 20, 0, 0] ∧ p2diag.P 1 = ![11 / 20, 9 / 20, 0, 0] ∧
    p2diag.P 2 = ![0, 0, 11 / 20, 9 / 20] ∧ p2diag.P 3 = ![0, 0, 11 / 20, 9 / 20] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (show (p2Frame _ _ _ _).P _ = _; rw [p2Frame_P]; norm_num)

/-- Every row gives `x = 1` probability `11/20`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem p2diag_mass : ∀ w, mass (p2diag.P w) xq = 11 / 20 := by
  intro w
  show mass ((p2Frame _ _ _ _).P w) xq = _
  rw [p2Frame_mass_xq]; split_ifs <;> rfl

/-- **Local Total Trust holds on the diagonal**: a single `P(x=1)`-cluster at `11/20 = π(x=1)`,
so both Simple-Trust cuts hold at every threshold.
Source: [[approval-final]] P2 l. 91; audit r2 adversarial N2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem p2diag_totalTrustWrt : TotalTrustWrt (questionOf xq) πp2 p2diag := by
  rw [totalTrustWrt_questionOf_iff
    (fun w => by rw [πp2_eq]; fin_cases w <;> norm_num [vec4_two, vec4_three])]
  have m := p2diag_mass
  constructor
  · intro t
    rw [mass_probEvent_eq, mass_inter_probEvent_eq]
    simp only [Fin.sum_univ_four, m, πp2_eq]
    simp +decide [xq, vec4_two, vec4_three]
    split_ifs <;> (try norm_num) <;> (try linarith)
  · intro t
    rw [mass_probEventLE_eq, mass_inter_probEventLE_eq]
    simp only [Fin.sum_univ_four, m, πp2_eq]
    simp +decide [xq, vec4_two, vec4_three]
    split_ifs <;> (try norm_num) <;> (try linarith)

/-- The tied option `𝟙_x − 11/20`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def oAd : Fin 4 → ℝ := fun w => ind xq w - 11 / 20

/-- The tied option `11/20 − 𝟙_x`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def oBd : Fin 4 → ℝ := fun w => 11 / 20 - ind xq w

/-- The tie-split strategy: `oBd` on the signal-1 worlds, `oAd` on the signal-2 worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def Sd : Fin 4 → (Fin 4 → ℝ) := ![oBd, oBd, oAd, oAd]

/-- `Sd` is a recommended strategy for `{oAd, oBd}`: cellwise (the two rows differ), and both
options tie at every row.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Sd_recommended : p2diag.Recommended {oAd, oBd} Sd := by
  obtain ⟨h0, h1, h2, h3⟩ := p2diag_P
  refine ⟨⟨fun w => ?_, fun w v hwv => ?_⟩, fun w o ho => ?_⟩
  · fin_cases w <;> simp [Sd, vec4_two, vec4_three]
  · fin_cases w <;> fin_cases v <;>
      first
        | rfl
        | (have := congrFun hwv 0; norm_num [h0, h1, h2, h3, vec4_two, vec4_three] at this; done)
  · simp only [mem_insert, mem_singleton] at ho
    fin_cases w <;> rcases ho with rfl | rfl <;>
      simp +decide [E, Fin.sum_univ_four, Sd, oAd, oBd, ind, xq, h0, h1, h2, h3, vec4_two,
        vec4_three] <;> norm_num

/-- **Local Value fails on the diagonal**: `E_π(Sd) = −7/20 < 0 = E_π(oBd)`.
Source: [[approval-final]] P2 l. 91; [[Deference Done Better]] fn 64 (every recommended strategy);
audit r2 adversarial N2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem p2diag_not_valuesWrt : ¬ ValuesWrt (questionOf xq) πp2 p2diag := by
  intro h
  have hmeas : ∀ o ∈ ({oAd, oBd} : DecisionProblem (Fin 4)), MeasurableWrt (questionOf xq) o := by
    intro o ho
    simp only [mem_insert, mem_singleton] at ho
    have hq := measurableWrt_questionOf_ind xq
    rcases ho with rfl | rfl
    · intro w v hwv; simp only [oAd, hq w v hwv]
    · intro w v hwv; simp only [oBd, hq w v hwv]
  have := h {oAd, oBd} (insert_nonempty _ _) hmeas Sd Sd_recommended oBd (by simp)
  rw [πp2_eq] at this
  simp +decide [E, stratValue, Fin.sum_univ_four, Sd, oAd, oBd, ind, xq, vec4_two,
    vec4_three] at this <;> norm_num at this

/-- **Packaged — the T4(c) equivalence does not extend to the diagonal**: on the P2 family at
`h₁ = h₂ = p_P`, the deferrer is a distribution, both `x`-cells have positive mass (`11/20`,
`9/20`), the rows differ, local Total Trust holds and local Value fails. `hlt : h₂ < h₁` in
`p2_valuesWrt_iff` is therefore load-bearing, and on the diagonal the two predicates come apart
by the tie mechanism of `tie4`.
Source: [[approval-final]] P2 l. 91, P2′ l. 93 (the standing `p_{H₂} < p_{H₁}`); audit r2
adversarial N2; findings F4
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem p2_diagonal_breaks : πp2 ∈ stdSimplex ℝ (Fin 4) ∧ p2diag.P 0 ≠ p2diag.P 2 ∧
    mass πp2 xq = 11 / 20 ∧ TotalTrustWrt (questionOf xq) πp2 p2diag ∧
    ¬ ValuesWrt (questionOf xq) πp2 p2diag := by
  obtain ⟨h0, _, h2, _⟩ := p2diag_P
  refine ⟨p2Def_mem (by norm_num) (by norm_num) (by norm_num), fun h => ?_, ?_,
    p2diag_totalTrustWrt, p2diag_not_valuesWrt⟩
  · have := congrFun h 0; rw [h0, h2] at this; norm_num at this
  · rw [πp2_eq]; simp +decide [mass_eq_sum_ite, Fin.sum_univ_four, xq, vec4_two, vec4_three] <;> norm_num

end

end Cleanroom.Corrigibility.CorrLegitGeneral
