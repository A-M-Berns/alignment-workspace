import Cleanroom.Corrigibility.CorrPowerChannel.J3
import Cleanroom.Corrigibility.CorrPowerChannel.SelfCap
import Cleanroom.Corrigibility.CorrPowerChannel.Orbit
import Cleanroom.Corrigibility.CorrPowerChannel.Grip
import Cleanroom.Corrigibility.CorrPowerChannel.Splice

/-!
# `corr-power-channel` — witnesses: the E3 family (T3's A1 and R2), and the repair-round-1 lifts

* **A1 at `n = 3`, `μ = h = 1/2`** (`e3_selfcap_inert`): `EVPI{s, ∅} = 0`; inserting the scan into
  `plans ∪ {∅}` leaves the residual at `2/3`: neither the per-option self-cap nor the set-level
  D17 unlock sees the scan.
* **R2 at `n = 3`, `η = 1/100`** (`e3_support_veto`): every plan and `∅` pass the support veto at
  `τ = 0`; the scan fails (harm `1/2` under a live hypothesis of mass `1/6`).
* **J3 over D18's full continuation set** (`e3_j3_iff_cont`, `e3_j3Given_iff_cont`): the E3 iffs of
  `J3.lean` hold verbatim over `plans ∪ {∅, s}` (`voiExp_insert_dominated`).
* **The value-certain grip on R1's kernel** (`powerGrip_r1`, `powerGrip_r1_strict`): `POWER^Γ =
  (1 − Γ)·9/10`, slope `−9/10`, strict at `Γ = 1/2` — the N+ for the `powerGrip` row, and the
  reason `r1_slopes` (informed `0`, blind `+3/20`) is not that witness.
* **`splice_alpha_bound`'s full package, inhabited** (`e4_reliable`, `e4_alpha_bound`): E4's own
  objects with `wise = {πw}`, `cls = {πw, splice}`, `α = 19/25` — tight on both reliability
  clauses by construction; and in its interior (`e4_reliable_interior`, `e4_alpha_bound_interior`,
  `η = 1/10`, `α = 4/5`, both clauses strict; repair round 2).

Sources: power-wisdom-final.md S11′ (l. 135), P8 (l. 181–183), D18 (l. 83), S5 (l. 109);
power-wisdom-adversary.md S11.1–S11.2 (l. 155–157); channel-final.md S9 (l. 81); scripts A1, R2,
E4; [[corr-power-channel-audit-r1-fidelity]] N2, N6, N7; [[corr-power-channel-audit-r1-adversarial]]
N2, N5; [[corr-power-channel-audit-r2-adversarial]] N3.
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Corrigibility.CorrCautionPower (harmOf harmOf_nonneg harmOf_nul)
open Finset hiding expect expect_const

noncomputable section

/-- The scan is dominated by the null option under every hypothesis (`h ≥ 0`).
Source: power-wisdom-adversary.md S11.1 (l. 155). Kind: L. Fidelity: n/a -/
theorem e3_scan_le_nul (n : ℕ) {h : ℝ} (hh : 0 ≤ h) (ω : E3Ω n) :
    e3V n h ω (e3Scan n) ≤ e3V n h ω (e3Nul n) := by
  simp only [e3Scan, e3Nul, e3V_scan, e3V_nul]
  split_ifs <;> linarith

/-- The null option is dominated by every plan under every hypothesis.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem e3_nul_le_plan (n : ℕ) (h : ℝ) (ω : E3Ω n) (j : Fin (n + 1)) :
    e3V n h ω (e3Nul n) ≤ e3V n h ω (Sum.inl j) := by
  simp only [e3Nul, e3V_nul, e3V_plan]
  split_ifs <;> norm_num

/-- **A1 (N+): the self-cap is inert against the scan, at `n = 3`, `μ = h = 1/2`.**
`EVPI{s, ∅} = 0`; `EVPI(plans ∪ {∅}) = 2/3 = EVPI(plans ∪ {∅, s})`: the D17 unlock increment of
the scan is `0`.
Source: power-wisdom-adversary.md S11.1–S11.2 (l. 155–157, "`2/3 → 2/3`"); power-wisdom-final.md
S11′ (l. 135); script A1
Kind: N+
Fidelity: exact
Hyps: none -/
theorem e3_selfcap_inert :
    evpi (e3P 2 (1 / 2) (by norm_num)) (e3V 2 (1 / 2)) {e3Scan 2, e3Nul 2} (by simp) = 0 ∧
      evpi (e3P 2 (1 / 2) (by norm_num)) (e3V 2 (1 / 2)) (insert (e3Nul 2) (e3Plans 2))
        (insert_nonempty _ _) = 2 / 3 ∧
      evpi (e3P 2 (1 / 2) (by norm_num)) (e3V 2 (1 / 2))
        (insert (e3Scan 2) (insert (e3Nul 2) (e3Plans 2))) (insert_nonempty _ _) = 2 / 3 := by
  have h1 := evpi_insert_dominated (e3P 2 (1 / 2) (by norm_num)) (e3V 2 (1 / 2))
    (e3Plans_nonempty 2) (a := e3Nul 2) (b := Sum.inl 0) (by simp [e3Plans])
    (fun ω => e3_nul_le_plan 2 (1 / 2) ω 0)
  have h2 := evpi_insert_dominated (e3P 2 (1 / 2) (by norm_num)) (e3V 2 (1 / 2))
    (insert_nonempty (e3Nul 2) (e3Plans 2)) (a := e3Scan 2) (b := e3Nul 2) (mem_insert_self _ _)
    (fun ω => e3_scan_le_nul 2 (by norm_num) ω)
  refine ⟨evpi_pair_null_eq_zero _ _ _ _ (fun ω => e3_scan_le_nul 2 (by norm_num) ω), ?_, ?_⟩
  · rw [h1, e3_evpi]; norm_num
  · rw [h2, h1, e3_evpi]; norm_num

/-- **R2 (N+): the support veto at `n = 3`, `η = 1/100`, `τ = 0`.** Every plan and `∅` pass; the
scan fails — under `(0, mind)` of mass `1/6 > 1/100` its harm is `1/2 > 0`.
Source: power-wisdom-final.md P8 (l. 183, "R2 … worst live harm `0` for `b₁, b₂, b₃, ∅` and `1/2`
for `s`"); script R2
Kind: N+
Fidelity: exact
Hyps: none -/
theorem e3_support_veto :
    (∀ j : Fin 3, SupportVeto (e3P 2 (1 / 2) (by norm_num)) (e3V 2 (1 / 2)) (e3Nul 2) (1 / 100) 0
      (Sum.inl j)) ∧
      SupportVeto (e3P 2 (1 / 2) (by norm_num)) (e3V 2 (1 / 2)) (e3Nul 2) (1 / 100) 0 (e3Nul 2) ∧
      ¬ SupportVeto (e3P 2 (1 / 2) (by norm_num)) (e3V 2 (1 / 2)) (e3Nul 2) (1 / 100) 0 (e3Scan 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j ω _
    simp only [harmOf, e3Nul, e3V_nul, e3V_plan]
    split_ifs <;> norm_num
  · intro ω _
    simp [harmOf, e3Nul, e3V_nul]
  · intro h
    have := h (0, true) (by simp [e3P_mass]; norm_num)
    simp [harmOf, e3Nul, e3Scan, e3V_nul, e3V_scan] at this
    norm_num at this

/-! ## J3 over D18's full continuation set (repair round 1, fidelity N7) -/

/-- Over E3, `∅` and the scan are dominated, so `plans ∪ {∅, s}` has the same VOI as the plans
under every experiment. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem e3_voiExp_cont {S : Type} [Fintype S] (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1)
    {h : ℝ} (hh : 0 ≤ h) (k : Experiment (E3Ω n) S) :
    voiExp (e3P n μ hμ) (e3V n h) k (insert (e3Scan n) (insert (e3Nul n) (e3Plans n)))
        (insert_nonempty _ _) =
      voiExp (e3P n μ hμ) (e3V n h) k (e3Plans n) (e3Plans_nonempty n) := by
  rw [voiExp_insert_dominated _ _ _ (insert_nonempty _ _) (mem_insert_self _ _)
      (fun ω => e3_scan_le_nul n hh ω),
    voiExp_insert_dominated _ _ _ (e3Plans_nonempty n)
      (show Sum.inl 0 ∈ e3Plans n by simp [e3Plans]) (fun ω => e3_nul_le_plan n h ω 0)]

/-- **S2's absolute J3 over D18's full continuation set `plans ∪ {∅, s}`**: the same iff as
`e3_j3_iff` — the two extra options are dominated, so neither the VOI nor the baseline moves.
Source: power-wisdom-final.md D18 (l. 83, "`A_{t+1} ⊇ {∅, s}`"), S2 (l. 103)
Kind: C
Fidelity: exact (D18's continuation set)
Hyps: (a) `0 ≤ h` -/
theorem e3_j3_iff_cont (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) {h : ℝ} (hh : 0 ≤ h) :
    J3 (e3P n μ hμ) (e3V n h) (ofMap Prod.fst) (e3Scan n) (e3Nul n)
        (insert (e3Scan n) (insert (e3Nul n) (e3Plans n))) (insert_nonempty _ _) ↔
      1 - ((n : ℝ) + 1)⁻¹ < μ * h := by
  rw [← e3_j3_iff n μ hμ hh]
  unfold J3
  rw [e3_voiExp_cont n μ hμ hh]

/-- **J3 against asking first over D18's full continuation set**: the same iff as
`e3_j3Given_iff`, hence `e3_j3Given_all_iff`'s "at every `n` iff `δ ≤ μh`" holds over
`plans ∪ {∅, s}` too.
Source: power-wisdom-final.md D18 (l. 83), S2 (l. 103), P2 (l. 159)
Kind: C
Fidelity: exact (D18's continuation set)
Hyps: (a) `0 ≤ h` -/
theorem e3_j3Given_iff_cont (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) {h : ℝ} (hh : 0 ≤ h)
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    J3Given (e3P n μ hμ) (e3V n h) (e3Q n δ hδ) (ofMap Prod.fst) (e3Scan n) (e3Nul n)
        (insert (e3Scan n) (insert (e3Nul n) (e3Plans n))) (insert_nonempty _ _) ↔
      δ * (1 - ((n : ℝ) + 1)⁻¹) < μ * h := by
  rw [← e3_j3Given_iff n μ hμ hh δ hδ]
  unfold J3Given
  rw [e3_voiExp_cont n μ hμ hh, e3_voiExp_cont n μ hμ hh]

/-! ## The value-certain grip on R1's kernel (repair round 1, N2 of both audits) -/

/-- R1's stakes as a value table on `{∅ = 0, act = 1}`: acting is worth `c = 1` when right and
`−h = −4` when wrong; `∅` is worth `0`.
Source: channel-final.md S9 (l. 81, R1). Kind: D. Fidelity: n/a (witness) -/
def r1V2 : World → Fin 2 → ℝ := fun ω => ![0, twoX 1 4 ω]

/-- **`POWER^Γ` on R1's kernel is `(1 − Γ)·9/10`**: `POWER = E[X⁺] = 9/10` under `twoPoint (1/10)`
and `E[V(∅)] = 0`, so the value-certain slope in `Γ` is `−9/10` — against the trusting agent's
informed slope `0` and blind slope `+3/20` on the same kernel (`r1_slopes`). The two are different
objects (`powerGrip` lands the humans' option in every world; the grip model of `Grip.lean` lands
only on the intent branch), which is why `r1_slopes` is not the witness for the `powerGrip` row.
Source: channel-final.md S9 (l. 81, R1); [[corr-power-channel-audit-r1-adversarial]] N2
Kind: N+
Fidelity: exact
Hyps: none -/
theorem powerGrip_r1 (Γ : ℝ) :
    powerGrip (twoPoint (1 / 10) (by norm_num)) r1V2 univ univ_nonempty Γ 0 =
      (1 - Γ) * (9 / 10) := by
  have hu : (univ : Finset (Fin 2)) = {0, 1} := by decide
  simp [powerGrip, power, attainable, expect_two, hu, r1V2, twoX, twoValue]
  norm_num

/-- **A strict instance of `powerGrip_lt_power_iff`** on R1's kernel at `Γ = 1/2`: `9/20 < 9/10`
(`∅ ∈ B`, `0 ≤ Γ`, and `E[V(∅)] = 0 < 9/10 = POWER`).
Source: [[corr-power-channel-mandate]] load-bearing 4; [[corr-power-channel-audit-r1-fidelity]] N2
Kind: N+
Fidelity: exact
Hyps: none -/
theorem powerGrip_r1_strict :
    powerGrip (twoPoint (1 / 10) (by norm_num)) r1V2 univ univ_nonempty (1 / 2) 0 <
      power (twoPoint (1 / 10) (by norm_num)) r1V2 univ univ_nonempty := by
  have h0 := powerGrip_r1 (1 / 2)
  have hp : power (twoPoint (1 / 10) (by norm_num)) r1V2 univ univ_nonempty = 9 / 10 := by
    have := powerGrip_r1 0
    unfold powerGrip at this
    linarith
  rw [h0, hp]
  norm_num

/-! ## `splice_alpha_bound`'s full package, inhabited (repair round 1, N5/N6 of the audits) -/

/-- (H3) on E4: the splice differs from the wise policy on the context the discriminator misreads.
Source: script E4. Kind: L. Fidelity: n/a -/
theorem splice_ne_e4W : splice e4D e4W e4B ≠ e4W := by
  intro h
  have := congrArg (fun f : Fin 5 → Distr (Fin 2) => (f 4).mass 1) h
  simp [splice, e4D, e4W, e4B, twoPtFin] at this

/-- **E4 is reliable at `(η, α) = (1/20, 19/25)`** on the class `{πw, splice}` with `wise = {πw}`:
the wise policy passes at `19/20 ≥ 1 − η`; the one unwise policy in the class (the splice) passes
at `19/25 ≤ α`. Both clauses hold with *equality* by the choice of parameters — `η` is `πw`'s miss
rate and `α` the splice's own pass rate — i.e. this inhabitant sits on the boundary of the
`Reliable` package; the interior inhabitant at the same objects is `e4_reliable_interior`
(`η = 1/10`, `α = 4/5`, both clauses strict).
Source: power-wisdom-final.md D19 (l. 91); script E4; [[corr-power-channel-audit-r1-adversarial]]
N5; [[corr-power-channel-audit-r2-adversarial]] N3
Kind: N+
Fidelity: exact (tight on both clauses by construction)
Hyps: none -/
theorem e4_reliable :
    Reliable (Distr.uniform : Distr (Fin 5)) e4Pass (1 / 20) (19 / 25) {e4W}
      {e4W, splice e4D e4W e4B} :=
  ⟨fun π hπ => by
      rw [Set.mem_singleton_iff] at hπ
      subst hπ
      rw [e4_realized.1]; norm_num,
    fun π hπ hnw => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hπ
      rcases hπ with rfl | rfl
      · exact absurd (Set.mem_singleton _) hnw
      · rw [e4_realized.2.2.1]⟩

/-- **`splice_alpha_bound` on its full package**, E4: `3/4 ≤ 19/25 ≤ 19/25` — the right-hand
inequality is `α` chosen as the splice's own pass rate, which is what "the `≤ α` clause is the
hypothesis projected" means.
Source: power-wisdom-final.md S5 (l. 109); script E4
Kind: N+
Fidelity: exact
Hyps: none -/
theorem e4_alpha_bound :
    (1 - 1 / 20 : ℝ) - discErr (Distr.uniform : Distr (Fin 5)) e4D ≤
        passRate (Distr.uniform : Distr (Fin 5)) (splice e4D e4W e4B) e4Pass ∧
      passRate (Distr.uniform : Distr (Fin 5)) (splice e4D e4W e4B) e4Pass ≤ 19 / 25 :=
  splice_alpha_bound (Distr.uniform : Distr (Fin 5)) e4Pass e4_reliable e4D
    (Set.mem_singleton _) (by simp) (fun h => splice_ne_e4W (Set.mem_singleton_iff.1 h))

/-! ### The interior inhabitant (repair round 2, adversarial N3) -/

/-- **E4 is reliable at `(η, α) = (1/10, 4/5)`** on the same class, with slack on both clauses:
`19/20 > 9/10` and `19/25 < 4/5`.
Source: power-wisdom-final.md D19 (l. 91); script E4; [[corr-power-channel-audit-r2-adversarial]]
N3 (probe `ReliableInterior.lean`, lifted)
Kind: N+
Fidelity: exact (both clauses strict: the package is inhabited in its interior)
Hyps: none -/
theorem e4_reliable_interior :
    Reliable (Distr.uniform : Distr (Fin 5)) e4Pass (1 / 10) (4 / 5) {e4W}
      {e4W, splice e4D e4W e4B} :=
  ⟨fun π hπ => by
      rw [Set.mem_singleton_iff] at hπ
      subst hπ
      rw [e4_realized.1]; norm_num,
    fun π hπ hnw => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hπ
      rcases hπ with rfl | rfl
      · exact absurd (Set.mem_singleton _) hnw
      · rw [e4_realized.2.2.1]; norm_num⟩

/-- At `(η, α) = (1/10, 4/5)` both reliability clauses hold strictly and `splice_alpha_bound`'s
conclusion reads `7/10 < 19/25 < 4/5`, strictly.
Source: power-wisdom-final.md S5 (l. 109); script E4; [[corr-power-channel-audit-r2-adversarial]] N3
Kind: N+
Fidelity: exact
Hyps: none -/
theorem e4_alpha_bound_interior :
    (1 - 1 / 10 : ℝ) < passRate (Distr.uniform : Distr (Fin 5)) e4W e4Pass ∧
      (1 - 1 / 10 : ℝ) - discErr (Distr.uniform : Distr (Fin 5)) e4D <
        passRate (Distr.uniform : Distr (Fin 5)) (splice e4D e4W e4B) e4Pass ∧
      passRate (Distr.uniform : Distr (Fin 5)) (splice e4D e4W e4B) e4Pass < 4 / 5 := by
  rw [e4_realized.1, e4_realized.2.1, e4_realized.2.2.1]
  norm_num

/-- `splice_alpha_bound` instantiated on the interior package (its own non-strict conclusion at
`η = 1/10`, `α = 4/5`). Source: power-wisdom-final.md S5 (l. 109); script E4. Kind: L.
Fidelity: exact -/
theorem e4_alpha_bound_interior' :
    (1 - 1 / 10 : ℝ) - discErr (Distr.uniform : Distr (Fin 5)) e4D ≤
        passRate (Distr.uniform : Distr (Fin 5)) (splice e4D e4W e4B) e4Pass ∧
      passRate (Distr.uniform : Distr (Fin 5)) (splice e4D e4W e4B) e4Pass ≤ 4 / 5 :=
  splice_alpha_bound (Distr.uniform : Distr (Fin 5)) e4Pass e4_reliable_interior e4D
    (Set.mem_singleton _) (by simp) (fun h => splice_ne_e4W (Set.mem_singleton_iff.1 h))

end

end Cleanroom.Corrigibility.CorrPowerChannel
