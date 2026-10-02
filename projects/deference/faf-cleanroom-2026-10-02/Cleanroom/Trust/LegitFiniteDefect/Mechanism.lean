import Cleanroom.Trust.LegitFiniteDefect.Defs

/-!
# Mechanism non-identifiability

Package `legit-finite-defect`, Target 6 (load-bearing 4; item 2-035). One frame on eight worlds
`(mechanism, report, θ)`, encoded as `Fin 8` with `w = 4·mech + 2·rep + θ` (`mech`, `rep`, `θ8`
decode). The frame's row at `w` is the *meaning* of the report `rep w`: `ρhi` is the clean
posterior on the clean `hi`-fibre (`3/4` on `θ = 1`, `1/4` on `θ = 0`), `ρlo` symmetric. Two
priors: `πclean` on clean worlds (report correlated with `θ`), `πmanip` on manipulated worlds
(same report marginal, report decoupled from `θ`), and the mixtures `πmix λ`.

* **(i) Observables coincide**: the report marginal is `(1/2, 1/2)` under every mixture, so every
  function of the report marginal takes the same value on both (by `congrArg`). "Everything the
  novice sees" is the report value — `θ` is never resolved (v6 §6.3's unresolvable question);
  that modelling choice is what makes (i) meaningful, and if `θ` were observed the detection
  hierarchy (Target 4(1)) says report gates would see the miscalibration.
* **(ii) Trust verdicts differ**: `TotalTrust πclean F` with the exact `∀ X s` quantifier, proved
  through `lit-ddb-frames`'s cycle (`totalTrust_iff_hullAndModestlyInformed`, no grid); and
  `¬ TotalTrust (πmix λ) F` for every `λ > 0`, at `X = 𝟙[θ = 1]`, `s = 3/4`, where the product
  sum is `−λ/4`.
* **(iii) Near-miss**: the manipulator's own fibre fails at the same `(X, s)`, so a
  mechanism-conditional test separates what the marginal cannot.

Register: finite shadow of "the record cannot reveal it"; legitimacy is a property of the
mechanism, not of any feedback statistic. No general Total Trust of partition experts is proved
here (that is `tt-finite-frames`'s).
-/

namespace Cleanroom.Trust.LegitFiniteDefect.Mechanism

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Trust.LegitFiniteDefect

noncomputable section

/-! ## The frame -/

/-- The mechanism coordinate: `0` = clean (worlds `0..3`), `1` = manipulated (worlds `4..7`).
Source: `run3/questions/scout-fresh-eyes.md` Q3; mandate Target 6
Kind: D
Fidelity: exact (encoding) -/
def mech : Fin 8 → Fin 2 := ![0, 0, 0, 0, 1, 1, 1, 1]

/-- The report coordinate: `0` = lo, `1` = hi.
Source: mandate Target 6
Kind: D
Fidelity: exact (encoding) -/
def rep : Fin 8 → Fin 2 := ![0, 0, 1, 1, 0, 0, 1, 1]

/-- The target `θ` (the last coordinate), as a real variable.
Source: mandate Target 6
Kind: D
Fidelity: exact (encoding) -/
def θ8 : Fin 8 → ℝ := ![0, 1, 0, 1, 0, 1, 0, 1]

/-- The meaning of report `hi`: the clean posterior on the clean `hi`-fibre, `3/4` on `θ = 1`.
Source: mandate Target 6
Kind: D
Fidelity: exact -/
def ρhi : Fin 8 → ℝ := ![0, 0, 1 / 4, 3 / 4, 0, 0, 0, 0]

/-- The meaning of report `lo`: the clean posterior on the clean `lo`-fibre, `3/4` on `θ = 0`.
Source: mandate Target 6
Kind: D
Fidelity: exact -/
def ρlo : Fin 8 → ℝ := ![3 / 4, 1 / 4, 0, 0, 0, 0, 0, 0]

/-- Both rows are distributions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ρ_mem : ρhi ∈ stdSimplex ℝ (Fin 8) ∧ ρlo ∈ stdSimplex ℝ (Fin 8) := by
  constructor <;> refine ⟨fun x => by fin_cases x <;> norm_num [ρhi, ρlo], ?_⟩ <;>
    simp [Fin.sum_univ_eight, ρhi, ρlo, vec8_two, vec8_three, vec8_four, vec8_five, vec8_six,
      vec8_seven] <;> norm_num

/-- The rows differ.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ρhi_ne_ρlo : ρhi ≠ ρlo := by
  intro h
  have := congrFun h 0
  simp [ρhi, ρlo] at this
  norm_num at this

/-- **The frame**: at every world the expert's row is the meaning of the world's report.
Source: mandate Target 6 ("One `Frame W` whose row at `w` is `ρ_{r(w)}`")
Kind: D
Fidelity: exact -/
def F : Frame (Fin 8) where
  P := fun w => if rep w = 1 then ρhi else ρlo
  P_mem := fun w => by
    split_ifs
    · exact ρ_mem.1
    · exact ρ_mem.2

/-- The rows of the frame, listed.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem F_P : F.P = ![ρlo, ρlo, ρhi, ρhi, ρlo, ρlo, ρhi, ρhi] := by
  funext w
  fin_cases w <;> simp [F, rep, vec8_two, vec8_three, vec8_four, vec8_five, vec8_six, vec8_seven]

/-- The expert's expectation of `θ` is `3/4` on the `hi` row and `1/4` on the `lo` row.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_rows : E ρhi θ8 = 3 / 4 ∧ E ρlo θ8 = 1 / 4 := by
  constructor <;>
    simp only [E, Fin.sum_univ_eight, ρhi, ρlo, θ8, vec8_two, vec8_three, vec8_four, vec8_five,
      vec8_six, vec8_seven] <;> norm_num

/-! ## The priors -/

/-- The clean prior: report correlated with `θ` (`(hi, 1) 3/8, (hi, 0) 1/8, (lo, 1) 1/8,
(lo, 0) 3/8`), supported on clean worlds.
Source: mandate Target 6
Kind: D
Fidelity: exact -/
def πclean : Fin 8 → ℝ := ![3 / 8, 1 / 8, 1 / 8, 3 / 8, 0, 0, 0, 0]

/-- The manipulated prior: same report marginal, report decoupled from `θ` (`(hi, 1) 1/8,
(hi, 0) 3/8, (lo, 1) 1/8, (lo, 0) 3/8`), supported on manipulated worlds.
Source: mandate Target 6
Kind: D
Fidelity: exact -/
def πmanip : Fin 8 → ℝ := ![0, 0, 0, 0, 3 / 8, 1 / 8, 3 / 8, 1 / 8]

/-- The mixture prior with manipulator weight `λ`.
Source: mandate Target 6
Kind: D
Fidelity: exact -/
def πmix (l : ℝ) : Fin 8 → ℝ := (1 - l) • πclean + l • πmanip

/-- The mixture at `λ = 1` is the manipulated prior, at `λ = 0` the clean one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πmix_one_zero : πmix 1 = πmanip ∧ πmix 0 = πclean := by
  constructor <;> funext w <;> simp [πmix]

/-- The clean prior and every mixture with `λ ∈ [0, 1]` are distributions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem priors_mem :
    πclean ∈ stdSimplex ℝ (Fin 8) ∧ ∀ l : ℝ, 0 ≤ l → l ≤ 1 → πmix l ∈ stdSimplex ℝ (Fin 8) := by
  refine ⟨⟨fun x => by fin_cases x <;> norm_num [πclean], ?_⟩, fun l hl0 hl1 => ⟨fun x => ?_, ?_⟩⟩
  · simp [Fin.sum_univ_eight, πclean, vec8_two, vec8_three, vec8_four, vec8_five, vec8_six,
      vec8_seven]
    norm_num
  · fin_cases x <;> simp [πmix, πclean, πmanip, vec8_two, vec8_three, vec8_four, vec8_five,
      vec8_six, vec8_seven] <;> nlinarith
  · simp [Fin.sum_univ_eight, πmix, πclean, πmanip, vec8_two, vec8_three, vec8_four, vec8_five,
      vec8_six, vec8_seven]
    ring

/-- The report marginal of a prior: the mass of each report value.
Source: mandate Target 6 (i) ("everything the novice sees")
Kind: D
Fidelity: exact -/
def reportMarginal (π : Fin 8 → ℝ) : Fin 2 → ℝ := fun r => mass π (univ.filter (fun w => rep w = r))

/-! ## (i) Observables coincide -/

/-- **Observables coincide.** The report marginal is `(1/2, 1/2)` under the clean prior and under
every mixture — computed, not assumed.
Source: trust-lab-2-035 (i); mandate Target 6 (i)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem reportMarginal_eq (l : ℝ) :
    reportMarginal (πmix l) = ![1 / 2, 1 / 2] ∧ reportMarginal πclean = ![1 / 2, 1 / 2] := by
  constructor <;> funext r <;> fin_cases r <;>
    simp [reportMarginal, mass, Finset.sum_filter, Fin.sum_univ_eight, πmix, πclean, πmanip, rep,
      vec8_two, vec8_three, vec8_four, vec8_five, vec8_six, vec8_seven] <;> ring

/-- **Every function of the report marginal** takes the same value under the clean prior and under
every mixture (the honest two-point form: `congrArg` on the computed equality).
Source: trust-lab-2-035 (i); trust-lab-050 (`gate_blind`)
Kind: L
Fidelity: exact -/
theorem observable_blind {α : Sort*} (g : (Fin 2 → ℝ) → α) (l : ℝ) :
    g (reportMarginal (πmix l)) = g (reportMarginal πclean) := by
  rw [(reportMarginal_eq l).1, (reportMarginal_eq l).2]

/-! ## (ii) Trust verdicts differ -/

/-- Membership of a two-point convex combination in the hull.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_hull_of_comb {s : Set (Fin 8 → ℝ)} {x y z : Fin 8 → ℝ} (hx : x ∈ s) (hy : y ∈ s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hz : z = a • x + b • y) :
    z ∈ convexHull ℝ s := by
  rw [hz]
  exact (convex_convexHull ℝ s) (subset_convexHull ℝ s hx) (subset_convexHull ℝ s hy) ha hb hab

/-- The candidates of the clean prior are the two rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cands_clean : F.cands πclean = {ρlo, ρhi} := by
  ext σ
  rw [Frame.mem_cands]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [F_P]
    fin_cases w <;> simp [πclean, vec8_two, vec8_three, vec8_four, vec8_five, vec8_six,
      vec8_seven] at hw ⊢
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num [πclean], by rw [F_P]; rfl⟩
    · exact ⟨3, by norm_num [πclean, vec8_three], by rw [F_P]; rfl⟩

/-- The cells of the two rows are the report fibres.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cells :
    F.cell ρhi = univ.filter (fun w => rep w = 1) ∧ F.cell ρlo = univ.filter (fun w => rep w = 0) := by
  constructor <;> ext w <;> fin_cases w <;>
    simp [Frame.mem_cell, F_P, rep, ρhi_ne_ρlo, ρhi_ne_ρlo.symm, vec8_two, vec8_three, vec8_four,
      vec8_five, vec8_six, vec8_seven]

/-- Both rows put all their mass on their own cell (self-mass `1`), so their informed selves are
themselves.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem selfMass_informed :
    F.selfMass ρhi = 1 ∧ F.selfMass ρlo = 1 ∧ F.informed ρhi = ρhi ∧ F.informed ρlo = ρlo := by
  have hhi : F.selfMass ρhi = 1 := by
    rw [Frame.selfMass, cells.1]
    simp [mass, Finset.sum_filter, Fin.sum_univ_eight, rep, ρhi, vec8_two, vec8_three, vec8_four,
      vec8_five, vec8_six, vec8_seven]
    norm_num
  have hlo : F.selfMass ρlo = 1 := by
    rw [Frame.selfMass, cells.2]
    simp [mass, Finset.sum_filter, Fin.sum_univ_eight, rep, ρlo, vec8_two, vec8_three, vec8_four,
      vec8_five, vec8_six, vec8_seven]
    norm_num
  refine ⟨hhi, hlo, ?_, ?_⟩
  · funext w
    rw [Frame.informed, hhi, F_P]
    fin_cases w <;> simp [ρhi, ρhi_ne_ρlo.symm, vec8_two, vec8_three, vec8_four,
      vec8_five, vec8_six, vec8_seven]
  · funext w
    rw [Frame.informed, hlo, F_P]
    fin_cases w <;> simp [ρlo, ρhi_ne_ρlo, vec8_two, vec8_three, vec8_four,
      vec8_five, vec8_six, vec8_seven]

/-- The clean prior is the even mixture of the two rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πclean_comb : πclean = (1 / 2 : ℝ) • ρlo + (1 / 2 : ℝ) • ρhi := by
  funext w
  fin_cases w <;> simp [πclean, ρlo, ρhi, vec8_two, vec8_three, vec8_four, vec8_five, vec8_six,
    vec8_seven] <;> norm_num

/-- The clean prior satisfies the hull-and-modestly-informed condition of Theorem 7.6, with
explicit weights: `πclean = ½ ρlo + ½ ρhi`, and each row is its own informed self.
Source: mandate Target 6 (ii) (the pattern of `Examples.fig3_hull`)
Kind: L
Fidelity: n/a -/
theorem hull_clean : HullAndModestlyInformed πclean F := by
  obtain ⟨hhi, hlo, ihi, ilo⟩ := selfMass_informed
  refine ⟨?_, ?_⟩
  · rw [cands_clean]
    exact mem_hull_of_comb (x := ρlo) (y := ρhi) (by simp) (by simp)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) πclean_comb
  · intro ρ hρ
    rw [cands_clean] at hρ
    simp only [mem_insert, mem_singleton] at hρ
    rcases hρ with rfl | rfl
    · refine ⟨by rw [hlo]; norm_num, ?_⟩
      rw [ilo]
      exact subset_convexHull ℝ _ (Set.mem_insert _ _)
    · refine ⟨by rw [hhi]; norm_num, ?_⟩
      rw [ihi]
      exact subset_convexHull ℝ _ (Set.mem_insert _ _)

/-- **Total Trust holds under the clean prior**, with the exact `∀ X s` quantifier, through the
cycle of `lit-ddb-frames` (Theorem 7.6). *Why it holds*: this is the self-certain (partition
expert) case — both rows have self-mass `1` and are their own informed selves
(`selfMass_informed`), so on the clean worlds `F` is a partition expert and `πclean` is its even
mixture (`πclean_comb`); nothing subtler than the hull condition with explicit weights is at work.
Source: trust-lab-2-035 (ii) (positive half); mandate Target 6 (ii)
Kind: C
Fidelity: stronger: exact quantifier instead of the source's declared indicator grid
Hyps: (a) none (the cycle is the dependency's theorem) -/
theorem totalTrust_clean : TotalTrust πclean F :=
  (totalTrust_iff_hullAndModestlyInformed priors_mem.1 F).2 hull_clean

/-- The product sum of Total Trust at `X = 𝟙[θ = 1]`, `s = 3/4` under the mixture is `−λ/4`.
Source: mandate Target 6 (ii)
Kind: L
Fidelity: n/a -/
theorem mix_product_sum (l : ℝ) :
    ∑ w, πmix l w * (θ8 w - 3 / 4) * (if (3 / 4 : ℝ) ≤ E (F.P w) θ8 then 1 else 0) = -l / 4 := by
  obtain ⟨ehi, elo⟩ := E_rows
  simp only [Fin.sum_univ_eight, F_P, vec8_two, vec8_three, vec8_four, vec8_five, vec8_six,
    vec8_seven, Matrix.cons_val_zero, Matrix.cons_val_one, ehi, elo]
  simp only [πmix, πclean, πmanip, θ8, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec8_two,
    vec8_three, vec8_four, vec8_five, vec8_six, vec8_seven, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num <;> linarith

/-- **Total Trust fails under every mixture with positive manipulator weight**, at
`X = 𝟙[θ = 1]`, `s = 3/4`: the event is `{rep = hi}` and the product sum is `−λ/4 < 0`. *Why it
fails, and how bluntly*: both rows vanish on the manipulated worlds, which carry mass `3λ/8`,
`λ/8` under `πmix λ` (`manip_worlds_outside_rows`), so the expert is wrong about the mechanism at
every manipulated world and `πmix λ` cannot lie in the hull of `{ρlo, ρhi}` — the failure is at
the hull condition of the cycle, not a subtle threshold effect, and every rung of the
trust ladder fails under the mixture, not Total Trust specifically. The explicit `(X, s)` is the
reader-facing face of that. This is the source's intended modelling (the report keeps its clean
meaning at a manipulated world).
Source: trust-lab-2-035 (ii) (negative half); mandate Target 6 (ii)
Kind: P
Fidelity: stronger: for every `λ > 0`, not one declared `λ`; the mixtures with `λ ≤ 1` are priors
(`priors_mem`)
Hyps: (a) `0 < λ` -/
theorem not_totalTrust_mix {l : ℝ} (hl : 0 < l) : ¬ TotalTrust (πmix l) F := by
  intro h
  have := h θ8 (3 / 4)
  rw [mix_product_sum] at this
  linarith

/-- Why the mixture fails: the rows vanish at the manipulated `hi`-world `6`, which the frame
labels `ρhi` and which carries mass `3λ/8 > 0` under every `πmix λ`, `λ > 0`.
Source: audit round 1 (adversarial probe P4); mandate Target 6
Kind: L
Fidelity: n/a -/
theorem manip_worlds_outside_rows (l : ℝ) (hl : 0 < l) :
    ρhi 6 = 0 ∧ ρlo 6 = 0 ∧ F.P 6 = ρhi ∧ πmix l 6 = 3 * l / 8 ∧ 0 < πmix l 6 := by
  refine ⟨by simp [ρhi, vec8_six], by simp [ρlo, vec8_six], by rw [F_P]; simp [vec8_six], ?_, ?_⟩
  · simp [πmix, πclean, πmanip, vec8_six]
    ring
  · simp [πmix, πclean, πmanip, vec8_six]
    linarith

/-- **Mechanism non-identifiability**, assembled: the report marginals coincide, Total Trust holds
under the clean prior and fails under every mixture with `0 < λ ≤ 1` (each a prior).
Source: trust-lab-2-035; mandate Target 6 (load-bearing 4)
Kind: C
Fidelity: exact (with the exact quantifier)
Hyps: (a) none -/
theorem mechanism_nonidentifiable :
    (∀ l, reportMarginal (πmix l) = reportMarginal πclean) ∧ TotalTrust πclean F ∧
      ∀ l, 0 < l → l ≤ 1 → πmix l ∈ stdSimplex ℝ (Fin 8) ∧ ¬ TotalTrust (πmix l) F :=
  ⟨fun l => observable_blind id l, totalTrust_clean,
    fun l hl0 hl1 => ⟨priors_mem.2 l hl0.le hl1, not_totalTrust_mix hl0⟩⟩

/-! ## (iii) Near-miss: the mechanism-conditional test separates -/

/-- **Near-miss.** The manipulator's own fibre `πmanip = πmix 1` fails Total Trust at the same
`(X, s)`: a test conditional on the mechanism bit separates what the report marginal cannot.
Source: trust-lab-2-035 (iii); mandate Target 6 (iii)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem not_totalTrust_manip : ¬ TotalTrust πmanip F := by
  rw [← πmix_one_zero.1]
  exact not_totalTrust_mix one_pos

end

end Cleanroom.Trust.LegitFiniteDefect.Mechanism
