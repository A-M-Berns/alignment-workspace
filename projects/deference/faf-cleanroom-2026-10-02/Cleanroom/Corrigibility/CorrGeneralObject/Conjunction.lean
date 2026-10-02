import Cleanroom.Corrigibility.CorrGeneralObject.Support

/-!
# corr-general-object — T3: acting on `Q` is a conjunction of below-threshold inequalities

* **(a)** (L) Optimality of `a` under the post-push credence is the conjunction, over every
  alternative `b`, of `corr-three-step`'s below-threshold inequality on `V b − V a`
  (`isOptimal_postPush_iff_belowThreshold`), through the bridge — `d1At_iff_forall_cont` with
  `a^Q` in the shutdown slot.
* **(b)** (L) The base-rate form per `(Q, a)`: the push expectation of `X_{Q,a}` splits over
  `R` and `W` (the `I` term vanishes, `pushExpect_devVar_split`); the inequality is
  `∑_R P k X ≤ −∑_W P k X` (`belowThreshold_iff_R_le_W`); with the four positivity guards the
  divided odds form `α/β ≤ (ε/(1−ε)) · (h/c)` (`belowThreshold_iff_odds`), with `c, h > 0`
  *proved* from the sign of `X` on `R`, `W` (`gainR_pos`, `harmW_pos`).
* **(c)** (P + N+, the headline) On a two-action menu the single member against the alternative
  suffices (`card_two_single_member_iff`); on three actions it does not: (A′) —
  `P = (16/25, 3/25, 6/25)`, `Q = (15/46, 13/46, 18/46)`, `V = [(3,−1,8),(3,8,6),(7,2,−1)]`,
  `k = (2/15, 3/16, 11/16)`: `a^P = plan₃`, `a^Q = plan₂`, posterior `(512, 135, 990)/1637`,
  the `plan₃` member holds, the `plan₁` member fails (`ap_*`).

Sources: [[general-object-final]] S2(a)(b)(c), P3, (A′), R1; [[corr-wf14b-inventory]] 004.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {A : Type} [Fintype A] [DecidableEq A]

/-! ## (a) the conjunction through the bridge -/

/-- **T3(a)**: `a` is optimal under `P(· | E_Q)` iff for every `b` the below-threshold inequality
of Setting S holds on `V b − V a` — `d1At_iff_forall_cont` with `a` in the shutdown slot
(`Sh = {a}`). The law of total expectation, three ways (the source says so): kind L.
Source: [[general-object-final]] S2(a), P3(a); filler F1 through `corr-three-step`
Kind: L
Fidelity: exact
Hyps: (a) the positivity guard; `{a}ᶜ` nonempty (a menu with an alternative) -/
theorem isOptimal_postPush_iff_belowThreshold (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k)
    (V : A → Ω → ℝ) (h : 0 < pushMass P k) (a : A) (h2 : ({a} : Finset A)ᶜ.Nonempty) :
    IsOptimal (postPush P k hk.nonneg h) V a ↔
      ∀ b, (toThreeStep P k hk V {a} (singleton_nonempty a) h2).belowThresholdIneq () (V b - V a) := by
  rw [isOptimal_postPush_iff P hk V h a]
  simp only [toThreeStep_belowThresholdIneq]

/-- **T3(a), the `D1At` form**: optimality of `a` under the post-push credence is desideratum 1
of the bridge with `Sh = {a}`.
Source: [[general-object-final]] S2(a)
Kind: L
Fidelity: exact
Hyps: (a) as above -/
theorem isOptimal_postPush_iff_d1At (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k)
    (V : A → Ω → ℝ) (h : 0 < pushMass P k) (a : A) (h2 : ({a} : Finset A)ᶜ.Nonempty) :
    IsOptimal (postPush P k hk.nonneg h) V a ↔
      (toThreeStep P k hk V {a} (singleton_nonempty a) h2).D1At () := by
  rw [isOptimal_postPush_iff P hk V h a, toThreeStep_d1At_singleton_iff]

/-! ## (b) the base-rate form per `(Q, a)` -/

/-- **The push expectation of `X_{Q,a}` splits over `R` and `W`**; the indifference term vanishes.
Source: [[general-object-final]] P3(b) ("the last term is `0`")
Kind: L
Fidelity: exact -/
theorem pushExpect_devVar_split (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ a : A) :
    pushExpect P k (devVar V πQ a) =
      ∑ ω ∈ Rset V πQ a, P.mass ω * k ω * devVar V πQ a ω +
        ∑ ω ∈ Wset V πQ a, P.mass ω * k ω * devVar V πQ a ω := by
  unfold pushExpect Rset Wset
  rw [← sum_filter_add_sum_filter_not univ (fun ω => 0 < devVar V πQ a ω)]
  congr 1
  rw [← sum_filter_add_sum_filter_not (univ.filter fun ω => ¬ 0 < devVar V πQ a ω)
    (fun ω => devVar V πQ a ω < 0)]
  have h1 : (univ.filter fun ω => ¬ 0 < devVar V πQ a ω).filter (fun ω => devVar V πQ a ω < 0) =
      univ.filter fun ω => devVar V πQ a ω < 0 := by
    ext ω; simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨not_lt.2 h.le, h⟩⟩
  have h2 : ∑ ω ∈ (univ.filter fun ω => ¬ 0 < devVar V πQ a ω).filter
      (fun ω => ¬ devVar V πQ a ω < 0), P.mass ω * k ω * devVar V πQ a ω = 0 := by
    apply sum_eq_zero
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    have : devVar V πQ a ω = 0 := le_antisymm (not_lt.1 hω.1) (not_lt.1 hω.2)
    rw [this, mul_zero]
  rw [h1, h2, add_zero]

/-- **The base-rate inequality in product form**: `E[X_{Q,a} 1_{E_Q}] ≤ 0` iff the `R`-part is
at most the negated `W`-part.
Source: [[general-object-final]] S2(b), P3(b)
Kind: L
Fidelity: exact -/
theorem belowThreshold_iff_R_le_W (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ a : A) :
    pushExpect P k (devVar V πQ a) ≤ 0 ↔
      ∑ ω ∈ Rset V πQ a, P.mass ω * k ω * devVar V πQ a ω ≤
        -(∑ ω ∈ Wset V πQ a, P.mass ω * k ω * devVar V πQ a ω) := by
  rw [pushExpect_devVar_split]
  constructor <;> intro h <;> linarith

/-- The sensor rate on `R`, `α_{Q,a} = P(E_Q | R_{Q,a})` (junk at `P(R) = 0`).
Source: [[general-object-final]] D10
Kind: D
Fidelity: exact under `0 < P(R)` -/
def sensorR (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ a : A) : ℝ :=
  (∑ ω ∈ Rset V πQ a, P.mass ω * k ω) / ∑ ω ∈ Rset V πQ a, P.mass ω

/-- The sensor rate on `W`, `β_{Q,a} = P(E_Q | W_{Q,a})` (junk at `P(W) = 0`).
Source: [[general-object-final]] D10
Kind: D
Fidelity: exact under `0 < P(W)` -/
def sensorW (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ a : A) : ℝ :=
  (∑ ω ∈ Wset V πQ a, P.mass ω * k ω) / ∑ ω ∈ Wset V πQ a, P.mass ω

/-- The press-conditional gain `c(Q,a) = E[X_{Q,a} | E_Q, R_{Q,a}]` (junk at zero mass).
Source: [[general-object-final]] D10
Kind: D
Fidelity: exact under `0 < P(E_Q ∧ R)` -/
def gainR (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ a : A) : ℝ :=
  (∑ ω ∈ Rset V πQ a, P.mass ω * k ω * devVar V πQ a ω) / ∑ ω ∈ Rset V πQ a, P.mass ω * k ω

/-- The press-conditional harm `h(Q,a) = −E[X_{Q,a} | E_Q, W_{Q,a}]` (junk at zero mass).
Source: [[general-object-final]] D10
Kind: D
Fidelity: exact under `0 < P(E_Q ∧ W)` -/
def harmW (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ a : A) : ℝ :=
  -(∑ ω ∈ Wset V πQ a, P.mass ω * k ω * devVar V πQ a ω) / ∑ ω ∈ Wset V πQ a, P.mass ω * k ω

/-- The error rate on decision-relevant worlds `ε_{Q,a} = P(W)/(P(W) + P(R))`.
Source: [[general-object-final]] D10
Kind: D
Fidelity: exact under `0 < P(W) + P(R)` -/
def errRate (P : Distr Ω) (V : A → Ω → ℝ) (πQ a : A) : ℝ :=
  (∑ ω ∈ Wset V πQ a, P.mass ω) / ((∑ ω ∈ Wset V πQ a, P.mass ω) + ∑ ω ∈ Rset V πQ a, P.mass ω)

/-- The push mass on `R` bounds the mass of `R` from below (kernel ≤ 1).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sum_le_sum_of_kernel (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k) (S : Finset Ω) :
    ∑ ω ∈ S, P.mass ω * k ω ≤ ∑ ω ∈ S, P.mass ω :=
  sum_le_sum fun ω _ => by
    have := mul_le_mul_of_nonneg_left (hk ω).2 (P.nonneg ω); simpa using this

/-- **`c(Q,a) > 0`**, proved from the sign of `X` on `R` (not assumed).
Source: [[general-object-final]] D10 (the mandate: "`c > 0` and `h > 0` proved")
Kind: L
Fidelity: exact
Hyps: (a) `0 < P(E_Q ∧ R)`, `k ≥ 0` -/
theorem gainR_pos (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k) (V : A → Ω → ℝ) (πQ a : A)
    (hR : 0 < ∑ ω ∈ Rset V πQ a, P.mass ω * k ω) : 0 < gainR P k V πQ a := by
  unfold gainR
  apply div_pos _ hR
  obtain ⟨ω₀, hω₀, hpos⟩ :=
    (sum_pos_iff_of_nonneg fun ω _ => mul_nonneg (P.nonneg ω) (hk ω).1).1 hR
  apply sum_pos'
  · intro ω hω
    have hX : 0 < devVar V πQ a ω := by simpa [Rset] using hω
    exact mul_nonneg (mul_nonneg (P.nonneg ω) (hk ω).1) hX.le
  · refine ⟨ω₀, hω₀, ?_⟩
    have hX : 0 < devVar V πQ a ω₀ := by simpa [Rset] using hω₀
    exact mul_pos hpos hX

/-- **`h(Q,a) > 0`**, proved from the sign of `X` on `W`.
Source: [[general-object-final]] D10
Kind: L
Fidelity: exact
Hyps: (a) `0 < P(E_Q ∧ W)`, `k ≥ 0` -/
theorem harmW_pos (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k) (V : A → Ω → ℝ) (πQ a : A)
    (hW : 0 < ∑ ω ∈ Wset V πQ a, P.mass ω * k ω) : 0 < harmW P k V πQ a := by
  unfold harmW
  obtain ⟨ω₀, hω₀, hpos⟩ :=
    (sum_pos_iff_of_nonneg fun ω _ => mul_nonneg (P.nonneg ω) (hk ω).1).1 hW
  have hneg : 0 < ∑ ω ∈ Wset V πQ a, P.mass ω * k ω * -(devVar V πQ a ω) := by
    apply sum_pos'
    · intro ω hω
      have hX : devVar V πQ a ω < 0 := by simpa [Wset] using hω
      exact mul_nonneg (mul_nonneg (P.nonneg ω) (hk ω).1) (by linarith)
    · refine ⟨ω₀, hω₀, ?_⟩
      have hX : devVar V πQ a ω₀ < 0 := by simpa [Wset] using hω₀
      exact mul_pos hpos (by linarith)
  have e : ∑ ω ∈ Wset V πQ a, P.mass ω * k ω * -(devVar V πQ a ω) =
      -(∑ ω ∈ Wset V πQ a, P.mass ω * k ω * devVar V πQ a ω) := by
    rw [← sum_neg_distrib]; apply sum_congr rfl; intro ω _; ring
  rw [e] at hneg
  exact div_pos hneg hW

/-- **The odds form of the base-rate inequality** (T3(b), the source's exact statement): with
`P(E_Q ∧ R) > 0` and `P(E_Q ∧ W) > 0` (which give `P(R), P(W) > 0` for a kernel),
`E[X_{Q,a} 1_{E_Q}] ≤ 0 ↔ α/β ≤ (ε/(1−ε)) · (h/c)`.
Source: [[general-object-final]] S2(b), P3(b); v1 §2.13(b) per `(Q, a)`
Kind: L
Fidelity: exact
Hyps: (a) the two positivity guards; `IsKernel k` -/
theorem belowThreshold_iff_odds (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k) (V : A → Ω → ℝ)
    (πQ a : A) (hR : 0 < ∑ ω ∈ Rset V πQ a, P.mass ω * k ω)
    (hW : 0 < ∑ ω ∈ Wset V πQ a, P.mass ω * k ω) :
    pushExpect P k (devVar V πQ a) ≤ 0 ↔
      sensorR P k V πQ a / sensorW P k V πQ a ≤
        (errRate P V πQ a / (1 - errRate P V πQ a)) * (harmW P k V πQ a / gainR P k V πQ a) := by
  have hmR : 0 < ∑ ω ∈ Rset V πQ a, P.mass ω := lt_of_lt_of_le hR (sum_le_sum_of_kernel P hk _)
  have hmW : 0 < ∑ ω ∈ Wset V πQ a, P.mass ω := lt_of_lt_of_le hW (sum_le_sum_of_kernel P hk _)
  have hc := gainR_pos P hk V πQ a hR
  have hh := harmW_pos P hk V πQ a hW
  rw [belowThreshold_iff_R_le_W]
  set eR := ∑ ω ∈ Rset V πQ a, P.mass ω * k ω with heR
  set eW := ∑ ω ∈ Wset V πQ a, P.mass ω * k ω with heW
  set mR := ∑ ω ∈ Rset V πQ a, P.mass ω with hmR'
  set mW := ∑ ω ∈ Wset V πQ a, P.mass ω with hmW'
  set vR := ∑ ω ∈ Rset V πQ a, P.mass ω * k ω * devVar V πQ a ω with hvR
  set vW := -(∑ ω ∈ Wset V πQ a, P.mass ω * k ω * devVar V πQ a ω) with hvW
  have hvRpos : 0 < vR := by
    have := hc; unfold gainR at this; rw [← heR, ← hvR] at this
    exact (div_pos_iff_of_pos_right hR).1 this
  have hvWpos : 0 < vW := by
    have := hh; unfold harmW at this; rw [← heW, ← hvW] at this
    exact (div_pos_iff_of_pos_right hW).1 this
  have e1 : sensorR P k V πQ a / sensorW P k V πQ a = (eR * mW) / (mR * eW) := by
    unfold sensorR sensorW; rw [← heR, ← heW, ← hmR', ← hmW']; field_simp
  have e2 : (errRate P V πQ a / (1 - errRate P V πQ a)) * (harmW P k V πQ a / gainR P k V πQ a) =
      (mW * vW * eR) / (mR * eW * vR) := by
    unfold errRate harmW gainR; rw [← heR, ← heW, ← hmR', ← hmW', ← hvR, ← hvW]
    have hne : mW + mR ≠ 0 := by positivity
    have : 1 - mW / (mW + mR) = mR / (mW + mR) := by
      rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]; ring
    rw [this]; field_simp
  rw [e1, e2, div_le_iff₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  constructor
  · intro h
    have : eR * mW * (mR * eW * vR) = (eR * mW * mR * eW) * vR := by ring
    have h2 : mW * vW * eR * (mR * eW) = (eR * mW * mR * eW) * vW := by ring
    rw [this, h2]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  · intro h
    have e3 : eR * mW * (mR * eW * vR) = (eR * mW * mR * eW) * vR := by ring
    have e4 : mW * vW * eR * (mR * eW) = (eR * mW * mR * eW) * vW := by ring
    rw [e3, e4] at h
    exact le_of_mul_le_mul_left h (by positivity)

/-! ## (c) the two-action reduction and its failure on three actions -/

/-- **T3(c), the reduction**: on a two-action menu the single member against the alternative
`b ≠ πQ` is the whole conjunction — `E[(V b − V πQ) 1_{E_Q}] ≤ 0 ↔ πQ` optimal after the push.
(The source writes the alternative as `a^P`; on two actions with the push decision-relevant it is
the unique `b ≠ πQ`, and `IsOptimal P b` is not needed for the equivalence.) The proof is a case
split whose other case is `E[(V πQ − V πQ) 1_{E_Q}] ≤ 0`, i.e. `0 ≤ 0`: kind L (audit r1 B2).
S2(c)'s content — that the reduction *fails* on three actions — lives in the witnesses
`ap_witness` ((A′): the `plan₃` member holds, the `plan₁` member fails) and `ce3_witness`.
Source: [[general-object-final]] S2(c) ("sufficient iff `|A| = 2`"); `d1At_of_singleton_cont`
Kind: L
Fidelity: exact
Hyps: (a) `card A = 2`, `b ≠ πQ`, the positivity guard -/
theorem card_two_single_member_iff (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k) (V : A → Ω → ℝ)
    (h : 0 < pushMass P k) (hcard : Fintype.card A = 2) {πQ b : A} (hb : b ≠ πQ) :
    pushExpect P k (V b - V πQ) ≤ 0 ↔ IsOptimal (postPush P k hk.nonneg h) V πQ := by
  rw [isOptimal_postPush_iff P hk V h πQ]
  constructor
  · intro hmem b'
    have huniv : ({πQ, b} : Finset A) = univ :=
      eq_univ_of_card _ (by rw [card_pair (Ne.symm hb), hcard])
    have hb' : b' ∈ ({πQ, b} : Finset A) := by rw [huniv]; exact mem_univ _
    rcases mem_insert.1 hb' with h1 | h1
    · subst h1; simp [pushExpect]
    · rw [mem_singleton] at h1; subst h1; exact hmem
  · intro H; exact H b

/-- (A′)'s prior `P = (16/25, 3/25, 6/25)`. Source: [[general-object-final]] P3(c). Kind: D. Fidelity: exact -/
def apP : Distr (Fin 3) where
  mass := ![16/25, 3/25, 6/25]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_three]; norm_num

/-- (A′)'s target `Q = (15/46, 13/46, 18/46)`. Source: [[general-object-final]] P3(c). Kind: D. Fidelity: exact -/
def apQ : Distr (Fin 3) where
  mass := ![15/46, 13/46, 18/46]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_three]; norm_num

/-- (A′)'s payoffs, row = plan, column = world: `[(3,−1,8),(3,8,6),(7,2,−1)]`.
Source: [[general-object-final]] P3(c). Kind: D. Fidelity: exact -/
def apV : Fin 3 → Fin 3 → ℝ := ![![3, -1, 8], ![3, 8, 6], ![7, 2, -1]]

/-- (A′)'s kernel `k = (2/15, 3/16, 11/16)`. Source: [[general-object-final]] P3(c). Kind: D. Fidelity: exact -/
def apK : Fin 3 → ℝ := ![2/15, 3/16, 11/16]

/-- (A′)'s kernel is a kernel. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem apK_isKernel : IsKernel apK := fun ω => by fin_cases ω <;> norm_num [apK]

/-- **N+ for T3(c), (A′)**: `a^P = plan₃`, `a^Q = plan₂`; push mass `1637/6000`; the member
against `plan₃` holds, the member against `plan₁` fails, so `plan₂` is *not* optimal after the
push although the agent's-own-plan inequality holds.
Source: [[general-object-final]] P3(c), (A′), R1 ("12 of 814 repair models")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ap_witness :
    IsOptimal apP apV 2 ∧ IsOptimal apQ apV 1 ∧ pushMass apP apK = 1637 / 6000 ∧
      pushExpect apP apK (apV 2 - apV 1) ≤ 0 ∧ 0 < pushExpect apP apK (apV 0 - apV 1) ∧
      ¬ IsOptimal (postPush apP apK apK_isKernel.nonneg
        (by rw [show pushMass apP apK = 1637 / 6000 from by
          simp [pushMass, apP, apK, Fin.sum_univ_three]; norm_num]; norm_num)) apV 1 := by
  have hm : pushMass apP apK = 1637 / 6000 := by
    simp [pushMass, apP, apK, Fin.sum_univ_three]; norm_num
  refine ⟨?_, ?_, hm, ?_, ?_, ?_⟩
  · intro b; fin_cases b <;> simp [expect, apP, apV, Fin.sum_univ_three] <;> norm_num
  · intro b; fin_cases b <;> simp [expect, apQ, apV, Fin.sum_univ_three] <;> norm_num
  · simp [pushExpect, apP, apV, apK, Fin.sum_univ_three]; norm_num
  · simp [pushExpect, apP, apV, apK, Fin.sum_univ_three]; norm_num
  · rw [isOptimal_postPush_iff apP apK_isKernel apV]
    push Not
    exact ⟨0, by simp [pushExpect, apP, apV, apK, Fin.sum_univ_three]; norm_num⟩

/-- (A′)'s posterior is `(512, 135, 990)/1637`. Source: [[general-object-final]] P3(c). Kind: N+. Fidelity: exact -/
theorem ap_postPush_mass (h : 0 < pushMass apP apK) :
    (postPush apP apK apK_isKernel.nonneg h).mass = ![512/1637, 135/1637, 990/1637] := by
  have hm : pushMass apP apK = 1637 / 6000 := by
    simp [pushMass, apP, apK, Fin.sum_univ_three]; norm_num
  funext ω
  rw [postPush_mass, hm]
  fin_cases ω <;> simp [apP, apK] <;> norm_num

end

end Cleanroom.Corrigibility.CorrGeneralObject
