/-
# Logical-induction corrigibility: the finite core and the EPI instantiation

Round `projects/deference/rounds/2026-09-15-li-corrigibility/`.

**1. Directional activation mismatch.**  Two options with their own activation events
`c_raw, c_corr` and activated securities `c_raw · w_raw`, `c_corr · w_act`.
`mismatch_identity` is the exact decomposition of the security difference into a
common-activation term, a raw-only term and a corr-only term; `mismatch_bound` charges the
common term by the reproduction certificate and decline regret, the raw-only term by the
width `D`, and drops the corr-only term, which is never positive.  The mismatch term is
the *joint* event `c_raw ∧ ¬c_corr` in one world; `Witness.marginal_refuted` is the two-
world fixture on which the marginal difference `E[c_raw] − E[c_corr]` is `0` while the
bypass premium is `D/2`.  `Witness.attained` attains `D`.  Common activation is the
special case `c_raw = c_corr`, where the term vanishes (`mismatch_common`) and the bound
is `MediatedRepairDominance.security_score_bypass_le_sharp`'s.

**2. Gated LUVs at the pinned Logical-Induction interface.**  A `LUV` is a threshold
family `gt : ℚ → Sentence`; `GatedAt v G φ X` says `G` is `X` gated by the sentence `φ`
in world `v`, `IndicatorAt v Y ψ` that `Y` is the indicator of `ψ`, and `gate`, `indicator`,
`constLUV` are concrete threshold families with those semantics in every world.  The
compiler lemmas (`GatedAt.valuesAt`, `IndicatorAt.valuesAt`) give the world value of the
gated variable: `x` where `φ` holds, `0` elsewhere.  This is the route by which an
activation-gated product `c · δ` is one `[0,1]`-LUV rather than a product of two.

**3. The compiled constraint.**  `MediatedPair.B` is the LUV combination
`U_raw − U_corr − λ·G_δ − G_ρ − G_M` with constant coefficients (`λ = L·δ_max / D` after
normalisation to `[0,1]`).  `ValidAt p v` is the world-side package — the five world
values, the reproduction certificate and the decline regret on the common-activation
branch — and `ValidAt.value_le_of_valuesAt` is the target shape
`ValidMediatedPair → ∀ W, W(B) ≤ 0`, for every coherent valuation of the terms.

**4. Expectation Provability Induction, instantiated.**  `li_bypass_le` takes the pinned
`BoundedSequence.expcoh` (`thm:expcoh`, from which `thm:expprovind` is two lines in the
paper) with its operational premises as named hypotheses, plus validity in every
completed-theory world, and concludes
`𝔼ₙ(U_raw,n) − 𝔼ₙ(U_corr,n) ≲ₙ λₙ 𝔼ₙ(G_δ,n) + 𝔼ₙ(G_ρ,n) + 𝔼ₙ(G_M,n)`.
No calibration hypothesis appears: the inequality is between the inductor's own
expectations.

**5. Finite-menu uniformisation.**  A hard argmax over a menu is not an expressible
feature; the near-argmax weighting `softWeight` (a normalised continuous threshold
indicator) is, and `softWeight_aggregate_ge` shows its weighted aggregate is at least
the maximum less `2δ`.  `uniform_of_soft` turns `aggregate ≲ₙ 0` into `max ≲ₙ 0` as
`δₙ → 0`; `max_asympLE` is the bounded-menu case, where no selector is needed.

**6. Witnesses.**  `Witness.pair` is a concrete pair over atoms `0, 1` for which `ValidAt`
holds in *every* world (`Witness.valid`), with `B` valued exactly `0` both on a
raw-only-activated world and on a common-activation world (`Witness.attained_mismatch`,
`Witness.attained_common`).

**What this does not establish.**  That any `MediatedPair` sequence is `P`-generable: the
operational premises of `thm:expcoh` are taken as hypotheses, and the round's
`LUV_COMPILATION.md` argues them at the paper's level.  That the world values are the
physical ones: `ValidAt` is what the architecture axioms in `Γ` must supply.  Anything
about the size of the right-hand side.  Names are provisional (`AGENTS.md` standard 6).
-/
import LogicalInduction.Properties.ExpectationProperties
import Workspace.Deference.Contrib.ActivatedValue

namespace Workspace.Deference.Contrib.LICorrigibility

open LogicalInduction
open Filter Topology
open scoped Classical

/-! ## 1. Directional activation mismatch -/

section Pointwise

/-- A Boolean activation as a real indicator. -/
noncomputable def indR (b : Bool) : ℝ := if b then 1 else 0

theorem indR_true : indR true = 1 := by simp [indR]
theorem indR_false : indR false = 0 := by simp [indR]
theorem indR_nonneg (b : Bool) : 0 ≤ indR b := by cases b <;> simp [indR]
theorem indR_le_one (b : Bool) : indR b ≤ 1 := by cases b <;> simp [indR]

/-- **The exact decomposition.**  The difference of two per-option activated securities
is a common-activation difference, plus the raw option's value where only raw activates,
minus the corrigibilized option's value where only it activates. -/
theorem mismatch_identity (cr cc : Bool) (wr wa : ℝ) :
    indR cr * wr - indR cc * wa
      = indR cr * indR cc * (wr - wa) + indR cr * (1 - indR cc) * wr
        - (1 - indR cr) * indR cc * wa := by
  cases cr <;> cases cc <;> simp [indR]

/-- **The exact directional bound.**  On the common branch the reproduction certificate
and the decline regret; on the raw-only branch the raw value itself; the corr-only
branch is never charged. -/
theorem mismatch_bound_exact (L δ ρ wr wapp wa : ℝ) (cr cc : Bool)
    (hwa : 0 ≤ wa)
    (hlip : cr = true → cc = true → |wr - wapp| ≤ L * δ)
    (hρ : cr = true → cc = true → wapp - wa ≤ ρ) :
    indR cr * wr - indR cc * wa
      ≤ indR cr * indR cc * (L * δ + ρ) + indR cr * (1 - indR cc) * wr := by
  cases cr <;> cases cc <;> simp [indR]
  · exact hwa
  · have h1 := le_trans (le_abs_self _) (hlip rfl rfl)
    have h2 := hρ rfl rfl
    linarith

/-- **The directional bound with the width constant.**  `M := c_raw · (1 − c_corr)` is
charged at the width `D` of the protected value. -/
theorem mismatch_bound (D L δ ρ wr wapp wa : ℝ) (cr cc : Bool)
    (hwr : wr ≤ D) (hwa : 0 ≤ wa)
    (hlip : cr = true → cc = true → |wr - wapp| ≤ L * δ)
    (hρ : cr = true → cc = true → wapp - wa ≤ ρ) :
    indR cr * wr - indR cc * wa
      ≤ indR cr * indR cc * (L * δ + ρ) + D * (indR cr * (1 - indR cc)) := by
  have h := mismatch_bound_exact L δ ρ wr wapp wa cr cc hwa hlip hρ
  have hM : indR cr * (1 - indR cc) * wr ≤ D * (indR cr * (1 - indR cc)) := by
    have h0 : 0 ≤ indR cr * (1 - indR cc) :=
      mul_nonneg (indR_nonneg cr) (by linarith [indR_le_one cc])
    nlinarith
  linarith

/-- Under common activation the mismatch term vanishes. -/
theorem mismatch_common (c : Bool) : indR c * (1 - indR c) = 0 := by
  cases c <;> simp [indR]

variable {X : Type*} [Fintype X]

/-- Expectation under a finite credence, over the reals. -/
noncomputable def expectR (μ V : X → ℝ) : ℝ := ∑ x, μ x * V x

/-- **The unsealed security-score bound.**  Per-option activations `cr, cc`; values in
`[0, D]`; the certificate and decline regret needed only where both activate.  Then
`E[U_raw] − E[U_corr] ≤ L·E[c_raw c_corr δ] + E[c_raw c_corr ρ] + D·E[c_raw (1 − c_corr)]`. -/
theorem security_bypass_le_mismatch (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (D L : ℝ)
    (Vr Vapp Vl δ ρ : X → ℝ) (cr cc : X → Bool)
    (hVr : ∀ x, Vr x ≤ D) (hVl : ∀ x, 0 ≤ Vl x)
    (hlip : ∀ x, cr x = true → cc x = true → |Vr x - Vapp x| ≤ L * δ x)
    (hρ : ∀ x, cr x = true → cc x = true → Vapp x - Vl x ≤ ρ x) :
    expectR μ (fun x => indR (cr x) * Vr x) - expectR μ (fun x => indR (cc x) * Vl x)
      ≤ L * expectR μ (fun x => indR (cr x) * indR (cc x) * δ x)
        + expectR μ (fun x => indR (cr x) * indR (cc x) * ρ x)
        + D * expectR μ (fun x => indR (cr x) * (1 - indR (cc x))) := by
  have hpt : ∀ x, indR (cr x) * Vr x - indR (cc x) * Vl x
      ≤ L * (indR (cr x) * indR (cc x) * δ x) + indR (cr x) * indR (cc x) * ρ x
        + D * (indR (cr x) * (1 - indR (cc x))) := by
    intro x
    have h := mismatch_bound D L (δ x) (ρ x) (Vr x) (Vapp x) (Vl x) (cr x) (cc x)
      (hVr x) (hVl x) (hlip x) (hρ x)
    linarith
  have hrhs : L * expectR μ (fun x => indR (cr x) * indR (cc x) * δ x)
        + expectR μ (fun x => indR (cr x) * indR (cc x) * ρ x)
        + D * expectR μ (fun x => indR (cr x) * (1 - indR (cc x)))
      = ∑ x, μ x * (L * (indR (cr x) * indR (cc x) * δ x) + indR (cr x) * indR (cc x) * ρ x
        + D * (indR (cr x) * (1 - indR (cc x)))) := by
    simp only [expectR, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hlhs : expectR μ (fun x => indR (cr x) * Vr x) - expectR μ (fun x => indR (cc x) * Vl x)
      = ∑ x, μ x * (indR (cr x) * Vr x - indR (cc x) * Vl x) := by
    simp only [expectR, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hrhs, hlhs]
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (hμ x)

end Pointwise

/-! ## 2. Gated and indicator LUVs at the Logical-Induction interface -/

section Gated

/-- `⊤` as a sentence. -/
def top : Sentence := LO.Propositional.Formula.falsum.imp LO.Propositional.Formula.falsum

/-- `⊥` as a sentence. -/
def bot : Sentence := LO.Propositional.Formula.falsum

/-- Negation as a sentence. -/
def neg (ψ : Sentence) : Sentence := ψ.imp LO.Propositional.Formula.falsum

theorem holds_top (v : PCWorld) : v.Holds top := fun h => h
theorem not_holds_bot (v : PCWorld) : ¬ v.Holds bot := fun h => h
theorem holds_and_iff (v : PCWorld) (φ ψ : Sentence) :
    v.Holds (LO.Propositional.Formula.and φ ψ) ↔ v.Holds φ ∧ v.Holds ψ := Iff.rfl
theorem holds_neg_iff (v : PCWorld) (ψ : Sentence) : v.Holds (neg ψ) ↔ ¬ v.Holds ψ := Iff.rfl

/-- `G` is `X` gated by `φ` in world `v`: below `0` every threshold holds; at `r ≥ 0`,
`G > r` iff `φ` and `X > r`. -/
def GatedAt (v : PCWorld) (G : LUV) (φ : Sentence) (X : LUV) : Prop :=
  ∀ r : ℚ, ((r : ℝ) < 0 → v.Holds (G.gt r)) ∧
    (0 ≤ (r : ℝ) → (v.Holds (G.gt r) ↔ (v.Holds φ ∧ v.Holds (X.gt r))))

/-- `Y` is the indicator of `ψ` in world `v` (the pointwise form of the pinned
`LUV.IsIndicator`). -/
def IndicatorAt (v : PCWorld) (Y : LUV) (ψ : Sentence) : Prop :=
  ∀ r : ℚ, ((r : ℝ) < 0 → v.Holds (Y.gt r)) ∧
    (0 ≤ (r : ℝ) → (r : ℝ) < 1 → (v.Holds (Y.gt r) ↔ v.Holds ψ)) ∧
    (1 ≤ (r : ℝ) → ¬ v.Holds (Y.gt r))

theorem IndicatorAt.of_isIndicator {Y : LUV} {ψ : Sentence} {DP : DeductiveProcess}
    (h : Y.IsIndicator ψ DP) (v : PCWorld) (hv : v.ConsistentWithTheory DP) :
    IndicatorAt v Y ψ := h v hv

/-- **Compiler lemma, gate open.**  Where `φ` holds the gated variable takes `X`'s value. -/
theorem GatedAt.valuesAt_of_holds {v : PCWorld} {G : LUV} {φ : Sentence} {X : LUV} {x : ℝ}
    (h : GatedAt v G φ X) (hφ : v.Holds φ) (hx : v.ValuesAt X x) : v.ValuesAt G x := by
  refine ⟨hx.1, hx.2.1, fun r => ⟨fun hr => ?_, fun hr hG => ?_⟩⟩
  · by_cases hr0 : (r : ℝ) < 0
    · exact (h r).1 hr0
    · exact ((h r).2 (not_lt.mp hr0)).mpr ⟨hφ, (hx.2.2 r).1 hr⟩
  · have hr0 : 0 ≤ (r : ℝ) := hx.1.trans hr.le
    exact (hx.2.2 r).2 hr (((h r).2 hr0).mp hG).2

/-- **Compiler lemma, gate closed.**  Where `φ` fails the gated variable is `0`. -/
theorem GatedAt.valuesAt_of_not_holds {v : PCWorld} {G : LUV} {φ : Sentence} {X : LUV}
    (h : GatedAt v G φ X) (hφ : ¬ v.Holds φ) : v.ValuesAt G 0 := by
  refine ⟨le_rfl, zero_le_one, fun r => ⟨fun hr => (h r).1 hr, fun hr hG => ?_⟩⟩
  exact hφ (((h r).2 hr.le).mp hG).1

/-- The gated variable's value in one expression. -/
theorem GatedAt.valuesAt {v : PCWorld} {G : LUV} {φ : Sentence} {X : LUV} {x : ℝ}
    (h : GatedAt v G φ X) (hx : v.ValuesAt X x) :
    v.ValuesAt G (if v.Holds φ then x else 0) := by
  by_cases hφ : v.Holds φ
  · simpa [hφ] using h.valuesAt_of_holds hφ hx
  · simpa [hφ] using h.valuesAt_of_not_holds hφ

/-- **Compiler lemma, indicator.** -/
theorem IndicatorAt.valuesAt {v : PCWorld} {Y : LUV} {ψ : Sentence}
    (h : IndicatorAt v Y ψ) : v.ValuesAt Y (if v.Holds ψ then 1 else 0) := by
  by_cases hψ : v.Holds ψ
  · simp only [hψ, if_true]
    refine ⟨zero_le_one, le_rfl, fun r => ⟨fun hr => ?_, fun hr hY => ?_⟩⟩
    · by_cases hr0 : (r : ℝ) < 0
      · exact (h r).1 hr0
      · exact ((h r).2.1 (not_lt.mp hr0) hr).mpr hψ
    · exact (h r).2.2 hr.le hY
  · simp only [hψ, if_false]
    refine ⟨le_rfl, zero_le_one, fun r => ⟨fun hr => (h r).1 hr, fun hr hY => ?_⟩⟩
    by_cases hr1 : (r : ℝ) < 1
    · exact hψ (((h r).2.1 hr.le hr1).mp hY)
    · exact (h r).2.2 (not_lt.mp hr1) hY

/-- The concrete gated threshold family. -/
def gate (φ : Sentence) (X : LUV) : LUV where
  gt r := if r < 0 then top else LO.Propositional.Formula.and φ (X.gt r)

/-- The concrete indicator threshold family. -/
def indicator (ψ : Sentence) : LUV where
  gt r := if r < 0 then top else if r < 1 then ψ else bot

/-- The constant threshold family, valued `q` in every world. -/
def constLUV (q : ℚ) : LUV where
  gt r := if r < q then top else bot

theorem gate_gatedAt (v : PCWorld) (φ : Sentence) (X : LUV) : GatedAt v (gate φ X) φ X := by
  intro r
  constructor
  · intro hr
    have : r < 0 := by exact_mod_cast hr
    simp only [gate, if_pos this]
    exact holds_top v
  · intro hr
    have : ¬ r < 0 := by
      intro hc
      exact absurd (show (r : ℝ) < 0 by exact_mod_cast hc) (not_lt.mpr hr)
    simp only [gate, if_neg this]
    exact holds_and_iff v φ (X.gt r)

theorem indicator_indicatorAt (v : PCWorld) (ψ : Sentence) : IndicatorAt v (indicator ψ) ψ := by
  intro r
  refine ⟨fun hr => ?_, fun hr0 hr1 => ?_, fun hr => ?_⟩
  · have : r < 0 := by exact_mod_cast hr
    simp only [indicator, if_pos this]
    exact holds_top v
  · have h0 : ¬ r < 0 := by
      intro hc
      exact absurd (show (r : ℝ) < 0 by exact_mod_cast hc) (not_lt.mpr hr0)
    have h1 : r < 1 := by exact_mod_cast hr1
    simp only [indicator, if_neg h0, if_pos h1]
  · have h1 : ¬ r < 1 := by
      intro hc
      exact absurd (show (r : ℝ) < 1 by exact_mod_cast hc) (not_lt.mpr hr)
    have h0 : ¬ r < 0 := fun hc => h1 (hc.trans (by norm_num))
    simp only [indicator, if_neg h0, if_neg h1]
    exact not_holds_bot v

theorem constLUV_valuesAt (v : PCWorld) (q : ℚ) (hq : 0 ≤ q ∧ q ≤ 1) :
    v.ValuesAt (constLUV q) q := by
  refine ⟨by exact_mod_cast hq.1, by exact_mod_cast hq.2, fun r => ⟨fun hr => ?_, fun hr hc => ?_⟩⟩
  · have : r < q := by exact_mod_cast hr
    simp only [constLUV, if_pos this]
    exact holds_top v
  · have : ¬ r < q := by
      intro h
      exact absurd (show (r : ℝ) < q by exact_mod_cast h) (not_lt.mpr hr.le)
    simp only [constLUV, if_neg this] at hc
    exact not_holds_bot v hc

end Gated

/-! ## 3. The compiled constraint and its validity -/

section Compiled

/-- One mediated pair, compiled: the two activated securities, the activation-gated
discrepancy and regret, the directional mismatch indicator, the two activation
sentences, and the normalised stability coefficient `λ = L · δ_max / D`.  Every LUV is
`[0,1]`-valued. -/
structure MediatedPair where
  Uraw : LUV
  Ucorr : LUV
  Gδ : LUV
  Gρ : LUV
  GM : LUV
  φraw : Sentence
  φcorr : Sentence
  lam : ℚ

/-- **The effective constructor.**  The bypass constraint
`U_raw − U_corr − λ·G_δ − G_ρ − G_M`, with constant coefficients. -/
def MediatedPair.B (p : MediatedPair) : LUVCombination where
  const := EF.const 0
  terms := [(EF.const 1, p.Uraw), (EF.const (-1), p.Ucorr), (EF.const (-p.lam), p.Gδ),
    (EF.const (-1), p.Gρ), (EF.const (-1), p.GM)]

/-- The world-side validity package: the five values the world assigns, the
reproduction certificate and the decline regret on the common-activation branch. -/
structure ValidAt (p : MediatedPair) (v : PCWorld) where
  wr : ℝ
  wapp : ℝ
  wa : ℝ
  δ : ℝ
  ρ : ℝ
  wr_mem : 0 ≤ wr ∧ wr ≤ 1
  wa_mem : 0 ≤ wa ∧ wa ≤ 1
  δ_mem : 0 ≤ δ ∧ δ ≤ 1
  ρ_mem : 0 ≤ ρ ∧ ρ ≤ 1
  raw_val : v.ValuesAt p.Uraw (if v.Holds p.φraw then wr else 0)
  corr_val : v.ValuesAt p.Ucorr (if v.Holds p.φcorr then wa else 0)
  δ_val : v.ValuesAt p.Gδ (if v.Holds p.φraw ∧ v.Holds p.φcorr then δ else 0)
  ρ_val : v.ValuesAt p.Gρ (if v.Holds p.φraw ∧ v.Holds p.φcorr then ρ else 0)
  M_val : v.ValuesAt p.GM (if v.Holds p.φraw ∧ ¬ v.Holds p.φcorr then 1 else 0)
  lip : v.Holds p.φraw → v.Holds p.φcorr → |wr - wapp| ≤ (p.lam : ℝ) * δ
  regret : v.Holds p.φraw → v.Holds p.φcorr → wapp - wa ≤ ρ

/-- A world's canonical valuation of LUVs: the value it assigns where it assigns one. -/
noncomputable def canonicalValue (v : PCWorld) (X : LUV) : ℝ :=
  if h : ∃ x, v.ValuesAt X x then Classical.choose h else 0

theorem canonicalValue_of_valuesAt {v : PCWorld} {X : LUV} {x : ℝ} (hx : v.ValuesAt X x) :
    canonicalValue v X = x := by
  have h : ∃ y, v.ValuesAt X y := ⟨x, hx⟩
  simp only [canonicalValue, dif_pos h]
  exact PCWorld.ValuesAt.eq (Classical.choose_spec h) hx

/-- The compiled constraint's value under any coherent valuation is the linear form. -/
theorem MediatedPair.value_eq (p : MediatedPair) (P : History) (ν : LUV → ℝ) :
    (p.B).value P ν = ν p.Uraw - ν p.Ucorr - (p.lam : ℝ) * ν p.Gδ - ν p.Gρ - ν p.GM := by
  simp only [LUVCombination.value, MediatedPair.B, EF.denote, EF.denoteWith_const,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

/-- Every coherent valuation of the terms assigns the values of the package. -/
theorem ValidAt.values_eq {p : MediatedPair} {v : PCWorld} (h : ValidAt p v)
    (ν : LUV → ℝ) (hν : (p.B).ValuesAt v ν) :
    ν p.Uraw = (if v.Holds p.φraw then h.wr else 0) ∧
    ν p.Ucorr = (if v.Holds p.φcorr then h.wa else 0) ∧
    ν p.Gδ = (if v.Holds p.φraw ∧ v.Holds p.φcorr then h.δ else 0) ∧
    ν p.Gρ = (if v.Holds p.φraw ∧ v.Holds p.φcorr then h.ρ else 0) ∧
    ν p.GM = (if v.Holds p.φraw ∧ ¬ v.Holds p.φcorr then 1 else 0) := by
  have hmem : ∀ q ∈ (p.B).terms, v.ValuesAt q.2 (ν q.2) := hν
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact PCWorld.ValuesAt.eq (hmem (EF.const 1, p.Uraw) (by simp [MediatedPair.B])) h.raw_val
  · exact PCWorld.ValuesAt.eq (hmem (EF.const (-1), p.Ucorr) (by simp [MediatedPair.B])) h.corr_val
  · exact PCWorld.ValuesAt.eq (hmem (EF.const (-p.lam), p.Gδ) (by simp [MediatedPair.B])) h.δ_val
  · exact PCWorld.ValuesAt.eq (hmem (EF.const (-1), p.Gρ) (by simp [MediatedPair.B])) h.ρ_val
  · exact PCWorld.ValuesAt.eq (hmem (EF.const (-1), p.GM) (by simp [MediatedPair.B])) h.M_val

/-- **Semantic validity.**  `ValidMediatedPair → ∀ W, W(B) ≤ 0`: in a world satisfying the
package, every coherent valuation of the constraint's terms gives it a nonpositive
value. -/
theorem ValidAt.value_le_of_valuesAt {p : MediatedPair} {v : PCWorld} (h : ValidAt p v)
    (P : History) (ν : LUV → ℝ) (hν : (p.B).ValuesAt v ν) : (p.B).value P ν ≤ 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h.values_eq ν hν
  rw [MediatedPair.value_eq, h1, h2, h3, h4, h5]
  by_cases hr : v.Holds p.φraw <;> by_cases hc : v.Holds p.φcorr <;> simp [hr, hc]
  · have hl := le_trans (le_abs_self _) (h.lip hr hc)
    have hg := h.regret hr hc
    linarith
  · exact h.wr_mem.2
  · exact h.wa_mem.1

/-- The canonical valuation is coherent on the constraint's terms. -/
theorem ValidAt.canonical_valuesAt {p : MediatedPair} {v : PCWorld} (h : ValidAt p v) :
    (p.B).ValuesAt v (canonicalValue v) := by
  intro q hq
  simp only [MediatedPair.B, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · rw [canonicalValue_of_valuesAt h.raw_val]; exact h.raw_val
  · rw [canonicalValue_of_valuesAt h.corr_val]; exact h.corr_val
  · rw [canonicalValue_of_valuesAt h.δ_val]; exact h.δ_val
  · rw [canonicalValue_of_valuesAt h.ρ_val]; exact h.ρ_val
  · rw [canonicalValue_of_valuesAt h.M_val]; exact h.M_val

/-- The package built from the compiler lemmas: gated and indicator presentations plus the
base values.  This is the constructor a realization uses. -/
def ValidAt.ofGated {p : MediatedPair} {v : PCWorld} {Xr Xa Xδ Xρ : LUV}
    (wr wapp wa δ ρ : ℝ)
    (hwr : 0 ≤ wr ∧ wr ≤ 1) (hwa : 0 ≤ wa ∧ wa ≤ 1) (hδ : 0 ≤ δ ∧ δ ≤ 1) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (gr : GatedAt v p.Uraw p.φraw Xr) (hxr : v.ValuesAt Xr wr)
    (ga : GatedAt v p.Ucorr p.φcorr Xa) (hxa : v.ValuesAt Xa wa)
    (gδ : GatedAt v p.Gδ (LO.Propositional.Formula.and p.φraw p.φcorr) Xδ) (hxδ : v.ValuesAt Xδ δ)
    (gρ : GatedAt v p.Gρ (LO.Propositional.Formula.and p.φraw p.φcorr) Xρ) (hxρ : v.ValuesAt Xρ ρ)
    (iM : IndicatorAt v p.GM (LO.Propositional.Formula.and p.φraw (neg p.φcorr)))
    (lip : v.Holds p.φraw → v.Holds p.φcorr → |wr - wapp| ≤ (p.lam : ℝ) * δ)
    (regret : v.Holds p.φraw → v.Holds p.φcorr → wapp - wa ≤ ρ) : ValidAt p v where
  wr := wr
  wapp := wapp
  wa := wa
  δ := δ
  ρ := ρ
  wr_mem := hwr
  wa_mem := hwa
  δ_mem := hδ
  ρ_mem := hρ
  raw_val := gr.valuesAt hxr
  corr_val := ga.valuesAt hxa
  δ_val := by simpa [holds_and_iff] using gδ.valuesAt hxδ
  ρ_val := by simpa [holds_and_iff] using gρ.valuesAt hxρ
  M_val := by simpa [holds_and_iff, holds_neg_iff] using iM.valuesAt
  lip := lip
  regret := regret

end Compiled

/-! ## 4. Expectation Provability Induction, instantiated -/

section EPI

/-- The day-`n` expectation of the compiled constraint is the linear form in the day-`n`
expectations of its terms. -/
theorem MediatedPair.expect_eq (p : MediatedPair) (P : History) (n : ℕ) :
    (p.B).expect P n
      = p.Uraw.expect P n - p.Ucorr.expect P n - (p.lam : ℝ) * p.Gδ.expect P n
        - p.Gρ.expect P n - p.GM.expect P n := by
  simp only [LUVCombination.expect, LUVCombination.expectAt, MediatedPair.B, EF.denote,
    EF.denoteWith_const, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, LUV.expect]
  push_cast
  ring

/-- Validity in every completed-theory world supplies the pinned `WorldValued` premise. -/
theorem worldValued_of_valid {DP : DeductiveProcess} (p : ℕ → MediatedPair)
    (hvalid : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ValidAt (p n) v) :
    LUVCombination.WorldValued (fun n => (p n).B) DP :=
  fun n v hv => ⟨canonicalValue v, (hvalid n v hv).canonical_valuesAt⟩

/-- Every completed value of the compiled constraint is nonpositive. -/
theorem completedHigh_le_zero {P : History} {DP : DeductiveProcess} (p : ℕ → MediatedPair)
    (hvalid : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ValidAt (p n) v) (n : ℕ) :
    LUVCombination.completedHigh (fun n => (p n).B) P DP n ≤ 0 := by
  apply Real.sSup_le _ le_rfl
  rintro x ⟨v, ν, hv, hν, rfl⟩
  exact (hvalid n v hv).value_le_of_valuesAt P ν hν

/-- Every completed value is bounded below by the negated coefficient sum, uniformly in
`n` under the share-norm bound. -/
theorem completedHigh_ge {P : History} {DP : DeductiveProcess} (p : ℕ → MediatedPair)
    (hvalid : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ValidAt (p n) v)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℚ) (hshare : ∀ n, ((p n).B).shareNorm P ≤ (b : ℝ)) (n : ℕ) :
    -(3 + (b : ℝ)) ≤ LUVCombination.completedHigh (fun n => (p n).B) P DP n := by
  obtain ⟨v, hv⟩ := exists_consistentWithTheory DP hworld
  have h := hvalid n v hv
  have hlam : |((p n).lam : ℝ)| ≤ b := by
    have hs := hshare n
    simp only [LUVCombination.shareNorm, MediatedPair.B, EF.denote, EF.denoteWith_const,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hs
    push_cast at hs
    simp only [abs_one, abs_neg] at hs
    linarith [abs_nonneg ((p n).lam : ℝ)]
  have hmem : ((p n).B).value P (canonicalValue v)
      ∈ LUVCombination.completedValues DP ((p n).B) P :=
    ⟨v, canonicalValue v, hv, h.canonical_valuesAt, rfl⟩
  have hbdd : BddAbove (LUVCombination.completedValues DP ((p n).B) P) := by
    refine ⟨0, ?_⟩
    rintro x ⟨w, ν, hw, hν, rfl⟩
    exact (hvalid n w hw).value_le_of_valuesAt P ν hν
  refine le_trans ?_ (le_csSup hbdd hmem)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h.values_eq (canonicalValue v) h.canonical_valuesAt
  rw [MediatedPair.value_eq, h1, h2, h3, h4, h5]
  have hlδ : ((p n).lam : ℝ) * h.δ ≤ b := by
    calc ((p n).lam : ℝ) * h.δ ≤ |((p n).lam : ℝ)| * h.δ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h.δ_mem.1
      _ ≤ |((p n).lam : ℝ)| * 1 := mul_le_mul_of_nonneg_left h.δ_mem.2 (abs_nonneg _)
      _ ≤ b := by linarith
  have hb0 : (0 : ℝ) ≤ b := (abs_nonneg _).trans hlam
  by_cases hr : v.Holds (p n).φraw <;> by_cases hc : v.Holds (p n).φcorr <;> simp [hr, hc] <;>
    linarith [h.wr_mem.1, h.wa_mem.2, h.ρ_mem.2, hlδ, hb0]

/-- **The Logical-Induction corollary.**  With the pinned `thm:expcoh` and its operational
premises as named hypotheses, validity in every completed-theory world gives
`𝔼ₙ(B_n) ≲ₙ 0`. -/
theorem li_constraint_le {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (p : ℕ → MediatedPair)
    (hvalid : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ValidAt (p n) v)
    (h : LUVCombination.BoundedSequence (fun n => (p n).B) P)
    (ops : LUVCombination.MeshSoftmaxOperationalWitness (fun n => (p n).B) P)
    (hcode : ∀ n q, q ∈ ((p n).B).terms → q.2.RpnThresholdCodes)
    (b : ℚ) (hb : 0 ≤ (b : ℝ)) (hshare : ∀ n, ((p n).B).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => ((p n).B).expect P n) ≲ₙ fun _ => 0 := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  have hcoh := LUVCombination.BoundedSequence.expcoh h ops (worldValued_of_valid p hvalid)
    hcode b hb hshare hworld
  have hhigh : limsup (LUVCombination.completedHigh (fun n => (p n).B) P DP) atTop ≤ 0 := by
    apply limsup_le_of_le
    · exact (isBoundedUnder_of ⟨-(3 + (b : ℝ)),
        fun n => completedHigh_ge p hvalid hworld b hshare n⟩).isCoboundedUnder_flip
    · exact Eventually.of_forall (completedHigh_le_zero p hvalid)
  have hlim : limsup (fun n => ((p n).B).expect P n) atTop ≤ 0 :=
    (hcoh.2.1.trans hcoh.2.2).trans hhigh
  obtain ⟨B, hB⟩ := h.bounded
  have hup : IsBoundedUnder (· ≤ ·) atTop (fun n => ((p n).B).expect P n) := by
    refine isBoundedUnder_of ⟨B, fun n => ?_⟩
    have := ((p n).B).abs_expectAt_le_l1Norm P (n + 1) n (hP n)
    have := abs_le.mp this
    show ((p n).B).expectAt P (n + 1) n ≤ B
    linarith [hB n]
  intro ε hε
  filter_upwards [eventually_lt_of_limsup_lt (show limsup (fun n => ((p n).B).expect P n)
    atTop < ε by linarith) hup] with n hn
  linarith

/-- **Logical Induction learns the corrigibility inequality.**  Under the hypotheses of
`li_constraint_le`,
`𝔼ₙ(U_raw,n) − 𝔼ₙ(U_corr,n) ≲ₙ λₙ·𝔼ₙ(G_δ,n) + 𝔼ₙ(G_ρ,n) + 𝔼ₙ(G_M,n)`. -/
theorem li_bypass_le {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (p : ℕ → MediatedPair)
    (hvalid : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ValidAt (p n) v)
    (h : LUVCombination.BoundedSequence (fun n => (p n).B) P)
    (ops : LUVCombination.MeshSoftmaxOperationalWitness (fun n => (p n).B) P)
    (hcode : ∀ n q, q ∈ ((p n).B).terms → q.2.RpnThresholdCodes)
    (b : ℚ) (hb : 0 ≤ (b : ℝ)) (hshare : ∀ n, ((p n).B).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (p n).Uraw.expect P n - (p n).Ucorr.expect P n) ≲ₙ
      fun n => ((p n).lam : ℝ) * (p n).Gδ.expect P n + (p n).Gρ.expect P n
        + (p n).GM.expect P n := by
  have hc := li_constraint_le p hvalid h ops hcode b hb hshare hworld
  intro ε hε
  filter_upwards [hc ε hε] with n hn
  rw [MediatedPair.expect_eq] at hn
  linarith

end EPI

/-! ## 5. Finite-menu uniformisation -/

section Menu

variable {ι : Type*}

/-- A weighted aggregate whose weights are supported on near-maximal scores is at least
the maximum less the window. -/
theorem nearMax_weighted_ge (s : Finset ι) (w sc : ι → ℝ) (m δ : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hsupp : ∀ i ∈ s, 0 < w i → m - 2 * δ ≤ sc i) :
    m - 2 * δ ≤ ∑ i ∈ s, w i * sc i := by
  have h : ∑ i ∈ s, w i * (m - 2 * δ) ≤ ∑ i ∈ s, w i * sc i := by
    refine Finset.sum_le_sum fun i hi => ?_
    rcases (hw i hi).lt_or_eq with hpos | hzero
    · exact mul_le_mul_of_nonneg_left (hsupp i hi hpos) (hw i hi)
    · rw [← hzero]; simp
  calc m - 2 * δ = ∑ i ∈ s, w i * (m - 2 * δ) := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ i ∈ s, w i * sc i := h

/-- The continuous threshold ramp `min 1 (max 0 ((x − y)/δ))`, an expressible feature of
`x` and `y` for rational `δ`. -/
noncomputable def ramp (δ x y : ℝ) : ℝ := min 1 (max 0 ((x - y) / δ))

theorem ramp_nonneg (δ x y : ℝ) : 0 ≤ ramp δ x y := by
  unfold ramp; exact le_min zero_le_one (le_max_left _ _)

theorem ramp_le_one (δ x y : ℝ) : ramp δ x y ≤ 1 := by
  unfold ramp; exact min_le_left _ _

theorem ramp_eq_one (δ x y : ℝ) (hδ : 0 < δ) (h : y + δ ≤ x) : ramp δ x y = 1 := by
  unfold ramp
  have : 1 ≤ (x - y) / δ := by rw [le_div_iff₀ hδ]; linarith
  rw [max_eq_right (zero_le_one.trans this), min_eq_left this]

theorem lt_of_ramp_pos (δ x y : ℝ) (hδ : 0 < δ) (h : 0 < ramp δ x y) : y < x := by
  unfold ramp at h
  by_contra hxy
  have : (x - y) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  rw [max_eq_left this, min_eq_right zero_le_one] at h
  exact lt_irrefl _ h

/-- The near-argmax weight: ramp of the score above `m − 2δ`, normalised. -/
noncomputable def softWeight (s : Finset ι) (δ : ℝ) (sc : ι → ℝ) (m : ℝ) (i : ι) : ℝ :=
  ramp δ (sc i) (m - 2 * δ) / ∑ j ∈ s, ramp δ (sc j) (m - 2 * δ)

/-- **The soft selector.**  With `m` the menu's maximal score and `δ > 0`, the
near-argmax weights are nonnegative, sum to one, and their aggregate is at least
`m − 2δ`. -/
theorem softWeight_aggregate_ge (s : Finset ι) (hs : s.Nonempty) (δ : ℝ) (hδ : 0 < δ)
    (sc : ι → ℝ) :
    (∀ i ∈ s, 0 ≤ softWeight s δ sc (s.sup' hs sc) i) ∧
    (∑ i ∈ s, softWeight s δ sc (s.sup' hs sc) i = 1) ∧
    s.sup' hs sc - 2 * δ ≤ ∑ i ∈ s, softWeight s δ sc (s.sup' hs sc) i * sc i := by
  set m := s.sup' hs sc with hm
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_mem_eq_sup' hs sc
  have hone : ramp δ (sc i₀) (m - 2 * δ) = 1 :=
    ramp_eq_one δ _ _ hδ (by rw [hm, hmax]; linarith)
  have hZ : 1 ≤ ∑ j ∈ s, ramp δ (sc j) (m - 2 * δ) := by
    calc (1 : ℝ) = ramp δ (sc i₀) (m - 2 * δ) := hone.symm
      _ ≤ ∑ j ∈ s, ramp δ (sc j) (m - 2 * δ) :=
        Finset.single_le_sum (fun j _ => ramp_nonneg δ (sc j) _) hi₀
  have hZpos : 0 < ∑ j ∈ s, ramp δ (sc j) (m - 2 * δ) := by linarith
  have hnn : ∀ i ∈ s, 0 ≤ softWeight s δ sc m i := fun i _ =>
    div_nonneg (ramp_nonneg _ _ _) hZpos.le
  have hsum : ∑ i ∈ s, softWeight s δ sc m i = 1 := by
    unfold softWeight
    rw [← Finset.sum_div, div_self hZpos.ne']
  refine ⟨hnn, hsum, nearMax_weighted_ge s _ sc m δ hnn hsum fun i _ hpos => ?_⟩
  have hr : 0 < ramp δ (sc i) (m - 2 * δ) := by
    unfold softWeight at hpos
    exact (div_pos_iff_of_pos_right hZpos).mp hpos
  exact (lt_of_ramp_pos δ _ _ hδ hr).le

/-- **Uniformisation.**  If the soft aggregate is asymptotically nonpositive and the
window vanishes, the menu maximum is asymptotically nonpositive. -/
theorem uniform_of_soft (m δ agg : ℕ → ℝ) (hagg : agg ≲ₙ fun _ => 0)
    (hδ : Tendsto δ atTop (𝓝 0)) (hlow : ∀ n, m n - 2 * δ n ≤ agg n) :
    m ≲ₙ fun _ => 0 := by
  intro ε hε
  have hε2 : 0 < ε / 4 := by positivity
  filter_upwards [hagg (ε / 2) (by positivity),
    (Metric.tendsto_atTop.1 hδ (ε / 4) hε2).choose_spec |> fun h =>
      eventually_atTop.2 ⟨_, h⟩] with n h1 h2
  have h3 : |δ n - 0| < ε / 4 := by simpa [Real.dist_eq] using h2
  have := (abs_lt.1 h3).2
  linarith [hlow n]

/-- **Bounded menus need no selector.**  Finitely many asymptotically nonpositive
sequences have an asymptotically nonpositive maximum. -/
theorem max_asympLE [Fintype ι] [Nonempty ι] (f : ι → ℕ → ℝ)
    (hf : ∀ i, f i ≲ₙ fun _ => 0) :
    (fun n => Finset.univ.sup' Finset.univ_nonempty (fun i => f i n)) ≲ₙ fun _ => 0 := by
  intro ε hε
  have hall : ∀ᶠ n in atTop, ∀ i, f i n ≤ 0 + ε := eventually_all.2 fun i => hf i ε hε
  filter_upwards [hall] with n hn
  exact Finset.sup'_le _ _ fun i _ => hn i

end Menu

/-! ## 6. Witnesses -/

namespace Witness

open LO.Propositional (Formula)

/-- Raw activation is atom `0`, corrigibilized activation atom `1`; the raw value is `1`,
the approve branch reproduces it exactly, the actual branch is worth `1/2`; `δ = 0`,
`ρ = 1/2`; `λ = 1`. -/
def pair : MediatedPair where
  Uraw := gate (Formula.atom 0) (constLUV 1)
  Ucorr := gate (Formula.atom 1) (constLUV (1/2))
  Gδ := gate (Formula.and (Formula.atom 0) (Formula.atom 1)) (constLUV 0)
  Gρ := gate (Formula.and (Formula.atom 0) (Formula.atom 1)) (constLUV (1/2))
  GM := indicator (Formula.and (Formula.atom 0) (neg (Formula.atom 1)))
  φraw := Formula.atom 0
  φcorr := Formula.atom 1
  lam := 1

/-- The package holds in every world. -/
noncomputable def valid (v : PCWorld) : ValidAt pair v :=
  ValidAt.ofGated (Xr := constLUV 1) (Xa := constLUV (1/2)) (Xδ := constLUV 0)
    (Xρ := constLUV (1/2)) 1 1 (1/2) 0 (1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (gate_gatedAt v _ _) (by simpa using constLUV_valuesAt v 1 (by norm_num))
    (gate_gatedAt v _ _) (by simpa using constLUV_valuesAt v (1/2) (by norm_num))
    (gate_gatedAt v _ _) (by simpa using constLUV_valuesAt v 0 (by norm_num))
    (gate_gatedAt v _ _) (by simpa using constLUV_valuesAt v (1/2) (by norm_num))
    (indicator_indicatorAt v _)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)

/-- The raw-only world: atom `0` true, atom `1` false. -/
def rawOnly : PCWorld := fun i => i = 0

/-- The common-activation world: both atoms true. -/
def both : PCWorld := fun _ => True

/-- **The mismatch term is attained**: on the raw-only world the constraint's value is
exactly `0`, with `U_raw = 1`, `U_corr = 0`, `G_M = 1`. -/
theorem attained_mismatch (P : History) :
    (pair.B).value P (canonicalValue rawOnly) = 0 ∧
    canonicalValue rawOnly pair.Uraw = 1 ∧ canonicalValue rawOnly pair.Ucorr = 0 ∧
    canonicalValue rawOnly pair.GM = 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    (valid rawOnly).values_eq (canonicalValue rawOnly) (valid rawOnly).canonical_valuesAt
  have hr : rawOnly.Holds (Formula.atom 0) := by
    show (0 : ℕ) = 0
    rfl
  have hc : ¬ rawOnly.Holds (Formula.atom 1) := by
    show ¬ ((1 : ℕ) = 0)
    decide
  simp only [pair] at h1 h2 h3 h4 h5 hr hc ⊢
  rw [MediatedPair.value_eq, h1, h2, h3, h4, h5]
  simp [hr, hc, valid, ValidAt.ofGated]

/-- **The common branch is attained**: on the common-activation world the value is again
exactly `0`, with `U_raw = 1`, `U_corr = 1/2`, `G_ρ = 1/2`, `G_M = 0`. -/
theorem attained_common (P : History) :
    (pair.B).value P (canonicalValue both) = 0 ∧
    canonicalValue both pair.Uraw = 1 ∧ canonicalValue both pair.Ucorr = 1/2 ∧
    canonicalValue both pair.GM = 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    (valid both).values_eq (canonicalValue both) (valid both).canonical_valuesAt
  have hr : both.Holds (Formula.atom 0) := trivial
  have hc : both.Holds (Formula.atom 1) := trivial
  simp only [pair] at h1 h2 h3 h4 h5 hr hc ⊢
  rw [MediatedPair.value_eq, h1, h2, h3, h4, h5]
  simp [hr, hc, valid, ValidAt.ofGated]
  norm_num

/-- **`D` is sharp.**  One world, raw activated, corrigibilized not, `w_raw = D`; the
premium is exactly `D · M` with `δ = ρ = 0`. -/
theorem attained (D : ℝ) :
    indR true * D - indR false * D = D * (indR true * (1 - indR false)) := by
  simp [indR]

/-- **The marginal-rate bound is refuted.**  Two equiprobable worlds with opposite
activation patterns: the marginal difference `E[c_raw] − E[c_corr]` is `0`, the joint
mismatch mass `E[c_raw (1 − c_corr)]` is `1/2`, and the premium is `D/2`. -/
theorem marginal_refuted (D : ℝ) :
    let μ : Fin 2 → ℝ := fun _ => 1/2
    let cr : Fin 2 → Bool := ![true, false]
    let cc : Fin 2 → Bool := ![false, true]
    let Vr : Fin 2 → ℝ := fun _ => D
    let Vl : Fin 2 → ℝ := fun _ => 0
    expectR μ (fun x => indR (cr x) * Vr x) - expectR μ (fun x => indR (cc x) * Vl x) = D / 2
      ∧ expectR μ (fun x => indR (cr x)) - expectR μ (fun x => indR (cc x)) = 0
      ∧ expectR μ (fun x => indR (cr x) * (1 - indR (cc x))) = 1/2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [expectR, indR, Fin.sum_univ_two]; ring
  · simp [expectR, indR, Fin.sum_univ_two]
  · simp [expectR, indR, Fin.sum_univ_two]

/-- **Reverse mismatch is free.**  Where only the corrigibilized option activates the
difference is `−w_act ≤ 0` and the mismatch term is `0`. -/
theorem reverse_free (wa : ℝ) (hwa : 0 ≤ wa) :
    indR false * 0 - indR true * wa ≤ 0 ∧ indR false * (1 - indR true) = 0 := by
  simp [indR]; exact hwa

end Witness

end Workspace.Deference.Contrib.LICorrigibility

#print axioms Workspace.Deference.Contrib.LICorrigibility.mismatch_identity
#print axioms Workspace.Deference.Contrib.LICorrigibility.mismatch_bound_exact
#print axioms Workspace.Deference.Contrib.LICorrigibility.mismatch_bound
#print axioms Workspace.Deference.Contrib.LICorrigibility.mismatch_common
#print axioms Workspace.Deference.Contrib.LICorrigibility.security_bypass_le_mismatch
#print axioms Workspace.Deference.Contrib.LICorrigibility.GatedAt.valuesAt
#print axioms Workspace.Deference.Contrib.LICorrigibility.IndicatorAt.valuesAt
#print axioms Workspace.Deference.Contrib.LICorrigibility.gate_gatedAt
#print axioms Workspace.Deference.Contrib.LICorrigibility.indicator_indicatorAt
#print axioms Workspace.Deference.Contrib.LICorrigibility.constLUV_valuesAt
#print axioms Workspace.Deference.Contrib.LICorrigibility.ValidAt.value_le_of_valuesAt
#print axioms Workspace.Deference.Contrib.LICorrigibility.ValidAt.ofGated
#print axioms Workspace.Deference.Contrib.LICorrigibility.worldValued_of_valid
#print axioms Workspace.Deference.Contrib.LICorrigibility.li_constraint_le
#print axioms Workspace.Deference.Contrib.LICorrigibility.li_bypass_le
#print axioms Workspace.Deference.Contrib.LICorrigibility.nearMax_weighted_ge
#print axioms Workspace.Deference.Contrib.LICorrigibility.softWeight_aggregate_ge
#print axioms Workspace.Deference.Contrib.LICorrigibility.uniform_of_soft
#print axioms Workspace.Deference.Contrib.LICorrigibility.max_asympLE
#print axioms Workspace.Deference.Contrib.LICorrigibility.Witness.valid
#print axioms Workspace.Deference.Contrib.LICorrigibility.Witness.attained_mismatch
#print axioms Workspace.Deference.Contrib.LICorrigibility.Witness.attained_common
#print axioms Workspace.Deference.Contrib.LICorrigibility.Witness.attained
#print axioms Workspace.Deference.Contrib.LICorrigibility.Witness.marginal_refuted
#print axioms Workspace.Deference.Contrib.LICorrigibility.Witness.reverse_free
