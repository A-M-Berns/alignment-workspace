/-
# The third non-capture link: the reference comparator and the content defect

Round `projects/deference/rounds/2026-09-24-transparent-channel/`, second pass.

**1. The reason-channel defect in content units** (`tauR`): the sensitivity mass of the
symmetric difference between the actual content and the reference content.
`abs_sub_le_tauR` is `sensitive_symmDiff` read as a defect bound: an extensional
program's verdict on the actual trace is within `τ_R` of its verdict on the reference
trace; `omission_le_adverse` is the one-sided form when the actual content is the
reference minus omissions (`adverse_union`); `tauR_eq_zero_of_eq` is the exact case;
`tauR_le_disagree` ties the content defect to the pathwise Boolean defect of
`TransparentChannel`: it is at most the total sensitivity mass times the disagreement
indicator.

**2. The three-link chain** (`li_noncapture_chain3`): `li_noncapture` on the pairs
(actual, reference), (reference, discovered), (discovered, full), the middle families
shared, so the expectations telescope and Logical Induction learns

    𝔼ₙ(U_actual) − 𝔼ₙ(U_full)  ≲ₙ  L·(τ_R + α + β),

with `τ_R` certified by the first pair's content bound, `α` by the supply theorem and `β`
by the discovery theorem.  The first link charges departure from the declared reference
process; the second and third charge the reference's own service and discovery limits.
Nothing of Logical Induction is re-proved; the proof is `li_noncapture` and
`li_noncapture_chain` added.

**What this does not establish.**  That any realization certifies `τ_R` (that is the
committed-advisor hypothesis of `TransparentEcosystem.realizes_reason`, under which it is
`0`); the Logical-Induction transfer of the *activation* defect indicators, which would
need a compiled constraint `G_M ≤ G_τ` with its own generability certificate (the
world-wise inequality is `TransparentChannel.mismatch_le_disagree`).  Names are
provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.ReasonDiscovery
import Workspace.Deference.Contrib.TransparentChannel

namespace Workspace.Deference.Contrib.TransparentChain

open LogicalInduction
open Workspace.Deference.Contrib.LICorrigibility
open Workspace.Deference.Contrib.TraceSteering
open Workspace.Deference.Contrib.ReasonSupply
open Workspace.Deference.Contrib.ReasonDiscovery
open scoped Classical
open Finset

/-! ## 1. The content defect -/

section Defect

variable {ι : Type*} [DecidableEq ι]

/-- **The reason-channel defect in content units**: the sensitivity mass of the symmetric
difference between the actual and the reference content. -/
def tauR (L : ι → ℝ) (c c' : Finset ι) : ℝ := ∑ r ∈ (c \ c' ∪ c' \ c), L r

theorem tauR_eq_zero_of_eq (L : ι → ℝ) (c : Finset ι) : tauR L c c = 0 := by
  simp [tauR]

theorem tauR_comm (L : ι → ℝ) (c c' : Finset ι) : tauR L c c' = tauR L c' c := by
  unfold tauR; rw [Finset.union_comm]

/-- **An extensional program's verdict moves by at most the defect**
(`sensitive_symmDiff`). -/
theorem abs_sub_le_tauR {F : Finset ι → ℝ} {L : ι → ℝ} (h : Sensitive F L) (c c' : Finset ι) :
    |F c - F c'| ≤ tauR L c c' :=
  sensitive_symmDiff h c c'

/-- **The one-sided form**: when the actual content is the reference minus omissions, the
advisor's gain is at most the adverse mass of what it omitted (`adverse_union`). -/
theorem omission_le_adverse {F : Finset ι → ℝ} {A : ι → ℝ} (h : Adverse F A)
    (actual ref : Finset ι) (hsub : actual ⊆ ref) :
    F actual - F ref ≤ ∑ r ∈ ref \ actual, A r := by
  have := adverse_union h actual (ref \ actual) Finset.sdiff_disjoint
  rwa [Finset.union_sdiff_of_subset hsub] at this

/-- **The content defect is bounded by the pathwise defect**: at most the total
sensitivity mass of the two contents times the disagreement indicator. -/
theorem tauR_le_disagree (L : ι → ℝ) (hL : ∀ r, 0 ≤ L r) (c c' : Finset ι) :
    tauR L c c' ≤ (∑ r ∈ c ∪ c', L r) * (if c = c' then 0 else 1) := by
  by_cases h : c = c'
  · subst h; simp [tauR]
  · simp only [h, if_false, mul_one]
    unfold tauR
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun r _ _ => hL r
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hr).1
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hr).1

end Defect

/-! ## 2. The three-link chain -/

section Chain

/-- **The three-link non-capture chain.**  `li_noncapture` on (actual, reference),
(reference, discovered) and (discovered, full), the middle families shared:
`𝔼ₙ(U_actual) − 𝔼ₙ(U_full) ≲ₙ L·(τ_R + (α + β))`, with `τ_R = a₁/b₁` the certified
content defect of the actual trace against the reference trace, `α = a₂/b₂` the
certified service loss of the reference supplier and `β = a₃/b₃` the certified discovery
residual of the reference inquiry. -/
theorem li_noncapture_chain3 {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (φa φr φd φf : ℕ → Sentence) (Xa Xr Xd Xf Xδ₁ Xκ₁ Xδ₂ Xκ₂ Xδ₃ Xκ₃ : ℕ → LUV) (L : ℚ)
    (hL : 0 ≤ L)
    (a₁ b₁ : ℕ) (hb₁ : 0 < b₁) (hab₁ : a₁ ≤ b₁)
    (a₂ b₂ : ℕ) (hb₂ : 0 < b₂) (hab₂ : a₂ ≤ b₂)
    (a₃ b₃ : ℕ) (hb₃ : 0 < b₃) (hab₃ : a₃ ≤ b₃)
    (hvalid₁ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ValidAt (MediatedPair.compile (φa n) (φr n) (Xa n) (Xr n) (Xδ₁ n) (Xκ₁ n) L) v)
    (hvalid₂ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ValidAt (MediatedPair.compile (φr n) (φd n) (Xr n) (Xd n) (Xδ₂ n) (Xκ₂ n) L) v)
    (hvalid₃ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ValidAt (MediatedPair.compile (φd n) (φf n) (Xd n) (Xf n) (Xδ₃ n) (Xκ₃ n) L) v)
    (hdefect : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ d : ℝ, v.ValuesAt (Xδ₁ n) d ∧ (v.Holds (φa n) → v.Holds (φr n) → d ≤ (a₁ : ℚ) / (b₁ : ℚ)))
    (hsupply : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ d : ℝ, v.ValuesAt (Xδ₂ n) d ∧ (v.Holds (φr n) → v.Holds (φd n) → d ≤ (a₂ : ℚ) / (b₂ : ℚ)))
    (hdiscover : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ d : ℝ, v.ValuesAt (Xδ₃ n) d ∧ (v.Holds (φd n) → v.Holds (φf n) → d ≤ (a₃ : ℚ) / (b₃ : ℚ)))
    (hext₁ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.ValuesAt (Xκ₁ n) 0)
    (hext₂ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.ValuesAt (Xκ₂ n) 0)
    (hext₃ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.ValuesAt (Xκ₃ n) 0)
    (hsealed₁ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.Holds (φa n) → v.Holds (φr n))
    (hsealed₂ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.Holds (φr n) → v.Holds (φd n))
    (hsealed₃ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.Holds (φd n) → v.Holds (φf n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hφa : RpnSentenceCodes φa) (hφr : RpnSentenceCodes φr) (hφd : RpnSentenceCodes φd)
    (hφf : RpnSentenceCodes φf)
    (hXa : LUV.RpnThresholdCodeSeq Xa) (hXr : LUV.RpnThresholdCodeSeq Xr)
    (hXd : LUV.RpnThresholdCodeSeq Xd) (hXf : LUV.RpnThresholdCodeSeq Xf)
    (hXδ₁ : LUV.RpnThresholdCodeSeq Xδ₁) (hXκ₁ : LUV.RpnThresholdCodeSeq Xκ₁)
    (hXδ₂ : LUV.RpnThresholdCodeSeq Xδ₂) (hXκ₂ : LUV.RpnThresholdCodeSeq Xκ₂)
    (hXδ₃ : LUV.RpnThresholdCodeSeq Xδ₃) (hXκ₃ : LUV.RpnThresholdCodeSeq Xκ₃) :
    (fun n => (gate (φa n) (Xa n)).expect P n - (gate (φf n) (Xf n)).expect P n) ≲ₙ
      fun _ => (L : ℝ) * (((a₁ : ℚ) / (b₁ : ℚ) : ℝ)
        + (((a₂ : ℚ) / (b₂ : ℚ) : ℝ) + ((a₃ : ℚ) / (b₃ : ℚ) : ℝ))) := by
  have h1 := li_noncapture (P := P) (DP := DP) φa φr Xa Xr Xδ₁ Xκ₁ L hL a₁ b₁ hb₁ hab₁ hvalid₁
    hdefect hext₁ hsealed₁ hworld hφa hφr hXa hXr hXδ₁ hXκ₁
  have h23 := li_noncapture_chain (P := P) (DP := DP) φr φd φf Xr Xd Xf Xδ₂ Xκ₂ Xδ₃ Xκ₃ L hL
    a₂ b₂ hb₂ hab₂ a₃ b₃ hb₃ hab₃ hvalid₂ hvalid₃ hsupply hdiscover hext₂ hext₃ hsealed₂
    hsealed₃ hworld hφr hφd hφf hXr hXd hXf hXδ₂ hXκ₂ hXδ₃ hXκ₃
  have h := asympLE_add h1 h23
  intro ε hε
  filter_upwards [h ε hε] with n hn
  simp only [MediatedPair.compile] at hn
  linarith

end Chain

end Workspace.Deference.Contrib.TransparentChain

#print axioms Workspace.Deference.Contrib.TransparentChain.tauR_eq_zero_of_eq
#print axioms Workspace.Deference.Contrib.TransparentChain.tauR_comm
#print axioms Workspace.Deference.Contrib.TransparentChain.abs_sub_le_tauR
#print axioms Workspace.Deference.Contrib.TransparentChain.omission_le_adverse
#print axioms Workspace.Deference.Contrib.TransparentChain.tauR_le_disagree
#print axioms Workspace.Deference.Contrib.TransparentChain.li_noncapture_chain3
