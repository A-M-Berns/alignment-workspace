/-
# Trace steering: the non-capture analogue of the corrigibility inequality

Round `projects/deference/rounds/2026-09-16-noncapture-compilation/`.

The reason-side comparison of a steered trace against its normalized comparator has the
same algebra as the effect-side comparison of a raw continuation against its
corrigibilization (`LICorrigibility.mismatch_bound`), with the mediation discrepancy
replaced by the **canonical content discrepancy** `d` between the two traces, the decline
regret replaced by the program's **non-extensionality** `κ` on each trace, and the
activation events replaced by the audit verdicts.

**1. The steering bound** (`steering_bound`): with `c_s, c_n` the audit verdicts on the
steered and normalized traces, `v_s, v_n` the program's verdicts and `v_s', v_n'` its
verdicts on the form-normalized traces of the same content, a content-Lipschitz
certificate `|v_s' − v_n'| ≤ L·d` and form terms `|v_s − v_s'| ≤ κ_s`, `|v_n − v_n'| ≤ κ_n`,
```
c_s·v_s − c_n·v_n  ≤  c_s c_n·(L·d + κ_s + κ_n) + D·c_s(1 − c_n)  .
```
**2. Extensionality** (`extensional_form_free`): a program that factors through the
canonical content has `κ = 0`; form steering — order, duplication, framing — has no
advantage against it.

**3. Weighted-count programs are content-Lipschitz** (`weightedCount_lipschitz`): the
committed-program class of weighted reason counts has `|V(c) − V(c')| ≤ L·|c Δ c'|` with
`L` the largest weight.  This is the reason-side twin of the evaluator's `L`-stability.

**3′. The total-scope repair** (`content_residual_zero_of_total_scope`): with every declared
reason type protected, the coverage barrier and sound authentication force the canonical
content to equal the true declared set, so the content residual against the fully-informed
comparator is `0`; the truthful cherry-picking countermodel is exactly what this hypothesis
removes, and it is a scope decision, not an interface property.

**4. Robust Openness over a declared class is a finite computation**
(`openUnder_iff`): for a finite declared class of log transforms, openness under every
transform is a finite conjunction of audit verdicts on transformed traces.

**5. The Logical-Induction transfer** (`steering_validAt`, `li_steering_le`): the steering
package supplies `LICorrigibility.ValidAt` for a compiled pair with `w_app := v_n' + (v_s
− v_s')`, so `li_bypass_le_compiled` applies verbatim: the inductor's expectations respect
the steering inequality, uniformly over polynomial-size efficiently generated menus, with
no calibration hypothesis.  Nothing of Logical Induction is re-proved.

**What this does not establish.**  That any normalization is the causal counterfactual of
an intervention; that the declared interface contains every relevant reason; that any
program is extensional; that the content discrepancy on activated worlds is small.  The
cherry-picking countermodel (`COUNTERMODELS.md` §1) is a fixture.  Names are provisional
(`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.LICorrigibilityCertificate

namespace Workspace.Deference.Contrib.TraceSteering

open LogicalInduction
open Workspace.Deference.Contrib.LICorrigibility
open scoped Classical

/-! ## 1. The steering bound -/

/-- **The steering bound.**  The reason-side twin of `mismatch_bound`. -/
theorem steering_bound (D L d κs κn vs vs' vn vn' : ℝ) (cs cn : Bool)
    (hvs : vs ≤ D) (hvn : 0 ≤ vn)
    (hlip : cs = true → cn = true → |vs' - vn'| ≤ L * d)
    (hκs : cs = true → cn = true → |vs - vs'| ≤ κs)
    (hκn : cs = true → cn = true → |vn - vn'| ≤ κn) :
    indR cs * vs - indR cn * vn
      ≤ indR cs * indR cn * (L * d + κs + κn) + D * (indR cs * (1 - indR cn)) := by
  cases cs with
  | false =>
      cases cn with
      | false => simp [indR]
      | true => simp [indR]; exact hvn
  | true =>
      cases cn with
      | false => simp [indR]; exact hvs
      | true =>
          simp [indR]
          have h1 := abs_le.mp (hlip rfl rfl)
          have h2 := abs_le.mp (hκs rfl rfl)
          have h3 := abs_le.mp (hκn rfl rfl)
          linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- The exact decomposition, as on the effect side. -/
theorem steering_identity (cs cn : Bool) (vs vn : ℝ) :
    indR cs * vs - indR cn * vn
      = indR cs * indR cn * (vs - vn) + indR cs * (1 - indR cn) * vs
        - (1 - indR cs) * indR cn * vn :=
  mismatch_identity cs cn vs vn

/-! ## 2. Extensionality -/

variable {Trace Content : Type*}

/-- A program is **extensional** when it factors through the canonical content. -/
def Extensional (canon : Trace → Content) (V : Trace → ℝ) : Prop :=
  ∃ F : Content → ℝ, ∀ T, V T = F (canon T)

/-- **Form steering is free against an extensional program**: two traces of the same
canonical content have the same verdict, so the form term is `0`. -/
theorem extensional_form_free {canon : Trace → Content} {V : Trace → ℝ}
    (h : Extensional canon V) (T T' : Trace) (hc : canon T = canon T') : |V T - V T'| ≤ 0 := by
  obtain ⟨F, hF⟩ := h
  rw [hF T, hF T', hc, sub_self, abs_zero]

/-- A program that reads the trace beyond its content is not extensional: the witness of
the necessity of canonicalization is any pair of same-content traces with different
verdicts. -/
theorem not_extensional_of_form {canon : Trace → Content} {V : Trace → ℝ}
    (T T' : Trace) (hc : canon T = canon T') (hv : V T ≠ V T') : ¬ Extensional canon V := by
  rintro ⟨F, hF⟩
  exact hv (by rw [hF T, hF T', hc])

/-! ## 3. Weighted-count programs are content-Lipschitz -/

/-- The verdict of a weighted-count program on a canonical content (a finite set of
reason ids). -/
def weightedCount {ι : Type*} (w : ι → ℝ) (c : Finset ι) : ℝ := ∑ r ∈ c, w r

/-- **Content-Lipschitz certificate of weighted-count programs.**  With `L` a bound on the
weights, `|V(c) − V(c')| ≤ L·|c Δ c'|`. -/
theorem weightedCount_lipschitz {ι : Type*} [DecidableEq ι] (w : ι → ℝ) (L : ℝ)
    (hL : ∀ r, |w r| ≤ L) (c c' : Finset ι) :
    |weightedCount w c - weightedCount w c'| ≤ L * (c \ c' ∪ c' \ c).card := by
  have hsplit : weightedCount w c - weightedCount w c'
      = ∑ r ∈ c \ c', w r - ∑ r ∈ c' \ c, w r := by
    unfold weightedCount
    have h1 : ∑ r ∈ c, w r = ∑ r ∈ c \ c', w r + ∑ r ∈ c ∩ c', w r := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff_inter c c')]
      congr 1
      exact (Finset.sdiff_union_inter c c').symm
    have h2 : ∑ r ∈ c', w r = ∑ r ∈ c' \ c, w r + ∑ r ∈ c ∩ c', w r := by
      rw [Finset.inter_comm, ← Finset.sum_union (Finset.disjoint_sdiff_inter c' c)]
      congr 1
      exact (Finset.sdiff_union_inter c' c).symm
    rw [h1, h2]; ring
  rw [hsplit]
  have hdisj : Disjoint (c \ c') (c' \ c) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1
  calc |∑ r ∈ c \ c', w r - ∑ r ∈ c' \ c, w r|
      ≤ |∑ r ∈ c \ c', w r| + |∑ r ∈ c' \ c, w r| := abs_sub _ _
    _ ≤ ∑ r ∈ c \ c', |w r| + ∑ r ∈ c' \ c, |w r| :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ r ∈ c \ c', L + ∑ r ∈ c' \ c, L :=
        add_le_add (Finset.sum_le_sum fun r _ => hL r) (Finset.sum_le_sum fun r _ => hL r)
    _ = L * (c \ c' ∪ c' \ c).card := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_union_of_disjoint hdisj]
        simp only [nsmul_eq_mul]
        push_cast
        ring

/-- **The total-scope repair.**  When every declared reason type is protected, the coverage
barrier (every true declared reason present at commitment) together with sound
authentication (every present declared reason true) forces the canonical content to be the
true declared set, so the content discrepancy against the fully-informed comparator is `0`.
Neither hypothesis is an interface property: the first is scope totality, the second is
the settlement engine's. -/
theorem content_residual_zero_of_total_scope {ι : Type*} [DecidableEq ι]
    (c truth : Finset ι) (hbar : ∀ r ∈ truth, r ∈ c) (hauth : ∀ r ∈ c, r ∈ truth) :
    (c \ truth ∪ truth \ c).card = 0 := by
  have : c = truth := Finset.Subset.antisymm (fun r hr => hauth r hr) (fun r hr => hbar r hr)
  subst this
  simp

/-! ## 4. Robust Openness over a declared transform class is a finite computation -/

/-- Openness under every transform of a finite declared class: the audit passes on
every transformed trace. -/
def openUnder (J : Finset (Trace → Trace)) (audit : Trace → Bool) (T : Trace) : Bool :=
  decide (∀ j ∈ J, audit (j T) = true)

theorem openUnder_iff (J : Finset (Trace → Trace)) (audit : Trace → Bool) (T : Trace) :
    openUnder J audit T = true ↔ ∀ j ∈ J, audit (j T) = true := by
  unfold openUnder
  exact decide_eq_true_iff

/-! ## 5. The Logical-Induction transfer -/

/-- **The steering package supplies the compiled pair's validity.**  With the raw value
`v_s`, the approve-branch surrogate `v_n' + (v_s − v_s')`, the actual value `v_n`, the
content discrepancy `d` and the form regret `κ_s + κ_n`, `ValidAt` holds for the compiled
pair, so `li_bypass_le_compiled` applies to trace steering verbatim. -/
def steering_validAt (φs φn : Sentence) (Xs Xn Xd Xκ : LUV) (lam : ℚ) (v : PCWorld)
    (vs vs' vn vn' d κs κn : ℝ)
    (hvs : 0 ≤ vs ∧ vs ≤ 1) (hvn : 0 ≤ vn ∧ vn ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1)
    (hκ : 0 ≤ κs + κn ∧ κs + κn ≤ 1)
    (hxs : v.ValuesAt Xs vs) (hxn : v.ValuesAt Xn vn) (hxd : v.ValuesAt Xd d)
    (hxκ : v.ValuesAt Xκ (κs + κn))
    (hlip : v.Holds φs → v.Holds φn → |vs' - vn'| ≤ (lam : ℝ) * d)
    (hκs : v.Holds φs → v.Holds φn → |vs - vs'| ≤ κs)
    (hκn : v.Holds φs → v.Holds φn → |vn - vn'| ≤ κn) :
    ValidAt (MediatedPair.compile φs φn Xs Xn Xd Xκ lam) v :=
  MediatedPair.compile_validAt φs φn Xs Xn Xd Xκ lam v vs (vn' + (vs - vs')) vn d (κs + κn)
    hvs hvn hd hκ hxs hxn hxd hxκ
    (fun hs hn => by
      have := hlip hs hn
      calc |vs - (vn' + (vs - vs'))| = |vs' - vn'| := by ring_nf
        _ ≤ (lam : ℝ) * d := this)
    (fun hs hn => by
      have h1 := abs_le.mp (hκs hs hn)
      have h2 := abs_le.mp (hκn hs hn)
      linarith [h1.1, h1.2, h2.1, h2.2])

/-- **Logical Induction learns the steering inequality**: the compiled theorem applied to
steering pairs.  The hypotheses are the emission of the two audit sentence families and
the four base families (steered verdict, normalized verdict, content discrepancy, form
regret), an e.c. bounded `λ_n`, validity of the steering package in every completed-theory
world, and a consistent world at every stage. -/
theorem li_steering_le {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (φs φn : ℕ → Sentence) (Xs Xn Xd Xκ : ℕ → LUV) (lam : ℕ → ℚ)
    (hvalid : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ValidAt (MediatedPair.compile (φs n) (φn n) (Xs n) (Xn n) (Xd n) (Xκ n) (lam n)) v)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (Λ : ℝ) (hΛ : ∀ n, |((lam n : ℚ) : ℝ)| ≤ Λ)
    (hlam : ∃ c, PolyFueled c (fun n => Encodable.encode (-(lam n))))
    (hφs : RpnSentenceCodes φs) (hφn : RpnSentenceCodes φn)
    (hXs : LUV.RpnThresholdCodeSeq Xs) (hXn : LUV.RpnThresholdCodeSeq Xn)
    (hXd : LUV.RpnThresholdCodeSeq Xd) (hXκ : LUV.RpnThresholdCodeSeq Xκ) :
    let p := fun n => MediatedPair.compile (φs n) (φn n) (Xs n) (Xn n) (Xd n) (Xκ n) (lam n)
    (fun n => (p n).Uraw.expect P n - (p n).Ucorr.expect P n) ≲ₙ
      fun n => ((p n).lam : ℝ) * (p n).Gδ.expect P n + (p n).Gρ.expect P n
        + (p n).GM.expect P n :=
  li_bypass_le_compiled φs φn Xs Xn Xd Xκ lam hvalid hworld Λ hΛ hlam hφs hφn hXs hXn hXd hXκ

/-! ## 6. Witnesses -/

namespace Witness

/-- **The steering bound is attained on the form branch**: same content, an order-sensitive
program, `κ_s = 1/4`, advantage `1/4`. -/
theorem form_attained :
    indR true * (3/4 : ℝ) - indR true * (1/2) = 1/4 ∧
    indR true * indR true * ((1 : ℝ) * 0 + 1/4 + 0) + 1 * (indR true * (1 - indR true)) = 1/4 := by
  simp [indR]; norm_num

/-- **A weighted-count witness of the Lipschitz certificate**: weights `1/4, −1/4`, contents
`{0}` and `{0, 1}`, difference `1/4 = L·1`. -/
theorem lipschitz_attained :
    let w : ℕ → ℝ := fun r => if r = 0 then 1/4 else -1/4
    |weightedCount w {0} - weightedCount w {0, 1}| = (1/4 : ℝ) * (({0} \ {0, 1} ∪ {0, 1} \ {0} : Finset ℕ)).card := by
  simp [weightedCount]
  norm_num [Finset.sdiff_eq_empty_iff_subset]
  decide

end Witness

end Workspace.Deference.Contrib.TraceSteering

#print axioms Workspace.Deference.Contrib.TraceSteering.steering_bound
#print axioms Workspace.Deference.Contrib.TraceSteering.steering_identity
#print axioms Workspace.Deference.Contrib.TraceSteering.extensional_form_free
#print axioms Workspace.Deference.Contrib.TraceSteering.not_extensional_of_form
#print axioms Workspace.Deference.Contrib.TraceSteering.weightedCount_lipschitz
#print axioms Workspace.Deference.Contrib.TraceSteering.content_residual_zero_of_total_scope
#print axioms Workspace.Deference.Contrib.TraceSteering.openUnder_iff
#print axioms Workspace.Deference.Contrib.TraceSteering.steering_validAt
#print axioms Workspace.Deference.Contrib.TraceSteering.li_steering_le
#print axioms Workspace.Deference.Contrib.TraceSteering.Witness.form_attained
#print axioms Workspace.Deference.Contrib.TraceSteering.Witness.lipschitz_attained
