import Cleanroom.Udt.UdtPolicyCalc.Tree

/-!
# Vanessa's dynamically consistent update, Bayesian case: T14

Post 4 ("Essential Miscellanea", lines 74–106, as rendered by Diffractor; ATTRIBUTION-UNVETTED
for Kosoy's rule): updating the generalized environment `(e, 0)` on the history `h` gives
`(P_{π⋈e}(h)·(e|h), P_{π⋈e}(¬h)·E_{π⋈e}[U | ¬h])`, and "the past agent perfectly agrees with the
future agent on what to do". The Bayesian specialization proved here: with an **action
environment** `e₀ : Node → A → FinDist O` (the "ordinary sort of environment that only reacts to
your action, not what you would do in different scenarios", Post 4 line 84), lifted to Post 1's
`Env` by `e π h := e₀ h (π h)`, the updated score
`S_h π' := pH · contVal π' + offMass` equals `V e U π'` for every continuation `π'` agreeing
with the reference policy `π` on every node that does not extend `h` (`score_eq_V`), so the
argmax over continuations is the ex-ante argmax (`score_argmax_iff`). `pH` depends on the
reference policy only through its values on nodes not extending `h` (`pH_eq_of_agreesOff`).

**Mandate deviation, disclosed.** The mandate's "policy-independent environment `e : Node →
FinDist O` (lift to `Env` by ignoring `π`)" would make `V e U` constant in `π` (the policy would
enter nowhere), so the theorem would be vacuous; the object Post 4 describes reads the *action at
the current node*, which is `ActionEnv` here. The policy-dependent failure witness (counterfactual
mugging) is in `Toys.lean`.

Package `udt-policy-calc` (faf-cleanroom run, 2026-09-29/30).
-/

namespace Cleanroom.Udt.UdtPolicyCalc

noncomputable section

namespace Tree

open Finset

variable {O A : Type} {n : ℕ}

/-- An **action environment**: at each node, the next observation's law depends on the action
taken *there*, not on the policy elsewhere (Post 4's "ordinary sort of environment").
Source: `references/udt101/04-essential-miscellanea.md` line 84 (udt-rep-2-023)
Kind: D
Fidelity: exact (Post 1's `e` reading `π` only at the current node)
Hyps: n/a -/
abbrev ActionEnv (O A : Type) (n : ℕ) [Fintype O] := Node O n → A → FinDist O

/-- The lift of an action environment to a policy-selection environment: `e π h := e₀ h (π h)`.
Source: `references/udt101/04-essential-miscellanea.md` line 84 (udt-rep-2-023)
Kind: D
Fidelity: exact
Hyps: n/a -/
def liftEnv [Fintype O] (e₀ : ActionEnv O A n) : Env O A n := fun π h => e₀ h (π h)

/-- The leaf `l` **extends** the node `h`: `h` is the length-`|h|` prefix of `l`.
Source: none: infrastructure (Post 4's "`h` occurs")
Kind: D
Fidelity: exact
Hyps: n/a -/
def LeafExt (h : Node O n) (l : Leaf O n) : Prop := prefixOf' l h.1 h.1.isLt.le = h.2

instance [DecidableEq O] (h : Node O n) : DecidablePred (LeafExt h) := fun l =>
  inferInstanceAs (Decidable (prefixOf' l h.1 h.1.isLt.le = h.2))

/-- Supporting lemma `LeafExt.apply_eq` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem LeafExt.apply_eq {h : Node O n} {l : Leaf O n} (hl : LeafExt h l) (j : Fin n)
    (hj : j.val < h.1.val) : l j = h.2 ⟨j.val, hj⟩ := by
  have := congrFun hl ⟨j.val, hj⟩
  simp only [prefixOf'] at this
  rw [← this]
  exact congrArg l (Fin.ext rfl)

/-- Supporting lemma `eq_on_lt_of_leafExt` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem eq_on_lt_of_leafExt {h : Node O n} {l l' : Leaf O n} (hl : LeafExt h l)
    (hl' : LeafExt h l') (j : Fin n) (hj : j.val < h.1.val) : l j = l' j := by
  rw [hl.apply_eq j hj, hl'.apply_eq j hj]

/-- Supporting lemma `prefixOf_eq_of_leafExt` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prefixOf_eq_of_leafExt {h : Node O n} {l l' : Leaf O n} (hl : LeafExt h l)
    (hl' : LeafExt h l') (k : Fin n) (hk : k.val ≤ h.1.val) : prefixOf l k = prefixOf l' k := by
  show (⟨k, prefixOf' l k k.isLt.le⟩ : Node O n) = ⟨k, prefixOf' l' k k.isLt.le⟩
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i
  show l (Fin.castLE _ i) = l' (Fin.castLE _ i)
  exact eq_on_lt_of_leafExt hl hl' _ (lt_of_lt_of_le i.isLt hk)

/-- The node `m` **extends** the node `h`: `h` is a prefix of `m`.
Source: none: infrastructure
Kind: D
Fidelity: exact
Hyps: n/a -/
def NodeExt (h m : Node O n) : Prop :=
  ∃ hk : h.1.val ≤ m.1.val, ∀ i : Fin h.1, h.2 i = m.2 (Fin.castLE hk i)

/-- Supporting lemma `NodeExt.refl` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem NodeExt.refl (h : Node O n) : NodeExt h h :=
  ⟨le_rfl, fun i => congrArg h.2 (Fin.ext rfl)⟩

/-- Supporting lemma `not_nodeExt_of_lt` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem not_nodeExt_of_lt {h m : Node O n} (hlt : m.1.val < h.1.val) : ¬ NodeExt h m :=
  fun ⟨hk, _⟩ => absurd hk (not_le.mpr hlt)

/-- A node on the path to `l` at depth `≥ |h|` extends `h` iff `l` does.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem nodeExt_prefixOf_iff {h : Node O n} {l : Leaf O n} {k : Fin n} (hk : h.1.val ≤ k.val) :
    NodeExt h (prefixOf l k) ↔ LeafExt h l := by
  constructor
  · rintro ⟨_, hi⟩
    funext i
    rw [hi i]
    simp only [prefixOf, prefixOf', Fin.castLE_castLE]
  · intro hl
    refine ⟨hk, fun i => ?_⟩
    rw [← hl]
    simp only [prefixOf, prefixOf', Fin.castLE_castLE]

/-- `π'` **agrees with `π` off `h`**: on every node that does not extend `h` (prefixes of `h`
and other branches).
Source: `references/udt101/04-essential-miscellanea.md` lines 102–104 ("what your policy does in the situations where `h` never happened") (udt-rep-2-023)
Kind: D
Fidelity: exact
Hyps: n/a -/
def AgreesOff (π π' : Pol O A n) (h : Node O n) : Prop := ∀ m, ¬ NodeExt h m → π m = π' m

/-- Supporting lemma `AgreesOff.refl` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem AgreesOff.refl (π : Pol O A n) (h : Node O n) : AgreesOff π π h := fun _ _ => rfl

/-- Changing a policy at `h` only is a continuation agreeing off `h`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem AgreesOff.update [DecidableEq (Node O n)] (π : Pol O A n) (h : Node O n) (a : A) :
    AgreesOff π (Function.update π h a) h := by
  intro m hm
  by_cases heq : m = h
  · subst heq
    exact absurd (NodeExt.refl m) hm
  · rw [Function.update_of_ne heq]

/-! ### The updated generalized environment and its score -/

/-- `P_{π⋈e}(h)`: the mass of the leaves extending `h`.
Source: `references/udt101/04-essential-miscellanea.md` line 96 (udt-rep-2-023)
Kind: D
Fidelity: exact
Hyps: n/a -/
def pH [Fintype O] [DecidableEq O] (e : Env O A n) (π : Pol O A n) (h : Node O n) : ℝ :=
  ∑ l ∈ univ.filter (LeafExt h), runLaw e π l

/-- `E_{π'⋈(e|h)}[U]`: the continuation's expected utility from `h`, the product of the kernel from
depth `|h|` on (`suffixLaw`) against `U` over the leaves extending `h`.
Source: `references/udt101/04-essential-miscellanea.md` line 96 (`e|h`) (udt-rep-2-023)
Kind: D
Fidelity: exact
Hyps: n/a -/
def contVal [Fintype O] [DecidableEq O] (e : Env O A n) (U : Leaf O n → ℝ) (h : Node O n) (π' : Pol O A n) : ℝ :=
  ∑ l ∈ univ.filter (LeafExt h), suffixLaw (envKernel e π') h.1 l * U l

/-- `b = P_{π⋈e}(¬h)·E_{π⋈e}[U | ¬h]` in multiplicative form (no division): the utility mass of the
leaves not extending `h`.
Source: `references/udt101/04-essential-miscellanea.md` line 96 (udt-rep-2-023)
Kind: D
Fidelity: exact (`P(¬h)·E[U | ¬h]` written as the unnormalized sum)
Hyps: n/a -/
def offMass [Fintype O] [DecidableEq O] (e : Env O A n) (U : Leaf O n → ℝ) (π : Pol O A n) (h : Node O n) : ℝ :=
  ∑ l ∈ univ.filter (fun l => ¬ LeafExt h l), runLaw e π l * U l

/-- **The score of a continuation under the updated generalized environment**:
`S_h π' := P(h)·E_{π'⋈(e|h)}[U] + P(¬h)·E[U | ¬h]` (the `λ`, environment and `b` parts of Post 4's
`(λe, b)`).
Source: `references/udt101/04-essential-miscellanea.md` lines 92–100 (udt-rep-2-023)
Kind: D
Fidelity: exact (Bayesian specialization)
Hyps: n/a -/
def score [Fintype O] [DecidableEq O] (e : Env O A n) (U : Leaf O n → ℝ) (π : Pol O A n) (h : Node O n) (π' : Pol O A n) : ℝ :=
  pH e π h * contVal e U h π' + offMass e U π h

/-- The product of the kernel strictly before depth `m`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def prefixLaw (F : Node O n → O → ℝ) (m : ℕ) (l : Leaf O n) : ℝ :=
  ∏ k ∈ univ.filter (fun k : Fin n => ¬ m ≤ k.val), F (prefixOf l k) (l k)

/-- Supporting lemma `pathLaw_eq_suffix_mul_prefix` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pathLaw_eq_suffix_mul_prefix (F : Node O n → O → ℝ) (m : ℕ) (l : Leaf O n) :
    pathLaw F l = suffixLaw F m l * prefixLaw F m l :=
  (Finset.prod_filter_mul_prod_filter_not univ (fun k : Fin n => m ≤ k.val) _).symm

/-- Supporting lemma `envKernel_liftEnv_eq_of_agreesOff` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem envKernel_liftEnv_eq_of_agreesOff [Fintype O] {e₀ : ActionEnv O A n} {π π' : Pol O A n}
    {h : Node O n} (hag : AgreesOff π π' h) {m : Node O n} (hm : ¬ NodeExt h m) (o : O) :
    envKernel (liftEnv e₀) π' m o = envKernel (liftEnv e₀) π m o := by
  simp only [envKernel, liftEnv]
  rw [hag m hm]

/-- Off `h`, the leaf law does not see the continuation.
Source: `references/udt101/04-essential-miscellanea.md` lines 102–104 (udt-rep-2-023)
Kind: L
Fidelity: exact
Hyps: none -/
theorem runLaw_eq_of_agreesOff_of_not_leafExt [Fintype O] {e₀ : ActionEnv O A n} {π π' : Pol O A n}
    {h : Node O n} (hag : AgreesOff π π' h) {l : Leaf O n} (hl : ¬ LeafExt h l) :
    runLaw (liftEnv e₀) π' l = runLaw (liftEnv e₀) π l := by
  unfold runLaw pathLaw
  refine Finset.prod_congr rfl fun k _ => ?_
  apply envKernel_liftEnv_eq_of_agreesOff hag
  intro hne
  by_cases hk : h.1.val ≤ k.val
  · exact hl ((nodeExt_prefixOf_iff hk).mp hne)
  · exact not_nodeExt_of_lt (show k.val < h.1.val by omega) hne

/-- On the leaves extending `h`, the prefix law is one number, the same for `π` and any
continuation agreeing off `h`.
Source: none: infrastructure (Post 4's `λ = P(h)`)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prefixLaw_eq_of_leafExt [Fintype O] {e₀ : ActionEnv O A n} {π π' : Pol O A n} {h : Node O n}
    (hag : AgreesOff π π' h) {l l' : Leaf O n} (hl : LeafExt h l) (hl' : LeafExt h l') :
    prefixLaw (envKernel (liftEnv e₀) π) h.1 l = prefixLaw (envKernel (liftEnv e₀) π') h.1 l' := by
  unfold prefixLaw
  refine Finset.prod_congr rfl fun k hk => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
  rw [prefixOf_eq_of_leafExt hl hl' k hk.le, eq_on_lt_of_leafExt hl hl' k hk]
  exact (envKernel_liftEnv_eq_of_agreesOff hag (not_nodeExt_of_lt (show k.val < h.1.val from hk)) _).symm

/-- The suffix law from depth `|h|` sums to one over the leaves extending `h`.
Source: `references/udt101/01-story-so-far.md` line 104 (udt-rep-2-018)
Kind: L
Fidelity: exact
Hyps: none -/
theorem sum_suffixLaw_leafExt [Fintype O] [DecidableEq O] {F : Node O n → O → ℝ} (hF : RowStochastic F) (h : Node O n) :
    ∑ l ∈ univ.filter (LeafExt h), suffixLaw F h.1 l = 1 := by
  have := sum_suffixLaw hF (n - h.1.val) h.1.val (by have := h.1.isLt; omega) h.2
  exact this

/-- **T14, headline (udt-rep-2-023; load-bearing 5).** For an action environment, the updated
score of every continuation `π'` agreeing with `π` off `h` equals its ex-ante value:
`S_h π' = E_{π'⋈e}[U]` (the law of total expectation in a finite tree). Hence the updated agent
and the time-`0` agent rank continuations identically — "dynamic consistency … a surprisingly
trivial theorem".
Source: `references/udt101/04-essential-miscellanea.md` lines 92–100 (udt-rep-2-023); ATTRIBUTION-UNVETTED for "Vanessa's rule as rendered by Diffractor"
Kind: P
Fidelity: exact (Bayesian specialization; the InfraBayes original is out of scope)
Hyps: (a) `AgreesOff π π' h` (the continuation changes nothing off `h`; explicit) -/
theorem score_eq_V [Fintype O] [DecidableEq O] (e₀ : ActionEnv O A n) (U : Leaf O n → ℝ) (π π' : Pol O A n) (h : Node O n)
    (hag : AgreesOff π π' h) : score (liftEnv e₀) U π h π' = V (liftEnv e₀) U π' := by
  have hoff : offMass (liftEnv e₀) U π h =
      ∑ l ∈ univ.filter (fun l => ¬ LeafExt h l), runLaw (liftEnv e₀) π' l * U l := by
    unfold offMass
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rw [runLaw_eq_of_agreesOff_of_not_leafExt hag hl]
  have hon : pH (liftEnv e₀) π h * contVal (liftEnv e₀) U h π' =
      ∑ l ∈ univ.filter (LeafExt h), runLaw (liftEnv e₀) π' l * U l := by
    unfold pH contVal
    rw [Finset.sum_mul_sum]
    have step : ∀ l ∈ univ.filter (LeafExt h), ∀ l' ∈ univ.filter (LeafExt h),
        runLaw (liftEnv e₀) π l * (suffixLaw (envKernel (liftEnv e₀) π') h.1 l' * U l') =
          suffixLaw (envKernel (liftEnv e₀) π) h.1 l * (runLaw (liftEnv e₀) π' l' * U l') := by
      intro l hl l' hl'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl hl'
      rw [runLaw, runLaw, pathLaw_eq_suffix_mul_prefix _ h.1, pathLaw_eq_suffix_mul_prefix _ h.1,
        prefixLaw_eq_of_leafExt hag hl hl']
      ring
    rw [Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun l' hl' => step l hl l' hl',
      Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    rw [sum_suffixLaw_leafExt (envKernel_rowStochastic (liftEnv e₀) π) h]
    simp only [one_mul]
  unfold score V
  rw [hon, hoff, Finset.sum_filter_add_sum_filter_not]

/-- **T14, the argmax corollary.** Among continuations agreeing with `π` off `h`, the updated
score's argmax is the ex-ante argmax.
Source: `references/udt101/04-essential-miscellanea.md` line 78 ("the past agent perfectly agrees with the future agent on what to do") (udt-rep-2-023)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem score_argmax_iff [Fintype O] [DecidableEq O] (e₀ : ActionEnv O A n) (U : Leaf O n → ℝ) (π : Pol O A n) (h : Node O n)
    (π' : Pol O A n) (hπ' : AgreesOff π π' h) :
    (∀ π'', AgreesOff π π'' h →
        score (liftEnv e₀) U π h π'' ≤ score (liftEnv e₀) U π h π') ↔
      (∀ π'', AgreesOff π π'' h → V (liftEnv e₀) U π'' ≤ V (liftEnv e₀) U π') := by
  constructor
  · intro H π'' hπ''
    have := H π'' hπ''
    rwa [score_eq_V e₀ U π π'' h hπ'', score_eq_V e₀ U π π' h hπ'] at this
  · intro H π'' hπ''
    rw [score_eq_V e₀ U π π'' h hπ'', score_eq_V e₀ U π π' h hπ']
    exact H π'' hπ''

/-- `P(h)` is the prefix law at any leaf extending `h` (the suffix mass is one).
Source: `references/udt101/04-essential-miscellanea.md` line 96 (udt-rep-2-023)
Kind: L
Fidelity: exact
Hyps: none -/
theorem pH_eq_prefixLaw [Fintype O] [DecidableEq O] (e : Env O A n) (π : Pol O A n) (h : Node O n) {l₀ : Leaf O n}
    (hl₀ : LeafExt h l₀) : pH e π h = prefixLaw (envKernel e π) h.1 l₀ := by
  unfold pH
  have : ∀ l ∈ univ.filter (LeafExt h),
      runLaw e π l = suffixLaw (envKernel e π) h.1 l * prefixLaw (envKernel e π) h.1 l₀ := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rw [runLaw, pathLaw_eq_suffix_mul_prefix _ h.1]
    congr 1
    unfold prefixLaw
    refine Finset.prod_congr rfl fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
    rw [prefixOf_eq_of_leafExt hl hl₀ k hk.le, eq_on_lt_of_leafExt hl hl₀ k hk]
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul,
    sum_suffixLaw_leafExt (envKernel_rowStochastic e π) h, one_mul]

/-- **`P(h)` does not depend on the policy at or below `h`** (only on the actions at `h`'s strict
prefixes): the "you only need to know what your policy does in the situations where `h` never
happened" remark.
Source: `references/udt101/04-essential-miscellanea.md` lines 102–104 (udt-rep-2-023)
Kind: P
Fidelity: exact
Hyps: (a) `AgreesOff π π' h` -/
theorem pH_eq_of_agreesOff [Fintype O] [DecidableEq O] (e₀ : ActionEnv O A n) {π π' : Pol O A n} {h : Node O n}
    (hag : AgreesOff π π' h) : pH (liftEnv e₀) π h = pH (liftEnv e₀) π' h := by
  by_cases hne : (univ.filter (LeafExt h)).Nonempty
  · obtain ⟨l₀, hl₀⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl₀
    rw [pH_eq_prefixLaw _ π h hl₀, pH_eq_prefixLaw _ π' h hl₀, prefixLaw_eq_of_leafExt hag hl₀ hl₀]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    unfold pH
    rw [hne, Finset.sum_empty, Finset.sum_empty]

end Tree

end

end Cleanroom.Udt.UdtPolicyCalc
