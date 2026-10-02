import FactoredSpaces.BayesNet
import Cleanroom.Decision.DpCausalConsist.PiSums

/-!
# `dp-causal-consist`: the truncated factorization over FAF's Bayes nets

The DAG side of the package, stated over FAF's objects: `Digraph V` (Mathlib), `Digraph.parents`,
`FactoredSpaces.CPD` (a conditional probability distribution per node and parent configuration),
`FactorizesOverDAG` (Markov compatibility, `BayesNet.lean:370`, unpacked here as `IsFor`),
`FactoredSpaces.Distr` (real-valued mass functions) and `Distr.condProb`.

**Defined here, absent from FAF** (mandate §0, §3.4): the factor `cpdFactor φ v x` of a CPD at a
point; the truncated factorization `truncate hG φ m a` (Pearl's `do(m := a)` law, Definition 24);
the conditional distribution `condDistr`; the descendant partition `desc`/`descM`/`nondesc` and
the fixed algebra `InFixedAlgebra` (events measurable in the non-descendant coordinates);
`CausalStructure` (an acyclic DAG with a CPD) and `CausalStructure.IsFor P` (exactly
`FactorizesOverDAG`'s witness, unpacked so the CPD stays explicit — the CPD at a null parent
configuration is not determined by `P`, and Theorem 3(i)'s iff is about that CPD).

**The one real lemma** (mandate T1): `sum_cpd_prod_eq_one` — summing the product of the CPD
factors of any coordinate set `S` over the values of `S` gives `1`, by removing a sink of `S`
(a node of maximal `Digraph.depth`) and integrating its factor out. Everything else — the
truncated law is a distribution, Pearl's invariance on the fixed algebra (`truncate_prob_eq_of_inFixedAlgebra`,
T1), the local Markov identity `P(x_v = b ∧ pa_v = c) = φ_v(c)(b) · P(pa_v = c)` (`prob_val_inter_parentCell`,
an FAF API request: FAF keeps `BayesNet.condProb_tau_eq` private and states it on `τ`), and
Theorem 3(i) (`thm3_i`) — is bookkeeping over `sum_out`.

**Disclosures.** `truncate` carries the acyclicity proof `hG` because its `sum_eq_one` needs a sink;
`[∀ v, Nonempty (Val v)]` supplies the base point of `sum_out`. `desc`/`nondesc` are classical
filters (`Digraph.IsAncestor` is `TransGen`, not decidable in general); on `Fin 3` witnesses their
membership is proved by hand.
-/

namespace Cleanroom.Decision.DpCausalConsist

open FactoredSpaces Finset

section cpd

variable {V : Type} [Fintype V] [DecidableEq V] {Val : V → Type} [∀ v, Fintype (Val v)]
  [∀ v, DecidableEq (Val v)] {G : Digraph V} [DecidableRel G.Adj]

/-- The factor `P(x_v | x_pa(v))` of a CPD family at the point `x`: `(φ v (x_pa(v))).mass (x v)`.
Source: FAF `FactorizesOverDAG` (`BayesNet.lean:370`, the factors of eq. (2))
Kind: D -/
def cpdFactor (φ : CPD (G := G) (Val := Val)) (v : V) (x : Pt Val) : ℝ :=
  (φ v (parentConfig G Val x v)).mass (x v)

/-- `cpdFactor` is nonnegative. Source: none: infrastructure. Kind: L -/
theorem cpdFactor_nonneg (φ : CPD (G := G) (Val := Val)) (v : V) (x : Pt Val) :
    0 ≤ cpdFactor φ v x :=
  (φ v _).nonneg _

omit [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] in
/-- The parent configuration at `v` reads only the parents of `v`.
Source: none: infrastructure
Kind: L -/
theorem parentConfig_congr (v : V) {x y : Pt Val} (h : ∀ u ∈ G.parents v, x u = y u) :
    parentConfig G Val x v = parentConfig G Val y v :=
  funext fun i => h i.1 i.2

/-- The factor at `v` reads only `v` and its parents.
Source: none: infrastructure
Kind: L -/
theorem cpdFactor_congr (φ : CPD (G := G) (Val := Val)) (v : V) {x y : Pt Val}
    (hpa : ∀ u ∈ G.parents v, x u = y u) (hv : x v = y v) :
    cpdFactor φ v x = cpdFactor φ v y := by
  have h1 : parentConfig G Val x v = parentConfig G Val y v := parentConfig_congr v hpa
  show (φ v (parentConfig G Val x v)).mass (x v) = (φ v (parentConfig G Val y v)).mass (y v)
  rw [h1, hv]

/-- Every nonempty set of nodes of an acyclic digraph has a sink (a node with no child in the
set): a node of maximal `Digraph.depth`.
Source: none: infrastructure (FAF `Digraph.depth_lt`)
Kind: L -/
theorem exists_sink (hG : G.IsAcyclic) {S : Finset V} (hS : S.Nonempty) :
    ∃ v ∈ S, ∀ u ∈ S, ¬ G.Adj v u := by
  obtain ⟨v, hv, hmax⟩ := S.exists_max_image (Digraph.depth hG) hS
  exact ⟨v, hv, fun u hu hadj => absurd (hmax u hu) (not_le.mpr (Digraph.depth_lt hG hadj))⟩

/-- **The CPD factors of any coordinate set sum to one over that set.** For every `S ⊆ V` and
base point `x₀`, `∑_{x : x = x₀ off S} ∏_{v ∈ S} φ_v(x_v | x_pa(v)) = 1`. Proof: remove a sink
`v` of `S` (no factor of `S ∖ {v}` reads `x_v`, and `φ_v`'s own parents exclude `v`), integrate
its factor out (`Distr.sum_eq_one`), recurse.
Source: mandate T1 ("the one real lemma of `Defs.lean`": the truncated law sums to one)
Kind: P
Fidelity: exact
Hyps: (a) `G` acyclic -/
theorem sum_cpd_prod_eq_one (hG : G.IsAcyclic) (φ : CPD (G := G) (Val := Val)) (S : Finset V)
    (x₀ : Pt Val) :
    ∑ x : Pt Val, (if ∀ u ∉ S, x u = x₀ u then ∏ v ∈ S, cpdFactor φ v x else 0) = 1 := by
  induction S using Finset.strongInduction generalizing x₀ with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have h0 : ∀ x : Pt Val, (∀ u ∉ (∅ : Finset V), x u = x₀ u) ↔ x = x₀ := by
      intro x; constructor
      · intro h; funext u; exact h u (Finset.notMem_empty u)
      · rintro rfl; intros; rfl
    simp_rw [h0, Finset.prod_empty]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  · obtain ⟨v, hv, hsink⟩ := exists_sink hG hne
    rw [sum_fix_coord v (x₀ v)]
    have key : ∀ x : Pt Val, x v = x₀ v →
        (∑ b, if ∀ u ∉ S, Function.update x v b u = x₀ u then
          ∏ w ∈ S, cpdFactor φ w (Function.update x v b) else 0)
        = if ∀ u ∉ S.erase v, x u = x₀ u then ∏ w ∈ S.erase v, cpdFactor φ w x else 0 := by
      intro x hxv
      have hcond : ∀ b : Val v, (∀ u ∉ S, Function.update x v b u = x₀ u) ↔
          (∀ u ∉ S.erase v, x u = x₀ u) := by
        intro b; constructor
        · intro h u hu
          by_cases huv : u = v
          · subst huv; exact hxv
          · have hu' : u ∉ S := fun h' => hu (Finset.mem_erase.mpr ⟨huv, h'⟩)
            have := h u hu'
            rwa [Function.update_of_ne huv] at this
        · intro h u hu
          have hne : u ≠ v := fun h' => hu (h' ▸ hv)
          rw [Function.update_of_ne hne]
          exact h u (fun h' => hu (Finset.mem_erase.mp h').2)
      have hprod : ∀ b : Val v, ∏ w ∈ S, cpdFactor φ w (Function.update x v b)
          = (φ v (parentConfig G Val x v)).mass b * ∏ w ∈ S.erase v, cpdFactor φ w x := by
        intro b
        rw [← Finset.mul_prod_erase S _ hv]
        congr 1
        · unfold cpdFactor
          have hpc : parentConfig G Val (Function.update x v b) v = parentConfig G Val x v := by
            funext i
            refine Function.update_of_ne (fun h' => Digraph.notMem_parents_self hG v ?_) b x
            have hi := i.2
            rw [h'] at hi
            exact hi
          rw [hpc, Function.update_self]
        · refine Finset.prod_congr rfl fun w hw => ?_
          have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
          have hwS : w ∈ S := (Finset.mem_erase.mp hw).2
          apply cpdFactor_congr
          · intro u hu
            apply Function.update_of_ne
            intro h'
            subst h'
            exact hsink w hwS ((Digraph.mem_parents G).mp hu)
          · exact Function.update_of_ne hwv _ _
      simp_rw [hcond, hprod]
      split_ifs with h
      · rw [← Finset.sum_mul, (φ v _).sum_eq_one, one_mul]
      · simp
    calc ∑ x : Pt Val, (if x v = x₀ v then ∑ b, if ∀ u ∉ S, Function.update x v b u = x₀ u then
            ∏ w ∈ S, cpdFactor φ w (Function.update x v b) else 0 else 0)
        = ∑ x : Pt Val, (if ∀ u ∉ S.erase v, x u = x₀ u then
            ∏ w ∈ S.erase v, cpdFactor φ w x else 0) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hxv : x v = x₀ v
          · rw [if_pos hxv, key x hxv]
          · rw [if_neg hxv, if_neg]
            intro h
            exact hxv (h v (fun h' => (Finset.mem_erase.mp h').1 rfl))
      _ = 1 := ih (S.erase v) (Finset.erase_ssubset hv) x₀

/-- **Summing out a coordinate set `S`**: for a weight `w` that reads only the coordinates off
`S`, `∑_x w(x) ∏_{v ∈ S} φ_v(x) = ∑_{x : x = x₀ on S} w(x)`.
Source: none: infrastructure (the workhorse of T1 and T2)
Kind: P
Hyps: (a) `G` acyclic; `w` reads only the coordinates off `S` -/
theorem sum_out (hG : G.IsAcyclic) (φ : CPD (G := G) (Val := Val)) (S : Finset V) (x₀ : Pt Val)
    (w : Pt Val → ℝ) (hw : ∀ x y, (∀ u ∉ S, y u = x u) → w y = w x) :
    ∑ x, w x * ∏ v ∈ S, cpdFactor φ v x
      = ∑ x : Pt Val, if (∀ u ∈ S, x u = x₀ u) then w x else 0 := by
  rw [sum_split_agree S x₀]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · rw [sum_agree_const_mul S x w _ (fun y hy => hw x y hy), sum_cpd_prod_eq_one hG φ S x,
      mul_one]
  · rfl

end cpd

/-! ## The truncated factorization and the conditional distribution -/

section truncate

variable {V : Type} [Fintype V] [DecidableEq V] {Val : V → Type} [∀ v, Fintype (Val v)]
  [∀ v, DecidableEq (Val v)] [∀ v, Nonempty (Val v)] {G : Digraph V} [DecidableRel G.Adj]

/-- The truncated product `∏_{v ≠ m} φ_v(x)` sums to one over the points with `x_m = a`.
Source: mandate T1 (`truncate_sum_eq_one`)
Kind: P
Hyps: (a) `G` acyclic -/
theorem truncate_sum_eq_one (hG : G.IsAcyclic) (φ : CPD (G := G) (Val := Val)) (m : V)
    (a : Val m) :
    ∑ x : Pt Val, (if x m = a then ∏ v ∈ Finset.univ.erase m, cpdFactor φ v x else 0) = 1 := by
  obtain ⟨z⟩ : Nonempty (Pt Val) := inferInstance
  have h := sum_cpd_prod_eq_one hG φ (Finset.univ.erase m) (Function.update z m a)
  rw [← h]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hiff : (∀ u ∉ Finset.univ.erase m, x u = Function.update z m a u) ↔ x m = a := by
    constructor
    · intro h'
      have := h' m (by simp)
      rwa [Function.update_self] at this
    · intro hxm u hu
      have hum : u = m := by
        by_contra hne
        exact hu (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
      subst hum
      rw [Function.update_self]; exact hxm
  rw [if_congr hiff rfl rfl]

/-- **The truncated factorization (Definition 24)** — Pearl's interventional law `do(m := a)`:
mass `∏_{v ≠ m} φ_v(x_v | x_pa(v))` at the points with `x_m = a`, `0` elsewhere. The factor of
`m` is cut; every other factor is kept, including those of the children of `m`, which read
`x_m = a` through their parent configuration.
Source: [[learning-cdt-renderings]] Definition 24 ("its interventional supposition of `a` is
`cf^G_s(a) := (P^{G,a}, V^{G,a})` by truncated factorization"); Theorem 3's setting
Kind: D
Fidelity: exact (finite coordinate spaces; the acyclicity proof is an argument because the
normalisation needs a sink) -/
noncomputable def truncate (hG : G.IsAcyclic) (φ : CPD (G := G) (Val := Val)) (m : V)
    (a : Val m) : Distr (Pt Val) where
  mass x := if x m = a then ∏ v ∈ Finset.univ.erase m, cpdFactor φ v x else 0
  nonneg x := by
    split_ifs
    · exact Finset.prod_nonneg fun v _ => cpdFactor_nonneg φ v x
    · exact le_rfl
  sum_eq_one := truncate_sum_eq_one hG φ m a

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
theorem truncate_mass (hG : G.IsAcyclic) (φ : CPD (G := G) (Val := Val)) (m : V) (a : Val m)
    (x : Pt Val) :
    (truncate hG φ m a).mass x =
      if x m = a then ∏ v ∈ Finset.univ.erase m, cpdFactor φ v x else 0 := rfl

/-- The truncated law vanishes off `{x_m = a}`.
Source: mandate T1 (`truncate_mass_eq_zero_of_ne`)
Kind: L -/
theorem truncate_mass_eq_zero_of_ne (hG : G.IsAcyclic) (φ : CPD (G := G) (Val := Val)) (m : V)
    (a : Val m) {x : Pt Val} (hx : x m ≠ a) : (truncate hG φ m a).mass x = 0 := by
  rw [truncate_mass, if_neg hx]

/-- **Success**: the truncated law gives `{x_m = a}` probability one.
Source: [[decision-problems-v2]] Definition 2 (success, `P^a_s(a) = 1`); mandate T1
(`cfG_success`)
Kind: L -/
theorem truncate_prob_act (hG : G.IsAcyclic) (φ : CPD (G := G) (Val := Val)) (m : V)
    (a : Val m) : (truncate hG φ m a).prob {x | x m = a} = 1 := by
  rw [prob_setOf_eq_sum_ite, ← truncate_sum_eq_one hG φ m a]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [truncate_mass]
  split_ifs <;> rfl

omit [∀ v, Nonempty (Val v)] [∀ v, DecidableEq (Val v)] [DecidableEq V] in
/-- The truncated law's probability of an event `X`, as an indicator sum.
Source: none: infrastructure
Kind: L -/
theorem truncate_prob_eq_sum [DecidableEq V] (hG : G.IsAcyclic) (φ : CPD (G := G) (Val := Val))
    [∀ v, DecidableEq (Val v)] [∀ v, Nonempty (Val v)] (m : V) (a : Val m) (X : Finset (Pt Val)) :
    (truncate hG φ m a).prob ↑X =
      ∑ x : Pt Val, if x ∈ X ∧ x m = a then ∏ v ∈ Finset.univ.erase m, cpdFactor φ v x else 0 := by
  rw [prob_eq_sum_ite]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [truncate_mass]
  by_cases hX : x ∈ X <;> by_cases hm : x m = a <;> simp [hX, hm]

end truncate

section condDistr

variable {S : Type} [Fintype S]

/-- **The conditional distribution `P(· | A)`** of a finite distribution on an event of positive
probability: mass `P(x)/P(A)` on `A`, `0` off it. FAF has the conditional *probability*
`Distr.condProb` (junk `0` at a null condition) but not the conditioned distribution; this is
the object Theorem 3 compares the truncated law with.
Source: [[learning-cdt-renderings]] Theorem 3(i) (`P_{s_d}(· | a)`); FAF `Distr.condProb`
Kind: D
Fidelity: exact
Hyps: (a) `0 < P(A)` -/
noncomputable def condDistr (P : Distr S) (A : Set S) (h : 0 < P.prob A) : Distr S where
  mass x := A.indicator P.mass x / P.prob A
  nonneg x := div_nonneg (Set.indicator_nonneg (fun _ _ => P.nonneg _) _) h.le
  sum_eq_one := by
    rw [← Finset.sum_div]
    exact div_self h.ne'

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
theorem condDistr_mass (P : Distr S) (A : Set S) (h : 0 < P.prob A) (x : S) :
    (condDistr P A h).mass x = A.indicator P.mass x / P.prob A := rfl

/-- The conditioned distribution's probabilities are FAF's conditional probabilities:
`(P(· | A))(B) = P.condProb B A = P(B ∩ A)/P(A)`.
Source: none: infrastructure (the seam to FAF's `Distr.condProb`)
Kind: L -/
theorem condDistr_prob (P : Distr S) (A : Set S) (h : 0 < P.prob A) (B : Set S) :
    (condDistr P A h).prob B = P.condProb B A := by
  unfold Distr.condProb
  show ∑ x, B.indicator (condDistr P A h).mass x = P.prob (B ∩ A) / P.prob A
  rw [show P.prob (B ∩ A) = ∑ x, (B ∩ A).indicator P.mass x from rfl, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hB : x ∈ B <;> by_cases hA : x ∈ A <;>
    simp [Set.indicator_apply, hB, hA, condDistr_mass]

/-- Two distributions are equal iff their masses agree.
Source: none: infrastructure (FAF's `Distr.ext` in pointwise form)
Kind: L -/
theorem distr_ext_iff (P Q : Distr S) : P = Q ↔ ∀ x, P.mass x = Q.mass x :=
  ⟨fun h x => by rw [h], fun h => Distr.ext (funext h)⟩

end condDistr

/-! ## Descendants, non-descendants, the fixed algebra -/

section desc

variable {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V)

open Classical in
/-- The strict descendants of `m` in `G` (`IsAncestor m v`, i.e. a directed path `m ⇝ v`).
Source: [[learning-cdt-renderings]] Definition 24 (`nondesc_G(m)`), complement
Kind: D -/
noncomputable def desc (m : V) : Finset V := Finset.univ.filter fun v => G.IsAncestor m v

/-- `m` together with its strict descendants.
Source: none: infrastructure
Kind: D -/
noncomputable def descM (m : V) : Finset V := insert m (desc G m)

/-- **The non-descendants of `m`** (`m` excluded): the coordinates an intervention on `m` leaves
alone.
Source: [[learning-cdt-renderings]] Definition 24 (`𝓔₀^G := ⟨nondesc_G(m)⟩`)
Kind: D -/
noncomputable def nondesc (m : V) : Finset V := (descM G m)ᶜ

variable {G}

omit [Fintype V] [DecidableEq V] in
/-- Membership in `desc`. Source: none: infrastructure. Kind: L -/
theorem mem_desc [Fintype V] {m v : V} : v ∈ desc G m ↔ G.IsAncestor m v := by
  simp [desc]

/-- Membership in `nondesc`. Source: none: infrastructure. Kind: L -/
theorem mem_nondesc {m v : V} : v ∈ nondesc G m ↔ v ≠ m ∧ ¬ G.IsAncestor m v := by
  simp [nondesc, descM, mem_desc]

/-- Non-membership in `nondesc`. Source: none: infrastructure. Kind: L -/
theorem notMem_nondesc {m v : V} : v ∉ nondesc G m ↔ v = m ∨ G.IsAncestor m v := by
  rw [mem_nondesc]; tauto

/-- `m` is not its own strict descendant in an acyclic digraph.
Source: none: infrastructure
Kind: L -/
theorem m_notMem_desc (hG : G.IsAcyclic) (m : V) : m ∉ desc G m := by
  rw [mem_desc]; exact hG m

/-- `m` is not a non-descendant of itself. Source: none: infrastructure. Kind: L -/
theorem m_notMem_nondesc (m : V) : m ∉ nondesc G m := by
  rw [notMem_nondesc]; exact Or.inl rfl

/-- `nondesc = (descM)ᶜ`, in the form `u ∉ descM ↔ u ∈ nondesc`.
Source: none: infrastructure
Kind: L -/
theorem notMem_descM_iff {m u : V} : u ∉ descM G m ↔ u ∈ nondesc G m := by
  simp [nondesc]

/-- `u ∉ desc ↔ u ∈ nondesc ∨ u = m` (acyclic `G`). Source: none: infrastructure. Kind: L -/
theorem notMem_desc_iff (hG : G.IsAcyclic) {m u : V} :
    u ∉ desc G m ↔ u ∈ nondesc G m ∨ u = m := by
  rw [mem_nondesc, mem_desc]
  by_cases h : u = m
  · subst h; exact ⟨fun _ => Or.inr rfl, fun _ => hG u⟩
  · simp [h]

variable [DecidableRel G.Adj]

/-- **Parents of non-descendants are non-descendants.**
Source: none: infrastructure (Pearl's invariance argument)
Kind: L -/
theorem parents_subset_nondesc {m v : V} (hv : v ∈ nondesc G m) :
    G.parents v ⊆ nondesc G m := by
  intro u hu
  have hadj : G.Adj u v := (Digraph.mem_parents G).mp hu
  rw [mem_nondesc] at hv ⊢
  by_contra hcon
  push Not at hcon
  by_cases hum : u = m
  · subst hum; exact hv.2 (Relation.TransGen.single hadj)
  · exact hv.2 (Relation.TransGen.tail (hcon hum) hadj)

/-- **The parents of `m` are non-descendants of `m`.**
Source: none: infrastructure
Kind: L -/
theorem parents_m_subset_nondesc (hG : G.IsAcyclic) (m : V) :
    G.parents m ⊆ nondesc G m := by
  intro u hu
  have hadj : G.Adj u m := (Digraph.mem_parents G).mp hu
  rw [mem_nondesc]
  refine ⟨hG.ne_of_adj hadj, fun hanc => hG m (Relation.TransGen.tail hanc hadj)⟩

omit [DecidableRel G.Adj] in
/-- `∏_v f v = (∏_{v ∈ descM} f v) · ∏_{v ∈ nondesc} f v`.
Source: none: infrastructure
Kind: L -/
theorem prod_univ_eq_descM_mul_nondesc (m : V) (f : V → ℝ) :
    ∏ v, f v = (∏ v ∈ descM G m, f v) * ∏ v ∈ nondesc G m, f v := by
  rw [nondesc, Finset.prod_mul_prod_compl]

omit [DecidableRel G.Adj] in
/-- `∏_{v ∈ descM} f v = f m · ∏_{v ∈ desc} f v`.
Source: none: infrastructure
Kind: L -/
theorem prod_descM (hG : G.IsAcyclic) (m : V) (f : V → ℝ) :
    ∏ v ∈ descM G m, f v = f m * ∏ v ∈ desc G m, f v := by
  rw [descM, Finset.prod_insert (m_notMem_desc hG m)]

omit [DecidableRel G.Adj] in
/-- `∏_{v ≠ m} f v = (∏_{v ∈ nondesc} f v) · ∏_{v ∈ desc} f v`.
Source: none: infrastructure
Kind: L -/
theorem prod_erase_eq_nondesc_mul_desc (hG : G.IsAcyclic) (m : V) (f : V → ℝ) :
    ∏ v ∈ Finset.univ.erase m, f v = (∏ v ∈ nondesc G m, f v) * ∏ v ∈ desc G m, f v := by
  have hunion : Finset.univ.erase m = nondesc G m ∪ desc G m := by
    ext u
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, mem_nondesc,
      mem_desc]
    constructor
    · intro h; by_cases ha : G.IsAncestor m u
      · exact Or.inr ha
      · exact Or.inl ⟨h, ha⟩
    · rintro (⟨h, -⟩ | h)
      · exact h
      · rintro rfl; exact hG _ h
  have hdisj : Disjoint (nondesc G m) (desc G m) := by
    rw [Finset.disjoint_left]
    intro u hu hd
    rw [mem_nondesc] at hu; rw [mem_desc] at hd
    exact hu.2 hd
  rw [hunion, Finset.prod_union hdisj]

end desc

/-! ## Causal structures -/

section structure_

variable {V : Type} [Fintype V] [DecidableEq V] (Val : V → Type) [∀ v, Fintype (Val v)]
  [∀ v, DecidableEq (Val v)]

/-- **A latent-free causal structure** (Definition 24): an acyclic DAG on the coordinates with a
CPD family. It is *a structure for* `P` when `IsFor` holds — exactly `FactorizesOverDAG`'s
witness, kept explicit (the CPD at a `P`-null parent configuration is not determined by `P`).
Source: [[learning-cdt-renderings]] Definition 24 ("a DAG `G` on the coordinates … whose
observable marginal is `P_s`"); FAF `FactorizesOverDAG` (`BayesNet.lean:370`)
Kind: D
Fidelity: exact for the latent-free case (latents are `Latent.lean`'s marginal construction) -/
structure CausalStructure where
  /-- The DAG. -/
  G : Digraph V
  /-- Decidable adjacency (needed for `Digraph.parents`). -/
  [decAdj : DecidableRel G.Adj]
  /-- Acyclicity. -/
  acyclic : G.IsAcyclic
  /-- The conditional probability distributions, one per node and parent configuration. -/
  φ : CPD (G := G) (Val := Val)

attribute [instance] CausalStructure.decAdj

variable {Val}

namespace CausalStructure

/-- **Markov compatibility, unpacked**: `Γ` is a structure for `P` iff `P` factorizes over `Γ.G`
through `Γ.φ`. This is `FactorizesOverDAG Γ.G Val P` with its witness named.
Source: FAF `FactorizesOverDAG` (`BayesNet.lean:370`); [[learning-cdt-renderings]] Theorem 3
("`P_s` Markov to `G`")
Kind: D
Fidelity: exact -/
def IsFor (Γ : CausalStructure Val) (P : Distr (Pt Val)) : Prop :=
  ∀ x, P.mass x = ∏ v, cpdFactor Γ.φ v x

/-- `IsFor` gives FAF's `FactorizesOverDAG`. Source: none: infrastructure. Kind: L -/
theorem IsFor.factorizesOverDAG {Γ : CausalStructure Val} {P : Distr (Pt Val)} (h : Γ.IsFor P) :
    FactorizesOverDAG Γ.G Val P :=
  ⟨Γ.φ, h⟩

/-- FAF's `FactorizesOverDAG` gives a causal structure (the DAG with the witnessing CPD).
Source: none: infrastructure
Kind: L -/
theorem exists_isFor_of_factorizesOverDAG (G : Digraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) {P : Distr (Pt Val)} (h : FactorizesOverDAG G Val P) :
    ∃ Γ : CausalStructure Val, Γ.G = G ∧ Γ.IsFor P := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨⟨G, hG, φ⟩, rfl, hφ⟩

/-- The truncated law of a structure at `do(m := a)`.
Source: [[learning-cdt-renderings]] Definition 24
Kind: D -/
noncomputable def truncate [∀ v, Nonempty (Val v)] (Γ : CausalStructure Val) (m : V)
    (a : Val m) : Distr (Pt Val) :=
  DpCausalConsist.truncate Γ.acyclic Γ.φ m a

/-- **Temporal** (Definition 26): the parents of the act are among the pre-query coordinates
`V₀` (given as a set of coordinates).
Source: [[learning-cdt-renderings]] Definition 26 ("temporal if … `pa_G(m) ⊆ V₀`"); mandate §3.4
Kind: D
Fidelity: exact for the parent clause; the mandate's stronger reading (also `pa(v) ⊆ V₀ ∪ {m}`
for post-query `v`) is `TemporalStrong` -/
def Temporal (Γ : CausalStructure Val) (m : V) (V₀ : Finset V) : Prop :=
  Γ.G.parents m ⊆ V₀

/-- The mandate's stronger "temporal" (§6.13): `pa(m) ⊆ V₀`, pre-query coordinates have no
post-query parents, and `m ∉ V₀` — exactly the three conjuncts below (audit r2 fid N7: an earlier
docstring claimed a vacuous fourth clause). The mandate's T3(C) reading adds `pa(v) ⊆ V₀ ∪ {m}`
for post-query `v` (no post-query parents); neither form is consumed by a theorem (finding F10).
Source: mandate T3(C) and §6.13 (the definition Theorem 3's (C) check needs)
Kind: D -/
def TemporalStrong (Γ : CausalStructure Val) (m : V) (V₀ : Finset V) : Prop :=
  Γ.G.parents m ⊆ V₀ ∧ (∀ v ∈ V₀, Γ.G.parents v ⊆ V₀) ∧ m ∉ V₀

end CausalStructure

end structure_

/-! ## Pearl's invariance and the local Markov identity -/

section pearl

variable {V : Type} [Fintype V] [DecidableEq V] {Val : V → Type} [∀ v, Fintype (Val v)]
  [∀ v, DecidableEq (Val v)] [∀ v, Nonempty (Val v)] {G : Digraph V} [DecidableRel G.Adj]

/-- **The key identity behind Pearl's invariance and the local Markov property**: for a weight `w`
reading only the non-descendant coordinates of `m` and a base point with `x₀ m = a`,
`∑_x w(x) ∏_{v ∈ {m} ∪ desc} φ_v(x) = ∑_x w(x) [x_m = a] ∏_{v ∈ desc} φ_v(x)` — the factor of `m`
and the descendants' factors both integrate out to one, whether or not `x_m` is pinned.
Source: none: infrastructure
Kind: P
Hyps: (a) `G` acyclic; `w` reads only `nondesc G m` -/
theorem sum_descM_eq_sum_desc_pin (hG : G.IsAcyclic) (φ : CPD (G := G) (Val := Val)) (m : V)
    (a : Val m) (w : Pt Val → ℝ) (hw : ∀ x y, (∀ u ∈ nondesc G m, y u = x u) → w y = w x) :
    ∑ x, w x * ∏ v ∈ descM G m, cpdFactor φ v x
      = ∑ x, (w x * if x m = a then 1 else 0) * ∏ v ∈ desc G m, cpdFactor φ v x := by
  obtain ⟨z⟩ : Nonempty (Pt Val) := inferInstance
  set x₀ : Pt Val := Function.update z m a with hx₀
  have hx₀m : x₀ m = a := by rw [hx₀, Function.update_self]
  rw [sum_out hG φ (descM G m) x₀ w (fun x y hy => hw x y fun u hu =>
    hy u (notMem_descM_iff.mpr hu))]
  rw [sum_out hG φ (desc G m) x₀ (fun x => w x * if x m = a then 1 else 0) ?_]
  · refine Finset.sum_congr rfl fun x _ => ?_
    have hiff : (∀ u ∈ descM G m, x u = x₀ u) ↔ ((∀ u ∈ desc G m, x u = x₀ u) ∧ x m = a) := by
      constructor
      · intro h
        refine ⟨fun u hu => h u (Finset.mem_insert_of_mem hu), ?_⟩
        rw [← hx₀m]; exact h m (Finset.mem_insert_self _ _)
      · rintro ⟨h1, h2⟩ u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · rw [h2, hx₀m]
        · exact h1 u hu
    rw [if_congr hiff rfl rfl]
    by_cases h1 : ∀ u ∈ desc G m, x u = x₀ u <;> by_cases h2 : x m = a <;> simp [h1, h2]
  · intro x y hy
    have hym : y m = x m := hy m (m_notMem_desc hG m)
    rw [hym, hw x y fun u hu => hy u (fun hd => (mem_nondesc.mp hu).2 (mem_desc.mp hd))]

/-- **An event is in the fixed algebra `𝓔₀^G`** iff it is a union of fibers of the projection to
the non-descendants of `m`: membership depends only on the non-descendant coordinates. Defined
by the *graph*, not by "the events on which truncation and `P` agree" (mandate §7's trap).
Source: [[learning-cdt-renderings]] Definition 24 (`𝓔₀^G := ⟨nondesc_G(m)⟩`)
Kind: D
Fidelity: exact -/
def InFixedAlgebra (G : Digraph V) (m : V) (X : Finset (Pt Val)) : Prop :=
  ∀ x y : Pt Val, (∀ u ∈ nondesc G m, x u = y u) → (x ∈ X ↔ y ∈ X)

/-- **Pearl's invariance (T1, dp-core-2-021(a))**: for every latent-free structure and every act,
the truncated law agrees with `P` on every event of the fixed algebra `𝓔₀^G`.
Source: [[learning-cdt-renderings]] Definition 24 ("on which `cf^G_s` is non-responsive");
"Non-responsiveness: form, not content" ("Every interventional supposition is non-responsive on
the algebra of the act's non-descendants"); mandate T1
Kind: P
Fidelity: exact
Hyps: (a) `G` acyclic; (a) `φ` factorizes `P` (Markov compatibility, `IsFor`); (a) `X ∈ 𝓔₀^G` -/
theorem truncate_prob_eq_of_inFixedAlgebra (hG : G.IsAcyclic) (φ : CPD (G := G) (Val := Val))
    {P : Distr (Pt Val)} (hφ : ∀ x, P.mass x = ∏ v, cpdFactor φ v x) (m : V) (a : Val m)
    (X : Finset (Pt Val)) (hX : InFixedAlgebra G m X) :
    (truncate hG φ m a).prob ↑X = P.prob ↑X := by
  have hL : (truncate hG φ m a).prob ↑X =
      ∑ x, ((if x ∈ X then (1 : ℝ) else 0) * ∏ v ∈ nondesc G m, cpdFactor φ v x)
        * (if x m = a then (1 : ℝ) else 0) * ∏ v ∈ desc G m, cpdFactor φ v x := by
    rw [truncate_prob_eq_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [prod_erase_eq_nondesc_mul_desc hG]
    by_cases hX' : x ∈ X <;> by_cases hm : x m = a <;> simp [hX', hm]
  have hR : P.prob ↑X =
      ∑ x, ((if x ∈ X then (1 : ℝ) else 0) * ∏ v ∈ nondesc G m, cpdFactor φ v x)
        * ∏ v ∈ descM G m, cpdFactor φ v x := by
    rw [prob_eq_sum_ite]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hφ x, prod_univ_eq_descM_mul_nondesc (G := G) m]
    by_cases hX' : x ∈ X <;> simp [hX', mul_comm]
  have hw : ∀ x y : Pt Val, (∀ u ∈ nondesc G m, y u = x u) →
      ((if y ∈ X then (1 : ℝ) else 0) * ∏ v ∈ nondesc G m, cpdFactor φ v y)
        = ((if x ∈ X then (1 : ℝ) else 0) * ∏ v ∈ nondesc G m, cpdFactor φ v x) := by
    intro x y hy
    rw [if_congr (hX y x fun u hu => hy u hu) rfl rfl]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    exact cpdFactor_congr φ v (fun u hu => hy u (parents_subset_nondesc hv hu)) (hy v hv)
  have key := sum_descM_eq_sum_desc_pin hG φ m a
    (fun x => (if x ∈ X then (1 : ℝ) else 0) * ∏ v ∈ nondesc G m, cpdFactor φ v x) hw
  rw [hL, hR, key]

/-- **The local Markov identity at a node** (an FAF API request — FAF proves the conditional
form only for `τ`-images, privately): for `φ` factorizing `P`, every node `v`, value `b` and
parent configuration `c`, `P(x_v = b ∧ x_pa(v) = c) = φ_v(c)(b) · P(x_pa(v) = c)`. Multiplicative,
so it holds at null parent cells too (both sides `0`); at a positive cell it says
`P(x_v = b | x_pa(v) = c) = φ_v(c)(b)`.
Source: Koller–Friedman's local Markov property; FAF `BayesNet.condProb_tau_eq` (private);
mandate T2(ii) ("conclude by (i) plus the null-cell clause")
Kind: P
Fidelity: exact
Hyps: (a) `G` acyclic; (a) `φ` factorizes `P` -/
theorem prob_val_inter_parentCell (hG : G.IsAcyclic) (φ : CPD (G := G) (Val := Val))
    {P : Distr (Pt Val)} (hφ : ∀ x, P.mass x = ∏ v, cpdFactor φ v x) (v : V) (b : Val v)
    (c : ParentVals G Val v) :
    P.prob {x | x v = b ∧ parentConfig G Val x v = c}
      = (φ v c).mass b * P.prob {x | parentConfig G Val x v = c} := by
  have hw : ∀ x y : Pt Val, (∀ u ∈ nondesc G v, y u = x u) →
      ((if parentConfig G Val y v = c then (1 : ℝ) else 0) * ∏ u ∈ nondesc G v, cpdFactor φ u y)
      = ((if parentConfig G Val x v = c then 1 else 0) * ∏ u ∈ nondesc G v, cpdFactor φ u x) := by
    intro x y hy
    rw [parentConfig_congr v (fun u hu => hy u (parents_m_subset_nondesc hG v hu))]
    congr 1
    refine Finset.prod_congr rfl fun u hu => ?_
    exact cpdFactor_congr φ u (fun u' hu' => hy u' (parents_subset_nondesc hu hu')) (hy u hu)
  have hN : P.prob {x | x v = b ∧ parentConfig G Val x v = c} =
      (φ v c).mass b * ∑ x, ((if parentConfig G Val x v = c then (1 : ℝ) else 0)
        * ∏ u ∈ nondesc G v, cpdFactor φ u x) * (if x v = b then 1 else 0)
        * ∏ u ∈ desc G v, cpdFactor φ u x := by
    rw [prob_setOf_eq_sum_ite, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hφ x, prod_univ_eq_descM_mul_nondesc (G := G) v, prod_descM hG v]
    by_cases h1 : x v = b <;> by_cases h2 : parentConfig G Val x v = c
    · have hm : cpdFactor φ v x = (φ v c).mass b := by
        unfold cpdFactor; rw [h2, h1]
      rw [if_pos ⟨h1, h2⟩, if_pos h2, if_pos h1, hm]
      ring
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  have hD : P.prob {x | parentConfig G Val x v = c} =
      ∑ x, ((if parentConfig G Val x v = c then (1 : ℝ) else 0)
        * ∏ u ∈ nondesc G v, cpdFactor φ u x) * ∏ u ∈ descM G v, cpdFactor φ u x := by
    rw [prob_setOf_eq_sum_ite]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hφ x, prod_univ_eq_descM_mul_nondesc (G := G) v]
    by_cases h2 : parentConfig G Val x v = c <;> simp [h2, mul_comm]
  rw [hN, hD, sum_descM_eq_sum_desc_pin hG φ v b _ hw]

/-- The parent cells of `v` are `P`-measurable pieces of the non-descendant coordinates; the
conditional form of `prob_val_inter_parentCell` at a positive cell.
Source: none: infrastructure
Kind: L -/
theorem condProb_val_parentCell (hG : G.IsAcyclic) (φ : CPD (G := G) (Val := Val))
    {P : Distr (Pt Val)} (hφ : ∀ x, P.mass x = ∏ v, cpdFactor φ v x) (v : V) (b : Val v)
    (c : ParentVals G Val v) (hc : 0 < P.prob {x | parentConfig G Val x v = c}) :
    P.condProb {x | x v = b} {x | parentConfig G Val x v = c} = (φ v c).mass b := by
  unfold Distr.condProb
  rw [div_eq_iff hc.ne']
  have : ({x : Pt Val | x v = b} ∩ {x | parentConfig G Val x v = c})
      = {x | x v = b ∧ parentConfig G Val x v = c} := by
    ext x; simp
  rw [this, prob_val_inter_parentCell hG φ hφ v b c]

end pearl

section cellpos

variable {V : Type} [Fintype V] [DecidableEq V] {Val : V → Type} [∀ v, Fintype (Val v)]
  [∀ v, DecidableEq (Val v)] [∀ v, Nonempty (Val v)] {G : Digraph V} [DecidableRel G.Adj]

/-- **A point of positive truncated mass sits in a `P`-positive parent cell of `m`**: if
`∏_{v ≠ m} φ_v(x) > 0` then `P(x_pa(m) = x_pa(m)) > 0`. Reason: `P(pa = c) ≥ ∑_{y = x on nondesc} P(y)
= ∏_{v ∈ nondesc} φ_v(x) · 1 > 0` (the factors of `m` and its descendants sum out). So the
null-cell freedom of the CPD never reaches the truncated support of a positive act: the wiki's
"almost surely" in Theorem 3(i) is harmless there (finding §6.1, resolved).
Source: mandate T2(ii) ("which is where you discover whether (ii) needs strict positivity of
`(s d).toDistr` on the parent cells" — it does not)
Kind: P
Hyps: (a) `G` acyclic; (a) `φ` factorizes `P` -/
theorem prob_parentCell_pos_of_prod_pos (hG : G.IsAcyclic) (φ : CPD (G := G) (Val := Val))
    {P : Distr (Pt Val)} (hφ : ∀ x, P.mass x = ∏ v, cpdFactor φ v x) (m : V) (x : Pt Val)
    (hT : 0 < ∏ v ∈ Finset.univ.erase m, cpdFactor φ v x) :
    0 < P.prob {y | parentConfig G Val y m = parentConfig G Val x m} := by
  have hN : 0 < ∏ v ∈ nondesc G m, cpdFactor φ v x := by
    apply Finset.prod_pos
    intro v hv
    rcases (cpdFactor_nonneg φ v x).lt_or_eq with h | h
    · exact h
    · exfalso
      have hvm : v ∈ Finset.univ.erase m :=
        Finset.mem_erase.mpr ⟨(mem_nondesc.mp hv).1, Finset.mem_univ _⟩
      rw [Finset.prod_eq_zero hvm h.symm] at hT
      exact lt_irrefl _ hT
  have hsum : ∑ y : Pt Val, (if ∀ u ∉ descM G m, y u = x u then
      ∏ v ∈ descM G m, cpdFactor φ v y else 0) = 1 := sum_cpd_prod_eq_one hG φ (descM G m) x
  have hle : (∏ v ∈ nondesc G m, cpdFactor φ v x)
      ≤ P.prob {y | parentConfig G Val y m = parentConfig G Val x m} := by
    rw [prob_setOf_eq_sum_ite]
    calc (∏ v ∈ nondesc G m, cpdFactor φ v x)
        = (∏ v ∈ nondesc G m, cpdFactor φ v x) * ∑ y : Pt Val, (if ∀ u ∉ descM G m, y u = x u then
            ∏ v ∈ descM G m, cpdFactor φ v y else 0) := by rw [hsum, mul_one]
      _ = ∑ y : Pt Val, (if ∀ u ∉ descM G m, y u = x u then P.mass y else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          split_ifs with hy
          · rw [hφ y, prod_univ_eq_descM_mul_nondesc (G := G) m, mul_comm]
            congr 1
            refine Finset.prod_congr rfl fun v hv => ?_
            refine cpdFactor_congr φ v (fun u hu => ?_) ?_
            · exact (hy u (notMem_descM_iff.mpr (parents_subset_nondesc hv hu))).symm
            · exact (hy v (notMem_descM_iff.mpr hv)).symm
          · simp
      _ ≤ ∑ y : Pt Val, (if parentConfig G Val y m = parentConfig G Val x m then P.mass y else 0) := by
          apply Finset.sum_le_sum
          intro y _
          split_ifs with h1 h2
          · exact le_rfl
          · exfalso
            apply h2
            exact parentConfig_congr m fun u hu =>
              h1 u (notMem_descM_iff.mpr (parents_m_subset_nondesc hG m hu))
          · exact P.nonneg y
          · exact le_rfl
  exact lt_of_lt_of_le hN hle

end cellpos

/-! ## Theorem 3(i) -/

section thm3i

variable {V : Type} [Fintype V] [DecidableEq V] {Val : V → Type} [∀ v, Fintype (Val v)]
  [∀ v, DecidableEq (Val v)] [∀ v, Nonempty (Val v)] {G : Digraph V} [DecidableRel G.Adj]

/-- **Theorem 3(i), the algebraic iff about one CPD**: for `φ` factorizing `P` and an act `a`
of positive probability, the truncated law `do(m := a)` equals `P(· | x_m = a)` iff at every
point `x` with `x_m = a` carrying truncated mass (`∏_{v ≠ m} φ_v(x) > 0`), the act's CPD factor
equals the act's marginal: `φ_m(x_pa(m))(a) = P(x_m = a)`. The right side is a statement about
`φ_m` alone — not about Markov compatibility, which is the hypothesis. The wiki's "almost surely"
is rendered as "on the support of the truncated law" (mandate §6.1): the equality is pointwise,
and it can bind at `P`-null parent cells, where the CPD is free.
Source: [[learning-cdt-renderings]] Theorem 3(i) ("`P^{G,a} = P_{s_d}(· | a)` on all of `𝓔` iff
`P_{s_d}(a | pa_G(m)) = P_{s_d}(a)` almost surely"), proof ("they agree at every `v` iff …")
Kind: P
Fidelity: variant: "a.s." read on the truncated support (the exact form); the state `s_d` is any
`Distr` here — recording and calibration enter in `thm3_ii`
Hyps: (a) `φ` factorizes `P`; (a) `0 < P(x_m = a)`; (a) `G` acyclic -/
theorem thm3_i (hG : G.IsAcyclic) (φ : CPD (G := G) (Val := Val)) {P : Distr (Pt Val)}
    (hφ : ∀ x, P.mass x = ∏ v, cpdFactor φ v x) (m : V) (a : Val m)
    (ha : 0 < P.prob {x | x m = a}) :
    truncate hG φ m a = condDistr P {x | x m = a} ha ↔
      ∀ x : Pt Val, x m = a → 0 < ∏ v ∈ Finset.univ.erase m, cpdFactor φ v x →
        (φ m (parentConfig G Val x m)).mass a = P.prob {x | x m = a} := by
  have hmass : ∀ x : Pt Val, x m = a →
      P.mass x = (φ m (parentConfig G Val x m)).mass a
        * ∏ v ∈ Finset.univ.erase m, cpdFactor φ v x := by
    intro x hx
    rw [hφ x, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m)]
    unfold cpdFactor
    rw [hx]
  rw [distr_ext_iff]
  constructor
  · intro h x hx hT
    have := h x
    rw [truncate_mass, condDistr_mass, if_pos hx,
      Set.indicator_of_mem (show x ∈ {x | x m = a} from hx), hmass x hx, eq_div_iff ha.ne',
      mul_comm ((φ m (parentConfig G Val x m)).mass a)] at this
    exact (mul_left_cancel₀ hT.ne' this).symm
  · intro h x
    rw [truncate_mass, condDistr_mass]
    by_cases hx : x m = a
    · rw [if_pos hx, Set.indicator_of_mem (show x ∈ {x | x m = a} from hx), hmass x hx]
      rcases (Finset.prod_nonneg fun v _ => cpdFactor_nonneg φ v x :
          (0 : ℝ) ≤ ∏ v ∈ Finset.univ.erase m, cpdFactor φ v x).lt_or_eq with hT | hT
      · rw [h x hx hT]
        field_simp
      · rw [← hT]; simp
    · rw [if_neg hx, Set.indicator_of_notMem (show x ∉ {x | x m = a} from hx)]
      simp

/-- **Theorem 3(i) for a strictly positive state**: every parent cell is positive, so the CPD is
the conditional and the right side of `thm3_i` is the wiki's own condition
`P(x_m = a | x_pa(m)) = P(x_m = a)` at every parent configuration — `CondIndepEventVar`-shaped
independence of the act from its parent configuration.
Source: [[learning-cdt-renderings]] Theorem 3(i); mandate T2(i) (`thm3_i_of_strictlyPositive`)
Kind: C
Fidelity: exact (the "a.s." reads on all of `Pt Val`, every point being positive)
Hyps: (a) `φ` factorizes `P`; (a) `P` strictly positive; (a) `G` acyclic -/
theorem thm3_i_of_strictlyPositive (hG : G.IsAcyclic) (φ : CPD (G := G) (Val := Val))
    {P : Distr (Pt Val)} (hφ : ∀ x, P.mass x = ∏ v, cpdFactor φ v x) (hP : P.StrictlyPositive)
    (m : V) (a : Val m) (ha : 0 < P.prob {x | x m = a}) :
    truncate hG φ m a = condDistr P {x | x m = a} ha ↔
      ∀ x : Pt Val, P.condProb {y | y m = a} {y | parentConfig G Val y m = parentConfig G Val x m}
        = P.prob {y | y m = a} := by
  rw [thm3_i hG φ hφ m a ha]
  have hcell : ∀ x : Pt Val, 0 < P.prob {y | parentConfig G Val y m = parentConfig G Val x m} := by
    intro x
    rw [P.prob_pos_iff]
    exact ⟨x, rfl, hP x⟩
  have hT : ∀ x : Pt Val, 0 < ∏ v ∈ Finset.univ.erase m, cpdFactor φ v x := by
    intro x
    have h1 : 0 < P.mass x := hP x
    rw [hφ x, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m)] at h1
    exact pos_of_mul_pos_right h1 (cpdFactor_nonneg φ m x)
  constructor
  · intro h x
    obtain ⟨z⟩ : Nonempty (Pt Val) := inferInstance
    set x' : Pt Val := Function.update x m a with hx'
    have hx'm : x' m = a := by rw [hx', Function.update_self]
    have hpc : parentConfig G Val x' m = parentConfig G Val x m := by
      refine parentConfig_congr m fun u hu => Function.update_of_ne ?_ a x
      intro h'
      rw [h'] at hu
      exact Digraph.notMem_parents_self hG m hu
    rw [condProb_val_parentCell hG φ hφ m a _ (hcell x), ← hpc]
    exact h x' hx'm (hT x')
  · intro h x hx _
    rw [← condProb_val_parentCell hG φ hφ m a _ (hcell x)]
    exact h x

end thm3i

end Cleanroom.Decision.DpCausalConsist
