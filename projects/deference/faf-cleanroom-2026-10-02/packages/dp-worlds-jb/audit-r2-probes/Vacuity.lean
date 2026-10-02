import Cleanroom.Decision.DpWorldsJb
import Mathlib.Data.Finset.Grade

/-!
# dp-worlds-jb — audit round 2, adversarial lens: vacuity and witness probes

Not imported by the library. Each probe is named `probeX_…` and its docstring says what it shows.
The companion `NoProbCountable.lean` holds the round's main probe (T6's witness annihilates
probabilities too).

* **Probe A (T6 vs T7: one designation, two algebras).** On a σ-algebra `MSet X` the annihilation
  designation `Jω` *is* the Dirac designation `Jσ` (every countable family has an infimum
  there). So Appendix A's contrast — no worlds on the measure algebra, Dirac worlds on
  `Borel(X)` — is a contrast between algebras under the *same* designation, and T6's hypotheses
  exclude `Borel(ℝ)` for the right reason: Lebesgue measure is not strictly positive there
  (`{0} ≠ ⊥` is null), while `Jω`-worlds exist on `Set ℕ` and on `MSet ℝ` (so
  `no_world_of_halving`'s conclusion is not automatic on infinite or uncountable algebras).
* **Probe B (`worldJω_equiv_atoms`, an N+ instance).** The ledger's witness cell for the
  countable equivalence is N− (`Dy`, both sides empty). `Finset (Fin 2)` is countable with atoms
  `{0}`, `{1}`: both sides are inhabited, the world at `{0}` holds `{0}` and not `{1}`, and the
  equivalence sends it back to the atom `{0}`.
* **Probe C (T4: the `null_zero` restriction in `jbVec_equiv` is load-bearing).** A finitely
  additive `𝒥 : Finset (Fin 2) → ℝ²` with `𝒥.1 = δ_1` but `𝒥 {0} = (0, 1)` is a `JBVec` outside
  the subtype; its `toJB` is a v2 pair (`V {1} = 0`, `V ⊤ = 1`) that no null-tolerant pair
  restricts to — so "any finitely additive vector measure with a probability first coordinate"
  is *not* equivalent to JB structures under the slide's own convention either; the side
  condition `𝒥(N).2 = 0` (automatic for a `𝒥` *built* from `(P, V)`) is needed for the converse.
* **Probe D (S2: a rotation with `c ≠ 0`).** The ledger's witness cell for `bolkerTransform` /
  `probability_component_not_invariant` names only the identity (`c = 0`). On the two-atom
  algebra with `P` uniform and `V {1} = 1`, `V {0} = 0`, the parameters `a = 1, b = 0, c = 1,
  d = 1/2` are admissible and move `P {0}` from `1/2` to `1/4`: the headline's content on a
  concrete non-trivial rotation.
* **Probe E (T3(iii) at the coarsest algebra).** With `Ω = Unit` (one atom) and a two-valued
  utility on `W = Bool`, rigidity is *not* faithful for all pairs — the theorem's necessity
  direction at the extreme coarse case.
-/

namespace Cleanroom.Decision.DpWorldsJb.AuditR2

open Cleanroom.Decision.DpWorldsJb Finset

noncomputable section

open Classical

/-! ## Probe A -/

/-- On a σ-algebra the annihilation designation `Jω` and the Dirac designation `Jσ` coincide. -/
theorem probeA_Jω_eq_Jσ (X : Type*) [MeasurableSpace X] : (Jω (MSet X)).1 = (Jσ X).1 := by
  ext D
  constructor
  · rintro ⟨hc, -⟩
    exact hc
  · intro hc
    exact ⟨hc, _, isGLB_sInter D hc⟩

/-- `Jω`-worlds exist on `Set ℕ` (the point worlds) and on `Borel(ℝ)` (the Dirac worlds). -/
theorem probeA_Jω_worlds_exist :
    Nonempty (World (Jω (Set ℕ))) ∧ Nonempty (World (Jω (MSet ℝ))) :=
  ⟨⟨principalWorld _ 0⟩, ⟨diracWorld _ 0⟩⟩

/-- Lebesgue measure on `Borel(ℝ)`, read at `J = ∅`. -/
def lebesgueEmpty : Prob (∅ : Designation (MSet ℝ)) where
  P := lebesgueProb.P
  nonneg := lebesgueProb.nonneg
  top := lebesgueProb.top
  add := lebesgueProb.add
  cont _ hD := hD.elim

/-- Lebesgue measure is not strictly positive on `Borel(ℝ)`: `{0} ≠ ⊥` is null. So T6's
hypotheses exclude the Borel algebra (where Dirac worlds live) for the right reason. -/
theorem probeA_lebesgue_not_strictlyPositive : ¬ StrictlyPositive lebesgueEmpty := by
  intro h
  have hne : singletonM (0 : ℝ) ≠ ⊥ := fun h0 =>
    Set.singleton_ne_empty (0 : ℝ) (congrArg Subtype.val h0)
  have := h _ hne
  change (0 : ℝ) < lebesgueProb.P (singletonM 0) at this
  rw [lebesgueProb_singleton] at this
  exact lt_irrefl _ this

/-! ## Probe B -/

/-- `Finset (Fin 2)` with `Jω`: both sides of `worldJω_equiv_atoms` are inhabited; the world at
the atom `{0}` holds `{0}` and not `{1}`; the equivalence returns the atom. -/
theorem probeB_finite_atoms :
    Nonempty (World (Jω (Finset (Fin 2)))) ∧
    (({0} : Finset (Fin 2)) ∈
        (worldJω_equiv_atoms (E := Finset (Fin 2))).symm ⟨{0}, Finset.isAtom_singleton 0⟩) ∧
    (({1} : Finset (Fin 2)) ∉
        (worldJω_equiv_atoms (E := Finset (Fin 2))).symm ⟨{0}, Finset.isAtom_singleton 0⟩) ∧
    ((worldJω_equiv_atoms (E := Finset (Fin 2)))
        ((worldJω_equiv_atoms (E := Finset (Fin 2))).symm ⟨{0}, Finset.isAtom_singleton 0⟩)).1
      = {0} := by
  refine ⟨⟨atomWorld _ {0} (Finset.isAtom_singleton 0)⟩, ?_, ?_, ?_⟩
  · show ({0} : Finset (Fin 2)) ≤ {0}
    exact le_rfl
  · show ¬ ({0} : Finset (Fin 2)) ≤ {1}
    decide
  · rw [Equiv.apply_symm_apply]

/-! ## Probe C -/

/-- The indicator of `i ∈ s`, as a real. -/
def ind (i : Fin 2) (s : Finset (Fin 2)) : ℝ := if i ∈ s then 1 else 0

theorem ind_add (i : Fin 2) (s t : Finset (Fin 2)) (h : Disjoint s t) :
    ind i (s ⊔ t) = ind i s + ind i t := by
  unfold ind
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t
  · exact absurd ht (Finset.disjoint_left.1 h hs)
  · simp [hs, ht]
  · simp [hs, ht]
  · simp [hs, ht]

/-- `𝒥 s := (𝟙[1 ∈ s], 𝟙[0 ∈ s])`: finitely additive, first coordinate `δ_1`, but `𝒥 {0} = (0, 1)`
— a `JBVec` violating `null_zero`. -/
def probeC_vec : JBVec (Finset (Fin 2)) where
  v s := (ind 1 s, ind 0 s)
  add s t h := Prod.ext (ind_add 1 s t h) (ind_add 0 s t h)
  nonneg s := by
    show 0 ≤ ind 1 s
    unfold ind
    split_ifs <;> norm_num
  top := by
    show ind 1 ⊤ = 1
    simp [ind]

theorem probeC_null_zero_fails : (probeC_vec.v {0}).1 = 0 ∧ (probeC_vec.v {0}).2 = 1 := by
  constructor
  · show ind 1 {0} = 0
    simp [ind]
  · show ind 0 {0} = 1
    simp [ind]

/-- Its `toJB` (`P = δ_1`, `V {1} = 0`, `V ⊤ = 1`) is a v2 pair to which no null-tolerant pair
restricts: the null-tolerant axiom at `({0}, {1})` forces `V ⊤ = V {1}`. So `jbVec_equiv`'s
subtype is not the whole of `JBVec`, and the slide's converse direction genuinely needs
`𝒥(N).2 = 0`. -/
theorem probeC_toJB_not_null_tolerant :
    ¬ ∃ q : JBPairNT (Finset (Fin 2)), q.P = probeC_vec.toProb ∧
      ∀ X (hq : 0 < q.P.P X) (hw : 0 < probeC_vec.toProb.P X),
        q.V ⟨X, hq⟩ = probeC_vec.toJB.V ⟨X, hw⟩ := by
  rintro ⟨q, hP, hV⟩
  have hd : Disjoint ({0} : Finset (Fin 2)) {1} := by decide
  have e : ({0} : Finset (Fin 2)) ⊔ {1} = Finset.univ := by decide
  have i0 : ind 1 {0} = 0 := by simp [ind]
  have i1 : ind 1 {1} = 1 := by simp [ind]
  have iu : ind 1 Finset.univ = 1 := by simp [ind]
  have p0 : q.P.P {0} = 0 := by rw [hP]; exact i0
  have p1 : 0 < q.P.P {1} := by rw [hP]; show (0 : ℝ) < ind 1 {1}; rw [i1]; norm_num
  have pu : 0 < q.P.P Finset.univ := by
    rw [hP]; show (0 : ℝ) < ind 1 Finset.univ; rw [iu]; norm_num
  have w1 : 0 < probeC_vec.toProb.P {1} := by show (0 : ℝ) < ind 1 {1}; rw [i1]; norm_num
  have wu : 0 < probeC_vec.toProb.P Finset.univ := by
    show (0 : ℝ) < ind 1 Finset.univ; rw [iu]; norm_num
  have key := q.avgNT {0} {1} hd
  rw [e, pvFun_of_null _ _ p0, zero_add, pvFun_of_pos _ _ p1, pvFun_of_pos _ _ pu] at key
  rw [hV _ pu wu, hV _ p1 w1] at key
  have v1 : probeC_vec.toJB.V ⟨{1}, w1⟩ = 0 := by
    rw [JBVec.toJB_V]
    show ind 0 {1} / ind 1 {1} = 0
    simp [ind]
  have vu : probeC_vec.toJB.V ⟨Finset.univ, wu⟩ = 1 := by
    rw [JBVec.toJB_V]
    show ind 0 Finset.univ / ind 1 Finset.univ = 1
    simp [ind]
  have qu : q.P.P Finset.univ = 1 := by rw [hP]; exact iu
  have q1 : q.P.P {1} = 1 := by rw [hP]; exact i1
  rw [v1, vu, qu, q1] at key
  norm_num at key

/-! ## Probe D -/

/-- The uniform distribution on `Fin 2`. -/
def unif2 : Dist (Fin 2) where
  p _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by simp

/-- Atom values `v 0 = 0`, `v 1 = 1`. -/
def val2 : Fin 2 → ℝ := fun i => if i = 1 then 1 else 0

theorem unif2_pos (X : Finset (Fin 2)) (hX : X ≠ ⊥) : 0 < (unif2.toJBPair val2).P.P X := by
  show (0 : ℝ) < mass unif2.p X
  unfold mass
  show (0 : ℝ) < ∑ _w ∈ X, (1 / 2 : ℝ)
  rw [Finset.sum_const, nsmul_eq_mul]
  have hne : X.Nonempty := Finset.nonempty_iff_ne_empty.2 hX
  have := Finset.card_pos.2 hne
  positivity

/-- The two-atom null-tolerant pair `(uniform, v)` with `V {0} = 0`, `V {1} = 1`, `V ⊤ = 1/2`. -/
def pair2 : JBPairNT (Finset (Fin 2)) := (unif2.toJBPair val2).toNT unif2_pos

theorem pair2_V (X : Finset (Fin 2)) (h : 0 < pair2.P.P X) :
    pair2.V ⟨X, h⟩ = condExp unif2.p val2 X := rfl

theorem pair2_V_top : pair2.V ⟨⊤, by rw [pair2.P.top]; exact one_pos⟩ = 1 / 2 := by
  rw [pair2_V]
  unfold condExp mass
  simp [unif2, val2]

theorem pair2_V_nonneg (X : Finset (Fin 2)) (h : 0 < pair2.P.P X) : 0 ≤ pair2.V ⟨X, h⟩ := by
  rw [pair2_V]
  unfold condExp
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro w _
    apply mul_nonneg (unif2.nonneg w)
    unfold val2
    split_ifs <;> norm_num
  · exact mass_nonneg unif2.nonneg X

/-- `a = 1, b = 0, c = 1, d = 1/2` is admissible for `pair2`: `V + 1/2 > 0` and `V ⊤ + 1/2 = 1`. -/
theorem pair2_admissible : BolkerAdmissible pair2 1 (1 / 2) := by
  constructor
  · intro X h
    have := pair2_V_nonneg X h
    linarith
  · rw [pair2_V_top]
    norm_num

theorem pair2_P_zero : pair2.P.P {0} = 1 / 2 := by
  show mass unif2.p {0} = 1 / 2
  rw [mass_singleton]
  rfl

theorem pair2_V_zero (h : 0 < pair2.P.P {0}) : pair2.V ⟨{0}, h⟩ = 0 := by
  rw [pair2_V]
  unfold condExp mass
  simp [unif2, val2]

/-- **A non-trivial Bolker rotation moves the probability component**: `P' {0} = 1/4 ≠ 1/2 = P {0}`.
So `probability_component_not_invariant`'s content is exhibited on a rotation with `c ≠ 0`, not
only read off the identity. -/
theorem probeD_rotation_moves_P :
    (bolkerTransform pair2 1 0 1 (1 / 2) pair2_admissible).P.P {0} = 1 / 4 ∧
    pair2.P.P {0} = 1 / 2 ∧
    (bolkerTransform pair2 1 0 1 (1 / 2) pair2_admissible).P ≠ pair2.P := by
  have h0 : 0 < pair2.P.P {0} := by rw [pair2_P_zero]; norm_num
  have hP' : (bolkerTransform pair2 1 0 1 (1 / 2) pair2_admissible).P.P {0} = 1 / 4 := by
    rw [bolkerTransform_P_of_pos _ _ _ _ _ _ _ h0, pair2_V_zero h0, pair2_P_zero]
    norm_num
  refine ⟨hP', pair2_P_zero, fun heq => ?_⟩
  have := congrArg (fun Q : Prob (∅ : Designation (Finset (Fin 2))) => Q.P {0}) heq
  change (bolkerTransform pair2 1 0 1 (1 / 2) pair2_admissible).P.P {0} = pair2.P.P {0} at this
  rw [hP', pair2_P_zero] at this
  norm_num at this

/-- The same conclusion through the headline's iff: `c = 1 ≠ 0` and `V {0} = 0 ≠ 1/2 = V ⊤`. -/
theorem probeD_via_headline :
    ¬ ((1 : ℝ) = 0 ∨ ∀ X (h : 0 < pair2.P.P X),
        pair2.V ⟨X, h⟩ = pair2.V ⟨⊤, by rw [pair2.P.top]; exact one_pos⟩) := by
  rintro (h | h)
  · norm_num at h
  · have h0 : 0 < pair2.P.P {0} := by rw [pair2_P_zero]; norm_num
    have := h {0} h0
    rw [pair2_V_zero h0, pair2_V_top] at this
    norm_num at this

/-! ## Probe E -/

/-- At the coarsest algebra (`Ω = Unit`) with a two-valued utility, rigidity is not faithful for
all pairs (T3(iii), necessity direction, extreme case). -/
theorem probeE_coarsest :
    ¬ (∀ μ μa : Dist Bool,
        (∀ ω, 0 < push (fun _ : Bool => ()) μa.p ω → 0 < push (fun _ : Bool => ()) μ.p ω) →
        ∀ X : Finset Unit, 0 < mass (push (fun _ : Bool => ()) μa.p) X →
          rigidV (fun _ : Bool => ()) μ.p μa.p (fun b => if b then 1 else 0) X =
            coarseV (fun _ : Bool => ()) μa.p (fun b => if b then 1 else 0) X) := by
  rw [rigid_faithful_iff_fibres_settle]
  intro h
  have := h true false rfl
  norm_num at this

end

end Cleanroom.Decision.DpWorldsJb.AuditR2
