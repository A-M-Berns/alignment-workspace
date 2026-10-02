import Cleanroom.Found.FixKakutani.Witness

/-!
# Matching pennies on a product of standard simplices (N+ witness for `kakutani_pi_stdSimplex`)

`Witness.lean` states matching pennies on the cube `[0,1]²` (the `kakutani_pi_Icc` form). The
decision, UEA and reflective-oracle packages cite the product-of-simplices form
`kakutani_pi_stdSimplex`, so this module restates the same game there: each player `i : Fin 2`
holds a distribution `x i ∈ stdSimplex ℝ (Fin 2)`, `toCube x i = x i 1` reads off the
probability of action `1`, and the best-response correspondence `mpBRSimplex` is `mpBR`
pulled back along `toCube` and intersected with the profile set. The full hypothesis package
is proved, `kakutani_pi_stdSimplex` yields the fixed point, the fixed point is exactly the
uniform profile, and there is no continuous selection (transported from the cube).
-/

namespace Cleanroom.Found.FixKakutani

open Set Filter Topology

/-- Mixed-strategy profiles of a two-player game with two actions each: the domain form of
`kakutani_pi_stdSimplex` with `ι = Fin 2` and `A i = Fin 2`.
Source: none: infrastructure (target 5a, simplex form)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev profiles : Set (Fin 2 → (Fin 2 → ℝ)) := Set.univ.pi fun _ : Fin 2 => stdSimplex ℝ (Fin 2)

/-- The probability each player assigns to action `1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def toCube (x : Fin 2 → (Fin 2 → ℝ)) : Fin 2 → ℝ := fun i => x i 1

/-- The distribution on `Fin 2` with mass `t` on action `1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ofProb (t : ℝ) : Fin 2 → ℝ := ![1 - t, t]

/-- The profile in which player `i` plays action `1` with probability `z i`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def lift (z : Fin 2 → ℝ) : Fin 2 → (Fin 2 → ℝ) := fun i => ofProb (z i)

/-- `toCube` is continuous.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem toCube_continuous : Continuous toCube :=
  continuous_pi fun i => (continuous_apply (1 : Fin 2)).comp (continuous_apply i)

/-- `lift` is continuous.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem lift_continuous : Continuous lift := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases j
  · simpa [lift, ofProb] using continuous_const.sub (continuous_apply i)
  · simpa [lift, ofProb] using continuous_apply i

/-- `toCube (lift z) = z`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem toCube_lift (z : Fin 2 → ℝ) : toCube (lift z) = z := by
  funext i
  simp [toCube, lift, ofProb]

/-- `ofProb t` is a distribution when `t ∈ [0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem ofProb_mem_stdSimplex {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ofProb t ∈ stdSimplex ℝ (Fin 2) := by
  refine ⟨fun j => ?_, ?_⟩
  · fin_cases j <;> simp [ofProb] <;> linarith [ht.1, ht.2]
  · simp [ofProb, Fin.sum_univ_two]

/-- A profile's action-`1` probabilities lie in the square.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem toCube_mem_square {x : Fin 2 → (Fin 2 → ℝ)} (hx : x ∈ profiles) : toCube x ∈ square := by
  rw [Set.mem_univ_pi]
  intro i
  exact mem_Icc_of_mem_stdSimplex (hx i (Set.mem_univ i)) 1

/-- `lift` sends the square into the profile set.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem lift_mem_profiles {z : Fin 2 → ℝ} (hz : z ∈ square) : lift z ∈ profiles := by
  rw [Set.mem_univ_pi]
  intro i
  exact ofProb_mem_stdSimplex (hz i (Set.mem_univ i))

/-- The matching-pennies best-response correspondence on profiles: `y ∈ mpBRSimplex x` iff `y`
is a profile and its action-`1` probabilities are best responses (`mpBR`) to those of `x`.
Source: none: infrastructure (target 5a, simplex form)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def mpBRSimplex (x : Fin 2 → (Fin 2 → ℝ)) : Set (Fin 2 → (Fin 2 → ℝ)) :=
  {y | y ∈ profiles ∧ toCube y ∈ mpBR (toCube x)}

/-- `mpBRSimplex` maps profiles to profiles.
Source: none: infrastructure (hypothesis package)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mpBRSimplex_maps : ∀ x ∈ profiles, mpBRSimplex x ⊆ profiles :=
  fun _ _ _ hy => hy.1

/-- `mpBRSimplex x` is nonempty for every profile `x`.
Source: none: infrastructure (hypothesis package)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mpBRSimplex_nonempty : ∀ x ∈ profiles, (mpBRSimplex x).Nonempty := by
  intro x hx
  obtain ⟨z, hz⟩ := mpBR_nonempty (toCube x) (toCube_mem_square hx)
  refine ⟨lift z, lift_mem_profiles (mpBR_maps _ (toCube_mem_square hx) hz), ?_⟩
  rw [toCube_lift]
  exact hz

/-- `mpBRSimplex x` is convex: the profile set is convex and `mpBR (toCube x)` is convex, and
`toCube` is linear.
Source: none: infrastructure (hypothesis package)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mpBRSimplex_convex : ∀ x ∈ profiles, Convex ℝ (mpBRSimplex x) := by
  intro x hx
  show Convex ℝ (profiles ∩ toCube ⁻¹' mpBR (toCube x))
  refine (convex_pi fun _ _ => convex_stdSimplex ℝ (Fin 2)).inter ?_
  exact (mpBR_convex _ (toCube_mem_square hx)).is_linear_preimage
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- `mpBRSimplex` has a closed graph over the profile set: the graph is the intersection of two
closed profile conditions with the preimage of the (closed) graph of `mpBR` under
`toCube × toCube`.
Source: none: infrastructure (hypothesis package)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mpBRSimplex_hasClosedGraphOn : HasClosedGraphOn mpBRSimplex profiles := by
  unfold HasClosedGraphOn
  have hset : {p : (Fin 2 → (Fin 2 → ℝ)) × (Fin 2 → (Fin 2 → ℝ)) |
      p.1 ∈ profiles ∧ p.2 ∈ mpBRSimplex p.1} =
      (Prod.fst ⁻¹' profiles) ∩ (Prod.snd ⁻¹' profiles) ∩
        (Prod.map toCube toCube ⁻¹' {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | q.1 ∈ square ∧ q.2 ∈ mpBR q.1}) := by
    ext ⟨x, y⟩
    simp only [mpBRSimplex, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Prod.map_apply]
    constructor
    · rintro ⟨hx, hy, h⟩
      exact ⟨⟨hx, hy⟩, toCube_mem_square hx, h⟩
    · rintro ⟨⟨hx, hy⟩, _, h⟩
      exact ⟨hx, hy, h⟩
  rw [hset]
  have hprof : IsClosed profiles := isClosed_set_pi fun _ _ => isClosed_stdSimplex ℝ (Fin 2)
  have hgraph : IsClosed {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | q.1 ∈ square ∧ q.2 ∈ mpBR q.1} :=
    mpBR_hasClosedGraphOn
  exact ((hprof.preimage continuous_fst).inter (hprof.preimage continuous_snd)).inter
    (hgraph.preimage (toCube_continuous.prodMap toCube_continuous))

/-- **N+ witness for `kakutani_pi_stdSimplex`: matching pennies on profiles.** The best-response
correspondence `mpBRSimplex` satisfies the full hypothesis package on
`Set.univ.pi (fun _ : Fin 2 => stdSimplex ℝ (Fin 2))`, so `kakutani_pi_stdSimplex` gives a fixed
point. Non-degeneracy: `mem_mpBRSimplex_self_iff` (the fixed point is the uniform profile) and
`mpBRSimplex_no_continuous_selection`.
Source: none: infrastructure (target 5a, simplex form)
Kind: N+
Fidelity: n/a
Hyps: (a) all, each proved above -/
theorem mpBRSimplex_exists_fixed : ∃ x ∈ profiles, x ∈ mpBRSimplex x :=
  kakutani_pi_stdSimplex (ι := Fin 2) (A := fun _ => Fin 2) mpBRSimplex mpBRSimplex_maps
    mpBRSimplex_nonempty mpBRSimplex_convex mpBRSimplex_hasClosedGraphOn

/-- The fixed points of `mpBRSimplex` are exactly the uniform profile (both players mix
`1/2`–`1/2`).
Source: none: infrastructure (target 5a, simplex form)
Kind: P
Fidelity: n/a
Hyps: (a) -/
theorem mem_mpBRSimplex_self_iff {x : Fin 2 → (Fin 2 → ℝ)} :
    x ∈ mpBRSimplex x ↔ x = fun _ => ofProb (1 / 2) := by
  constructor
  · rintro ⟨hx, h⟩
    have hc : toCube x = fun _ => 1 / 2 := mem_mpBR_self_iff.1 h
    funext i
    have h1 : x i 1 = 1 / 2 := congrFun hc i
    have hsum : x i 0 + x i 1 = 1 := by
      have := (hx i (Set.mem_univ i)).2
      simpa [Fin.sum_univ_two] using this
    funext j
    fin_cases j
    · simp [ofProb]; linarith
    · simp [ofProb]; linarith
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [Set.mem_univ_pi]
      intro i
      exact ofProb_mem_stdSimplex ⟨by norm_num, by norm_num⟩
    · have : toCube (fun _ : Fin 2 => ofProb (1 / 2)) = fun _ => 1 / 2 := by
        funext i; simp [toCube, ofProb]
      rw [this]
      exact mem_mpBR_self_iff.2 rfl

/-- **No continuous selection** of `mpBRSimplex` on the profile set: one would transport along
`lift`/`toCube` to a continuous selection of `mpBR` on the square, which
`mpBR_no_continuous_selection` rules out.
Source: none: infrastructure (target 5a, simplex form)
Kind: P
Fidelity: n/a
Hyps: (a) -/
theorem mpBRSimplex_no_continuous_selection :
    ¬ ∃ g : (Fin 2 → (Fin 2 → ℝ)) → (Fin 2 → (Fin 2 → ℝ)),
      ContinuousOn g profiles ∧ ∀ x ∈ profiles, g x ∈ mpBRSimplex x := by
  rintro ⟨g, hg_cont, hg_sel⟩
  apply mpBR_no_continuous_selection
  refine ⟨fun z => toCube (g (lift z)), ?_, ?_⟩
  · exact toCube_continuous.comp_continuousOn
      (hg_cont.comp lift_continuous.continuousOn fun z hz => lift_mem_profiles hz)
  · intro z hz
    have := (hg_sel (lift z) (lift_mem_profiles hz)).2
    rwa [toCube_lift] at this

end Cleanroom.Found.FixKakutani
