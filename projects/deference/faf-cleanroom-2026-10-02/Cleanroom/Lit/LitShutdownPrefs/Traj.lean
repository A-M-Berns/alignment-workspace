import Cleanroom.Lit.LitShutdownPrefs.Lottery

/-!
# Utility-vector trajectories (carrier (b) of the mandate)

`Traj := List ℝ`, one real per pre-shutdown timestep. `len t` counts utilities (Thornley 2025 §8:
"I won't count shutdown as part of the trajectory-length"), so the sources' "shutdown at
timestep `t`" is `len = t − 1`. `sumTotal t = t.sum` (Thornley 2024 §11 "sum-total utility").
Discounting is never built into the carrier; `discSum δ` is a utility *function* used only by
witnesses.

Length machinery on lotteries: `lengths X = (supp X).image len`, `mem_lengths_iff` (a length is
in `lengths X` iff the length event has positive mass), and `condLen X l h` (the sublottery on
`{len = l}`, proof-carrying: defined only for `l ∈ lengths X`).
-/

namespace Cleanroom.Lit.LitShutdownPrefs

/-- A trajectory: the vector of utilities at the pre-shutdown timesteps.
Source: Thornley 2023 §8 ll. 296–300; 2024 §11 ll. 259–263; [[lit-shutdown-prefs-mandate]] Carrier §
Kind: D
Fidelity: exact (Pareto Indifference absorbed: trajectories *are* utility vectors) -/
abbrev Traj : Type := List ℝ

/-- Trajectory length: the number of pre-shutdown timesteps.
Source: Thornley 2025 §8 ("I won't count shutdown as part of the trajectory-length")
Kind: D
Fidelity: exact -/
def len (t : Traj) : ℕ := t.length

/-- Sum-total utility: the sum of utilities before shutdown.
Source: Thornley 2024 §11 ll. 267–268
Kind: D
Fidelity: exact -/
def sumTotal (t : Traj) : ℝ := t.sum

/-- The `δ`-discounted sum `∑ᵢ δ^i · t[i]` (a witness utility; not part of the carrier).
Source: [[lit-shutdown-prefs-mandate]] Target 6 (witness)
Kind: D -/
def discSum (δ : ℝ) : Traj → ℝ
  | [] => 0
  | x :: xs => x + δ * discSum δ xs

namespace Lottery

/-- The set of trajectory-lengths assigned positive probability.
Source: Thornley 2025 §4 ("trajectory-lengths assigned positive probability")
Kind: D
Fidelity: exact -/
def lengths (X : Lottery Traj) : Finset ℕ := X.support.image len

/-- A length is in `lengths X` iff its event has positive mass.
Source: none: infrastructure
Kind: L -/
theorem mem_lengths_iff (X : Lottery Traj) (l : ℕ) :
    l ∈ X.lengths ↔ 0 < X.mass (fun t => len t = l) := by
  constructor
  · intro hl
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hl
    exact X.mass_pos_of_mem _ t ht rfl
  · intro h
    by_contra hl
    have : X.mass (fun t => len t = l) = 0 := by
      unfold mass expect wsum
      refine Finset.sum_eq_zero fun t ht => ?_
      have : len t ≠ l := fun e => hl (Finset.mem_image.mpr ⟨t, ht, e⟩)
      simp [this]
    rw [this] at h
    exact lt_irrefl _ h

/-- The sublottery of `X` conditional on length `l`, for `l ∈ lengths X` (proof-carrying).
Source: Thornley 2024 §11 ("we can pick out sublotteries by conditioning on shutdown occurring
at a particular timestep"); [[lit-shutdown-prefs-mandate]] Target 7 (`condLen`)
Kind: D
Fidelity: exact (no junk value: the membership proof is an argument) -/
noncomputable def condLen (X : Lottery Traj) (l : ℕ) (h : l ∈ X.lengths) : Lottery Traj :=
  X.condOn (fun t => len t = l) ((X.mem_lengths_iff l).mp h)

/-- The conditioned lottery lives on length `l`.
Source: none: infrastructure
Kind: L -/
theorem condLen_mass_self (X : Lottery Traj) (l : ℕ) (h : l ∈ X.lengths) :
    (X.condLen l h).mass (fun t => len t = l) = 1 :=
  X.mass_condOn_self _ _

/-- `lengths` of the conditioned lottery is `{l}`.
Source: none: infrastructure
Kind: L -/
theorem lengths_condLen (X : Lottery Traj) (l : ℕ) (h : l ∈ X.lengths) :
    (X.condLen l h).lengths = {l} := by
  unfold lengths condLen
  rw [support_condOn]
  ext m
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨t, ⟨_, ht⟩, rfl⟩; exact ht
  · rintro rfl
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
    exact ⟨t, ⟨ht, rfl⟩, rfl⟩

/-- Ratio form of the conditional expectation on a length class.
Source: [[lit-shutdown-prefs-mandate]] Carrier § ("ratio forms are lemmas")
Kind: L -/
theorem expect_condLen (X : Lottery Traj) (l : ℕ) (h : l ∈ X.lengths) (g : Traj → ℝ) :
    (X.condLen l h).expect g = X.condSum (fun t => len t = l) g / X.mass (fun t => len t = l) :=
  X.expect_condOn _ _ g

/-- The length decomposition of the mass function: `X = ∑_{l ∈ lengths X} mass_l • condLen X l`
(as a sum over the attached finset, so each term carries its membership proof).
Source: Thornley 2025 §7 ("`X` can be expressed in the form `p₁X₁ + … + pₙXₙ` where `X₁` is `X`
conditional on the shortest positive-probability trajectory-length, …")
Kind: L
Fidelity: exact -/
theorem p_eq_sum_condLen (X : Lottery Traj) :
    X.p = ∑ l ∈ X.lengths.attach, X.mass (fun t => len t = l.1) • (X.condLen l.1 l.2).p := by
  have hterm : ∀ l : {l // l ∈ X.lengths},
      X.mass (fun t => len t = l.1) • (X.condLen l.1 l.2).p = X.p.filter (fun t => len t = l.1) :=
    fun l => X.mass_smul_condOn_p _ _
  simp_rw [hterm]
  ext t
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.filter_apply]
  by_cases ht : t ∈ X.support
  · have hl : len t ∈ X.lengths := Finset.mem_image.mpr ⟨t, ht, rfl⟩
    rw [Finset.sum_eq_single ⟨len t, hl⟩]
    · simp
    · intro l _ hne
      have : len t ≠ l.1 := fun e => hne (Subtype.ext e.symm)
      simp [this]
    · intro h; exact absurd (Finset.mem_attach _ _) h
  · have h0 : X.p t = 0 := Finsupp.notMem_support_iff.mp ht
    rw [h0]
    symm
    exact Finset.sum_eq_zero fun l _ => by simp

/-- Two disjoint events have total mass at most one.
Source: none: infrastructure
Kind: L -/
theorem mass_add_mass_le_one_of_disjoint {T : Type} (X : Lottery T) (q q' : T → Prop)
    [DecidablePred q] [DecidablePred q'] (h : ∀ t, q t → q' t → False) :
    X.mass q + X.mass q' ≤ 1 := by
  calc X.mass q + X.mass q'
      = X.expect (fun t => (if q t then (1 : ℝ) else 0) + (if q' t then 1 else 0)) :=
        (X.expect_add _ _).symm
    _ ≤ X.expect (fun _ => 1) := by
        apply X.expect_mono
        intro t
        by_cases hq : q t <;> by_cases hq' : q' t <;> simp [hq, hq']
        exact (h t hq hq').elim
    _ = 1 := X.expect_const_one

/-- If two distinct lengths both have positive probability, neither has all the mass.
Source: none: infrastructure
Kind: L -/
theorem mass_lt_one_of_ne (X : Lottery Traj) {l l' : ℕ} (hl' : l' ∈ X.lengths)
    (hne : l ≠ l') : X.mass (fun t => len t = l) < 1 := by
  have h1 := X.mass_add_mass_le_one_of_disjoint (fun t => len t = l) (fun t => len t = l')
    (fun t e e' => hne (e.symm.trans e'))
  have h2 := (X.mem_lengths_iff l').mp hl'
  linarith

/-- When a single length carries all the mass, conditioning on it is the identity.
Source: [[lit-shutdown-prefs-mandate]] Target 8(a) ("handle `lengths X = {l}` separately, where `condLen X l = X`")
Kind: L -/
theorem condLen_eq_self (X : Lottery Traj) (l : ℕ) (h : X.lengths = {l}) (hl : l ∈ X.lengths) :
    X.condLen l hl = X := by
  have hall : ∀ t ∈ X.support, len t = l := fun t ht => by
    have : len t ∈ X.lengths := Finset.mem_image.mpr ⟨t, ht, rfl⟩
    rw [h] at this
    exact Finset.mem_singleton.mp this
  have hmass : X.mass (fun t => len t = l) = 1 := by
    unfold mass
    rw [X.expect_congr (g₂ := fun _ => 1) (fun t ht => by simp [hall t ht])]
    exact X.expect_const_one
  have hfilt : X.p.filter (fun t => len t = l) = X.p := by
    rw [Finsupp.filter_eq_self_iff]
    exact fun t ht => hall t (Finsupp.mem_support_iff.mpr ht)
  ext1
  show (X.mass (fun t => len t = l))⁻¹ • X.p.filter (fun t => len t = l) = X.p
  rw [hmass, hfilt, inv_one, one_smul]

/-- The length decomposition over any finset known to equal `lengths X` (so a second lottery with
the same lengths can be decomposed over the *same* index set).
Source: Thornley 2025 §7 (the two decompositions of `X` and `Y` over the shared lengths)
Kind: L -/
theorem p_eq_sum_condLen' (X : Lottery Traj) (s : Finset ℕ) (hs : s = X.lengths) :
    X.p = ∑ l ∈ s.attach, X.mass (fun t => len t = l.1) • (X.condLen l.1 (hs ▸ l.2)).p := by
  subst hs
  exact X.p_eq_sum_condLen

/-- `lengths X` is nonempty.
Source: none: infrastructure
Kind: L -/
theorem lengths_nonempty (X : Lottery Traj) : X.lengths.Nonempty :=
  X.support_nonempty.image len

end Lottery

end Cleanroom.Lit.LitShutdownPrefs
