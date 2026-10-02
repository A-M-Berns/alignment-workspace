import Cleanroom.Decision.DpLocalOpt.Ssa

/-!
# `dp-local-opt`: Definition 23, the coalition Lemma 1 and Proposition 13 (T10)

Definition 23 (conflict-freeness for a family `𝓜` of "moral patients" `D ⊆ 𝒟`): no `D ∈ 𝓜` has
a joint revision of `C` on `D` that improves `𝔼_μ[r ∣ occ(D)]`, `occ(D) := ⋃_{d ∈ D} occ(d)`.
HA-7′: `μ_{B,C}(occ(D))` does not depend on `C` restricted to `D` (the coalition Lemma 1,
`mass_occSet_congr_off`), and leaves outside `occ(D)` are untouched by a revision on `D`, so
`V_B(C') − V_B(C) = μ(occ(D)) (𝔼_{C'}[r ∣ occ(D)] − 𝔼_C[r ∣ occ(D)])`: occurrence-conditioned
Definition 23 is the `𝓜`-coalition Nash condition of the common-value game
(`conflictFree_iff_coalition_nash`, Proposition 13(i)), whose endpoints are optimality (trivial
family) and mixed Definition 22 (singletons), and which is antitone in refinement. At
`μ(occ(D)) = 0` both conditional expectations are Lean's `0` and the clause imposes nothing,
matching HA-7′.
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [DecidableEq ι] [∀ d, DecidableEq (acts d)]

/-! ### Sets of points and their occurrence events -/

section defs

/-- `C'` *agrees with `C` off `D`*: a joint (mixed) revision of `C` on the points of `D`.
Source: [[decision-problems-v2]] §8 Definition 23 ("revising `C` on `D_i` only")
Kind: D -/
def AgreesOff (C C' : Proc ι acts K) (D : Finset ι) : Prop := ∀ d, d ∉ D → C' d = C d

/-- `occ(D) := {ℓ : some `d ∈ D` has `#_d(ℓ) > 0`}`.
Source: [[decision-problems-v2]] §8 Definition 23 (`occ(D_i) := ⋃_{d ∈ D_i} occ(d)`)
Kind: D -/
def occSet (D : Finset ι) (B : Tree Ω ι acts K) : Finset B.Leaves :=
  Finset.univ.filter fun ℓ => ∃ d ∈ D, 0 < count d B ℓ

/-- `occ(D) = ⋃_{d ∈ D} occ(d)`.
Source: [[decision-problems-v2]] §8 Definition 23
Kind: L -/
theorem occSet_eq_biUnion (D : Finset ι) (B : Tree Ω ι acts K) :
    occSet D B = D.biUnion fun d => occ d B := by
  ext ℓ; simp [occSet, occ]

/-- `occ({d}) = occ(d)`.
Source: none: infrastructure
Kind: L -/
theorem occSet_singleton (d : ι) (B : Tree Ω ι acts K) : occSet {d} B = occ d B := by
  ext ℓ; simp [occSet, occ]

/-- Membership in `occSet`.
Source: none: infrastructure
Kind: L -/
@[simp] theorem mem_occSet (D : Finset ι) (B : Tree Ω ι acts K) (ℓ : B.Leaves) :
    ℓ ∈ occSet D B ↔ ∃ d ∈ D, 0 < count d B ℓ := by
  simp [occSet]

/-- `occSet` is monotone in `D`.
Source: none: infrastructure
Kind: L -/
theorem occSet_mono {D D' : Finset ι} (h : D' ⊆ D) (B : Tree Ω ι acts K) :
    occSet D' B ⊆ occSet D B := by
  intro ℓ hℓ
  rw [mem_occSet] at hℓ ⊢
  obtain ⟨d, hd, hc⟩ := hℓ
  exact ⟨d, h hd, hc⟩

end defs

/-! ### The coalition Lemma 1 -/

section coalitionLemma

/-- `μ_{B,C}(occ(D))` as an indicator sum.
Source: none: infrastructure
Kind: L -/
theorem mass_occSet (C : Proc ι acts K) (D : Finset ι) (B : Tree Ω ι acts K) :
    mass C B (occSet D B) = ∑ ℓ, if (∃ d ∈ D, 0 < count d B ℓ) then leafLaw C B ℓ else 0 :=
  mass_filter C B _

/-- **HA-7′, the coalition Lemma 1**: `μ_{B,C}(occ(D))` does not depend on `C` restricted to `D` —
two procedures agreeing off `D` give `occ(D)` the same mass (joint and mixed revisions included).
`occ(D)` is reached by non-`D` draws only.
Source: `repair/harmony.md` HA-7′ ("For any set `D` of queried points, `μ_{B,C}(occ(D))` does not
depend on `C` restricted to `D` (joint and mixed revisions included)") | [[decision-problems-v2]]
§3.1 Lemma 1 (the singleton case) | dp-core-053 | dp-cf-098
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem mass_occSet_congr_off (D : Finset ι) :
    (B : Tree Ω ι acts K) → ∀ {C C' : Proc ι acts K}, AgreesOff C C' D →
      mass C' B (occSet D B) = mass C B (occSet D B)
  | leaf _ _, _, _, _ => by simp [mass_occSet]
  | chance _ β child, C, C', h => by
      have ih : ∀ i, (∑ ℓ, if (∃ d ∈ D, 0 < count d (child i) ℓ) then leafLaw C' (child i) ℓ
          else 0) = ∑ ℓ, if (∃ d ∈ D, 0 < count d (child i) ℓ) then leafLaw C (child i) ℓ else 0 :=
        fun i => by
          rw [← mass_occSet, ← mass_occSet]; exact mass_occSet_congr_off D (child i) h
      rw [mass_occSet, mass_occSet, sum_leaves_chance, sum_leaves_chance]
      simp only [count_chance, leafLaw_chance, ite_mul_zero_eq, ← Finset.mul_sum, ih]
  | decision d' child, C, C', h => by
      have ih : ∀ a, (∑ ℓ, if (∃ d ∈ D, 0 < count d (child a) ℓ) then leafLaw C' (child a) ℓ
          else 0) = ∑ ℓ, if (∃ d ∈ D, 0 < count d (child a) ℓ) then leafLaw C (child a) ℓ else 0 :=
        fun a => by
          rw [← mass_occSet, ← mass_occSet]; exact mass_occSet_congr_off D (child a) h
      rw [mass_occSet, mass_occSet, sum_leaves_decision, sum_leaves_decision]
      by_cases hd : d' ∈ D
      · -- every leaf below a `D`-node is in `occ(D)`: both masses are `1`
        have hall : ∀ (a : acts d') (ℓ : (child a).Leaves),
            ∃ d ∈ D, 0 < count d (decision d' child) ⟨a, ℓ⟩ :=
          fun a ℓ => ⟨d', hd, by simp [count_decision]⟩
        simp only [hall, if_true, leafLaw_decision, ← Finset.mul_sum, sum_leafLaw, mul_one,
          FinDistr.sum_one]
      · have hcount : ∀ (a : acts d') (ℓ : (child a).Leaves),
            (∃ d ∈ D, 0 < count d (decision d' child) ⟨a, ℓ⟩) ↔
              ∃ d ∈ D, 0 < count d (child a) ℓ := by
          intro a ℓ
          constructor
          · rintro ⟨d, hdD, hc⟩
            refine ⟨d, hdD, ?_⟩
            have hne : d' ≠ d := fun e => hd (e ▸ hdD)
            simpa [count_decision, hne] using hc
          · rintro ⟨d, hdD, hc⟩
            refine ⟨d, hdD, ?_⟩
            have hne : d' ≠ d := fun e => hd (e ▸ hdD)
            simpa [count_decision, hne] using hc
        simp only [hcount, leafLaw_decision, ite_mul_zero_eq, ← Finset.mul_sum, ih, h d' hd]

/-- Off `occ(D)`, procedures agreeing off `D` give every leaf the same mass.
Source: `repair/harmony.md` HA-7′ ("leaves outside `occ(D)` untouched")
Kind: L -/
theorem leafLaw_congr_off_of_not_occSet (D : Finset ι) {C C' : Proc ι acts K}
    (h : AgreesOff C C' D) (B : Tree Ω ι acts K) {ℓ : B.Leaves} (hℓ : ℓ ∉ occSet D B) :
    leafLaw C' B ℓ = leafLaw C B ℓ := by
  apply leafLaw_congr_off_of_count_zero C D h B ℓ
  intro d hd
  rw [mem_occSet] at hℓ
  exact Nat.eq_zero_of_not_pos fun hc => hℓ ⟨d, hd, hc⟩

end coalitionLemma

/-! ### Conditional expectation on `occ(D)` and Definition 23 -/

section def23

variable (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- `𝔼_{μ_C}[r ∣ occ(D)]`, as `(∑_{ℓ ∈ occ(D)} μ_C(ℓ) r(ℓ)) / μ_C(occ(D))`; Lean's `x / 0 = 0` at
`μ_C(occ(D)) = 0`.
Source: [[decision-problems-v2]] §8 Definition 23 (`𝔼_μ[r ∣ occ(D_i)]`)
Kind: D -/
def condExp (D : Finset ι) : K :=
  (∑ ℓ ∈ occSet D B, leafLaw C B ℓ * payoff B ℓ) / mass C B (occSet D B)

/-- **Definition 23 (conflict-freeness), occurrence mode**: for every patient `D ∈ 𝓜`, no joint
revision of `C` on `D` improves `𝔼[r ∣ occ(D)]`. At `μ(occ(D)) = 0` both sides are Lean's `0`,
so the clause imposes nothing there (HA-7′: "at `μ(occ(D)) = 0` both sides vanish and
Definition 23 imposes nothing").
Source: [[decision-problems-v2]] §8 Definition 23 (line 285)
Kind: D
Fidelity: exact (occurrence mode; the `x / 0 = 0` convention agrees with HA-7′'s reading) -/
def ConflictFree (𝓜 : Set (Finset ι)) : Prop :=
  ∀ D ∈ 𝓜, ∀ C' : Proc ι acts K, AgreesOff C C' D → condExp C' B D ≤ condExp C B D

/-- **HA-7′ / Remark 8.2**: for a revision `C'` on `D`,
`V_B(C') − V_B(C) = ∑_{ℓ ∈ occ(D)} (μ_{C'}(ℓ) − μ_C(ℓ)) r(ℓ)`.
Source: `repair/harmony.md` HA-7′ ("`V_B(C') − V_B(C) = μ(occ(D)) (𝔼_{C'}[r ∣ occ(D)] −
𝔼_C[r ∣ occ(D)])` (leaves outside `occ(D)` untouched)")
Kind: P
Fidelity: exact (the unnormalised form; `condExp_le_iff` is the normalised one) -/
theorem value_sub_eq_sum_occSet (D : Finset ι) {C' : Proc ι acts K} (h : AgreesOff C C' D) :
    value C' B - value C B =
      ∑ ℓ ∈ occSet D B, (leafLaw C' B ℓ - leafLaw C B ℓ) * payoff B ℓ := by
  unfold value
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ℓ => ℓ ∈ occSet D B),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ℓ => ℓ ∈ occSet D B),
    Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hoff : ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ∉ occSet D B), leafLaw C' B ℓ * payoff B ℓ =
      ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ∉ occSet D B), leafLaw C B ℓ * payoff B ℓ := by
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    rw [Finset.mem_filter] at hℓ
    rw [leafLaw_congr_off_of_not_occSet D h B hℓ.2]
  rw [hoff]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- **HA-7′, normalised**: with `0 < μ_C(occ(D))`, a revision on `D` improves `𝔼[r ∣ occ(D)]` iff
it improves `V_B`.
Source: `repair/harmony.md` HA-7′
Kind: C
Fidelity: exact
Hyps: (a) `0 < μ_C(occ(D))` (HA-7′'s non-degeneracy) -/
theorem condExp_le_iff (D : Finset ι) (hpos : 0 < mass C B (occSet D B)) {C' : Proc ι acts K}
    (h : AgreesOff C C' D) : condExp C' B D ≤ condExp C B D ↔ value C' B ≤ value C B := by
  unfold condExp
  rw [mass_occSet_congr_off D B h, div_le_div_iff_of_pos_right hpos, ← sub_nonpos,
    ← Finset.sum_sub_distrib]
  have : (∑ ℓ ∈ occSet D B, (leafLaw C' B ℓ * payoff B ℓ - leafLaw C B ℓ * payoff B ℓ)) =
      value C' B - value C B := by
    rw [value_sub_eq_sum_occSet C B D h]
    exact Finset.sum_congr rfl fun ℓ _ => by ring
  rw [this, sub_nonpos]

/-- At `μ_C(occ(D)) = 0` the Definition 23 clause for `D` holds for every revision (both sides
are `0`).
Source: `repair/harmony.md` HA-7′ ("at `μ(occ(D)) = 0` both sides vanish")
Kind: L -/
theorem condExp_le_of_mass_eq_zero (D : Finset ι) (h0 : mass C B (occSet D B) = 0)
    {C' : Proc ι acts K} (h : AgreesOff C C' D) : condExp C' B D ≤ condExp C B D := by
  unfold condExp
  rw [mass_occSet_congr_off D B h, h0, div_zero, div_zero]

/-- **Proposition 13(i) (Conjecture 1 corrected, A39)**: occurrence-conditioned conflict-freeness
for `𝓜` is the `𝓜`-coalition Nash condition of the common-value game — no patient of positive
occurrence mass has a `V_B`-improving joint revision.
Source: `repair/harmony.md` HA-7′ ("occurrence-conditioned Definition 23 for *any* family `𝓜`
`⟺` no `D ∈ 𝓜` has a `V_B`-improving joint revision — an `𝓜`-coalition Nash condition of the
common-value game") | A39 | dp-core-053 | dp-cf-098 | dp-cf-2-054
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem conflictFree_iff_coalition_nash (𝓜 : Set (Finset ι)) :
    ConflictFree C B 𝓜 ↔
      ∀ D ∈ 𝓜, 0 < mass C B (occSet D B) → ∀ C' : Proc ι acts K, AgreesOff C C' D →
        value C' B ≤ value C B := by
  unfold ConflictFree
  constructor
  · intro h D hD hpos C' hC'
    exact (condExp_le_iff C B D hpos hC').mp (h D hD C' hC')
  · intro h D hD C' hC'
    rcases (mass_nonneg C B (occSet D B)).lt_or_eq with hpos | h0
    · exact (condExp_le_iff C B D hpos hC').mpr (h D hD hpos C' hC')
    · exact condExp_le_of_mass_eq_zero C B D h0.symm hC'

/-- **The trivial family is optimality**: with `0 < μ_C(occ(𝒟))` (`𝒟 = queried B`),
conflict-freeness for `{𝒟}` is `V`-optimality — no "root queries" hedge is needed (HA-8′: the
conditioning cancels by HA-7′).
Source: [[decision-problems-v2]] §8 Conjecture 1 ("With `𝓜` trivial …, conflict-freeness
contains `V`-optimality") as corrected by A39 / HA-8′ ("grand `{(1,1)}`, which *equals*
optimality (the 'when the root queries' hedge in Conjecture 1 is unnecessary)")
Kind: C
Fidelity: exact (the corrected statement; Conjecture 1's "contains" is an equality)
Hyps: (a) `0 < μ_C(occ(queried B))` -/
theorem conflictFree_trivial_iff (hpos : 0 < mass C B (occSet (queried B) B)) :
    ConflictFree C B {queried B} ↔ IsOptimal C B := by
  rw [conflictFree_iff_coalition_nash]
  constructor
  · intro h C''
    have hC' : AgreesOff C (fun d => if d ∈ queried B then C'' d else C d) (queried B) :=
      fun d hd => by simp [hd]
    have := h (queried B) rfl hpos _ hC'
    rwa [value_congr_queried B (C := fun d => if d ∈ queried B then C'' d else C d) (C' := C'')
      (fun d hd => by simp [hd])] at this
  · intro h D hD _ C' _
    rw [Set.mem_singleton_iff] at hD
    exact h C'

/-- At `μ_C(occ(D)) = 0` a revision on `D` leaves `V_B` unchanged: every leaf of `occ(D)` has mass
`0` under `C` and, by the coalition Lemma 1, under any `C'` agreeing off `D`.
Source: `repair/harmony.md` HA-7′ ("imposes nothing" at mass `0`); audit r1 adversarial N1
(probe C, adopted)
Kind: P -/
theorem value_eq_of_agreesOff_of_mass_zero (D : Finset ι) {C' : Proc ι acts K}
    (h : AgreesOff C C' D) (h0 : mass C B (occSet D B) = 0) : value C' B = value C B := by
  have h0' : mass C' B (occSet D B) = 0 := by rw [mass_occSet_congr_off D B h]; exact h0
  have hz : ∀ ℓ ∈ occSet D B, leafLaw C B ℓ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun ℓ _ => leafLaw_nonneg C B ℓ).mp h0
  have hz' : ∀ ℓ ∈ occSet D B, leafLaw C' B ℓ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun ℓ _ => leafLaw_nonneg C' B ℓ).mp h0'
  have e := value_sub_eq_sum_occSet C B D h
  have hsum : ∑ ℓ ∈ occSet D B, (leafLaw C' B ℓ - leafLaw C B ℓ) * payoff B ℓ = 0 :=
    Finset.sum_eq_zero fun ℓ hℓ => by rw [hz' ℓ hℓ, hz ℓ hℓ]; ring
  exact sub_eq_zero.mp (e.trans hsum)

/-- **Proposition 13(i) exactly as A39 states it** — no positivity clause: occurrence-conditioned
Definition 23 for `𝓜` holds iff no `D ∈ 𝓜` has a `V_B`-improving joint revision.
Source: `repair/harmony.md` HA-7′; A39 ("no `D ∈ 𝓜` has a joint revision improving `V_B`");
audit r1 adversarial N1 (probe C, adopted)
Kind: C
Fidelity: exact (A39's wording; the positivity clause of `conflictFree_iff_coalition_nash` is
removable)
Hyps: (a) all -/
theorem conflictFree_iff_coalition_nash' (𝓜 : Set (Finset ι)) :
    ConflictFree C B 𝓜 ↔
      ∀ D ∈ 𝓜, ∀ C' : Proc ι acts K, AgreesOff C C' D → value C' B ≤ value C B := by
  rw [conflictFree_iff_coalition_nash]
  constructor
  · intro h D hD C' hC'
    rcases (mass_nonneg C B (occSet D B)).lt_or_eq with hpos | h0
    · exact h D hD hpos C' hC'
    · exact (value_eq_of_agreesOff_of_mass_zero C B D hC' h0.symm).le
  · intro h D hD _ C' hC'
    exact h D hD C' hC'

/-- **The trivial family is optimality, with no hypothesis at all** (no "root queries" hedge, no
positivity).
Source: [[decision-problems-v2]] §8 Conjecture 1 as corrected by A39 / HA-8′; audit r1
adversarial N1 and fidelity non-blocking 3 (probe C, adopted)
Kind: C
Fidelity: exact (the corrected statement, unconditional)
Hyps: (a) all -/
theorem conflictFree_trivial_iff' : ConflictFree C B {queried B} ↔ IsOptimal C B := by
  rw [conflictFree_iff_coalition_nash']
  constructor
  · intro h C''
    have hC' : AgreesOff C (fun d => if d ∈ queried B then C'' d else C d) (queried B) :=
      fun d hd => by simp [hd]
    have := h (queried B) rfl _ hC'
    rwa [value_congr_queried B (C := fun d => if d ∈ queried B then C'' d else C d) (C' := C'')
      (fun d hd => by simp [hd])] at this
  · intro h D hD C' _
    rw [Set.mem_singleton_iff] at hD
    exact h C'

/-- Mixed coherence at `d` holds when `μ_C(occ(d)) = 0` (every deviation leaves `V_B` unchanged).
Source: A32 ("vacuous at points the procedure never reaches")
Kind: L -/
theorem coherentAt_of_mass_eq_zero (d : ι) (h0 : mass C B (occ d B) = 0) : CoherentAt C B d := by
  intro m
  rw [value_deviate_eq_ssaNum_add_offOcc]
  have hself : C.deviate d (C d) = C := by
    funext d'; by_cases hd : d' = d
    · subst hd; simp
    · simp [Proc.deviate_ne C _ hd]
  conv_rhs => rw [← hself, value_deviate_eq_ssaNum_add_offOcc]
  have hz : ∀ m', ssaNum C B d m' = 0 := by
    intro m'
    rw [← ssaValue_mul_mass, h0, mul_zero]
  rw [hz, hz]

/-- A revision on `{d}` is a point-deviation at `d`.
Source: none: infrastructure
Kind: L -/
theorem agreesOff_singleton_iff {C' : Proc ι acts K} (d : ι) :
    AgreesOff C C' {d} ↔ C' = C.deviate d (C' d) := by
  constructor
  · intro h; funext d'
    by_cases hd : d' = d
    · subst hd; simp
    · rw [Proc.deviate_ne C _ hd]; exact h d' (by simpa using hd)
  · intro h d' hd
    rw [h, Proc.deviate_ne C _ (by simpa using hd)]

/-- **Singletons are mixed Definition 22**: conflict-freeness for the family of singletons of
queried points is `Coherent` (no positivity needed: both sides are vacuous at `μ(occ(d)) = 0`).
Source: `repair/harmony.md` HA-8′ ("singletons … (`=` Definition 22)") | A39
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem conflictFree_singletons_iff :
    ConflictFree C B ((fun d => ({d} : Finset ι)) '' (↑(queried B) : Set ι)) ↔ Coherent C B := by
  rw [conflictFree_iff_coalition_nash]
  constructor
  · intro h d hd m
    rcases (mass_nonneg C B (occ d B)).lt_or_eq with hpos | h0
    · have := h {d} ⟨d, by simpa using hd, rfl⟩ (by rwa [occSet_singleton]) (C.deviate d m)
        (by rw [agreesOff_singleton_iff]; simp)
      exact this
    · exact coherentAt_of_mass_eq_zero C B d h0.symm m
  · rintro h D ⟨d, hd, rfl⟩ _ C' hC'
    rw [agreesOff_singleton_iff] at hC'
    rw [hC']
    exact h d (by simpa using hd) (C' d)

/-- **Antitone in refinement (HA-9′ Axis I)**: if every patient of `𝓜'` lies inside a patient of
`𝓜`, conflict-freeness for `𝓜` implies it for `𝓜'`.
Source: `repair/harmony.md` HA-9′ ("conflict-freeness is antitone in the refinement order of `𝓜`
(a coarser patient may revise any subset)") | dp-cf-2-054
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem conflictFree_antitone {𝓜 𝓜' : Set (Finset ι)} (hfine : ∀ D' ∈ 𝓜', ∃ D ∈ 𝓜, D' ⊆ D)
    (h : ConflictFree C B 𝓜) : ConflictFree C B 𝓜' := by
  rw [conflictFree_iff_coalition_nash] at h ⊢
  intro D' hD' hpos C' hC'
  obtain ⟨D, hD, hsub⟩ := hfine D' hD'
  have hpos' : 0 < mass C B (occSet D B) :=
    lt_of_lt_of_le hpos (mass_mono C B (occSet_mono hsub B))
  exact h D hD hpos' C' fun d hd => hC' d fun hmem => hd (hsub hmem)

end def23

end Cleanroom.Decision.DpLocalOpt
