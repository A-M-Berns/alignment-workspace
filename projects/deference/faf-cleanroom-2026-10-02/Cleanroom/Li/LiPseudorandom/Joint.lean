import Cleanroom.Li.LiPseudorandom.Family
import Cleanroom.Li.LiPseudorandom.Lift

/-!
# `li-pseudorandom` — T9: jointly pseudorandom families (extension)

Three forms of T9, all proved:

* **Varied target.** `diag_pseudorandom` (T1) is stated with a day-varying target `p : ℕ → ℝ`,
  and `variedPseudorandom_of_causal` (`Fixed.lean`) gives FAF's `VariedPseudorandom` at a
  rational `q : ℕ → ℚ` relative to the market the family builds. At the LIA of record with the
  alternating target `pairTarget p₁ p₂`, the combined two-family stream is `pairTarget`-varied
  pseudorandom (`truthStar₂_variedPseudorandom`).

* **Two families with cross-reading.** The two-family stream of record `truthStar₂` is the
  diagonal over the **disjoint union** of three rule families (`twoFamilyRules`, via
  `unionRules`): the builder rules of every P-generable weighting (as `diagBuilder`), their even
  lifts and their odd lifts (`lift evenSched`, `lift oddSched`, `Lift.lean`). Its even subfamily
  is pseudorandom with frequency `p₁`, and its odd subfamily with frequency `p₂`, relative to the
  LIA over the process deciding *both* subfamilies, for every `f` — against every P-generable
  weighting on that market, which may read the other family's decided atoms (they are legal price
  features): `truthStar₂_even_pseudorandom`, `truthStar₂_odd_pseudorandom` (paper forms
  `…_all`). This is what `def-dose-response`'s `k` coins and anson-050's product closure need.

* **Countably many families at once** (the mandate's first sentence). `truthStarω a g q` places
  member `m` of family `r` on day `Nat.pair r m` and diagonalizes over the disjoint union of the
  builder rules and the lifts of every family (`omegaRules`); family `r` is pseudorandom with
  frequency `q r` relative to the LIA over the process deciding all of them, for every `r` and
  every `f` (`truthStarω_pseudorandom`), and the combined stream is `omegaTarget q`-varied
  pseudorandom (`truthStarω_variedPseudorandom`).

History. Before repair round 2 `truthStar₂` diagonalized over the builder rules only and the
cross-reading form was left OPEN with a diagnosis blaming a missing FAF closure property
(P-generability of the day-reindexed weighting). The round-2 fidelity audit (B1) showed, by a
probe, that no such property is needed: T1 quantifies over arbitrary strictly causal rules, and
the lift of a builder rule is one. The obstacle was the package's own rule family, and the
mandate's construction — the disjoint union — was the right one. `truthStar₂` is not a definition
of record (the mandate lists `truthR`, `CausalRule`, `diag`, `atomDP`, `atomFamily`, `truth⋆`), so
the redefinition touches nothing a dependent imports from `Family.lean`; the statement of
`truthStar₂_variedPseudorandom` and the witness `truthStar₂_not_eventuallyConst`
(`Witnesses.lean`) are unchanged.
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction Filter Topology

/-! ## The alternating target -/

/-- The alternating target: `p₁` on even days, `p₂` on odd days.
Source: mandate T9
Kind: D
Fidelity: exact -/
noncomputable def pairTarget (p₁ p₂ : ℚ) : ℕ → ℚ := fun n => if Even n then p₁ else p₂

/-- The alternating target lies in `[0,1]` when both values do.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairTarget_mem {p₁ p₂ : ℚ} (h₁ : 0 ≤ p₁ ∧ p₁ ≤ 1) (h₂ : 0 ≤ p₂ ∧ p₂ ≤ 1) (n : ℕ) :
    0 ≤ ((pairTarget p₁ p₂ n : ℚ) : ℝ) ∧ ((pairTarget p₁ p₂ n : ℚ) : ℝ) ≤ 1 := by
  unfold pairTarget
  split_ifs
  · exact ⟨by exact_mod_cast h₁.1, by exact_mod_cast h₁.2⟩
  · exact ⟨by exact_mod_cast h₂.1, by exact_mod_cast h₂.2⟩

/-- The alternating target is `p₁` on even days.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairTarget_even (p₁ p₂ : ℚ) (m : ℕ) :
    ((pairTarget p₁ p₂ (2 * m) : ℚ) : ℝ) = (p₁ : ℝ) := by
  unfold pairTarget
  rw [if_pos (even_two_mul m)]

/-- The alternating target is `p₂` on odd days.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairTarget_odd (p₁ p₂ : ℚ) (m : ℕ) :
    ((pairTarget p₁ p₂ (2 * m + 1) : ℚ) : ℝ) = (p₂ : ℝ) := by
  unfold pairTarget
  rw [if_neg (Nat.not_even_iff_odd.2 (odd_two_mul_add_one m))]

/-! ## The two-family stream -/

/-- **The rule family of the two-family diagonal**: the disjoint union (`unionRules`, indexed by
`Nat.pair`) of the builder rules of the enumeration (family `0`, as in `diagBuilder`), their even
lifts (family `1`) and their odd lifts (family `2`). The mandate's "`diag` over the disjoint union
of the rule families" for two subfamilies.
Source: mandate T9
Kind: D
Fidelity: exact -/
noncomputable def twoFamilyRules (B : (ℕ → Bool) → History) (gen : ℕ → ℕ → EF) :
    ℕ → CausalRule :=
  unionRules fun i j =>
    if i = 0 then builderRule B (gen j)
    else if i = 1 then lift evenSched B (gen j)
    else lift oddSched B (gen j)

/-- Family `0` of `twoFamilyRules`: the builder rules.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoFamilyRules_zero (B : (ℕ → Bool) → History) (gen : ℕ → ℕ → EF) (j : ℕ) :
    twoFamilyRules B gen (Nat.pair 0 j) = builderRule B (gen j) := by
  rw [twoFamilyRules, unionRules_pair]
  simp

/-- Family `1` of `twoFamilyRules`: the even lifts.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoFamilyRules_one (B : (ℕ → Bool) → History) (gen : ℕ → ℕ → EF) (j : ℕ) :
    twoFamilyRules B gen (Nat.pair 1 j) = lift evenSched B (gen j) := by
  rw [twoFamilyRules, unionRules_pair]
  simp

/-- Family `2` of `twoFamilyRules`: the odd lifts.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoFamilyRules_two (B : (ℕ → Bool) → History) (gen : ℕ → ℕ → EF) (j : ℕ) :
    twoFamilyRules B gen (Nat.pair 2 j) = lift oddSched B (gen j) := by
  rw [twoFamilyRules, unionRules_pair]
  simp

/-- With a covering enumeration, `twoFamilyRules` contains the builder rule, the even lift and
the odd lift of every P-generable weighting.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoFamilyRules_mem (B : (ℕ → Bool) → History) (gen : ℕ → ℕ → EF)
    (hcov : ∀ W, PGenerableWeighting W → ∃ k, gen k = W) (W : ℕ → EF)
    (hW : PGenerableWeighting W) :
    (∃ k, twoFamilyRules B gen k = builderRule B W) ∧
      (∃ k, twoFamilyRules B gen k = lift evenSched B W) ∧
      (∃ k, twoFamilyRules B gen k = lift oddSched B W) := by
  obtain ⟨j, rfl⟩ := hcov W hW
  exact ⟨⟨Nat.pair 0 j, twoFamilyRules_zero B gen j⟩, ⟨Nat.pair 1 j, twoFamilyRules_one B gen j⟩,
    ⟨Nat.pair 2 j, twoFamilyRules_two B gen j⟩⟩

/-- **The two-family stream of record**: the diagonal over `twoFamilyRules` at the LIA of record
and the enumeration of record, alternating target. Even members form family 1 (target `p₁`), odd
members family 2 (target `p₂`). Repair round 2: redefined over the disjoint union of the rule
families (was: over the builder rules only, which left the cross-reading form open).
Source: mandate T9
Kind: D
Fidelity: variant: rules evaluated on the prefix-built market (as `truthStar`); equal to the
mandate's diagonal under `CausalBuilder`, which `liaHistory_atomDP_causal` supplies -/
noncomputable def truthStar₂ (a g : ℕ → ℕ) (p₁ p₂ : ℚ) : ℕ → Bool :=
  diag (twoFamilyRules (fun x => liaHistory (atomDP a x g)) genWeighting)
    (fun n => (pairTarget p₁ p₂ n : ℝ))

/-- **The combined stream is `pairTarget`-varied pseudorandom** relative to the LIA over the
process deciding both families, for every `f` (the varied form of T9; the builder rules are
family `0` of `twoFamilyRules`). Statement unchanged by the repair-round-2 redefinition.
Source: mandate T9 (varied form); FAF `VariedPseudorandom`
Kind: C
Fidelity: stronger: all `f`
Hyps: (a) -/
theorem truthStar₂_variedPseudorandom (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (p₁ p₂ : ℚ)
    (h₁ : 0 ≤ p₁ ∧ p₁ ≤ 1) (h₂ : 0 ≤ p₂ ∧ p₂ ≤ 1) :
    ∀ f : DeferralFunction, VariedPseudorandom (truthR (truthStar₂ a g p₁ p₂)) (pairTarget p₁ p₂)
      f (liaHistory (atomDP a (truthStar₂ a g p₁ p₂) g)) :=
  variedPseudorandom_of_builderRule_mem (fun x => liaHistory (atomDP a x g)) g
    (liaHistory_atomDP_causal a g) hg
    (twoFamilyRules (fun x => liaHistory (atomDP a x g)) genWeighting)
    (fun W hW => (twoFamilyRules_mem _ _ genWeighting_covers W hW).1) (pairTarget p₁ p₂)
    (fun n => by unfold pairTarget; split_ifs <;> assumption)

/-- **T9, two-family form with cross-reading, paper form (even subfamily).** For every
P-generable weighting `W` divergent on the LIA over the process deciding both subfamilies — so
`W` may read the odd family's decided atoms — the `W`-weighted truth frequency of the even
members of `truthStar₂` tends to `p₁`.
Source: mandate T9; [[anson-inventory]] anson-050 (product closure); `def-dose-response` (`k` coins)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem truthStar₂_even_pseudorandom_all (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (p₁ p₂ : ℚ)
    (h₁ : 0 ≤ p₁ ∧ p₁ ≤ 1) (h₂ : 0 ≤ p₂ ∧ p₂ ≤ 1) :
    ∀ W : ℕ → EF, PGenerableWeighting W →
      DivergentWeighting W (liaHistory (atomDP a (truthStar₂ a g p₁ p₂) g)) →
      weightedAverage (fun i => (W i).denote (liaHistory (atomDP a (truthStar₂ a g p₁ p₂) g)))
        (fun n => truthR (truthStar₂ a g p₁ p₂) (2 * n)) ≈ₙ (fun _ => (p₁ : ℝ)) := by
  intro W hW hWdiv
  obtain ⟨k, hk⟩ := (twoFamilyRules_mem _ _ genWeighting_covers W hW).2.1
  exact subfamily_of_lift (liaHistory_atomDP_causal a g) hg evenSched _ _
    (pairTarget_mem h₁ h₂) (p₁ : ℝ) (pairTarget_even p₁ p₂) hW hk hWdiv

/-- **T9, two-family form with cross-reading, paper form (odd subfamily).** Symmetric to
`truthStar₂_even_pseudorandom_all`, with frequency `p₂`.
Source: mandate T9; [[anson-inventory]] anson-050; `def-dose-response`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem truthStar₂_odd_pseudorandom_all (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (p₁ p₂ : ℚ)
    (h₁ : 0 ≤ p₁ ∧ p₁ ≤ 1) (h₂ : 0 ≤ p₂ ∧ p₂ ≤ 1) :
    ∀ W : ℕ → EF, PGenerableWeighting W →
      DivergentWeighting W (liaHistory (atomDP a (truthStar₂ a g p₁ p₂) g)) →
      weightedAverage (fun i => (W i).denote (liaHistory (atomDP a (truthStar₂ a g p₁ p₂) g)))
        (fun n => truthR (truthStar₂ a g p₁ p₂) (2 * n + 1)) ≈ₙ (fun _ => (p₂ : ℝ)) := by
  intro W hW hWdiv
  obtain ⟨k, hk⟩ := (twoFamilyRules_mem _ _ genWeighting_covers W hW).2.2
  exact subfamily_of_lift (liaHistory_atomDP_causal a g) hg oddSched _ _
    (pairTarget_mem h₁ h₂) (p₂ : ℝ) (pairTarget_odd p₁ p₂) hW hk hWdiv

/-- **T9, two-family form with cross-reading (even subfamily).** The even subfamily of the
two-family stream inhabits FAF's `PseudorandomFrequency` with frequency `p₁` relative to the LIA
over the process deciding both subfamilies, for every `f`. The weightings quantified over may
read the odd family's decided atoms. Was OPEN until repair round 2 (round-2 fidelity audit B1).
Source: mandate T9; [[anson-inventory]] anson-050 (product closure); `def-dose-response` (`k` coins)
Kind: C
Fidelity: stronger: all `f`
Hyps: (a) -/
theorem truthStar₂_even_pseudorandom (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (p₁ p₂ : ℚ)
    (h₁ : 0 ≤ p₁ ∧ p₁ ≤ 1) (h₂ : 0 ≤ p₂ ∧ p₂ ≤ 1) :
    ∀ f : DeferralFunction, PseudorandomFrequency (fun n => truthR (truthStar₂ a g p₁ p₂) (2 * n))
      (p₁ : ℝ) f (liaHistory (atomDP a (truthStar₂ a g p₁ p₂) g)) :=
  pseudorandomFrequency_of_all _ _ _ (truthStar₂_even_pseudorandom_all a g hg p₁ p₂ h₁ h₂)

/-- **T9, two-family form with cross-reading (odd subfamily).** Symmetric to
`truthStar₂_even_pseudorandom`, with frequency `p₂`.
Source: mandate T9; [[anson-inventory]] anson-050; `def-dose-response`
Kind: C
Fidelity: stronger: all `f`
Hyps: (a) -/
theorem truthStar₂_odd_pseudorandom (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (p₁ p₂ : ℚ)
    (h₁ : 0 ≤ p₁ ∧ p₁ ≤ 1) (h₂ : 0 ≤ p₂ ∧ p₂ ≤ 1) :
    ∀ f : DeferralFunction,
      PseudorandomFrequency (fun n => truthR (truthStar₂ a g p₁ p₂) (2 * n + 1))
        (p₂ : ℝ) f (liaHistory (atomDP a (truthStar₂ a g p₁ p₂) g)) :=
  pseudorandomFrequency_of_all _ _ _ (truthStar₂_odd_pseudorandom_all a g hg p₁ p₂ h₁ h₂)

/-! ## Countably many families at once -/

/-- The target of countably many families: `q r` on every day of family `r` (day `n` belongs to
family `(Nat.unpair n).1`).
Source: mandate T9 ("countably many families at once")
Kind: D
Fidelity: exact -/
noncomputable def omegaTarget (q : ℕ → ℚ) : ℕ → ℚ := fun n => q (Nat.unpair n).1

/-- On day `Nat.pair r m` the target is `q r`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma omegaTarget_pair (q : ℕ → ℚ) (r m : ℕ) :
    ((omegaTarget q (Nat.pair r m) : ℚ) : ℝ) = (q r : ℝ) := by
  simp [omegaTarget, Nat.unpair_pair]

/-- The countable-family target lies in `[0,1]` when every `q r` does.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma omegaTarget_mem {q : ℕ → ℚ} (hq : ∀ r, 0 ≤ q r ∧ q r ≤ 1) (n : ℕ) :
    0 ≤ ((omegaTarget q n : ℚ) : ℝ) ∧ ((omegaTarget q n : ℚ) : ℝ) ≤ 1 :=
  ⟨by exact_mod_cast (hq _).1, by exact_mod_cast (hq _).2⟩

/-- **The rule family of countably many families**: the disjoint union of the builder rules
(family `0`) and, for every `r`, the lifts along `pairSched r` (family `r + 1`).
Source: mandate T9 ("diag over the disjoint union of the rule families")
Kind: D
Fidelity: exact -/
noncomputable def omegaRules (B : (ℕ → Bool) → History) (gen : ℕ → ℕ → EF) : ℕ → CausalRule :=
  unionRules fun i j =>
    if i = 0 then builderRule B (gen j) else lift (pairSched (i - 1)) B (gen j)

/-- Family `0` of `omegaRules`: the builder rules.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma omegaRules_zero (B : (ℕ → Bool) → History) (gen : ℕ → ℕ → EF) (j : ℕ) :
    omegaRules B gen (Nat.pair 0 j) = builderRule B (gen j) := by
  rw [omegaRules, unionRules_pair]
  simp

/-- Family `r + 1` of `omegaRules`: the lifts along `pairSched r`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma omegaRules_succ (B : (ℕ → Bool) → History) (gen : ℕ → ℕ → EF) (r j : ℕ) :
    omegaRules B gen (Nat.pair (r + 1) j) = lift (pairSched r) B (gen j) := by
  rw [omegaRules, unionRules_pair]
  simp

/-- **The countable-family stream of record**: member `m` of family `r` is day `Nat.pair r m`;
the diagonal over `omegaRules` at the LIA of record and the enumeration of record, with target
`q r` on family `r`.
Source: mandate T9 ("countably many families at once")
Kind: D
Fidelity: variant: rules evaluated on the prefix-built market (as `truthStar`); equal to the
mandate's diagonal under `CausalBuilder`, which `liaHistory_atomDP_causal` supplies -/
noncomputable def truthStarω (a g : ℕ → ℕ) (q : ℕ → ℚ) : ℕ → Bool :=
  diag (omegaRules (fun x => liaHistory (atomDP a x g)) genWeighting)
    (fun n => (omegaTarget q n : ℝ))

/-- **T9, countably many families, paper form.** For every family `r` and every P-generable
weighting `W` divergent on the LIA over the process deciding all the families — `W` may read every
other family's decided atoms — the `W`-weighted truth frequency of family `r` tends to `q r`.
Source: mandate T9 ("countably many families at once … each is pseudorandom against weightings
that read the other families' truth values")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem truthStarω_pseudorandom_all (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (q : ℕ → ℚ)
    (hq : ∀ r, 0 ≤ q r ∧ q r ≤ 1) (r : ℕ) :
    ∀ W : ℕ → EF, PGenerableWeighting W →
      DivergentWeighting W (liaHistory (atomDP a (truthStarω a g q) g)) →
      weightedAverage (fun i => (W i).denote (liaHistory (atomDP a (truthStarω a g q) g)))
        (fun m => truthR (truthStarω a g q) (Nat.pair r m)) ≈ₙ (fun _ => (q r : ℝ)) := by
  intro W hW hWdiv
  obtain ⟨j, rfl⟩ := genWeighting_covers W hW
  exact subfamily_of_lift (liaHistory_atomDP_causal a g) hg (pairSched r) _ _
    (omegaTarget_mem hq) (q r : ℝ) (omegaTarget_pair q r) hW (omegaRules_succ _ _ r j) hWdiv

/-- **T9, countably many families (FAF's predicate).** Every family `r` of `truthStarω a g q`
inhabits `PseudorandomFrequency` with frequency `q r` relative to the LIA over the process
deciding all the families, for every `f`.
Source: mandate T9 ("countably many families at once"); FAF `PseudorandomFrequency`
Kind: C
Fidelity: stronger: all `f`
Hyps: (a) -/
theorem truthStarω_pseudorandom (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (q : ℕ → ℚ)
    (hq : ∀ r, 0 ≤ q r ∧ q r ≤ 1) :
    ∀ (r : ℕ) (f : DeferralFunction),
      PseudorandomFrequency (fun m => truthR (truthStarω a g q) (Nat.pair r m)) (q r : ℝ) f
        (liaHistory (atomDP a (truthStarω a g q) g)) :=
  fun r => pseudorandomFrequency_of_all _ _ _ (truthStarω_pseudorandom_all a g hg q hq r)

/-- **The combined countable-family stream is `omegaTarget q`-varied pseudorandom** relative to
the LIA over the process deciding all the families, for every `f`.
Source: mandate T9 (varied form); FAF `VariedPseudorandom`
Kind: C
Fidelity: stronger: all `f`
Hyps: (a) -/
theorem truthStarω_variedPseudorandom (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (q : ℕ → ℚ)
    (hq : ∀ r, 0 ≤ q r ∧ q r ≤ 1) :
    ∀ f : DeferralFunction, VariedPseudorandom (truthR (truthStarω a g q)) (omegaTarget q)
      f (liaHistory (atomDP a (truthStarω a g q) g)) :=
  variedPseudorandom_of_builderRule_mem (fun x => liaHistory (atomDP a x g)) g
    (liaHistory_atomDP_causal a g) hg
    (omegaRules (fun x => liaHistory (atomDP a x g)) genWeighting)
    (fun W hW => by
      obtain ⟨j, rfl⟩ := genWeighting_covers W hW
      exact ⟨Nat.pair 0 j, omegaRules_zero _ _ j⟩)
    (omegaTarget q) (fun n => hq _)

end Cleanroom.Li.LiPseudorandom
