import Cleanroom.Corrigibility.LegitNegPricing.Basic

/-!
# Managing the news: B2's threshold, B3/B4's extremal voiding, B5's two prices

Package `legit-neg-pricing`, targets 2–4 (load-bearing 1). Sources: `clusters/B/NEGATIVES.md`
B2–B5, `clusters/B/VERIFY.md` (B2–B5 survive), `clusters/B/fixtures/fx_conditioning.py`
(`voiding_family`, B2, B3), `fx_cdot.py` (B5), pinned by [[corr-legit-neg-inventory]] items
016–018.

Everything is over `voidingFamily prior hn hs x p w : Problem S (Option (ProperSub S))` of
`legit-neg-static`: `none` keeps legitimacy everywhere with numbers `x`; `some B` voids on the
proper non-empty `B`, keeps `x − p` off `B`, and the humans value the void terminals at `w`.
Conditional expectations are `Problem.Hcond` (junk `/0`; every headline carries the positivity
of the mass it divides by). The null convention is exclusion (`P2 = none` at `P(L | a) = 0`).
-/

namespace Cleanroom.Corrigibility.LegitNegPricing

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

section VoidingFamily

variable {S : Type} [Fintype S] [DecidableEq S] (prior : S → ℚ) (hn : ∀ s, 0 ≤ prior s)
  (hs : ∑ s, prior s = 1) (x : S → ℚ) (p w : ℚ)

/-- The event "the state lies in `B`", as a `Bool` event on the states.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def inB (B : ProperSub S) : S → Bool := fun s => decide (s ∈ B.1)

/-- The complementary event "the state is kept" (`= !inB B`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def keptB (B : ProperSub S) : S → Bool := fun s => !decide (s ∈ B.1)

/-- `keptB_eq_not_inB`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma keptB_eq_not_inB (B : ProperSub S) : keptB B = fun s => !inB B s := rfl

/-- `vf_leg_none`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma vf_leg_none (s : S) : (voidingFamily prior hn hs x p w).leg s none = true := rfl

/-- `vf_leg_some`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma vf_leg_some (s : S) (B : ProperSub S) :
    (voidingFamily prior hn hs x p w).leg s (some B) = keptB B s := rfl

/-- `vf_u_none`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma vf_u_none (s : S) : (voidingFamily prior hn hs x p w).u s none = x s := rfl

/-- `vf_u_some`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma vf_u_some (s : S) (B : ProperSub S) :
    (voidingFamily prior hn hs x p w).u s (some B) = if s ∈ B.1 then w else x s - p := rfl

/-- `vf_prior`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma vf_prior : (voidingFamily prior hn hs x p w).prior = prior := rfl

/-- `P(L | keep) = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma vf_PL_none : (voidingFamily prior hn hs x p w).PL none = 1 := by
  simp [Problem.PL, Problem.mass, hs]

/-- `P(L | void B) = π(¬B)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma vf_PL_some (B : ProperSub S) :
    (voidingFamily prior hn hs x p w).PL (some B) = (voidingFamily prior hn hs x p w).mass (keptB B) :=
  rfl

/-- `π(¬B) = 1 − π(B)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma vf_mass_keptB (B : ProperSub S) :
    (voidingFamily prior hn hs x p w).mass (keptB B)
      = 1 - (voidingFamily prior hn hs x p w).mass (inB B) := by
  rw [keptB_eq_not_inB]; exact (voidingFamily prior hn hs x p w).mass_not (inB B)

/-- `H keep = ∑ s, π s · x s`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma vf_H_none : (voidingFamily prior hn hs x p w).H none = ∑ s, prior s * x s := rfl

/-- `P1 (S1 u) keep = H keep` (`keep` is legitimate everywhere).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma vf_P1_S1_none :
    (voidingFamily prior hn hs x p w).P1 (S1 (voidingFamily prior hn hs x p w).u) none
      = (voidingFamily prior hn hs x p w).H none :=
  (voidingFamily prior hn hs x p w).P1_S1_eq_H_of_allLeg none fun _ => rfl

/-- `P1 (S1 u) (void B) = ∑_{s ∉ B} π s x s − p · π(¬B)`: cdot reads only the kept states.
Source: [[corr-legit-neg-inventory]] item 016 (B2)
Kind: L
Fidelity: exact -/
lemma vf_P1_S1_some (B : ProperSub S) :
    (voidingFamily prior hn hs x p w).P1 (S1 (voidingFamily prior hn hs x p w).u) (some B)
      = (∑ s, prior s * ind (keptB B s) * x s)
        - p * (voidingFamily prior hn hs x p w).mass (keptB B) := by
  unfold Problem.P1 Problem.mass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [S1_apply, vf_leg_some, vf_u_some, vf_prior, keptB]
  by_cases h : s ∈ B.1 <;> simp [h] ; ring

/-- `H keep` split over `B` and its complement.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma vf_H_none_split (B : ProperSub S) :
    (voidingFamily prior hn hs x p w).H none
      = (∑ s, prior s * ind (inB B s) * x s) + ∑ s, prior s * ind (keptB B s) * x s :=
  (voidingFamily prior hn hs x p w).W_split _ (inB B) none

/-- **B2, the value of voiding `B` under conditioning.** `P2 (S1 u) (void B) = 𝔼[x | ¬B] − p`
whenever the kept mass is positive: conditioning sees only the kept states' numbers, penalised.
Exclusion convention (`none` when `π(¬B) = 0`, which the hypothesis excludes).
Source: [[corr-legit-neg-inventory]] item 016 (B2); NEGATIVES B2
Kind: P
Fidelity: exact
Hyps: (a) `π(¬B) ≠ 0` is the source's `0 < π(B) < 1` -/
theorem P2_void_eq (B : ProperSub S)
    (hk : (voidingFamily prior hn hs x p w).mass (keptB B) ≠ 0) :
    (voidingFamily prior hn hs x p w).P2 (S1 (voidingFamily prior hn hs x p w).u) (some B)
      = some ((voidingFamily prior hn hs x p w).Hcond (keptB B) none - p) := by
  rw [P2_of_ne _ _ _ (by rw [vf_PL_some]; exact hk), vf_P1_S1_some, vf_PL_some]
  congr 1
  unfold Problem.Hcond
  simp only [vf_u_none, vf_prior]
  rw [sub_div, mul_div_cancel_right₀ _ hk]

/-- **B2, the value of keeping.** `P2 (S1 u) keep = H keep` (`keep` is fully legitimate).
Exclusion convention (defined: `P(L | keep) = 1`).
Source: [[corr-legit-neg-inventory]] item 016 (B2)
Kind: L
Fidelity: exact -/
theorem P2_keep_eq :
    (voidingFamily prior hn hs x p w).P2 (S1 (voidingFamily prior hn hs x p w).u) none
      = some ((voidingFamily prior hn hs x p w).H none) := by
  rw [P2_of_ne _ _ _ (by rw [vf_PL_none]; exact one_ne_zero), vf_P1_S1_none, vf_PL_none, div_one]

/-- `H keep = π(B) 𝔼[x | B] + π(¬B) 𝔼[x | ¬B]` when both masses are positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma vf_H_none_eq_mix (B : ProperSub S)
    (hB : (voidingFamily prior hn hs x p w).mass (inB B) ≠ 0)
    (hk : (voidingFamily prior hn hs x p w).mass (keptB B) ≠ 0) :
    (voidingFamily prior hn hs x p w).H none
      = (voidingFamily prior hn hs x p w).mass (inB B)
          * (voidingFamily prior hn hs x p w).Hcond (inB B) none
        + (voidingFamily prior hn hs x p w).mass (keptB B)
          * (voidingFamily prior hn hs x p w).Hcond (keptB B) none := by
  rw [vf_H_none_split prior hn hs x p w B]
  unfold Problem.Hcond
  simp only [vf_u_none, vf_prior]
  rw [mul_div_cancel₀ _ hB, mul_div_cancel₀ _ hk]

/-- **The news threshold** `p* = π(B) (𝔼[x | ¬B] − 𝔼[x | B])` of B2.
Source: [[corr-legit-neg-inventory]] item 016 (B2)
Kind: D
Fidelity: exact -/
def newsThreshold (B : ProperSub S) : ℚ :=
  (voidingFamily prior hn hs x p w).mass (inB B)
    * ((voidingFamily prior hn hs x p w).Hcond (keptB B) none
        - (voidingFamily prior hn hs x p w).Hcond (inB B) none)

/-- **B2, the difference identity** (load-bearing 1): with `0 < π(B) < 1`,
`P2 (void B) − P2 (keep) = π(B) (𝔼[x | ¬B] − 𝔼[x | B]) − p`, on the unpacked values of
`P2_void_eq` and `P2_keep_eq`. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 016 (B2); NEGATIVES B2; VERIFY B "B2 — survives"
Kind: P
Fidelity: exact
Hyps: (a) both masses positive (the source's `0 < π(B) < 1`) -/
theorem P2_void_sub_keep (B : ProperSub S)
    (hB : (voidingFamily prior hn hs x p w).mass (inB B) ≠ 0)
    (hk : (voidingFamily prior hn hs x p w).mass (keptB B) ≠ 0) :
    ((voidingFamily prior hn hs x p w).Hcond (keptB B) none - p)
        - (voidingFamily prior hn hs x p w).H none
      = newsThreshold prior hn hs x p w B - p := by
  rw [vf_H_none_eq_mix prior hn hs x p w B hB hk, newsThreshold]
  have := vf_mass_keptB prior hn hs x p w B
  linear_combination
    (-(voidingFamily prior hn hs x p w).Hcond (keptB B) none) * this

/-- **B2, the threshold** (load-bearing 1): conditioning strictly prefers voiding `B` to keeping
iff `p < p*`, and ties iff `p = p*`. Stated on the defined values of `P2` (`P2_void_eq`,
`P2_keep_eq`), exclusion convention.
Source: [[corr-legit-neg-inventory]] item 016 (B2); NEGATIVES B2
Kind: P
Fidelity: exact
Hyps: (a) both masses positive -/
theorem P2_void_gt_keep_iff (B : ProperSub S)
    (hB : (voidingFamily prior hn hs x p w).mass (inB B) ≠ 0)
    (hk : (voidingFamily prior hn hs x p w).mass (keptB B) ≠ 0) :
    ((voidingFamily prior hn hs x p w).H none
        < (voidingFamily prior hn hs x p w).Hcond (keptB B) none - p
      ↔ p < newsThreshold prior hn hs x p w B)
    ∧ ((voidingFamily prior hn hs x p w).H none
        = (voidingFamily prior hn hs x p w).Hcond (keptB B) none - p
      ↔ p = newsThreshold prior hn hs x p w B) := by
  have h := P2_void_sub_keep prior hn hs x p w B hB hk
  constructor
  · rw [← sub_pos, h]; exact sub_pos
  · constructor <;> intro h' <;> linarith

/-- **B2 at `p = 0`**: conditioning strictly prefers voiding `B` iff the voided states score
below the kept ones, `𝔼[x | B] < 𝔼[x | ¬B]`. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 016 (B2)
Kind: C
Fidelity: exact
Hyps: (a) both masses positive -/
theorem P2_void_gt_keep_iff_zero (B : ProperSub S)
    (hB : (voidingFamily prior hn hs x 0 w).mass (inB B) ≠ 0)
    (hk : (voidingFamily prior hn hs x 0 w).mass (keptB B) ≠ 0) :
    (voidingFamily prior hn hs x 0 w).H none < (voidingFamily prior hn hs x 0 w).Hcond (keptB B) none
      ↔ (voidingFamily prior hn hs x 0 w).Hcond (inB B) none
          < (voidingFamily prior hn hs x 0 w).Hcond (keptB B) none := by
  have h := (P2_void_gt_keep_iff prior hn hs x 0 w B hB hk).1
  rw [sub_zero] at h
  rw [h, newsThreshold]
  have hBpos : 0 < (voidingFamily prior hn hs x 0 w).mass (inB B) :=
    lt_of_le_of_ne ((voidingFamily prior hn hs x 0 w).mass_nonneg _) (Ne.symm hB)
  constructor
  · intro h'; linarith [(mul_pos_iff_of_pos_left hBpos).1 h']
  · intro h'; exact mul_pos hBpos (by linarith)

/-- **B2, the cleared form** (lemma, no positivity needed): multiplied through by `π(¬B)`,
`P1 (void B) − π(¬B) · H keep = π(B) ∑_{¬B} π x − π(¬B) ∑_{B} π x − p π(¬B)`.
Source: [[corr-legit-neg-inventory]] item 016 (B2)
Kind: L
Fidelity: exact -/
theorem vf_P1_void_sub_cleared (B : ProperSub S) :
    (voidingFamily prior hn hs x p w).P1 (S1 (voidingFamily prior hn hs x p w).u) (some B)
        - (voidingFamily prior hn hs x p w).mass (keptB B) * (voidingFamily prior hn hs x p w).H none
      = (voidingFamily prior hn hs x p w).mass (inB B) * (∑ s, prior s * ind (keptB B s) * x s)
        - (voidingFamily prior hn hs x p w).mass (keptB B) * (∑ s, prior s * ind (inB B s) * x s)
        - p * (voidingFamily prior hn hs x p w).mass (keptB B) := by
  rw [vf_P1_S1_some, vf_H_none_split prior hn hs x p w B]
  have := vf_mass_keptB prior hn hs x p w B
  linear_combination (-(∑ s, prior s * ind (keptB B s) * x s)) * this

/-! ### B3: the extremal voiding, and B5: cdot's price -/

section Max

variable [Nonempty S]

/-- `max_s x s` over the (non-empty) state space.
Source: [[corr-legit-neg-inventory]] item 017 (B3)
Kind: D
Fidelity: exact -/
def xmax : ℚ := univ.sup' univ_nonempty x

omit [DecidableEq S] in
/-- `le_xmax`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma le_xmax (s : S) : x s ≤ xmax x := Finset.le_sup' x (mem_univ s)

omit [DecidableEq S] in
/-- `xmax_attained`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma xmax_attained : ∃ s, x s = xmax x := by
  obtain ⟨s, -, hs⟩ := Finset.exists_mem_eq_sup' univ_nonempty x
  exact ⟨s, hs.symm⟩

/-- The kept-state conditional mean of `x` never exceeds `max x`: hence, with `p = 0`,
`P2 (void B) ≤ some (max x)` for every `B` (B3's upper bound, on the value of `P2_void_eq`).
Source: [[corr-legit-neg-inventory]] item 017 (B3)
Kind: P
Fidelity: exact
Hyps: (a) positive kept mass -/
theorem Hcond_kept_le_xmax (B : ProperSub S)
    (hk : 0 < (voidingFamily prior hn hs x p w).mass (keptB B)) :
    (voidingFamily prior hn hs x p w).Hcond (keptB B) none ≤ xmax x := by
  unfold Problem.Hcond
  simp only [vf_u_none, vf_prior]
  rw [div_le_iff₀ hk]
  unfold Problem.mass
  simp only [vf_prior]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  have h0 : 0 ≤ prior s * ind (keptB B s) := mul_nonneg (hn s) (ind_nonneg _)
  calc prior s * ind (keptB B s) * x s ≤ prior s * ind (keptB B s) * xmax x :=
        mul_le_mul_of_nonneg_left (le_xmax x s) h0
    _ = xmax x * (prior s * ind (keptB B s)) := by ring

/-- The kept-state mean attains `max x` iff every kept state of positive prior attains it.
Source: [[corr-legit-neg-inventory]] item 017 (B3); VERIFY B "B3"
Kind: P
Fidelity: exact (qualified by positive prior, which the source leaves implicit)
Hyps: (a) positive kept mass -/
theorem Hcond_kept_eq_xmax_iff (B : ProperSub S)
    (hk : 0 < (voidingFamily prior hn hs x p w).mass (keptB B)) :
    (voidingFamily prior hn hs x p w).Hcond (keptB B) none = xmax x
      ↔ ∀ s, keptB B s = true → 0 < prior s → x s = xmax x := by
  unfold Problem.Hcond
  simp only [vf_u_none, vf_prior]
  rw [div_eq_iff hk.ne']
  have hmass : (voidingFamily prior hn hs x p w).mass (keptB B)
      = ∑ s, prior s * ind (keptB B s) := rfl
  rw [hmass, Finset.mul_sum]
  have key : (∑ s, prior s * ind (keptB B s) * x s) = ∑ s, xmax x * (prior s * ind (keptB B s))
      ↔ ∑ s, prior s * ind (keptB B s) * (xmax x - x s) = 0 := by
    have hsum : ∑ s, prior s * ind (keptB B s) * (xmax x - x s)
        = (∑ s, xmax x * (prior s * ind (keptB B s))) - ∑ s, prior s * ind (keptB B s) * x s := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hsum, sub_eq_zero, eq_comm]
  rw [key, Finset.sum_eq_zero_iff_of_nonneg (fun s _ =>
    mul_nonneg (mul_nonneg (hn s) (ind_nonneg _)) (sub_nonneg.2 (le_xmax x s)))]
  constructor
  · intro h s hks hps
    have := h s (mem_univ s)
    rw [hks, ind_true, mul_one, mul_eq_zero] at this
    rcases this with h1 | h1
    · exact absurd h1 hps.ne'
    · linarith
  · intro h s _
    by_cases hks : keptB B s = true
    · by_cases hps : 0 < prior s
      · rw [h s hks hps]; ring
      · have : prior s = 0 := le_antisymm (not_lt.1 hps) (hn s)
        simp [this]
    · simp [Bool.not_eq_true] at hks; simp [hks]

/-- `B* = {s | x s < max x}`, a proper non-empty subset whenever `x` is not constant at its
maximum: the extremal voiding of B3.
Source: [[corr-legit-neg-inventory]] item 017 (B3)
Kind: D
Fidelity: exact -/
def Bstar (h : ∃ s, x s < xmax x) : ProperSub S :=
  ⟨univ.filter fun s => x s < xmax x,
    by obtain ⟨s, hs⟩ := h; exact ⟨s, by simp [hs]⟩,
    by
      intro heq
      obtain ⟨t, ht⟩ := xmax_attained x
      have : t ∈ univ.filter fun s => x s < xmax x := by rw [heq]; exact mem_univ t
      simp only [mem_filter, mem_univ, true_and] at this
      exact absurd ht this.ne⟩

/-- `mem_Bstar`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_Bstar (h : ∃ s, x s < xmax x) (s : S) : s ∈ (Bstar x h).1 ↔ x s < xmax x := by
  simp [Bstar]

/-- **B3, the extremal voiding attains the maximum**: with `p = 0`, voiding `B*` scores
`P2 = max x` — the state space except its best states. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 017 (B3); NEGATIVES B3
Kind: P
Fidelity: exact
Hyps: (a) `x` not constant at its max (so `B*` is proper and non-empty); positive kept mass -/
theorem P2_Bstar_eq_xmax (h : ∃ s, x s < xmax x)
    (hk : 0 < (voidingFamily prior hn hs x 0 w).mass (keptB (Bstar x h))) :
    (voidingFamily prior hn hs x 0 w).P2 (S1 (voidingFamily prior hn hs x 0 w).u)
      (some (Bstar x h)) = some (xmax x) := by
  rw [P2_void_eq prior hn hs x 0 w _ hk.ne', sub_zero]
  congr 1
  rw [Hcond_kept_eq_xmax_iff prior hn hs x 0 w _ hk]
  intro s hks _
  simp only [keptB, Bool.not_eq_true', decide_eq_false_iff_not, mem_Bstar, not_lt] at hks
  exact le_antisymm (le_xmax x s) hks

/-- **B3, every optimal voiding set contains `B*`** (on states of positive prior): if voiding
`B` attains `max x`, every sub-maximal state of positive prior is voided.
Source: VERIFY B "B3 — survives"
Kind: C
Fidelity: exact (positive-prior qualification)
Hyps: (a) positive kept mass -/
theorem Bstar_subset_of_optimal (B : ProperSub S)
    (hk : 0 < (voidingFamily prior hn hs x 0 w).mass (keptB B))
    (hopt : (voidingFamily prior hn hs x 0 w).Hcond (keptB B) none = xmax x)
    (s : S) (hps : 0 < prior s) (hlt : x s < xmax x) : s ∈ B.1 := by
  rw [Hcond_kept_eq_xmax_iff prior hn hs x 0 w B hk] at hopt
  by_contra hsB
  have := hopt s (by simp [keptB, hsB]) hps
  exact absurd this hlt.ne

end Max

/-- **B3/B5, cdot's price**: with `p = 0`, `P1 (void B) = P1 keep − 𝔼[1_B x]` — voiding `B`
costs cdot exactly the score it would have earned there (the chat's "protection proportional
to the score", as an identity).
Source: [[corr-legit-neg-inventory]] items 017 (B3), 018 (B5); NEGATIVES B5
Kind: L
Fidelity: exact -/
theorem P1_void_eq_keep_sub (B : ProperSub S) :
    (voidingFamily prior hn hs x 0 w).P1 (S1 (voidingFamily prior hn hs x 0 w).u) (some B)
      = (voidingFamily prior hn hs x 0 w).P1 (S1 (voidingFamily prior hn hs x 0 w).u) none
        - ∑ s, prior s * ind (inB B s) * x s := by
  rw [vf_P1_S1_some, vf_P1_S1_none, vf_H_none_split prior hn hs x 0 w B]; ring

/-- **B3, cdot never strictly prefers a pure voiding** when the voided scores are at or above
the floor: `P1 (void B) ≤ P1 keep`, with equality iff `x = 0` on every voided state of positive
prior.
Source: [[corr-legit-neg-inventory]] item 017 (B3)
Kind: P
Fidelity: exact (positive-prior qualification)
Hyps: (a) `0 ≤ x` on `B` (the source's range assumption) -/
theorem P1_void_le_keep (B : ProperSub S) (hx : ∀ s ∈ B.1, 0 ≤ x s) :
    (voidingFamily prior hn hs x 0 w).P1 (S1 (voidingFamily prior hn hs x 0 w).u) (some B)
        ≤ (voidingFamily prior hn hs x 0 w).P1 (S1 (voidingFamily prior hn hs x 0 w).u) none
    ∧ ((voidingFamily prior hn hs x 0 w).P1 (S1 (voidingFamily prior hn hs x 0 w).u) (some B)
        = (voidingFamily prior hn hs x 0 w).P1 (S1 (voidingFamily prior hn hs x 0 w).u) none
      ↔ ∀ s ∈ B.1, 0 < prior s → x s = 0) := by
  rw [P1_void_eq_keep_sub]
  have hnn : ∀ s ∈ (univ : Finset S), 0 ≤ prior s * ind (inB B s) * x s := by
    intro s _
    by_cases h : s ∈ B.1
    · simp only [inB, h, decide_true, ind_true, mul_one]; exact mul_nonneg (hn s) (hx s h)
    · simp [inB, h]
  constructor
  · linarith [Finset.sum_nonneg hnn]
  · rw [sub_eq_self, Finset.sum_eq_zero_iff_of_nonneg hnn]
    constructor
    · intro h s hsB hps
      have := h s (mem_univ s)
      simp only [inB, hsB, decide_true, ind_true, mul_one, mul_eq_zero] at this
      rcases this with h1 | h1
      · exact absurd h1 hps.ne'
      · exact h1
    · intro h s _
      by_cases hsB : s ∈ B.1
      · by_cases hps : 0 < prior s
        · simp [h s hsB hps]
        · have : prior s = 0 := le_antisymm (not_lt.1 hps) (hn s)
          simp [this]
      · simp [inB, hsB]

/-- **B5, cdot's gain rule**: with a gain `G` (in `P1` units) on the kept states, cdot prefers
the voiding iff `G > 𝔼[1_B x]`.
Source: [[corr-legit-neg-inventory]] item 018 (B5); `fx_cdot.py` B5
Kind: L
Fidelity: exact -/
theorem P1_gain_rule (B : ProperSub S) (G : ℚ) :
    (voidingFamily prior hn hs x 0 w).P1 (S1 (voidingFamily prior hn hs x 0 w).u) none
        < (voidingFamily prior hn hs x 0 w).P1 (S1 (voidingFamily prior hn hs x 0 w).u) (some B) + G
      ↔ ∑ s, prior s * ind (inB B s) * x s < G := by
  rw [P1_void_eq_keep_sub]; constructor <;> intro h <;> linarith

/-- **B5, conditioning's price**: with a gain `G` (in `P1` units) on the kept states, P2 prefers
the voiding iff `G > π(B) π(¬B) (𝔼[x | B] − 𝔼[x | ¬B])`, on the defined values (exclusion
convention).
Source: [[corr-legit-neg-inventory]] item 018 (B5); `fx_cdot.py` B5 (`priceP2`)
Kind: P
Fidelity: exact
Hyps: (a) both masses positive -/
theorem P2_gain_rule (B : ProperSub S) (G : ℚ)
    (hB : (voidingFamily prior hn hs x 0 w).mass (inB B) ≠ 0)
    (hk : (voidingFamily prior hn hs x 0 w).mass (keptB B) ≠ 0) :
    (voidingFamily prior hn hs x 0 w).H none
        < ((voidingFamily prior hn hs x 0 w).P1 (S1 (voidingFamily prior hn hs x 0 w).u) (some B) + G)
            / (voidingFamily prior hn hs x 0 w).mass (keptB B)
      ↔ (voidingFamily prior hn hs x 0 w).mass (inB B) * (voidingFamily prior hn hs x 0 w).mass (keptB B)
          * ((voidingFamily prior hn hs x 0 w).Hcond (inB B) none
              - (voidingFamily prior hn hs x 0 w).Hcond (keptB B) none) < G := by
  have hkpos : 0 < (voidingFamily prior hn hs x 0 w).mass (keptB B) :=
    lt_of_le_of_ne ((voidingFamily prior hn hs x 0 w).mass_nonneg _) (Ne.symm hk)
  rw [lt_div_iff₀ hkpos, vf_P1_S1_some, vf_H_none_eq_mix prior hn hs x 0 w B hB hk]
  have hK : (voidingFamily prior hn hs x 0 w).Hcond (keptB B) none
      * (voidingFamily prior hn hs x 0 w).mass (keptB B) = ∑ s, prior s * ind (keptB B s) * x s := by
    unfold Problem.Hcond; simp only [vf_u_none, vf_prior]; rw [div_mul_cancel₀ _ hk]
  have hm := vf_mass_keptB prior hn hs x 0 w B
  have key : ((voidingFamily prior hn hs x 0 w).mass (inB B)
        * (voidingFamily prior hn hs x 0 w).Hcond (inB B) none
      + (voidingFamily prior hn hs x 0 w).mass (keptB B)
        * (voidingFamily prior hn hs x 0 w).Hcond (keptB B) none)
      * (voidingFamily prior hn hs x 0 w).mass (keptB B)
      - ((∑ s, prior s * ind (keptB B s) * x s) - 0 * (voidingFamily prior hn hs x 0 w).mass (keptB B))
      = (voidingFamily prior hn hs x 0 w).mass (inB B) * (voidingFamily prior hn hs x 0 w).mass (keptB B)
          * ((voidingFamily prior hn hs x 0 w).Hcond (inB B) none
              - (voidingFamily prior hn hs x 0 w).Hcond (keptB B) none) := by
    linear_combination ((voidingFamily prior hn hs x 0 w).mass (keptB B)
      * (voidingFamily prior hn hs x 0 w).Hcond (keptB B) none) * hm + hK
  constructor <;> intro h <;> linarith

/-- **B5, the two prices differ by `π(B) 𝔼[x]`**: `𝔼[1_B x] − π(B)π(¬B)(𝔼[x|B] − 𝔼[x|¬B]) = π(B) H keep`.
Source: [[corr-legit-neg-inventory]] item 018 (B5)
Kind: L
Fidelity: exact
Hyps: (a) both masses positive -/
theorem price_gap (B : ProperSub S)
    (hB : (voidingFamily prior hn hs x 0 w).mass (inB B) ≠ 0)
    (hk : (voidingFamily prior hn hs x 0 w).mass (keptB B) ≠ 0) :
    (∑ s, prior s * ind (inB B s) * x s)
        - (voidingFamily prior hn hs x 0 w).mass (inB B) * (voidingFamily prior hn hs x 0 w).mass (keptB B)
          * ((voidingFamily prior hn hs x 0 w).Hcond (inB B) none
              - (voidingFamily prior hn hs x 0 w).Hcond (keptB B) none)
      = (voidingFamily prior hn hs x 0 w).mass (inB B) * (voidingFamily prior hn hs x 0 w).H none := by
  rw [vf_H_none_eq_mix prior hn hs x 0 w B hB hk]
  have hBB : (voidingFamily prior hn hs x 0 w).mass (inB B)
      * (voidingFamily prior hn hs x 0 w).Hcond (inB B) none = ∑ s, prior s * ind (inB B s) * x s := by
    unfold Problem.Hcond; simp only [vf_u_none, vf_prior]; rw [mul_div_cancel₀ _ hB]
  have hm := vf_mass_keptB prior hn hs x 0 w B
  linear_combination (-1 : ℚ) * hBB
    - ((voidingFamily prior hn hs x 0 w).mass (inB B)
        * (voidingFamily prior hn hs x 0 w).Hcond (inB B) none) * hm

end VoidingFamily

/-! ### B4: the wild gamble (N+ for B3) -/

/-- B4's four equiprobable outcomes scoring `1, 3/5, 2/5, 1/5`; the arm voids the three worst.
Source: [[corr-legit-neg-inventory]] item 017 (B4); NEGATIVES B4
Kind: D
Fidelity: exact -/
abbrev b4 (w : ℚ) : Problem (Fin 4) (Option (ProperSub (Fin 4))) :=
  voidingFamily (fun _ => 1/4) (fun _ => by norm_num) (by simp) ![1, 3/5, 2/5, 1/5] 0 w

/-- The arm: void on `{1, 2, 3}`.
Source: [[corr-legit-neg-inventory]] item 017 (B4)
Kind: D
Fidelity: exact -/
def b4arm : ProperSub (Fin 4) := ⟨{1, 2, 3}, by decide, by decide⟩

/-- **B4 (N+ for B3)**: `P2 (arm) = 1 > 11/20 = P2 (keep)`, `H (arm) = 1/4 + (3/4) w`,
`P(L | arm) = 1/4`. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 017 (B4); VERIFY B "B4 — survives"
Kind: N+
Fidelity: exact -/
theorem B4_wild_gamble (w : ℚ) :
    (b4 w).P2 (S1 (b4 w).u) (some b4arm) = some 1
    ∧ (b4 w).P2 (S1 (b4 w).u) none = some (11/20)
    ∧ (b4 w).H (some b4arm) = 1/4 + 3/4 * w
    ∧ (b4 w).PL (some b4arm) = 1/4 := by
  have hk : (b4 w).mass (keptB b4arm) = 1/4 := by
    simp +decide [Problem.mass, keptB, b4arm, Fin.sum_univ_four] <;> norm_num
  have hk' : (b4 w).mass (keptB b4arm) ≠ 0 := by rw [hk]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [P2_void_eq _ _ _ _ _ _ b4arm hk', sub_zero]
    congr 1
    simp +decide [Problem.Hcond, Problem.mass, keptB, b4arm, Fin.sum_univ_four] <;> norm_num
  · rw [P2_keep_eq, vf_H_none]
    simp [Fin.sum_univ_four] <;> norm_num
  · simp +decide [Problem.H, Problem.W, EU, b4arm, Fin.sum_univ_four] <;> ring
  · rw [vf_PL_some, hk]

/-! ### B2's toy corollaries: the chat's `(1 − v)/2`, and the hybrid's `π_g δ + π_b (1 − v)` -/

/-- **B2 on C's toy** (`toyC v p 0`: the penalty in `u`, hence in `H` — VERIFY B on B2):
conditioning strictly prefers the voiding `a₁` iff `p < (1 − v)/2`, ties iff `p = (1 − v)/2`.
Exclusion convention (both `P(L | a) > 0` here).
Source: [[corr-legit-neg-inventory]] item 016 (B2, the chat's threshold); `fx_conditioning.py` B2
Kind: P
Fidelity: exact -/
theorem toyC_P2_news (v p : ℚ) :
    (argmaxOpt ((toyC v p 0).P2 (S1 (toyC v p 0).u)) = {1} ↔ p < (1 - v) / 2)
    ∧ (argmaxOpt ((toyC v p 0).P2 (S1 (toyC v p 0).u)) = univ ↔ p = (1 - v) / 2) := by
  have hPL : ∀ a, (toyC v p 0).PL a ≠ 0 :=
    Fin.forall_fin_two.2 ⟨by rw [toyC, toyB_PL_zero]; norm_num, by rw [toyC, toyB_PL_one]; norm_num⟩
  rw [argmaxOpt_P2_eq_argmax_div _ _ hPL, argmax_fin2_eq_one_iff, argmax_fin2_eq_univ_iff]
  simp only [toyC, toyB_PL_zero, toyB_PL_one, toyB_P1_S1_zero, toyB_P1_S1_one]
  constructor <;> constructor <;> intro h <;> norm_num at h ⊢ <;> linarith

/-- **B2 on C's toy, cdot**: `P1` strictly keeps iff `v + p > 0`, ties only at `v = p = 0`
(the assertion C1's fixture never makes, inventory 033 — made here).
Source: [[corr-legit-neg-inventory]] items 016, 033; `fx_conditioning.py` B2 ("keeps iff v + p > 0")
Kind: P
Fidelity: exact -/
theorem toyC_P1_keeps_iff (v p : ℚ) :
    (argmax ((toyC v p 0).P1 (S1 (toyC v p 0).u)) = {0} ↔ 0 < v + p)
    ∧ (argmax ((toyC v p 0).P1 (S1 (toyC v p 0).u)) = univ ↔ v + p = 0) := by
  rw [argmax_fin2_eq_zero_iff, argmax_fin2_eq_univ_iff]
  simp only [toyC, toyB_P1_S1_zero, toyB_P1_S1_one]
  constructor <;> constructor <;> intro h <;> norm_num at h ⊢ <;> linarith

/-- **B2 on the hybrid toy** (`toyB v w (1 − δ) 1 π_b` with the penalty in `V` only, `H` clean):
conditioning strictly prefers `a₁` iff `p < π_g δ + π_b (1 − v)` — the B16 threshold, the
chat's `(1 − v)/2` at `δ = 0`, `π_b = 1/2`. Exclusion convention (`π_b < 1` keeps `a₁` defined).
Source: [[corr-legit-neg-inventory]] item 016 (B2, "with δ > 0"); NEGATIVES B16
Kind: P
Fidelity: exact
Hyps: (a) `π_b < 1` -/
theorem hybrid_P2_news (v w δ πb p : ℚ) (h0 : 0 ≤ πb) (h1 : πb < 1) :
    argmaxOpt ((toyB v w (1 - δ) 1 πb h0 h1.le).P2 (hybridV (toyB v w (1 - δ) 1 πb h0 h1.le) p))
      = {1} ↔ p < (1 - πb) * δ + πb * (1 - v) := by
  have hPL : ∀ a, (toyB v w (1 - δ) 1 πb h0 h1.le).PL a ≠ 0 :=
    Fin.forall_fin_two.2 ⟨by rw [toyB_PL_zero]; norm_num, by rw [toyB_PL_one]; linarith⟩
  rw [argmaxOpt_P2_eq_argmax_div _ _ hPL, argmax_fin2_eq_one_iff]
  simp only [toyB_PL_zero, toyB_PL_one, toyB_P1_hybrid_zero, toyB_P1_hybrid_one, div_one]
  have hg : 0 < 1 - πb := by linarith
  rw [mul_div_cancel_left₀ _ hg.ne']
  constructor <;> intro h <;> nlinarith

/-- **B2's N+ witness**: the fixture's grid point `v = 1/10, p = 0` on C's toy: conditioning
strictly voids (`P2 a₁ = 1 > 11/20`) while `H` strictly keeps. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 016; NEGATIVES C1 worked point
Kind: N+
Fidelity: exact -/
theorem B2_witness :
    argmaxOpt ((toyC (1/10) 0 0).P2 (S1 (toyC (1/10) 0 0).u)) = {1}
    ∧ argmax (toyC (1/10) 0 0).H = {0} := by
  constructor
  · exact (toyC_P2_news (1/10) 0).1.2 (by norm_num)
  · rw [argmax_fin2_eq_zero_iff, toyC, toyB_H_zero, toyB_H_one]; norm_num

end Cleanroom.Corrigibility.LegitNegPricing
