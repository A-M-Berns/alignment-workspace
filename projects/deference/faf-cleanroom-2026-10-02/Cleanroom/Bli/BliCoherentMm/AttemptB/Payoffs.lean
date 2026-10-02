import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# `bli-coherent-mm` (attempt B) · Payoffs: Soto's intermediate payoffs (T8, extension)

Soto's PDF 04 ("Propositional coherence") pays world shares *incrementally* as prime formulas
get decided: a share of a world `W` valuating `n` primes, `k` of which are confirmed and none
refuted, has received `1/2^(n−k)` in total; a confirmation pays `1/2^(n−k−1) − 1/2^(n−k)`, a
refutation takes back `1/2^(n−k)`. This is **not** FAF's market (FAF pays by world at the end),
so it is formalized as finite arithmetic over a decision state, disclosed `variant`:

* `World n := Fin n → Bool`, `Decision n := Fin n → Option Bool` (undecided / decided);
  `Refuted`, `confirmed`, `decided`, and the running total `payoff W s`.
* **(a)** `payoff_eq_uniform` — the running total is the uniform-completion probability of `W`
  given the decisions (`1 / |completions s|` if `W` is a completion, else `0`), the reading
  bli-soto-a-2-003 (i) gives Soto's scheme; `increment_confirm` / `increment_refute` /
  `increment_of_refuted` — Soto's three increment rules are exactly the differences of
  `payoff`, so any refinement path telescopes (`sum_increments`).
* **(b)** `payoff_full` / `bundle_full` — once every prime is decided the total is `1` for the
  true world and `0` otherwise, and a share of `φ` (the bundle of `φ`-worlds) totals `1[φ]` —
  the identity inventory item 031 claims, over a finite refinement sequence.
* **(c)** `half_forcing` — the one-step cash inequality behind 2-003 (iii): the cheaper child of
  an unrefuted world split on a fresh prime, bought at `θ < 1/2`, has immediate payoff
  `(1/2)·2^{−m}` exceeding its cost `θ · P(W)` whenever `P(W) ≤ 2^{−m}`. Stated as a per-step
  inequality, not as FAF's `Exploits`.

Sources: Soto PDF 04 pp. 1–2 (bli-soto-a-031); bli-soto-a-2-inventory 2-003;
[[bli-coherent-mm-mandate]] T8, Known issue 7. ATTRIBUTION-UNVETTED: the uniform-average
reading of the scheme and the `½`-forcing observation are this run's, not Soto's.
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptB.Payoffs

open Finset

/-! ## Worlds, decision states, the running total -/

/-- A world over `n` prime formulas: a Boolean assignment.
Source: Soto PDF 04 ("the set of worlds is all possible boolean valuations of these formulas")
Kind: D
Fidelity: variant: prime formulas are indices `Fin n`, not FAF sentences (disclosed) -/
abbrev World (n : ℕ) := Fin n → Bool

/-- A decision state: each prime undecided (`none`) or decided with a truth value.
Source: Soto PDF 04 ("`k` of its assignments have been confirmed correct, `n − k` still to be
confirmed or refuted")
Kind: D
Fidelity: variant (disclosed) -/
abbrev Decision (n : ℕ) := Fin n → Option Bool

variable {n : ℕ}

/-- `W` is refuted by `s`: some prime is decided against `W`.
Source: Soto PDF 04 ("one of its assignments has already been refuted")
Kind: D
Fidelity: exact -/
def Refuted (W : World n) (s : Decision n) : Prop := ∃ i, s i = some (!W i)

instance (W : World n) (s : Decision n) : Decidable (Refuted W s) := by
  unfold Refuted; infer_instance

/-- The number of primes decided in agreement with `W` (Soto's `k`).
Source: Soto PDF 04
Kind: D
Fidelity: exact -/
def confirmed (W : World n) (s : Decision n) : ℕ :=
  (univ.filter fun i => s i = some (W i)).card

/-- The number of decided primes.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def decided (s : Decision n) : ℕ := (univ.filter fun i => (s i).isSome).card

/-- **Soto's running total**: a share of `W` has received `1/2^(n−k)` if `W` is unrefuted with
`k` confirmations, and `0` if refuted.
Source: Soto PDF 04 ("When a trader first comes into possession of one of its shares, it
receives as immediate payoff `1/2^{n−k}` … if … refuted … it receives `0`")
Kind: D
Fidelity: exact (as the running total; the increments are `increment`) -/
def payoff (W : World n) (s : Decision n) : ℚ :=
  if Refuted W s then 0 else 1 / 2 ^ (n - confirmed W s)

/-- Decide prime `i` with value `b`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def decideAt (s : Decision n) (i : Fin n) (b : Bool) : Decision n := Function.update s i (some b)

/-- Soto's **increment** on deciding prime `i` as `b`: the change of the running total.
Source: Soto PDF 04 (the three rules)
Kind: D
Fidelity: exact -/
def increment (W : World n) (s : Decision n) (i : Fin n) (b : Bool) : ℚ :=
  payoff W (decideAt s i b) - payoff W s

/-! ## (a) The running total is the uniform-completion probability -/

/-- The completions of a decision state: the worlds agreeing with every decided prime.
Source: bli-soto-a-2-003 (i) (this run's reading)
Kind: D
Fidelity: n/a -/
def completions (s : Decision n) : Finset (World n) :=
  univ.filter fun V => ∀ i, ∀ b, s i = some b → V i = b

/-- A world is unrefuted iff it is a completion.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_refuted_iff_mem_completions (W : World n) (s : Decision n) :
    ¬ Refuted W s ↔ W ∈ completions s := by
  simp only [Refuted, completions, mem_filter, mem_univ, true_and, not_exists]
  constructor
  · intro h i b hb
    by_contra hne
    apply h i
    rw [hb]
    cases hW : W i <;> cases b <;> simp_all
  · intro h i hi
    have := h i _ hi
    cases W i <;> simp at this

/-- On an unrefuted world every decided prime is confirmed: `confirmed = decided`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma confirmed_eq_decided_of_not_refuted {W : World n} {s : Decision n} (h : ¬ Refuted W s) :
    confirmed W s = decided s := by
  unfold confirmed decided
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro hi; rw [hi]; rfl
  · intro hi
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hi
    rw [hb]
    have := (not_refuted_iff_mem_completions W s).mp h
    simp only [completions, mem_filter, mem_univ, true_and] at this
    rw [this i b hb]

/-- The completions of `s` are the product of `{b}` on decided primes and `{true, false}` on
undecided ones.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma completions_eq_piFinset (s : Decision n) :
    completions s = Fintype.piFinset fun i => match s i with
      | some b => ({b} : Finset Bool)
      | none => univ := by
  ext V
  simp only [completions, mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · intro h i
    cases hs : s i with
    | none => simp
    | some b => simp [h i b hs]
  · intro h i b hb
    have := h i
    rw [hb] at this
    simpa using this

/-- The number of completions is `2^(n − decided s)`.
Source: bli-soto-a-2-003 (i)
Kind: P
Fidelity: exact -/
theorem card_completions (s : Decision n) : (completions s).card = 2 ^ (n - decided s) := by
  rw [completions_eq_piFinset, Fintype.card_piFinset]
  have hprod : ∀ i, (match s i with | some b => ({b} : Finset Bool) | none => univ).card =
      if (s i).isSome then 1 else 2 := by
    intro i
    cases s i <;> simp
  simp_rw [hprod]
  rw [prod_ite, prod_const_one, one_mul, prod_const]
  congr 1
  unfold decided
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i => (s i).isSome)
  rw [card_univ, Fintype.card_fin] at this
  omega

/-- **(a) The running total is the uniform-completion probability of the world given the
decisions**: `1 / |completions s|` if `W` completes `s`, else `0`.
Source: bli-soto-a-2-003 (i) (this run's reading of Soto PDF 04, ATTRIBUTION-UNVETTED)
Kind: P
Fidelity: variant (finite arithmetic over indices, not FAF's market)
Hyps: (a) none -/
theorem payoff_eq_uniform (W : World n) (s : Decision n) :
    payoff W s = if W ∈ completions s then 1 / ((completions s).card : ℚ) else 0 := by
  unfold payoff
  by_cases h : Refuted W s
  · rw [if_pos h, if_neg (fun hm => (not_refuted_iff_mem_completions W s).mpr hm h)]
  · rw [if_neg h, if_pos ((not_refuted_iff_mem_completions W s).mp h), card_completions,
      confirmed_eq_decided_of_not_refuted h]
    push_cast
    rfl

/-- A refuted world stays refuted under every further decision.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma refuted_decideAt_of_refuted {W : World n} {s : Decision n} (h : Refuted W s) (i : Fin n)
    (b : Bool) (hi : s i = none) : Refuted W (decideAt s i b) := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, ?_⟩
  have hij : j ≠ i := fun hji => by rw [hji, hi] at hj; simp at hj
  simp [decideAt, Function.update_of_ne hij, hj]

/-- Deciding a fresh prime in agreement with `W` does not refute an unrefuted `W`, and confirms
one more prime.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma confirmed_decideAt_confirm {W : World n} {s : Decision n} (i : Fin n) (hi : s i = none) :
    confirmed W (decideAt s i (W i)) = confirmed W s + 1 := by
  unfold confirmed
  have hnot : i ∉ univ.filter fun j => s j = some (W j) := by simp [hi]
  have : (univ.filter fun j => decideAt s i (W i) j = some (W j)) =
      insert i (univ.filter fun j => s j = some (W j)) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    by_cases hj : j = i
    · subst hj; simp [decideAt]
    · simp [decideAt, hj]
  rw [this, card_insert_of_notMem hnot]

/-- Deciding a fresh prime in agreement with `W` does not refute an unrefuted `W`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_refuted_decideAt_confirm {W : World n} {s : Decision n} (h : ¬ Refuted W s) (i : Fin n) :
    ¬ Refuted W (decideAt s i (W i)) := by
  rintro ⟨j, hj⟩
  by_cases hji : j = i
  · subst hji
    simp [decideAt] at hj
  · exact h ⟨j, by simpa [decideAt, Function.update_of_ne hji] using hj⟩

/-- Deciding a fresh prime against `W` refutes it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma refuted_decideAt_refute (W : World n) (s : Decision n) (i : Fin n) :
    Refuted W (decideAt s i (!W i)) :=
  ⟨i, by simp [decideAt]⟩

/-- Fewer primes are confirmed than exist when one is still undecided.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma confirmed_lt_of_undecided (W : World n) {s : Decision n} {i : Fin n} (hi : s i = none) :
    confirmed W s < n := by
  unfold confirmed
  have hsub : (univ.filter fun j => s j = some (W j)) ⊂ univ := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨subset_univ _, fun h => ?_⟩
    have := (Finset.ext_iff.mp h i).mpr (mem_univ i)
    simp [hi] at this
  have := card_lt_card hsub
  rwa [card_univ, Fintype.card_fin] at this

/-- **Soto's confirmation rule**: deciding a fresh prime in agreement with an unrefuted `W` pays
`1/2^(n−k−1) − 1/2^(n−k)`.
Source: Soto PDF 04 ("the trader immediately receives `1/2^{n−k−1} − 1/2^{n−k}`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem increment_confirm (W : World n) {s : Decision n} (h : ¬ Refuted W s) {i : Fin n}
    (hi : s i = none) :
    increment W s i (W i) = 1 / 2 ^ (n - confirmed W s - 1) - 1 / 2 ^ (n - confirmed W s) := by
  unfold increment payoff
  rw [if_neg h, if_neg (not_refuted_decideAt_confirm h i), confirmed_decideAt_confirm i hi]
  congr 2

/-- **Soto's refutation rule**: deciding a fresh prime against an unrefuted `W` takes back
`1/2^(n−k)`.
Source: Soto PDF 04 ("if one assignment is refuted, it immediately loses `1/2^{n−k}`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem increment_refute (W : World n) {s : Decision n} (h : ¬ Refuted W s) (i : Fin n) :
    increment W s i (!W i) = -(1 / 2 ^ (n - confirmed W s)) := by
  unfold increment payoff
  rw [if_neg h, if_pos (refuted_decideAt_refute W s i)]
  ring

/-- A refuted world's share never pays again.
Source: Soto PDF 04 ("so that the total payoff it has obtained now equals `0`")
Kind: L
Fidelity: exact -/
theorem increment_of_refuted (W : World n) {s : Decision n} (h : Refuted W s) {i : Fin n}
    (hi : s i = none) (b : Bool) : increment W s i b = 0 := by
  unfold increment payoff
  rw [if_pos h, if_pos (refuted_decideAt_of_refuted h i b hi)]
  ring

/-- A refinement path: a list of decisions applied in order.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def applyPath (s : Decision n) : List (Fin n × Bool) → Decision n
  | [] => s
  | (i, b) :: rest => applyPath (decideAt s i b) rest

/-- The increments along a path.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def pathIncrements (W : World n) (s : Decision n) : List (Fin n × Bool) → List ℚ
  | [] => []
  | (i, b) :: rest => increment W s i b :: pathIncrements W (decideAt s i b) rest

/-- **The increments telescope**: along any refinement path, the sum of Soto's increments is
the final running total minus the initial one (the purchase).
Source: Soto PDF 04 ("intermediate payoffs that end up adding up as necessary");
bli-soto-a-031
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem sum_increments (W : World n) (s : Decision n) (path : List (Fin n × Bool)) :
    (pathIncrements W s path).sum = payoff W (applyPath s path) - payoff W s := by
  induction path generalizing s with
  | nil => simp [pathIncrements, applyPath]
  | cons p rest ih =>
      obtain ⟨i, b⟩ := p
      simp only [pathIncrements, applyPath, List.sum_cons, ih, increment]
      ring

/-! ## (b) Once everything is decided, worlds and bundles pay their truth -/

/-- The world a fully decided state names.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def ofFull (s : Decision n) (hfull : ∀ i, (s i).isSome) : World n :=
  fun i => (s i).get (hfull i)

/-- The completions of a fully decided state are exactly the world it names.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma completions_full (s : Decision n) (hfull : ∀ i, (s i).isSome) :
    completions s = {ofFull s hfull} := by
  ext V
  simp only [completions, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h
    funext i
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hfull i)
    rw [h i b hb]
    simp [ofFull, hb]
  · rintro rfl i b hb
    simp [ofFull, hb]

/-- **(b) Fully decided: a world's share has received `1` if it is the true world, `0`
otherwise.**
Source: Soto PDF 04 ("When all prime formulas are eventually decided … the expected reward
works out"); bli-soto-a-031
Kind: P
Fidelity: variant (finite arithmetic)
Hyps: (a) `hfull` -/
theorem payoff_full (W : World n) (s : Decision n) (hfull : ∀ i, (s i).isSome) :
    payoff W s = if W = ofFull s hfull then 1 else 0 := by
  rw [payoff_eq_uniform, completions_full s hfull]
  simp

/-- **(b) A share of `φ` — the bundle of `φ`-worlds — totals `1[φ]` once everything is
decided** (Soto's Def 1 bundle reading; the telescoping identity of item 031).
Source: Soto PDF 04 ("buying a share of `φ` will actually mean buying a share of all worlds in
which it's satisfied"); bli-soto-a-031
Kind: P
Fidelity: variant (`φ` is a decidable predicate on assignments; finite arithmetic)
Hyps: (a) `hfull` -/
theorem bundle_full (φ : World n → Prop) [DecidablePred φ] (s : Decision n)
    (hfull : ∀ i, (s i).isSome) :
    ∑ W ∈ univ.filter φ, payoff W s = if φ (ofFull s hfull) then 1 else 0 := by
  simp_rw [payoff_full _ s hfull]
  by_cases hφ : φ (ofFull s hfull)
  · rw [if_pos hφ, Finset.sum_eq_single (ofFull s hfull)]
    · simp
    · intro W _ hW; rw [if_neg hW]
    · intro h; exact absurd (mem_filter.mpr ⟨mem_univ _, hφ⟩) h
  · rw [if_neg hφ]
    apply Finset.sum_eq_zero
    intro W hW
    rw [mem_filter] at hW
    rw [if_neg]
    rintro rfl
    exact hφ hW.2

/-! ## (c) The one-step cash inequality (`½`-forcing) -/

/-- A child of an unrefuted world with `m` undecided primes, split on a fresh prime, pays
`(1/2) · 2^{−m}` immediately (one more undecided prime).
Source: bli-soto-a-2-003 (iii) (this run's observation, ATTRIBUTION-UNVETTED)
Kind: L
Fidelity: exact -/
lemma child_payoff (m : ℕ) : (1 : ℚ) / 2 ^ (m + 1) = (1 / 2) * (1 / 2 ^ m) := by
  rw [pow_succ]; field_simp

/-- **(c) The `½`-forcing inequality**: buying the cheaper child at price `θ < 1/2` of a parent
priced `P ≤ 2^{−m}` costs `θ · P`, strictly less than the child's immediate payoff
`(1/2) · 2^{−m}`. A per-step inequality — **not** FAF's `Exploits`.
Source: bli-soto-a-2-003 (iii); [[bli-coherent-mm-mandate]] T8(c)
Kind: P
Fidelity: exact (as the per-step inequality)
Hyps: (a) none -/
theorem half_forcing {θ P : ℚ} (m : ℕ) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2)
    (hP : P ≤ 1 / 2 ^ m) : θ * P < 1 / 2 ^ (m + 1) := by
  rw [child_payoff]
  calc θ * P ≤ θ * (1 / 2 ^ m) := mul_le_mul_of_nonneg_left hP hθ0
    _ < (1 / 2) * (1 / 2 ^ m) := mul_lt_mul_of_pos_right hθ (by positivity)

end Cleanroom.Bli.BliCoherentMm.AttemptB.Payoffs
