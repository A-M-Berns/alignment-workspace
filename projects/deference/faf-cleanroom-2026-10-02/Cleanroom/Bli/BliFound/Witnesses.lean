import Cleanroom.Bli.BliFound.Bridge
import LogicalInduction.Framework.Machine.Witnesses

/-!
# `bli-found` · Witnesses: non-vacuity of the bridge lemma and of the small/large split

* **The bridge lemma on a real e.c. trader.** FAF's `buyAtomDaily` (`Framework/Machine/Witnesses.lean`)
  trades one share of `⌜aₙ⌝` on day `n` and is `EfficientlyComputable`
  (`efficientlyComputable_buyAtomDaily`). `MentionedBy` catches its day-`n` sentence, and that
  sentence is small on day `n` from day `1` on — the `N` of the bridge lemma, exhibited
  (`buyAtomDaily_small_from_one`), independently of the structured bound (which was OPEN in the
  first pass and is now proved in `Structured.lean`).
* **The split is non-degenerate.** For every day `n` there is a sentence large on day `n`
  (`largeOn_witness`: an atom whose index has more than `sizeBound n` digits), and a sentence
  small on day `n + 1` but large on day `n` (`crossing_witness`) — stated symbolically, never
  evaluated.
* **Finding (mandate T1).** The program's N+ phrasing — "a day-varying e.c. family whose day-`n`
  sentence is small on day `n` but not on day `n − 1`" — is unsatisfiable eventually: by the bridge
  lemma an e.c. family's day-`n` sentences are small on day `n − 1` too for large `n` (polynomial
  size against `2^{2^{n-1}}`). The two witnesses above are what can be shipped.

Sources: mandate T1 (witness paragraph); `Framework/Machine/Witnesses.lean`.
-/

namespace Cleanroom.Bli.BliFound

open LogicalInduction LO.Propositional

/-! ## `buyAtomDaily` -/

/-- `MentionedBy` catches `buyAtomDaily`'s day-`n` sentence `⌜aₙ⌝`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma buyAtomDaily_mentions (n : ℕ) : MentionedBy (buyAtomDaily.strat n) (Formula.atom n) :=
  Or.inl ⟨EF.const 1, by simp [buyAtomDaily]⟩

/-- `buyAtomDaily` mentions nothing but `⌜aₙ⌝` on day `n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mentionedBy_buyAtomDaily {n : ℕ} {φ : Sentence} (h : MentionedBy (buyAtomDaily.strat n) φ) :
    φ = Formula.atom n := by
  rcases h with ⟨e, he⟩ | ⟨p, hp, k, hk⟩
  · simp [buyAtomDaily] at he
    exact he.2
  · simp [buyAtomDaily] at hp
    rw [hp] at hk
    simp [EF.priceQueries] at hk

/-- `sizeBound (n + 1) = (sizeBound n)^2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sizeBound_succ (n : ℕ) : sizeBound (n + 1) = sizeBound n * sizeBound n := by
  unfold sizeBound
  rw [pow_succ, pow_mul, sq]

/-- `n + 3 ≤ 2^{2^n}` for `n ≥ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma add_three_le_sizeBound {n : ℕ} (hn : 1 ≤ n) : n + 3 ≤ sizeBound n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [sizeBound]
  | succ k _ ih =>
      rw [sizeBound_succ]
      nlinarith

/-- `⌜aₙ⌝` is small on day `n` from day `1` on (`(natDigits4 (n + 5)).length + 1 ≤ n + 3 ≤ 2^{2^n}`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma smallOn_atom_self {n : ℕ} (hn : 1 ≤ n) : SmallOn n (Formula.atom n) := by
  unfold SmallOn
  rw [tokenSize_atom]
  have h1 := length_natDigits4_add_five n
  have h2 := add_three_le_sizeBound hn
  omega

/-- **N+ for the bridge lemma on a real e.c. trader**: `buyAtomDaily` is efficiently computable
(FAF's `efficientlyComputable_buyAtomDaily`), and with `N = 1` every sentence it mentions on day
`n ≥ N` is small on day `n` — the bridge lemma's conclusion, exhibited directly (without the
structured bound, which was OPEN in the first pass and is now proved).
Source: mandate T1 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem buyAtomDaily_small_from_one :
    EfficientlyComputable buyAtomDaily ∧
      ∀ n ≥ 1, ∀ φ, MentionedBy (buyAtomDaily.strat n) φ → SmallOn n φ := by
  refine ⟨efficientlyComputable_buyAtomDaily, fun n hn φ hφ => ?_⟩
  rw [mentionedBy_buyAtomDaily hφ]
  exact smallOn_atom_self hn

/-- The trader genuinely varies with the day (FAF's `buyAtomDaily_nonconstant`), so the witness is
not a constant strategy. -/
example : (buyAtomDaily.strat 0).trades ≠ (buyAtomDaily.strat 1).trades := buyAtomDaily_nonconstant

/-! ## The split is non-degenerate -/

/-- An atom whose index is `4 ^ sizeBound n` has `sizeBound n + 1` base-4 digits.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma length_natDigits4_four_pow_add_five (K : ℕ) (hK : 1 ≤ K) :
    (natDigits4 (4 ^ K + 5)).length = K + 1 := by
  have hlt : 4 ^ K + 5 < 4 ^ (K + 1) := by
    rw [pow_succ]
    have : 4 ≤ 4 ^ K := by
      calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ K := Nat.pow_le_pow_right (by norm_num) hK
    omega
  have hge : 4 ^ K ≤ 4 ^ K + 5 := Nat.le_add_right _ _
  rw [length_natDigits4_eq_log (by positivity)]
  rw [Nat.log_eq_of_pow_le_of_lt_pow hge hlt]

/-- **A sentence large on day `n`**, for every `n`: the atom `⌜a_{4^{sizeBound n}}⌝` has size
`sizeBound n + 2`. Stated symbolically (never evaluated).
Source: mandate T1 (split non-degeneracy)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem largeOn_witness (n : ℕ) : ¬ SmallOn n (Formula.atom (4 ^ sizeBound n)) := by
  unfold SmallOn
  rw [tokenSize_atom, length_natDigits4_four_pow_add_five _ (le_trans (by norm_num) (two_le_sizeBound n))]
  omega

/-- **A sentence small on day `n + 1` but large on day `n`**: the atom `⌜a_{4^{sizeBound n}}⌝`,
of size `sizeBound n + 2 ≤ (sizeBound n)^2 = sizeBound (n + 1)`.
Source: mandate T1 (split non-degeneracy)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem crossing_witness (n : ℕ) :
    SmallOn (n + 1) (Formula.atom (4 ^ sizeBound n)) ∧ ¬ SmallOn n (Formula.atom (4 ^ sizeBound n)) := by
  refine ⟨?_, largeOn_witness n⟩
  unfold SmallOn
  rw [tokenSize_atom, length_natDigits4_four_pow_add_five _ (le_trans (by norm_num) (two_le_sizeBound n))]
  rw [sizeBound_succ]
  have := two_le_sizeBound n
  nlinarith

end Cleanroom.Bli.BliFound
