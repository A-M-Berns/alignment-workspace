import Cleanroom.Bli.BliFound.Constraints
import Cleanroom.Li.LiPseudorandom.AtomDP
import LogicalInduction.Properties.Conditioning

/-!
# `bli-leak` · Leak: the definitions of record and L3.1

Package `bli-leak` (area `bli`, namespace `Cleanroom.Bli.BliLeak`). This file holds the
definitions the rest of the package is stated over, and the one theorem that needs nothing
but sizes: **the leak market agrees with the base inductor on every sentence small on the day
it is priced** (`leakHistory_E1x`, target L3.1), stated with `bli-found`'s agreement predicate
of record `E1x`.

The objects:

* two fresh-atom families through `bli-found`'s allocator — `leakFamily = 8` (the leak atoms
  `leakAtom K n = freshAtom 8 ⟨n, K⟩`, `K` a size pad) and `memberFamily = 9` (the placement
  `member n = freshAtomCode 9 ⟨n, 0⟩` of the pseudorandom family, whose atoms are
  `memberAtom = atomFamily member`); the mandate named `7`/`8`, but `bli-found`'s registry now
  lists `7` as `bli-transfer`'s, so this package takes the next two reserved rows (findings K7);
* the leak-reading coefficient `leakCoef ℓ e n = 2 · price (ℓ n) (e n) − 1` (five `EF` nodes,
  the shape of FAF's `adviceCoefficient`) and the trader `leakTrader ℓ e χ` that on day `n`
  holds the single position `(leakCoef ℓ e n, χ n)` when the edit day `e n` is `≤ n` (rank
  legality) and nothing otherwise;
* the edited market `leakHistory Q ℓ e t`: `Q` with the price of `ℓ n` on day `e n` replaced by
  `t n` (a `Classical` definition, as FAF's `adviceRow`);
* `pendingBound g C`: at most `C` members undecided at any time;
* the union-process facts every later file needs: a member's atom pays its truth value in every
  world consistent with a stage `≥ g n` (`union_atomDP_decided`), and `TheoryTruth` follows from
  that (`theoryTruth_of_decided`);
* the day-`0` size fact used by the transport of FAF's PE1 witness (`smallOn_zero_iff`,
  `smallSet_zero`): on day `0` only `⊥` is small.

Sources: [[bli-program]] §3.2(b) (L3), §4 row L3; the mandate `bli-leak-mandate` § Definitions
of record. Nothing here is a headline except `leakHistory_E1x`; the exploitation content is
`Exploit.lean`, the machine certificate `Trader.lean`.
-/

namespace Cleanroom.Bli.BliLeak

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound
open Cleanroom.Li.LiPseudorandom

/-! ## The two families -/

/-- The fresh-atom family of the leak atoms: `8` (registry request; the mandate's `7` is now
`bli-transfer`'s overlay-witness family).
Source: mandate § Definitions of record; K7
Kind: D
Fidelity: n/a -/
def leakFamily : ℕ := 8

/-- The fresh-atom family of the pseudorandom family's placement: `9`.
Source: mandate § Definitions of record; K7
Kind: D
Fidelity: n/a -/
def memberFamily : ℕ := 9

/-- The placement of the pseudorandom family: member `n` sits on the atom index
`freshAtomCode memberFamily ⟨n, 0⟩` (day first, so `atomDay` reads `n`).
Source: mandate § Definitions of record (`member`)
Kind: D
Fidelity: exact -/
def member (n : ℕ) : ℕ := freshAtomCode memberFamily (Nat.pair n 0)

/-- The placement is injective (`freshAtom_injective` through `Nat.pair`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma member_injective : Function.Injective member := by
  intro m n h
  have h' := (freshAtomCode_inj.mp h).2
  exact (Nat.pair_eq_pair.mp h').1

/-- The atoms of the pseudorandom family: `memberAtom n = atom (member n)`; this is
`li-pseudorandom`'s `atomFamily` at the placement `member`.
Source: mandate § Definitions of record (`χ := atomFamily member`)
Kind: D
Fidelity: exact -/
def memberAtom : ℕ → Sentence := atomFamily member

/-- `memberAtom_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma memberAtom_eq (n : ℕ) : memberAtom n = Formula.atom (member n) := rfl

/-- The leak atom of member `n` with size pad `K`: `freshAtom leakFamily ⟨n, K⟩`. Its token size
is `log₄ (code + 5) + 2`, so a pad `K` with `sizeBound k ≤ log₄ K` makes it large on day `k`.
Source: mandate § Definitions of record (`leakAtom`)
Kind: D
Fidelity: exact -/
def leakAtom (K n : ℕ) : Sentence := freshAtom leakFamily (Nat.pair n K)

/-- The leak atoms of a fixed pad are pairwise distinct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma leakAtom_injective (K : ℕ) : Function.Injective (leakAtom K) := by
  intro m n h
  have h' := (freshAtom_inj.mp h).2
  exact (Nat.pair_eq_pair.mp h').1

/-- A member atom is never a leak atom (different families).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma memberAtom_ne_leakAtom (K n m : ℕ) : memberAtom n ≠ leakAtom K m := by
  intro h
  have h' : freshAtom memberFamily (Nat.pair n 0) = freshAtom leakFamily (Nat.pair m K) := h
  have := (freshAtom_inj.mp h').1
  simp [memberFamily, leakFamily] at this

/-! ## Sizes: the leak atom is large on its edit day -/

/-- The token size of a leak atom, in logarithmic form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tokenSize_leakAtom (K n : ℕ) :
    tokenSize (leakAtom K n) = Nat.log 4 (freshAtomCode leakFamily (Nat.pair n K) + 5) + 2 := by
  unfold leakAtom freshAtom
  rw [tokenSize_atom, length_natDigits4_eq_log (by omega)]

/-- **A padded leak atom is large.** If `sizeBound k ≤ log₄ K` then `leakAtom K n` is not small
on day `k`, for every member `n` (the pad dominates the code, and the size is its `log₄`).
Source: mandate L3.1 (`leakAtom_large_of_pad`); the argument of `bli-found`'s `stateAtom_large`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem leakAtom_large_of_pad {k K : ℕ} (h : sizeBound k ≤ Nat.log 4 K) (n : ℕ) :
    ¬ SmallOn k (leakAtom K n) := by
  intro hsmall
  unfold SmallOn at hsmall
  rw [tokenSize_leakAtom] at hsmall
  have h1 : Nat.log 4 K ≤ Nat.log 4 (freshAtomCode leakFamily (Nat.pair n K) + 5) :=
    Nat.log_mono_right (le_trans (le_freshAtomCode_pair _ _ _) (Nat.le_add_right _ 5))
  omega

/-- The pad of record for an edit on day `N₀`: `K = 4 ^ sizeBound N₀` makes every leak atom
large on every day `≤ N₀`.
Source: mandate L3.1, L3.4 (`K := 4 ^ sizeBound N₀`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem leakAtom_large_pow (N₀ : ℕ) {k : ℕ} (hk : k ≤ N₀) (n : ℕ) :
    ¬ SmallOn k (leakAtom (4 ^ sizeBound N₀) n) :=
  leakAtom_large_of_pad (by rw [Nat.log_pow (by norm_num)]; exact sizeBound_mono hk) n

/-! ## Day `0`: only `⊥` is small -/

/-- Every sentence other than `⊥` has token size at least `3` (an atom token carries at least two
digits plus its terminator; every connective adds at least two tokens).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem three_le_tokenSize_of_ne_falsum {φ : Sentence} (h : φ ≠ ⊥) : 3 ≤ tokenSize φ := by
  cases φ with
  | atom a => exact three_le_tokenSize_atom a
  | falsum => exact absurd rfl h
  | and φ ψ =>
      change 3 ≤ tokenSize (φ ⋏ ψ)
      rw [tokenSize_and]
      have := one_le_tokenSize φ
      omega
  | or φ ψ =>
      change 3 ≤ tokenSize (φ ⋎ ψ)
      rw [tokenSize_or]
      omega
  | imp φ ψ =>
      change 3 ≤ tokenSize (φ 🡒 ψ)
      rw [tokenSize_imp]
      have := one_le_tokenSize φ
      omega

/-- **On day `0` only `⊥` is small**: `sizeBound 0 = 2` and every other sentence has size `≥ 3`.
Source: mandate L3.0 (proof of `E1x`); `bli-found` `Size.lean` module docstring
Kind: L
Fidelity: exact -/
theorem smallOn_zero_iff (φ : Sentence) : SmallOn 0 φ ↔ φ = ⊥ := by
  constructor
  · intro h
    by_contra hne
    have h3 := three_le_tokenSize_of_ne_falsum hne
    have h2 : sizeBound 0 = 2 := by norm_num [sizeBound]
    unfold SmallOn at h
    omega
  · rintro rfl
    exact smallOn_falsum 0

/-- `smallSet 0 = {⊥}`.
Source: mandate L3.0
Kind: L
Fidelity: exact -/
theorem smallSet_zero : smallSet 0 = {⊥} := by
  ext φ
  rw [mem_smallSet, smallOn_zero_iff, Finset.mem_singleton]

/-! ## The leak-reading coefficient and trader -/

/-- The leak-reading coefficient of member `n`: `2 · price (ℓ n) (e n) − 1`, i.e. `+1` share if
the leaked price says "true" and `−1` if it says "false". `EF` has no subtraction, so it is spelled
`add (mul (const 2) (price (ℓ n) (e n))) (const (-1))` — five nodes, the shape of FAF's
`adviceCoefficient`. Its rank is the edit day `e n`.
Source: mandate § Definitions of record (`leakCoef`); [[bli-program]] §3.2(b)
Kind: D
Fidelity: exact -/
def leakCoef (ℓ : ℕ → Sentence) (e : ℕ → ℕ) (n : ℕ) : EF :=
  .add (.mul (.const 2) (.price (ℓ n) (e n))) (.const (-1))

/-- `leakCoef_denote`: the coefficient's value on a history is `2 · V (e n) (ℓ n) − 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma leakCoef_denote (ℓ : ℕ → Sentence) (e : ℕ → ℕ) (n : ℕ) (V : History) :
    (leakCoef ℓ e n).denote V = 2 * V (e n) (ℓ n) - 1 := by
  show (leakCoef ℓ e n).denoteWith [] V = _
  simp only [leakCoef, EF.denoteWith_add, EF.denoteWith_mul, EF.denoteWith_const,
    EF.denoteWith_price]
  push_cast
  ring

/-- `leakCoef_rank`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma leakCoef_rank (ℓ : ℕ → Sentence) (e : ℕ → ℕ) (n : ℕ) :
    (leakCoef ℓ e n).rank = e n := by
  simp [leakCoef]

/-- **The leak-reading trader.** On day `n` it holds the single position `(leakCoef ℓ e n, χ n)` —
one share of `χ n` bought or sold according to the leaked price of `ℓ n` on day `e n` — when the
edit day `e n` is `≤ n` (the rank certificate `rank_le` demands it), and no position otherwise.
The trade is *priced by the market it faces* (`V n (χ n)`), which for the leak market is the base
inductor's price because `χ n` is never a leak atom (`Exploit.lean`).
Source: mandate § Definitions of record (`leakTrader`); [[bli-program]] §3.2(b)
Kind: D
Fidelity: variant: the mandate's trader trades on every day; here days with `n < e n` are empty
(the alternative, clamping the read to `min (e n) n`, would read an unedited price) -/
def leakTrader (ℓ : ℕ → Sentence) (e : ℕ → ℕ) (χ : ℕ → Sentence) : Trader where
  strat n :=
    { trades := if e n ≤ n then [(leakCoef ℓ e n, χ n)] else []
      rank_le := by
        intro p hp
        split_ifs at hp with hen
        · rw [List.mem_singleton] at hp
          subst hp
          simpa using hen
        · simp at hp }

/-- `leakTrader_trades`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma leakTrader_trades (ℓ : ℕ → Sentence) (e : ℕ → ℕ) (χ : ℕ → Sentence) (n : ℕ) :
    ((leakTrader ℓ e χ).strat n).trades =
      if e n ≤ n then [(leakCoef ℓ e n, χ n)] else [] := rfl

/-! ## The leak market -/

open Classical in
/-- **The leak market**: `Q` with the price of the leak atom `ℓ n` on day `e n` replaced by
`t n`, for every member `n`; every other coordinate is `Q`'s. A `Classical` definition, as FAF's
`adviceRow`; `ComputableMarket` asks for a rational table and a program, not for the history to
be a computable Lean function (`Instance.lean`). The market of the theorems is
`leakHistory Q (leakAtom K) e (truthR x)`.
Source: mandate § Definitions of record (`leakHistory`); [[bli-program]] §3.2(b) (`overlay Q leak`)
Kind: D
Fidelity: exact -/
noncomputable def leakHistory (Q : History) (ℓ : ℕ → Sentence) (e : ℕ → ℕ) (t : ℕ → ℝ) :
    History :=
  fun m φ => if h : ∃ n, φ = ℓ n ∧ m = e n then t h.choose else Q m φ

variable {Q : History} {ℓ : ℕ → Sentence} {e : ℕ → ℕ} {t : ℕ → ℝ}

/-- The leak coordinate carries the planted value: `leakHistory Q ℓ e t (e n) (ℓ n) = t n`
(for injective `ℓ`).
Source: mandate L3.1 (`leakHistory_leak`)
Kind: L
Fidelity: exact -/
lemma leakHistory_leak (hℓ : Function.Injective ℓ) (n : ℕ) :
    leakHistory Q ℓ e t (e n) (ℓ n) = t n := by
  have hex : ∃ k, ℓ n = ℓ k ∧ e n = e k := ⟨n, rfl, rfl⟩
  rw [leakHistory, dif_pos hex]
  congr 1
  exact (hℓ hex.choose_spec.1).symm

/-- **Exact agreement off the leak atoms**: a sentence that is no leak atom is priced by `Q` on
every day. Stronger than `E1x`: only the leak coordinates move.
Source: mandate L3.1 (`leakHistory_eq_of_ne`)
Kind: L
Fidelity: exact -/
lemma leakHistory_eq_of_ne {φ : Sentence} (h : ∀ n, φ ≠ ℓ n) (m : ℕ) :
    leakHistory Q ℓ e t m φ = Q m φ := by
  rw [leakHistory, dif_neg]
  rintro ⟨n, hn, -⟩
  exact h n hn

/-- Exact agreement on a day that is no edit day.
Source: mandate L3.1 (`leakHistory_off`)
Kind: L
Fidelity: exact -/
lemma leakHistory_eq_of_day {m : ℕ} (h : ∀ n, m ≠ e n) (φ : Sentence) :
    leakHistory Q ℓ e t m φ = Q m φ := by
  rw [leakHistory, dif_neg]
  rintro ⟨n, -, hn⟩
  exact h n hn

/-- The leak market prices in `[0, 1]` when `Q` and the planted values do.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma leakHistory_mem_Icc (hQ : ∀ m φ, 0 ≤ Q m φ ∧ Q m φ ≤ 1)
    (ht : ∀ n, 0 ≤ t n ∧ t n ≤ 1) (m : ℕ) (φ : Sentence) :
    0 ≤ leakHistory Q ℓ e t m φ ∧ leakHistory Q ℓ e t m φ ≤ 1 := by
  rw [leakHistory]
  split_ifs
  · exact ht _
  · exact hQ m φ

/-- **L3.1. The leak market agrees with `Q` on every day-small sentence.** If each leak atom
`ℓ n` is large on its edit day `e n`, then `E1x Q (leakHistory Q ℓ e t)`: on day `m`, every
sentence of `smallSet m` is priced by `Q`. The content is the largeness of each leak atom on the
day it is edited; the reading day, on which the atom is small, is a *later* day, and that is the
reading-back mechanism, not a violation of `E1x`.
Source: mandate L3.1; [[bli-program]] §3.2(b); bli-slides-030 ("since traders don't touch large
sentences, we can modify them however we like")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem leakHistory_E1x (hlarge : ∀ n, ¬ SmallOn (e n) (ℓ n)) :
    E1x Q (leakHistory Q ℓ e t) := by
  intro m φ hφ
  rw [mem_smallSet] at hφ
  rw [leakHistory, dif_neg]
  rintro ⟨n, rfl, rfl⟩
  exact hlarge n hφ

/-- **Exact agreement before the first edit day**: if every edit day is `≥ N₀`, the leak market
*is* `Q` on days `< N₀` (the hypothesis of the finite-prefix retreat, L3.4).
Source: mandate L3.4
Kind: L
Fidelity: exact -/
theorem leakHistory_agree_before {N₀ : ℕ} (hN : ∀ n, N₀ ≤ e n) :
    ∀ m < N₀, ∀ φ, leakHistory Q ℓ e t m φ = Q m φ := by
  intro m hm φ
  refine leakHistory_eq_of_day (fun n h => ?_) φ
  have := hN n
  omega

/-! ## Pending members -/

/-- **At most `C` members undecided at any time**: for every day `m`, at most `C` members
`n ≤ m` have their decision day `g n` after `m`.
Source: mandate § Definitions of record (`pendingBound`); [[bli-program]] §3.2(b) ("at most `f`
trades are pending at any time")
Kind: D
Fidelity: exact -/
def pendingBound (g : ℕ → ℕ) (C : ℕ) : Prop :=
  ∀ m, ((Finset.range (m + 1)).filter (fun n => m < g n)).card ≤ C

/-- Decision one day late (`g n = n + 1`) leaves exactly one member pending.
Source: mandate § Definitions of record (`g := fun n ↦ n + 1` gives `C = 1`)
Kind: L
Fidelity: exact -/
lemma pendingBound_succ : pendingBound (fun n => n + 1) 1 := by
  intro m
  have h : (Finset.range (m + 1)).filter (fun n => m < n + 1) = {m} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    omega
  rw [h, Finset.card_singleton]

/-! ## Decided-after-reading, in the stage form -/

/-- **A member's atom pays its truth value in every world consistent with a stage `≥ g n`** of
a process containing `atomDP a x g` (stage form of "decided with delay", from
`literalOf_mem_atomDP`), for any base process `DP₀` in the union.
Source: mandate L3.3 (`hdec` for `atomDP`), L3.5; `li-pseudorandom` `atomDP_theoryTruth`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem union_atomDP_decided (DP₀ : DeductiveProcess) {a g : ℕ → ℕ} (hg : ∀ j, j < g j)
    (x : ℕ → Bool) :
    ∀ n (v : PCWorld) m, g n ≤ m → v.ConsistentWith ((DP₀.union (atomDP a x g)).D m) →
      v.payout (atomFamily a n) = truthR x n := by
  intro n v m hm hv
  have hmem := hv _ (Finset.mem_union_right _
    (literalOf_mem_atomDP (a := a) (x := x) hg hm))
  unfold atomFamily truthR PCWorld.payout
  unfold Cleanroom.Li.LiPseudorandom.literalOf at hmem
  by_cases hx : x n = true
  · rw [if_pos hx] at hmem
    simp [hx, hmem]
  · have hx' : x n = false := by simpa using hx
    rw [if_neg (by simp [hx'])] at hmem
    rw [PCWorld.holds_neg] at hmem
    simp [hx', hmem]

/-- `TheoryTruth` follows from the stage form of "decided with delay": a world consistent with
every stage is consistent with stage `g n`.
Source: mandate L3.3 (the `thm:benford` bundle)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem theoryTruth_of_decided {χ : ℕ → Sentence} {DP : DeductiveProcess} {t : ℕ → ℝ}
    {g : ℕ → ℕ}
    (hdec : ∀ n (v : PCWorld) m, g n ≤ m → v.ConsistentWith (DP.D m) → v.payout (χ n) = t n) :
    AffineCombination.TheoryTruth χ DP t :=
  fun n v hv => hdec n v (g n) le_rfl (hv (g n))

end Cleanroom.Bli.BliLeak
