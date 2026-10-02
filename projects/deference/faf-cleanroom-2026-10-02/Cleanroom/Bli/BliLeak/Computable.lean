import Cleanroom.Bli.BliLeak.Leak
import Mathlib.Computability.PartrecCode

/-!
# `bli-leak` · Computable: the leak market is a computable market (L3.6)

**The lemma.** If `Q` is a computable market, `x` a computable stream and `e` a computable
edit-day function, then `leakHistory Q (leakAtom K) e (truthR x)` is a computable market
(`leakHistory_computableMarket`), by FAF's `ComputableMarket.ofComputableTable` on the rational
table

`leakQuote quote e x K n c = if isLeakCode K c ∧ n = e (leakMemberOf c) then (if x (leakMemberOf c) then 1 else 0) else quote n c`,

where the leak-atom recogniser is read off Foundation's `Formula.toNat`: an atom's code is
`⟨1, a⟩ + 1`, so `encode (leakAtom K k) = ⟨1, ⟨leakTag, ⟨k, K⟩⟩⟩ + 1` (`encode_leakAtom`, by `rfl`),
`leakMemberOf` reads `k` back, and `isLeakCode K c` re-encodes and compares — the shape of FAF's
`cxTable` (`Construction/Freeze/Counterexample.lean`). Exactness (`leakHistory_eq_leakQuote`) is a
case split on whether the queried cell is a leak coordinate; computability is `Computable.cond`
twice over primitive recursive pieces and the three computable inputs.

At the instance of record (`Closed.lean`) the stream is `li-pseudorandom` T7 (OPEN), so
`leakMarket_computableMarket` is derived from this lemma and the two open primitives; the
grade-(a) content is here.
-/

namespace Cleanroom.Bli.BliLeak

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound
open Cleanroom.Li.LiPseudorandom

/-! ## The leak-atom recogniser -/

/-- The atom tag of the leak family: `cleanroomBaseTag + leakFamily`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def leakTag : ℕ := cleanroomBaseTag + leakFamily

/-- Foundation's code of a leak atom: an atom's code is `⟨1, a⟩ + 1` (`Formula.toNat`).
Source: mandate L3.6 (the table's shape, as FAF's `cxTable`)
Kind: L
Fidelity: n/a -/
lemma encode_leakAtom (K k : ℕ) :
    Encodable.encode (leakAtom K k) = Nat.pair 1 (Nat.pair leakTag (Nat.pair k K)) + 1 := rfl

/-- The member index read off a sentence code (junk on codes that are no leak atom's).
Source: mandate L3.6
Kind: D
Fidelity: n/a -/
def leakMemberOf (c : ℕ) : ℕ := c.pred.unpair.2.unpair.2.unpair.1

/-- The leak-atom code of pad `K` at the member read off `c`.
Source: mandate L3.6
Kind: D
Fidelity: n/a -/
def leakCodeOf (K c : ℕ) : ℕ := Nat.pair 1 (Nat.pair leakTag (Nat.pair (leakMemberOf c) K)) + 1

/-- The recogniser: `c` is the code of a leak atom of pad `K` iff re-encoding the member read off
`c` gives `c` back.
Source: mandate L3.6
Kind: D
Fidelity: n/a -/
def isLeakCode (K c : ℕ) : Bool := decide (c = leakCodeOf K c)

/-- `leakMemberOf_encode`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma leakMemberOf_encode (K k : ℕ) : leakMemberOf (Encodable.encode (leakAtom K k)) = k := by
  rw [encode_leakAtom]
  simp [leakMemberOf, Nat.unpair_pair]

/-- The recogniser is exact.
Source: mandate L3.6
Kind: L
Fidelity: exact -/
lemma isLeakCode_iff (K c : ℕ) :
    isLeakCode K c = true ↔ ∃ k, c = Encodable.encode (leakAtom K k) := by
  constructor
  · intro h
    exact ⟨leakMemberOf c, of_decide_eq_true h⟩
  · rintro ⟨k, rfl⟩
    apply decide_eq_true
    rw [leakCodeOf, leakMemberOf_encode, encode_leakAtom]

/-- `leakMemberOf` is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma leakMemberOf_primrec : Primrec leakMemberOf :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.pred)))))

/-- `leakCodeOf K` is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma leakCodeOf_primrec (K : ℕ) : Primrec (leakCodeOf K) :=
  Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1)
    (Primrec₂.natPair.comp (Primrec.const leakTag)
      (Primrec₂.natPair.comp leakMemberOf_primrec (Primrec.const K))))

/-- Decidable equality on `ℕ`, as a primitive recursive `Bool`-valued function of two arguments
(Mathlib's `Primrec.eq` destructured; the two `Decidable` instances are reconciled by
`decide_eq_decide`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma decide_eq_primrec₂ : Primrec₂ (fun a b : ℕ => decide (a = b)) := by
  obtain ⟨_, h⟩ := (Primrec.eq : PrimrecRel (@Eq ℕ))
  exact Primrec₂.mk (h.of_eq (fun p => decide_eq_decide.mpr Iff.rfl))

/-- The recogniser is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isLeakCode_primrec (K : ℕ) : Primrec (isLeakCode K) :=
  (decide_eq_primrec₂.comp Primrec.id (leakCodeOf_primrec K)).of_eq (fun _ => rfl)

/-! ## The table -/

/-- **The leak market's rational table**: at a leak coordinate `(e k, ⌜leakAtom K k⌝)` the planted
value `if x k then 1 else 0`, elsewhere the base table.
Source: mandate L3.6
Kind: D
Fidelity: exact -/
def leakQuote (quote : ℕ → ℕ → ℚ) (e : ℕ → ℕ) (x : ℕ → Bool) (K n c : ℕ) : ℚ :=
  if isLeakCode K c = true ∧ n = e (leakMemberOf c) then (if x (leakMemberOf c) then 1 else 0)
  else quote n c

/-- **Exactness**: the leak market is the real cast of its table.
Source: mandate L3.6
Kind: L
Fidelity: exact -/
lemma leakHistory_eq_leakQuote {Q : History} {quote : ℕ → ℕ → ℚ}
    (hexact : ∀ n φ, Q n φ = (quote n (Encodable.encode φ) : ℝ)) (e : ℕ → ℕ) (x : ℕ → Bool)
    (K n : ℕ) (φ : Sentence) :
    leakHistory Q (leakAtom K) e (truthR x) n φ =
      (leakQuote quote e x K n (Encodable.encode φ) : ℝ) := by
  by_cases h : ∃ k, φ = leakAtom K k ∧ n = e k
  · obtain ⟨k, rfl, rfl⟩ := h
    rw [leakHistory_leak (leakAtom_injective K)]
    have h1 : isLeakCode K (Encodable.encode (leakAtom K k)) = true :=
      (isLeakCode_iff _ _).2 ⟨k, rfl⟩
    unfold leakQuote
    rw [if_pos ⟨h1, by rw [leakMemberOf_encode]⟩, leakMemberOf_encode]
    unfold truthR
    split_ifs <;> simp
  · simp only [leakHistory]
    rw [dif_neg h, hexact n φ]
    unfold leakQuote
    rw [if_neg]
    rintro ⟨h1, h2⟩
    obtain ⟨k, hk⟩ := (isLeakCode_iff _ _).1 h1
    have hφ : φ = leakAtom K k := Encodable.encode_injective hk
    subst hφ
    rw [leakMemberOf_encode] at h2
    exact h ⟨k, rfl, h2⟩

/-- **The table is computable** from the base table, the edit-day function and the stream.
Source: mandate L3.6
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem leakQuote_computable {quote : ℕ → ℕ → ℚ}
    (hquote : Computable (fun z : ℕ => quote z.unpair.1 z.unpair.2))
    {e : ℕ → ℕ} (he : Computable e) {x : ℕ → Bool} (hx : Computable x) (K : ℕ) :
    Computable (fun z : ℕ => leakQuote quote e x K z.unpair.1 z.unpair.2) := by
  have hn : Computable (fun z : ℕ => z.unpair.1) := Computable.fst.comp Computable.unpair
  have hc : Computable (fun z : ℕ => z.unpair.2) := Computable.snd.comp Computable.unpair
  have hk : Computable (fun z : ℕ => leakMemberOf z.unpair.2) :=
    leakMemberOf_primrec.to_comp.comp hc
  have hleak : Computable (fun z : ℕ => isLeakCode K z.unpair.2) :=
    (isLeakCode_primrec K).to_comp.comp hc
  have heq : Computable (fun z : ℕ => decide (z.unpair.1 = e (leakMemberOf z.unpair.2))) :=
    (Primrec₂.to_comp decide_eq_primrec₂).comp hn (he.comp hk)
  have hval : Computable (fun z : ℕ => (if x (leakMemberOf z.unpair.2) then (1 : ℚ) else 0)) :=
    (Computable.cond (hx.comp hk) (Computable.const (1 : ℚ)) (Computable.const (0 : ℚ))).of_eq
      (fun z => by cases x (leakMemberOf z.unpair.2) <;> simp)
  have h2 : Computable (fun z : ℕ =>
      cond (isLeakCode K z.unpair.2)
        (cond (decide (z.unpair.1 = e (leakMemberOf z.unpair.2)))
          (if x (leakMemberOf z.unpair.2) then (1 : ℚ) else 0) (quote z.unpair.1 z.unpair.2))
        (quote z.unpair.1 z.unpair.2)) :=
    Computable.cond hleak (Computable.cond heq hval hquote) hquote
  refine h2.of_eq (fun z => ?_)
  unfold leakQuote
  by_cases h1 : isLeakCode K z.unpair.2 = true <;>
    by_cases h3 : z.unpair.1 = e (leakMemberOf z.unpair.2) <;> simp [h1, h3]

/-- A computable market's quote table is a computable function (FAF's `computable_quote`,
re-proved here to keep the `Freeze` import out; `Nat.Partrec.Code.eval_part` and
`Partrec.of_eq_tot`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma computableMarket_table {Q : History} (hQ : ComputableMarket Q) :
    ∃ quote : ℕ → ℕ → ℚ, (∀ n φ, Q n φ = (quote n (Encodable.encode φ) : ℝ)) ∧
      Computable (fun z : ℕ => quote z.unpair.1 z.unpair.2) := by
  obtain ⟨-, quote, code, hexact, hcode⟩ := hQ
  refine ⟨quote, hexact, ?_⟩
  rw [← Computable.encode_iff]
  have hp : Partrec (fun z : ℕ => code.eval z) :=
    Nat.Partrec.Code.eval_part.comp (Computable.const code) Computable.id
  exact hp.of_eq_tot (fun z => hcode z)

/-- **L3.6. The leak market is a computable market**, for a computable base market, a computable
edit-day function and a computable stream: FAF's `ComputableMarket.ofComputableTable` on
`leakQuote`.
Source: mandate L3.6 (`leakHistory_computableMarket`)
Kind: C
Fidelity: exact
Hyps: (a); at the instance of record `hx` is `li-pseudorandom` T7 (OPEN) -/
theorem leakHistory_computableMarket {Q : History} (hQ : ComputableMarket Q) {e : ℕ → ℕ}
    (he : Computable e) {x : ℕ → Bool} (hx : Computable x) (K : ℕ) :
    ComputableMarket (leakHistory Q (leakAtom K) e (truthR x)) := by
  obtain ⟨quote, hexact, hquote⟩ := computableMarket_table hQ
  refine ComputableMarket.ofComputableTable (leakQuote quote e x K)
    (leakHistory_mem_Icc hQ.1 (fun n => by unfold truthR; split_ifs <;> norm_num))
    (leakHistory_eq_leakQuote hexact e x K) ?_
  exact Computable.encode_iff.mpr (leakQuote_computable hquote he hx K)

end Cleanroom.Bli.BliLeak
