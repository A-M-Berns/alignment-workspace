import Cleanroom.Found.LiQuoteLane.Defs
import LogicalInduction.Construction.Primcodable
import LogicalInduction.Construction.DeductiveDovetail
import LogicalInduction.Construction.Conditioning.Presentation

/-!
# `li-quote-lane` · Computability: the ledger process is a computable deductive process (T1.4)

FAF's `ComputableDeductiveProcess DP` (`Framework/Criterion.lean`) asks for one partial recursive
program emitting the encoded stage `D n` — no polynomial bound. `bli-found`'s
`extendBy_computable` demands a `Primrec` enumeration of the schedule, which the stages of a
schedule reading a *LIA quote* cannot satisfy (LIA quotes are `Computable`, not provably
`Primrec`: `liaStates` runs `Nat.find` minimizations, `bli-found-liacomputation.md` §2). This
file supplies the `Computable` certificate the LIA instance can meet:

* `literalProcess_computable_ofComputable`: a literal process with a *computable* list enumeration
  of its stages is computable (the `Primrec` form is `bli-found`'s `literalProcess_computable`);
* `ledgerEntries_rec_computable`: the ledger's stage lists are computable from a computable table
  `a` and computable publication schedules, built by `Computable.nat_rec` over a candidate range
  (Mathlib has `Primrec.list_flatMap` but no `Computable` list-comprehension combinators);
* `ledgerProcess_computable` (T1.4, headline): through FAF's
  `DeductiveProcessComputation.union_toComputable`.

API note (findings): `bli-found`'s `Primrec` form is the stronger certificate and stays; this is
the one the LIA instance satisfies.

Scope: one-way.
-/

namespace Cleanroom.Found.LiQuoteLane

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

-- `Nat.unpair` unfolds through `Nat.sqrt`; keeping it opaque stops the unifier from evaluating
-- it on open terms (FAF's `notes/lean-gotchas.md`, as in `Construction/Quotation/MarketQuoteCodes.lean`).
attribute [local irreducible] Nat.sqrt

/-! ## A literal process with a computable enumeration is computable -/

/-- **A literal process is computable from a computable list enumeration of its stages** (the
`Computable` twin of `bli-found`'s `literalProcess_computable`, whose hypothesis is `Primrec`).
The stage encoder is the canonical sorted, duplicate-free code of the mapped list (FAF's
`encode_toFinset_eq`), a primitive recursive function of the list, composed with the computable
enumeration; `Nat.Partrec.Code.exists_code` names the program.
Source: mandate T1.4
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem literalProcess_computable_ofComputable (L : LiteralSchedule)
    (enum : ℕ → List (ℕ × ℕ × Bool)) (henum : ∀ s, (enum s).toFinset = L.lits s)
    (hcomp : Computable enum) : ComputableDeductiveProcess (literalProcess L) := by
  have hprim : Primrec fun l : List (ℕ × ℕ × Bool) =>
      Encodable.encode (((l.map literalOf).dedup).insertionSort sentenceCodeLE) :=
    Primrec.encode.comp (sentenceInsertionSort_prim.comp (dedup_prim.comp
      (Primrec.list_map Primrec.id (literalOf_prim.comp Primrec.snd).to₂)))
  have hc : Computable fun s => Encodable.encode ((literalProcess L).D s) := by
    refine (hprim.to_comp.comp hcomp).of_eq fun s => ?_
    rw [literalProcess_D_eq_toFinset L enum henum s, encode_toFinset_eq]
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hc.partrec)
  exact ⟨code, fun s => by rw [hcode]; simp⟩

/-! ## A computable enumeration of the ledger's stages -/

/-- The candidate range of packed triples `⟨n, ⟨j, c⟩⟩` with `n, j, c ≤ s`: every such triple is
`< candBound s` (monotonicity of `Nat.pair`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def candBound (s : ℕ) : ℕ := Nat.pair s (Nat.pair s s) + 1

/-- The Boolean stage test on a packed candidate `k = ⟨n, ⟨j, c⟩⟩`: `n, j, c ≤ s`, published, and
`c` a rational code.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def entryTest (e : ℕ → PublicationSchedule) (s k : ℕ) : Bool :=
  decide (k.unpair.1 ≤ s) && decide (k.unpair.2.unpair.1 ≤ s) &&
    decide (k.unpair.2.unpair.2 ≤ s) && (Encodable.decode (α := ℚ) k.unpair.2.unpair.2).isSome &&
    decide ((e k.unpair.2.unpair.1).e k.unpair.1 ≤ s)

/-- `entryTest_eq_true_iff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma entryTest_eq_true_iff {e : ℕ → PublicationSchedule} {s k : ℕ} :
    entryTest e s k = true ↔
      (k.unpair.1 ≤ s ∧ k.unpair.2.unpair.1 ≤ s ∧ k.unpair.2.unpair.2 ≤ s ∧
        (e k.unpair.2.unpair.1).e k.unpair.1 ≤ s ∧
        (Encodable.decode (α := ℚ) k.unpair.2.unpair.2).isSome = true) := by
  unfold entryTest
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- The (at most one) entry contributed by packed candidate `k` at stage `s`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def entryAt (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (s k : ℕ) : List (ℕ × ℕ × Bool) :=
  cond (entryTest e s k) [ledgerEntry a k.unpair.2.unpair.1 k.unpair.1 k.unpair.2.unpair.2] []

/-- The stage-`s` entries collected over the candidates `k < K`, by structural recursion.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def recEntries (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (s : ℕ) :
    ℕ → List (ℕ × ℕ × Bool)
  | 0 => []
  | k + 1 => recEntries a e s k ++ entryAt a e s k

/-- `mem_entryAt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_entryAt {a : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule} {s k : ℕ} {x : ℕ × ℕ × Bool} :
    x ∈ entryAt a e s k ↔
      (k.unpair.1 ≤ s ∧ k.unpair.2.unpair.1 ≤ s ∧ k.unpair.2.unpair.2 ≤ s ∧
        (e k.unpair.2.unpair.1).e k.unpair.1 ≤ s ∧
        (Encodable.decode (α := ℚ) k.unpair.2.unpair.2).isSome = true) ∧
      x = ledgerEntry a k.unpair.2.unpair.1 k.unpair.1 k.unpair.2.unpair.2 := by
  unfold entryAt
  rw [← entryTest_eq_true_iff]
  cases entryTest e s k
  · simp
  · simp

/-- `mem_recEntries`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_recEntries {a : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule} {s : ℕ}
    {x : ℕ × ℕ × Bool} : ∀ {K : ℕ}, x ∈ recEntries a e s K ↔ ∃ k, k < K ∧ x ∈ entryAt a e s k
  | 0 => by simp [recEntries]
  | K + 1 => by
      rw [recEntries, List.mem_append, mem_recEntries (K := K)]
      constructor
      · rintro (⟨k, hk, hx⟩ | hx)
        · exact ⟨k, by omega, hx⟩
        · exact ⟨K, by omega, hx⟩
      · rintro ⟨k, hk, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact Or.inl ⟨k, hk, hx⟩
        · exact Or.inr hx

/-- `Nat.pair` is monotone in both arguments.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pair_le_pair {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    Nat.pair a b ≤ Nat.pair a' b' := by
  have h1 : Nat.pair a b ≤ Nat.pair a' b := by
    rcases ha.lt_or_eq with h | rfl
    · exact (Nat.pair_lt_pair_left b h).le
    · exact le_rfl
  have h2 : Nat.pair a' b ≤ Nat.pair a' b' := by
    rcases hb.lt_or_eq with h | rfl
    · exact (Nat.pair_lt_pair_right a' h).le
    · exact le_rfl
  exact h1.trans h2

/-- The recursive enumeration has the ledger schedule's stages as its `toFinset`s.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem recEntries_toFinset (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (s : ℕ) :
    (recEntries a e s (candBound s)).toFinset = (ledgerSchedule a e).lits s := by
  ext x
  rw [List.mem_toFinset, mem_recEntries, ledgerSchedule_lits, List.mem_toFinset,
    mem_ledgerEntries]
  constructor
  · rintro ⟨k, -, hk⟩
    rw [mem_entryAt] at hk
    obtain ⟨⟨hn, hj, hc, he, hd⟩, rfl⟩ := hk
    exact ⟨_, _, _, hn, hj, hc, he, hd, rfl⟩
  · rintro ⟨n, j, c, hn, hj, hc, he, hd, rfl⟩
    refine ⟨Nat.pair n (Nat.pair j c), ?_, ?_⟩
    · have h2 : Nat.pair n (Nat.pair j c) ≤ Nat.pair s (Nat.pair s s) :=
        pair_le_pair hn (pair_le_pair hj hc)
      unfold candBound
      omega
    · rw [mem_entryAt]
      refine ⟨?_, ?_⟩
      · simp only [Nat.unpair_pair]
        exact ⟨hn, hj, hc, he, hd⟩
      · simp only [Nat.unpair_pair]

/-- `ratOfCode` is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ratOfCode_prim : Primrec ratOfCode :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const 0)

/-- `candBound` is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma candBound_prim : Primrec candBound :=
  Primrec.succ.comp (Primrec₂.natPair.comp Primrec.id (Primrec₂.natPair.comp Primrec.id Primrec.id))

/-- The entry list of a candidate is computable in `(s, k)` from a computable table and computable
publication schedules.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma entryAt_computable {a : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule}
    (ha : Computable fun p : ℕ × ℕ => a p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) :
    Computable fun q : ℕ × ℕ => entryAt a e q.1 q.2 := by
  -- Projections of the packed candidate.
  have hs : Primrec fun q : ℕ × ℕ => q.1 := Primrec.fst
  have hk : Primrec fun q : ℕ × ℕ => q.2 := Primrec.snd
  have hn : Primrec fun q : ℕ × ℕ => q.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hjc : Primrec fun q : ℕ × ℕ => q.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hj : Primrec fun q : ℕ × ℕ => q.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hjc)
  have hc : Primrec fun q : ℕ × ℕ => q.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hjc)
  -- The primitive recursive part of the test.
  have hand : Primrec₂ (fun x y : Bool => x && y) := Primrec.dom_bool₂ _
  have hle1 : Primrec fun q : ℕ × ℕ => decide (q.2.unpair.1 ≤ q.1) :=
    Primrec.nat_le.decide.comp hn hs
  have hle2 : Primrec fun q : ℕ × ℕ => decide (q.2.unpair.2.unpair.1 ≤ q.1) :=
    Primrec.nat_le.decide.comp hj hs
  have hle3 : Primrec fun q : ℕ × ℕ => decide (q.2.unpair.2.unpair.2 ≤ q.1) :=
    Primrec.nat_le.decide.comp hc hs
  have hsome : Primrec fun q : ℕ × ℕ =>
      (Encodable.decode (α := ℚ) q.2.unpair.2.unpair.2).isSome :=
    Primrec.option_isSome.comp ((Primrec.decode (α := ℚ)).comp hc)
  have htest1 : Primrec fun q : ℕ × ℕ => decide (q.2.unpair.1 ≤ q.1) &&
      decide (q.2.unpair.2.unpair.1 ≤ q.1) && decide (q.2.unpair.2.unpair.2 ≤ q.1) &&
      (Encodable.decode (α := ℚ) q.2.unpair.2.unpair.2).isSome :=
    hand.comp (hand.comp (hand.comp hle1 hle2) hle3) hsome
  -- The publication clause, computable through `he`.
  have htest2 : Computable fun q : ℕ × ℕ =>
      decide ((e q.2.unpair.2.unpair.1).e q.2.unpair.1 ≤ q.1) :=
    (Primrec₂.to_comp Primrec.nat_le.decide).comp (he.comp (hj.to_comp.pair hn.to_comp))
      hs.to_comp
  have htest : Computable fun q : ℕ × ℕ => entryTest e q.1 q.2 :=
    ((Primrec₂.to_comp hand).comp htest1.to_comp htest2).of_eq fun q => rfl
  -- The polarity, computable through `a` and rational comparison.
  have hle : Computable fun q : ℕ × ℕ =>
      decide (a q.2.unpair.2.unpair.1 q.2.unpair.1 ≤ ratOfCode q.2.unpair.2.unpair.2) :=
    ((Primrec₂.to_comp ratLE_prim.decide).comp (ha.comp (hj.to_comp.pair hn.to_comp))
      ((ratOfCode_prim.comp hc).to_comp) : _)
  have hpol : Computable fun q : ℕ × ℕ =>
      decide (ratOfCode q.2.unpair.2.unpair.2 < a q.2.unpair.2.unpair.1 q.2.unpair.1) := by
    refine ((Primrec.dom_bool Bool.not).to_comp.comp hle).of_eq fun q => ?_
    rw [← decide_not]
    exact decide_eq_decide.mpr not_le
  have hpay : Primrec fun q : ℕ × ℕ =>
      ledgerPayload q.2.unpair.2.unpair.1 q.2.unpair.1 q.2.unpair.2.unpair.2 :=
    (Primrec₂.natPair.comp hn (Primrec₂.natPair.comp hj hc)).of_eq fun q => rfl
  have hentry : Computable fun q : ℕ × ℕ =>
      ledgerEntry a q.2.unpair.2.unpair.1 q.2.unpair.1 q.2.unpair.2.unpair.2 :=
    ((Computable.const ledgerFamily).pair (hpay.to_comp.pair hpol)).of_eq fun q => rfl
  exact (Computable.cond htest (Computable.list_cons.comp hentry (Computable.const []))
    (Computable.const [])).of_eq fun q => rfl

/-- `recEntries` agrees with the `Nat.rec` form `Computable.nat_rec` produces.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma recEntries_eq_rec (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (s : ℕ) : ∀ K : ℕ,
    recEntries a e s K = Nat.rec (motive := fun _ => List (ℕ × ℕ × Bool)) []
      (fun k IH => IH ++ entryAt a e s k) K
  | 0 => rfl
  | K + 1 => by rw [recEntries, recEntries_eq_rec a e s K]

/-- **The ledger's stage lists are computable** from a computable table and computable
publication schedules (`Computable.nat_rec` over the candidate range).
Source: mandate T1.4
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem ledgerEntries_rec_computable {a : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule}
    (ha : Computable fun p : ℕ × ℕ => a p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) :
    Computable fun s => recEntries a e s (candBound s) := by
  have h1 : Computable fun q : ℕ × (ℕ × List (ℕ × ℕ × Bool)) => q.2.2 :=
    Computable.snd.comp Computable.snd
  have h2 : Computable fun q : ℕ × (ℕ × List (ℕ × ℕ × Bool)) => (q.1, q.2.1) :=
    Computable.fst.pair (Computable.fst.comp Computable.snd)
  have h3 : Computable fun q : ℕ × (ℕ × List (ℕ × ℕ × Bool)) => entryAt a e q.1 q.2.1 :=
    ((entryAt_computable ha he).comp h2).of_eq fun q => rfl
  have hh : Computable₂ fun (s : ℕ) (p : ℕ × List (ℕ × ℕ × Bool)) =>
      p.2 ++ entryAt a e s p.1 :=
    (Computable.list_append.comp h1 h3).of_eq fun q => rfl
  refine (Computable.nat_rec candBound_prim.to_comp (Computable.const []) hh).of_eq fun s => ?_
  rw [recEntries_eq_rec]

/-! ## T1.4: the ledger process is computable -/

/-- **T1.4 (headline). The ledger process is a computable deductive process**, given a computable
base, a computable published table `a` and computable publication schedules `e` — through FAF's
`DeductiveProcessComputation.union_toComputable`. The certificate is `Computable`, not `Primrec`:
this is the one a LIA quote table satisfies (`OneWay.lean`), where `bli-found`'s `Primrec` form
cannot be met. Scope: one-way.
Source: mandate T1.4; [[route-negative-introspective]] §4.4 (vq-wiki-2-017 (a), "computable … legal deductive processes"); root-deference-037
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem ledgerProcess_computable {base : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hbase : ComputableDeductiveProcess base)
    (ha : Computable fun p : ℕ × ℕ => a p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) :
    ComputableDeductiveProcess (ledgerProcess base a e) :=
  DeductiveProcessComputation.union_toComputable hbase.nonemptyComputation.some
    (literalProcess_computable_ofComputable (ledgerSchedule a e)
      (fun s => recEntries a e s (candBound s)) (recEntries_toFinset a e)
      (ledgerEntries_rec_computable ha he)).nonemptyComputation.some

end Cleanroom.Found.LiQuoteLane
