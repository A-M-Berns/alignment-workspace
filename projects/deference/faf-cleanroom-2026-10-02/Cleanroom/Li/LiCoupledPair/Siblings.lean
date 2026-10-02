import Cleanroom.Li.LiCoupledPair.A.Sibling
import Cleanroom.Li.LiCoupledPair.B.Sibling
import Cleanroom.Li.LiCoupledPair.B.ConditionedWitness

/-!
# `li-coupled-pair` · Siblings: T4.1 — the sealed-sibling family, two routes, one literal content

Reconciled module (namespace `Cleanroom.Li.LiCoupledPair`) for [[li-coupled-pair-mandate]] T4.1.
Both angles built the family `{H^{[N]}}` ("`A`'s quotes of days `< N` as facts, frozen there;
quotes of index `≥ N` are never injected", anson-016) and proved each member an inductor, over
materially different processes:

* **Of record (angle A): `siblingProcess base a e N := extendBy base (siblingSchedule a e N)`**
  (`Defs.lean`, the mandate's definition) with `H^{[N]} := liaHistory` of it — FAF's LIA built
  fresh on the frozen ledger (`sibling_inductor`, by `LIA_is_logical_inductor` on
  `A.siblingProcess_computable`). Agreement with `H⁺` is at the level of **LIA states**
  (`sibling_agree_below`: the sibling *is* `H⁺` at every day `≤ s` while no day-`≥ N` quote has
  been published by `s` — the exact condition; the mandate's `∀ j, s < (e j).e N` is its
  monotone-schedule corollary, findings F3). Witness `paperSiblingFamily` (N+).
* **Variant kept (angle B): `siblingProcessB DPH0 c₁ σ N := DPH0 ∪ prefixProcess (frozenSeq c₁ σ N)`**
  with `H^{[N]} := conditionedHistory P (frozen prefix conjunction)` — a *fixed* inductor `P`
  conditioned on the clocked record of `A`'s table frozen at day `N` (`sibling_inductor_B`, by
  FAF's `thm:scon` with `frozenSeq_codes`). Freezing is exact (`sibling_frozen`: no day-`≥ N`
  literal is ever in any stage), agreement with `H⁺` is **stage equality** below `N`
  (`siblingB_agree_below`). Witness `paperSiblingFamily_B` (N+).

**Reconciliation (`siblingB_literal_iff_siblingA`, new here):** the two processes adjoin the
same ledger literals — for every item `j`, day `n`, rational code `c`, the literal
`ledgerEntry a j n c` is eventually in angle B's frozen prefix process iff it is eventually in
angle A's frozen schedule, and both iff `n < N`. They differ only in *when* (A: the publisher's
stage `(e j).e n`; B: the clocked position) and in *how* the inductor is obtained (fresh LIA vs
conditioning), which is why the package ships both. No disagreement: neither proves what the
other refutes.

One-way per `N` (`A` fixed) throughout; the family becomes the two-way object only once `A`
reads it (`TwoWay.lean`, T4.3).
-/

namespace Cleanroom.Li.LiCoupledPair

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane
open Nat.Partrec (Code)

/-! ## A. T4.1 of record: the frozen ledger process and FAF's LIA over it (angle A) -/

export Cleanroom.Li.LiCoupledPair.A (siblingProcess_computable liaStates_eq_of_eq_prefix
  siblingProcess_le_ledgerProcess sibling_theoryWorld sibling_agree_below_of_monotone
  siblingHistory_agree_below paperTable paperSiblingProcess paperSiblingFamily
  paperSibling_inductor paperSibling_hworld paperSibling_determined paperSiblingProcess_succ_ne
  paperSibling_both_polarities)

/-- **T4.1 (headline of record). The sealed sibling `H^{[N]}` is a logical inductor over its
frozen process, for a fixed computable `A`:** FAF's `LIA_is_logical_inductor` on
`siblingProcess base (liaQuote DPA · ·) e N`, whose computability is the filtered enumeration of
li-quote-lane's stage lists. Angle A (`A.sibling_inductor`). Scope: one-way per `N`.
Source: [[frozen-deliberation-deference-v6]] §3–§4 (A1) (anson-016/017); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037); mandate T4.1
Kind: C
Fidelity: variant: plain trader class
Hyps: (a) none -/
theorem sibling_inductor (base DPA : DeductiveProcess) (hbase : ComputableDeductiveProcess base)
    (hA : ComputableDeductiveProcess DPA) (quoted : ℕ → ℕ → Sentence)
    (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2) (e : ℕ → PublicationSchedule)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) (N : ℕ) :
    IsLogicalInductor (siblingHistory base (fun j n => liaQuote DPA n (quoted j n)) e N)
      (siblingProcess base (fun j n => liaQuote DPA n (quoted j n)) e N) :=
  A.sibling_inductor base DPA hbase hA quoted hq e he N

/-- **Every stage of the sibling's process has a consistent world** (for a base free of the ledger
family and satisfiable; `bli-found`'s `extendBy_hworld`). Angle A (`A.sibling_hworld`).
Source: mandate T4.1 (`sibling_hworld`)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem sibling_hworld {base : DeductiveProcess} {a : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule}
    (hfree : ProcessFreeOf (ledgerSchedule a e) base)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base.D n)) (N : ℕ) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((siblingProcess base a e N).D n) :=
  A.sibling_hworld hfree h N

/-- **Determinacy below `N`:** for `n < N`, every completed-theory world of the sibling's process
values `α_{j,n}` at `a j n`. For `n ≥ N` **nothing is stated** — the frozen process never mentions
those atoms (`siblingSchedule_mem_iff`) and no junk value is assigned (the mandate's T4 trap).
Angle A (`A.siblingLuv_determinedVia`).
Source: mandate T4.1 (`sibling_determined`); [[frozen-deliberation-deference-v6]] §3 (anson-016)
Kind: C
Fidelity: exact (days `< N`; silent on `≥ N`, as the source)
Hyps: (a) none (`hmem` is the `[0,1]` range of the table) -/
theorem siblingLuv_determinedVia (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (N j n : ℕ)
    (hN : n < N) :
    LUV.DeterminedVia (ledgerLuv j n) (siblingProcess base a e N) (a j n) :=
  A.siblingLuv_determinedVia base a e hmem N j n hN

/-- **The sibling *is* `H⁺` until a day-`≥ N` quote is published:** if no quote of a day `≥ N` has
been published by stage `s`, the LIA states of the frozen process and of the full ledger process
coincide at every day `m ≤ s` (prefix invariance of FAF's recursion, `liaStates_eq_of_eq_prefix`).
The hypothesis is the exact condition; the mandate's `∀ j, s < (e j).e N` is its corollary for
monotone schedules (`sibling_agree_below_of_monotone`; findings F3). Angle A
(`A.sibling_agree_below`).
Source: mandate T4.1 (`sibling_agree_below`); [[frozen-deliberation-deference-v6]] §3
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem sibling_agree_below (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (N s : ℕ) (hs : ∀ j n, N ≤ n → s < (e j).e n) {m : ℕ}
    (hm : m ≤ s) :
    liaStates (siblingProcess base a e N) m = liaStates (ledgerProcess base a e) m :=
  A.sibling_agree_below base a e N s hs hm

/-! ## B. The variant kept: the sibling by conditioning on the frozen clocked record (angle B) -/

export Cleanroom.Li.LiCoupledPair.B (frozenSeq frozenSeq_codes siblingProcessB siblingCondition
  siblingHistoryB frozenSeq_literal_mem_siblingSchedule siblingProcessB_hworld
  siblingProcessB_theoryWorld siblingPrefix_ne_succ paperSiblingCode paperSiblingCode_spec)

/-- **T4.1 by conditioning: the sealed sibling `P | (frozen clocked record)` is a logical
inductor over `DPH0 ∪ prefixProcess (frozenSeq c₁ σ N)`**, for every `N` — FAF's `thm:scon` with
the certificate `frozenSeq_codes` (one `ifZero` on the day test over `clockedSeq_codes`). Angle B
(`B.sibling_inductor_B`). Scope: one-way per `N`.
Source: [[frozen-deliberation-deference-v6]] §2–§6 (anson-016/017); mandate T4.1 (angle B)
Kind: L (one application of FAF's endpoint; the content is `frozenSeq_codes`, `sibling_frozen`, `siblingB_agree_below`)
Fidelity: variant: plain trader class; FAF's capped conditional; clocked positions
Hyps: (a) none (`hσ` discharged at the witness) -/
theorem sibling_inductor_B (P : History) (DPH0 : DeductiveProcess) [IsLogicalInductor P DPH0]
    (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (hσ : UnaryRuler fun p => (σ p.unpair.1).e p.unpair.2) (N : ℕ) :
    IsLogicalInductor (siblingHistoryB P c₁ σ N) (siblingProcessB DPH0 c₁ σ N) :=
  B.sibling_inductor_B P DPH0 c₁ σ hσ N

/-- **Frozen: never injected.** No ledger literal of a day `n ≥ N` is in any stage of the frozen
prefix process — the source's "quotes of index `≥ N` are never injected", exactly, with no junk
value. Angle B (`B.sibling_frozen`).
Source: [[frozen-deliberation-deference-v6]] §3 (anson-016); mandate T4 traps
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem sibling_frozen (c₁ : Code) (σ : ℕ → PublicationSchedule) (N j n c s : ℕ) (hn : N ≤ n)
    (b : Bool) :
    literalOf (ledgerFamily, ledgerPayload j n c, b) ∉ (prefixProcess (frozenSeq c₁ σ N)).D s :=
  B.sibling_frozen c₁ σ N j n c s hn b

/-- **The conditioned sibling is `H⁺` stage for stage below `N`:** for `s < N` its stage `s` equals
the full clocked process's (positions `≤ s` carry days `≤ s < N`). Angle B
(`B.sibling_agree_below`).
Source: mandate T4.1 (`sibling_agree_below`); anson-016
Kind: P
Fidelity: exact (at the level of stages)
Hyps: (a) none -/
theorem siblingB_agree_below (DPH0 : DeductiveProcess) (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (N s : ℕ) (hs : s < N) :
    (siblingProcessB DPH0 c₁ σ N).D s = (B.clockedProcess DPH0 c₁ σ).D s :=
  B.sibling_agree_below DPH0 c₁ σ N s hs

/-- **Determinacy below `N`, conditioning route:** for `n < N`, every completed-theory world of
`siblingProcessB` values `α_{j,n}` at `a j n`; nothing for `n ≥ N`. Angle B
(`B.ledgerLuv_determinedVia_sibling`).
Source: mandate T4.1 (`sibling_determined`); anson-016
Kind: C
Fidelity: exact (days `< N`)
Hyps: (a) none (`hc`: `c₁` computes the table's polarity; `hmem` the `[0,1]` range) -/
theorem siblingB_determinedVia {a : ℕ → ℕ → ℚ} (DPH0 : DeductiveProcess) (c₁ : Code)
    (σ : ℕ → PublicationSchedule) (hc : ∀ p, c₁.eval p = Part.some (B.gateVal a p))
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (N j n : ℕ) (hn : n < N) :
    LUV.DeterminedVia (ledgerLuv j n) (siblingProcessB DPH0 c₁ σ N) (a j n) :=
  B.ledgerLuv_determinedVia_sibling DPH0 c₁ σ hc hmem N j n hn

/-- **T4.1 witness, conditioning route (N+):** the sibling family at `paperDP 𝗜𝚺₁`,
`A := liaHistory (paperDP 𝗜𝚺₁)`, each `H^{[N]}` the paper LIA conditioned on the frozen clocked
record of `A`'s prices of the tag-0 atoms (next-day gate): inductor, determinacy below `N`,
worlds, and the family varies with `N`. Angle B (`B.paperSiblingFamily`).
Source: mandate T4.1 (`siblingFamily_paper`); [[frozen-deliberation-deference-v6]] §3
Kind: N+
Fidelity: variant: plain trader class; FAF's capped conditional; clocked positions
Hyps: (a) none -/
theorem paperSiblingFamily_B (N : ℕ) :
    IsLogicalInductor
        (siblingHistoryB (liaHistory (paperDP 𝗜𝚺₁)) paperSiblingCode
          (fun _ => PublicationSchedule.succ) N)
        (siblingProcessB (paperDP 𝗜𝚺₁) paperSiblingCode (fun _ => PublicationSchedule.succ) N) ∧
      (∀ j n, n < N → LUV.DeterminedVia (ledgerLuv j n)
        (siblingProcessB (paperDP 𝗜𝚺₁) paperSiblingCode (fun _ => PublicationSchedule.succ) N)
        (liaQuote (paperDP 𝗜𝚺₁) n (witnessQuoted j n))) ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith
        ((siblingProcessB (paperDP 𝗜𝚺₁) paperSiblingCode (fun _ => PublicationSchedule.succ) N).D n)) ∧
      (∃ s, freshAtom ledgerFamily (ledgerPayload 0 N (Encodable.encode (-1 : ℚ))) ∈
        (prefixProcess (frozenSeq paperSiblingCode (fun _ => PublicationSchedule.succ) (N + 1))).D s) ∧
      ∀ s, freshAtom ledgerFamily (ledgerPayload 0 N (Encodable.encode (-1 : ℚ))) ∉
        (prefixProcess (frozenSeq paperSiblingCode (fun _ => PublicationSchedule.succ) N)).D s :=
  B.paperSiblingFamily N

/-! ## C. Reconciliation: the two frozen processes adjoin the same literals -/

/-- **The frozen clocked record eventually writes the literal of `(j, n, c)` iff `n < N`.**
Forward: `sibling_frozen` (nothing of a day `≥ N` is ever written). Backward: angle B's
`frozenSeq_eventually` (below `N` every literal is written once the clock has paid its fuel).
Source: mandate "Reconciler" (two sibling witnesses); anson-016 ("never injected")
Kind: P
Fidelity: exact
Hyps: (a) none (`hc`: `c₁` computes the table's polarity) -/
theorem frozenSeq_literal_iff {a : ℕ → ℕ → ℚ} (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (hc : ∀ p, c₁.eval p = Part.some (B.gateVal a p)) (N j n c : ℕ)
    (hd : (Encodable.decode (α := ℚ) c).isSome = true) :
    (∃ s, literalOf (ledgerEntry a j n c) ∈ (prefixProcess (frozenSeq c₁ σ N)).D s) ↔ n < N := by
  constructor
  · rintro ⟨s, hs⟩
    by_contra hN
    simp only [ledgerEntry] at hs
    exact B.sibling_frozen c₁ σ N j n c s (not_lt.mp hN) _ hs
  · intro hn
    obtain ⟨t, ht⟩ := B.frozenSeq_eventually c₁ σ hc N j n c hn hd
    exact ⟨t, mem_prefixProcess.mpr ⟨t, le_rfl, ht⟩⟩

/-- **The frozen ledger schedule of record carries the entry of `(j, n, c)` at some stage iff
`n < N`** (`siblingSchedule_mem_iff` with the stage `max (max n j) (max c ((e j).e n))`).
Source: mandate "Reconciler"; anson-016
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem siblingSchedule_literal_iff (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (N j n c : ℕ)
    (hd : (Encodable.decode (α := ℚ) c).isSome = true) :
    (∃ s, ledgerEntry a j n c ∈ (siblingSchedule a e N).lits s) ↔ n < N := by
  constructor
  · rintro ⟨s, hs⟩
    rw [siblingSchedule_lits, List.mem_toFinset, mem_siblingEntries, entryDay_ledgerEntry] at hs
    exact hs.2
  · intro hn
    refine ⟨max (max n j) (max c ((e j).e n)), ?_⟩
    rw [siblingSchedule_lits, List.mem_toFinset, mem_siblingEntries, entryDay_ledgerEntry]
    refine ⟨mem_ledgerEntries.mpr ⟨n, j, c, ?_, ?_, ?_, ?_, hd, rfl⟩, hn⟩
    · exact le_max_of_le_left (le_max_left _ _)
    · exact le_max_of_le_left (le_max_right _ _)
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_of_le_right (le_max_right _ _)

/-- **Reconciliation of the two sibling witnesses: they adjoin the same ledger literals.** For
every item `j`, day `n` and rational code `c`, the literal `ledgerEntry a j n c` is eventually
in angle B's frozen prefix process `prefixProcess (frozenSeq c₁ σ N)` iff its entry is eventually
in angle A's frozen schedule `siblingSchedule a σ N` — both iff `n < N`. The two processes differ
in *when* a literal arrives (the publisher's stage `(σ j).e n` vs the clocked position) and in
how their inductor is obtained (fresh LIA vs conditioning), not in what they decide.
Source: mandate "Reconciler" (ships both witnesses); [[frozen-deliberation-deference-v6]] §3
Kind: P
Fidelity: exact
Hyps: (a) none (`hc`: `c₁` computes the table's polarity) -/
theorem siblingB_literal_iff_siblingA {a : ℕ → ℕ → ℚ} (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (hc : ∀ p, c₁.eval p = Part.some (B.gateVal a p)) (N j n c : ℕ)
    (hd : (Encodable.decode (α := ℚ) c).isSome = true) :
    (∃ s, literalOf (ledgerEntry a j n c) ∈ (prefixProcess (frozenSeq c₁ σ N)).D s) ↔
      ∃ s, ledgerEntry a j n c ∈ (siblingSchedule a σ N).lits s :=
  (frozenSeq_literal_iff c₁ σ hc N j n c hd).trans
    (siblingSchedule_literal_iff a σ N j n c hd).symm

end Cleanroom.Li.LiCoupledPair
