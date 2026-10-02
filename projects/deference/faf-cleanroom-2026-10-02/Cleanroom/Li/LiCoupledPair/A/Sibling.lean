import Cleanroom.Li.LiCoupledPair.DefsHeavy
import Cleanroom.Found.LiQuoteLane.Computability
import Cleanroom.Found.LiQuoteLane.OneWay
import Cleanroom.Found.LiQuoteLane.PaperWitness

/-!
# `li-coupled-pair` · A/Sibling: the sealed-sibling family exists (T4.1)

For a fixed `A` (any computable `DPA`), the per-`N` sealed sibling `H^{[N]}` — FAF's LIA over
`base ⊕ Q^{<N}` (`siblingProcess`, `Defs.lean`) — is a logical inductor over its frozen process
(`sibling_inductor`: `LIA_is_logical_inductor` on `siblingProcess_computable`), every stage of the
frozen process has a consistent world (`sibling_hworld`), the frozen ledger's LUVs of days `n < N`
are determined at `A`'s quotes (`siblingLuv_determinedVia`; **nothing** is stated for `n ≥ N`),
and the sibling **is** `H⁺` until a day-`≥ N` quote is published (`sibling_agree_below`: the two
processes' LIA states coincide at every day `m ≤ s` as long as no quote of day `≥ N` has been
published by stage `s`; through `liaStates_eq_of_eq_prefix`, prefix invariance of FAF's recursion).

**Scope: one-way per `N`** (`A` fixed; `H^{[N]}` reads `A`). The family becomes the two-way object
only when `A` reads it back (`SealedSiblingSystem`, `A/JointInductor.lean`).

**On the mandate's agreement hypothesis.** The mandate states `sibling_agree_below` under
`∀ j, s < (e j).e N`; that implies "no quote of day `≥ N` is published by `s`" only for *monotone*
publication schedules, and `PublicationSchedule` of record (`li-quote-lane`) is weak (`n ≤ e n`,
no monotonicity). The theorem is stated under the exact condition `∀ j n, N ≤ n → s < (e j).e n`,
and the mandate's form is the corollary `sibling_agree_below_of_monotone` (findings, presentation).

N+: `paperSiblingFamily` at `base = DPA = paperDP 𝗜𝚺₁`, `A = liaHistory (paperDP 𝗜𝚺₁)`, next-day
publication: consecutive siblings' processes differ (`paperSiblingProcess_succ_ne`: the day-`N`
affirmed literal is in a stage of `H^{[N+1]}`'s process and in no stage of `H^{[N]}`'s), both
polarities occur in every sibling's ledger for days `n < N` (`paperSibling_both_polarities`). The
quote *values* are not claimed to vary (`li-quote-lane` F7).
-/

namespace Cleanroom.Li.LiCoupledPair.A

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair

/-! ## Structure of the frozen schedule -/

/-- Membership in a stage of the frozen schedule, through the full ledger schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_siblingSchedule_lits {a : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule} {N s : ℕ}
    {x : ℕ × ℕ × Bool} :
    x ∈ (siblingSchedule a e N).lits s ↔ x ∈ (ledgerSchedule a e).lits s ∧ entryDay x < N := by
  rw [siblingSchedule_lits, List.mem_toFinset, mem_siblingEntries, ledgerSchedule_lits,
    List.mem_toFinset]

/-- The frozen schedule is functional (one polarity per atom), inherited from the ledger schedule.
Source: none: infrastructure (`li-quote-lane` `ledgerSchedule_functional`)
Kind: L
Fidelity: n/a -/
theorem siblingSchedule_functional (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (N : ℕ) :
    (siblingSchedule a e N).Functional := by
  intro s f p h
  rw [mem_siblingSchedule_lits, mem_siblingSchedule_lits] at h
  exact ledgerSchedule_functional a e s f p ⟨h.1.1, h.2.1⟩

/-- The frozen schedule touches no atom the full ledger does not.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma siblingSchedule_atoms_subset (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (N : ℕ) :
    (siblingSchedule a e N).atoms ⊆ (ledgerSchedule a e).atoms := by
  rintro c ⟨s, x, hx, rfl⟩
  exact ⟨s, x, (mem_siblingSchedule_lits.mp hx).1, rfl⟩

/-- A base free of the full ledger schedule is free of every frozen schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem processFreeOf_sibling {a : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule}
    {base : DeductiveProcess} (h : ProcessFreeOf (ledgerSchedule a e) base) (N : ℕ) :
    ProcessFreeOf (siblingSchedule a e N) base :=
  fun k φ hφ c hc hmem => h k φ hφ c hc (siblingSchedule_atoms_subset a e N hmem)

/-- **Every stage of the sibling's process is contained in the full ledger process's stage.**
Source: mandate T4 (`siblingProcess_le_ledgerProcess`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem siblingProcess_le_ledgerProcess (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (N s : ℕ) :
    (siblingProcess base a e N).D s ⊆ (ledgerProcess base a e).D s := by
  intro φ hφ
  rw [siblingProcess_D, Finset.mem_union] at hφ
  rw [ledgerProcess_D, Finset.mem_union]
  rcases hφ with h | h
  · exact Or.inl h
  · right
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
    rw [List.mem_toFinset, mem_siblingEntries] at hx
    exact Finset.mem_image.mpr ⟨x, List.mem_toFinset.mpr hx.1, rfl⟩

/-! ## `hworld` and conservativity -/

/-- **Every stage of the sibling's process has a consistent world** (from a base free of family `3`
and satisfiable; `bli-found`'s `extendBy_hworld`).
Source: mandate T4.1 (`sibling_hworld`)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem sibling_hworld {base : DeductiveProcess} {a : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule}
    (hfree : ProcessFreeOf (ledgerSchedule a e) base)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base.D n)) (N : ℕ) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((siblingProcess base a e N).D n) :=
  extendBy_hworld (siblingSchedule_functional a e N) (processFreeOf_sibling hfree N) h

/-- One world consistent with every stage of the sibling's process (FAF's propositional
compactness on `sibling_hworld`): the world quantifier of `siblingLuv_determinedVia` is non-empty.
Source: mandate T4.1
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem sibling_theoryWorld {base : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hfree : ProcessFreeOf (ledgerSchedule a e) base)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base.D n)) (N : ℕ) :
    ∃ v : PCWorld, v.ConsistentWithTheory (siblingProcess base a e N) :=
  DeductiveProcess.exists_consistentWithTheory _ (sibling_hworld hfree h N)

/-! ## Determinacy of the frozen ledger (days `n < N` only) -/

/-- **Stage form.** For `n < N`, once stage `s` has passed `n`, `j`, `⌜r⌝` and `(e j).e n`, every
world consistent with stage `s` of the sibling's process affirms `⌜α_{j,n} > r⌝` when `r < a j n`
and denies it when `a j n ≤ r`.
Source: mandate T4.1 (`sibling_determined`, stage form)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem siblingLuv_decided_by (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (N j n : ℕ) (hN : n < N) (r : ℚ) {s : ℕ}
    (hs : n ≤ s ∧ j ≤ s ∧ Encodable.encode r ≤ s ∧ (e j).e n ≤ s) (v : PCWorld)
    (hv : v.ConsistentWith ((siblingProcess base a e N).D s)) :
    (r < a j n → v.Holds ((ledgerLuv j n).gt r)) ∧
      (a j n ≤ r → ¬ v.Holds ((ledgerLuv j n).gt r)) := by
  have hmem : ∀ b, b = decide (r < a j n) →
      (ledgerFamily, ledgerPayload j n (Encodable.encode r), b) ∈
        (siblingSchedule a e N).lits s :=
    fun b hb => (siblingSchedule_mem_iff a e N j n r b s).mpr
      ⟨hN, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, hb⟩
  have hlit : ∀ b, b = decide (r < a j n) →
      v.Holds (literalOf (ledgerFamily, ledgerPayload j n (Encodable.encode r), b)) := by
    intro b hb
    apply hv
    rw [siblingProcess_D, Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨_, List.mem_toFinset.mpr
      (by rw [← List.mem_toFinset, ← siblingSchedule_lits]; exact hmem b hb), rfl⟩)
  constructor
  · intro hr
    have := hlit true (decide_eq_true hr).symm
    simpa using this
  · intro hr
    have := hlit false (decide_eq_false (not_lt.mpr hr)).symm
    rw [literalOf_false, PCWorld.holds_neg] at this
    exact this

/-- **T4.1, determinacy of the frozen ledger:** for `n < N`, every world consistent with every
stage of `siblingProcess base a e N` values `α_{j,n}` at `a j n` (the table in `[0,1]`). For
`n ≥ N` **nothing is stated** — the frozen process never mentions those atoms
(`siblingSchedule_mem_iff`), and no junk value is assigned (mandate T4 trap).
Source: mandate T4.1 (`sibling_determined`); [[frozen-deliberation-deference-v6]] §3 (anson-016)
Kind: C
Fidelity: exact (days `< N`; silent on `≥ N`, as the source)
Hyps: (a) none (`hmem` is the `[0,1]` range of the table, discharged for LIA quotes by `liaQuote_mem`) -/
theorem siblingLuv_determinedVia (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (N j n : ℕ)
    (hN : n < N) :
    LUV.DeterminedVia (ledgerLuv j n) (siblingProcess base a e N) (a j n) := by
  intro v hv
  unfold PCWorld.ValuesAt
  refine ⟨by exact_mod_cast (hmem j n).1, by exact_mod_cast (hmem j n).2, fun r => ?_⟩
  have hs : n ≤ max (max n j) (max (Encodable.encode r) ((e j).e n)) ∧
      j ≤ max (max n j) (max (Encodable.encode r) ((e j).e n)) ∧
      Encodable.encode r ≤ max (max n j) (max (Encodable.encode r) ((e j).e n)) ∧
      (e j).e n ≤ max (max n j) (max (Encodable.encode r) ((e j).e n)) :=
    ⟨le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _),
      le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩
  have h := siblingLuv_decided_by base a e N j n hN r hs v (hv _)
  constructor
  · intro hr
    exact h.1 (by exact_mod_cast hr)
  · intro hr
    exact h.2 (by exact_mod_cast hr.le)

/-! ## Computability -/

/-- `entryDay` is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma entryDay_prim : Primrec entryDay :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))

/-- A computable enumeration of the frozen schedule's stages: `li-quote-lane`'s computable
enumeration of the ledger's stages, filtered to days `< N`.
Source: mandate T4.1 (`siblingProcess_computable`)
Kind: L
Fidelity: n/a -/
theorem siblingEntries_rec_computable {a : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule}
    (ha : Computable fun p : ℕ × ℕ => a p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) (N : ℕ) :
    Computable fun s =>
      (recEntries a e s (candBound s)).filter fun x => decide (entryDay x < N) := by
  have hp : PrimrecPred fun x : ℕ × ℕ × Bool => entryDay x < N :=
    primrecPred_iff_primrec_decide.mpr
      (Primrec.nat_lt.decide.comp entryDay_prim (Primrec.const N))
  exact (Primrec.listFilter hp).to_comp.comp (ledgerEntries_rec_computable ha he)

/-- The filtered enumeration has the frozen schedule's stages as its `toFinset`s.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem siblingEntries_rec_toFinset (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (N s : ℕ) :
    ((recEntries a e s (candBound s)).filter fun x => decide (entryDay x < N)).toFinset =
      (siblingSchedule a e N).lits s := by
  ext x
  rw [List.mem_toFinset, List.mem_filter, mem_siblingSchedule_lits, ← recEntries_toFinset,
    List.mem_toFinset, decide_eq_true_eq]

/-- **The sibling's process is a computable deductive process** for a computable base, table and
schedules (`li-quote-lane` T1.4's argument on the filtered enumeration).
Source: mandate T4.1 (`siblingProcess_computable`)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem siblingProcess_computable {base : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hbase : ComputableDeductiveProcess base)
    (ha : Computable fun p : ℕ × ℕ => a p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) (N : ℕ) :
    ComputableDeductiveProcess (siblingProcess base a e N) :=
  DeductiveProcessComputation.union_toComputable hbase.nonemptyComputation.some
    ((literalProcess_computable_ofComputable (siblingSchedule a e N)
      (fun s => (recEntries a e s (candBound s)).filter fun x => decide (entryDay x < N))
      (siblingEntries_rec_toFinset a e N)
      (siblingEntries_rec_computable ha he N)).nonemptyComputation.some)

/-! ## T4.1: the sibling inductor -/

/-- **T4.1 (headline). The per-`N` sealed sibling exists over FAF's construction:** for computable
`base` and `DPA`, a computable quoted family and computable schedules, FAF's LIA over
`siblingProcess base (fun j n => liaQuote DPA n (quoted j n)) e N` is a logical inductor over that
frozen process — `LIA_is_logical_inductor` on `siblingProcess_computable` with `A`'s table
computable through its market program (`liaQuote_computable`). **One-way per `N`** (`A` fixed).
Fidelity: plain trader class (as `li-quote-lane` T6.1).
Source: [[frozen-deliberation-deference-v6]] §3–§4 (A1) (anson-016/017); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037)
Kind: C
Fidelity: variant: plain trader class
Hyps: (a) none -/
theorem sibling_inductor (base DPA : DeductiveProcess) (hbase : ComputableDeductiveProcess base)
    (hA : ComputableDeductiveProcess DPA) (quoted : ℕ → ℕ → Sentence)
    (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2) (e : ℕ → PublicationSchedule)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) (N : ℕ) :
    IsLogicalInductor (siblingHistory base (fun j n => liaQuote DPA n (quoted j n)) e N)
      (siblingProcess base (fun j n => liaQuote DPA n (quoted j n)) e N) :=
  LIA_is_logical_inductor (siblingProcess base (fun j n => liaQuote DPA n (quoted j n)) e N)
    (siblingProcess_computable (a := fun j n => liaQuote DPA n (quoted j n)) hbase
      (liaQuote_computable DPA hA quoted hq) he N)

/-! ## The sibling is `H⁺` until a day-`≥ N` quote is published -/

/-- **Prefix invariance of FAF's LIA recursion:** two processes with the same stages `≤ n` have the
same day-`n` state. Through FAF's bounded evaluator: a successful run of
`liaPrefixFromStagesAtFuel` on the stage table `DP.D` to day `n + 1` is the semantic prefix of
*both* processes (`liaPrefixFromStagesAtFuel_sound`, whose table hypothesis only reads stages
`< n + 1`), and the day-`n` state is its last entry (`liaStatePrefix_getD`). The firm on day `n`
reads stages `≤ n` only; the market maker never sees the process.
Source: none: infrastructure (FAF `liaPrefixFromStagesAtFuel_sound`; `bli-found-liacomputation.md` §1, §4)
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem liaStates_eq_of_eq_prefix (DP DP' : DeductiveProcess) (n : ℕ)
    (h : ∀ m, m ≤ n → DP.D m = DP'.D m) : liaStates DP n = liaStates DP' n := by
  obtain ⟨fuel, states, hstates⟩ := exists_liaPrefixFromStagesAtFuel DP.D (n + 1)
  have h1 : states = liaStatePrefix DP (n + 1) :=
    liaPrefixFromStagesAtFuel_sound DP DP.D fuel (n + 1) (fun _ _ => rfl) hstates
  have h2 : states = liaStatePrefix DP' (n + 1) :=
    liaPrefixFromStagesAtFuel_sound DP' DP.D fuel (n + 1) (fun m hm => h m (by omega)) hstates
  have hlen : n < states.length := by
    rw [h1, liaStatePrefix_length]
    omega
  have e1 := liaStatePrefix_getD DP (Nat.lt_succ_self n)
  have e2 := liaStatePrefix_getD DP' (Nat.lt_succ_self n)
  rw [← h1] at e1
  rw [← h2] at e2
  rw [← e1, ← e2, List.getD_eq_getElem states _ hlen, List.getD_eq_getElem states _ hlen]

/-- As long as no quote of a day `≥ N` has been published by stage `s`, the frozen and the full
ledger entry lists coincide at every stage `m ≤ s`.
Source: mandate T4.1 (`siblingProcess_agree_below`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem siblingEntries_eq_below (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (N s : ℕ)
    (hs : ∀ j n, N ≤ n → s < (e j).e n) {m : ℕ} (hm : m ≤ s) :
    siblingEntries a e N m = ledgerEntries a e m := by
  unfold siblingEntries
  rw [List.filter_eq_self]
  intro x hx
  obtain ⟨n, j, c, -, -, -, he, -, rfl⟩ := mem_ledgerEntries.mp hx
  rw [entryDay_ledgerEntry, decide_eq_true_eq]
  by_contra hN
  have := hs j n (not_lt.mp hN)
  omega

/-- The frozen and the full ledger process have the same stages `m ≤ s` as long as no quote of a
day `≥ N` has been published by stage `s`.
Source: mandate T4.1 (`siblingProcess_agree_below`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem siblingProcess_D_eq_below (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (N s : ℕ) (hs : ∀ j n, N ≤ n → s < (e j).e n) {m : ℕ}
    (hm : m ≤ s) :
    (siblingProcess base a e N).D m = (ledgerProcess base a e).D m := by
  rw [siblingProcess_D, ledgerProcess_D, siblingEntries_eq_below a e N s hs hm]

/-- **T4.1, `sibling_agree_below`: the sibling *is* `H⁺` until a day-`≥ N` quote is published.**
If no quote of a day `≥ N` has been published by stage `s`, the LIA states of the frozen process
and of the full ledger process coincide at every day `m ≤ s` (prefix invariance). The hypothesis is
the exact condition; the mandate's `∀ j, s < (e j).e N` is its monotone-schedule corollary below.
`hs` ranges over every item `j`, although only `j ≤ s` can be in stage `s` (`mem_ledgerEntries`);
`∀ j ≤ s` would do. At the witness (`e = succ`) the condition is exactly `s ≤ N`, and it is sharp:
agreement through day `N`, failure of the condition at `s = N + 1` (audit r1 probe
`SiblingAgreeWitness.lean`).
Source: mandate T4.1 (`sibling_agree_below`); [[frozen-deliberation-deference-v6]] §3 ("the frozen prefix runs to index `n−1`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem sibling_agree_below (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (N s : ℕ) (hs : ∀ j n, N ≤ n → s < (e j).e n) {m : ℕ}
    (hm : m ≤ s) :
    liaStates (siblingProcess base a e N) m = liaStates (ledgerProcess base a e) m :=
  liaStates_eq_of_eq_prefix _ _ m fun _ hk =>
    siblingProcess_D_eq_below base a e N s hs (le_trans hk hm)

/-- `sibling_agree_below` for the histories: the sibling's and `H⁺`'s prices coincide at every day
`m ≤ s` before any day-`≥ N` quote is published.
Source: mandate T4.1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem siblingHistory_agree_below (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (N s : ℕ) (hs : ∀ j n, N ≤ n → s < (e j).e n) {m : ℕ}
    (hm : m ≤ s) :
    siblingHistory base a e N m = liaHistory (ledgerProcess base a e) m := by
  unfold siblingHistory liaHistory
  rw [sibling_agree_below base a e N s hs hm]

/-- The mandate's form: for **monotone** publication schedules, `∀ j, s < (e j).e N` suffices.
Source: mandate T4.1 (`sibling_agree_below`, as stated there)
Kind: L
Fidelity: exact (under monotone schedules; `PublicationSchedule` of record is not monotone)
Hyps: (a) none -/
theorem sibling_agree_below_of_monotone (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (hmono : ∀ j, Monotone (e j).e) (N s : ℕ)
    (hs : ∀ j, s < (e j).e N) {m : ℕ} (hm : m ≤ s) :
    liaStates (siblingProcess base a e N) m = liaStates (ledgerProcess base a e) m :=
  sibling_agree_below base a e N s (fun j _ hn => lt_of_lt_of_le (hs j) (hmono j hn)) hm

/-! ## N+: the family over the paper process -/

/-- `A`'s table in the paper witness: the paper LIA's day-`n` prices of the atoms `⟨0, ⟨j, n⟩⟩`.
Source: none: infrastructure (T4.1 witness)
Kind: D
Fidelity: n/a -/
noncomputable abbrev paperTable (j n : ℕ) : ℚ := liaQuote (paperDP 𝗜𝚺₁) n (witnessQuoted j n)

/-- The sibling `N`'s process in the paper witness: `paperDP 𝗜𝚺₁ ⊕ Q^{<N}` with next-day
publication.
Source: none: infrastructure (T4.1 witness)
Kind: D
Fidelity: n/a -/
noncomputable abbrev paperSiblingProcess (N : ℕ) : DeductiveProcess :=
  siblingProcess (paperDP 𝗜𝚺₁) paperTable (fun _ => PublicationSchedule.succ) N

/-- **T4.1 (N+). The sealed-sibling family over `paperDP 𝗜𝚺₁`:** `H^{[N]}` is FAF's LIA over
`paperDP 𝗜𝚺₁ ⊕ Q^{<N}` reading `A = liaHistory (paperDP 𝗜𝚺₁)`'s prices of the day-varying atoms,
published the next day; a family `ℕ → History`, each member an inductor over its frozen process.
Source: mandate T4.1 (`siblingFamily_paper`)
Kind: N+
Fidelity: variant: plain trader class
Hyps: (a) none -/
noncomputable abbrev paperSiblingFamily (N : ℕ) : History :=
  siblingHistory (paperDP 𝗜𝚺₁) paperTable (fun _ => PublicationSchedule.succ) N

/-- Each member of the paper family is an inductor over its frozen process.
Source: mandate T4.1 (`siblingFamily_paper`)
Kind: N+
Fidelity: variant: plain trader class
Hyps: (a) none -/
theorem paperSibling_inductor (N : ℕ) :
    IsLogicalInductor (paperSiblingFamily N) (paperSiblingProcess N) :=
  sibling_inductor (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)
    witnessQuoted witnessQuoted_computable (fun _ => PublicationSchedule.succ)
    succSchedule_computable N

/-- Every stage of every member's process has a consistent world.
Source: mandate T4.1 (`siblingFamily_paper`)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperSibling_hworld (N : ℕ) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperSiblingProcess N).D n) :=
  sibling_hworld (processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁))
    (paperDP_hworld 𝗜𝚺₁) N

/-- In member `N`, the ledger LUVs of days `n < N` are determined at `A`'s quotes.
Source: mandate T4.1 (`siblingFamily_paper`)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperSibling_determined (N j n : ℕ) (hN : n < N) :
    LUV.DeterminedVia (ledgerLuv j n) (paperSiblingProcess N) (paperTable j n) :=
  siblingLuv_determinedVia _ _ _ (fun j n => liaQuote_mem (paperDP 𝗜𝚺₁) n (witnessQuoted j n))
    N j n hN

/-- **N+ grounds: consecutive siblings' processes differ.** The affirmed literal of item `j`, day
`N`, threshold `-1` is in a stage of `H^{[N+1]}`'s process and in no stage of `H^{[N]}`'s (not in
the frozen ledger, `siblingSchedule_mem_iff`; not in `paperDP 𝗜𝚺₁`, cleanroom-free).
Source: mandate T4.1 (`siblingFamily_paper`: "prove `siblingProcess … N ≠ siblingProcess … (N+1)` as processes")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperSiblingProcess_succ_ne (N : ℕ) : paperSiblingProcess (N + 1) ≠ paperSiblingProcess N := by
  intro heq
  set j : ℕ := 0
  set s : ℕ := max (max N j) (max (Encodable.encode (-1 : ℚ)) (N + 1))
  have hmem : (ledgerFamily, ledgerPayload j N (Encodable.encode (-1 : ℚ)), true) ∈
      (siblingSchedule paperTable (fun _ => PublicationSchedule.succ) (N + 1)).lits s := by
    rw [siblingSchedule_mem_iff]
    refine ⟨Nat.lt_succ_self N, le_max_of_le_left (le_max_left _ _),
      le_max_of_le_left (le_max_right _ _), le_max_of_le_right (le_max_left _ _),
      le_max_of_le_right (le_max_right _ _), ?_⟩
    have : (-1 : ℚ) < paperTable j N := by
      linarith [(liaQuote_mem (paperDP 𝗜𝚺₁) N (witnessQuoted j N)).1]
    simp [this]
  have hin : freshAtom ledgerFamily (ledgerPayload j N (Encodable.encode (-1 : ℚ))) ∈
      (paperSiblingProcess (N + 1)).D s := by
    rw [siblingProcess_D, Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨_, by rw [← siblingSchedule_lits]; exact hmem, rfl⟩)
  rw [heq, siblingProcess_D, Finset.mem_union] at hin
  rcases hin with h | h
  · exact (paperDP_cleanroomFree 𝗜𝚺₁ s _ h).freshAtomCode_notMem ledgerFamily
      (ledgerPayload j N (Encodable.encode (-1 : ℚ))) (by simp [freshAtom])
  · obtain ⟨x, hx, hx'⟩ := Finset.mem_image.mp h
    rw [← siblingSchedule_lits, mem_siblingSchedule_lits] at hx
    have hday : entryDay x = N := by
      obtain ⟨n', j', c', -, -, -, -, -, rfl⟩ :=
        mem_ledgerEntries.mp (List.mem_toFinset.mp (by rw [ledgerSchedule_lits] at hx; exact hx.1))
      rw [entryDay_ledgerEntry]
      simp only [ledgerEntry, literalOf] at hx'
      rcases hb : decide (ratOfCode c' < paperTable j' n') with _ | _ <;> rw [hb] at hx' <;>
        simp only [Bool.cond_false, Bool.cond_true] at hx'
      · exact absurd hx' (by simp [freshAtom])
      · exact (ledgerPayload_inj.mp (freshAtom_inj.mp hx').2).1
    omega

/-- **N+ grounds: both polarities occur in every member's frozen ledger**, for every item and every
day `n < N` (`r = -1` affirmed, `r = 2` denied).
Source: mandate T4.1 (`siblingFamily_paper`)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperSibling_both_polarities (N j n : ℕ) (hN : n < N) :
    (∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (-1 : ℚ)), true) ∈
        (siblingSchedule paperTable (fun _ => PublicationSchedule.succ) N).lits s) ∧
      ∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (2 : ℚ)), false) ∈
        (siblingSchedule paperTable (fun _ => PublicationSchedule.succ) N).lits s := by
  obtain ⟨⟨s₁, h₁⟩, ⟨s₂, h₂⟩⟩ := ledgerSchedule_both_polarities paperTable
    (fun _ => PublicationSchedule.succ) (fun j n => liaQuote_mem (paperDP 𝗜𝚺₁) n (witnessQuoted j n))
    j n
  refine ⟨⟨s₁, ?_⟩, ⟨s₂, ?_⟩⟩
  · rw [mem_siblingSchedule_lits]
    exact ⟨h₁, by simp [entryDay, ledgerPayload, hN]⟩
  · rw [mem_siblingSchedule_lits]
    exact ⟨h₂, by simp [entryDay, ledgerPayload, hN]⟩

end Cleanroom.Li.LiCoupledPair.A
