import Cleanroom.Bli.BliFound.Extend
import Cleanroom.Bli.BliFound.Tags
import Cleanroom.Found.LiAsympCalc.Defs
import LogicalInduction.Properties.SelfTrust
import LogicalInduction.Properties.ExpectationAffine
import LogicalInduction.Framework.Expectations
import LogicalInduction.Framework.Machine.ThresholdMachine

/-!
# `li-quote-lane`: definitions of record

The definitions module of the package `Cleanroom.Found.LiQuoteLane` ([[li-quote-lane-mandate]]).
Only definitions (and the two membership lemmas that pin them) live here; theorem files import
this one. Everything is stated over FAF's objects (`DeductiveProcess`, `LUV`, `History`,
`IsLogicalInductor`, `DeferralFunction`, `EF`) and `bli-found`'s decided-literal extension
`extendBy`, so that the fourteen dependents state their two-market headlines without inventing a
ledger of their own.

**Scope: one-way.** Every object here models the channel *`H` reads `A`*: a fixed inductor `A`
publishes numbers, and `H`'s deductive process is augmented with decided threshold literals that
record them. Nothing here is two-way; the two-way (mutually reading) pair is `li-coupled-pair`'s
open row of record.

**Conventions pinned here** (dependents rely on them):

* `PublicationSchedule` is the *weak* `n ≤ e n` of [[deference-in-logical-induction-v6]] §0.4 and
  [[setting-and-notation]] (same-day publication allowed); [[li-deference]]'s strict `n < e n` is
  the instance `DeferralFunction.toPublicationSchedule`.
* The ledger atom for item `j`, day `n`, threshold `r` is `freshAtom 3 ⟨n, ⟨j, ⌜r⌝⌝⟩⟩` — family `3`
  of `bli-found`'s registry, day first so that `Size.atomDay` reads the day. Its threshold code is
  exactly FAF's `arithmeticThresholdLUV` shape (`quoteAtom ⟨code, ⟨n, ⌜r⌝⟩⟩`) with the fresh
  family in place of the tag-2 quotation shell, so every `LUV` lemma of FAF applies. **Payload
  collision (disclosed):** `bli-found`'s example `dayVaryingSchedule` also uses family `3` with
  payload `⟨n, k⟩`; the two are never adjoined to one process.
* The ledger literal for threshold `r` has FAF's strict polarity `⌜X > r⌝`: it is affirmed when
  `r < a j n` and denied when `a j n ≤ r` (so at `r = a j n` it is *denied*, a polarity
  `PCWorld.ValuesAt` leaves free; nothing downstream sees it). The corpus's "`a_n ≥ k/n`" is the
  complement of the same information (disclosure (β) of the mandate).
* Thresholds are *code-bounded*: at stage `s` the literals for all `n, j, ⌜r⌝ ≤ s` with
  `(e j).e n ≤ s` are present (disclosure (α)); the corpus's day-`n` grid `k/n` is a sub-schedule.
  `ledgerSchedule_mem_iff` (`Ledger.lean`) records which threshold is decided by which stage.
-/

namespace Cleanroom.Found.LiQuoteLane

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## A. Publication schedules -/

/-- A **publication schedule**: the stage `e n ≥ n` at which the day-`n` item is posted into the
reader's process. Weak (`n ≤ e n`): same-day publication is allowed, as in v6 §0.4 and
[[setting-and-notation]]; the strict `n < e n` of [[li-deference]] is
`DeferralFunction.toPublicationSchedule`. Scope: one-way.
Source: [[setting-and-notation]] lines 50–71 (vq-wiki-001); [[deference-in-logical-induction-v6]] §0.4
Kind: D
Fidelity: exact (weak form of record; strict form is an instance)
Hyps: n/a -/
structure PublicationSchedule where
  /-- The publication stage of day `n`. -/
  e : ℕ → ℕ
  /-- Publication never precedes the day. -/
  le : ∀ n, n ≤ e n

/-- Same-day publication: `e n = n`. Scope: one-way.
Source: [[deference-in-logical-induction-v6]] §0.4 (the `n ≤ e(n)` case); Known issue 1
Kind: D
Fidelity: exact
Hyps: n/a -/
def PublicationSchedule.sameDay : PublicationSchedule := ⟨id, fun _ => le_rfl⟩

/-- Next-day publication: `e n = n + 1`. Scope: one-way.
Source: [[li-deference]] lines 106–113 (the strict schedule at its cheapest); mandate T6.2
Kind: D
Fidelity: exact
Hyps: n/a -/
def PublicationSchedule.succ : PublicationSchedule := ⟨Nat.succ, fun n => Nat.le_succ n⟩

/-- `li-deference`'s strict publication function, as a FAF `DeferralFunction` (`f n > n`, graph in
`FP`), viewed as a publication schedule. Scope: one-way.
Source: [[li-deference]] lines 106–113 (root-deference-2-004 (d)); Known issue 1
Kind: D
Fidelity: exact
Hyps: n/a -/
def DeferralFunction.toPublicationSchedule (f : DeferralFunction) : PublicationSchedule :=
  ⟨f.f, fun n => (f.lt n).le⟩

/-- `toPublicationSchedule_e`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma DeferralFunction.toPublicationSchedule_e (f : DeferralFunction) (n : ℕ) :
    (DeferralFunction.toPublicationSchedule f).e n = f.f n := rfl

/-- The strict instance publishes strictly after the day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma DeferralFunction.toPublicationSchedule_lt (f : DeferralFunction) (n : ℕ) :
    n < (DeferralFunction.toPublicationSchedule f).e n := f.lt n

/-! ## B. The ledger LUV and the ledger schedule -/

/-- The fresh-atom family this package owns in `bli-found`'s registry: `3` ("ledger atoms").
Source: `bli-found` `freshAtom` registry (family 3 is registered to `li-quote-lane`)
Kind: D
Fidelity: n/a -/
def ledgerFamily : ℕ := 3

/-- The payload of the ledger atom for item `j`, day `n`, threshold code `c`: `⟨n, ⟨j, c⟩⟩`, day
first (registry rule, so `Size.atomDay` reads the day).
Source: mandate T1.1
Kind: D
Fidelity: n/a -/
def ledgerPayload (j n c : ℕ) : ℕ := Nat.pair n (Nat.pair j c)

/-- The payload is injective in `(j, n, c)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ledgerPayload_inj {j n c j' n' c' : ℕ} :
    ledgerPayload j n c = ledgerPayload j' n' c' ↔ n = n' ∧ j = j' ∧ c = c' := by
  unfold ledgerPayload
  constructor
  · intro h
    have h1 := Nat.pair_eq_pair.mp h
    have h2 := Nat.pair_eq_pair.mp h1.2
    exact ⟨h1.1, h2.1, h2.2⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-- **The ledger LUV** `α_{j,n}` of the reader's language: the `[0,1]`-LUV whose threshold sentence
`⌜α_{j,n} > r⌝` is the fresh atom `freshAtom 3 ⟨n, ⟨j, ⌜r⌝⟩⟩`. `j` indexes the published item
(several numbers per day; the family-of-schedules extension is an instance), `n` the day. The
threshold code has exactly the shape of FAF's `arithmeticThresholdLUV code n` (`quoteAtom
⟨code, ⟨n, ⌜r⌝⟩⟩`) with the run's fresh family in place of the tag-2 quotation shell. The atoms
are *decided* by `ledgerSchedule`, which is what makes the LUV "determined at the published value"
a theorem (`ledgerLuv_determinedVia`, `Ledger.lean`) rather than a hypothesis. Scope: one-way.
Source: [[setting-and-notation]] lines 50–71 (vq-wiki-001); [[deference-in-logical-induction-v6]] §0.4 lines 100–104
Kind: D
Fidelity: exact, with disclosures (α) code-bounded thresholds and (β) strict polarity (module docstring)
Hyps: n/a -/
def ledgerLuv (j n : ℕ) : LUV :=
  ⟨fun r => freshAtom ledgerFamily (ledgerPayload j n (Encodable.encode r))⟩

/-- `ledgerLuv_gt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma ledgerLuv_gt (j n : ℕ) (r : ℚ) :
    (ledgerLuv j n).gt r = freshAtom ledgerFamily (ledgerPayload j n (Encodable.encode r)) := rfl

/-- The rational named by a code (`0` on a non-code), the same junk convention as FAF's
`decodedQuotationRat`, restated here so that `Defs` imports no `Construction.Quotation` module.
Source: none: infrastructure (FAF `decodedQuotationRat`)
Kind: D
Fidelity: n/a -/
def ratOfCode (c : ℕ) : ℚ := (Encodable.decode (α := ℚ) c).getD 0

/-- `ratOfCode_encode`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma ratOfCode_encode (r : ℚ) : ratOfCode (Encodable.encode r) = r := by
  simp [ratOfCode]

/-- The schedule entry recording item `j`'s day-`n` value `a j n` at threshold code `c`: the ledger
atom of family `3`, payload `⟨n, ⟨j, c⟩⟩`, with polarity `decide (ratOfCode c < a j n)` — FAF's
strict `⌜X > r⌝` reading (disclosure (β)).
Source: mandate T1.1
Kind: D
Fidelity: n/a -/
def ledgerEntry (a : ℕ → ℕ → ℚ) (j n c : ℕ) : ℕ × ℕ × Bool :=
  (ledgerFamily, ledgerPayload j n c, decide (ratOfCode c < a j n))

/-- The entries present at stage `s`: for every `n, j, c ≤ s` with `(e j).e n ≤ s` and `c` the
code of a rational, the entry `ledgerEntry a j n c`. A list (so that the computability
certificate is the list itself); `ledgerSchedule` takes its `toFinset`.
Source: mandate T1.1
Kind: D
Fidelity: n/a -/
def ledgerEntries (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (s : ℕ) :
    List (ℕ × ℕ × Bool) :=
  (List.range (s + 1)).flatMap fun n =>
    (List.range (s + 1)).flatMap fun j =>
      (List.range (s + 1)).filterMap fun c =>
        if (e j).e n ≤ s ∧ (Encodable.decode (α := ℚ) c).isSome = true then
          some (ledgerEntry a j n c) else none

/-- Membership in the stage-`s` entry list.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_ledgerEntries {a : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule} {s : ℕ}
    {x : ℕ × ℕ × Bool} :
    x ∈ ledgerEntries a e s ↔ ∃ n j c, n ≤ s ∧ j ≤ s ∧ c ≤ s ∧ (e j).e n ≤ s ∧
      (Encodable.decode (α := ℚ) c).isSome = true ∧ x = ledgerEntry a j n c := by
  simp only [ledgerEntries, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨n, hn, j, hj, c, hc, hx⟩
    split_ifs at hx with h
    simp only [Option.some.injEq] at hx
    exact ⟨n, j, c, by omega, by omega, by omega, h.1, h.2, hx.symm⟩
  · rintro ⟨n, j, c, hn, hj, hc, he, hd, rfl⟩
    refine ⟨n, by omega, j, by omega, c, by omega, ?_⟩
    rw [if_pos ⟨he, hd⟩]

/-- Entries are never withdrawn.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ledgerEntries_mono (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) :
    ∀ s, ∀ x ∈ ledgerEntries a e s, x ∈ ledgerEntries a e (s + 1) := by
  intro s x hx
  rw [mem_ledgerEntries] at hx ⊢
  obtain ⟨n, j, c, hn, hj, hc, he, hd, rfl⟩ := hx
  exact ⟨n, j, c, by omega, by omega, by omega, by omega, hd, rfl⟩

/-- **The ledger schedule** of a published table `a : ℕ → ℕ → ℚ` (`a j n` = item `j`'s day-`n`
number) under per-item publication schedules `e`: at stage `s` the literals
`(3, ⟨n, ⟨j, ⌜r⌝⟩⟩, decide (r < a j n))` for all `n, j, ⌜r⌝ ≤ s` with `(e j).e n ≤ s`. Finite
(bounded indices), monotone (`ledgerEntries_mono`), and functional with no hypothesis
(`ledgerSchedule_functional`, `Ledger.lean`): one polarity per triple. Scope: one-way.
Source: [[setting-and-notation]] lines 50–71 (vq-wiki-001); [[deference-in-logical-induction-v6]] §0.4; root-deference-036
Kind: D
Fidelity: exact, with disclosures (α) and (β)
Hyps: n/a -/
def ledgerSchedule (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) : LiteralSchedule :=
  LiteralSchedule.ofList (ledgerEntries a e) (ledgerEntries_mono a e)

/-- `ledgerSchedule_lits`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma ledgerSchedule_lits (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (s : ℕ) :
    (ledgerSchedule a e).lits s = (ledgerEntries a e s).toFinset := rfl

/-- **The ledger-augmented deductive process** `DP_H ⊕ ledger`: the base process with the ledger
schedule adjoined stage by stage through `bli-found`'s `extendBy` (FAF's
`DeductiveProcess.union`). This is the corpus's `H⁺`-process: the reader's own process plus the
decided threshold facts that record what `A` published. Scope: one-way.
Source: [[setting-and-notation]] lines 50–71 (vq-wiki-001); [[deference-in-logical-induction-v6]] §0.4 lines 100–104; root-deference-036; anson-012 (via `bli-found`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def ledgerProcess (base : DeductiveProcess) (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) :
    DeductiveProcess :=
  extendBy base (ledgerSchedule a e)

/-- `ledgerProcess_D`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma ledgerProcess_D (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (s : ℕ) :
    (ledgerProcess base a e).D s = base.D s ∪ (ledgerEntries a e s).toFinset.image literalOf := rfl

/-! ## C. The cross-market quotation package (a hypothesis package) -/

/-- **The cross-market quote package** (T2.1). `Y n` is the LUV `⌜𝔼^H_{f n}(X n)⌝` of `A`'s
language: `quote_codes` says the family is e.c. (FAF's `MachineThresholdCodeSeq`), and
`reflected` says every world consistent with `A`'s completed theory `DPA` values `Y n` at `H`'s
realized day-`f n` expectation of `X n`. It mirrors FAF's `ExpectedFutureExpectationQuote P DP f
X Y` with the one history split into `H` (inside the expectation) and `DPA` (the process that
determines it); `source_codes` is left to the consumer (it is about `X`, not the quote) and
`affine` is dropped (FAF's is a same-market portfolio certificate the endpoints construct, not a
hypothesis a dependent needs).

**Hypothesis package (Kind D).** Its `reflected` field is a *modelling hypothesis* on `DPA`: that
`A`'s completed theory determines `H`'s day-`f(n)` expectation. For an arbitrary inductor `A`
this needs Σ₁-completeness of `Γ_A` about the machine computing `H` — `li-coupled-pair` target
(1). Over a ledger-augmented `DPA` it is a theorem (T2.4, `MirrorPair.lean`). Every headline
stated over this package lists it as hypothesis (c) until discharged. **The package carries no
world:** over a `DPA` with a contradictory stage `reflected` is vacuous, so the package is
inhabited for every `H`, `X`, `f` (audit r2 adversarial non-blocking 3, probe
`AdvR2CrossQuoteVacuous.lean`) — the same shape as FAF's `ExpectedFutureExpectationQuote`, whose
consumers carry `hworld`. A headline stated over this package must also carry
`∀ n, ∃ v, v.ConsistentWith (DPA.D n)` (at the mirror instance: `paperMirror_hworld`,
`cleanMirror_hworld`, lifted by `ledgerProcess_theoryWorld`). Scope: one-way (`A` reads `H`'s
realized expectation; nothing is said about `H` reading `A`).
Source: [[faithful-acceleration]] §4(II) (root-fa-002, the (A2)/(A3) assumption); [[setting-and-notation]] (vq-wiki-001, "new: a cross-market quote LUV"); root-deference-036 (the contract `C_n`); [[deference-in-logical-induction-v6]] §5.2 (A2)–(A3)
Kind: D
Fidelity: variant: `ExpectedFutureExpectationQuote` with the history split into `H` and `DPA`, `source_codes` and `affine` dropped
Hyps: (c) `reflected` (Σ₁-completeness of `Γ_A` about `H`'s machine; `li-coupled-pair`) -/
structure CrossQuotePackage (H : History) (DPA : DeductiveProcess) (f : DeferralFunction)
    (X Y : ℕ → LUV) : Prop where
  /-- The quote family is e.c. -/
  quote_codes : LUV.MachineThresholdCodeSeq Y
  /-- Every completed-theory world of `DPA` values `Y n` at `H`'s realized day-`f n` expectation. -/
  reflected : ∀ n, LUV.DeterminedVia (Y n) DPA ((X n).expect H (f.f n))

/-! ## D. The one-way pair -/

/-- **The one-way coupled pair** (T6): a fixed inductor `A` over `DPA`, a table `a` of `A`'s
prices of the quoted sentences (`a_eq`), and an inductor `H` over the ledger-augmented process
`ledgerProcess DPH a e`, with the process's non-vacuity (`hworld`) and the determinacy of every
ledger LUV at the published value (`determined`). Every field is *derived* by the constructor
`OneWayPair.ofLIA` (`OneWay.lean`, from FAF's `LIA_is_logical_inductor` on both sides) — the
structure only bundles what a dependent needs to state a two-market headline. `H` and `A` are
abstract histories here (the mandate's `liaHistory` instances are `OneWayPair.ofLIA`'s values,
definitionally), so that dependents' statements do not import `Construction.LIA`.

**No recursion:** `A` is fixed, so `a` is a fixed computable table and the ledger stage `s` is
computable outright; the well-founded recursion of `bli-found-liacomputation.md` §4 is for a
process whose stage `n+1` reads the *same* market's day-`n` quotes (vq-wiki-2-017's
self-referential process, and the two-way pair), both `li-coupled-pair`'s. **`hworld` is for the
reader's process only** (the mandate's table): `A_inductor` does not make `DPA` satisfiable, so a
dependent stating something about `A`'s prices carries `∀ n, ∃ v, v.ConsistentWith (DPA.D n)`
itself (`OneWayPair.ofLIA_A_hworld`, `OneWay.lean`). Scope: one-way — `H` reads `A`; `A` does
not read `H`.
Source: [[route-sparse-schedule]] §9, §10 hypothesis 7 (vq-wiki-067); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037); [[faithful-acceleration]] §3 ("taken as given")
Kind: D
Fidelity: variant: plain trader class — `H` is inexploitable by FAF's `EfficientlyComputable` traders; the conjecture's oracle-relativized `H⁺ ⊣ Pᴸ` has no FAF object
Hyps: n/a (a structure; its constructor `OneWayPair.ofLIA` has (a) throughout) -/
structure OneWayPair where
  /-- `A`'s deductive process. -/
  DPA : DeductiveProcess
  /-- `H`'s base deductive process (before the ledger). -/
  DPH : DeductiveProcess
  /-- The quoted sentences: item `j`, day `n`. -/
  quoted : ℕ → ℕ → Sentence
  /-- Per-item publication schedules. -/
  e : ℕ → PublicationSchedule
  /-- The fixed market `A`. -/
  A : History
  /-- The reader's market `H` (over the ledger-augmented process). -/
  H : History
  /-- The published table: `A`'s exact rational day-`n` price of `quoted j n`. -/
  a : ℕ → ℕ → ℚ
  /-- The table is `A`'s prices. -/
  a_eq : ∀ j n, (a j n : ℝ) = A n (quoted j n)
  /-- `A` is a logical inductor over `DPA`. -/
  A_inductor : IsLogicalInductor A DPA
  /-- `H` is a logical inductor over the ledger-augmented process. -/
  H_inductor : IsLogicalInductor H (ledgerProcess DPH a e)
  /-- Every stage of the ledger-augmented process has a consistent world. -/
  hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess DPH a e).D n)
  /-- Every ledger LUV is determined, in the ledger-augmented process, at the published value. -/
  determined : ∀ j n, LUV.DeterminedVia (ledgerLuv j n) (ledgerProcess DPH a e) (a j n)

/-- The reader's process of a one-way pair.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev OneWayPair.process (p : OneWayPair) : DeductiveProcess := ledgerProcess p.DPH p.a p.e

/-! ## E. The ledger price feature and the pull-back -/

/-- **The ledger price feature** `𝔼^H_n(α_{j,n})` as an expressible feature of day-`n` prices: the
price feature of the day-`n` threshold bundle (`LUV.expectAffine`, precision `n + 1`) of the ledger
LUV. It denotes the reader's day-`n` expectation of the ledger LUV (`ledgerFeature_denote`,
`Feature.lean`) and is a `PGenerableWeighting` (`ledgerFeature_pgenerable`). It is the
FAF-faithful substitute for "reading a posted number": FAF's `EF` has no constructor for an
externally posted number, so a published number enters the reader's feature language only through
the decided sentences that name it. Scope: one-way.
Source: [[route-recurring-ccee]] §2 (R2) (vq-wiki-048 (d): `â_n := 𝔼^H_n(⌜a_n⌝)`, the ledger-estimate device); [[route-sparse-schedule]] §2 (L); trust-lab-2-009
Kind: D
Fidelity: exact (FAF's `AffineCombination.priceFeature` of FAF's `LUV.expectAffine`)
Hyps: n/a -/
def ledgerFeature (j n : ℕ) : EF := ((ledgerLuv j n).expectAffine (n + 1)).priceFeature n

/-- **Pull-back of a feature progression along a deferral function** (T5.1): `pullBack f u m` is
`u k` when `m = f k` for the (unique, when `f` is injective) `k ≤ m`, and the zero constant
otherwise. The search is bounded by `m` because `k < f k`. Single market, no ledger.
Source: [[route-transitivity]] §2 line 68 (vq-wiki-2-005)
Kind: D
Fidelity: exact
Hyps: n/a -/
def pullBack (f : DeferralFunction) (u : ℕ → EF) (m : ℕ) : EF :=
  if h : ∃ k, k < m + 1 ∧ f.f k = m then u (Nat.find h) else EF.const 0

/-- The rational twin of `pullBack`: `pullBackRat f q m = q k` when `m = f k` (`k ≤ m`), else `0`.
This is the weight sequence `w` a `ConditionalExpectationQuote` (`thm:ccee`) gates at `w (f n)`.
Source: [[route-transitivity]] §2 line 68 (vq-wiki-2-005); FAF `ConditionalExpectationQuote`
Kind: D
Fidelity: exact
Hyps: n/a -/
def pullBackRat (f : DeferralFunction) (q : ℕ → ℚ) (m : ℕ) : ℚ :=
  if h : ∃ k, k < m + 1 ∧ f.f k = m then q (Nat.find h) else 0

end Cleanroom.Found.LiQuoteLane
