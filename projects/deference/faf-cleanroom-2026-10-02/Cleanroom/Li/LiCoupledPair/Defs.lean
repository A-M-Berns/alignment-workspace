import Cleanroom.Found.LiQuoteLane.Defs
import Cleanroom.Found.LiQuoteLane.Ledger
import LogicalInduction.Construction.LIA

/-!
# `li-coupled-pair`: definitions of record (shared, light)

The definitions module of the package `Cleanroom.Li.LiCoupledPair` ([[li-coupled-pair-mandate]]
§Definitions). Angle A writes it; angle B imports it. Everything is stated over FAF's objects and
`li-quote-lane`'s definitions of record (`ledgerLuv`, `ledgerEntries`, `ledgerSchedule`,
`ledgerProcess`, `PublicationSchedule`, `CrossQuotePackage`); no new fresh-atom family is
introduced (the sibling family reuses `li-quote-lane`'s family `3`).

**Layout.** This file is the *light* half: it imports only `LiQuoteLane.Defs`/`.Ledger` and
`Construction.LIA`. The two definitions of record whose *statements* need the LIA compiler —
`UniformLIAEvaluator` (its type mentions `Option (List RationalBeliefState)`, whose `Primcodable`
instance FAF declares in `Construction/LIACompiler.lean`) and `SigmaPair` (mentions `paperDP`,
and `Construction/Paper/TheoremDP.lean` imports the compiler through `ComputationDP`) — are in
`DefsHeavy.lean`. A file that needs neither should import this one only.

**Scope clauses** (plan §0.4 rule 1) are in every docstring: *one-way* = `H` reads `A` with `A`
fixed; *two-way* = each market's process reads the other's output.

**What is defined here and what is not.** `siblingSchedule`/`siblingProcess`/`siblingHistory` are
the corpus's sealed-sibling family `H^{[N]}` ([[frozen-deliberation-deference-v6]] §3): the ledger
of `A`'s quotes *frozen* at day `N` — quotes of day `≥ N` are **never injected**, not merely
delayed (mandate T4 trap). `SealedSiblingSystem` and `TwoWayPair` are *carriers*: `Prop`-free
bundles of markets, processes, tables and the facts a dependent needs; they assert nothing by
themselves (a structure with a free `Y` or with the inductor facts as fields is a `T`, the
mandate's trap) — the content is in the constructors (`A/Joint.lean`, `A/JointInductor.lean`) and
the OPEN rows `sealedSystem_exists` / `twoWayPair_exists`.
-/

namespace Cleanroom.Li.LiCoupledPair

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane

/-! ## A. The sealed-sibling family: the ledger frozen at day `N` -/

/-- The day of a ledger entry: the first component of its payload `⟨n, ⟨j, c⟩⟩`.
Source: none: infrastructure (`li-quote-lane` `ledgerPayload`, day first)
Kind: D
Fidelity: n/a -/
def entryDay (x : ℕ × ℕ × Bool) : ℕ := x.2.1.unpair.1

/-- `entryDay_ledgerEntry`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma entryDay_ledgerEntry (a : ℕ → ℕ → ℚ) (j n c : ℕ) :
    entryDay (ledgerEntry a j n c) = n := by
  simp [entryDay, ledgerEntry, ledgerPayload]

/-- The stage-`s` entries of the ledger **frozen at day `N`**: `li-quote-lane`'s `ledgerEntries a e s`
restricted to the entries of days `n < N`. Scope: one-way per `N` (`A` fixed).
Source: [[frozen-deliberation-deference-v6]] §3 (anson-016: "`Q^{<n}` settles the quotes `a_1,…,a_{n−1}` as facts and freezes there")
Kind: D
Fidelity: exact (the corpus's `Q^{<N}` at the ledger's granularity; disclosures (α)/(β) of `li-quote-lane` inherited)
Hyps: n/a -/
def siblingEntries (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (N s : ℕ) :
    List (ℕ × ℕ × Bool) :=
  (ledgerEntries a e s).filter fun x => decide (entryDay x < N)

/-- Membership in the frozen entry list.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_siblingEntries {a : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule} {N s : ℕ}
    {x : ℕ × ℕ × Bool} :
    x ∈ siblingEntries a e N s ↔ x ∈ ledgerEntries a e s ∧ entryDay x < N := by
  simp [siblingEntries, List.mem_filter]

/-- Frozen entries are never withdrawn.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma siblingEntries_mono (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (N : ℕ) :
    ∀ s, ∀ x ∈ siblingEntries a e N s, x ∈ siblingEntries a e N (s + 1) := by
  intro s x hx
  rw [mem_siblingEntries] at hx ⊢
  exact ⟨ledgerEntries_mono a e s x hx.1, hx.2⟩

/-- **The sealed-sibling schedule** `Q^{<N}`: the ledger schedule of `A`'s table `a` under the
publication schedules `e`, with every entry of day `≥ N` removed from every stage — frozen, not
delayed. Scope: one-way per `N`.
Source: [[frozen-deliberation-deference-v6]] §3 (anson-016); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037)
Kind: D
Fidelity: exact (frozen prefix at the ledger's granularity)
Hyps: n/a -/
def siblingSchedule (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (N : ℕ) : LiteralSchedule :=
  LiteralSchedule.ofList (siblingEntries a e N) (siblingEntries_mono a e N)

/-- `siblingSchedule_lits`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma siblingSchedule_lits (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (N s : ℕ) :
    (siblingSchedule a e N).lits s = (siblingEntries a e N s).toFinset := rfl

/-- **Which threshold is decided by which stage of the frozen ledger:** the literal for item `j`,
day `n`, threshold `r`, polarity `b` is in stage `s` of `siblingSchedule a e N` iff `n < N` and
`li-quote-lane`'s `ledgerSchedule_mem_iff` clause holds. For `n ≥ N` **no** literal of
`ledgerLuv j n` is ever present (the right-hand side is false), which is the frozen-sibling
content: nothing is said about days `≥ N`, and no junk value is assigned to them.
Source: [[frozen-deliberation-deference-v6]] §3 (anson-016, "never injected")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem siblingSchedule_mem_iff (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (N j n : ℕ)
    (r : ℚ) (b : Bool) (s : ℕ) :
    (ledgerFamily, ledgerPayload j n (Encodable.encode r), b) ∈ (siblingSchedule a e N).lits s ↔
      n < N ∧ (n ≤ s ∧ j ≤ s ∧ Encodable.encode r ≤ s ∧ (e j).e n ≤ s ∧
        b = decide (r < a j n)) := by
  rw [siblingSchedule_lits, List.mem_toFinset, mem_siblingEntries, ← List.mem_toFinset,
    ← ledgerSchedule_lits, ledgerSchedule_mem_iff]
  simp only [entryDay, ledgerPayload, Nat.unpair_pair]
  tauto

/-- **The sealed-sibling process** `D ⊕ Q^{<N}`: the base process with the frozen ledger adjoined
(`bli-found`'s `extendBy`). The corpus's process of `H^{[N]}`. Scope: one-way per `N` (`A` fixed);
the *family* `N ↦ siblingProcess … N` is read by `A` in the two-way system (`SealedSiblingSystem`).
Source: [[frozen-deliberation-deference-v6]] §3 (anson-016); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037)
Kind: D
Fidelity: exact
Hyps: n/a -/
def siblingProcess (base : DeductiveProcess) (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule)
    (N : ℕ) : DeductiveProcess :=
  extendBy base (siblingSchedule a e N)

/-- `siblingProcess_D`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma siblingProcess_D (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (N s : ℕ) :
    (siblingProcess base a e N).D s =
      base.D s ∪ (siblingEntries a e N s).toFinset.image literalOf := rfl

/-- **The sealed-sibling family** `{H^{[N]}}`: FAF's LIA over each frozen process. A function
`ℕ → History`, one inductor per index, as the corpus demands ("blindness forces a family").
Scope: one-way per `N`.
Source: [[frozen-deliberation-deference-v6]] §3, §5 (anson-016)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable abbrev siblingHistory (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (N : ℕ) : History :=
  liaHistory (siblingProcess base a e N)

/-! ## B. The sealed-sibling system (two-way carrier) -/

/-- **The sealed-sibling system** (two-way carrier): three kinds of inductor on one clock —
`A` over `DPA0 ⊕ (contract ledger)`, `H⁺` over `base ⊕ (full quote ledger)`, and the family
`sib N` over `base ⊕ Q^{<N}` — with the contract `C_n` settled at `σ n` to
`Y n := H^{[n]}_{F n}(P^{(n)})`, the sibling's **exact** day-`F n` quote of the contract sentence
(no grid rounding: FAF quotes are exact rationals; anson-2-014's flag, Fidelity `variant`).
`A`'s quote table `a` is `A`'s prices of the quoted sentences (`a_eq`), and `A`'s contract atoms
are `ledgerLuv 0 n` of `A`'s language, determined at `Y n` (`determinedA`). Schedules:
`e_lt_F : (e j).e n < F n` (publication before the sibling's horizon), `F_lt_σ : F n < σ n`
(settlement after the horizon). Scope: **two-way** — `A` reads the siblings (through `Y`), the
siblings and `H⁺` read `A` (through `a`).

**Carrier, not claim.** Every field is a fact a dependent needs; the structure asserts nothing.
The content is the constructor `sealedSystem_of_uniform` (`A/JointInductor.lean`, under the named
hypothesis `UniformLIAEvaluator`) and the OPEN row `sealedSystem_exists`
(`li-coupled-pair-open.txt`). A dependent stating a two-way headline over `S : SealedSiblingSystem`
reads `partial: over the OPEN pair` unless it instantiates the constructor.

**Two disclosures (repair round 1).** (i) `A`'s process `ledgerProcess DPA0 (fun _ n => Y n)
(fun _ => σ)` records `Y n` under *every* item index `j` (the ledger enumerates `j ≤ s`), so it
decides `ledgerLuv j n` at `Y n` for all `j`; `determinedA` speaks of item `0` only, the contract
atom of record `C_n = ledgerLuv 0 n`. The copies at `j ≥ 1` are consistent duplicates, not second
contracts (audit r1 fidelity N6 / adversarial §3.4). (ii) Family 3 (`ledgerLuv`) is used on both
sides: `A`'s process records `Y n` and `H⁺`'s records `a j n` under the same sentences
`ledgerLuv j n`. The processes are separate, so nothing clashes, but `quoted` and `contract` must
stay **outside family 3** — a `quoted j n := (ledgerLuv 0 n).gt r` (the source's `a_n := A_n(C_n)`
channel) would make `H⁺`'s own ledger literal carry a second meaning. The witness `paperSealedSpec`
reads the tag-0 atoms `witnessQuoted` (audit r1 adversarial §3.3; a note for `def-frozen-sibling`).
Source: [[frozen-deliberation-deference-v6]] §3–§5 (anson-016/017); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037)
Kind: D
Fidelity: variant: exact rational contract (no grid rounding); plain trader class
Hyps: n/a (a structure) -/
structure SealedSiblingSystem where
  /-- The weaker reasoner's base process (shared by `H⁺` and every sibling). -/
  base : DeductiveProcess
  /-- `A`'s base process (before the contract ledger). -/
  DPA0 : DeductiveProcess
  /-- Per-item publication schedules of `A`'s quotes into the `H`-side processes. -/
  e : ℕ → PublicationSchedule
  /-- The horizon (deferral) `F`: the sibling is read at day `F n`. -/
  F : DeferralFunction
  /-- The settlement schedule `σ` of the contract into `A`'s process. -/
  σ : PublicationSchedule
  /-- Publication precedes the horizon. -/
  e_lt_F : ∀ j n, (e j).e n < F.f n
  /-- The horizon precedes settlement. -/
  F_lt_σ : ∀ n, F.f n < σ.e n
  /-- The quoted sentences: item `j`, day `n` (what the `H`-side reads of `A`). -/
  quoted : ℕ → ℕ → Sentence
  /-- The contract sentences `P^{(n)}` (base-language quantities, as sentences). -/
  contract : ℕ → Sentence
  /-- `A`'s quote table. -/
  a : ℕ → ℕ → ℚ
  /-- The settled values `Y n`. -/
  Y : ℕ → ℚ
  /-- The predictor `A`. -/
  A : History
  /-- The advised reasoner `H⁺` (full ledger). -/
  Hplus : History
  /-- The sealed siblings `H^{[N]}`. -/
  sib : ℕ → History
  /-- The contract settles to the sibling's exact day-`F n` quote of `P^{(n)}`. -/
  Y_eq : ∀ n, Y n = liaQuote (siblingProcess base a e n) (F.f n) (contract n)
  /-- The table is `A`'s prices. -/
  a_eq : ∀ j n, (a j n : ℝ) = A n (quoted j n)
  /-- `A` is an inductor over its base plus the contract ledger (`C_n` settled at `σ n` to `Y n`). -/
  A_inductor : IsLogicalInductor A (ledgerProcess DPA0 (fun _ n => Y n) (fun _ => σ))
  /-- `H⁺` is an inductor over the full ledger process. -/
  Hplus_inductor : IsLogicalInductor Hplus (ledgerProcess base a e)
  /-- Each sibling is an inductor over its frozen process. -/
  sib_inductor : ∀ N, IsLogicalInductor (sib N) (siblingProcess base a e N)
  /-- Every stage of `A`'s process has a consistent world. -/
  hworldA : ∀ n, ∃ v : PCWorld,
    v.ConsistentWith ((ledgerProcess DPA0 (fun _ n => Y n) (fun _ => σ)).D n)
  /-- Every stage of `H⁺`'s process has a consistent world. -/
  hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n)
  /-- Every stage of every sibling's process has a consistent world. -/
  hworldSib : ∀ N n, ∃ v : PCWorld, v.ConsistentWith ((siblingProcess base a e N).D n)
  /-- `A`'s contract LUV `C_n` is determined, in `A`'s process, at `Y n`. -/
  determinedA : ∀ n, LUV.DeterminedVia (ledgerLuv 0 n)
    (ledgerProcess DPA0 (fun _ n => Y n) (fun _ => σ)) (Y n)
  /-- Every ledger LUV is determined, in `H⁺`'s process, at the published quote. -/
  determinedH : ∀ j n, LUV.DeterminedVia (ledgerLuv j n) (ledgerProcess base a e) (a j n)
  /-- In sibling `N`, the ledger LUVs of days `n < N` are determined at the published quote;
  nothing is asserted for `n ≥ N`. -/
  determinedSib : ∀ N j n, n < N →
    LUV.DeterminedVia (ledgerLuv j n) (siblingProcess base a e N) (a j n)

/-! ## C. The two-way pair (two-way carrier, timed both ways) -/

/-- **The two-way pair** (the OPEN row of record's carrier, T5): `A` is an inductor over
`DPA0 ⊕ (ledger of H's realized day-`f n` expectations of `XH n`, published at `(σ j).e n`)` and
`H` an inductor over `DPH0 ⊕ (ledger of A's day-`n` prices of `quotedA j n`, published at
`(e j).e n`)` — each market's process reads the *other's* output, with the timing fields
`aA_eq`/`aH_eq` pinning what is read and `payout_after_lookahead : f n < (σ j).e n` (the payout
is after the lookahead; same-day publication on the `H` side is allowed by `PublicationSchedule`).
Scope: **two-way, timed both ways.**

**Carrier, not claim.** The structure asserts nothing (its inductor fields assumed is the
mandate's `T` trap); the content is the constructor `twoWayPair_of_uniform`
(`A/JointInductor.lean`, under `UniformLIAEvaluator`) and the OPEN row `twoWayPair_exists`. Not to
be confused with `SigmaPair` (`DefsHeavy.lean`): there `A`'s side is `paperDP T` and the reading
is *determinacy via the completed theory* with no timing.

**Family 3 on both sides (repair round 1, audit r1 adversarial §3.3).** The sentence
`ledgerLuv j n` records `aH j n` in `A`'s process and `aA j n` in `H`'s. The processes are
separate, so nothing clashes, but `quotedA` and `XH` must stay **outside family 3**: a
`quotedA j n := (ledgerLuv 0 n).gt r` would be a literal of `H`'s own ledger family with a
different meaning. The witness `paperTwoWaySpec` reads the tag-0 atoms `witnessQuoted` and the
tag-free `cleanX` (`A.cleanX_tagFree`). A note for `def-frozen-sibling`.
Source: [[route-sparse-schedule]] §9 (vq-wiki-067); [[route-negative-introspective]] §4.4 (vq-wiki-2-017 (b)); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037)
Kind: D
Fidelity: variant: plain trader class (`EfficientlyComputable`), FAF quotes exact
Hyps: n/a (a structure) -/
structure TwoWayPair where
  /-- `A`'s base process. -/
  DPA0 : DeductiveProcess
  /-- `H`'s base process. -/
  DPH0 : DeductiveProcess
  /-- What `H` reads of `A`: the sentences `quotedA j n`. -/
  quotedA : ℕ → ℕ → Sentence
  /-- Publication schedules of `A`'s quotes into `H`'s process. -/
  e : ℕ → PublicationSchedule
  /-- What `A` reads of `H`: `H`'s day-`f n` expectation of the LUV `XH n`. -/
  XH : ℕ → LUV
  /-- The lookahead. -/
  f : DeferralFunction
  /-- Payout schedules of `H`'s realized expectations into `A`'s process. -/
  σ : ℕ → PublicationSchedule
  /-- Payout after the lookahead. -/
  payout_after_lookahead : ∀ j n, f.f n < (σ j).e n
  /-- The market `A`. -/
  A : History
  /-- The market `H`. -/
  H : History
  /-- `A`'s published table. -/
  aA : ℕ → ℕ → ℚ
  /-- `H`'s realized-expectation table. -/
  aH : ℕ → ℕ → ℚ
  /-- `aA` is `A`'s prices of the quoted sentences. -/
  aA_eq : ∀ j n, (aA j n : ℝ) = A n (quotedA j n)
  /-- `aH` is `H`'s realized day-`f n` expectation of `XH n`. -/
  aH_eq : ∀ j n, (aH j n : ℝ) = (XH n).expect H (f.f n)
  /-- `A` is an inductor over its process, which reads `H`. -/
  A_inductor : IsLogicalInductor A (ledgerProcess DPA0 aH σ)
  /-- `H` is an inductor over its process, which reads `A`. -/
  H_inductor : IsLogicalInductor H (ledgerProcess DPH0 aA e)
  /-- Every stage of `A`'s process has a consistent world. -/
  hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess DPA0 aH σ).D n)
  /-- Every stage of `H`'s process has a consistent world. -/
  hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess DPH0 aA e).D n)
  /-- `A`'s ledger LUVs are determined at `H`'s realized expectations. -/
  determinedA : ∀ j n, LUV.DeterminedVia (ledgerLuv j n) (ledgerProcess DPA0 aH σ) (aH j n)
  /-- `H`'s ledger LUVs are determined at `A`'s prices. -/
  determinedH : ∀ j n, LUV.DeterminedVia (ledgerLuv j n) (ledgerProcess DPH0 aA e) (aA j n)

/-- `A`'s process of a two-way pair.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev TwoWayPair.processA (p : TwoWayPair) : DeductiveProcess := ledgerProcess p.DPA0 p.aH p.σ

/-- `H`'s process of a two-way pair.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev TwoWayPair.processH (p : TwoWayPair) : DeductiveProcess := ledgerProcess p.DPH0 p.aA p.e

end Cleanroom.Li.LiCoupledPair
