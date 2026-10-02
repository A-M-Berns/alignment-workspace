import Cleanroom.Found.LiQuoteLane.Ledger
import Cleanroom.Found.LiQuoteLane.Computability
import LogicalInduction.Construction.LIACompiler

/-!
# `li-quote-lane` · OneWay: the one-way coupled pair exists (T6.1)

The run's N+ generator: for any computable `DPA`, `DPH`, quoted sentences and publication
schedules, FAF's `liaHistory` over the ledger-augmented process `ledgerProcess DPH a e`, with
`a j n := liaQuote DPA n (quoted j n)` the fixed inductor `A`'s exact rational day-`n` prices, is
a FAF logical inductor over that process — `LIA_is_logical_inductor` applied to T1.4, where the
table's computability comes from `A`'s own `MarketComputation`
(`IsLogicalInductor.marketComputable`). Bundled as `OneWayPair.ofLIA` with `A := liaHistory
DPA`, `hworld` (T1.5) and determinacy (T1.2, `hmem` from `liaHistory_range`).

**No well-founded recursion.** `DPA` is fixed, so `liaQuote DPA` is a fixed computable function
and the ledger stage `s` is computable outright. The recursion of `bli-found-liacomputation.md`
§4 is for a process whose stage `n+1` reads *its own* day-`n` quotes (vq-wiki-2-017's
self-referential process, and the two-way pair) — both `li-coupled-pair`'s. The plan's "by
well-founded recursion on the day" describes the two-way case.

**Fidelity against vq-wiki-067: `variant: plain trader class`.** `H⁺` is inexploitable by FAF's
`EfficientlyComputable` traders; the conjecture's oracle-relativized `H⁺ ⊣ Pᴸ` has no FAF
object and is *not* proved. Nothing this run states needs the relativization (T3.1 carries `hL`,
a (c) on the table in FAF's fixed class standing in for (L) — `Readability.lean`; T4.2 needs
nothing).

**What the pair does not carry.** `A_inductor` does not make `A`'s process satisfiable (FAF's
criterion holds vacuously over a process with an unsatisfiable stage), and the structure's
`hworld` is for the *reader's* process only, as the mandate's table specified. A dependent that
states something about `p.A`'s prices for `p : OneWayPair` must carry
`∀ n, ∃ v, v.ConsistentWith (p.DPA.D n)` itself (`OneWayPair.ofLIA_A_hworld`).

This is the only file of the package importing `Construction.LIACompiler` (plan §0.5). Scope:
one-way.
-/

namespace Cleanroom.Found.LiQuoteLane

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc

/-- LIA quotes lie in `[0,1]` (the rational form of `liaHistory_range`).
Source: none: infrastructure (FAF `liaHistory_range`)
Kind: L
Fidelity: n/a -/
theorem liaQuote_mem (DPA : DeductiveProcess) (n : ℕ) (φ : Sentence) :
    0 ≤ liaQuote DPA n φ ∧ liaQuote DPA n φ ≤ 1 := by
  have h := liaHistory_range DPA n φ
  rw [liaHistory_eq_quote_cast] at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- The exact rational quote of a certified market program along computable day and
sentence-code streams is computable (FAF's `MarketComputation.quote_comp_computable`, re-proved
here so that this file imports only `Construction.LIACompiler`).
Source: none: infrastructure (FAF `MarketComputation.quote_comp_computable`)
Kind: L
Fidelity: n/a -/
theorem marketComputation_quote_computable {P : History} (M : MarketComputation P)
    {d g : ℕ × ℕ → ℕ} (hd : Computable d) (hg : Computable g) :
    Computable fun a => M.quote (d a) (g a) := by
  have hin : Computable fun a => Nat.pair (d a) (g a) := Primrec₂.natPair.to_comp.comp hd hg
  have heval : Partrec fun a => M.code.eval (Nat.pair (d a) (g a)) :=
    Nat.Partrec.Code.eval_part.comp (Computable.const M.code) hin
  have henc : Computable fun a => Encodable.encode (M.quote (d a) (g a)) :=
    heval.of_eq fun a => Part.eq_some_iff.mpr (by simpa using M.code_spec (Nat.pair (d a) (g a)))
  exact Computable.encode_iff.mp henc

/-- **The LIA quote table of a computable family of quoted sentences is computable** — through
the `MarketComputation` that `LIA_is_logical_inductor` supplies (`quote_exact`, `code_spec`),
composed with the sentence codes. `Computable`, not `Primrec` (findings F1).
Source: mandate T6.1; FAF `MarketComputation.quote_comp_computable`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem liaQuote_computable (DPA : DeductiveProcess) (hA : ComputableDeductiveProcess DPA)
    (quoted : ℕ → ℕ → Sentence) (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2) :
    Computable fun p : ℕ × ℕ => liaQuote DPA p.2 (quoted p.1 p.2) := by
  obtain ⟨M⟩ := (LIA_is_logical_inductor DPA hA).marketComputable.nonemptyComputation
  have hM := marketComputation_quote_computable M (d := fun p : ℕ × ℕ => p.2)
    (g := fun p : ℕ × ℕ => Encodable.encode (quoted p.1 p.2)) Computable.snd
    (Computable.encode.comp hq)
  refine hM.of_eq fun p => ?_
  have h := M.quote_exact p.2 (quoted p.1 p.2)
  rw [liaHistory_eq_quote_cast] at h
  exact_mod_cast h.symm

/-- **T6.1 (headline). The one-way coupled pair exists**: for computable `DPA`, `DPH`, a
computable family of quoted sentences and computable publication schedules, FAF's constructed
market over the ledger-augmented process — which records `A := liaHistory DPA`'s exact day-`n`
prices of the quoted sentences as decided threshold literals — is a logical inductor over that
process. Composition: `LIA_is_logical_inductor` on `ledgerProcess_computable` (T1.4) with the
table's computability from `A`'s market program. No recursion (module docstring). **No `hfree`
and no `hworld` here**: FAF's `LIA_is_logical_inductor` needs only computability, so over a
`DPH` that already holds opposite family-3 literals the conclusion is FAF's degenerate branch
(`isLogicalInductor_of_stage_unsatisfiable`); the bundle `OneWayPair.ofLIA` carries both
hypotheses and its `hworld` field (T1.5) is what excludes that branch. Scope: one-way;
Fidelity against vq-wiki-067: plain trader class (module docstring).
Source: [[route-sparse-schedule]] §9, §10 hypothesis 7 (vq-wiki-067, conjectured ~0.85); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037); anson-2-002; [[faithful-acceleration]] §3 ("taken as given")
Kind: C
Fidelity: variant: plain trader class (`EfficientlyComputable`), not the conjecture's relativized `Pᴸ`
Hyps: (a) none -/
theorem oneWayPair_inductor (DPA DPH : DeductiveProcess) (hA : ComputableDeductiveProcess DPA)
    (hH : ComputableDeductiveProcess DPH) (quoted : ℕ → ℕ → Sentence)
    (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2) (e : ℕ → PublicationSchedule)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) :
    IsLogicalInductor
      (liaHistory (ledgerProcess DPH (fun j n => liaQuote DPA n (quoted j n)) e))
      (ledgerProcess DPH (fun j n => liaQuote DPA n (quoted j n)) e) :=
  LIA_is_logical_inductor _
    (ledgerProcess_computable hH (liaQuote_computable DPA hA quoted hq) he)

/-- **T6.1, bundled: the one-way pair from FAF's LIA on both sides**, every field derived —
`A := liaHistory DPA` (`LIA_is_logical_inductor`), `H := liaHistory (ledgerProcess DPH a e)`
(`oneWayPair_inductor`), `hworld` (T1.5, base free of family 3 and satisfiable), determinacy
(T1.2 with `hmem` from `liaQuote_mem`). Scope: one-way.
Source: mandate T6.1 (`OneWayPair` of record)
Kind: C
Fidelity: variant: plain trader class
Hyps: (a) none -/
noncomputable def OneWayPair.ofLIA (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (hH : ComputableDeductiveProcess DPH)
    (quoted : ℕ → ℕ → Sentence) (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2)
    (e : ℕ → PublicationSchedule) (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2)
    (hfree : ProcessFreeOf (ledgerSchedule (fun j n => liaQuote DPA n (quoted j n)) e) DPH)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) : OneWayPair where
  DPA := DPA
  DPH := DPH
  quoted := quoted
  e := e
  A := liaHistory DPA
  H := liaHistory (ledgerProcess DPH (fun j n => liaQuote DPA n (quoted j n)) e)
  a := fun j n => liaQuote DPA n (quoted j n)
  a_eq := fun j n => (liaHistory_eq_quote_cast DPA n (quoted j n)).symm
  A_inductor := LIA_is_logical_inductor DPA hA
  H_inductor := oneWayPair_inductor DPA DPH hA hH quoted hq e he
  hworld := ledgerProcess_hworld hfree hworld
  determined := fun j n =>
    ledgerLuv_determinedVia DPH _ e (fun j n => liaQuote_mem DPA n (quoted j n)) j n

/-- `(OneWayPair.ofLIA …).A = liaHistory DPA`, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem OneWayPair.ofLIA_A (DPA DPH : DeductiveProcess) (hA : ComputableDeductiveProcess DPA)
    (hH : ComputableDeductiveProcess DPH) (quoted : ℕ → ℕ → Sentence)
    (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2) (e : ℕ → PublicationSchedule)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2)
    (hfree : ProcessFreeOf (ledgerSchedule (fun j n => liaQuote DPA n (quoted j n)) e) DPH)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    (OneWayPair.ofLIA DPA DPH hA hH quoted hq e he hfree hworld).A = liaHistory DPA := rfl

/-- `(OneWayPair.ofLIA …).H = liaHistory (ledgerProcess DPH a e)`, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem OneWayPair.ofLIA_H (DPA DPH : DeductiveProcess) (hA : ComputableDeductiveProcess DPA)
    (hH : ComputableDeductiveProcess DPH) (quoted : ℕ → ℕ → Sentence)
    (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2) (e : ℕ → PublicationSchedule)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2)
    (hfree : ProcessFreeOf (ledgerSchedule (fun j n => liaQuote DPA n (quoted j n)) e) DPH)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    (OneWayPair.ofLIA DPA DPH hA hH quoted hq e he hfree hworld).H =
      liaHistory (ledgerProcess DPH (fun j n => liaQuote DPA n (quoted j n)) e) := rfl

/-- **What `OneWayPair` does not carry, made explicit:** `A_inductor` does not make `A`'s process
satisfiable — FAF's criterion holds vacuously over a process with an unsatisfiable stage, and
`LIA_is_logical_inductor` needs only computability — and the structure's `hworld` is for the
*reader's* process only, as the mandate's table specified. So `OneWayPair.ofLIA` over a
contradictory `DPA` is a bona fide pair whose fixed market is FAF's LIA over a process no world is
consistent with (audit r2 adversarial non-blocking 4, probe `AdvR2OneWayDegenerateA.lean`). A
dependent that states something about `p.A`'s prices for `p : OneWayPair` must carry
`∀ n, ∃ v, v.ConsistentWith (p.DPA.D n)` itself; for `OneWayPair.ofLIA` it is the base
hypothesis unchanged (`.DPA = DPA` definitionally), and `paperOneWayPair` has it through
`paperDP_hworld`. Adding an `A_hworld` field would change the definition of record (an
orchestrator decision); this lemma is the dependents' handle meanwhile.
Source: none: infrastructure (audit r2 adversarial non-blocking 4)
Kind: L
Fidelity: n/a -/
theorem OneWayPair.ofLIA_A_hworld (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (hH : ComputableDeductiveProcess DPH)
    (quoted : ℕ → ℕ → Sentence) (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2)
    (e : ℕ → PublicationSchedule) (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2)
    (hfree : ProcessFreeOf (ledgerSchedule (fun j n => liaQuote DPA n (quoted j n)) e) DPH)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) :
    ∀ n, ∃ v : PCWorld,
      v.ConsistentWith ((OneWayPair.ofLIA DPA DPH hA hH quoted hq e he hfree hworld).DPA.D n) :=
  hworldA

/-! ## Extension: the family-of-schedules generator -/

/-- **The family-of-schedules generator** (`def-dose-response`'s arms): one `H⁺` deciding `A`'s
quotes of a single computable sentence family `φ` on every schedule of a countable computable
list `e : ℕ → PublicationSchedule` — the instance `quoted j n := φ n` of `OneWayPair.ofLIA`,
with item `j` published on schedule `e j`. Scope: one-way.
Source: mandate, extension (the family-of-schedules generator); `def-dose-response`
Kind: C
Fidelity: variant: plain trader class
Hyps: (a) none -/
noncomputable def OneWayPair.ofLIA_family (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (hH : ComputableDeductiveProcess DPH)
    (φ : ℕ → Sentence) (hφ : Computable φ) (e : ℕ → PublicationSchedule)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2)
    (hfree : ProcessFreeOf (ledgerSchedule (fun _ n => liaQuote DPA n (φ n)) e) DPH)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) : OneWayPair :=
  OneWayPair.ofLIA DPA DPH hA hH (fun _ n => φ n) (hφ.comp Computable.snd) e he hfree hworld

/-- In the family generator, item `j`'s ledger LUV on day `n` is determined at `A`'s day-`n`
price of `φ n`, in the extended process, for every schedule index `j`; and it is decided by
stage `max n j ⌜r⌝ ((e j).e n)` (`ledgerLuv_decided_by`).
Source: mandate, extension
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem OneWayPair.ofLIA_family_determined (DPA DPH : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA) (hH : ComputableDeductiveProcess DPH)
    (φ : ℕ → Sentence) (hφ : Computable φ) (e : ℕ → PublicationSchedule)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2)
    (hfree : ProcessFreeOf (ledgerSchedule (fun _ n => liaQuote DPA n (φ n)) e) DPH)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) (j n : ℕ) :
    LUV.DeterminedVia (ledgerLuv j n)
      (OneWayPair.ofLIA_family DPA DPH hA hH φ hφ e he hfree hworld).process
      (liaQuote DPA n (φ n)) :=
  (OneWayPair.ofLIA_family DPA DPH hA hH φ hφ e he hfree hworld).determined j n

end Cleanroom.Found.LiQuoteLane
