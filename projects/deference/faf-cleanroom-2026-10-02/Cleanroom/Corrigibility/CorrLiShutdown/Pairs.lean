import Cleanroom.Corrigibility.CorrLiShutdown.Setting
import Cleanroom.Found.LiQuoteLane.OneWay
import Cleanroom.Found.LiQuoteLane.Computability

/-!
# `corr-li-shutdown` — Pairs: the two constructors of the shutdown pair of record

* `ShutdownPair.ofOneWayPair`: `li-quote-lane`'s `OneWayPair` **with the roles swapped** — its
  *fixed* market (`p.A`, over `p.DPA`) is this package's overseer, its *reader* (`p.H`, over the
  ledger process) is this package's agent; item `0` of the quoted family is the verdict family
  `φ`, published on the same day. Every field is a projection of `p` except the e.c. certificate
  of `φ` (a parameter) and the `[0,1]` range of the table, derived from the overseer's inductor
  certificate through `a_eq`.
* `ShutdownPair.ofTable`: **any computable `[0,1]` press table** with FAF's LIA as the agent —
  an overseer that is not an inductor ("press every day", a fixed computable press pattern) is
  admitted on purpose; the agent's inductor certificate is `LIA_is_logical_inductor` over
  `ledgerProcess_computable`. This is the constructor the no-T7 witnesses use.

This is the only file of the package importing `Cleanroom.Found.LiQuoteLane.OneWay` (hence
FAF's `LIACompiler`); the theorems never do.
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane

/-- **The shutdown pair from a one-way pair, roles swapped** (design decision 1): the fixed
market of `p` is the overseer, the reader is the agent, `φ := p.quoted 0`, published same-day.
Source: mandate design decision 1; `li-quote-lane` `OneWayPair`
Kind: D
Fidelity: exact (a repackaging of `OneWayPair`'s fields)
Hyps: (a) (`hcodes` is the e.c. certificate of the verdict family, a parameter the caller discharges; `hsame` is the same-day publication of item `0`) -/
noncomputable def ShutdownPair.ofOneWayPair (p : OneWayPair)
    (hcodes : MachineSentenceCodes (p.quoted 0)) (hsame : ∀ n, (p.e 0).e n ≤ n) :
    ShutdownPair where
  base := p.DPH
  table := p.a
  e := p.e
  sameDay := hsame
  φ := p.quoted 0
  φ_codes := hcodes
  table_mem := fun n => by
    haveI := p.A_inductor
    have h := IsLogicalInductor.price_mem_Icc (P := p.A) (DP := p.DPA) n (p.quoted 0 n)
    rw [← p.a_eq 0 n] at h
    exact_mod_cast h
  agent := p.H
  agent_inductor := p.H_inductor
  hworld := p.hworld

/-- The agent of `ofOneWayPair p` is `p`'s reader, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ShutdownPair.ofOneWayPair_agent (p : OneWayPair)
    (hcodes : MachineSentenceCodes (p.quoted 0)) (hsame : ∀ n, (p.e 0).e n ≤ n) :
    (ShutdownPair.ofOneWayPair p hcodes hsame).agent = p.H := rfl

/-- The press table of `ofOneWayPair p` is the overseer's price of `φ n`, definitionally through
`a_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ShutdownPair.ofOneWayPair_press (p : OneWayPair)
    (hcodes : MachineSentenceCodes (p.quoted 0)) (hsame : ∀ n, (p.e 0).e n ≤ n) (n : ℕ) :
    ((ShutdownPair.ofOneWayPair p hcodes hsame).press n : ℝ) = p.A n (p.quoted 0 n) :=
  p.a_eq 0 n

/-- **The shutdown pair from a computable press table** (design decision 1, last clause): the
agent is FAF's LIA over the agent's computable base process plus the ledger of a computable
`[0,1]` table, published same-day; the overseer is the table itself (not an inductor).
Source: mandate design decision 1 ("a press that is any computable `[0,1]` table … is also admitted"); FAF `LIA_is_logical_inductor`; `li-quote-lane` `ledgerProcess_computable`, `ledgerProcess_hworld`
Kind: D (a definition; the discharging theorems are FAF's `LIA_is_logical_inductor` over `ledgerProcess_computable` and `ledgerProcess_hworld` — audit r2 fidelity N4)
Fidelity: exact
Hyps: (a) (`hfree`: the base mentions no ledger atom — `processFreeOf_ledgerSchedule_of_tagFree`; `hworld`: the base is satisfiable stage by stage) -/
noncomputable def ShutdownPair.ofTable (base : DeductiveProcess)
    (hbase : ComputableDeductiveProcess base) (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (press : ℕ → ℚ) (hpress : Computable press) (hmem : ∀ n, 0 ≤ press n ∧ press n ≤ 1)
    (hfree : ProcessFreeOf
      (ledgerSchedule (fun _ n => press n) (fun _ => PublicationSchedule.sameDay)) base)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base.D n)) : ShutdownPair where
  base := base
  table := fun _ n => press n
  e := fun _ => PublicationSchedule.sameDay
  sameDay := fun _ => le_rfl
  φ := φ
  φ_codes := hφ
  table_mem := hmem
  agent := liaHistory (ledgerProcess base (fun _ n => press n) (fun _ => PublicationSchedule.sameDay))
  agent_inductor :=
    LIA_is_logical_inductor _
      (ledgerProcess_computable hbase (hpress.comp Computable.snd) Computable.snd)
  hworld := ledgerProcess_hworld hfree hworld

/-- The agent of `ofTable` is the LIA over the ledger process, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ShutdownPair.ofTable_agent (base : DeductiveProcess)
    (hbase : ComputableDeductiveProcess base) (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (press : ℕ → ℚ) (hpress : Computable press) (hmem : ∀ n, 0 ≤ press n ∧ press n ≤ 1)
    (hfree : ProcessFreeOf
      (ledgerSchedule (fun _ n => press n) (fun _ => PublicationSchedule.sameDay)) base)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base.D n)) :
    (ShutdownPair.ofTable base hbase φ hφ press hpress hmem hfree hworld).agent =
      liaHistory (ledgerProcess base (fun _ n => press n) (fun _ => PublicationSchedule.sameDay)) :=
  rfl

/-- The press of `ofTable` is the table, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ShutdownPair.ofTable_press (base : DeductiveProcess)
    (hbase : ComputableDeductiveProcess base) (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (press : ℕ → ℚ) (hpress : Computable press) (hmem : ∀ n, 0 ≤ press n ∧ press n ≤ 1)
    (hfree : ProcessFreeOf
      (ledgerSchedule (fun _ n => press n) (fun _ => PublicationSchedule.sameDay)) base)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base.D n)) (n : ℕ) :
    (ShutdownPair.ofTable base hbase φ hφ press hpress hmem hfree hworld).press n = press n :=
  rfl

/-- **The shutdown pair from a computable table of published numbers** (design decision 1, last
clause, generalized — audit r1 adversarial N7): item `j` of the ledger is the computable `[0,1]`
table `table j n`, published same-day; item `0` is the press, item `1` the board's report
(`Reports.lean`); the agent is FAF's LIA over the base plus the ledger. `ofTable` is the
one-table special case (`table j n := press n`), on which the report item *is* the press; here
the report can be any computable stream, independent of the press (`WitnessesB.lean`,
`twoTablePair`).
Source: mandate design decision 1 ("a press that is any computable `[0,1]` table … is also admitted"); audit r1 adversarial N7
Kind: D (as `ofTable`; audit r2 fidelity N4)
Fidelity: exact
Hyps: (a) (`hfree`: the base mentions no ledger atom; `hworld`: the base is satisfiable stage by stage) -/
noncomputable def ShutdownPair.ofTables (base : DeductiveProcess)
    (hbase : ComputableDeductiveProcess base) (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (table : ℕ → ℕ → ℚ) (htable : Computable fun p : ℕ × ℕ => table p.1 p.2)
    (hmem : ∀ j n, 0 ≤ table j n ∧ table j n ≤ 1)
    (hfree : ProcessFreeOf (ledgerSchedule table (fun _ => PublicationSchedule.sameDay)) base)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base.D n)) : ShutdownPair where
  base := base
  table := table
  e := fun _ => PublicationSchedule.sameDay
  sameDay := fun _ => le_rfl
  φ := φ
  φ_codes := hφ
  table_mem := hmem 0
  agent := liaHistory (ledgerProcess base table (fun _ => PublicationSchedule.sameDay))
  agent_inductor :=
    LIA_is_logical_inductor _ (ledgerProcess_computable hbase htable Computable.snd)
  hworld := ledgerProcess_hworld hfree hworld

/-- The table of `ofTables` is the given table, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ShutdownPair.ofTables_table (base : DeductiveProcess)
    (hbase : ComputableDeductiveProcess base) (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (table : ℕ → ℕ → ℚ) (htable : Computable fun p : ℕ × ℕ => table p.1 p.2)
    (hmem : ∀ j n, 0 ≤ table j n ∧ table j n ≤ 1)
    (hfree : ProcessFreeOf (ledgerSchedule table (fun _ => PublicationSchedule.sameDay)) base)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base.D n)) (j n : ℕ) :
    (ShutdownPair.ofTables base hbase φ hφ table htable hmem hfree hworld).table j n =
      table j n :=
  rfl

end Cleanroom.Corrigibility.CorrLiShutdown
