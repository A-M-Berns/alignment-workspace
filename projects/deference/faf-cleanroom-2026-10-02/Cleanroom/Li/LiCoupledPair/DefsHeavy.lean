import Cleanroom.Li.LiCoupledPair.Defs
import LogicalInduction.Construction.LIACompiler
import LogicalInduction.Construction.Paper.TheoremDP
import LogicalInduction.Construction.Quotation.MarketQuoteCodes

/-!
# `li-coupled-pair`: definitions of record whose statements need the LIA compiler (shared)

The heavy half of the package's definitions ([[li-coupled-pair-mandate]] §Definitions; the light
half is `Defs.lean`). Two definitions live here because their *statements* cannot be written
without `Construction/LIACompiler.lean`:

* `UniformLIAEvaluator` — the one named hypothesis of the package. Its type is
  `Computable (fun p : (List (Finset Sentence) × ℕ) × ℕ => liaPrefixFromStagesAtFuel …)`, which
  needs `Primcodable (Option (List RationalBeliefState))`; FAF declares
  `Primcodable RationalBeliefState` in `LIACompiler.lean` (line 150), not in `LIAComputation.lean`.
* `SigmaPair` — angle A's determinacy pair, stated over `paperDP T` (`Construction/Paper/TheoremDP`,
  which imports the compiler through `Construction/Paper/ComputationDP`).

So the mandate's "the joint recursion file imports `LIAComputation` only" holds for `A/Joint.lean`
(which imports `Defs.lean`, not this file), while every file that *consumes* the hypothesis or
`paperDP` carries the compiler anyway — as `li-quote-lane`'s `PaperQuotation.lean` and
`Witnesses.lean` already do.
-/

namespace Cleanroom.Li.LiCoupledPair

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane

/-! ## A. The named hypothesis: uniform computability of FAF's bounded LIA evaluator -/

/-- **`UniformLIAEvaluator`** — the package's one named hypothesis: FAF's bounded LIA state-prefix
evaluator `liaPrefixFromStagesAtFuel` is computable **uniformly in the stage table** (presented as
a finite list, read through `decodedStageTable`), the fuel and the day. FAF proves exactly this,
as the **`private`** lemma `liaPrefixFromStagesAtFuel_prim`
(`Construction/LIACompiler.lean:3665`, in `Primrec` form); its public boundary
(`LIABoundedEvaluatorCompiler`, `liaEncodedQuoteNatAtFuel_computable`) is per fixed
`DeductiveProcessComputation`, which is what blocks the jointly defined processes of the two-way
pair and the sealed-sibling system from reaching `LIA_is_logical_inductor`. Taken as a named
hypothesis, graded **(b)** "FAF private lemma; API request: make `liaPrefixFromStagesAtFuel_prim`
public". Every theorem assuming it says so in `Hyps:`, and its ledger row reads
`partial: UniformLIAEvaluator (b)`. `uniform_of_primrec` discharges it in one line from the
`Primrec` form, so an API fix discharges every consumer at once. Stated with `Computable`, which
is what the consumers need (`ledgerProcess_computable` takes `Computable` tables).
Source: [[li-coupled-pair-mandate]] §Context / §Definitions; FAF `liaPrefixFromStagesAtFuel_prim` (private)
Kind: D
Fidelity: n/a (a hypothesis of record; (b) FAF private lemma)
Hyps: n/a -/
def UniformLIAEvaluator : Prop :=
  Computable fun p : (List (Finset Sentence) × ℕ) × ℕ =>
    liaPrefixFromStagesAtFuel (decodedStageTable p.1.1) p.1.2 p.2

/-- The `Primrec` form (FAF's private `liaPrefixFromStagesAtFuel_prim`) implies the hypothesis:
the one-line discharge an FAF API fix would provide.
Source: [[li-coupled-pair-mandate]] §Definitions
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem uniform_of_primrec
    (h : Primrec fun p : (List (Finset Sentence) × ℕ) × ℕ =>
      liaPrefixFromStagesAtFuel (decodedStageTable p.1.1) p.1.2 p.2) :
    UniformLIAEvaluator :=
  h.to_comp

/-! ## B. The Σ₁ determinacy pair (angle A's carrier) -/

/-- **The Σ₁ determinacy pair** `SigmaPair`: `H` is an inductor over `DPH0 ⊕ (ledger of A's prices
of `quotedA j n`, published at `(e j).e n`)` where `A := liaHistory (paperDP T)` is FAF's paper
LIA (`A_eq`), and `A`'s *completed theory* determines `H`'s realized day-`f n` expectations of
`XH n` through FAF's own quotation LUVs: `code` is a `RationalQuoteCode T` naming the computable
sequence `n ↦ MH.expectQuoteAt XH n (f n)` (`H`'s exact rational expectation, through `H`'s market
program `MH`), and `package` is the discharged `CrossQuotePackage H (paperDP T) f XH code.luv`
(`crossQuotePackage_sigma`, `A/Sigma.lean`).

**Scope: two-way in determinacy, one-way in timing.** `H` reads `A` at the controlled stages
`(e j).e n`; `A`'s theory determines `H`'s expectations, but `paperDP T` decides the quotation
literal `(code.luv n).gt r` at a dovetail stage **nobody controls** (`bli-found` F-14): there is no
"decided by stage `σ(n)`" here. This is **not** the plan's two-way pair (`TwoWayPair`,
`Defs.lean`), whose `A`-side reading is timed by a payout schedule; a dependent that needs the
timing takes the mirror ledger (`li-quote-lane` T2.4) or the OPEN `twoWayPair_exists`. Fidelity
against [[fa-positive-results-corrected-v3]] (A3): `exact (determinacy); timing: none` — (A3)
asks for exactly determinacy ("no bound on how long the construction takes to run").
Source: [[faithful-acceleration]] §4(II) (root-fa-002); [[fa-positive-results-corrected-v3]] (A2)–(A3); anson-2-014; [[route-sparse-schedule]] §1, §10 (S1) (vq-wiki-029)
Kind: D
Fidelity: exact (determinacy); timing: none
Hyps: n/a (a structure; `sigmaPair_paper` inhabits it with (a) throughout) -/
structure SigmaPair where
  /-- The arithmetic theory of `A`'s process. -/
  T : LO.FirstOrder.ArithmeticTheory
  /-- `T` is Δ₁-definable. -/
  [deltaOne : T.Δ₁]
  /-- `T` extends `𝗥₀` (Σ₁-completeness, through `BooleanQuoteCode.ofComputable`). -/
  [r0 : 𝗥₀ ⪯ T]
  /-- `H`'s base process. -/
  DPH0 : DeductiveProcess
  /-- What `H` reads of `A`. -/
  quotedA : ℕ → ℕ → Sentence
  /-- Publication schedules of `A`'s quotes into `H`'s process. -/
  e : ℕ → PublicationSchedule
  /-- The LUVs of `H`'s language whose deferred expectations `A`'s theory determines. -/
  XH : ℕ → LUV
  /-- The lookahead. -/
  f : DeferralFunction
  /-- The market `A`. -/
  A : History
  /-- `A` is FAF's paper LIA over `paperDP T`. -/
  A_eq : A = liaHistory (paperDP T)
  /-- The market `H`. -/
  H : History
  /-- `H` is an inductor over its process, which reads `A`'s exact day-`n` prices. -/
  H_inductor : IsLogicalInductor H
    (ledgerProcess DPH0 (fun j n => liaQuote (paperDP T) n (quotedA j n)) e)
  /-- `H`'s exact market program. -/
  MH : MarketComputation H
  /-- `A`'s quotation code for `H`'s realized deferred expectations. -/
  code : RationalQuoteCode T (fun n => MH.expectQuoteAt XH n (f.f n))
  /-- The cross-market quote package, discharged. -/
  package : CrossQuotePackage H (paperDP T) f XH code.luv
  /-- Every stage of `A`'s process has a consistent world. -/
  hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP T).D n)
  /-- Every stage of `H`'s process has a consistent world. -/
  hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith
    ((ledgerProcess DPH0 (fun j n => liaQuote (paperDP T) n (quotedA j n)) e).D n)

attribute [instance] SigmaPair.deltaOne SigmaPair.r0

/-- `H`'s process of a Σ₁ pair.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable abbrev SigmaPair.processH (p : SigmaPair) : DeductiveProcess :=
  ledgerProcess p.DPH0 (fun j n => liaQuote (paperDP p.T) n (p.quotedA j n)) p.e

end Cleanroom.Li.LiCoupledPair
