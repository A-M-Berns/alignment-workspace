import Cleanroom.Li.LiPseudorandom.Family
import LogicalInduction.Construction.LIACompiler

/-!
# `li-pseudorandom` — T7: computability of the family of record (OPEN)

The certificate that turns `truthStar_learned` into an unconditional theorem is
`IsLogicalInductor (liaHistory (atomDP a (truthStar a g q) g)) (atomDP a (truthStar a g q) g)`,
which by FAF's `LIA_is_logical_inductor` reduces to `ComputableDeductiveProcess (atomDP a
(truthStar a g q) g)`, which reduces (given `Computable a`, `Computable g`) to
`Computable (truthStar a g q)` at a rational target `q`.

**Status: OPEN** (listed in `li-pseudorandom-open.txt`). What is established here:

* `truthStar_isLogicalInductor` — the `IsLogicalInductor` instance **from** `starDP_computable`
  (FAF's `LIA_is_logical_inductor`); it rests on the open statement and is listed open.
* `truthStar_learned_of_computable` — `thm:benford` for the family of record with the instance
  discharged from `starDP_computable`; also listed open, for the same reason.

**What the statement is about (repair round 1).** The round-1 audits showed that with the
enumeration `genWeighting` chosen by `Classical.choice`, `truthStar` was whichever sequence the
chosen surjection produced (the diagonal depends on the enumeration's *order*), and
`Computable (truthStar …)` was not a provable statement about it — the obstacle was in the
definition of record, not in FAF. That is repaired: `genWeighting` is now FAF's machine
enumeration parsed as features, explicit and primitive recursive (`genWeighting_primrec`,
`Countable.lean`), with exact coverage. So `truthStar a g q n` is now a finite computation from
(i) the enumeration — a program, (ii) rational arithmetic (`q`, the tilts and masses are
rationals; `clamp`, `factor`, `mart`, `pot` and the comparison in `diagStep` are rational
operations on rational inputs), and (iii) the LIA's day-`≤ n` quotes on the process determined by
the days `< n` already decided (LIA locality, `liaStates_congr`, `AtomDP.lean`). The open
statement is a genuine unproved step, and its remaining obstacles are:

1. **The LIA evaluator, uniform in the process code** (the main gap). The computation that
   decides day `n` must run the LIA over a process whose code depends on the days `< n`. FAF's
   `liaEntries_computable process : Computable (fun n => encode (liaStates DP n).entries)`
   (`Construction/LIACompiler.lean`) is proved for each fixed
   `process : DeductiveProcessComputation DP`: the process code enters as
   `Primrec.const process.code` in `processStageAtFuel_prim` (`LIACompiler.lean:212–218`), upstream
   of the private `liaEncodedEntriesAtFuel_prim` — per-process, not uniform. Mathlib's
   `Nat.Partrec.Code.evaln_prim` is uniform in the code, so a uniform re-run of that development
   (`Primrec₂ (fun code n => …)`) is plausible but is a re-derivation of ~100 private lemmas: an
   FAF API request (**a uniform `liaEntries` code**). Route B (Kleene's
   `Nat.Partrec.Code.fixed_point₂`) needs the same uniformity plus an extensional identification of
   the fixed point's process with `atomDP a (truthStar …) g`.
2. **The rational rendering of the potential**: `EF.denote` of the enumerated features at the
   LIA's rational quotes equals the cast of FAF's `EF.denoteRat` (a routine but sizeable
   bridge), and the real comparison in `diagStep` is then a decidable rational comparison.
3. **The reduction `starDP_computable ← truthStar_computable`**: a `Computable` analogue of FAF's
   `encode_stage_prim_of_list` / `ComputableDeductiveProcess.ofEncodePrim`
   (`Construction/DeductiveDovetail.lean`, stated for `Primrec` stage lists — `truthStar` is at
   best computable), plus `Computable` of `literalOf a x` and of the filtered image that forms
   the stage — routine.

Neither open statement was weakened; no hypothesis `(hcomp : ComputableDeductiveProcess …)` was
smuggled onto T6.3's headline.

This file and `Market.lean` import `LogicalInduction.Construction.LIACompiler` directly
(`Family.lean` and `Countable.lean` reach it transitively through
`Construction/Statistics/HistoricalMaturity` and `…/SettlementCompiler`). `Market.lean` shows
what *is* certified today: for primitive recursive `a` and `x`, `atomDP a x succ` is a
`ComputableDeductiveProcess` and the LIA over it a logical inductor
(`atomDP_succ_computable`, `atomDP_succ_isLogicalInductor`) — the fixed-family case; the open
statement here is the self-referential one, where the stream is the diagonal over that LIA.
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction Filter Topology

/-- **T7 (OPEN).** The family of record at a rational target is computable, for computable
placement `a` and delay profile `g`. Since repair round 1 the enumeration inside the definition
is primitive recursive (`genWeighting_primrec`); what remains is the LIA evaluator uniform in the
process code and the rational rendering of the potential (module docstring, items 1–2).
Source: mandate T7; [[anson-inventory]] anson-034 (the "computable" half of the sub-target)
Kind: OPEN
Fidelity: exact
Hyps: (a) -/
theorem truthStar_computable (a g : ℕ → ℕ) (_ha : Computable a) (_hg : Computable g) (q : ℚ) :
    Computable (truthStar a g (q : ℝ)) := by
  sorry

/-- **T7 (OPEN).** The process of record is a computable deductive process (the paper's
`def:dedproc` certificate), for computable `a`, `g` and rational target. Reduces to
`truthStar_computable` through item 3 of the module docstring.
Source: mandate T7; FAF `ComputableDeductiveProcess`
Kind: OPEN
Fidelity: exact
Hyps: (a) -/
theorem starDP_computable (a g : ℕ → ℕ) (_ha : Computable a) (_hg : Computable g) (q : ℚ) :
    ComputableDeductiveProcess (atomDP a (truthStar a g (q : ℝ)) g) := by
  sorry

/-- **The LIA over the process of record is a logical inductor** — FAF's
`LIA_is_logical_inductor` applied to `starDP_computable`. Rests on the open T7 statement (listed
open for that reason).
Source: mandate T7; FAF `LIA_is_logical_inductor` (`thm:lia`)
Kind: C
Fidelity: exact
Hyps: (a) except `starDP_computable` (OPEN T7) -/
theorem truthStar_isLogicalInductor (a g : ℕ → ℕ) (ha : Computable a) (hg : Computable g)
    (q : ℚ) :
    IsLogicalInductor (liaHistory (atomDP a (truthStar a g (q : ℝ)) g))
      (atomDP a (truthStar a g (q : ℝ)) g) :=
  LIA_is_logical_inductor _ (starDP_computable a g ha hg q)

/-- **`thm:benford` for the family of record, with the inductor certificate discharged from T7**:
the LIA's price of `atom (a n)` on day `n` tends to `q`. Rests on the open T7 statement.
Source: mandate T6.3/T7; FAF `lic_learning_pseudorandom_frequency`
Kind: C
Fidelity: exact
Hyps: (a) except `starDP_computable` (OPEN T7) and `hcodes` ((a)-when-discharged parameter) -/
theorem truthStar_learned_of_computable (a g : ℕ → ℕ) (ha : Computable a) (hg : Computable g)
    (hinj : Function.Injective a) (hg' : ∀ j, j < g j) (q : ℚ) (hq : 0 ≤ q ∧ q ≤ 1)
    (hcodes : MachineSentenceCodes (atomFamily a)) :
    (fun n => liaHistory (atomDP a (truthStar a g (q : ℝ)) g) n (atomFamily a n)) ≈ₙ
      (fun _ => (q : ℝ)) :=
  haveI := truthStar_isLogicalInductor a g ha hg q
  truthStar_learned a g hinj hg' (q : ℝ) (by exact_mod_cast hq) hcodes

end Cleanroom.Li.LiPseudorandom
