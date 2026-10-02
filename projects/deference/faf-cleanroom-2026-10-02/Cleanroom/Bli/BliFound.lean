import Cleanroom.Bli.BliFound.Tags
import Cleanroom.Bli.BliFound.Extend
import Cleanroom.Bli.BliFound.Size
import Cleanroom.Bli.BliFound.State
import Cleanroom.Bli.BliFound.Constraints
import Cleanroom.Bli.BliFound.PaperInstances
import Cleanroom.Bli.BliFound.Structured
import Cleanroom.Bli.BliFound.Bridge
import Cleanroom.Bli.BliFound.Witnesses
import Cleanroom.Bli.BliFound.StateSentence
import Cleanroom.Bli.BliFound.Emitter
import Cleanroom.Bli.BliFound.Unlinked
import Cleanroom.Bli.BliFound.Grid

/-!
# `bli-found`: FAF-facing foundations of the BLI area and the LI chain

Root module of the package `bli-found` (area `bli`, namespace `Cleanroom.Bli.BliFound`). A
dependent imports this one name and gets:

* **Tags** — the run's fresh-atom allocator `freshAtom family payload` (tags from
  `cleanroomBaseTag = 9`, disjoint from every tag FAF uses; family registry in its docstring),
  the tag-freeness predicates `TagFreeSentence`/`TagFreeProcess`/`TagFreeFamily`/
  `CleanroomFreeSentence`/`CleanroomFreeProcess`.
* **Extend** — `LiteralSchedule`, `literalProcess`, `extendBy DP L := DP.union (literalProcess L)`;
  `literalProcess_consistent`, `extendBy_consistentWith`/`extendBy_hworld` (`hworld` inherited),
  `extendBy_decides_iff`/`extendBy_decidesTheory_iff` (conservativity, anson-012, semantic
  reading), `extendBy_computable`.
* **Size** — `tokenSize` (digit-metered canonical RPN length: FAF's `def:ec` meter),
  `sizeBound n = 2^{2^n}`, `SmallOn`, `smallSet` (finite), `sizeBound_lt_card_smallSet` (from
  day `1`), `atomDay` (reads the day of the run's families, of FAF's tag-`3` product atoms and
  of their tag-`6` old-language copies exactly, of tag-`2` quotation claims as the packed input,
  `≥` the day — so `Sminus` under-approximates the prose scope; the tag-`3`/`6` cases are repair
  round 2's definition-of-record change, audit r2 fidelity B1), `Sminus`.
* **State** — `stateAtom`/`policyPoint`/`actionAt`, `stateAtom_large`/`stateAtom_small`/
  `stateAtom_large_of_writeOut`, the state schedule and `stateProcess`, `bliDP`,
  `bliDP_exclusive`, `bliDP_hworld`, `bliDP_conservative`, `bliDP_computable`,
  `policyLinkProcess` with its transports.
* **Constraints** — `StateSystem` and the constraint predicates `E1x`, `E1r`, `E2x`, `E2i`,
  `E3`, `E3fin`, `E4`, `E5`, `LNK`, `COMP`, `LIC`, `TB`, `PCP`, `D_PC`, `D_ND`, `D_NNU`, the
  bundles `IsBLI_AppB`, `IsBLI_Roman` — all conditioning on B1's `stateAtom` — and their
  **σ-parametric forms** `E2xσ`, `E2iσ`, `E3σ`, `E3finσ`, `E4σ`, `E5σ`, `TBσ`, `IsBLI_AppBσ`,
  `IsBLI_Romanσ` (the state-sentence family a parameter, so faith in the B2 `stateSentence` is
  statable; `E2x S P = E2xσ stateAtom S P` by `rfl`; repair round 2). **`FS` (support = face)
  is not defined here** — it needs the face of a grid and is `bli-superbelief`'s.
* **PaperInstances** — disjointness of fresh atoms from `quoteAtom`/`productAtom`/
  `paperPrimeSentence`/`eventAtom`, `theoremDP_cleanroomFree`/`paperDP_cleanroomFree`, the N+
  day-varying extension of `paperDP 𝗜𝚺₁`, `bliDP_paperDP_hworld` (T5.3 at a real process) with
  the two-state N+ in both the small-code (`twoStates`) and the large-code (`largeStates`,
  `largeStates_stateAtom_large`) regimes, and the product-atom scope lemmas
  `atomDay_productAtom`/`productAtom_notMem_Sminus`.

* **Structured** — the structured-escape size bound `tokenSize_le_of_structured` (`C = 10`):
  every formula code FAF's structured paper-prime parser emits is a tree (`FTree`) that the
  numeric De Morgan involution `negFormulaCode` preserves in shape, so its size is bounded by
  fuel alone. This was the package's one OPEN statement; it is now proved.
* **Bridge** — `MentionedBy`, the bridge lemma `bridge_lemma` (T1: an e.c. trader eventually
  names only day-small sentences), proved in full from FAF's `def:ec` metering through the
  stream lemma, the contraction lemma, the parse-size lemma and the two escape bounds; no
  `sorry` anywhere in the package.
* **Witnesses** — the bridge lemma's N+ on FAF's `buyAtomDaily` with `N = 1`
  (`buyAtomDaily_small_from_one`, no OPEN dependence) and the split's non-degeneracy
  (`largeOn_witness`, `crossing_witness`).

* **StateSentence** — T7, the B2 linked state sentence over FAF's single market `paperDP T`:
  the market's own quote code `marketQuoteCode T` and interval quotes `quoteAt T m φ lo hi`
  (reflected at the market's exact price), the cell literals `cellSentence` (tag-`2` quotation
  atoms `paperDP T` decides), the state sentence `stateSentence T round m q` as their
  conjunction with `stateSentence_reflected`/`_decided`/`_refuted`/`_exclusive`, the cell-form
  linkage predicate `LNKcell` with `LNKcell_stateSentence` (and the `S.val`-to-cell tie
  `b2StateSystem_val_mem_cellOfTable`), and the N+ at `𝗜𝚺₁` (`LNKcell_witness`; two candidate
  tables the rounding can write out, `actualCode`/`flippedCode`, of which exactly the actual one
  holds: `witnessStates_decided`). `Constraints.LNK` (closed intervals, B1's atom hard-coded) is
  refutable for every state system at `quoteAt T` (`Unlinked.lnk_quoteAt_refutable`, findings
  F-13) and is `flagged`; `LNKcell` is the mandate's single-value form. `Sminus` admits none of
  this file's quote atoms (`quoteAt_notMem_Sminus`, findings F-14).

* **Emitter** — stretch S2: the emitter bridge `machineSentenceCodes_eventually_small` (FAF's
  polynomial-time write-out class `MachineSentenceCodes` names only day-small sentences
  eventually; same metering as the bridge lemma) and `not_machineSentenceCodes_stateAtom`: a
  family of state atoms with long write-outs infinitely often is not machine-nameable.
* **Unlinked** — the other half of D5's "true of B2, false by construction for B1", in its
  honest form: `stateAtom_free` (every completed-theory world of `paperDP T` can be overridden
  to hold the fresh state atom) and `lnkcell_stateAtom_iff_unconditional` (linkage for B1's
  atom holds iff the quotes are forced unconditionally — the atom adds nothing), by the first
  pass's conservativity machinery; `lnkcell_fails_at_impossible_cell` (the `(2, 3)` test refutes
  any held state sentence, B1 and B2 alike — not a contrast); `lnk_quoteAt_refutable`
  (`Constraints.LNK` is false for every state system at `quoteAt T`).
* **Grid** — repair round 2: `stateSentence_ne_stateAtom` (the B2 sentence is never B1's atom,
  so the main-body predicates cannot take it), what the cells of `LNKcell_stateSentence` can
  force (`lnkcell_default_cell_tautology`, `hcell_forces_overlap`: legitimate cells for
  `halfRound` necessarily overlap, findings F-16), the market-independent four-table grid
  `fixedStates` with `fixedStates_decided` (exactly the actual table holds) and
  `LNKcell_fixedSystem`, and the `RoundsOf` tie for the B2 system (`b2StateSystem_val_actual`,
  `b2StateSystem_roundsOf` under index coverage).

The bridge lemma, the structured bound, the B2 state sentence, the emitter bridge and the
unlinked-B1 results landed after the definitions release and changed no definition of record.
Repair round 1 (audit r1) added `RoundsOf`, `oneState`/`isBLI_AppB_const_one`,
`stateAtom_actual_holds`, the `flippedCode` witness, the `S.val`-to-cell lemmas, the F-14 scope
lemmas and the Unlinked rewrite; it changed no definition of record either (`LNK`'s docstring
and Fidelity line were corrected, its statement untouched). **Repair round 2 (audit r2) changed
one definition of record**: `Size.atomDay` now reads the day of FAF's tag-`3` product atoms (and
of tag-`6` old-language copies) instead of `0`, which only *removes* sentences from `Sminus`, so
every dependent's faith predicate becomes weaker, never stronger (audit r2 fidelity B1; the
under-approximation claim was false for product atoms before). It also added the σ-parametric
constraint forms, the large-regime T5 witness and the `Grid` module.
-/
