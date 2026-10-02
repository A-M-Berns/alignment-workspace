# bli-transfer · attempt B · findings about the sources

*Attempt B (angle B, the splice-stream route) of the dual package `bli-transfer`, 2026-09-30, [scrubbed]. Lean: `Cleanroom/Bli/BliTransfer/AttemptB/`. Severity scale ([STANDARDS](../../../STANDARDS.md) §5): blocking the note's conclusion / local error / imprecision / presentation. Each entry says what was proved in Lean and what is analysis.*

## F-B1 — T3 is false: the clamped market is never a logical inductor (blocking for `bli-program` §3.2(d) and §4 L5; corrects the mandate's T3)

**Claim under test.** `IsLogicalInductor Q DP → IsLogicalInductor (clamp Q) DP` with `clamp Q k ψ = max (min (Q k ψ) (1 − ε_k)) ε_k`, `ε_k = 2^{-2^k}` (program §3.2(d); bli-paper-033/039, bli-slides-006/008, bli-soto-a-002 reading C; mandate T3, whose proof route needs "trade magnitude `≤ 2^{p(n)}`").

**Refuted in Lean** (`Clamp.lean`, `clamp_not_isLogicalInductor`): for **every** history `Q` and every deductive process with consistent worlds, `clamp Q` is exploited by the efficiently computable trader `sellBottom`, which on day `n` sells `2^{2^{n+1}}` shares of `⊥`. Its net worth is `∑_{i ≤ n} 2^{2^{i+1}} · P i ⊥`, which is `≥ 0` in every world (`⊥` pays `0`) and `≥ 2^{2^{n+1}} · ε_n = 2^{2^n}` on day `n` on any market with `P n ⊥ ≥ ε_n` — the clamp forces exactly this floor (`clamp_mem_Icc`). Non-vacuity: at FAF's LIA over `paperDP 𝗜𝚺₁`, the base is an inductor and the clamp is not (`WitnessLia.clamp_lia_not_isLogicalInductor`). The coefficient `2^{2^{n+1}}` is expressible at cost `O(n)` by `n+1` nested `letE`-squarings of `const 2` (`sqTower_denoteWith`); the trader is certified through FAF's machine combinators (`sellBottom_ec`: constant sentence family, price-free coefficient stream emitted by `MachineTokenStream.concatVar`).

**Why the mandate's route fails.** The rewrite leg (read the clamp exactly) is fine; the settlement residual `∑_n magnitude_n · ε_n` is not summable because e.c. magnitude is doubly exponential, not `2^{poly}` (F-B2). The attack is independent of the rate: an expressible floor `ε_n` of polynomial cost is `≥ 2^{-2^{p(n)}}` for some polynomial `p`, and a trader with `p+1` squarings beats it; so no clamp with an expressible rate rescues the variant (analysis; the Lean covers the definition of record `ε_k = 2^{-2^k}` and, more generally, any market with `P n ⊥ ≥ 2^{-2^n}`).

**Surviving neighbour.** T1 with exact constraint 1 (`overlay_isLogicalInductor_of_transfer`): an *expressible* re-pricing of *large* sentences that never touches `⊥` (small on every day) has no settlement residual at all. Non-dogmatism cannot be imposed by a floor on refutable sentences; the LI paper's non-dogmatism is about unrefutable ones.

## F-B2 — "trade magnitude `≤ 2^{p(n)}`" is false for FAF's traders (blocking for `bli-program` §4 L5's citation; mandate Known issue 7)

**Refuted in Lean** (`not_magnitude_le_two_pow_poly`): for every market `V` and every polynomial `p`, `sellBottom`'s day-`n` magnitude `2^{2^{n+1}}` exceeds `2^{p(n)}` for some `n` (`bli-found`'s `eventually_poly_le_two_pow`). The program cited the bound as available; the mandate asked for it as the lemma `magnitude_le_of_ec`. The true bound is doubly exponential in the day: `letE` sharing lets a feature of cost `c` with `b`-bit constants denote up to `2^{b·2^c}`; without sharing (trees) the bound would be `M^{cost}`, i.e. `2^{poly}`. This is a property of FAF's `def:ec` class, which admits `letE` (Criterion.lean's docstring: circuits are straight-line programs with sharing, "compactly specifiable in polynomial time"). Not proved here: the positive doubly-exponential bound.

## F-B3 — Program §3.1 hypothesis (iii) under-specifies the oracle (imprecision; mandate Known issue 5, confirmed)

The program says "`(k, ψ) ↦ expr k ψ` is in `FP`" without saying how `ψ` arrives. In FAF the rewriter sees a raw spelling — canonical run, Gödel escape `[1, c]`, structured escape `[1, 0, …]` — chosen by the exploiting machine. The honest hypothesis is the run-level oracle `SpliceOracle expr` (`Certificate.lean`): one `FP` word function whose specification quantifies over every block-complete word whose decode `parseRpn` accepts as `ψ`. `SpliceOracle.ofRaw` states the mandate's literal-spelling form; the interface of record uses the contraction form (`UnRpnContractsTo`), which admits any spelling of the body's own leaves. Confirmed by formalization: the T1.5 witness oracle is only correct on all spellings because FAF's `tableLookup` is keyed by parsing.

## F-B4 — Program §3.1's guard `¬ SmallOn k ψ` on the map (imprecision; mandate Known issue 6, confirmed)

Dropped in `ExprMap` (fire wherever the value is reproduced; leaves may read days `≤ k`); the guarded statement is the corollary `ExprMap.ofLargeOnly`. The guard would force the oracle to decide smallness from a raw spelling in polynomial time. (On Gödel codes the test is primitive recursive — `SmallCode.smallCode_primrec` — which is the computability T1.4 needs, not the polynomial-time recognition on raw spellings the guard would need.)

## F-B5 — bli-paper-031 footnote / bli-slides-002 (confirmed; mandate Known issue 1)

The stated condition ("the number of small sentences grows faster than any polynomial") is not the operative one; what T1 uses is *which* sentences are small (`SmallOn n φ := tokenSize φ ≤ 2^{2^n}`, `bli-found`) and, crucially, *expressibility* of the re-pricing: `ExprMap.silent` (Tier B) is a real constraint — an `ov` that sets un-fired large sentences to `1/2` is not an expression map, and a trader reading such a leaf is not rewritten. Not re-proved: the sharp refutation L3 (`bli-leak`).

## F-B6 — bli-slides-002's two readings (confirmed; mandate Known issue 2)

"Traders never read large prices" is T2's class `RestrictedEC`, a strict subclass of `def:ec` (`Witnesses.lean`: `largeReader` is e.c. and reads a day-`0`-large atom); T2 (`restrictedEC_not_exploits_overlay`) holds for it for *every* re-pricing in `[0,1]`, no expressibility needed — which shows the reading proves too little and too much: it is not the criterion. "Large = unread" is circular (`bli-found` F-5). T1 is the theorem under neither reading.

## F-B7 — bli-slides-030's "modify them however we like" (confirmed false as a transfer; mandate Known issue 3)

The surviving form is T1: modify the large prices by any efficiently expressible function of the day's (or earlier days') small prices, with Tier B elsewhere. Attribution of the corrected theorem is ATTRIBUTION-UNVETTED (it is this run's statement).

## F-B8 — Rate of the rounding (bli-paper-033/039, bli-slides-006/008, bli-soto-a-002(C); mandate Known issue 4) and the Route A attempt record (T4)

**Status.** The rounded form (Route A) is not settled here in either direction; the clamped form is refuted (F-B1). Attempt record:

- *Proof attempt.* The bounded-difference route needs a summable day-value gap; a day-`n` leaf reading `price φ 0` under a rounding of day `0` sees a fixed error `≤ 2^{-1}` multiplied by a coefficient of magnitude up to `2^{2^{poly(n)}}` (F-B2) — unbounded for every rate. The finite-perturbation trick (hard-code the first `K` days) only moves the problem to day `K`. Stall point: the coefficient's amplification of an early-day rounding error is not controlled by any rate.
- *Refutation attempt.* The `⊥`-seller refutes any rounding that maps a positive price of a refuted sentence **up** to a grid point `≥ 2^{-2^n}`: `sellBottom_exploits` applies verbatim to any market with `P n ⊥ ≥ 2^{-2^n}` for all `n`. So a rounding with a *ceiling* on refuted sentences is dead whenever `Q` prices them positively. A rounding that rounds *down* (floor to the grid, `0` stays `0`) escapes this attack; a refutation of it would need a rounding artefact with a persistent sign on a sentence the trader can settle, and the amplifier alone does not obviously profit (its position is on a sentence the rounded market also prices sensibly). Stall point: no candidate with a persistent sign under floor rounding.
- *Positive partials.* Rounding restricted to days `≥ K` with all day-`< K` leaves frozen is T1 plus FAF's finite-support freeze (not assembled here). Rounding that is itself expressible: none of the source's roundings is.

Severity for bli-paper-039 as printed: blocking (its argument is 031 + 033, 033's rate is undischarged, and the clamped reading of 033 is false); surviving neighbour: T1 with exact constraint 1.

## F-B9 — De Bruijn shifting (mandate Known issue 8; confirmed)

The administrative `letE (price ψ k) e` shifts free variables of `e` by one; `EF.Closed` on bodies (`ExprMap.closed`) discharges it through `Closed.denoteWith_env_irrelevant`. For T3's body `clampE k` (which reads `var 0` on purpose) the general leaf-semantics law `spliceOn_denoteWith_of_leaf` is the one that applies — the rewrite of record is stated for arbitrary `expr` with the leaf semantics as a hypothesis, and the `ExprMap` instance is a corollary. The design where the squarings computing `ε_k` are nested *inside* the bound value (`epsE`) keeps the clamp body's `var 0` at the price with no index bookkeeping.

## F-B10 — The plan's `paperLIA` exists (presentation; mandate T1.5)

The mandate reports the name `paperLIA` as absent at pin `159ec3f`. It exists: `LogicalInduction.paperLIA` at `Construction/Paper/TheoremDP.lean:442`, a `noncomputable abbrev` for `LIA_is_logical_inductor (paperDP T) (paperDP_computable T)` taking `[T.Δ₁]`; `WitnessLia.lean` uses it at `T := 𝗜𝚺₁`.

## F-B11 — FAF's freeze is the constant-body special case of the splice (positive; mandate § Context)

`OracleBridge.SpliceOracle.ofRunOracle`: any `FreezeStep.RunOracle selRun quoteRun` is a `SpliceOracle` for `constMap sel quote` (bodies `const (quote k ψ)`), and `SpliceOracle.ofTable entries` gives a machine-checked, all-spellings splice oracle for every finite constant-body map from FAF's `FreezeOracle.runOracleOf`. The mandate's remark that `liaHistory` is the overlay with `ov = 0` off support is thus witnessed at the oracle level.

## F-B12 — T1.5's non-vacuity is finite-support (presentation; mandate T1.5)

The machine-checked witness map fires on two cells (`witnessAtom` on days `0` and `1`), so the overlay is also a finite-support perturbation of `Q` (FAF's `lic_iff_of_finiteSupportPerturbation` already covers that class). A witness with infinitely many fired cells needs an oracle recognizing an infinite atom family from every spelling — a tag test on the payload plus a comparison of the run's digit count against `2^{2^k}` under early termination — not built (the mandate's sketch; analysis of its cost in the report). The non-degeneracy that *is* proved: the overlay differs from `Q` at a day-large sentence (`overlay_witness_ne`), and an e.c. presented trader is rewritten non-trivially.
