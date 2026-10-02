# bli-transfer — attempt A report (angle A: the machine-model flat pass)

*Written 2026-09-30 by the attempt-A formalizer (Claude Fable 5.1, [scrubbed]) of the dual package `bli-transfer`. Lean under `Cleanroom/Bli/BliTransfer/AttemptA/`, namespace `Cleanroom.Bli.BliTransfer.AttemptA`, root module `Cleanroom/Bli/BliTransfer/AttemptA.lean` (per `formalize`'s dual-attempt layout; the mandate's `BliTransfer/` root is the reconciler's). Binding: `00-common`, [STANDARDS](../../../STANDARDS.md), `bli-transfer-mandate`. Companion files: [bli-transfer-a-ledger](bli-transfer-a-ledger.md), [bli-transfer-a-findings](bli-transfer-a-findings.md), `bli-transfer-a-open.txt` (empty).*

## State of the package

**T1 (L1, core) is proved at the criterion's own quantifier, with no OPEN.** `Computable.overlay_isLogicalInductor'`: for every logical inductor `Q` over `DP`, every re-pricing `ov` with an expression map `E : ExprMap Q ov`, a `SpliceCertificate E.expr` (a polynomial-time run-level oracle whose specification is quantified over every spelling `parseRpn` accepts) and a computable table for `ov`, the overlay `overlay Q ov` is a logical inductor over `DP`. Its `noExploit` is for **every** `EfficientlyComputable` trader: the splice of an e.c. trader is e.c. (`Certificate.EfficientlyComputable.spliceOn`, kind C, no trader class), and exploits `Q` by the same amounts from the bridge day on (`Transfer.Trader.spliceOn_exploits`). The two legs are kept apart (`Transfer.overlay_isLogicalInductor_of_spliceEC` names the efficiency transport as a hypothesis; `Headline.overlay_isLogicalInductor` composes it with the certificate; `Computable.overlay_isLogicalInductor'` discharges the overlay's computability).

**T2 (L4, core) proved as a disclosed `(c)`**: `Restricted.restrictedEC_not_exploits_overlay`, with the N+ class witness and the separating e.c. trader (`Witnesses.lean`).

**T1.4 proved** (`Computable.overlay_computableMarket`): the smallness test on Gödel codes is primitive recursive by course-of-values recursion on Foundation's decoder.

**T1.5 proved as N+ over the real construction** (`WitnessOracle.lean`, `WitnessLia.lean`): `witness_isLogicalInductor DP hDP : IsLogicalInductor (overlay (liaHistory DP) (wOv DP)) DP` for every computable process, instantiated at `paperDP 𝗜𝚺₁` (whose stages have consistent worlds, `paperDP_hworld`); the overlay provably changes a price (`overlay_ne_lia`) and rewrites an e.c. trader non-trivially (`familyReader_splice_ne`); the certificate's oracle handles every spelling.

**T3 (stretch) partial** (`Clamp.lean`): the accounting through the rewrite is proved (`clampSpec`, `Strategy.clamp_value_sub_le`, `Trader.clamp_netWorth_sub_le`) and the headline `clamp_isLogicalInductor_of` is conditional on three named hypotheses not discharged here — the day-aware clamp certificate, the mandate's `magnitude_le_of_ec` (through bounded partial sums of `magnitude · ε`), and the clamped table's computability. Stall points in [bli-transfer-a-findings](bli-transfer-a-findings.md) § T3. **T4** ends as an attempt record in the findings (both directions, stall points), never an OPEN row. **T5** not attempted (said so in the findings).

**Gate**: `scripts/wp-audit` PASS on all fourteen modules after the last edit (axioms `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`; no OPEN entry). Kernel replay is consolidation's.

**Contamination**: none — nothing under `research/faf-lab/` or any transcript was read.

## Layout conflict, flagged

`formalize` § Dual attempts puts attempt A in `Cleanroom/Bli/BliTransfer/AttemptA/` with deliverables under `packages/bli-transfer/attempt-a/`; the mandate's header puts angle A in `Cleanroom/Bli/BliTransfer/` with prose at `packages/bli-transfer/bli-transfer-*.md`. I followed `formalize` (the more specific dual-attempt rule, and collision-free whichever convention attempt B follows). Consequence: `scripts/wp-audit`'s open-list glob `run/wp/*/*-open.txt` does not reach `attempt-a/bli-transfer-a-open.txt`; the package has no OPEN entry, so nothing is lost, but a reconciler adding one must place it at the package level.

## Definitions of record (`Defs.lean`)

All as the mandate specifies, with these decisions:

- `overlay Q ov k ψ = if SmallOn k ψ then Q k ψ else (ov k ψ : ℝ)`; `overlay_small`, `overlay_large` are `simp`.
- `EF.freeBound`, `EF.Closed`, and the environment half of the program's `denote_eq_of_agree_on_leaves` as `EF.denoteWith_congr_env` (agreement below `freeBound` suffices) with the corollaries `EF.Closed.denoteWith_env_irrelevant`, `EF.Closed.denoteWith_eq_denote`.
- `ExprMap Q ov` with fields `expr`, `closed`, `leaves` (`p.1 ≤ k ∧ SmallOn p.1 p.2`), `fires`, `silent`, and **`ov_range` as a field** (not derivable: a body's denotation is unconstrained and `expr` may be `none` on a small sentence). The program's guarded form is the corollary `ExprMap.ofLargeOnly`. `ExprMap.rank_le` derives the rank discipline from `leaves`.
- `RestrictedEC`, `epsK k = (1/2)^(2^k)`, `epsE k` (`k` nested `letE`-squarings), `clampE k` (one outer `letE` binding `ε_k`, so the price is `var 1` inside; `clampE_freeBound = 1`), `clampE_denoteWith`, `clampE_cost_le : cost ≤ 4k + 18`, `clamp Q` on every sentence, `E1c`, `clamp_mem_Icc`, `abs_clamp_sub_le`.

## T1.1 — the splice (`Splice.lean`)

`EF.spliceOn expr` keeps the dead leaf under the administrative `letE` exactly as FAF's `freezeOn` (Known issue 8). The laws are stated once over a **`SpliceSpec expr Q P`** (bodies with at most `var 0` free; a body with the base price bound denotes the target price; un-fired leaves agree), so that the overlay (`ExprMap.spliceSpec`, closed bodies, target `overlay Q ov`) and the clamp (`clampE k` reads the bound price as `var 0`, target `clamp Q`) share one rewrite, one denotation law and one strategy/trader lift:

| declaration | kind | note |
|---|---|---|
| `EF.rank_le_spliceOn` / `EF.spliceOn_rank_le` / `EF.spliceOn_rank` | L | rank preserved exactly under the rank discipline (`hrank : expr k ψ = some e → e.rank ≤ k`) |
| `EF.spliceOn_cost_le` | L | `cost ≤ (B + 2) · cost` for bodies of cost `≤ B` |
| `EF.spliceOn_denoteWith` | L | exact transport, every environment; the leaf half of `denote_eq_of_agree_on_leaves` |
| `Strategy.spliceOn`, `Trader.spliceOn` | D | coefficient-wise, day-wise; `Strategy.ext` is the tool downstream |
| `Strategy.spliceOn_value` | L | exact on a day whose traded sentences settle at the same price on both markets |

## T1.2 — the accounting (`Transfer.lean`)

- `exists_settle_day` (C, hyps (a)): from `Cleanroom.Bli.BliFound.bridge_lemma`, the day `N` from which every traded sentence is day-small.
- `Trader.netWorth_difference_le_of_tail_eq` (C, (a)): the generic finite-prefix accounting — two traders on two `[0,1]`-markets whose day values agree from `N` on have net worths within `∑_{d<N}(magnitude + magnitude)`; mirror of FAF's `freezeOn_netWorth_difference_le` with `D = range N`. Reused by T2 (and by T3 if reached).
- `Trader.spliceOn_netWorth_difference_le` (C): the splice instance, constant `spliceErrorBound E Tr N`.
- `Trader.spliceOn_exploits` (C): exploitation transports from `(Tr, overlay)` to `(Tr.spliceOn, Q)` by `Exploits.of_boundedDifference` (world quantifier `v.ConsistentWith (DP.D n)`, trap (v)).
- `noExploit_overlay_of_spliceEC`, `overlay_isLogicalInductor_of_spliceEC` (C): the two-hypothesis forms; `hec` and `hcomp` are named hypotheses, never fields of a structure (trap (ii)).

## T1.3 — the certificate (`TokenModel.lean`, `Contraction.lean`, `Certificate.lean`)

The chain, each link its own lemma with the FAF twin named in its docstring:

1. **Token model** (`TokenModel.lean`): `spliceTokenRunOn expr` on the contracted stream, control `EF.freezeTokenNext` and `EF.FreezeTokenState.Matches` reused verbatim, body looked up at the code level (`exprCode expr day code`, decode-then-serialize; no oracle here). `strategyOfTokens_spliceTokenRunOn_trades` (C, (a)): on every stream, well-formed or garbage, decoding the output gives the `spliceOn`-rewritten trades. The one-token commutation `streamReadFrom_spliceTokenEmitOn` re-runs FAF's dispatch with the body case through `EF.streamReadFrom_serialize_self`. Rank validation commutes by `EF.spliceOn_rank`.
2. **Contraction** (`Contraction.lean`): `EF.rawSerialize` (leaves as canonical runs `0 :: rpn ψ ++ [k]`, never Gödel codes), `unRpn_rawSerialize_append`; the flat emitter `spliceEmitOn exprRun buf D = D :: raw ++ [8]` / `[D]`; `RunAgrees expr exprRun` — **the run-level agreement quantified over every spelling `parseRpn` accepts** (Known issue 5); `unRpn_rpnSpliceRunOn` (C) from FAF's emitter-generic `unRpn_rpnConditionRun_of` with `Z fc d = spliceBodyOn expr fc d`; `SpliceStreamRewriter` (mirror of `FreezeStreamRewriter`); `EfficientlyComputable.spliceOn_of_rewriter` (mirror of `EfficientlyComputable.freezeOn`); `spliceStreamRewriter_of_flatPass`.
3. **The pass** (`Certificate.lean`): `SpliceOracle exprRun` = FAF's `RunOracle` with `R_length_le` **polynomial** (`R_poly.eval v.length`), input `pair zW (pair tokW bufW)` (the raw input word is passed through for a day-aware instance; unused by T1), `R_spec` on every well-formed day block and every buffered run. The block emitter `spliceEmitR` guards the oracle call by `|guardWord W| = 9|W| + 8` and emits nothing when the guard fails — this is what lets `runFold_mem_FP`'s **universal** budget `qQ.eval |W| + k(|cli| + |tok|)` close with a body polynomial in the state (`spliceEmitW_length_le`, `emitPoly O = R_poly ∘ (9X + 8) + 3`, `k = 1`). The parameter block is `pair (F x) x` (`FPFold.mem_FP_withInput`'s shape). On every reachable state the guard holds: `decodeBits_runFold_splice` carries the invariant `|csBuf cli| + ∑(3|r| + 3) ≤ |W| + 3`, seeded by `blockSplit_measure` (`∑(|r|+1) + |partial| = |ds|`). `splicePass_mem_FP` (C) is `runFold_mem_FP` with `condStepR` and the new emitter; `decodeBits_splicePass` (C) computes `rpnConditionRun (spliceEmitOn exprRun)` itself, with no clamp. `SpliceCertificate expr` = a lookup, its `RunAgrees`, an oracle; nothing quantified over traders. `EfficientlyComputable.spliceOn` (C): the splice of every e.c. trader is e.c.

Measured: `import LogicalInduction.Construction.Freeze.Step` alone, 6.8 s wall (one run, warm cache, [scrubbed], 2026-09-30); `import LogicalInduction.Construction.LIACompiler` alone, 6.3 s wall (one run, warm).

**Which spellings the certificate covers**: all — the generic theorem takes `RunAgrees` over every run `parseRpn` reads as a sentence with nothing left over (canonical run, Gödel escape `[1, c]`, structured escape `[1, 0, …]`). An instance proving `RunAgrees` only on canonical runs would be a `(c)`; the generic theorem does not admit it.

## T1.4 — computability (`Computable.lean`)

`tsCode` (the decoded sentence's `tokenSize + 1`, `0` on invalid codes) is primitive recursive by `Primrec.of_courseOfValues` (FAF's packaging of `Primrec.nat_strong_rec`), mirroring FAF's `sentencePrimcodable`; `dl4` (base-4 digit length) likewise; `smallCode n c` is `Primrec₂`; `ComputableTable ov` is the second conjunct of `ComputableMarket` with `Computable` in place of the code; `overlay_computableMarket` (C) combines `Q`'s certificate, `ov`'s table and the test through `Computable.cond` and `ComputableMarket.ofComputableTable`. No polynomial-time content is claimed. `overlay_isLogicalInductor'` is the headline of record.

**Hypothesis provenance of the headline** (`overlay_isLogicalInductor'`): `[IsLogicalInductor Q DP]` (a); `E : ExprMap Q ov` — the instance's definition, its fields are the program's (i)–(ii) as restated (D); `C : SpliceCertificate E.expr` — the instance's obligation, one `FP` oracle with its spec (a for the theorem; the instance must prove it); `hov : ComputableTable ov` — the instance's re-pricing table is computable (a for the theorem; disclosed as an obligation the mandate allowed either as a derived fact or as a field). No `(b)`, no `(c)` in the headline.

## T2 — restricted class (`Restricted.lean`, `Witnesses.lean`)

- `restrictedEC_not_exploits_overlay` (C; `(c)`: quantified over `RestrictedEC`, not the criterion) for every `[0,1]`-valued `ov`, no expression map. Route: identity rewrite (`Strategy.value_congr_of_small`), bridge day, generic accounting. No `IsLogicalInductor` conclusion is stated.
- N+ `restrictedWitness` (day-`n ≥ 1` trade `(price ⌜aₙ⌝ n, ⌜aₙ⌝)`, none on day `0` — the only day-`0` small sentence is `⊥`), e.c. via `EfficientlyComputable.ofTradeBlocksBig` at the atom family and `MachineSpliceStream.serialize_price`; in the class by `smallOn_atom_self`.
- Separation `restrictedEC_separation`: `largeReader` (every day, `price ⌜a_{4^{sizeBound 0}}⌝ 0` on `⊥`) is e.c. and not `RestrictedEC` (`largeOn_witness 0`).

## T1.5 — non-vacuity (`WitnessOracle.lean`, `WitnessLia.lean`)

**The witness map.** `wExpr k ψ = some (const (1/2))` exactly when `k = 0` and `ψ` is an atom of the run's family `7` (`freshAtom 7 payload = atom (Nat.pair (cleanroomBaseTag + 7) payload)`, tag `wTag = 16`; the registry row is added to `Cleanroom.Bli.BliFound.Tags`); `none` otherwise. `wOv DP` is `1/2` where the map fires and the LIA's exact quote `liaQuote DP` elsewhere (Tier B). **Every atom is large on day `0`** (`three_le_tokenSize_atom`, `sizeBound 0 = 2`), so `fires` needs no size comparison. Disclosed scope: the map fires on day `0` only; a map firing on large family atoms of every day `k` would need, in its oracle, a comparison of the run's length with `2^{2^k}` (a capped double-exponential in unary) on top of the family test — the shape `bli-assemble`'s oracle extends.

**The oracle** (`wOracle : SpliceOracle wExprRun`): a block fold over the buffered run's bits (`wStepOf`; count capped at `3` in unary, whether the first block is the numeral `1`, the last block's bits; `runFold_cli_mem_FP` with a `+20` state bound), then the value tests through FAF's `DigitFP` — `subW`/`unpairFstW` for the canonical run `[t]` (`5 ≤ t ∧ (t − 5).unpair.1 = wTag`), `predW`/`unpairFstW`/`unpairSndW` for the Gödel escape `[1, c]` (`c − 1 = Nat.pair 1 a`, `a.unpair.1 = wTag`), `leW` comparisons against the numerals, and `NumEqBits 0` for the day. `R_spec` holds on **every** buffered word (its complete blocks are exactly the tokens `decodeBits` yields, `undigitize_eq_blockSplit`), so the universal `SpliceOracle` interface is met without weakening it (findings F-A2 stands as a remark only). Output bound: a constant (`R_poly = C |wOut|`).

**Run-level agreement on every spelling** (`wRunAgrees : RunAgrees wExpr wExprRun`), by cases on `parseRpn_cons`: `[0]` (`⊥`); `[1, 0, …]` structured — denotes a tag-`5` atom (`parseStructuredPaperPrime_atom`, from the parser's definition), never the family; `[1, c]` Gödel — `wExpr_decode` reads the map off the code's tag without any tightness of Foundation's decoder (`⊥` has infinitely many codes, as FAF notes); `[2/3/4, …]` connectives; `[t ≥ 5]` canonical atom.

**Instance obligations discharged**: `wCertificate`, `wOv_computableTable` (the family test on codes is `Primrec₂`; `Computable.cond` with the LIA's own table from `ComputableMarket.exists_computableTable`).

**Non-degeneracy, proved**: `overlay_ne_lia DP` — the day-`0` LIA state is a finite `entries` table quoting `0` off its `support` (`RationalBeliefState.quote_eq_zero_of_not_mem`); the family atom with payload `sup (encode) + 1` is off it (`Nat.right_le_pair`), so `Q` prices it `0` and the overlay `1/2`. Trader side: `familyReader` (every day `price ⌜a⌝ 0` for the family atom `a = Nat.pair wTag 0`, on `⊥`) is e.c. (`ofTradeBlocksBig`) and its splice differs on every day (`familyReader_splice_ne`).

**Headline**: `witness_isLogicalInductor (DP) (hDP)` from `LIA_is_logical_inductor` and `overlay_isLogicalInductor'`; `witness_isLogicalInductor_paperDP` at `paperDP 𝗜𝚺₁` with `witness_process_hworld` (trap (v)). Grade **N+**: the real inductor, a price change proved, the trader side exercised, all spellings. Measured: `import LogicalInduction.Construction.LIACompiler` alone, 6.3 s wall (one run, warm cache); `WitnessLia.lean` elaborates in well under a minute in a slot.

## T3 — the clamp (`Clamp.lean`, partial)

- `clampExpr k _ = some (clampE k)`, `clampExpr_rank` (no leaves), **`clampSpec Q : SpliceSpec clampExpr Q (clamp Q)`** (L): the clamp body reads the bound price as `var 0` (`clampE_freeBound = 1`, `clampE_denoteWith`) — the reason `Splice.SpliceSpec` was stated with one free variable rather than closedness.
- `Strategy.clamp_value_sub_le` (C, (a)): `|(T.spliceOn clampExpr).value Q w − T.value (clamp Q) w| ≤ T.magnitude (clamp Q) · ε_n` — the rewrite reads the clamp exactly; only the settlement term remains (`abs_clamp_sub_le`). Not a Lipschitz argument (mandate T3's trap).
- `Trader.clamp_netWorth_sub_le` (C, (a)): net worths within `∑_{i ≤ n} magnitude_i · ε_i`.
- `clamp_isLogicalInductor_of` (C, **partial**): `IsLogicalInductor (clamp Q) DP` given `hec` (the clamp's efficiency transport), `hbound` (bounded partial sums for every e.c. trader) and `hcomp`. What each needs, and where the attempt stopped, is in the findings § T3: `magnitude_le_of_ec` stalled at the bound on a decoded rational constant by its token under the `Encodable ℚ` instance the decoder uses; the clamp certificate needs the day clamp `min k n` and a token-model congruence on rank-valid streams; the table's computability needs FAF's rational `Primrec` kit (`Construction/Primcodable.lean`), not imported. Also shipped in `Defs.lean`: `E1c`, `clamp_mem_Icc` (non-dogmatism everywhere), `abs_clamp_sub_le`. Ledger Status: `partial: clamp certificate, magnitude bound and table computability named, not discharged`.

## T4 — Route A attempt record

Recorded in [bli-transfer-a-findings](bli-transfer-a-findings.md) § T4: the proof attempt stalls because a rounding is not expressible (no `SpliceSpec`; `EF.denote` is continuous) and the day-`n` read of a day-`0` price by a `2^{n²}`-magnitude e.c. coefficient defeats any per-trader constant; the refutation attempt stalls because the artefact (`2^{-2^k}`) is too small for an e.c. trader to amplify with a persistent sign. No theorem, no OPEN row (plan §0.3).

## T5 — iterated overlays

Not attempted; no definition stated. The findings sketch the shape (depth-`d` substitution inside bodies, a composed certificate through `mem_FP_comp` with `emitPoly` compounding for fixed `d`).

## What the reconciler should know

- The certificate interface (`SpliceOracle`, `SpliceCertificate`, `RunAgrees`) is the package's contract with `bli-assemble`; its universal `R_spec` (every buffered word) was met by the witness oracle without weakening, and `WitnessOracle.lean` is the template (family test under both atom spellings; add the day-`k` size comparison for state atoms).
- `Splice.SpliceSpec` generalizes the mandate's closed-body law to bodies reading `var 0`; the `ExprMap` instance is `ExprMap.spliceSpec`. If attempt B kept the closed-body form, the reconciler can keep either; `ExprMap`'s fields are the mandate's verbatim plus `ov_range`.
- `Transfer.Trader.netWorth_difference_le_of_tail_eq` is the one accounting lemma; T1, T2 and T3 are its instances.
- The parameter block `pair (F x) x` in `Certificate.splicePass_mem_FP` is what a day-aware (T3) oracle would read the day from; T1's oracle ignores it.
