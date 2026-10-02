# bli-leak — ledger

*One row per headline ([STANDARDS](../../STANDARDS.md) §6). Namespace prefix `Cleanroom.Bli.BliLeak.` omitted. "Hyps (b)/(c)" lists only non-(a) hypotheses; "—" means every hypothesis is (a) or there is none; "(OPEN T7)" means the row rests on `li-pseudorandom` T7 through this package's open list (`bli-leak-open.txt`). Witness column: the N+ instance that inhabits the row's hypothesis package. Status vocabulary as [STANDARDS](../../STANDARDS.md) §6; every row using the process of record's inductor certificate reads `partial: over OPEN computability (li-pseudorandom T7)`, as `li-pseudorandom`'s report requires. Refutation rows carry plan §0.4 rule 3's three items (the source's sentence, the reading formalized, the surviving neighbour) in the "Claim" column. Written by the formalizer (Claude Fable 5.1, [scrubbed], 2026-09-30). The gate line is the last `scripts/wp-audit` result recorded in [bli-leak-report](bli-leak-report.md).*

## Definitions of record (`Leak.lean`, `Instance.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `leakFamily`, `memberFamily` | mandate § Definitions; K7 | fresh-atom families `8` (leak atoms) and `9` (placement); the mandate's `7`/`8` shifted because `7` is now `bli-transfer`'s | D | variant: family numbers | — | — | defined (registry request in the report) |
| `member`, `memberAtom` | mandate § Definitions | the placement `freshAtomCode 9 ⟨n, 0⟩` and its atoms `atomFamily member` | D | exact | — | `member_injective`, `machineSentenceCodes_memberAtom` | defined |
| `leakAtom K n` | mandate § Definitions | `freshAtom 8 ⟨n, K⟩`, `K` a size pad | D | exact | — | `leakAtom_injective`, `machineSentenceCodes_leakAtom` | defined |
| `leakCoef`, `leakTrader` | mandate § Definitions; `bli-program` §3.2(b) | `2 · price (ℓ n) (e n) − 1`; the single position `(leakCoef n, χ n)` on days `e n ≤ n`, empty otherwise | D | variant: empty trade list on days `n < e n` (the rank certificate demands `e n ≤ n`; the mandate offered a hypothesis or a clamp) | — | — | defined |
| `leakHistory Q ℓ e t` | mandate § Definitions | `Q` with `(e n, ℓ n) ↦ t n` for every `n`; a `Classical` definition as FAF's `adviceRow` | D | exact | — | — | defined |
| `pendingBound g C` | mandate § Definitions | at most `C` members undecided at any time | D | exact | — | `pendingBound_succ` | defined |
| `leakStream`, `leakDP`, `leakQ`, `leakMarket`, `leakTraderRecord`, `recordDelay`, `recordPad` | mandate L3.5 | the instance of record over `paperDP T`: `unionStar` at `member`, delay `n + 1`, `1/2`; the union process; the LIA over it; the leak market at pad `4 ^ sizeBound N₀`, edit day `N₀` | D | exact | — | `leakStream_not_eventuallyConst` | defined |

## L3.0 — the sources' transfer is false (`Transport.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `posthoc_transfer_refuted` (closed at `𝗜𝚺₁`; `_ofTheory` over any consistent `Δ₁` `T ⊇ 𝗜𝚺₁`) | bli-slides-030, bli-slides-005, `main.tex:427/444`; `bli-program` §3.2(b), §3.11(j) | **Refuted.** (i) Source: "since traders don't touch large sentences, we can modify them however we like without messing up any rationality properties of the market" (bli-slides-030, [Understanding Trust talk 2024-10.pdf](../../sources/references/bli/slides/Understanding%20Trust%20talk%202024-10.pdf) p25); "`ℙ` is now a logical inductor, since it agrees with `ℚ` on small prices" (`main.tex:444`); "constraints 1–3 are easy enough (we can modify large sentences however we like)" (bli-slides-005, p10). (ii) Reading formalized (ATTRIBUTION-UNVETTED, findings K8): the *transfer* — `∀ Q P DP, IsLogicalInductor Q DP → ComputableMarket P → E1x Q P → IsLogicalInductor P DP` — is false. (iii) Surviving neighbours: FAF's `lic_iff_of_finiteSupportPerturbation` (finite support), `bli-transfer` L1 (expressible overlays) and L4 (`RestrictedEC`), and `exploits_leakHistory_iff` below | C | exact | — | the transport itself at `paperDP 𝗜𝚺₁` (FAF's day-varying `cxDiagonal`); `cxPerturbed_ne_liaHistory` (the edit is real) | refuted |
| `cxPerturbed_E1x` | mandate L3.0 | FAF's PE1 witness `E1x`-agrees with `liaHistory (paperDP T)` (day `0`: `smallSet 0 = {⊥}`, the advice row leaves `⊥` alone; days `≥ 1`: equal) | C | exact | — | as above | proved |
| `cxPerturbed_not_logicalInductor` | mandate L3.0 | the PE1 witness is no inductor: FAF's `adviceTrader` exploits it (`cxPerturbed_exploited`, FAF's `exploits` with the witness named) | C | exact | — | as above | proved |
| `smallOn_zero_iff`, `smallSet_zero` | mandate L3.0 | on day `0` only `⊥` is small | L | exact | — | — | proved |

## L3.1 — the leak market agrees on day-small sentences (`Leak.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `leakHistory_E1x` | mandate L3.1; bli-slides-030 | if each leak atom is large on its edit day, `E1x Q (leakHistory Q ℓ e t)` | P | exact | — | `leakMarket_E1x` (the instance, pad `4 ^ sizeBound N₀`, `leakAtom_large_pow`) | proved |
| `leakHistory_eq_of_ne`, `leakHistory_agree_before` | mandate L3.1, L3.4 | exact agreement off the leak atoms; exact agreement on days before the first edit day | L | stronger than `E1x` | — | — | proved |
| `leakAtom_large_of_pad`, `leakAtom_large_pow`, `leakAtom_small` | mandate L3.1 | a padded leak atom is large on the padded day (and every earlier one); every leak atom is eventually small on its own day (`Rate.lean`, via `machineSentenceCodes_eventually_small`) | L | exact | — | — | proved |

## L3.2 — the leak-reading trader is efficiently computable (`Trader.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `leakTrader_ec` (+ `_of_le`, `_const`, `leakTrader_record_ec`) | mandate L3.2; K1 | for machine-metered `ℓ`, `χ`, machine-written `e`, and a ruler count `if e n ≤ n then 1 else 0`: `EfficientlyComputable (leakTrader ℓ e χ)`, by `ofTradeBlocksBig` over `serialize_price` (the route of FAF's `adviceTrader_efficient`); the count discharged for `∀ n, e n ≤ n` and for `e = const N₀` | C | exact | — | `leakTrader_record_ec K N₀` (the trader of record) | proved |
| `machineSentenceCodes_atom_of_machineDigits` | mandate L3.2 (FAF API request) | an atom family over a machine-written index is machine-metered | L | exact | — | `machineSentenceCodes_memberAtom`, `machineSentenceCodes_leakAtom` | proved |

## L3.3 — post-hoc editing refuted, the abstract leak theorem (`Exploit.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `leakTrader_exploits` | mandate L3.3; `bli-program` §3.2(b), §4 L3 | over any inductor `Q` (`hworld`), a machine-metered family decided with delay `g` (stage form `hdec`), at most `C` pending, pseudorandom at `1/2` relative to `Q`, an injective leak family disjoint from the traded one, and `e n ≤ n` eventually: the leak trader exploits `leakHistory Q ℓ e (truthR x)`. Scope: pseudorandom relative to the base inductor, whose price the trade pays; decided after reading; at most `C` pending | P | exact (the mandate's `hlarge` is not a hypothesis of exploitation) | — | `leak_instance_exploits` (L3.5; every hypothesis but the inductor certificate discharged at grade (a)) | proved |
| `leakHistory_not_logicalInductor` | mandate L3.4 (unconditional corollary) | the leak market is no inductor once the trader's certificate is in hand; no computability of the market needed | C | exact | — | `leak_instance_not_logicalInductor` | proved |
| `posthoc_transfer_refuted_late_of` | mandate L3.4 (abstract form) | for a leak package with all edits on day `N₀`, leak atoms large on day `N₀`, and a computable leak market: a computable market agreeing with an inductor exactly on days `< N₀` and on every day-small sentence need not be an inductor | C | exact | `hcomp : ComputableMarket (leakHistory …)` — (a) as a hypothesis; at the instance it is (OPEN T7) | `posthoc_transfer_refuted_late` (closed form, OPEN T7) | proved (abstract); the closed form is `partial: over OPEN computability (li-pseudorandom T7)` |
| `netWorth_ge_of_rounds`, `round_ge_quarter`, `card_early_or_pending_le` | mandate L3.3 (proof) | the accounting: `δ · #good − #bad ≤ net worth`; the `1/4` margin; at most `N + C` bad rounds | L | exact | — | — | proved |

## L3.4 — the finite-prefix retreat (`Closed.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `posthoc_transfer_refuted_late` | mandate L3.4; bli-slides-030 (the retreat "edit only late days") | **Refuted (over OPEN T7).** (i) Source as L3.0; the retreat: "day `0` is degenerate; freeze the first `N₀` days and edit only large sentences of days `≥ N₀`". (ii) Reading: `∀ Q P DP, IsLogicalInductor Q DP → ComputableMarket P → (∀ n < N₀, ∀ φ, P n φ = Q n φ) → E1x Q P → IsLogicalInductor P DP` is false for every `N₀`. (iii) Survivors as L3.0. Scope: exploitation (a); the counterexample market's computability and the instance's inductor certificate rest on `li-pseudorandom` T7 | C | exact | (OPEN T7) `leakQ_isLogicalInductor`, `leakMarket_computableMarket` | the instance of record; `leakStream_not_eventuallyConst`, `leakCoordinates_infinite` | partial: over OPEN computability (li-pseudorandom T7) |

## L3.5 — the instance over `paperDP T` (`Instance.lean`, `Closed.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `leak_instance_exploits` | mandate L3.5 | with the base's inductor certificate as a hypothesis, the trader of record exploits the leak market of record over the process of record; `hworld`, `hdec`, `MachineSentenceCodes`, `pendingBound`, pseudorandomness, disjointness all discharged at (a) | C | exact | (OPEN T7) the instance `IsLogicalInductor (leakQ T) (leakDP T)` as a hypothesis | `leakStream_not_eventuallyConst`, `member_injective`, `leakCoordinates_infinite`, `leakMarket_ne_leakQ` | proved (instance as hypothesis) |
| `leak_instance_exploits_closed`, `leak_instance_not_logicalInductor_closed` | mandate L3.5 | the closed forms | C | exact | (OPEN T7) `leakQ_isLogicalInductor` | as above | partial: over OPEN computability (li-pseudorandom T7) |
| `union_atomDP_member_hworld`, `literalProcess_memberSchedule` | mandate L3.5 (`hworld` for the union — the dependent's obligation) | `atomDP member x g` is `bli-found`'s literal process of the member schedule; a cleanroom-free consistent base stays consistent with it adjoined | C | exact | — | `leakDP_hworld` (at `paperDP T`) | proved |
| `leakStream_computable`, `leakDP_computable` | mandate L3.5/L3.6 (T7) | the stream and the process of record are computable | OPEN | exact | — | — | open (li-pseudorandom T7) |
| `leakQ_isLogicalInductor` | mandate L3.5 | the LIA over the process of record is an inductor | OPEN | exact | (OPEN T7) `leakDP_computable` | — | open (li-pseudorandom T7) |

## L3.6 — the leak market is a computable market (`Computable.lean`, `Closed.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `leakHistory_computableMarket` | mandate L3.6 | for a computable market `Q`, a computable edit-day function `e` and a computable stream `x`, `leakHistory Q (leakAtom K) e (truthR x)` is a computable market: FAF's `ofComputableTable` on the table `leakQuote` (the leak-atom recogniser read off Foundation's `Formula.toNat`; exactness `leakHistory_eq_leakQuote`; computability `leakQuote_computable` by `Computable.cond` over primitive recursive pieces) | C | exact | — | `leakMarket_computableMarket` (the instance; its `hx` is OPEN T7) | proved |
| `leakMarket_computableMarket` | mandate L3.6 | the leak market of record is a computable market | C | exact | (OPEN T7) `leakStream_computable`, `leakQ_isLogicalInductor` (the base's table) | — | partial: over OPEN computability (li-pseudorandom T7) |

## L3.7 — the surviving neighbour (`Neighbour.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `exploits_leakHistory_iff` (with `netWorth_leakHistory_eq`) | mandate L3.7 | a trader none of whose strategies mentions a leak atom has the same net worth on both markets in every world, hence exploits one iff the other | C | exact | — | — (a universally quantified equality; the criterion-level survivors are `bli-transfer`'s L1/L4, cited) | proved |
| `denoteWith_congr_of_priceQueries` | mandate L3.7 (FAF API request) | `EF.denoteWith` congruence on histories agreeing at the queried cells | L | exact | — | — | proved |

## L8 — counterlogical conditioning is not an object (`Counterlogical.lean`, `Witnesses.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `adjoinSentence_stage_unsatisfiable` (+ `not_holds_of_neg_mem_stage`) | mandate L8.1; bli-soto-b-2-022 | if `∼ψ ∈ DP.D N`, no world is consistent with stage `N` of `DP.adjoinSentence ψ` | L | exact | — | `dayVaryingRefuted_mem` | proved |
| `counterlogical_criterion_vacuous` (+ `_of_consistent`) | mandate L8.2; bli-soto-b-2-022 (ii); `bli-program` §4 L8 | over a computable process refuting `ψ` at a stage (it is itself consistent at), **every** computable market is an inductor over `DP.adjoinSentence ψ`. Scope: vacuous criterion, every computable market; the base process is consistent at the refuting stage | C | exact | — | `counterlogical_two_inductors_dayVarying` (N+: `paperDP 𝗜𝚺₁` + day-varying schedule, `ψ = freshAtom 3 ⟨1,1⟩` refuted at stage `2`, base consistent there; the constant markets `0` and `1`, disagreeing everywhere, both inductors) | proved |
| `conditionedHistory_junk` | mandate L8.3 (i); K9 | at a condition priced `0`, FAF's conditional quote is the **junk value `1`, not `0`**, for every `φ` | L | exact | — | — | proved |
| `counterlogical_price_tendsto_zero`, `counterlogical_conj_tendsto_zero` | mandate L8.3 (ii) | under an inductor over `DP` refuting `ψ`: `P n ψ → 0` and `P n (φ ⋏ ψ) ≈ₙ 0` for every `φ` — the quote is a ratio of two vanishing sequences, capped at `1` (`conditionedHistory_eq_div_or_one`) | C | exact | — | — | proved |
| `omegaQuote`, `lastUndecidedDay`, `decisionDay` | mandate L8.4 (stretch); bli-soto-b-030 | Ω's "latest state not having decided `C`" and its capped quote as definitions; `undecided_at_lastUndecidedDay`; non-junk iff `P m (B ⋏ C) < P m C` (`omegaQuote_eq`) | D | variant: stage-membership reading of "decided"; junk at a stage-`0` decision | — | — | defined (no "reasonable" theorem: bli-soto-b-030 is ill-posed there, findings) |

## E1 — the rate (`Rate.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `no_early_read` | mandate E1 (statement corrected) | an e.c. trader mentions on day `n` only sentences of size `≤ 2 ^ (A (n+1)^E)` | C | weaker: `2 ^ (A (n+1)^E)`, not the mandate's `A (n+1)^E` (findings F-1) | — | — | proved |
| `no_early_read_large` (+ `leakAtom_unreadable_before`) | mandate E1; `bli-program-construction` X8 (refuted) | a sentence large on day `k` is mentioned on day `n` only if `2 ^ k < A (n+1)^E`: singly exponential in `k`; "readable on day `k + 1`" is false | C | weaker: singly rather than doubly exponential rate | — | — | proved |

## E2, S1, L3.6 stretch — not delivered

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `not_pseudorandom_of_decided` | mandate E2 | a family decided on its own day is not pseudorandom | — | — | — | — | not attempted in Lean (see the report: the mixed-truth family has no FAF provability-induction hook; recorded as the obstruction) |
| unboundedly late edits | mandate S1 | L3.3 at `e n = n.unpair.1` | — | — | — | — | not attempted (the abstract theorem already admits it: `e n ≤ n` holds; the pad and gate rulers are the open work) |
| grade-(a) computability of L3.4 | mandate L3.6 stretch | FAF's settlement advice planted on day `N₀` | — | — | — | — | not attempted (obstruction recorded in the report) |
