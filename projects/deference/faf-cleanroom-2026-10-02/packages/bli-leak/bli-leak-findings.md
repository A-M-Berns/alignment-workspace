# bli-leak — findings about the sources

*Findings about the research, the plan and the mandate ([STANDARDS](../../STANDARDS.md) §5), each with a severity (blocking the note's conclusion / local error / imprecision / presentation) and a pointer. The mandate's K1–K10 are confirmed or corrected first; new findings (F-1…) follow; bli-soto-b-030 is recorded only, per plan §9. Written by the formalizer (Claude Fable 5.1, [scrubbed], 2026-09-30). Attribution claims are labelled ATTRIBUTION-UNVETTED.*

## The headline finding: "modify large prices however we like" is false as a transfer (confirmed, at grade (a))

**Pointer.** bli-slides-030 ([Understanding Trust talk 2024-10.pdf](../../sources/references/bli/slides/Understanding%20Trust%20talk%202024-10.pdf) p25: "since traders don't touch large sentences, we can modify them however we like without messing up any rationality properties of the market"); bli-slides-005 (`AISC 2025 - Paul final presentation (BLI).pdf`.pdf) p10: "constraints 1–3 are easy enough (we can modify large sentences however we like)"); `research/references/bli/understanding-trust/overleaf-final-source/main.tex:427` ("if we assign new prices to large sentences (across all the ℚₙ) in any way we like, it does not jeopardize the Logical Induction Criterion") and `:444` ("ℙ is now a logical inductor, since it agrees with ℚ on small prices"); `bli-program` §3.2(b), §3.11(j).

**Finding.** Read as a transfer statement — agreement with a logical inductor on every sentence small on the day it is priced (`E1x`), together with computability, makes a market a logical inductor — the claim is **false**, and FAF already contains the witness: its refutation of the paper's `thm:ifp` (PE1) exhibits the constructed inductor with day `0` alone re-priced (`cxPerturbed T`), which is computable, exploited by an efficiently computable trader, and — because on day `0` only `⊥` is small (`smallSet 0 = {⊥}`, `Cleanroom.Bli.BliLeak.smallSet_zero`) and the advice row leaves `⊥` alone — `E1x`-agrees with the inductor (`cxPerturbed_E1x`). `posthoc_transfer_refuted` (closed at `𝗜𝚺₁`) is the theorem; no pseudorandom family and nothing open enters it. The retreat "day `0` is degenerate; edit only late days" is refuted by the leak theorem: for any `N₀`, planting on day `N₀` the future decisions of a family pseudorandom relative to the inductor, one large atom per member, yields a market agreeing with the inductor exactly on days `< N₀` and on every day-small sentence, exploited by a five-node trader (`leakTrader_exploits`, grade (a) over any inductor with such a family; `posthoc_transfer_refuted_late`, over the instance of record, `partial: over OPEN computability (li-pseudorandom T7)`). **Severity: blocking the sources' conclusion** ("ℙ is a logical inductor") *as argued*; the conclusion itself is not refuted — an overlay the criterion tolerates must be efficiently expressible (`bli-transfer` L1), and the BLI construction must be restated in that form (`bli-program` §3.1, §3.3). The reading "transfer" (rather than "existence", bli-slides-005) is a choice among readings: ATTRIBUTION-UNVETTED (K8).

## K1 — the plan's certificate is the wrong lemma (local error in the plan; confirmed)

**Pointer.** `plan` `### bli-leak`; `bli-program` §4 row L3 ("the leak-reading e.c. trader (certificate via `ofSingleTradeBlocksBig` …)").

**Finding.** `EfficientlyComputable.ofSingleTradeBlocksBig` requires `∀ n, (f n).priceFree`; the leak coefficient `2 · price (ℓ n) (e n) − 1` *is* a price read. The certificate is `EfficientlyComputable.ofTradeBlocksBig` at count `if e n ≤ n then 1 else 0` over `MachineSpliceStream.serialize_price` — the route FAF's own `adviceTrader_efficient` takes (`Trader.lean`, `leakTrader_ec`). **Severity: local error in the plan.**

## K2 — the construction draft's day arithmetic, and the mandate's rate (local error in a superseded draft; confirmed, and the correction corrected)

**Pointer.** `bli-program-construction` X8 ("index `2^(2^k)+k`, readable on day `k+1`"); `bli-program` §3.2(a) ("readable on every day `n ≥ (2^(2^k)/c)^(1/d)` — doubly-exponentially later"); the mandate E1 (`tokenSize φ ≤ A * (n+1)^E`; "unreadable before day ≈ `2^(2^k)`").

**Finding.** X8 is false: writing that index takes `2^k` bits. But the program's correction and the mandate's E1 overshoot in the other direction: `bli-found`'s bridge meters what a trader can name by `bridgeBound C P ≤ 2^((C+6)(P+1))` in its polynomial output length `P` — *exponential* in the polynomial, because FAF's structured paper-prime escape lets `P` digits name a sentence of canonical size exponential in `P` (`tokenSize_le_of_structured`). The theorem the size model supports is `no_early_read : tokenSize φ ≤ 2^(A (n+1)^E)` and the rate `no_early_read_large : ¬ SmallOn k φ → MentionedBy (Tr.strat n) φ → 2^k < A (n+1)^E` — the day is at least of order `(2^k / A)^(1/E)`, **singly** exponential in `k`. Whether a *tighter* polynomial bound holds for what an e.c. trader can name is not decided here (the escape bound is an upper bound; no trader naming a size-`2^P` sentence with `P` digits is exhibited). **Severity: local error in X8 (confirmed); imprecision in the program's §3.2(a) rate and the mandate's E1 statement (new, F-1).** See F-1.

## K3 — the program misreads FAF's PE1 (imprecision; confirmed)

**Pointer.** `bli-program` §4 row L3 ("refines FAF's `not_overgeneral_ifp` to computable advice"); `bli-program-construction` X8 ("with computable-but-expensive advice in place of uncomputable advice").

**Finding.** FAF's advice market is already `ComputableMarket` (`computableMarket_cxPerturbed`: the advice is the diagonal's own settlement, found by a computable search). What the leak theorem adds is *late* edit days (any `N₀`, refuting the finite-prefix retreat) and an *independent* leaked truth (a pseudorandom family, not the market's own settlement), not computability. This re-scopes L3: L3.0 is a transport of FAF's witness, L3.3–L3.5 the new content. **Severity: imprecision.**

## K4 — `thm:dontwait` is the wrong hook (confirmed)

**Pointer.** `bli-program-construction` X8 ("`lic_does_not_anticipate_halting_unconditional` (`thm:dontwait`) for the family"); `bli-program` §3.2(b).

**Finding.** `thm:dontwait` concerns never-halting families whose prices go to `0`; a leak of a price that goes to `0` is worthless to the trader (the round value `(2t−1)(t − q)` with `q → t` is `≈ 0`). The hook is `thm:benford` (`lic_learning_pseudorandom_frequency` at `p = 1/2`) on a family decided *after* its reading day: then `q ≈ 1/2` while `t ∈ {0,1}`, and each decided round is worth `≥ 1/4`. **Severity: local error in X8; the program's §3.2(b) has it right.**

## K5 — extension mismatch (confirmed)

**Pointer.** `bli-program` §6 (this package's extension "a computable family pseudorandom relative to `liaHistory (paperDP T)`"); `plan` `### bli-leak` (the rate).

**Finding.** The former became `li-pseudorandom` (its T7, still open there); the plan's extension — the rate, E1 — is the one delivered (with the statement corrected, F-1). **Severity: presentation.**

## K6 — one family, one delay (confirmed)

**Pointer.** `bli-program` §3.2(b) ("decided within a computable delay `f` after the day `n(j)`"); `plan` ("decided-with-delay variant").

**Finding.** Both are `atomDP`'s delay profile `g`; with the reading day equal to the member index, `g n = n + 1` (`recordDelay`) and `pendingBound recordDelay 1` (`pendingBound_succ`). The abstract theorem takes any `g` with `pendingBound g C`. No second family exists. **Severity: presentation.**

## K7 — the registry (corrected)

**Pointer.** The mandate § Definitions of record and K7 ("this package takes `7` (leak atoms) and `8` (the pseudorandom placement)"); `Cleanroom/Bli/BliFound/Tags.lean` (the family registry in `freshAtom`'s docstring).

**Finding.** Since the mandate was written, `bli-found`'s registry lists family `7` as `bli-transfer`'s overlay-witness atoms (both attempts, `overlayWitnessFamily := 7`). This package therefore takes **`8` (leak atoms, `leakAtom K n = freshAtom 8 ⟨n, K⟩`) and `9` (the placement, `member n = freshAtomCode 9 ⟨n, 0⟩`)** — the next two reserved rows. Registry request for the orchestrator: add `| 8 | leak atoms, payload ⟨n, K⟩ (n the member, K the size pad) | bli-leak |` and `| 9 | pseudorandom placement, payload ⟨n, 0⟩ | bli-leak |` to `Tags.lean`'s table; `Tags.lean` was not edited. FAF's tags `7`/`8` (`schedAtom`/`signAtom`) are unrelated (the run's atoms are `Nat.pair (9 + f) _`; `freshAtom_ne_faf`). **Severity: local error in the mandate; corrected here.**

## K8 — which reading each row refutes (confirmed)

**Pointer.** bli-slides-005 vs bli-slides-030; `main.tex:427/444`.

**Finding.** bli-slides-005's "constraints 1–3 are easy" is about the *existence* of a BLI (existence at the degenerate point mass is `bli-trajectory`'s); the reading refuted here is the *transfer* ("without messing up any rationality properties", bli-slides-030; `main.tex:427/444`). The ledger's refutation rows say so; the choice of reading is ATTRIBUTION-UNVETTED. **Severity: presentation.**

## K9 — the junk value is `1`, not `0` (confirmed)

**Pointer.** bli-soto-b-2-022 ("`conditionalQuote` … has a vanishing denominator"); FAF `Properties/Conditioning.lean:67`.

**Finding.** FAF's `conditionalQuote V φ ψ = if V (φ ⋏ ψ) < V ψ then V (φ ⋏ ψ) / V ψ else 1`: at `V ψ = 0` (with nonnegative prices) it returns **`1`** for every `φ` (`conditionedHistory_junk`). The inventory's "vanishing denominator" is right; a docstring saying "conditioning on a refuted sentence gives price `0`" would be wrong. Under an inductor over the base, both numerator and denominator vanish (`counterlogical_price_tendsto_zero`, `counterlogical_conj_tendsto_zero`), so the quote carries no information either way. **Severity: imprecision (guarded).**

## K10 — memory (confirmed)

`Transport.lean` (through `Freeze.Counterexample` to `LIACompiler`) and `Exploit.lean` (`HistoricalMaturity`) were checked one at a time in their own files; `Closed.lean` (the one direct `LIACompiler` import) likewise. No slice kill occurred. **Severity: n/a.**

## F-1 — the mandate's E1 is not derivable from the bridge (imprecision in the mandate; new)

**Pointer.** The mandate E1 (`no_early_read (hTr) : ∃ N A E, ∀ n ≥ N, ∀ φ, MentionedBy (Tr.strat n) φ → tokenSize φ ≤ A * (n+1)^E`, "from `tokenSize_le_bridgeBound_of_mentionedBy`, `bridgeBound_le`"); `bli-program` §3.2(a).

**Finding.** `bridgeBound_le : bridgeBound C P ≤ 2^((C+6)(P+1))` gives an exponential-of-polynomial bound, not a polynomial one; the polynomial statement is neither derivable from the bridge nor refuted here. Delivered instead: `no_early_read` with `2^(A (n+1)^E)` and the rate `2^k < A (n+1)^E` (`no_early_read_large`, `leakAtom_unreadable_before`), both `Fidelity: weaker` with the reason in the docstring. The construction draft's "readable on day `k+1`" (X8) is false a fortiori. **Severity: imprecision (the mandate's statement); the plan's phrase "how late … as a function of the editor's certificate" is answered — `A`, `E` are the trader's `FP` polynomial's data — at the singly-exponential rate.**

## F-2 — largeness is not a hypothesis of exploitation (presentation; new)

**Pointer.** The mandate L3.3 (hypothesis list includes `hlarge`).

**Finding.** `leakTrader_exploits` needs no largeness: the trader reads a coordinate the market has set, whatever its size. Largeness enters only `E1x` (L3.1) — it is what makes the counterexample *agree* with the inductor. The mandate's list conflates the two roles; the docstring says so. **Severity: presentation.**

## F-3 — the trader's rank certificate forces a design choice (presentation; new)

**Pointer.** The mandate § Definitions of record (`leakTrader`: "`rank_le` needs `e n ≤ n`; make `e n ≤ n` a hypothesis or clamp with `min (e n) n`").

**Finding.** For the finite-prefix retreat `e = const N₀`, `e n ≤ n` fails on days `n < N₀`, and clamping the read to `min (e n) n` would read an *unedited* price on those days (harmless for exploitation, but not what the trader is for). The trader of record holds its position only on days `e n ≤ n` (empty trade list otherwise), the count `if e n ≤ n then 1 else 0` is a unary ruler for the two edit-day functions used (`leakTrader_ec_of_le`, `leakTrader_ec_const`), and the exploitation theorem takes `e n ≤ n` *eventually*. `Fidelity: variant` on `leakTrader`. **Severity: presentation.**

## F-4 — `TheoryTruth` is derivable from the stage form of "decided" (presentation; new)

**Pointer.** The mandate L3.3 (hypotheses `TheoryTruth χ DP t` *and* `hdec`).

**Finding.** `hdec` (stage form) implies `TheoryTruth` (`theoryTruth_of_decided`): a world consistent with every stage is consistent with stage `g n`. One hypothesis fewer on L3.3. **Severity: presentation.**

## F-5 — `hworld` for the union is a two-line corollary of `bli-found`'s conservativity (presentation; new)

**Pointer.** `li-pseudorandom-report.md` ("`hworld` for the union … the dependent's obligation").

**Finding.** `atomDP member x g` **is** `bli-found`'s `literalProcess` of an explicit schedule (`literalProcess_memberSchedule`), so `extendBy_hworld` with `paperDP_cleanroomFree` gives `hworld` for `(paperDP T).union (atomDP member x g)` for *every* stream `x` and delay `g` (`union_atomDP_member_hworld`). Other dependents of `li-pseudorandom` with a `freshAtom` placement can reuse the schedule construction. **Severity: presentation (a reusable lemma).**

## F-6 — E2 (a family decided on its own day is not pseudorandom) is not provable by the mandate's route, and is doubtful as stated (imprecision in the mandate; new)

**Pointer.** The mandate E2 (`not_pseudorandom_of_decided (hdec : ∀ n, χ n ∈ DP.D n ∨ ∼χ n ∈ DP.D n) [IsLogicalInductor Q DP] … : ¬ PseudorandomFrequency t p f Q`; "`lic_provind` gives `Q n (χ n) ≈ₙ t n`; the P-generable weighting `W i := price (χ i) i` … then contradicts frequency `p`"); FAF `DeferralPatient` (`Properties/Pseudorandomness.lean:173`).

**Finding.** Three obstacles, in increasing severity. (i) *No FAF hook for a mixed-truth family.* `lic_provind` (and `_true`/`_false`) needs all members theorems, or all disprovable; the literal family `n ↦ literalOf n` is machine-metered only for a machine-emittable truth stream; `affine_provind_theory_eq` needs a constant value. (ii) *The weighting is not patient.* FAF's `PseudorandomFrequency` quantifies over `f`-patient weightings only — `DeferralPatient f W P := ∃ C, ∀ n, ∑_{i ∈ Icc n (f n)} (W i).denote P ≤ C` — and `W i := price (χ i) i` has window sums of order `f n − n`, unbounded for any deferral that grows (e.g. `f n = 2n`); a refutation must use a sparse market-reading weighting whose sparsity is machine-emittable, and the weighted-average argument then needs a rate on `|Q n (χ n) − t n|` along the sparse set, which no `≈ₙ` statement supplies. (iii) *The claim over an arbitrary inductor is doubtful.* For a truth stream not computable at all, nothing forces an inductor's day-`n` price of `χ n` toward `t n` even though `χ n ∈ DP.D n`: a trader never sees the process, and the plausible payout of a day-`n` position in `χ n` is the day's coin; a market pricing a fair-coin family at `1/2` forever looks unexploitable (the trader's net worth is a `±1/2` random walk, unbounded below as well as above) — unformalized, conjectural, recorded as such. The provable neighbour is the *relative* form: under the extra hypothesis `Q n (χ n) ≈ₙ t n` (which FAF supplies for a machine-emittable truth through the literal family), pseudorandomness fails against a suitable patient weighting — a target with a rate argument of its own, not attempted here. Nothing about E2 is stated in Lean. **Severity: imprecision in the mandate (the route named does not exist); the extension is open, and its general form should be re-scoped to the relative form before anyone formalizes it.**

## bli-soto-b-030 — Ω's logical counterfactual as an undecided conditional (recorded only, per plan §9)

**Pointer.** `bli-soto-b-inventory` 030 (PIBBSS report §3.2, fn. 12–13).

**Finding.** "`n` the latest state not having decided `C`" admits one definition over a `DeductiveProcess` — the day before the first stage containing `C` or `∼C` (`decisionDay`, `lastUndecidedDay`, with a junk value at a stage-`0` decision) — and the quote `O_n(B ∣ C)` is FAF's capped `conditionalQuote` there (`omegaQuote`), non-junk iff `P m (B ⋏ C) < P m C` at that day (`omegaQuote_eq`). "These conditionals are pretty reasonable" has no statable content: nothing constrains the quote at an undecided day beyond the criterion's `≈ₙ` facts, which are about limits, not about one day. **Ill-posed as stated; recorded, not a target.** The author's replacement (bli-soto-b-2-022 (iii): an early state's expectation of a later state) is `bli-rvc-ui`'s hypothetical marginalization — pointer only; ATTRIBUTION-UNVETTED.
