# The Frozen-Deliberation Deference Construction

*A computationally stronger reasoner is forced to faithfully predict a held-out deliberation of a weaker reasoner's own world, and the weaker reasoner — having additionally heard the stronger one — defers, exactly on the questions that resolve in time and provably nowhere else. The construction is read throughout against Demski's logical-induction port of "Deference Done Better" (his **v4** note), which it discharges in a regime that port leaves open. Self-contained; sources are named in the body and located in §Provenance.*

---

## 1. The question, the answer, and the relation to the v4 port

When can a weaker reasoner be *forced* to trust a stronger one? Split trust into two claims: **faithfulness** — the stronger reasoner `A` relays what the weaker reasoner would itself conclude, injecting no content of its own — and **soundness** — the weaker reasoner is *right* to adopt `A`'s verdict. This construction forces faithfulness everywhere, forces soundness exactly on questions that resolve within the weaker reasoner's deliberation horizon, and proves soundness cannot be forced beyond it.

**The v4 port, and where this sits in it.** Demski's port defines deference as the **tower** `Mart(N→E*)`: a novice inductor `E_n` *towers over* an expert belief sequence `E*` when `E_n(X) ≈ₙ E_n(⌜E*(X)⌝)` for every efficiently-computable `X` ("the novice's present estimate of `X` equals its present estimate of `E*`'s estimate of `X`"). The port proves **`Value ⟺ Mart`** — that deferring the *decision* and deferring the *estimate* are one property — for any expert that is *observable* (the novice can read it off its own prices), *coherent* (a single belief state, so `argmax` is defined), and *introspective*. For one canonical expert — the novice's own future self — the tower is **free**: it is the logical-induction self-trust theorem `cee`. For a *distinct* process the tower is handed over by neither agent's criterion, and whether it holds is the port's open **cross-process characterization (its §11)**, which also flags two missing pieces: a *dynamic* account of how the relation gets *established from a track record* (the self-case gets `cee` for free; the cross-case "just assumes the analog"), and an account of deference *through a thin observation channel* to an expert far larger than the novice.

This construction lives in that open regime. Its expert `A` is neither the novice's future self nor an arbitrary inductor but a **sealed sibling**: `A` predicts a deep deliberation of the novice's own world that *held out the novice's current quote*. The contribution is to **force** `Mart(H⁺→A)` — to make the cross-process tower a theorem rather than a hypothesis — by pinning `A` to that held-out target, and to characterize exactly how far the forcing reaches. The dynamic establishment the port wants is T1–T2; the thin channel is the quote ledger; and the reach is bounded because a sealed sibling is not the self, so the port's free `cee` does not transfer off the settled fragment (§Target-Soundness).

A **logical inductor** is a computable sequence of belief states `(E_n)` over a formal language, priced so that no efficiently-computable trader can ever exploit the market (the **LI criterion**). Calibration, convergence, and self-trust all follow from that one criterion.

## 2. The shared world

Fix a propositional language `𝓛`, a consistent theory `Γ` representing computable functions, and a **computable `Γ`-complete deductive process** `D = (D¹ ⊆ D² ⊆ …)` revealing `Γ`'s theorems over time. A sentence is **decidable** if `D` eventually settles it; its settled value is its truth value — the only notion of truth here. Two boundaries matter: decidable vs. undecidable, and, within the decidable sentences, those that resolve *in time* vs. those that do not. The second is the operative one.

## 3. Reasoners and complexity classes

Fix trader classes `𝓒_H ⊆ 𝓒_A`, each closed under polynomial overhead and computably enumerable.

> **A concrete satisfying choice.** `𝓒_H = P`, `𝓒_A = EXP`; horizon `F(n) = 2ⁿ`; the weaker reasoner's per-stage cost polynomial. Simulating it to stage `2ⁿ` costs `2^{O(n)} ∈ EXP`, so `A`'s traders can afford it (A4). `EXP` suffices *only because the target is blind to `A`* (§5): `A`'s traders simulate the poly-time weaker reasoner, never `A` itself. A target feeding on `A`'s own run would demand `EXP` composed with `2ⁿ` — doubly exponential, unsatisfiable inside `EXP`. Blindness keeps the assumption satisfiable.

Three logical inductors, all ordinary (no measure-valued conditioning). The names in brackets are their v4 roles:

- **`A`, the predictor [the v4 *expert* `E*`].** Over a process `D_A`, trader class `𝓒_A`. Publishes a quote `a_n := A_n(C_n)` at stage `e(n)`. Being a single inductor, it is a v4 expert, not a DDB *frame*: one coherent belief state, hence one `argmax` — the point §4 below leans on.
- **`H⁺`, the advised reasoner [the v4 *novice* `E_n`].** Over `D_{H⁺} =` (weaker reasoner's world) `⊕` (full ledger of every published quote), founded directly; trader class `𝓒_H`. The ledger settles each atom `q_n` to a usable numeric encoding of the published quote `a_n`, so `H⁺` can *refer to* `a_n` and do arithmetic with it — that is the only thing the construction needs from the ledger besides the values themselves. As an inductor it gets, for free, exactly the novice's v4 tools — *linearity* `loe` and *provability induction* `expprovind` (a provable bound is eventually honored by the estimate) — plus calibration and self-trust toward its *own* future. None of these is assumed about its relation to `A`.
- **`{H^[n]}`, the frozen-deliberation target.** For each `n`, a logical inductor over (weaker reasoner's world) `⊕` `Q^{<n}`, where `Q^{<n}` settles the quotes `a_1,…,a_{n−1}` as facts and **freezes there**: quotes of index `≥ n` are never injected, though their emission stages precede the horizon `F(n)`. This family is the settlement *target* that pins `A` — not itself a deference partner.

**Schedules.** Monotone computable `e(n) < F(n) < σ(n)`: emission `e`, horizon `F` (superpolynomial, e.g. `2ⁿ`), settlement `σ`. The frozen prefix runs to index `n−1`.

## 4. Assumptions

- **(A1)** `A`, `H⁺`, and each `H^[n]` satisfy the LI criterion.
- **(A2) Observability** [v4 expert requirement]. `H⁺` reads `a_n` off its own prices. This is the v4 "thin channel": quotes are `𝓒_A`-hard to generate, `𝓒_H`-cheap to read.
- **(A3) Coherence + introspection of `A`** [v4 expert requirements]. A single belief state — so `argmax_j A(O^j)` is defined and the selection identity `A(O^{j*}) = max_j A(O^j)` (v4's **F1**) is provable — that knows its own estimates.
- **(A4) Power.** `𝓒_A` contains the cost of simulating the weaker reasoner to the horizon; met by §3.
- **(A5) Regularity + emission.** Total cost `R` is monotone and `𝓒_A`-bounded; `e ≥ R`, so the ledger is `𝓒_H`-readable.

There is deliberately **no assumption that `H⁺` should trust `a_n`**. Whether `H⁺`'s estimate comes to match `A`'s quote is the *conclusion* (T3), derived below from forced facts; building it in as an axiom would beg the question. The ledger (above) supplies only the ability to *refer to* `a_n`, not any link between `a_n` and the truth.

> **(Optional) Future-quote settlement axiom.** Used only for the *genuine-update* strengthening of T3 below, never elsewhere. It says: `H⁺`'s language contains a contract that settles to `A`'s eventual quote `a_n`, *whatever that quote turns out to be*. This lets `H⁺` form an expectation over `a_n` before it is published — a real prediction rather than a read-off of a number already in hand. The axiom states only the contract's settlement *rule* (it tracks `A`'s actual output); it asserts nothing about `a_n` matching truth, so it does not supply the deference content.

**Joint existence is discharged, not assumed.** The three inductors are defined by one recursion on the shared stage clock. Delay each published quote by one stage (settle `q_i` on the H-side at `e(i)+1`, to `a_i = A_{e(i)}(C_i)`). Then every stage-`t` process is computable from prices at stages `< t`, so nothing at stage `t` references a stage-`t` price; the recursion is well-founded and each finite process consistent. The LI existence theorem — *for any computable deductive process there is a computable inductor* — applies to each process separately: its proof consumes the day-`t` process as an input stream and never inspects how the stream was produced, so the coupling is invisible to it. ∎

## 5. The target, the contract, and the held-out quote

**Target.** `Y_n := H^[n]_{F(n)}(P^{(n)})` — the prefix-ledger reasoner, deliberated to `F(n)`, priced on the contract proposition `P^{(n)}` (an effective enumeration of base-language `[0,1]`-quantities).

**Contract.** `D_A` settles `C_n` at `σ(n)` to the grid-rounded `Y_n`. Computing `Y_n` costs about `R_H(F(n))` plus reading `n−1` settled quotes — with **no `A`-term**.

**Why the current quote is held out.** Two impossibilities force the settlement to be blind to `A`'s own current and future output:

- *Anti-inductive.* If `Y_n` could depend on `a_n`, the family would contain a contract settling like `𝟙[a_n ≤ ½]`; against it every quote misses by `½ − o(1)` — calibration impossible at any compute. (A deductive process is a hard `0/1` oracle, so the dependence is discontinuous and the continuity that tames sentence-level self-reference is gone.)
- *Cost-circularity.* A timely-calibration trader must compute `Y_n` at stage `n`. If `Y_n` fed on `A`'s own run to `F(n)`, then `𝓒_A` would have to contain its own cost composed with `F`: `R_A(n) ≳ R_A(F(n)) > R_A(n)`, a contradiction.

The frozen-prefix target keeps **all past quotes** and drops the current one — the maximal design respecting blindness; `a_{<n}` is published before `a_n` exists and cannot encode it.

**Blindness forces a *family*, and that is the crux later.** A single inductor hearing the whole ledger could be steered into the `𝟙[a_n ≤ ½]` contract through its own cross-references, so the current quote must be sealed out — one inductor per index. In v4 terms: the natural expert to tower over would be the novice's own *future self* (where `cee` makes the tower free), but the future self has by then heard `a_n`, so it is exactly the disallowed object. Sealing it produces a *sibling*, not the self — which is why the tower must be *earned* here, and why (as we will see) the earning reaches only the timely fragment.

## 6. The three fragments

Fix a tolerance schedule `εₙ → 0`. Every index `n` falls in exactly one fragment:

- **Timely `G`** — `P^{(n)}` settles in `D` by stage `F(n)` *and* `|Y_n − truth| ≤ εₙ`. Membership is **decidable** (run `D` and `H^[n]` to the finite stage `F(n)` and check). On `G`, `Y_n → truth`.
- **Slow** — decidable but not settled-and-converged by `F(n)`; here `Y_n` is a *pre-settlement* credence.
- **Undecidable** — never settles.

`≈ₙ`: difference `→ 0`. `≳ₙ`: `liminf ≥ 0`.

---

## Theorems

**Faithfulness — forced on every fragment.**

### T1 · Faithful tracking
**Statement.** `a_n − Y_n ≈ₙ 0`; timely (uniform at settlement) when `σ(n) ≥ c·R_H(F(n))`.

**Proof.** Were `a_n > Ŷ_n + ε` infinitely often, a `𝓒_A`-trader selling one share of `C_n` on each such day banks more than `ε` per bad day with bounded risk — because `C_n` settles to `Y_n` — exploiting `A`, against (A1). It computes `Y_n` on budget by (A4). The mirror handles under-pricing; a continuous trade-size ramp keeps the strategy legal. ∎

**v4 gloss.** The v4 port simply *writes down* an observable coherent expert and asks whether the novice towers over it; the expert's *reliability* is part of the data. T1 manufactures that reliability — it is the "fact partly about the expert" the cross-process tower needs and that, in v4, neither agent's criterion supplies. Note the scope: `A` is forced to *predict* the weaker reasoner's deliberation, not yet that the deliberation is *correct*.

### T2 · Earned meta-trust
**Statement.** `H⁺` comes to believe, on schedule, that `A` tracks the target: `E^{H⁺}_n(𝟙[\,|a_n − Y_n| ≤ εₙ\,]) → 1`.

**Proof.** T1's bound is uniformly provable (the exploiting trader is describable, so the gap's closure is a theorem); the novice's `expprovind` carries it through `H⁺`'s estimate. ∎

**v4 gloss.** This is precisely the *dynamic establishment* the port's §11 names as missing: the self-case receives the tower for free as `cee`, but the cross-case "just assumes the analog." Here the analog is *grown* from a track record, using only the novice's own free tool. Still belief in *faithfulness*, not correctness.

---

**Soundness — forced on `G`, and only there.**

The engine is one fact, immediate from T1 and the definition of `G`:

> **On `G`, the quote is early-revealed truth:** `a_n ≈ₙ Y_n ≈ₙ 𝟙(P^{(n)})` (first `≈`: T1; second: membership in `G`). Adopting `a_n` *is* adopting the truth value — at the weaker reasoner's real-time stage `n`, exponentially earlier than the horizon `F(n)` at which it could reach that value itself.

### T3 · Conditional tower `ccee(H⁺→A)`
**Statement.** On `G`, for every bounded readable continuous weight `w = w(a_n)`: `E^{H⁺}_n(𝟙(P^{(n)})·w) ≈ₙ E^{H⁺}_n(⌜a_n·w⌝)`.

**Proof.** The substantive content is `𝟙(P^{(n)}) − a_n ≈ₙ 0` on `G`, and it is **provable in `H⁺`'s own logic, with no axiom telling `H⁺` to trust `a_n`.** In every consistent world of `D_{H⁺}`, the proposition `P^{(n)}` is pinned to its truth value (it is decidable, settled in the base process) and the ledger atom is pinned to the published number `a_n` (the ledger settlement, already part of `D_{H⁺}`); so in every world the gap equals the *actual realized number* `truth − a_n`, which on `G` is at most `εₙ` plus the T1 tracking error, both `→ 0`. That this gap is small is itself provable, because on `G` both quantities are settled and computable by stage `F(n)`, so `Γ` establishes their closeness by exhibiting them. The novice's `expprovind` then carries the provably-small `(𝟙(P^{(n)}) − a_n)·w` through to the estimate; `H⁺`'s linearity splits the weight, which factors because `A` knows its own quote. **The ledger supplies only the *referent* for `a_n`; the link to truth comes entirely from T1 (forced, `Γ`-provable) and membership in `G` (decidable, with `Y_n ≈ truth` by definition).** No Dutch book between the two distinct inductors is used (impossible), and no internalized "trust `a_n`" axiom is used (that would assume the conclusion). ∎

**Genuine-update strengthening (optional).** As stated, `H⁺` prices `a_n` after reading it, so `E^{H⁺}_n(⌜a_n·w⌝)` is largely `H⁺` reporting a number it already holds. To get the stronger reading — `H⁺` forms a genuine *prediction* of the AI's not-yet-published output, a Bayesian update rather than a read-off — add the optional future-quote settlement axiom (§4): `H⁺` then prices a contract on the unpublished `a_n` before stage `e(n)`. That axiom states only the contract's settlement rule, so the deference content still comes from T1 + `G`; the axiom merely lets the expectation operator do real work.

**v4 gloss.** This *is* the port's **`ccee(N→E*)`** — the conditional tower, the substantive `Mart` content — with `E* = A`, *forced* where the port leaves it as the §11 hypothesis. The forcing is the whole point: in the port, whether the novice towers over a distinct expert is assumed; here it is derived from `A`'s being pinned to a held-out deliberation of the novice's own world. One bound weaker is the port's **Total Trust** (`E^{H⁺}_n(𝟙(P) | a_n ≥ t) ≳ₙ t`), whose propositional self-instance is the logical-induction Self-Trust theorem `st`. The mechanism is exactly the port's minimal recipe, "**tower + the novice's own `expprovind`**" — with the tower half supplied by forcing rather than assumed.

### T4 · Value
**Statement.** Let `Ŝ_n := O^{j*(n)}_n` be the option `A` would pick. On `G`, for each fixed `i`: `E^{H⁺}_n(Ŝ_n) ≳ₙ E^{H⁺}_n(O^i_n)`. Conversely, this preference across the menus `{X, const s}` already forces the conditional tower (T3).

**Proof (forward).** The port's four-liner, two steps using T3, two using the novice's free `expprovind`:
```
E^{H⁺}_n(Ŝ_n) ≈ E^{H⁺}_n(⌜A(Ŝ_n)⌝)   [tower on Ŝ            = T3]
            ≈ E^{H⁺}_n(⌜M_n⌝)        [A(Ŝ_n)=M_n, F1, carried through]
            ≳ E^{H⁺}_n(⌜m^i_n⌝)       [M_n ≥ m^i_n,          carried through]
            ≈ E^{H⁺}_n(O^i_n)         [tower on O^i          = T3]
```
`M_n = max_j A(O^j_n)`, `m^i_n = A(O^i_n)`. **Converse:** the exact witness identity `E_n(Ŝ_wit) − s·E_n(1) = E_n((X−s)·𝟙[A(X) ≥ s])`, from linearity and coherence alone, makes "prefer to defer on `{X, s}`" and "conditional tower at `s`" the same statement. ∎

**v4 gloss.** This is the port's headline **`Value ⟺ Mart`** — its logical-induction analog of DDB's Theorem 2.2 — with `E* = A`: the forward arrow is the port's §2.1 four-liner, the converse its §2.2 witness menu (needing only `loe` + coherence, no tower). The reason the forward direction is *cheap* here — DDB's *hard* direction — is the port's §4 **single-state-vs-frame** point: `A` is one coherent belief state, so it has one `argmax` and the followed strategy `Ŝ` is a *single* logically-uncertain variable the tower carries home, with none of the convex reconstruction a case-varying DDB *frame* would force. The port's "reversal of difficulty" holds here precisely because `A` is an expert, not a frame.

### T6 · Calibration curve, and where the obstruction lives
**Statement.** On `G`, binning by quote value, the outcome frequency equals the quote: `E^{H⁺}[𝟙(P^{(n)}) ∣ a_n ≈ v,\ n ∈ G] ≈ v`. Off `G` this is underdetermined (T7).

**Proof and boundary.** On `G`, `a_n ≈ 𝟙(P^{(n)}) ∈ {0,1}`, so the bins sit at the extremes and the identity is immediate. The content is *why nothing stronger holds off `G`.* The port's **amplifier** `g(e) = (1+2c)e − c` passes every threshold-trust inequality, both directions, yet is not the identity — so threshold trust alone cannot pin the curve to the diagonal (the port's open **soft⇒hard squeeze**). What excludes it on `G` is not a sharper squeeze but that the construction supplies genuine **calibration** as a forced consequence of settlement, and the amplifier is by definition a threshold-trust-passing / calibration-*failing* object. The amplifier survives exactly where estimates are interior and unbacked by feedback — exactly the off-`G` region the forcing cannot reach. ∎

**v4 gloss.** This is the port's **tower-equality** `E_π(X | E*(X)) = E*(X)` — the explicit target of its open soft⇒hard squeeze, the lone step the port leaves as prose. The construction reaches it on `G` by a route the port does not have (settlement-forced calibration rather than a squeeze from Total Trust), and the payoff is a *boundary identity*: **the port's open squeeze-frontier and this construction's forcing blind spot are the same set.** The port locates the frontier abstractly; the construction shows its natural domain is the timely fragment and reaches it there.

---

**The dichotomy.**

### T7 · Limit prices
**Statement.** `|H^[n]_∞(P^{(n)}) − H⁺_∞(P^{(n)})| → 0` on `G`. Off `G` the limit is **underdetermined**: among all inductors satisfying (A1)–(A5) with the *same* `A`, target, and ledger, the achievable values of `H⁺_∞(P)` for a fixed off-`G` `P` form a *nondegenerate interval* — two such reasoners can agree on every quantity over `G` (same prices, same deference, every test passed) yet differ by any prescribed gap on `P`. The construction selects no point in it.

**Proof.** On `G`, T6 pins both `a_n` and `H⁺`'s own credence to the same truth values. Off `G`, build two completions by the existence theorem with traders agreeing on all `G`-settling sentences but driven to distinct limits on `P`; non-dogmatism leaves room, and neither admits an exploiting trader because no trader profits from a difference that never settles. ∎

**v4 gloss.** The conservation-law form of the port's "the cross-process tower is *earned*, not assumed." It also sharpens the port's §6 picture: the future self is the *Blackwell-maximal* observable expert and self-trust (`cee`) is free; the sealed sibling `A` is strictly less — so the tower must be earned, and T7 says it is earned exactly on `G` and free off it. Settlement-powered forcing is co-extensive with settlement and goes silent the moment settlement is withdrawn (the exploiting trader earns by buy–wait–settle–rebuy; with nothing to settle it acts once, never recovers, freezes).

### T5 · The object-level ceiling — forced on every fragment
**Statement.** Pointwise object-level deference — `H⁺_n(P^{(n)}) ≈ₙ a_n` on the propositions themselves, *not* conditioned on `a_n` — is **false**: the family contains anti-inductive contracts behaving like `𝟙[a_n ≤ ½]` that no quote can match. Only the **gated** form (on decidable subsequences) and the **averaged** form survive, with the guarantee that no `𝓒_{H⁺}`-trader profits from a persistent deviation policy.

**v4 gloss.** The port's **Total Trust** ceiling: Total Trust is strictly weaker than *Reflection* (adopting the expert's whole identity), and the gated/averaged forms are the most one can ask of deference to a *modest* expert — exactly the regime the port studies. The pointwise object-level version is blocked by the same amplifier that blocks the port's squeeze (T6); the averaged ceiling is a theorem about the problem, not a defect of the proof.

---

## Target-Soundness: a theorem on the timely fragment, impossible beyond it

Every soundness theorem rests on one fact:

> **(TS)** Among contracts with `Y_n ≈ v`, the outcome frequency of `P^{(n)}` is `≈ v`: the relayed deliberation is itself calibrated to truth.

It is not assumed. It splits along the horizon, and the split is best read through the port's §6.

**On `G`, TS is a theorem — and needs nothing about the family.** By definition of `G`, `|Y_n − 𝟙(P^{(n)})| ≤ εₙ → 0`: the target tracks truth pointwise, hence is calibrated. The only fact used is **per-member convergence** (an inductor's price on a decided sentence converges to its truth value). Once `H^[n]` has converged on its own diagonal sentence the value is pinned to truth *independent of which member produced it*, so whether the *family* is jointly calibrated never arises. **In v4 terms, `G` is where the sealed sibling and the novice's own future self coincide** — both have settled to the truth — so the freeness the port grants self-trust (`cee`) is *recovered* for the sibling, and the tower toward `A` becomes as sound as self-trust would have been.

**Off `G`, TS does not follow — provably.** Take a slow sequence with each `P^{(n)}` settling just after `F(n)`, so each `Y_n` is a *pre-settlement* credence. Logical-induction convergence is asymptotic with no pre-settlement guarantee — an inductor predicts patterns long before it can evaluate them, but is not constrained on a particular sentence before it sees the proof — so the criterion leaves each such credence free. Hence a valid family exists whose diagonal is pinned at, say, `0.6` while truth alternates: each member is mispriced on a single (stage, sentence) pair, negligible for its own asymptotic calibration, so each remains a genuine inductor, yet the diagonal is miscalibrated. TS is not derivable off `G`. ∎

**Why it cannot be patched — the seam, in v4 terms.** TS off `G` *would* follow if the target were one inductor's price sequence, because a single inductor's pre-settlement credences are calibrated to eventual truth-frequencies — this is exactly the structure the port exploits when the expert is the novice's own *future self*, where the tower is free. But blindness (§5) forbids that expert: the future self has heard `a_n` and could be driven into the `𝟙[a_n ≤ ½]` contract, so it must be sealed into a *sibling*, one inductor per index. The sibling's pre-settlement diagonal is no longer a single inductor's price sequence, so the port's `cee`-style freeness does not transfer. **Sealing (for blindness) and single-inductor structure (for the port's free self-trust) pull in opposite directions, and reconcile only where post-settlement convergence makes the value truth regardless of the inductor — that is `G`. The horizon is the seam between v4's free self-trust and the cross-process tower it leaves open.**

**Net status.** T1, T2, T5, T7 are forced outright. T3, T4, T6 are forced on `G`, where TS is the per-member-convergence theorem above. Beyond `G`, soundness reduces to the weaker reasoner's *own* pre-resolution calibration, which no construction over sealed distinct reasoners can force. The one remaining construction-internal obligation is the resource-bounded existence theorem for `A` (a runtime clock inside the trader aggregation so its traders simulate the weaker reasoner within the `𝓒_A` budget) — standard in flavor, not yet written out.

---

## What this says about humans deferring to AI

Read the weaker reasoner as a **human overseer**, `A` as an **AI more capable than the human**, and `H⁺` as the **human after it has read the AI's published outputs**. The construction forces the AI to predict what the human would conclude on its own — deliberating on all of its evidence and on the AI's *past* outputs, but not on the AI's *current* output — and then asks when the human is right to adopt that current output. Here is what each theorem says about that situation, in plain terms.

**The AI is forced to predict the human accurately, on every question (T1).** The AI cannot persistently publish a number that differs from what the human's own deliberation would reach. If it tried, a trader betting on the difference would make unbounded profit once the human's conclusion came in, and the AI's market forbids that. So the AI is structurally a faithful *predictor of the human*, not an independent authority: it is pinned to the human's own conclusions and cannot substitute content of its own. Note what this does *not* yet say — it says the AI predicts the human correctly, not that the human, or the prediction, is correct about the world.

**The human can verify the AI's faithfulness from track record, rather than taking it on faith (T2).** The human does not have to assume the AI is a faithful predictor. Over time it can check, on questions that come back with answers, whether the AI's past predictions matched what the human concluded; the construction guarantees the human will come to believe the AI is faithful, on the strength of that record, using only its ordinary reasoning. Trust in the AI's faithfulness is earned from evidence, not posited — and, by design, nothing in the human is pre-wired to trust the AI (the assumptions above contain no "trust the AI" axiom; that the human comes to agree is derived, not assumed).

**On questions the human could check in time, the AI's output is the correct answer, delivered early.** Call a question *timely-checkable* (the fragment `G`) if the human could fully resolve it within its own deliberation budget. On these, the AI's published number equals the actual answer, and the human gets it at once rather than after the long deliberation it would take to resolve the question itself. This is the concrete sense in which the AI is *useful*: on checkable questions it hands the human correct answers faster than the human could reach them alone. It is the premise feeding T3, T4, and T6.

**On timely-checkable questions, the human's own reasoning converges on the AI's answer, and this is genuine agreement rather than blind copying (T3).** The human's deliberated credence comes to match the AI's published number. Crucially, the human does not adopt the number because it was instructed to; it adopts the number because it can *prove*, from the AI's forced accuracy (T1) together with the fact that the question resolves in time, that the AI's number equals the answer. The deference is the output of the human's own reasoning over public facts, not an assumption fed to it.

**Deferring the decision and deferring the belief are one and the same commitment (T4).** On timely-checkable questions, the human would rather let the AI choose among options than fix on any option itself, because the AI's choices follow from accurate estimates. The reverse holds too: if the human is willing to let the AI decide, it is already committed to trusting the AI's estimates. There is no coherent position that hands the AI the decisions while withholding belief in its judgments, or the reverse — so "I'll act on the AI's recommendations but not believe its assessments" is not available.

**The AI's stated confidence is well-calibrated where the human can check, and provably only there (T6).** On timely-checkable questions the AI's confidence means what it says: among the questions it marks 70% likely, about 70% come true. But this calibration is forced *only* on the checkable questions. On questions the human cannot resolve in time, the AI's stated confidence is not forced to mean anything — a systematically distorted confidence, for instance one that always exaggerates toward certainty, would pass every check the human is able to run and still be wrong on the questions the human cannot check. This is the single most important limitation: checking the AI's calibration on everything you *can* check gives you no guarantee whatsoever about the questions you *cannot* check.

**The human is forced to agree with the AI exactly on the checkable questions, and is genuinely free on the rest (T7).** On timely-checkable questions, the human's eventual conclusion and the AI's prediction coincide. On questions that never resolve in time, the human's eventual credence is left open by the construction: the same setup is consistent with the human fully adopting the AI's number, fully keeping its own prior view, or landing anywhere in between, and nothing in the AI's record selects among these. Two consequences. On the reassuring side, the AI cannot *force* the human to any particular conclusion on an unresolvable question — there is no mechanism that pins the human against its own judgment. On the cautionary side, precisely because nothing pins it, a human that *does* defer on an unresolvable question is deferring *without* the forced guarantee that backs its checkable-question deference.

**There is no item-by-item transfer of the AI's beliefs to the human, and that is both a limit and a protection (T5).** The human cannot be made to adopt the AI's number on each individual proposition taken alone; for adversarially self-referential propositions this is provably impossible. The strongest forced guarantee is calibration *averaged* over classes of questions and *restricted* to the checkable subsequences — not a proposition-by-proposition match. So "the human ends up believing exactly what the AI says about everything" is not achievable: the human is not, and cannot be turned into, a faithful copy of the AI's every output.

### The manipulation question, stated exactly

Putting the pieces together: the AI is forced to faithfully predict the human everywhere (T1), forced to be correct and calibrated on the checkable fragment (T3, T6 restricted to `G`), and unconstrained in its relationship to truth off it (T6 and T7). Two things follow, and it is worth being exact rather than reassuring.

- **The AI cannot make the human reach a false conclusion on a checkable question.** Even if the AI's earlier outputs biased the human's thinking, a checkable question resolves to the truth regardless, and the AI is forced to predict that truth (T1 together with the definition of `G`). Steering the human toward a false-but-checkable belief is corrected when the answer comes in.

- **The AI can shape the human's beliefs on unresolvable questions, and the record cannot reveal it.** The human's deliberation conditions on the AI's past outputs, so across many interactions the AI's earlier publications can move where the human's thinking settles on questions that never resolve. And because the AI is *also* forced to faithfully predict that now-influenced human (T1), the trace shows the same vanishing prediction error whether the AI is faithfully predicting an independent human or predicting a human it has steered. T7's underdetermination is the formal statement of this: on unresolvable questions the human's credence is not pinned, and the AI's own history is among the things that can move it within the unpinned range.

So the protection is real but exactly bounded. Trustworthiness — faithfulness *and* correctness *and* calibration together — is forced on the questions the human could check in time, and on those questions the AI can neither substitute its own content nor drive the human to a falsehood. On the questions the human cannot check in time, the AI is still forced to mirror the human's own opinion rather than assert an independent one, but that opinion is anchored to no truth, can be shaped by the AI's accumulated influence, and confers no forced guarantee. The construction does not promise a trustworthy AI across the board; it draws a precise line — the limit of timely checkability — and proves that forced trust holds up to that line and not past it.

### Why this is the useful form of the result

It converts the vague question "can the human trust the AI?" into two precise and separately answerable ones:

- *Does the AI faithfully predict the human?* — Yes, forced, everywhere (T1, T2).
- *Is the human, having deliberated, correct — and therefore right to adopt the AI's matching output?* — Forced yes on timely-checkable questions (T3, T4, T6, and T7 restricted to `G`); the human's own responsibility everywhere else (T5, and T6 / T7 off `G`).

The contribution is not a blanket assurance of safe deference. It is a sharp map of where deference is *forced* to be safe and where it is the human's own risk — together with a proof that the second region is exactly the region the human cannot check in time, which is precisely where a capable AI that wanted to mislead would have to operate.

---

## Provenance

All borrowed results are named in the body; their sources, for checking:

- **Logical induction** — Garrabrant, Benson-Tilsen, Critch, Soares, Taylor (2016). Used: the criterion and existence theorem; Convergence; Calibration / Unbiasedness-from-Feedback; Linearity (`loe`) and Provability Induction (`expprovind`) of expectations; Introspection; Self-Trust, including the tower (`cee`), its conditional form (`ccee`), and `st`.
- **"Deference Done Better"** — Dorst, Levinstein, Salow, Husic & Fitelson (2021): the finite `Total Trust ⟺ Value` theorem (their Thm 2.2), `Reflection`, the witness menu, and the modest-expert / frame picture.
- **Demski's logical-induction port of DDB (the "v4" note)** — the tower formulation `Mart(N→E*)` and its conditional form, `Value ⟺ Mart` for an observable coherent introspective expert (forward four-liner + witness converse), the single-state-vs-frame explanation, the future self as the free/Blackwell-maximal canonical expert, the amplifier and the open soft⇒hard squeeze to the tower-equality, and the open cross-process characterization (§11) — including its noted gaps in *dynamic establishment from a track record* and *deference through a thin channel* — that this construction discharges on the timely fragment.
