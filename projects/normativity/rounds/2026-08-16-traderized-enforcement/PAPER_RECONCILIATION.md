# Paper reconciliation

Where this round's results sit in the generalized-Logical-Induction narrative,
and which of that narrative's intended steps they change.

The one-line answer: the architecture coheres. Force is intact, deductive
recovery is clean in both directions, and the semantic channel works once live
worlds are defined by **support** rather than by Dirac admissibility. What remains
is a real but ordinary gap: the enforcement inequality controls *expectations*
under admitted credences, while the exploitation criterion is *worldwise*, and the
bridge between them needs a hypothesis.

An earlier draft of this note defined a live world as one whose own price vector
lies in the admissible region. That is wrong, and everything it implied is
withdrawn — see §5.

## 1. Two models, one algorithm

**Model A**, which is what PR #38 built: the assessment set is `PC(D_t)`, and
`K_t` is an ambient constraint the enforcement trader pushes prices toward.
Safety asks whether enforcement loses too much in a world `D_t` still permits.

**Model B**, which the paper intends: the **semantic** object is a credal set
`C_t ⊆ Δ(Ω_t)`, primitive rather than derived, and

    Ω_t^live  =  { ω : ∃ μ ∈ C_t, μ(ω) > 0 } .

Its price projection `K_t = π_t(C_t)` is what a trader can see and enforce. A
world is live when *some* admissible credence gives it positive mass; it need not
be admissible as a point mass. When a source supplies only a price region, the
semantics is a **named lift** and not a derivation — `SEMANTIC_PROJECTION.md` §4.

**They are different constructions, and an earlier draft of this note said
otherwise.** The world process is not consumed only by the criterion: Logical
Induction's `Budgeter` quantifies over it twice, in the shutoff test and in the
scaling factor, so a construction assessed against `Ω_t^live` must use

    TF^live + E     rather than     TF^D + E ,

and these are different functions of the same belief history. One sentence, a
unit buy at `1/2`, budget `1/10`: the scaling is `1/5` against `{A false, A true}`
and `1` against `{A true}` alone, because the dropped world is exactly where the
buy loses (`test_budgeter`). Different scaling, different aggregate, different
prices.

They **coincide in the deductive special case**, and only there: `C_t^D =
Δ(PC(D_t))` gives `Ω_t^live = PC(D_t)`, whereupon the generalized Budgeter *is*
the ordinary Budgeter. That specialization is checked across stages in
`test_budgeter.DeductiveSpecialization`.

So "same algorithm, different criterion" is available only under that explicit
hypothesis, and the choice between the two models is a mathematical fork rather
than an editorial one.

**Generalized exploitation (Model B).** A trader `T` exploits `P` relative to a
live-world process `Ω^live` when

    { W( ∑_{i≤n} T_i(P) )  :  n ∈ ℕ,  W ∈ Ω_n^live }

is bounded below and not bounded above. Same shape as `def:exploitation`, with
`PC(D_n)` replaced.

**Which recovers ordinary Logical Induction.** Model A recovers it by making
`K_t` vacuous, which is the wrong direction for a generalization — deduction
stays primitive and the constraint is an add-on. Model B recovers it by making
`K_t` the deductive constraint, which is the right direction: deduction becomes
an instance. §3 proves the recovery.

## 2. The live-world lift, at the type the Budgeter consumes

**The typing question, and the source's answer.** When the priced fragment grows,
what does the generalized construction quantify over? A sequence of world sets on
growing domains does not admit literal nesting: a valuation on `Φ_t` is not a
valuation on `Φ_{t+1}`.

The source does not have this problem, because its worlds are **total**. A world
is a truth assignment `W : Sentences → 𝔹` (`def:world`), so the world space is
fixed and `PC(D_{t+1}) ⊆ PC(D_t)` is ordinary subset inclusion. What varies is the
finite **support** the computation touches: the `Budgeter` proof fixes
`S' = ⋃_{i≤n} support(T_i)` and observes that every quantity it needs — the
shutoff test and the scaling infimum alike — depends only on a world's restriction
to `S'`, a finite set.

So the generalized object is one process over a fixed world space, exposing

    restrict(t, S)  =  { W|_S : W ∈ L_t } ,     finite for finite S.

The priced fragment growing changes which supports are queried; it does not change
the type of anything. `src/assessment.py` is that interface.

**Theorem (statement).** Let `L` be an **assessment process** over a fixed world
space, satisfying

- **(L1) temporal nesting.** `L_{t+1} ⊆ L_t`.
- **(L2) effective finite restriction.** A total computable function returning,
  for each date `t` and finite sentence support `S`, the finite set
  `restrict(t, S)`.
- **(L3) nonemptiness.** `L_t ≠ ∅`, on the supports actually queried.

Then `Budgeter` and `TradingFirm` of `arXiv:1609.03543` §5, with `PC(D_t)|_S`
replaced by `restrict(t, S)` throughout, are well defined and computable, and the
analogues of `lem:budgeter`.1–3 and `lem:tfdom` hold with exploitation read
relative to `L`.

**Restriction consistency is a lemma, not a hypothesis.** Restriction composes, so
for `S ⊆ S'` the restrictions of `restrict(t, S')` to `S` are exactly
`restrict(t, S)`. It is checked in `test_assessment` so a hand-built process
cannot quietly violate it, but nothing assumes it.

**Nesting is checked on common supports.** `restrict(t+1, S) ⊆ restrict(t, S)` is
the computable shadow of (L1); global nesting implies it, and the converse holds
for processes closed in the product topology — which `PC(D_t)` is — though nothing
here relies on the converse. `test_assessment.TheFailureCaseIsRejected` displays a
process failing it, on both a small and a large support.

**What each hypothesis pays for**, from the source proofs:

| source step | what it consumes |
|---|---|
| `Budgeter` computability | (L2): the shutoff test and the infimum both range over `restrict(m, S')`, finite and decidable |
| `lem:budgeter`.1 | (L2) only |
| `lem:budgeter`.2 | **(L1)**: its induction needs a world assessed at `t` to have been assessed at `t-1`, pointwise on total worlds |
| `lem:budgeter`.3 | the exploitation definition alone |
| `lem:tfdom` | `.2` and `.3`, plus the source's `ℓ¹` bound on strategies, which is about traders and not worlds |
| `lem:mm` | **nothing** — it quantifies over all worlds, so any assessment process inherits its bound |
| (L3) | not used by the algebra; without it the infimum is over an empty set and the criterion is vacuous |

`PC(D_t)` satisfies all three. `Ω_t^live` satisfies (L1) when `C_{t+1} ⊆ C_t`,
which is sufficient and not necessary — two credal sets can have the same live
worlds with neither containing the other (`test_semantics.Nesting`).

**Evidence: `lean-proved`.** The proof-closing pass formalized it against the pinned
dependency's own `Budgeter`, `TradingFirm`, `Strategy n`, `Trader` and `MarketMaker`:
`BudgeterAt_value_eq_of_safe`, `budgetedTrader_netWorth_floor`,
`exists_budgetedTrader_exploits`, `AssessmentFirm.trading_firm_dominance` and
`AssessmentFirm.no_efficient_trader_exploits`.

**And the hypotheses are weaker than (L1)–(L3).** The formalization uses none of
global nesting, nonemptiness or effectiveness: only support-local nesting and finite
sound-and-complete restrictions. The table above is superseded on two rows — nesting is
consumed by `lem:budgeter`.1 as well as `.2`, and (L3) is a nonvacuity condition on the
§4 properties rather than a hypothesis of the construction. `PROOF_CLOSURE.md` §II
carries the corrected account and the witnesses separating the two nestings.

## 3. Deductive recovery

Take the canonical deductive constraint `K_t^D = π_t( Δ(PC(D_t)) )`, the
coherence polytope generated by the propositionally consistent worlds. Then

    Ω_t^live  =  PC(D_t)          and therefore     generalized criterion  =  LIC_D .

**Forward.** `δ_ω ∈ Δ(PC(D_t)) = C_t^D` for `ω ∈ PC(D_t)`, so `ω` is live.

**Reverse.** Every `μ ∈ Δ(PC(D_t))` is supported inside `PC(D_t)` by definition,
so a live world is in `PC(D_t)`.

Both directions are the definition of support, and **no hypothesis about the
pricing map appears**. An earlier draft ran the recovery through the price region
`π_t(Δ(PC(D_t)))` and needed the pricing map to separate worlds; that route is not
merely unproved but false, and `SEMANTIC_PROJECTION.md` §2 has the witness — the
anticorrelated mixture projects into the region with its whole support
deductively impossible.

Checked at four stages of a three-sentence fragment on sets of sizes 4, 2, 2 and 1,
plus the two-sentence correlated pair, with both directions exercised separately
(`test_semantics.DeductiveSemanticRecovery`). **Derived**, with no caveat.

**What is recovered is the semantics, not the algorithm's use of `D`.** The
source still consumes `D` inside `Budgeter` and inside the definition of
exploitation. The correct sentence for the paper is therefore:

> traderization generalizes the **operative-force role** associated with
> deduction

and not "traderization replaces the deductive process". The round has said this
since its first pass and nothing here changes it.

## 4. The obstruction, and why two channels

The paper wants a reason finite prices cannot simply be required to satisfy the
constraint. There are now three independent ones, and they are of different
kinds.

1. **Existence.** A market maker additionally required to display `P_t ∈ K_t`
   must satisfy two demands at once, and they can be jointly infeasible — one
   sentence, `K = {P ≤ 1/2}`, an ordinary aggregate buying one share flat. Logical
   Induction's own maker is total; this one is not known to be, and here is not.
2. **Slack.** The actual maker's contract bounds the aggregate's cube maximum
   gain by `2^-n` rather than forcing it to zero, so what it delivers is
   conformance, not projection.
3. **Geometry.** Exactness is not always available. For a one-sentence region
   strictly inside `(0,1)` no continuous trader achieves exact membership against
   a positive disturbance budget (`derived`); a coherence relation in two
   dimensions leaves a surviving cancellable band (`witness`); and the general
   condition is conjectural. `ENFORCEMENT.md` §5 keeps the four evidence levels
   apart.

So the two-channel split is defensible, and the clean statement is

    what counts as admissible   ≠   how finite prices are pushed toward admissibility.

**Adopt it.** It is the round's best candidate for the paper's central
integration result, and reason 1 is the strongest form of it: the two channels
are not merely convenient to separate, the collapsed version can fail to exist.

## 5. The withdrawn reading, and what replaced it

An earlier draft defined `Ω_t^live` as the `{0,1}` worlds whose own price vector
lies in `K_t`, and concluded that a constraint source launders its own liability:
every live world is in `K_t`, the enforcement inequality gives the position
nonnegative value there, so liability is identically zero and the safety theorem
holds by construction.

**Both halves are wrong.** The definition is degenerate — under
`K = {p(A) = 1/2}` neither world's point mass is admitted and the Dirac reading
returns *no live worlds at all*, while both worlds are live at capacity `1/2`. And
the laundering witness does not launder: under `K = {p(A) ≤ 1/2}` the credence
`μ(A) = 1/2` is admitted and gives the true world positive mass, so that world
stays live, and the enforcement position still loses `−9/40` there.
`test_regressions.DiracLiveWorldsAreNotLiveWorlds` pins all of it.

The logical error was a type collapse. The enforcement inequality bounds the
position's value at **price vectors** in `K_t`, and `E_μ[E_t]` is exactly the
position's value at `π_t(μ)`. So what the inequality delivers is

    E_μ[ E_t ]  ≥  ∑_j β_j g_j(P_t)²  ≥  0     for every μ ∈ C_t ,

a bound on **expectations**, from which nothing follows about the value at any
individual world in the support of such a `μ`. Writing `Ω^live ⊆ K_t` was reading
a credence as a price vector.

**So the safety condition keeps its content under the correct semantics**, and
Models A and B agree on the witness rather than disagreeing: both convict.

## 6. The bridge, and what it costs

What survives is a genuine gap, of ordinary size.

**The problem.** An admitted credence can have nonnegative expected value for the
enforcement position while putting tiny mass on a live world where the position
loses heavily. Exhibited: with `K = {p(A) ≤ c}` for `c` running `1/4`, `1/20`,
`1/100`, the expectation stays nonnegative under an admitted credence at every
step while the worldwise loss at the true world grows monotonically
(`test_semantics.SmallSupportHidesLargeLoss`).

**Support capacity.** Define `θ_t(ω) = max { μ(ω) : μ ∈ C_t }`, computed exactly
by vertex enumeration of `C_t`. Liveness and the quantitative condition are the
same number at two thresholds: `ω` is live exactly when `θ_t(ω) > 0`, and the
coverage hypothesis asks for `θ_t(ω) ≥ θ` uniformly.

**The bridge inequality.** From `E_μ[X] ≥ a`, `μ(ω) ≥ θ`, and an upper bound `U`
on `X` at the other worlds,

    X(ω)  ≥  ( a − (1 − θ) U ) / θ .

`U` is **named, not smuggled** — the dispatch was right to insist. For a realised
position it is the cube maximum gain `max_gain(ζ_E, P)`, which is exactly the
largest value the position takes in any world, so it is computable from declared
quantities. With `a = 0` from the enforcement inequality this gives

    E_t(ω)  ≥  − (1 − θ_t(ω)) · max_gain(ζ_{E,t}, P_t) / θ_t(ω) ,

checked at every live world over a price grid
(`test_semantics.TheSupportBridge`).

**Coverage is one route, not the only one, and not necessary.** The liability
identity already gives `L_t(ω) ≤ ∑_j β_j g_j(P_t) d_j(ω)` at *any* world, live or
not, with no support hypothesis at all. The two bounds use different information —
the first the region's geometry relative to the world, the second the credal
capacity — and neither dominates. So the safety theorem does **not** need
Coverage; Coverage is a sufficient route to its hypothesis when the deficits are
not the natural quantity to know.

## 7. Three coverage questions, kept apart

**1. Support existence.** `ω` live iff `θ_t(ω) > 0`. **Definitional**, not a
theorem, and it is the definition §5 got wrong.

**2. Quantitative support coverage.** `θ_t(ω) ≥ θ > 0`. **A sufficient
hypothesis** for the bridge of §6, competing with the deficit route rather than
completing it. Not shown necessary.

**3. Diachronic removal.** A source setting `θ_t(ω) = 0`. Under support semantics
this is not a bookkeeping choice: it means the constraint *entails* `ω`
impossible, which is settlement-shaped, and it is the one place the old laundering
worry survives — in a much narrower form. It belongs with provenance,
answerability and the settlement interface's write-once and no-claw-back rules,
not with the algebraic safety theorem.

The round does **not** unify the three, and nothing here licenses one condition
doing all three jobs. Both names stay provisional and neither is identified with
`coverage(Due)`; the type mismatch in `INTEGRATION_MAP.md` §3 is unchanged.

## 7a. Nesting

**Lemma.** `C_{t+1} ⊆ C_t ⟹ Ω_{t+1}^live ⊆ Ω_t^live`. If `ω` is live at `t+1`
some `μ ∈ C_{t+1} ⊆ C_t` gives it positive mass. Immediate, and recorded because
the trading-firm lift needs it.

Which sources give credal nesting: monotone deduction, accumulating settlements,
and normative constraints that only ever tighten. Which do not: **revisable
normative constraints that enlarge or rotate `K_t`** — verified, with an enlarging
revision breaking both the credal containment and the live-set containment
(`test_semantics.Nesting`). So the lift's hypothesis is exactly *the constraint
only ever tightens*, and normative revision falls outside it. That is identified,
not solved.

## 8. One paper or two

**One paper, with the force result as a self-contained module.** The reason is
theorem dependency, not length.

The force results — the compiler, the enforcement inequality, the conformance
modulus, the exactness case analysis, the existence asymmetry — mention no
criterion, no assessment set and no deductive process. They are statements about
a market maker's contract, a region and a price. They can be stated, proved and
read without any of the generalized-LI apparatus, and a reader wanting only
"how do I make a bounded reasoner respect a convex constraint" needs nothing else.

The safety result cannot be lifted out: it composes `lem:mm` and `lem:tfdom` with
a liability hypothesis over an assessment set, and that set is the generalized
semantics. The coupling is what puts the two in one paper, and it is a cleaner
coupling than the previous draft supposed — the semantics supplies the set, the
force module supplies the position, and the bridge of §6 joins them.

So: force as a module with its own statement of what it assumes about the market
maker; the generalized-LI paper consuming it, and carrying the live-world lift,
the recovery theorem, and whatever Coverage turns out to be.

## 9. The eight sentences

1. **The generalized semantic object replacing deduction** is a time-indexed
   credal constraint `C_t ⊆ Δ(Ω_t)` — a restriction on distributions over worlds,
   primitive rather than derived from anything in price space.
2. **The live worlds** are those some admissible credence gives positive mass:
   `Ω_t^live = { ω : ∃ μ ∈ C_t, μ(ω) > 0 }`. Liveness is `θ_t(ω) > 0` for the
   support capacity `θ_t(ω) = max{ μ(ω) : μ ∈ C_t }`.
3. **What finite prices show of it** is the projection `K_t = π_t(C_t)`, the
   priced marginals admissible credences induce — and nothing more.
4. **Why prices cannot reconstruct the semantics**: `π_t` is not injective on
   credal sets. `Δ({00,11})` and its fibre saturation share a projection and have
   different live worlds, and separating the individual worlds does not help
   because separating points is not separating mixtures.
   `SEMANTIC_PROJECTION.md` §2.
5. **Traderized force enforces the projection.** The compiled position makes
   prices outside `K_t` carry positive cube-maximum gain, so the market maker
   cannot display them beyond a declared tolerance `δ_t`, at intensity
   `(ε_t + M_t)/δ_t²`.
6. **The preservation theorem**: if the enforcement position's cumulative value
   over the live worlds is bounded below by `−B`, no efficiently computable trader
   exploits the modified market, and every such trader's assessed net worth is at
   most `1 + B`.
7. **Ordinary deduction instantiates both channels.** Semantically,
   `C_t^D = Δ(PC(D_t))` gives `Ω_t^live = PC(D_t)` in both directions with no
   hypothesis on `π_t`, so the criterion specializes to `LIC_D`. In force,
   `K_t^D = π_t(C_t^D)` is the finite coherence polytope, and enforcing it costs
   nothing in its own live worlds.
8. **The interface that remains open** is the arrow into the mechanism: whether a
   normative practice yields a semantic constraint `C_t` (strong form) or only a
   price demand `K_t` (weak form, giving force without semantics). Item 39.

All eight are precise. Two questions behind them are open and are ordinary: the
necessity of either liability bridge (item 45), and what governs a source setting
a world's support capacity to zero (item 44).

## 10. Paper viability

**Core generalized-Logical-Induction paper: available conditional on one named
theorem.** The theorem is the live-world TradingFirm lift — the claim that the
source construction runs over any nested, effectively presented, nonempty
live-world process. It is read off `lem:budgeter`.1–3 and `lem:tfdom` rather than
proved here, and it is the step that makes the generalized criterion a theorem
rather than an analogy.

**Minimum viable spine**, in dependency order: semantic state and support-live
worlds; the projection obstruction; the lift; deductive recovery and criterion
recovery; the compiler and the conformance theorem; bounded-liability
preservation; and the two routes to bounding liability. Nine of those are derived
or proved and one — the lift — is the conditional.

**The stronger spine** adds the normative-static instantiation, which is item 39
and is properly a downstream application. **It should not be treated as blocking**:
a paper whose deductive instantiation is exact and whose normative instantiation
is an open interface is a complete paper with a stated application boundary.

**Not available** would require a load-bearing step to be only an analogy. The
lift is the one candidate, and formalizing it is the single highest-value next
piece of work.
