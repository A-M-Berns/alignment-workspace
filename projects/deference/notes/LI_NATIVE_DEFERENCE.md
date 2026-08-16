# LI-native deference — Stage V interface and boundary

Human register: [Deference wiki](https://github.com/A-M-Berns/alignment-workspace/wiki/Deference).

**Status:** `ci-only`; verification register for
`prompts/2026-08-11-stage-v-li-native/`. Names introduced here are provisional.
All FAF references are to the pinned commit
`1fffea44eece253cda1722568a3adfe34e822f03`.

## 1. Actual FAF substrate

| question | pinned declaration |
|---|---|
| market | `LogicalInduction.History := ℕ → Sentence → ℝ`, `Framework/Foundations.lean:45`; exact-rational computability is `ComputableMarket`, `Framework/Criterion.lean:1041` |
| operational quotes | `MarketComputation`, with `quote`, code, exactness and code specification, `Criterion.lean:1051` |
| strategy | `Strategy n`, a finite list of `(EF × Sentence)` trades with coefficient rank at most `n`, `Criterion.lean:1385` |
| trader | `Trader.strat : (n : ℕ) → Strategy n`, `Criterion.lean:1428` |
| wealth | `Trader.netWorth`, the cumulative sum of actual strategy values, `Criterion.lean:1436` |
| exploitation | bounded-below and not bounded-above `plausibleAssessments`, `Criterion.lean:1441` |
| criterion | `IsLogicalInductor.marketComputable`, `.processComputable`, and `.noExploit`, `Criterion.lean:1748` |
| constructed inductor | `LIA_is_logical_inductor`, `Construction/LIACompiler.lean:7301` |

`EF` is the quote-responsive coefficient language: rational constants, sentence
prices, addition, multiplication, maximum, safe reciprocal and sharing
(`Criterion.lean:43`). `EF.denote` evaluates against a history
(`Criterion.lean:73`), `EF.rank` records the latest price day read
(`Criterion.lean:164`), and `EF.continuous_denote` proves continuity
(`Criterion.lean:215`). A day-`n` strategy may read prices through day `n`; it
cannot read `P (f n)` when `n < f n`. A discontinuous hard gate is not an EF.

`EfficientlyComputable` is not an informal polynomial-time label. It requires
programs emitting the digit stream of the serialized RPN strategy under a
polynomial fuel clock (`Criterion.lean:1730`). `ComputableMarket` requires total
partial-recursive exact quotes but no polynomial runtime (`Criterion.lean:1034`).
Therefore another market's computability does not by itself make its quote
sequence legal as a trader coefficient.

## 2. Criterion to forcing: what now closes

`Workspace.Deference.Contrib.MagnitudePrediction.unitTrader` buys one share of
the day-`n` grade contract. `unitTrader_netWorth_eq` proves its actual FAF net
worth is exactly the cumulative signed error. Stage V adds:

- `unitTrader_ec`: `RpnSentenceCodes φ` constructs the actual FAF
  `EfficientlyComputable` certificate using
  `EfficientlyComputable.ofSingleTradeBlocks`
  (`Framework/RpnEmission.lean:293`);
- `signed_bddAbove_of_bddBelow_rpn`: bounded downside plus
  `IsLogicalInductor.noExploit` yields bounded upside, with no named trader-
  admissibility hypothesis;
- `topSequence_rpn`, `top_unitTrader_bddBelow`, and `top_signed_bddAbove`: a
  concrete hypothesis-package witness using tautology contracts.

This is the complete honest chain

```text
RpnSentenceCodes
  → actual EfficientlyComputable Trader
  → actual FAF net worth equals signed error
  → IsLogicalInductor.noExploit
  → bounded-downside signed assessments have bounded upside.
```

The criterion does not supply bounded downside for every buy-one-each-day
sequence. The theorem keeps that premise. It forces a Dutch-book boundedness
statement, not pointwise or magnitude convergence.

## 3. Faithful acceleration: exact residue

`FaithfulAcceleration.accelTrader` already is an actual FAF `Trader`.
`accelTrader_netWorth_eq` and `netWorth_sub_banked_abs_le` use actual FAF net
worth and isolate a bounded open position. `weight_not_divergent` constructs both
halves of `Trader.Exploits` and invokes `IsLogicalInductor.noExploit`. Its EF rank,
expressibility and one-day resale accounting are discharged.

Three inputs remain:

1. `hEC`. The arbitrary exogenous rational sequence `a` is embedded in trader
   syntax without a polynomial emission certificate. FAF's splice/emission
   combinators can replace this opaque premise by an explicit `PolyRatCodes`-like
   input, but `a` being another logical inductor's prices does not discharge it:
   market quote computation has no polynomial bound.
2. `hbias`. This relates one process's current prices to another process's later
   prices. FAF is a single-history framework and supplies no cross-market
   calibration theorem.
3. `hworld`. It is not implied by generic `IsLogicalInductor`; FAF admits an
   inductor over an eventually inconsistent process (`Framework/Affine.lean:210`).
   It is discharged for the concrete arithmetic process by
   `theoremDP_hworld` (`Construction/Witnesses/ComputationDP.lean:249`).

The current theorem uses `P (n+1) φ` only when the held position is resold. The
day-`n` strategy does not inspect that quote, so it is legal. This is not a
future-price security. General lookahead additionally needs bounded concurrent
support/exposure.

Item 7 is therefore partially closed: actual market, strategy, wealth and LIC
application exist, and one signed forcing chain is now hypothesis-complete at the
admissibility layer. Cross-process faithful acceleration remains interface and
assumption debt.

## 4. Computational futurity in FAF

`DeferralFunction` supplies `n < f n` and a program computing `f` with fuel
polynomial in `f n`, not in `n` (`Properties/SelfTrust.lean:37`). A present EF
cannot inspect a future quote. A sentence can name it:

- `RationalQuoteCode.ofComputable` turns a total computable bounded rational
  sequence into a threshold-sentence LUV (`Witnesses/QuoteCodeOfMarket.lean:150`);
- `theoremFutureQuoteCode` names `P (f n) (φ n)` for the constructed arithmetic
  LIA without evaluating that rational during sentence emission
  (`QuoteCodeOfMarket.lean:785`);
- `lic_no_expected_net_update_closed` proves the present price is asymptotically
  its present expectation of that quoted later price (`QuoteCodeOfMarket.lean:797`).

This is a real temporal logical object absent from the finite kernel: a compact
present sentence about a later exact market computation. It is not yet a theorem
of bounded computational non-possession. Future quotes are total computable, FAF
has no resource-indexed `Agent` state, and no declaration proves that the day-`n`
process has not or cannot evaluate the later quote. Thus

```text
present describability ≠ present bounded computability
```

is supported by the code architecture but not formalized as a separation theorem.

## 5. Smallest future recommendation object

For two efficiently named proposal-score sentences `φ₀(n), φ₁(n)`, the total
computable Boolean

```text
C(n) := [P (f n) (φ₁ n) > P (f n) (φ₀ n)]
```

can be named by `BooleanQuoteCode.ofComputable`
(`Construction/Witnesses/QuotationAffine.lean:223`). Its `.sentence` is present
syntax, `.sentence_poly` is efficiently emitted, and `.reflected` connects
completed-theory worlds to the computation (`QuotationAffine.lean:196`). Hard
comparison is legal inside the quoted computation; it would be illegal as a
discontinuous price-responsive EF coefficient.

A continuous alternative is the bounded rational mixture weight

```text
q₁(n) := (1 + s₁(n)) / (2 + s₀(n) + s₁(n)),
```

where `sᵢ(n)` is the exact future quote. `RationalQuoteCode.ofComputable` can name
it. This is a quoted future recommendation fact or scalar, not an FAF decision
agent: FAF has no proposal, policy, randomization, sampling or execution type.

Fallibility survives because neither construction relates scores to a target
quantity. For example, if an external evaluator assigns utility `1` to proposal
zero and `0` to proposal one, `q₁ > 0` always assigns positive probability to a
suboptimal proposal. The Boolean rule can likewise select a proposal the evaluator
ranks lower. No correctness is definitional.

`A_n` can honestly mean the day-`n` market state `P n`. `A_{f(n)}` can mean the
same market process at the later index `P (f n)`. Current `A` can name statements
about the later state without placing that later quote in a day-`n` EF. What FAF
does not establish is that current `A` lacks the resources to compute the quoted
result already.

## 6. Expectations and self-trust interface

`LUV` is a family of threshold sentences, not a decision variable
(`Framework/Expectations.lean:54`). `LUV.expect` is a finite sum of threshold
prices (`Expectations.lean:114`). Generic future-price and self-trust theorems use
explicit representation objects `FuturePriceQuote`,
`ExpectedFutureExpectationQuote`, and `SelfTrustQuote`
(`Properties/SelfTrust.lean:120,109,164`). The criterion-derived endpoints are
`lic_expected_future_expectations`, `lic_no_expected_net_update`, and
`lic_self_trust` (`SelfTrust.lean:323,338,377`). Closed versions over the
constructed arithmetic LIA include `lic_self_trust_closed`
(`QuoteCodeOfMarket.lean:967`).

These are asymptotic, fuzzy price/expectation relations. They contain no action,
authorization, capability, or controller field.

## 7. Future H⁺ as computation

A total computable Boolean output `h(f(n))` can be named with
`BooleanQuoteCode.ofComputable`; a bounded rational report can be named with
`RationalQuoteCode.ofComputable`. The sentence can be emitted without executing
the reported computation, and the quotation presentation supplies eventual
logical settlement. This yields prediction of a report.

It does not by itself yield trust in the report, advice quality, calibration to
an external target, or a rule for using it. Provability induction handles
systematically provable/refutable sequences; an arbitrary slow mixed output does
not become timely predictable merely because it eventually settles. A report
that queries its own price introduces self-reference and needs FAF's specialized
fixed-point machinery or a new totality certificate.

FAF has one stronger conditional bridge. `FeedbackTruthComputation`
(`Construction/Witnesses/FeedbackTruth.lean:30`) certifies that a rational truth
computation finishes by the next deferral deadline.
`lic_wub_ofComputation_unconditional`
(`Construction/Witnesses/FeedbackUnconditional.lean:42`) then gives weighted
signed-bias convergence for current prices against that completed-theory truth
stream, assuming the sentence, weighting, deferral and support certificates. A
quoted future H⁺ output can instantiate the truth stream when its computation has
the deadline certificate. This is signed unbiasedness, not pointwise or magnitude
accuracy, report reliability, advice correctness or jurisdiction. FAF's displayed
inhabitation of this deadline interface is a constant-output case; a nonconstant
H⁺ witness remains formalization work.

No language extension is needed merely to name a fixed computable H⁺ output. A
typed report-content/reliability link is needed to turn prediction into advice.

## 8. Item 28's conditional core and the jurisdiction boundary

`StaticViewFactorization.FactorsThroughStaticView` states that a value
functional factors through selected price and realization projections.
`value_eq_of_price_realization_eq` proves it is constant on each equal-view fiber.
The theorem is fully polymorphic: finiteness, probability and arithmetic are not
needed. `staticView_eq` separately proves literal identity when the entire
architecture type is exactly the pair.

The worked case carries jurisdiction in the architecture type. Two instances
have equal price and realization and different jurisdiction. A static value
agrees; a jurisdiction-reading value differs and is proved not to factor through
the static view.

What the theorem rules out: any value that explicitly factors only through the
selected `(P,r)` cannot distinguish different hidden authorization, capability,
transition or provenance payloads on the same fiber.

What it does not rule out: a jurisdiction-sensitive value; an additional
authorization, capability, continuation or transition input; encoding such facts
inside `P` or `r`; different prices or realizations; approximate conclusions when
the projections are merely close; or any claim that jurisdiction is good or bad.
The result is exact and syntactic about the chosen projections.

The representation consequence is the result: authorization must enter before
the valuation's factorization boundary. Adding a number downstream of the same
realization does not do that.

## 9. Foreclosure and trader visibility

FAF contains no authorization, capability state or transition relation. Encoding
“future correction remains available” as a sentence lets an inductor price that
logical fact if settlement and efficient syntax are supplied. It does not preserve
the capability, value it, or make its removal exploitable.

There is no legal trader corresponding to bad preemption merely because it is
preemption. A controller can remove correction exactly as anticipated, with the
capability sentence correctly priced; all FAF wealth paths remain coherent. An
exploit requires an added security connecting execution histories to payouts and
a systematic pricing gap. The gap, not preemption, supplies the arbitrage.
