# Can the motivating normative statics discharge safety?

Not "can some region be enforced safely" — can *these* statics, the settlement and
core construction already in the normativity line, satisfy the
bounded-enforcement-liability hypothesis that preserves nonexploitability.

Exactness is not the question. The market maker's own finite-time contract carries
slack, ordinary coherence is not exact at finite dates either, and the application
wants `g_{t,j}(P_t) ≤ δ_t` with a declared schedule. What the application must not
do is destroy the no-exploitation guarantee.

**Verdict: 2 — one natural additional clause is needed, and it already exists in
the corpus in another context.**

## 0. The chain, arrow by arrow

Every arrow the application rests on, with what actually establishes it. Nothing
below is stronger than the weakest arrow in the path that uses it.

| # | arrow | evidence |
|---|---|---|
| A1 | market-maker contract + force declaration ⟹ `Σ_j β_j g_j(P_t)² ≤ ε_t + M_t`, hence `g_j(P_t) ≤ δ_t` | **lean-proved** — `TraderizedEnforcement.weighted_square_le_slack_add_volume` |
| A2 | the compiled position is a legal day-`t` `Strategy n` | **derived** — exhibited in the source's feature grammar, not written as a term |
| A3 | liability identity: `L_t(ω) ≤ Σ_j β_{t,j} g_j(P_t) d_j(ω)` | **lean-proved** — `weighted_square_sub_deficit_le_pair` |
| A4 | substituting the promise and the intensity: `L_t(ω) ≤ (ε_t + M_t)·‖d_t(ω)‖₁ / δ_t` | **derived** from A1 and A3 |
| **A5** | **outflow protocol with capital `B` ⟹ `Σ_t q_t ≤ B` ⟹ `Σ_{t≤n} E_t(ω) ≥ −B` for all `n` and all `ω ∈ Ω_n^live`**, with `q_t = (ε_t + M_t)·D_t/δ_t` and `D_t = sup_{ω ∈ Ω_t^live} Σ_j d_{t,j}(ω)` | **derived** — §7–8, §13a |
| **A5′** | **the `D_t` that was certified is the `D_t` of the position that was emitted** | **derived** — §7a; enforced by construction in `compile_safe_force`, and by a binding check in the lower-level path |
| A6 | `B < ∞` ⟹ no efficiently computable trader exploits the modified market, and assessed net worth is at most `1 + B` | **derived**, conditional on A7 |
| A7 | the generalized live-world Budgeter/TradingFirm lift | **derived and unformalized** — the paper's only conditional, `PAPER_RECONCILIATION.md` |
| A8 | settlement rows contribute zero deficit; core rows carry `max(0, r − m_c)`, independent of `θ` | **derived** — §1–2 |
| A9 | settlement monotonicity makes the depth non-increasing for a fixed endorsement under irreversible settlement | **derived** — `NL-SI-C4`; **helpful, and neither necessary nor sufficient**. Not sufficient because non-increasing is not summable; not necessary because the cost product can be summable while the depth rises on some dates, so long as pressure or tolerance compensate |

**Where the new arrow sits.** A5 is the arrow this pass adds, and it enters
*before* bounded liability rather than restating it. Its inputs — `ε_t` from the
market, `M_t` a declared volume bound, `δ_t` the tolerance about to be promised,
`d_t` from the semantic/settlement state — are all available at or before the
moment force is emitted, which is what makes it a protocol rather than a
hypothesis. Its output is exactly A6's hypothesis.

**The one inexactness in A5**, stated rather than buried: `Σ_t charge_t ≤ B` is
*strictly stronger* than the criterion needs. The criterion picks one world at
horizon `n` and follows it; the charge maximizes over live worlds independently
at each date. So a diverging certificate establishes only that this route does not
certify safety — §4's contrast additionally exhibits realized divergence at a
followed world, which is the stronger statement and is what makes it a genuine
failure rather than a proof gap.

**What the chain does not contain.** Any claim that bounded liability is
*necessary* (`PRIORITIES.md` item 40), any exhibited exploiting trader for the
failing fixture, and any unconditional statement — every path through A6 inherits
A7's conditionality.

## 1. The motivating region, and its two families

At date `t`: a post-settlement simplex, an endorsed region inside it, a declared
core minimum `θ_min`, and `NL-SI-A2`'s admissible-reference polytope compiled to
price-space rows by `CORE_CONDITION.md`. The resulting `K_t^norm` has rows from
two sources, and they behave differently.

**Settlement / coherence rows.** Right-hand sides are minima over the assessed
worlds, so every assessed world satisfies every one of them. Their exclusion
deficit is **identically zero**, and by the kernel-checked nonnegativity reading
they contribute nothing to enforcement liability — ever, at any intensity.
Checked at three stages in `test_normative`.

**Core / endorsement rows.** These are useful precisely when they exclude a credal
state the settled record still permits, and they carry all the liability.

There is no third source in the motivating statics.

## 2. What a core row's deficit actually is

For an endorsement `⟪c, q⟫ ≥ r` with `c` indexed by worlds, write
`m_c = min_ω c_ω` — the least any assessed world delivers. `NL-SI-A2`'s row is
`(1−θ)⟪c,q⟫ ≥ r − θ·m_c`, and its worst deficit over assessed worlds is

    d = max(0, r − m_c) ,

attained at a world achieving the minimum. **It does not depend on `θ`.** The core
minimum sets how deep the reference must sit inside the endorsed region; it does
not change how far the endorsement outruns what the worlds deliver. Verified at
three values of `θ`.

So the liability is governed by one quantity per endorsement: **how far the
book's demand exceeds the worst still-assessed world**.

## 3. What the existing statics already give

Settlement is monotone (`NL-SI-C4`) and never reopened (`NL-SI-P1`), so the
assessed worlds shrink and `m_c` is **non-decreasing**. Hence `d` is
**non-increasing** along any settlement trajectory: `1/2, 1/2, 0` on the displayed
instance, reaching zero exactly when the record entails the endorsement.

Finite gating (`P3`) bounds how many rows are live per date, hence the length of
the deficit vector.

**That is monotonicity and a bounded row count. It is not summability**, and the
declared-quantity ceiling `(ε_t + M_t)·D_t/δ_t` has `M_t` — a bound on
cumulative ordinary trading volume — growing in the numerator.

## 4. Two trajectories

**Safe.** The endorsement is vindicated by settlement after two dates; the deficit
is `1/2, 1/2, 0, 0, …`. Cumulative bound `135/8`, and **identical at horizons 4, 8
and 12** — finitely many dates carry any deficit at all, so `B < ∞` is discharged
outright.

**Unsafe.** Minimally altered: nothing ever settles, the deficit stays `1/2`, and
`M_t = t`. Cumulative bound `52.3 → 182.5 → 392.5` at the same horizons, growing
quadratically. And it is not only the bound: the compiled position is short the
endorsement's direction at a world the record still permits, so the loss is real.

Both are exact-rational and run in `test_normative`.

## 5. The type comparison the addendum asks for

The one candidate with the right shape is the settlement interface's `P2`.

```text
P2 downside limit
  bearer:      the engine
  quantifiers: worldwise, against the book's holdings
  trajectory:  a guarantee at each date, with declared means
  what it bounds: the engine's loss on the book's positions
  declared means: refusal, or bounded aggregate participant budgets

enforcement liability
  bearer:      the enforcement trader
  quantifiers: every date n, every world in Omega_n^live, cumulative to n
  trajectory:  uniform over the whole horizon
  what it bounds: omega( sum_{t<=n} E_t ), the compiled position's own value
  declared means: none — the trader is exempt from budget caps by construction
```

The **quantifier structure matches exactly**: worldwise, cumulative, uniform in
horizon. What differs is the bearer, the holdings, and — decisively — the declared
means. `P2`'s two means are refusal and bounded aggregate participant budgets, and
the enforcement trader is exempt from both: unit weight and no budget cap are its
defining privileges (`SOURCE_AUDIT.md` §7). **So `P2` as written does not cover
it**, and identifying them by shape alone would be exactly the vocabulary error
the round has been avoiding.

## 6. Per-endorsement caps do not aggregate

The first thing to try is the modular clause: each endorsement declares a finite
bound on the cumulative outflow of its own compiled position. It fails, and the
failure is not subtle.

Let endorsement `e` be live at date `e` alone, with exclusion deficit `1`, at
tolerance `1/2` against `ε + M = 1`. Its whole-lifetime outflow is `2`, finite.
Exactly one row is live at every date, so finite gating is obeyed everywhere. And
the aggregate certificate after `n` dates is exactly `2n`.

    for all e, B_e < ∞     does not give     Σ_e B_e < ∞ ,

and a source can walk that gap forever by retiring each endorsement as it admits
the next. `test_outflow.PerEndorsementCapsDoNotAggregate`.

**Finite gating does not close it.** Gating bounds how many rows are live *per
date*; nothing in it bounds the number of dates. A clause citing gating for
lifetime safety claims more than gating gives, and
`test_outflow.GatingIsNotALifetimeBound` is the named regression.

So the account must be **global over the enforcement channel**, or decomposed
into an allocation that is *summable* rather than merely finite termwise.

## 7. The account

`src/outflow.py`. Finite lifetime capital `B`, spent down as force is emitted.

**The charge.** A date's force costs `(ε_t + M_t)·D_t / δ_t` — the
declared-quantity liability ceiling, renamed. That rename is the move: a quantity
the safety analysis could previously only report after the fact becomes a price
paid in advance. It uses no realized price, so §6's timing question answers
cleanly — the charge is computable *before* the trade is emitted, from the
market's slack, a declared volume bound, the tolerance the mechanism is about to
promise, and the deficit vector the semantic/settlement state supplies.

**Caps, not reserves.** `cap` promises capital to an endorsement against global
capital and refuses when it is short, and `spend` enforces `spent_e ≤ B_e`. Both
`Σ_e B_e ≤ B` and the per-endorsement bound hold, which is everything the safety
theorem needs, and §6's counterexample dies at the fourth admission rather than
running forever. It is deliberately **not** ring-fencing: capital promised to an
endorsement and not yet spent remains available to unallocated charges. The word
is *cap* because the behaviour is a cap, and true reservation would be a stricter
discipline nothing here requires.

**Additivity.** The certificate is exactly additive over rows and identically
zero on settlement rows, so per-endorsement charging is well defined. It is
*conservative*: realized liability of a sum can be smaller than the sum of
component liabilities, because positions cancel in price space.

## 7a. The certificate binds to the request, or it certifies nothing

A charge is only a safety quantity if the thing whose deficit was certified is the
thing whose trader is emitted. It was not, and the gap was exploitable rather than
theoretical.

**The substitution.** Take `K_easy = {p ≥ 0}`, which nothing in the cube can
violate, so its live-world aggregate is honestly `0` and a `verified` certificate
says so. Hand that certificate to the funded entry point while asking it to
enforce `K_hard = {p ≥ ½}`. The account is charged **nothing**, the position is
emitted anyway, and at the live world `p = 0` against a contract-satisfying price
of `1/4` it really loses. Repeat and the cumulative liability diverges while the
holder quotes a finite `B`.

**What a certificate now carries.** Four identities, because the proposition
mentions all four:

| bound | why it is operative |
|---|---|
| exact **row presentation** | the round chose Option A; duplicates and order change the emitted position |
| exact **support** | `(0,1,0)` means nothing without which sentence sits where |
| exact **date** | the live set shrinks, so a later certificate is cheaper and must not fund earlier force |
| exact **live-world set** | two assessment processes can disagree at one date; at one date, support and presentation, the narrow set `{A=1}` has aggregate `0` where the wide `{A=0,A=1}` has `1/2` |

Neither the enumeration order of the live worlds nor the order of the rows is
operative, and both are sorted out of the key. Row permutation is *derived*
invariant: the compiled position `Σ_j β_j g_j(P)·c_j` and the certified aggregate
`sup_ω Σ_j d_j(ω)` are both sums over rows at a uniform intensity, so a
permutation permutes summands. Row **multiplicity** is a different matter and is
kept, since `k` copies scale position and charge by `k`. So the presentation
identity is the **multiset of exact rational rows** — not the polytope `K`, not a
duplicate-free set, and not a class under redundancy or rescaling.

**Three structural consequences.**

1. `LiveDeficitCertificate` is constructed only by `by_enumeration`; the
   initializer requires a module-private witness, so the verified state cannot be
   filled in by a caller.
2. A bound a caller asserts is a **`LiveDeficitClaim`** — a different type, not a
   flag. It can price a request and cannot certify one. A reason string is not a
   proof and the type no longer pretends it is.
3. `compile_safe_force` computes the certificate from the **same `Region`
   instance** it is about to enforce, so there is no separate object to mismatch.
   The lower-level `compile_funded_force` accepts a certificate and checks
   `binds` on all four identities, reporting which field differs. It takes the
   live worlds precisely so it *can* check the fourth — an earlier version
   checked three and left the assessment state free, which was the substitution
   above with the region held fixed.

## 7b. What `compile_safe_force` does not certify

The boundary is worth stating plainly, because the phrase *safety-certified* can
be read as more than it is.

    supplied live worlds L_t   ⟹   safe **relative to** L_t .

That is the force layer's business and the whole of it. What it does **not**
establish is that the supplied `L_t` are the live worlds of the intended semantic
process — that the normative record really yields `C_t`, and that `C_t` really has
support `L_t`. That arrow is `PRIORITIES.md` item 39 and no code here touches it.

So: **`compile_safe_force` closes certificate substitution inside the force layer.
It does not authenticate the normative semantics supplied to it.** A caller
feeding it the wrong assessment state gets a sound certificate about the wrong
question, and nothing in this round can detect that.

## 8. Safety theorem

    account discipline  ⟹  Σ_t charge_t ≤ B  ⟹  for all n, ω ∈ Ω_n^live,
                                                 Σ_{t≤n} E_t(ω) ≥ −B .

The second arrow needs care about the quantifier. The criterion picks a world at
horizon `n` and follows it back; the certificate maximizes over live worlds
*independently at each date*. The certificate is therefore a **strictly stronger
sufficient condition** than the criterion needs, not a restatement of it —
`charge_is_conservative` checks the domination on a trajectory, and
`test_outflow.ChargeIsAdditiveOverRowsAndConservativeOverWorlds` exhibits the gap
rather than hiding it. This is the price of a certificate computable in advance.

Conditional on the live-world Budgeter/TradingFirm lift, `B < ∞` then gives
nonexploitability with assessed net worth at most `1 + B`.

## 9. What force costs, and the three ways it stays affordable

The charge is a product of three factors and the condition is that the product be
summable:

    q_t = (ε_t + M_t)·D_t / δ_t ,        Σ_t q_t < ∞ .

Ordinary aggregate pressure, normative exclusion depth, tolerated error. **No one
of them is privileged.** Indefinite force stays affordable if the depth decays, or
if the pressure decays, or if the tolerance loosens, or any combination.

Inverting against a per-date allowance `b_t` gives the affordability relation

    δ_t ≥ (ε_t + M_t)·D_t / b_t ,

which is one reading of the same equation: the remaining account determines how
tightly the reasoner may be forced, given the other two factors.

**A withdrawn theorem.** A previous version of this note claimed that a date whose
promise says anything costs at least `D_t`, and so that persistent positive depth
exhausted any finite account. The step is wrong: `δ_t ≤ 1` gives only
`q_t ≥ (ε_t + M_t)·D_t`, and the dropped factor is not bounded below.
`test_outflow.DepthOnlyImpossibilityIsWithdrawn` carries the counterexample —
`D_t = 1/2` and `δ_t = 1` forever against `ε_t + M_t = 2^-t` sums to under `1`, so
the normative distance never closes at all and force is affordable forever.
`meaningful_dates_are_finite` now raises rather than answering.

**The corrected limitative theorem** needs floors on two factors and a ceiling on
the third:

    D_t ≥ d > 0,  ε_t + M_t ≥ c > 0,  δ_t ≤ δ̄   ⟹   q_t ≥ cd/δ̄ > 0 ,

so finitely many such dates fit in finite capital — at most `B·δ̄/(cd)`. All three
hypotheses are load-bearing and `positive_floor_dates` refuses to run without
them. What it does **not** say is that any factor must decay; it says that if none
of them moves, the account runs out.

**Two witnesses, and they are different objects.** The abstract one stipulates
`D_t = 2^-t` against volume `t+1` at fixed tolerance `1/2`, total under `17/2` —
that shows the *mechanism* admits indefinite nonvacuous force. Whether the
motivating *statics* generate such a trajectory is a separate question, and §9a
answers it.

## 9a. Do the motivating statics generate one?

**Not from sentence-indicator endorsements.** `P(A) ≥ r` has world coefficients in
`{0,1}`, so its worst live delivery is `0` while any `A = 0` world survives and `1`
once none does. The depth holds at `r` and drops to zero in a single step; there is
no gradual closure available from this shape.
`test_normative.BooleanEndorsementsJumpToZero`.

**Yes from affine ones.** Take a priceable affine functional of priced sentences
whose demand sits at exactly the value the settled record *approaches*: settlement
establishes `A_1, A_2, …` in turn, each raising the worst surviving delivery
halfway to `r`, while the growing fragment keeps a world below it alive. Then the
endorsement is never vindicated at any date, a positive core minimum is admissible
at every date (`θ_max` rises from `63/127`), the depth halves from `1/4`, and the
cumulative charge converges.
`test_normative.StaticsGenerateAForeverUnvindicatedTrajectory`.

So the statics do produce forever-unresolved-but-affordable normative force — but
the endorsement has to be an affine demand rather than a sentence, which is a
substantive constraint on what kind of normative content this covers.

## 10. What happens at exhaustion, and what does not help

**Quarantine** withholds force and spends nothing; the endorsement keeps its
normative standing and loses operative effect. **Relaxation** buys the tightest
affordable promise. **Refusal at admission** is `cap` failing. **Tolling**,
if force is withheld for account reasons, is the behaviour that fits the existing
answerability architecture — a deadline should not count a failure the substrate
caused — and it is a constitutional choice, recorded as one and not made here.

**Weakening the core minimum does not help.** The worst deficit is
`max(0, r − m_c)`, in which `θ` does not appear. Lowering the declared core
minimum weakens the demand on the reference and leaves the charge exactly where
it was. A protocol answering exhaustion by weakening the core has paid nothing —
`test_outflow.ExhaustionBehaviour.test_weakening_the_core_minimum_does_not_reduce_the_charge`.

## 11. Presentation

The account bills a row presentation, and presentations of the same admissible set
are not interchangeable. A previous version of this note claimed they were. It
tested a compiler retuned for the occasion — dividing the intensity by the row
count — where the installed `ForceDeclaration` uses a uniform
`β_j = (ε + M)/δ²` for every row, so the retuning *was* the result.

**What the installed compiler actually does**, at a fixed declared tolerance:

| operation | position | realized liability | charge |
|---|---|---|---|
| `k` duplicate rows | `× k` | `× k` | `× k` |
| rescaling by `λ` | `× λ²` | `× λ²` | `× λ²` |
| one redundant non-duplicate row | `× 3` on the displayed instance | changes | changes |

**What survives.** Rescaling is a genuine reparametrization: a row scaled by `λ`
measures its violation in units `λ` times finer, so declaring `λ·η` asks for the
same actual conformance `η`, and at matched targets the position, the realized
liability and the charge all agree. A source gains nothing by rescaling.

**What does not.** Duplication is redundancy and it is billed. Even at matched
actual conformance — available only at square `k`, since `k` copies give
`δ/√k` — the position and realized liability agree while the charge does not,
because the certificate sums the same deficit once per copy. And redundancy is
general: `p_A ≥ ½` and `p_B ≥ ½` already imply `p_A + p_B ≥ 1`, and adding the
implied row leaves the admissible set exactly where it was and triples the emitted
position.

**So the answer to "is safety cost a property of `K_t` or of how it is asked
for?"** is: of how it is asked for. The round takes **Option A** — the
presentation is part of the force request, `(K_t, presentation)` is what force
consumes — with one normalization result on top: scalar rescaling need not be
normalized because the compiler already handles it. Duplicate and redundant rows
are *not* normalized, and a constitutional layer wanting presentation-independent
cost must either deduplicate, weight, or minimize over presentations. That is
`PRIORITIES.md` item 46 and is deliberately not decided here.

## 12. Where the clause belongs

The corpus already adopted this discipline for the same failure. `NL-SI-P1`'s
proof describes the structure it refutes —

> a false exposed constraint survives arbitrarily many tests when an outside
> source replenishes every paid loss and only current locks are tracked

— and records the repair as *"a limit on cumulative net outflow, not a
re-litigation of what was settled."* An externally funded enforcement trader
propping up an endorsement the record never vindicates **is** an outside source
replenishing every paid loss while only current positions are tracked.

**Not a rename of `P2`.** `P2` bounds the engine's downside on book holdings; its
declared means are refusal and bounded participant budgets, and the enforcement
trader is exempt from both by construction. The quantifier structure matches
exactly — worldwise, cumulative, uniform in horizon — but the bearer, holdings
and means do not. The correct move is a **sibling clause under a shared
principle**, not a broadening of `P2`:

> Every privileged channel that can impose losses unavailable to ordinary bounded
> participants carries a finite cumulative downside account.

That covers `P2` and traderized force as two instances with different bearers.
Whether to state the shared principle, or only the sibling, is reserved.

**Replenishment is the load-bearing detail.** If an outside source may top the
account up without limit, the guarantee is gone — that is exactly the failure
`NL-SI-P1` names. Replenishment must be bounded globally, or admitted only under
a new constitutional era with its own finite allocation. This is the one place
where a plausible-looking implementation choice silently destroys the theorem.

**Source-owned or market-owned.** Source-owned budgeting makes an endorsement's
persistence its author's responsibility and fits answerability; market-owned
allowance makes safety architectural and independent of who authored the
constraint. The theorem is indifferent — it needs only that the total be finite.
The choice is constitutional and is reserved.

## 13. Two sufficient trajectory conditions, neither necessary

**Deficit route.** `Σ_t (ε_t + M_t)·‖d_t(ω)‖₁ / δ_t < ∞`. Satisfied by the safe
fixture with finitely many nonzero terms, and by the forever-unvindicated fixture
with infinitely many. Nothing shows it necessary.

**Support route.** `Σ_t (1 − θ_t(ω))·U_t / θ_t(ω) < ∞`. The motivating statics
supply no lower bound on live-world support capacity and no summable bound on
`U_t`, so this route is **not** discharged by them; it remains available to a
source that supplies those quantities. Nothing shows it necessary either.

## 13a. Why the per-date charge gives the horizon quantifier

The one step worth writing out, since the certificate and the criterion quantify
differently.

**Proposition.** Let `q_t = sup_{ω ∈ Ω_t^live} L_t(ω)` where `L_t(ω)` is the
date-`t` liability ceiling of A4, and suppose `Σ_t q_t ≤ B`. Then for every
horizon `n` and every `ω ∈ Ω_n^live`, `Σ_{t≤n} E_t(ω) ≥ −B`.

*Proof.* Fix `n` and `ω ∈ Ω_n^live`. The live process is nested, so `ω ∈ Ω_t^live`
for every `t ≤ n`. Hence `L_t(ω) ≤ q_t` for each such `t`, by the definition of
`q_t` as a supremum over a set containing `ω`. Summing, and using
`E_t(ω) ≥ −L_t(ω)` from A3–A4, gives
`Σ_{t≤n} E_t(ω) ≥ −Σ_{t≤n} L_t(ω) ≥ −Σ_{t≤n} q_t ≥ −B`. ∎

Nesting is exactly what the proof consumes, and it is hypothesis `(L1)` of the
live-world lift — so this proposition is not an extra assumption, it reuses one
already made. The conservatism is visible in the second inequality: the criterion
follows one world, the certificate takes a supremum at each date independently,
and `charge_is_conservative` checks the domination on a trajectory.

**Which aggregate is billed.** `D_t` is the **sharp** `sup_ω Σ_j d_j(ω)`, not the
rowwise `Σ_j sup_ω d_j(ω)`. They differ: two rows pinning one price from opposite
sides are worst at opposite worlds and cannot be violated together at any world,
giving `1/2` against `1`. `LiveDeficitCertificate` computes both by enumeration
over the live worlds and bills the sharp one by default, because the rowwise one
overcharges and buys nothing.

## 13b. What counts as meaningful force

`δ_t ≤ 1` is **not** a presentation-independent notion, because scaling a row by
`λ` scales its violations by `λ`. The invariant statement is relative to the
largest violation the row can attain in the cube, `V_max = r − Σ_i min(c_i, 0)`:
force is nonvacuous when `δ_t ≤ α·V_max` for a declared `α < 1`. Every claim in
§9 about "meaningful" force is to be read at a fixed `α`, and the corrected
limitative theorem's tolerance ceiling `δ̄` is where that enters.

## 13c. The end-to-end proposition

Putting the binding and the horizon argument together, this is what a holder of a
`SafetyCertifiedForce` may assert.

**Proposition.** Let `F_t` be produced by `compile_safe_force` from an exact row
presentation `R_t` over support `S_t`, at date `t`, against live worlds `L_t`,
with declared `ε_t`, `M_t` and tolerance `δ_t`. Then the emitted position `E_t` is
the trader compiled from `R_t`, and

    for every ω ∈ L_t:   E_t(ω)  ≥  −(ε_t + M_t)·D_t/δ_t  =  −q_t ,

where `D_t = max_{ω ∈ L_t} Σ_j d_j(ω)` was computed by enumerating `L_t` against
`R_t` — the same presentation, the same support, the same date. That exact `q_t`
has been debited from an account whose total lifetime capital is at most `B`.

Hence, for a nested assessment process, `Σ_t q_t ≤ B` gives
`Σ_{t≤n} E_t(ω) ≥ −B` for every `n` and every `ω ∈ L_n`, by §13a. Conditional on
the generalized TradingFirm lift, nonexploitability follows.

The load-bearing word is **exact**, four times over. Before the binding, each of
those four could differ between the certified object and the emitted one.

## 13d. The motivating application, stated precisely

**Proposition.** The settlement/core statics admit priceable rational row
presentations that are feasible, and therefore compile through the traderized
force interface; the resulting force meets its declared finite-time tolerance.
For the displayed settlement trajectories the statics also generate live-world
deficit schedules whose full certified cost `Σ_t (ε_t + M_t)·D_t/δ_t` is finite.
Hence the installed outflow protocol yields bounded cumulative enforcement
liability, and therefore — conditional on the generalized live-world TradingFirm
lift — preserves nonexploitability.

**Two witnesses, and they are different in kind.**

*Eventual vindication is safe.* A sentence-shaped endorsement `P(A) ≥ ½`: the
depth holds at `½` while an `A = 0` world survives and drops to `0` when none
does. Force costs something, then costs nothing.

*Permanent unresolved force can also be safe.* The single global affine
endorsement `c = ½B + ¼C + Σ_j 2^-(j+2)A_j` at `r = ¾`, with
`m_t = ¾ − 2^-(t+2)` and `D_t = 2^-(t+2) > 0` at every finite `t`. Never
vindicated, positive core minimum throughout, and `Σ_t q_t = 9/8` exactly at the
displayed market parameters.

Both run end to end through `compile_safe_force`, with the certified `D_t` equal
to the closed form and the charge equal to `q_t`.

**What is not claimed.** That every trajectory of the statics is safe. The claim
is that **the statics admit natural trajectories satisfying the sufficient
condition** — and the round separately carries one that does not, whose realized
liability at a followed world diverges.

## 14. What is not established

**Presentation-independent cost.** The account bills a presentation, duplicate
and redundant rows cost more, and the round chose Option A — presentation is part
of the force request — rather than solving it. `PRIORITIES.md` item 46.

That the account is necessary (`PRIORITIES.md` item 40). That the deficit route is
the best available. That the charge is anywhere near tight — it is a worst-case
certificate over worlds, and how conservative it is has not been measured. That an
efficient trader exploits the bounded-liability-failing fixture: the realized
cumulative loss at a followed world diverges, which is a failure of the
hypothesis, and **not** an exhibited exploitation.

Whether a revisable normative practice keeps the depth non-increasing at all:
**it need not** — revision can raise `r` or reopen `m_c` — and revision is outside
the live-world lift's nesting hypothesis for the same reason.

And the whole chain is conditional on the live-world Budgeter/TradingFirm lift,
which is `derived` and unformalized.
