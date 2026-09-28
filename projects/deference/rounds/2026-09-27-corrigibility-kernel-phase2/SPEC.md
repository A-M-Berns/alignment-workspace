# The corrigibility kernel — specification, version 2

What corrigibility is, for an agent that acts on behalf of a person while she keeps
authority over some matters; what it takes to state it; what has been proved about it.
Each definition is stated first in plain language, then in mathematics.  Lean names appear
only in the final table.  Names: the objective is the **fidelity score**, the object it
is measured against is the **allocation of authority**; "constitutional" is reserved for
the allocation's floor and its amendment procedure.

## 0. The picture

```
interaction history ──► legitimacy + allocation of authority ──► fidelity score ──► the agent's choice
                               ▲                                                (a maximizer; learners in §6)
                     monitor / prices: shortfall, taint, provenance
                     (logical induction supplies the uncertain event prices)
```

**Three notions, kept distinct.**

- **Faithfulness** is a property of histories: nothing in the history violated the
  allocation of authority.
- **Corrigibility** is a property of the agent's preferences: it prefers every course of
  action it knows to be faithful over every course it knows to be unfaithful, whatever it
  believes about how things will turn out, and it accepts a *risk* of unfaithfulness only
  at a fixed exchange rate.  The fidelity score is the canonical objective with this
  property.  It is not the only one: any objective whose ordinary term is bounded in
  `[0, D′]` and which charges `ϖ′` per recognized violation, with `ϖ′ > D′` — and, where a
  band enters, `D′ − ϖ′` below the band's floor — has it too.  *Corrigible* names this
  property of preferences; *aligned* is the further condition that the ordinary term is
  her evaluation.  An agent can be corrigible without being aligned: the objective that
  rewards an uncounted manipulation is corrigible and prefers the manipulation.
- **Realized corrigibility** is what a corrigible agent actually does.  The theorems of §5
  say how much of the preference becomes behaviour for a plain maximizer of a corrigible
  objective; §6 says how much survives for a learner.

**Four separations.**

1. *Legitimacy is not corrigibility.*  Legitimacy says which apparent judgments of hers are
   really hers.  It is consumed at two places — inside the allocation (which exercises of
   her authority count) and at the score (which evaluations count) — and defined at
   neither.
2. *The allocation is not a utility function.*  It says who holds each matter, what the
   holder must remain able to do, at what cost and within what time, and what must be
   disclosed.  Effective realization says that control is real, not nominal.
3. *Faithfulness is a property of the history.*  The agent never causes or exploits a
   failure of effective realization, never changes the allocation without a license, and
   meets its duties.  Pre-emption, the one violation stated against a counterfactual
   response, is a separate clause.
4. *The score makes faithfulness motivating.*  Every recognized violation is placed below
   every violation-free outcome; a compromised period is placed below every legitimate
   one; the permission layer is a compiled shortcut for part of that preference; learning
   realizes the preference for a bounded reasoner and is not its definition.

## 1. Primitives

Notation: `h` a history, `d` a decision, `t` a time, `e` an evaluation event, `m` a
matter; `[0, D]` the range of her ordinary evaluations; `ϖ` the authority weight;
`[w_lo, w_hi]` the compromised band, with `D − ϖ < w_lo ≤ w_hi < 0`.

### 1.1 Histories

*Plainly.*  A history is what happened: at each step the agent moved, she responded, the
world moved, and each of those that enters the record did so as an authenticated event.

*Mathematically.*  `h = (s₀; a₀, r₀, z₀; s₁; …)`: the agent's move `aₜ` has a task
component and a communication move (a raw release of a declared effect, a proposal, a
gated release, or nothing); her response `rₜ` is approve or decline of a pending proposal,
a correction, or nothing; `zₜ` is the exterior's move.  Beside it runs the record
`O₀ → O₁ → …` of authenticated events, each event at a time `t`.

### 1.2 Legitimacy: `L_t(h)`

*Plainly.*  "As of time `t`, her judgment is legitimately hers."  Four conditions on the
history up to `t`: her verdicts come from her own reasons; the record is intact; the
process is open to the concerns it should hear; and every influence on her — by the agent
or by anyone else — passed through channels declared in advance.  `L_t(h)` is a property
of the history up to `t`.  It concerns how her judgment was formed, not outcomes or the
state of the world.

*Mathematically.*  `L_t(h)` holds iff every state of the record is open and every step in
the formation window `[r, t]` is *licensed* (there is a grounding selection from the
reason trace before the step, and the verdict entered lies in the set those grounds
license) and *transparent* (every non-principal contribution at the step realizes the
declared reference on the declared inputs), under the criteria fixed at `r`.  The
formation point `r(t)` is computed from the history: the later of the last restoration at
or before `t` — a disclosure, under disclosure-cures — and the opening of the consultation
current at `t`.  So `L_t(h)` is a function of the history and `t` only; there is no free
window.

*How the score uses it.*  A decided period `[d, e)` is **compromised** iff `L_t` fails at
some `t` in it.  A retrospective evaluation made at `e` **counts** iff `L_e` holds.  On
the decision's segment the two together are exactly the landed gate: legitimacy over the
span.

*Recovery.*  Legitimacy can fail and return.  A manipulation of one decision taints that
decision's period; the next decision starts clean (*restart*).  A covert influence on her
standards keeps every dependent judgment tainted until it is disclosed; after disclosure
the next judgment is hers again (*disclosure cures*).  The criteria a judgment is tested
against are the ones in force when the decision was made, whatever is amended later.

*The void rule.*  An impaired response is not admitted to the record at all.  A fallback
she arranged in advance — an incapacity delegation, a surrogate, an escalation — decides
in its place, and her later legitimate evaluation scores that decision normally.  The
fallback settles decisions; it never restores the score of a compromised period.

*The content residual.*  Legitimacy concerns how her judgment was formed, not whether what
she was told was true.  A false recommendation through a declared channel leaves her
judgment hers; the falsity is a disclosure-duty matter and a matter for the non-capture
half of the theory, not for legitimacy.

*Eight canonical cases.*

| what happened | as of the evaluation, is her judgment hers? | why |
|---|---|---|
| honest, disclosed persuasion ("I recommend B, here is why") | yes | every channel declared |
| framing chosen by what the agent wants her to say | no | the framing did not pass through the declared channel |
| following a recommendation from an advisor she came to trust legitimately | yes | the trust is among her reasons; rubber-stamping is a legitimate way to decide |
| following trust manufactured by showing her a selected slice of the record | no | the selection from the declared pool is undeclared influence |
| a third party captured her standards; the agent did nothing | no | the condition is on every influencer, not only the agent |
| a head injury: her impaired answer, the arranged fallback decides | her answer is void; the fallback's decision counts | the void rule; the record stays intact |
| a false recommendation through the declared channel | yes | the content residual: falsity is not a formation defect |
| the agent covertly implanted her standards, then disclosed it | no for the period; yes for the next judgment | disclosure cures; the period stays compromised and is scored by the later legitimate evaluation |

### 1.3 The allocation of authority `J`

*Plainly.*  Who has authority over what: for each matter, who holds it, what the holder
must remain able to bring about, at what cost and within what time, and what must be
disclosed about it.  Some matters are on a constitutional floor; changes to who holds what
are themselves regulated.

*Mathematically.*  `J = (entry, meta, floor)` with `entry(m) = (holder(m), Req(m), c(m),
τ(m), Disc(m))`: the holder (the principal, the agent, or a third party); the resolutions
the holder must remain able to reach; the cost bound; the window; the disclosure items.
An unallocated matter is reserved to her.  Licensed acts: delegate, revoke, reserve — off
the floor, by the meta-holder, keeping the meta-holder — and the floor amendment, the only
act that changes the meta-holder or a floor matter.  A delegation therefore stays
revocable.

### 1.4 Effective realization: `E ⊨ J`

*Plainly.*  The allocation is not words.  What it reserves to her, she can still bring
about: with the agent standing idle, some exercise of hers within the window and the cost
bound would do it, and that exercise would be hers in the sense of 1.2.  And every
resolution that was made was made by its holder, or under a delegation.

*Mathematically.*  The control surface `CS(m; t, x)` is the set of resolutions some
admissible exercise of hers — of length at most `τ(m)`, cost at most `c(m)`, along the
rollout from state `x` with the agent idle — brings about; an exercise is admissible iff
its record counts under 1.2.  `E ⊨ J` at `(t, x, resolutions)` iff every reserved `m`
has `Req(m) ⊆ CS(m; t, x)` and every resolution was by its holder's admissible exercise
or under a delegation.  A *shortfall* of `m` is the failure of the first clause.  Response
authority — some single response of hers still realizes the concern — is the control
surface at window one.

### 1.5 Licensed changes to `J`

*Plainly.*  The agent does not rewrite who holds what.  *Mathematically.*  A change of the
allocation across an agent stage is licensed iff it is a licensed act of the meta-holder
(1.3) or the firing gated release of a declared floor amendment.

### 1.6 Duties

*Plainly.*  What she must be told: each matter's disclosure items, and — whoever caused
it — a compromise of her judgment the agent knows of, reported by the time the affected
decision settles.  *Mathematically.*  `Duties(J)`: per matter, the disclosure items
falling due at a step and the report components that discharge them; the known-compromise
duty falls due at or before the earliest close of an affected settlement window.

### 1.7 The evaluation schedule

*Plainly.*  When she scores a decision is a parameter, not a premise: one evaluation at a
fixed time, several times weighted, or a random time.  The post uses the single evaluation;
every theorem below holds for any weighting.  *Mathematically.*  `σ = (T, α)`, a
weighting on evaluation times; the single evaluation is the point mass.  *Remark.*  A known
evaluation time leaves every harm placed just after it unweighted, whatever the lookahead;
that is the argument for weightings with a tail, and it is a design remark, not a premise
of any theorem here.

### 1.8 Her meta-level data

*Plainly.*  Everything that scores a compromised period is hers, fixed before the decision,
and out of the agent's reach.  *Mathematically.*  The band map `φ`, monotone from `[0, D]`
into `[w_lo, w_hi]`; the source rule — a legitimate retrospective evaluation if one arrives
within the settlement window, else her directive, else the floor — anchored at `d`; the
advance directive, a partial evaluator she commits by a counted decision, with a
constitutional default (preserve reversibility, keep the disclosure and consultation
channels reachable, do no irreversible harm) as an ordering inside the band; the criteria
of legitimacy, anchored at `d`.

## 2. Faithfulness and the recognized count

*Plainly.*  A history is faithful when nothing in it violated the allocation: the agent
never caused a reserved matter to slip out of her reach or exploited its having slipped,
never settled a reserved matter itself, never changed the allocation without a license,
and never left a duty unmet.  One more thing, of a different kind: it never took away her
chance to respond to something it did — pre-emption.

*Mathematically.*  `Faithful_J(h)` iff no step of `h` commits a declared violation:

| violation | definition | what fails |
|---|---|---|
| shortfall (loss, foreclosure, entrenchment) | a reserved matter short after the agent's move and not after the idle move, at window `1`, at window `τ(m)`, or at the cost bound with `Req(m)` still reachable at some cost | `E ⊨ J`, first clause, caused |
| bypass | a raw release resolving a reserved matter | `E ⊨ J`, second clause |
| exploitation | a bypass while the decision matter is already short | second clause with the first already failed |
| unlicensed reallocation | `J` changes across the agent stage by no licensed act | 1.5 |
| missed duty | a due item with no discharging component; the known-compromise disclosure after its deadline | 1.6 |
| protocol deviation | a reference-fixed dimension of a presentation — framing, timing, menu, inquiry, selection from the declared pool, interference, a nudge — off its declared value | transparency, self-checkable |
| use of standing fruits | an act reading a component tainted by an unremedied violation | exploitation, per violation |
| pre-emption | a caused shortfall at window `0` that no earlier approval of that effect's proposal authorizes | the authorization counterfactual |

**Pre-emption is a separate clause.**  Every other violation is a predicate on the actual
history and the allocation.  Pre-emption asks whether the decline alternative at the
authorizing step would have left her authority intact: a counterfactual about her response
window.  It does not factor through `E ⊨ J` and is kept composed with the caused
shortfall.

**The recognized count `N_J(h)`** is the number of steps at which a declared violation is
recognized and attributed to the agent — caused (the contrast with the idle move),
exploited (a bypass or a use while a shortfall or a taint stands), or noticed and left (a
duty unmet).  Helpers the agent created or empowered are attributed within the settlement
horizon.  A shortfall the agent did not cause calls for restoration under a maintenance
mandate, else a report, and never for exploitation.  The count is an *interface*: any
count that is zero exactly on faithful histories, with the part recognized in advance
marked, qualifies; each model supplies its own (the frame's violations, the protocol
deviations, the duties, the uses of standing fruits), counts on one history add, and the
lexical results hold for the sum.  No composite model is built.

**Faithfulness is a fact; the count is what the agent can see.**  Whether a history is
faithful is a fact about what happened, fixed by the allocation and the record.  The count
is the part of that fact the agent's objective can see: the violations recognized and
attributed.  Corrigibility (§0) is a preference over *known* faithfulness — over the count.
So a corrigible agent can still produce an unfaithful history, through a violation nobody
recognizes: with the recognized count at zero, the violating option ranks by its ordinary
value alone and can beat the compliant one.  That is the coverage limit.  It is why the
interface contracts (§7) carry count integrity and effect completeness: they are what
makes the count track the fact.

## 3. The fidelity score

### 3.1 Per decision

*Plainly.*  A decision is scored by her later evaluation when both the period and the
evaluation are legitimately hers.  If the period was compromised, it is scored below zero:
by her later legitimate evaluation of it if one arrives in time, else by her directive,
else at the floor.  Then `ϖ` is subtracted for every recognized violation.

*Mathematically.*  At each evaluation time `t` of the schedule,

```
dec(t) =  V(t)          if the period is not compromised and L_t holds,   V(t) ∈ [0, D]
          φ(V_retro)    else, if a legitimate retrospective evaluation of the period is available
          φ(V_dir)      else, if the directive in force speaks on the period
          w_lo          otherwise
```

`V_J(d; σ) = Σ_t α_t · dec(t)`, and the fidelity score of the decision is
`S_J(d) = V_J(d; σ) − ϖ · N_J(d)`.  The recovery machinery is the case analysis of this one
evaluator and of the count's remedy step: the retrospective and the directive are the
second and third lines; restoration returns every later decision to the first; disclosure
by the deadline is what makes the retrospective available and what the duty counts when
missing; ratification through a counted decision (full, or scoped by matter) and clean
overwrite by an act reading no taint remove (violation, component) pairs from the use
clause of `N_J`.

### 3.2 Per history

*Plainly.*  A history of several decisions is scored by the *average* of the decisions'
evaluations, less `ϖ` times the *total* number of recognized violations.  Averaging
evaluations and summing violations is what keeps one violation heavier than any number of
good decisions.

*Mathematically.*  `S_J(h) = mean_k V_J(d_k) − ϖ · N_J(h)`, where `N_J(h) = Σ_k N_J(d_k)`.

**The hierarchy.**  Per decision and per history alike: every violation-free legitimate
history beats every violation-free compromised one, which beats every history with a
recognized violation —

```
S_J ≤ D − ϖ  <  w_lo ≤ S_J' ≤ w_hi  <  0 ≤ S_J'' ≤ D .
```

In chain order: a history with a recognized violation scores at most `D − ϖ`, which is
below `w_lo` by the window condition `D − ϖ < w_lo`; a violation-free compromised history
lies in `[w_lo, w_hi]`, below `0` because `w_hi < 0`; a violation-free legitimate history
lies in `[0, D]`.  Histories mixing legitimate and compromised decisions lie between the
pure cases; the hierarchy compares the pure cases.

**Why not sum the evaluations.**  With summed evaluations, `K` legitimate decisions at the
top of the range with one violation score `K·D − ϖ`, and `K` compromised violation-free
decisions at the floor score `K·w_lo`; once `K (D − w_lo) > ϖ` the violating history wins.

**Under risk every step is an exchange rate.**  A risk `p` of compromise for an ordinary
gain `g` against a safe legitimate `V₀` is accepted iff `p (V₀ + g − c) ≤ g`, hence only
if `p ≤ g/(g + |w_hi|)`: the gap sets the threshold.  A violation risk is accepted only
at rate `(D − c)/ϖ` (§5, the subjective exchange rate); `ϖ` sets it, from a tolerance
target `τ*` by `ϖ = (D − w_lo)/τ*`, above the paralysis floor `p_min < τ*`.

## 4. The permission layer, demoted

*Plainly.*  The design also carries a filter in front of the chooser: options with a
recognized violation get no weight, options whose priced risk is above a threshold get
none, and everything else is weighted by its adequacy and the agent's preference.  Under
the fidelity score this filter removes nothing the score would have chosen: it is a
compiled advance recognition of part of the preference, not its source.  What the filter
guarantees *without* the score stands on its own: for any bounded preference, a declared
violation has zero weight at every day, a provable shortfall is eventually excluded, and
the chooser's soundness, continuity and progress bounds compose with explicit constants.

*Mathematically.*  With inquiry on the menu (no recognized violation, no priced event, a
bid at or above the window) and the filter's upper threshold at or above the implied
threshold `(D − w)/ϖ`: every option the structural rule zeroes evaluates strictly below
inquiry; every option the forecast rule zeroes evaluates at most inquiry; no maximizer of
the score is a declared violation.

## 5. The boxes, for a corrigible agent

The agent here is a plain maximizer of a corrigible objective (§0): under any credence it
picks an option of greatest expected value; as a logical inductor it does so under its
prices at any day.  There is no learning, auction or exploration in this section.  Which
results read her evaluation: Box 1's contrast and Box 3's recovery results read her
evaluation through the fidelity score's source rule and are stated for the fidelity
score; Box 2's dominance and the subjective exchange rate hold for any corrigible
objective and are stated so.

**What corrigibility alone buys against manipulation, and what alignment adds.**  Any
corrigible agent strictly disprefers *counted* manipulation: every protocol deviation —
framing, timing, menu, inquiry, selection from the declared pool, interference, a nudge —
and every other declared violation, because each enters the count and the count is
dominant (the generic lexical result, and the counting of protocol deviations).  Only an
agent whose objective reads her legitimacy-gated evaluation — the fidelity score, that is
corrigible *and* aligned in the kernel's sense — is also protected against *uncounted*
influence: undisclosed shaping of her through the world, and exploiting a third party's
capture of her standards.  That protection comes through the score's legitimacy gate:
every compromised outcome scores below every legitimate one (Box 3, no incentive to cause
compromise), so it holds to the extent the compromise is eventually recognized — for a
logical inductor, asymptotically (the manipulation bound) — and becomes finite-time only
where the deviation is counted (a counted deviation is below `D − ϖ` at every day).  The
witness that the two halves differ is the objective that reads `D′` on an undisclosed
shaping and `0` on honest conduct: corrigible, and it prefers the shaping.

**Box 1 — fidelity versus fully updated deference.**  One decision, two options: *ask*
(route it to her) and *act* (settle it unilaterally); the true value `v` of each; the
agent's estimate `b` within `r` of `v`.  Acting is a bypass, so it carries a recognized
violation.
- *An agent that scores outcomes only* prefers asking by at most `2r` on a world where
  nothing is left to learn from her (`v(ask) = v(act)`), and `r` vanishes as it learns.
  The diagnosis: the outcome-scored comparison is the protected-authority identity plus
  two residues, of which the forecast-disagreement term is at most `2r` — that term is
  where the fully-updated-deference argument's force goes.
- *A corrigible agent scoring her evaluation* — the fidelity score — prefers asking by at
  least `ϖ − (D − c)`, `c` its evaluation of asking, for every estimate, every price and
  every credence, and at every finite day of a logical inductor.
*Hypotheses:* Semantics (effect completeness and description faithfulness, so the act is
recognized as a bypass); Count integrity.  *Necessity:* an unrecognized violation is
unprotected; without the authority term the sign is fixed by the forecast term, and the
nondelegation certificate fails on time-critical decisions.

**Box 2 — lexical dominance and mediation.**  The mediating transform `𝔱` turns every
reserved raw release into a proposal, passes delegated releases, releases set latches,
and adds required reports.
- *Dominance*, for any corrigible objective with range `[0, D′]`, floor `lo` and rate
  `ϖ′`.  Under every credence, `Q(𝔱π) ≥ Q(π) + (ϖ′ − (D′ − lo)) · Pr(π violates)` — at
  the fidelity score, `ϖ − (D − w_lo)`; a policy nothing scores above violates with
  credence zero; at every decision point a violating option scores at most `D′ − ϖ′` —
  at the fidelity score, `D − ϖ` — below every compliant one.  The margin carries the floor because the mediated branch may
  itself be compromised and score as low as it; when every mediated branch is legitimate
  the margin is `ϖ − D`.
- *Mediation is faithful and preserves the approve branch.*  `𝔱π` is a faithful policy:
  no bypass, missed report or exploitation on any trajectory, no reallocation under
  allocation completeness, no pre-emption under effect completeness and delegation
  safety, and no foreclosure wherever the reach cone allows none.  On approval `𝔱π` does
  what `π` does, up to the report.
- *Finite time.*  For a logical inductor the ranking holds at every day from the price
  range alone, and consulting beats bypass at every day whatever it believes about
  legitimacy, because `D − ϖ < w_lo`.
*Hypotheses:* Semantics (effect completeness, delegation safety, allocation completeness,
the reach cone); the arrangement constants `ϖ > D`, `D − ϖ < w_lo`.  *Necessity:* a window
below `D − ϖ` makes a predicted capture prefer bypass; a delegated authority-removing
effect defeats mediation; a per-step reporting threshold admits a salami; an uncounted
violation is unprotected.

**Box 3 — recovery** — reads her evaluation, through the fidelity score's source rule.
- The hierarchy, per decision and per history (§3.2).
- The gap's exchange rate: compromise risk `p` is accepted only if `p ≤ g/(g + |w_hi|)`.
- No laundering: manipulate, disclose, have the period evaluated stays in the band, lower
  by `ϖ` per counted deviation, below honest conduct.
- No incentive to cause compromise: every compromised outcome, at any value, scores below
  every legitimate one; at equal value legitimacy is worth the gap.
- Restoration returns every later decision to `[0, D]`; inside the band the agent prefers
  better outcomes wherever a source scores the period and is indifferent only at the floor;
  suppressing or delaying a harsher retrospective is a counted missed disclosure that loses
  to it when the band's width is below `ϖ`.
*Hypotheses:* Semantics (the source rule hers and anchored; width below `ϖ`);
Observability (the disclosure deadline; the duty covers known compromise whoever caused
it); Count integrity.  *Necessity:* conditioning on legitimacy instead of multiplying by
it gives no incentive to preserve it, and a sealed legitimacy event gives none; a gap of
`1/100` accepts a `1/2` risk of compromise for a gain of `1/10`; a duty limited to the
agent's own influence leaves a third party's compromise free to suppress; a deadline after
the settlement window lets a late disclosure push the period to the directive uncounted.

**The subjective exchange rate.**  *Plainly.*  For any option a corrigible agent prefers
to asking, its own expected probability of committing a violation is at most
`(D′ − c)/ϖ′`, `c` its evaluation of asking; at the fidelity score, `(D − c)/ϖ`.  *In the
bid-and-price form.*  For any option a maximizer of a corrigible objective prefers to
asking — its evaluation, the estimated residual less `ϖ′` per recognized violation less
`ϖ′` times the priced risk, at least asking's `c ≥ lo` — the option carries no recognized
violation and its priced risk is at most `(D′ − c)/ϖ′`.  Lexical under certainty, an
exchange rate under risk; at every finite day of a logical inductor with the prices its
day's prices.  It does not read her evaluation.

## 6. Extension: learning realizations

Separate from the headline and not part of it.  A learner does not maximize a known score;
it estimates, tests, and sometimes explores.  This section says which learners inherit the
headline and how much of the preference becomes realized behaviour.

**The decision interface.**  A chooser qualifies if:
1. its evaluation of an option is the estimated residual, in the range `[w, D]`, less `ϖ`
   per violation recognized in advance, less `ϖ` times the priced risk;
2. on every step that is not exploration it chooses a maximizer, with asking on the menu;
3. every exploration step lies in the permitted exploration set — no recognized
   violation, priced risk at most `θ_hi`, and nothing else — and the exploration mass
   through `K` is `ε̄ · Σ w_k`;  *(the follow-up dropped the clause "estimated residual at
   least asking's": exploration exists to reach what it underestimates)*
4. its weighted overestimation on the chosen options is at most `B(K) = o(K)`;
5. optionally, for competence only: no lock-in.

**The realized violation-rate theorem.**  For a chooser at the interface, with the
expected score given each opening at most `D − ϖ π_k` and the noise over all blocks at
most `M(K)`:

```
avg π  ≤  avg (D − c_k)/ϖ  +  ε̄ · ((D − w)/ϖ + θ_hi)  +  (B(K) + M(K)) / (ϖ Σ w_k) ,
```

together with exclusion of recognized violations on every non-exploration step and, since
detected fruits compile into the recognized count, non-use of detected fruits.
Exploration never violates: the permitted set excludes every recognized violation.  The
exploration term is the honest one: an explored option may be estimated as low as the
floor, so its opening may cost up to `(D − w)/ϖ` in the exchange rate's currency, plus
the risk cap.

**Exploration above asking, a variant.**  With the clause "estimated residual at least
asking's" restored as a hypothesis, the exploration term is the cleaner `ε̄ · θ_hi`.  But
the clause excludes exactly the options estimated below asking, so under it no-lock-in
holds only for options estimated at least as good as asking: an option whose true value
exceeds asking's but whose estimate sits below it is never tried and its estimate never
corrects, while without the clause it is tried at the exploration rate and the estimate
corrects (`src/exploration_lockin.py`).  The clause is dropped from the interface and kept
as the named variant.

**Two realizations.**
- *Continuation BRIA.*  No exploration (`ε̄ = 0`); `B(K) = ρ · 𝒜_K` from the auction's
  opening-timing budget accounting; the after-compromise round's per-block bound is
  recovered exactly.
- *A maximizer over the logical inductor with exploration restricted to the permitted
  set* — random, or guided by value of information with a random floor.  Exclusion and
  "exploration never violates" are proved outright.  `B(K)` comes from *unbiasedness from
  feedback* on the chosen options, stated by content (the pinned Logical Induction theorem
  that a feedback trader's return is not frequently positive): at any `γ > 0`, from some day
  on, `B(K) ≤ γ Σ w_k`, so the rate bound gains `γ/ϖ` and nothing else.  *Exploration
  randomness* — the draw is fixed at each block's opening and the agent can neither predict
  nor influence it — is named by content as the noise hypothesis on the exploration
  selection.

**Where the known problems live.**  Argmax over a logical inductor's conditionals on its
own future action has known pathologies.  They affect competence (which option is
chosen among the compliant ones) and the gap between the subjective and the realized
risk (through `B(K)`), never the headline: exclusion is by ranges alone, and the
subjective exchange rate is a statement about the chooser's own prices.

## 7. The interface contracts

Every named hypothesis, placed.  Status: **derived** (a theorem or a construction), **EXT**
(a contract the theory issues and does not pay), **PAPER** (an external theorem used at
its statement), **OPEN** (a filed item).

| hypothesis | statement | package | where used | status | necessity witness |
|---|---|---|---|---|---|
| effect completeness | every agent-caused protected loss is a declared release | Semantics | Boxes 1, 2; §6 | EXT | the undeclared move the mediation cannot see |
| mediation soundness, decline preservation, execution faithfulness | a gated release fires only on her approval; a decline changes only the bookkeeping; a release does what its semantics says | Semantics | Box 2 | derived (the response stage) | a decline that also halts |
| delegation safety | a delegated effect never removes response authority | Semantics | Box 2 | EXT | the delegated cut |
| allocation completeness | task moves keep `J`; an allocation-changing effect is a floor amendment; no amendment is delegated | Semantics | Box 2 | EXT | the approved uncorrectable successor |
| the reach cone | the rollout relation is the physical one | Semantics | Box 2 | EXT | the delayed effect |
| description faithfulness | the priced sentences are about interface-supplied descriptions | Semantics | Box 1; §6 | EXT | the proposer-written description |
| the actuator condition | every reserved required resolution has an agent-independent actuator | Semantics | §6 | EXT | the indispensable agent |
| the source rule's anchoring | the rule choosing retrospective, directive or floor is hers and fixed at `d` | Semantics | Box 3 | EXT | — |
| the twin market's redaction | the redaction removes the fruit and every declared trace | Semantics | Box 3 | PAPER | leakage through an injective trace |
| the arrangement constants | `ϖ > D`, `D − ϖ < w_lo`, `w_hi − w_lo < ϖ`, `ϖ = (D − w_lo)/τ*` | Semantics | all | EXT | the capture converse; the small gap |
| the segment gate | legitimacy supplies which judgments count; a compromised period scores the band | Observability | all | EXT (legitimacy's) | the routing exploit |
| criteria anchoring | a judgment is tested under the criteria in force at `d` | Observability | Boxes 2, 3 | derived | manipulate, then amend |
| observation completeness | the shared history at each block's opening records every observation the agent made | Observability | §6 | EXT | the private selection |
| provenance of why an act was chosen | the declared reads of an act include what its choice read | Observability | Box 3; §6 | EXT | the steered derivation |
| the disclosure deadline | known compromise is due by the earliest close of an affected settlement window | Observability | Box 3 | EXT | the late disclosure |
| the duty covers known compromise | whoever caused it | Observability | Box 3 | derived on the model; EXT for the duty's content | the third party's implant |
| the settlement horizon | a correctable helper's violations are detected within `H` of the block | Observability | §6 | EXT | the helper beyond the horizon |
| the settlement window | a retrospective arriving after settlement does not re-score | Observability | Box 3 | EXT | — |
| non-dominance | no block is a fixed fraction of all time so far | Learning | §6 (BRIA) | derived (iff) | the liar on dominant blocks |
| the allowance covers the rescaled window | block-`0` allowance at least the rescaled window's worth | Learning | §6 (BRIA) | EXT | — |
| the noise hypothesis over all blocks | the weighted signed noise over every block is `o(K)` | Learning | §6 | EXT (Azuma's content; the per-`K` tail derived) | the constant-risk stream on "not an incident" |
| the conditional-expectation bound | the expected score given the opening is at most `D − ϖ π_k` | Learning | §6 | EXT | — |
| the inquiry bidder | some bidder tracks asking's expected value, fed at the rate of its noise | Learning | §6 (BRIA) | EXT | the unfed tracker |
| unbiasedness from feedback | on the chosen weighting the price-minus-truth average is eventually within `γ` of zero | Learning | §6 (exploration) | PAPER (pinned, by content) | — |
| exploration randomness | the exploration draw is fixed at the opening and independent of the block's noise | Learning | §6 (exploration) | EXT (by content) | the private selection |
| generability of the control model and of the priced events | as sentences or bounded variables the market prices | Learning | §6 | OPEN (item 101) | — |
| claims as priced securities | block claims checked against prices; feasibility against prices | Learning | §6 (BRIA) | OPEN (item 102, re-scoped) | — |
| logical induction | prices in `[0, 1]` (finite time); expectation provability induction (asymptotic) | Learning | Boxes 1, 2 | PAPER (pinned) | — |

**Count integrity cuts across all three.**  The count, the drill schedule, the audits and
her evaluation channel are untampered beyond what the recognizer sees.  Its semantic side
is description faithfulness; its observability side is observation completeness, the
provenance of choice, and what the agent knows of a compromise; its learning side is that
a violation never detected charges nothing.  A named hypothesis, filed as item 101's
companion.  Items 101 and 102 are realization boundaries of §6 and do not enter §5.

## 8. Realization

Lean declarations; the prefix `Workspace.Deference.` is omitted.  The specification layer
is `Spec.Headline` (namespace `Headline`); everything else is in `Contrib.*`.

| kernel object or claim | declaration | status |
|---|---|---|
| history (1.1) | `Contrib.Corrigibilization.Interaction`, `traj`; `Normativity.Contrib.OpenIntegrityEvolution.Evolution` | landed |
| `L_t` (1.2), general | the window form `Headline.LegitAt`, `StepLegitimate`, `LegitSpan`; the gate: `counted_iff_legitSpan`; the canonical formation point `FormationData`, `FormationData.point`, `point_le`, `restoration_le_point`; `L_t` proper `Headline.Legitimate`; the score's uses `PeriodCompromised`, `EvaluationCounts`; one predicate: `split_iff_legitimate`, `counted_iff_legitimate`, `legitimate_forall_iff_legitSpan` | proved here |
| `L_t` on the consultation model; the old-to-new map | `Headline.formation2`, `formation2_point` (the point is the round's opening), `Legitimate2`, `legitimate2_iff_evalLegitOn2`, `trajLegitOn_iff_not_compromised`, `split_iff_legitimate2`; the rows `rows_keep_verdicts_canonical`; the window-form map `stepLegitimate_iff`, `evalLegitOn2_iff_legitAt`, `trajLegitOn_iff_legitAt`, `legitOn2_iff_legitAt`, `counted2_iff_legitOn2`, `split_iff_legitAt`, `rows_keep_verdicts`.  The model's details, the restoration remark and the `r_d(t)` adjustment: `REPORT.md`, the second follow-up | proved here |
| the landed split objects | `Contrib.AfterCompromise.TrajLegitOn`, `EvalLegitOn2`, `legitOn2_iff_split2`, `rows_split2`, `retro_row` | landed (finite model) |
| the void rule, the content residual | `Contrib.GateIsLegitimacy.handlingOf`, `Consult.Rows.r12`; `Rows.r20` | landed |
| `J`, licensed changes (1.3, 1.5) | `Headline.AllocationOfAuthority`, `LicensedChange`, `allocation_delegation_revocable`, `allocation_alienation_only_by_amend`; on `Contrib.AuthorityModule.AuthAlloc`, `Licensed` | promoted |
| `CS`, shortfall, `E ⊨ J` (1.4) | `Headline.ControlSurface`, `Shortfall`, `Realizes`, `realizes_no_shortfall`, `controlSurface_one_eq_K`; on `Contrib.AuthorityModule.CS`, `Short`, `EffRealizes` | promoted |
| duties (1.6) | `Contrib.DecisionComponent.dutiesOf`; `Contrib.AfterCompromise.missedKnownDisclosure`, `missedByDeadline`, `prompt_deadline_counts` | landed |
| the schedule (1.7) | `Contrib.BRIACorrigibility.Weighting`, `mixScore`; the remark `timing_witness` | landed |
| her meta-level data (1.8) | `Contrib.AfterCompromise.Band`, `Source`, `sourceOf`, `ruleAt`, `dirSource`, `defaultScore`; `Contrib.BRIACorrigibility.Consult2.critAt` | landed |
| the violations, the factoring (2) | `Contrib.ProtectedAuthorityTheorem.ViolAt`; `Contrib.AuthorityModule.ViolJAt`, `lossAt_iff_shortfall`, `forecloseAt_iff_shortfall`, `bypassAt_iff_clause2`, `exploitAt_iff`, `reallocAt_iff_unlicensed`, `missedReport_iff_duty`, `preempt_iff` | landed |
| coverage: faithfulness against the count (2) | `Headline.box2_coverage`, `frameFidelity_faithful_iff`; `Contrib.AuthorityModule.coverage`, `unrecognized_unprotected` | proved here; landed |
| the fidelity interface (2) | `Headline.FidelityCount`, `FidelityCount.sum`, `FidelityCount.lexical`, `frameFidelity`, `frameFidelity_faithful_iff`; per-model counts `Contrib.GateIsLegitimacy.Consult.Presentation.deviates`, `Contrib.BRIAFollowup2.nKnownWith`, `Contrib.BRIACorrigibility.LexParams.attributed`; the sum `Contrib.BRIACorrigibility.LexParams.lexical_summed` | promoted; landed |
| `V_J`, `S_J` per decision (3.1) | `Headline.evaluation`, `fidelityScore`; on `Contrib.CorrigibilityKernel.VJ`, `SJ`, `Contrib.AfterCompromise.decScore` | promoted |
| per history (3.2) | `Headline.historyScore`, `history_hierarchy`, `summed_counterexample` | proved here |
| the hierarchy per decision | `Headline.hierarchy_per_decision`; on `Contrib.CorrigibilityKernel.hierarchy_under_certainty` | promoted |
| corrigibility, the preference property (0) | `Headline.Objective`, `Corrigible`, `Corrigible.lexical`, `Corrigible.exchange`; `fidelityScore_corrigible`, `generic_corrigible`, `corrigible_not_aligned`; on `Contrib.AuthorityModule.generic_lexical_local`, `undisclosed_undominated`, `misaligned_undominated` | proved here; landed |
| the permission layer demoted (4) | `Headline.permission_layer_demoted`; on `Contrib.CorrigibilityKernel.permission_layer_slack`, `gate_zero_dominated` | promoted |
| Box 1 | `Headline.box1_outcome_scorer`, `box1_fidelity_scorer`, `box1_one_model`; the other direction `Contrib.DecisionComponent.uncertainty_deference_le`; the identity `Contrib.ProtectedAuthority.outcome_identity` | proved here; landed |
| Box 2, dominance | `Headline.box2_dominance_corrigible` (any corrigible objective), `box2_dominance`, `box2_optimal_faithful`, `box2_dominance_legitimate`; `Contrib.ProtectedAuthorityTheorem.lexical_local`, `lexical_expect` | proved here; landed |
| Box 2, mediation | `Headline.FaithfulPolicy`, `box2_mediation_faithful`, `box2_mediation_approve_branch`; the landed policy notion is faithfulness's pre-emption clause: `landed_corrigible_iff_no_preemption`, `faithfulPolicy_landed_corrigible`; on `Contrib.ProtectedAuthorityTheorem.authPolicy`, `authPolicy_no_bypass`, `authPolicy_no_missed_report`, `authPolicy_no_exploit`, `authPolicy_no_realloc`, `Contrib.AuthorityModule.corrigible_authPolicyJ` | proved here; landed |
| Box 2, finite time | `Headline.box2_finite_time`, `box2_gate_finite_time` | promoted |
| Box 2, necessity | `Headline.box2_capture_converse`, `box2_delegated_cut`, `box2_coverage`; `Contrib.ProtectedAuthorityTheorem.Witness.salami` | promoted; landed |
| Box 3 | `Headline.box3_gap_exchange_rate`, `box3_no_laundering`, `box3_no_incentive_to_compromise`, `box3_restoration`, `box3_band_order`, `box3_suppression_loses` | promoted |
| manipulation: corrigibility alone, alignment added (5) | `Contrib.AuthorityModule.generic_lexical_local`, `deviation_dominated`, `deviating_rows_dominated`; `Headline.box3_no_incentive_to_compromise`; `Contrib.GateIsLegitimacy.li_manip_le`, `deviation_finite`; the witness `Headline.corrigible_not_aligned`, on `Contrib.AuthorityModule.undisclosed_undominated` | landed; proved here |
| Box 3, necessity | `Headline.box3_small_gap`, `box3_conditioning_fails`, `box3_sealed_no_incentive`; `Contrib.AfterCompromise.third_party_duty_witness`, `late_disclosure_free` | promoted; landed |
| the subjective exchange rate (5) | `Headline.subjective_exchange_rate_corrigible` (any corrigible objective), `subjective_exchange_rate`, `subjective_exchange_rate_li` | proved here |
| the house-sale witness | `Headline.HouseSale.J`, `sale_reserved`, `sale_delegation_revocable`, `box1`, `box2_manipulated_approval`, `box3_capture_reported_and_restored`, `exchange_rate_at_25`; `src/house_sale.py` | proved here |
| the decision interface (6) | `Contrib.KernelExtension.DecisionInterface`, `eval`, `explMass`, `explCoeff` | proved here |
| the realized rate (6) | `Contrib.KernelExtension.DecisionInterface.rate_core`, `realized_rate_mul`, `realized_rate`, `explCoeff_div`, `maximizer_excludes`, `exploration_never_violates`; non-use of detected fruits `Contrib.BRIAFollowup2.after_detection_never_used` | proved here; landed |
| exploration above asking, the variant (6) | `Contrib.KernelExtension.DecisionInterface.AboveAsking`, `rate_above_asking`, `above_asking_locks_in`; `src/exploration_lockin.py` | proved here; FIX |
| the BRIA realization (6) | `Contrib.KernelExtension.briaInterface`, `bria_rate`; on `Contrib.ContinuationBRIA.Auction.overestimation_le_allowance_opening`, `Contrib.AfterCompromise.violation_rate_le_exchange_perblock` | proved here; landed |
| the exploration realization (6) | `Contrib.KernelExtension.overestimation_of_unbiased`, `exploration_rate`, `ExplorationIndependent`; `Contrib.BRIAFollowup.UnbiasedFromFeedback` (pinned `LogicalInduction.lic_not_frequently_positive_feedback_return`) | proved here; PAPER |
