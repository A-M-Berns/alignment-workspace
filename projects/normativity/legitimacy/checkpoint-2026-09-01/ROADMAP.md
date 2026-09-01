# Roadmap from the September checkpoint

**The question this roadmap answers:** given everything now known, what is the
shortest path to a theorem of legitimacy that is useful for corrigibility?

Four buckets, and the boundaries between them are the point.

    closed          closed for research sequencing (see below)
    active          being worked, with a shaped question
    open but shaped a precise question and a visible route
    missing idea    a precise question and no route

> **"Closed" here means closed for research sequencing**: the current theory regards
> the question as sufficiently answered to consume downstream unless an actual
> contradiction appears. **It is not an evidence class.** Almost everything under
> *Closed* is **paper-derived and test-supported**, not Lean-proved and not
> registered as proven; `STATUS_LEDGER.md` is the row-by-row account and governs.
> The two axes are independent, and a result can be closed for sequencing while its
> formal verification is still owed — which is the normal state here.

This is **not** a copy of `PRIORITIES.md`. Priority items are work orders;
this page says which are still worth issuing and which the checkpoint retired.

---

## Closed for research sequencing

Consume these; do not reopen without an actual contradiction. **Closed for research
sequencing; paper-derived + test-supported unless the ledger marks otherwise.**

- **The fixed-era composition.** Claim stream to claim-weighted Progress and to
  substrate preservation, with every arrow carrying a prose derivation and no gap
  left implicit. (`rounds/2026-08-31-normative-affordability/FIXED_ERA_THEOREM.md`,
  frozen.) The composition is complete; it is not formally verified.
- **The service typing.** Service is allocated authority.
- **Actionability at its weakest hypothesis.** `phi` bounded away from zero away
  from zero, necessary and sufficient; convexity buys only the rate.
- **Exogenous persistence.** `liminf L_t(1) = 0`, for any star-shaped date cost,
  with the finite-horizon optimum and the online equivalence.
- **Bounded-delay transport and its cost.** Interval feasibility, FIFO
  completeness, the sliding-window closed form.
- **The three service problems.** `persistence == eventual full service ⊊ uniform
  bounded delay`.
- **The friction collapse.** On the sharp linear branch under nested assessment,
  `F_r = 0`.
- **Sharp Timely Service.** The Layer I endpoint.
- **Deadline insolvency certificates.**
- **The structural half of diachronic answerability.** Grounded replay,
  prospective revision, slice-wise conservation, no silent terminal closure, the
  persistent-wait theorem, the answerability–service dichotomy.

---

## Active

- **Lean ports.** Everything above is paper-derived; three narrow declarations are
  kernel-checked. This is a standing item family (`AGENTS.md`) and the natural
  fate of `test-supported` work. The highest-value single port is **Theorem F2**,
  because everything downstream reduces to it.
- **The naming audit.** Nineteen provisional names are outstanding
  (`SUPERSESSION.md` §3). Maintainer-owned.

---

## Open but shaped

Ranked by *distance to a legitimacy theorem*, not by tractability.

### 1. Certifying semantic transport — where do the (T) constants come from?

`PRIORITIES.md` item 76. **The single highest-value open problem.**

Sharp Timely Service ends in `epsbar^r_N(T)` and nothing certifies it. Within an
era this is a technical gap. **Across eras it is the whole of Layer II**: "how much
of a reason survives a revision" *is* the transport constant.

*The visible route.* The note's anchored interpretation `J_alpha : Rep_alpha -> V_alpha`
with the fidelity preorder `⊑` and slice faithfulness. Anchoring is the right
property — the interpretation is not what the current evaluator says an old
representation means. What is missing is quantitative: `J_alpha` and `⊑` are
ordinal, `eps(t,s)` is metric, and no modulus connects them.

*Why first.* It unblocks cross-era answerability, and it converts the endpoint
theorem from conditional to constructive.

### 2. Cross-era Answerability

What makes a later reason or service count as *answering* an earlier one?

*The visible route.* The note's transfer components already give the accounting
shape (`Pre/Post/sat/disp`). What is missing is the licence condition on `disp`.
**A theory of authorized disposition is the pivot**: it simultaneously supplies
defeat, closes the laundering channel that would otherwise make every insolvency
vanish, and repairs the `sum c_t = infinity` hypothesis of EV1. **Filed as
`PRIORITIES.md` item 77.** See `ANSWERABILITY_AND_SERVICE.md` §6. Whether cross-era
answering needs a second item beyond the licence is not yet known.

### 3. Counterfactual non-capture

What protects the reason-generating and revision process itself?

*The visible route.* The Carroll round has a working criterion (live covering
authority plus counterfactual persistence under ancestry excision) and a sharp
negative (excision is non-monotone and non-composable, from two independent
sources). `SELF_SEALING.md` locates the boundary: Continuity alone cannot prove No
Clean Self-Sealing; ambient factorization plus behavioral locality can.

*Why third and not later.* It is the pillar with no Layer I analogue at all, so it
will not get easier by waiting, and every legitimacy statement is vacuous without
it.

### 4. Closed-loop affordability

`PRIORITIES.md` item 75. E3–E5 of `CLOSED_LOOP_EXISTENCE.md`.

*Shape.* The tractable first question is monotone: if enforcing a reason weakly
decreases its future depth, does the persistence criterion survive and is the
greedy tranche rule still causal-optimal? The adversarial one is whether a policy
can be driven into a friction trap it created.

*Priority note.* Lower than it looks. Every Layer I theorem is conditional on
exogenous friction, but a legitimacy theorem does not need the closed loop —
it needs the constants of (T) and a disposition theory. Closed-loop work makes
Layer I *robust*; it does not move the program toward Layer II.

### 5. The legitimacy predicate itself

Write down the statement. `LEGITIMACY_DECOMPOSITION.md` §5 argues that the
decomposition cannot be canonized until a definition with a conclusion someone
downstream wants exists, and none does.

*This is cheap and nobody has done it.* It should probably come before (3) and
(4), because it will change what those rounds are trying to prove.

### 6. The deference / corrigibility instantiation

Instantiate the legitimacy theorem in the successor setting. Downstream of (5)
and blocked on it.

---

## Missing idea

- **Justified defeat as a normative notion.** `MayDispose` is a licence predicate
  with no theory of what licenses it. Related to (2) above but strictly harder:
  (2) needs the accounting to be sound, this needs the licence to be *right*.
- **Coverage.** The world-to-record adequacy condition. Deliberately outside the
  answerability system in both bodies of work, consumer-relative, and nothing
  currently says what a consumer may demand.
- **A computable coherence modulus, or a proof there is none.** Carried from the
  August consolidation, open in both directions, and *not* settled by either
  nearby Gaifman impossibility result — both turn on a desideratum the candidate
  algorithm already fails.
- **Whether `F_r` is ever zero for a norm a practice actually produces.** The
  endpoint theorem is conditional on a residual nobody has exhibited vanishing in
  a realistic instance.

---

## What should no longer receive research energy

Stated explicitly, because the alternative is that someone rediscovers each of
these.

1. **Rate-region or time-sharing geometry of authority.** Withdrawn twice from two
   directions. The budget is a consumable stock; the persistence region replaces
   the object entirely.
2. **Any gap or density condition on cheap dates.** Three failed attempts. `D4` is
   the criterion.
3. **Realized force as a service measure.** Every quantity built on it inverts the
   sign of successful learning.
4. **Sharpening the online competitive ratio for accumulated authority.** Proved
   impossible; only the qualitative persistence equivalence survives.
5. **Improving the exogenous persistence criterion.** It is exact for every
   star-shaped cost. Further generality would need a non-star-shaped charge, and no
   realization produces one.
6. **A converse to the overload certificate as a near-term target**
   (`PRIORITIES.md` item 74). It certifies the failure of a hypothesis whose
   necessity is itself unknown (item 40); it stays filed and stays sequenced behind.
7. **Extending the affordability round.** It is finished. Further passes there
   would be Layer I polish while Layer II is where the program is blocked.

---

## The shortest path, in one line

> Certify semantic transport (1), which gives cross-era answerability (2) a
> content-preservation metric; write the legitimacy predicate (5) so that (3) knows
> what it must protect; then prove non-capture (3) and instantiate for deference
> (6). Closed-loop affordability (4) is robustness work that can proceed in
> parallel and blocks nothing.
