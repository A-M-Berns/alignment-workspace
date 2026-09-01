# Exogenous friction against the closed loop

## 1. Two models, and the benchmark lives in the first

**Exogenous friction.** The sequence `q_t` — or `s_t` and `m_t` separately — is
fixed independently of the authority policy. `SHARP_PERSISTENCE.md` S1 and S2 and
`ONLINE_EXISTENCE.md` O1 are theorems about this model and nothing else. It is a
*benchmark*: a sequence-selection problem with the engine's response summarized by
a worst-case charge.

**Policy-dependent friction.** In the traderized learner the friction is not
exogenous. The ordinary volume `M_t` responds to the prices earlier authority
helped set; the live-world set responds to settlement, which responds to
interaction; so the exclusion depth `D_t` is a function of the history the policy
helped produce. Writing `q^{pi, omega}_t` for the friction the policy `pi` induces
against exterior history `omega`, the existence question is

    exists pi  forall admissible omega :   sum_t a^{pi,omega}_t = infinity
                                           and the account stays above -B ,

which is a causal game, not a sequence selection.

Everything the round has proved about persistence is a statement in the first
model. This document says exactly what survives.

## 2. The quantifier worry dissolves, and leaves a worse problem

The dispatch asks whether

    forall pi :  liminf_t q^{pi}_t = 0

suffices, warning that it is "not obviously enough to construct one policy whose
own induced sequence has dips".

It is enough, by instantiation: the threshold rule `pi*` of `ONLINE_EXISTENCE.md`
is a policy, so the hypothesis applies to it, so its own induced friction sequence
dips, so it triggers at every level and its allocation diverges. No construction is
needed.

**But the hypothesis is a strange thing to assume.** It quantifies over every
policy, including ones that never allocate anything, and it is not the sort of
statement a model of the engine would supply. What one would actually check is the
instantiated version,

    forall admissible omega :  liminf_t q^{pi*, omega}_t = 0 ,

which is self-referential — a property of the very policy whose success it
establishes — and therefore has to be verified against the closed loop rather than
read off a friction model.

So the honest position is: **the criterion becomes policy-relative.** In the
exogenous model it is a property of the world; in the closed loop it is a property
of a (policy, world) pair, and the theorem degenerates to "the threshold rule works
when the threshold rule sees dips".

## 3. What a usable closed-loop condition looks like

The condition worth having is a **forcing** one, because it is checkable against
the engine rather than against a policy's own trace.

**Definition (robust cheap-date recurrence).** From every reachable history `h` and
for every `k`, the controller has a strategy that, against every admissible
exterior continuation, reaches within finitely many dates a date whose friction is
at most `2^-k`, while spending no budget in the interim.

**Theorem C1.** Under robust cheap-date recurrence, persistence is achievable in
the closed loop on any positive budget.

*Proof.* Run the forcing strategies in sequence: from the current history, force a
date with friction at most `2^-k`, spend tranche `B 2^{-(k+1)}` there, and advance
`k`. Each stage terminates against every exterior by hypothesis, the tranches sum
to `B`, and each contributes at least a fixed positive allocation by the same
computation as O1. `square`

The hypothesis has the right shape for the engine to supply: it is a statement
about what the market and settlement can be made to do, not about a trace. It is
also visibly strong — it asks the controller to be able to *make* enforcement
cheap, and nothing in the round shows any traderized instance satisfies it.

**Where the exogenous model is a legitimate approximation.** If the friction is
*policy-stable* — every policy and exterior induces the same sequence up to a
uniform two-sided constant — then a dip for one is a dip for all, and S1 transfers
with the constants folded into the tranches. Two sufficient conditions for that,
neither established here: the ordinary volume bound `M_t` is a declared schedule
rather than a realized quantity, which is how the enforcement round's contract
actually states it; and the live set's evolution is driven by settlement that the
enforcement position does not influence, which is the deductive instance's
`PC(D_t)` and is *not* true on the empirical channel, where procedures are
funding-responsive.

The deductive instance therefore has a real claim to being exogenous, and the
empirical one does not. That is the sharpest scoping statement available.

## 4. The hierarchy

Recording it explicitly so later work cannot import a benchmark result into the
closed loop.

| level | model | status |
|---|---|---|
| **E0** | fixed-era construction/composition | frozen; `FIXED_ERA_THEOREM.md` |
| **E1** | exogenous friction, conservative charge | exact: `liminf q_t = 0`; online equals offline |
| **E2** | exogenous friction, sharp robust charge | exact: `liminf L_t(1) = 0`, equivalently `liminf min(s_t^2, s_t sqrt(m_t)) = 0`, which reduces to `liminf s_t = 0` exactly under an engine-scale floor `m_t >= m_0 > 0`; `SHARP_PERSISTENCE.md` Lemma S3 |
| **E3** | E1/E2 intersected with Answerability's admissible traces | partial: a per-window floor needs summable window minima; `SERVICE_ADMISSIBLE_EXISTENCE.md` |
| **E4** | policy-dependent friction, closed loop | open; C1 is a sufficient forcing condition with no instance |
| **E5** | signed-account robust scheduling | open; needs a predictable account-drift lower bound |

E1 and E2 are complete. E3 has one theorem and a frontier. E4 and E5 have a
statement of what would be needed and nothing more.

## 5. What this does not establish

That any traderized instance satisfies robust cheap-date recurrence. That the
deductive channel's friction really is policy-independent — the argument in §3 is
that settlement there is not funding-responsive, which is a reading of the
settlement interface's completeness clause and not a theorem. That E4 is harder
than E3; both are open and they are open for different reasons.
