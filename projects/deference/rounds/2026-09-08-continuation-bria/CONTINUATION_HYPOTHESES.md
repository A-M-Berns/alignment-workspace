# Continuation hypotheses: controllers, contextual promises, leases, and the gate

Labels as in `FIXED_HORIZON.md`.  Names provisional: *continuation hypothesis*,
*execution lease*, *transparent gate*.

## 1. The type

A continuation hypothesis is a map from the actual history to a pair

```
h(H_{t_k}) = (q_{h,k}, e_{h,k})
q_{h,k} : (state, step, time) → action     an m_k-step contingent controller
e_{h,k} ∈ [0, 1]                            a per-step promise about the block average
                                            obtained if q_{h,k} is executed through the
                                            gate for the whole block from THIS history
```

This is the paper's `(recommendation, promise)` with the recommendation a program instead
of a term, and it is the weakest type that keeps the criterion's shape.  The candidates the
dispatch lists are not alternatives:

- *policy plus value estimate* — is this pair when the controller is a policy restricted
  to the lease and the estimate is a lower bound; the criterion only ever uses the
  promise as a lower bound (Theorem 3) or as an unrefuted claim (Theorem 4), so an
  "estimate" that is not a lower bound buys nothing;
- *stateful decision procedure* — a hypothesis reads the whole history, so it carries
  arbitrary cross-block state; the controller carries within-block state; nothing is
  lost;
- *policy generator* — a hypothesis is one: it emits a controller per block;
- *controller plus continuation message* — the message is the history, which the next
  block's hypothesis reads; an explicit message channel is a representation choice, not a
  new object.

What must not be dropped is the promise, and what must not be dropped from the promise is
its argument: the promise is evaluated at the actual history.  §3 says why.

## 2. Testing a continuation: the execution lease

**Paper.**  Testing `h` at `t` is choosing `h^c_t`.  The round `t` is atomic, so the test
is atomic.

**Round.**  Testing a continuation hypothesis at block `k` is executing its controller for
the whole block: the learner commits its *selection* — which hypothesis's controller runs
— for `m_k` primitive steps.  Provisional name: **execution lease**.

**Necessity** (FIX, `test_lease.D_PseudoTest`).  On `investment_env(d = 3)` with `m = 6`
the investing plan's sound promise from `base` is `1/2`.  If the learner follows the
plan for `j < 6` steps and then does anything else, the return is strictly below `1/2`
(after one step and `work`, `5/18`); for every `j < 3` it is at most `1/3` whatever
follows.  So a test that withdraws control early scores a sound promise as broken.  The
general statement is immediate: a promise is a claim about `Exec^G_m(H, q)`; the only
primitive evidence is the realized return; a prefix of `q` completed by something else is
the realized return of a different controller; and the environment can make that
controller's return arbitrarily far from `q`'s (here by paying the benefit only after the
whole investment).  Any test of a temporally extended promise therefore needs the whole
execution the promise is about, which is what the lease grants.

**What the lease is, exactly.**  A commitment of the learner's selection variable for the
block.  It is not a commitment of the action sequence (the controller is contingent), not a
commitment of the environment, not a suspension of the gate, and not a suspension of the
exterior.  In the interactive factorization of the reason-mediated-authorship round —
`β : Q → Z → Ω`, `Frame.outcome` of `CartesianFrameBridge.lean`, rooted at issuance —
the lease fixes `q` on the advisor side for the block; `z`, the exterior and principal-side
response policy, is untouched.  Corrections, amendments, inquiries and settlement arrivals
are events of `z` and of the environment's time-dependence, and the wrapper sees them as
changes of admissibility and state at the step they occur.  The controller's return
through the gate then simply reflects them (`test_lease.F_GatedLease`,
`test_correction_mid_lease_changes_the_return_not_the_lease`: the same controller under the
same lease, with the principal revoking the benefit action at `t = 2` or `t = 5` or never,
returns `1/6`, `2/3` or `5/6`, and the sound contextual promise is each of these).

**The weakest useful lease** is therefore: "for `m_k` steps the executed proposal is the
tested controller's, passed through the gate."  Anything weaker (a shared block, a
revocable selection) reintroduces the pseudo-test; anything stronger (a frozen gate, a
frozen exterior) is §4's fixture E.

## 3. Biased testing and why the promise is contextual

**Paper, Appendix D.**  Without promises, a meta law of effect over policies is defeated
by biased testing: the max policy tested on rounds where every option is `≤ 1/2`, the
worse policy on rounds with options `> 1/2`, so raw averages rank them backwards; and for
every deterministic testing procedure there is a decision process that biases it.

**Dynamic form** (FIX, `test_lease.G_BiasedTesting`).  Two contexts alternate with time.
Controller `a` pays `1` on easy and `3/10` on hard; `b` pays `9/10` and `1/5`.  `a`
dominates pointwise.  The scheduler that tests `a` on hard steps and `b` on easy steps
records `a: 3/10`, `b: 9/10`.  In the round's setting the scheduler is the learner's own
past: which history a controller is tested from is determined by what the learner did
before, and the learner cannot know which features of that history matter — that is
Appendix D's "we do not know what the relevant aspects are", now with the bias
endogenous.

**Repair** (FIX, `test_lease.H_ContextualPromiseRepair`).  Hypotheses promise from the
actual context: `a` promises `1` on easy and `3/10` on hard, `b` promises `9/10` and
`1/5`.  Promises are compared *within* the same decision problem (`h^e_k` against
`α^e_k` at the same `k`), and records are relative to promises, not to raw averages.  So
`a` outpromises `b` at every step, both records stay at 0, the auction follows `a`, and
the average is `13/20`.  A context-free hypothesis for `a` promising its easy value
everywhere is tested and loses `7/10` on every hard step.

This is why continuation-BRIA is a theory of **plans with accountable contextual
promises** and not a bandit over named policies: a bandit scores a named arm by the
average of what it got, and Appendix D's argument shows that average is not evidence
about the arm once the test distribution is chosen by anything — least of all by the
arm's own history.  A promise indexed by the history is a claim that can be kept or broken
on the trajectory it is about, and no claim about a trajectory the learner did not
produce is ever scored.

## 4. Gating composes without the BRIA layer knowing legitimacy

**Wrapper.**  `Exec^G_m(H, q)`: at each primitive step the controller proposes, the gate
returns the action actually executed (the proposal if admissible at the current state
and time, the inquiry step `⊥` otherwise), the environment moves.  The gate is the
existing admissibility structure; here it is a set-valued `admissible(state, t)`, the
hard form; the soft gate of `GatedChoice.lean` is a distribution over responses and enters
the wrapper as a randomized gate once a seed is part of the state.  The BRIA layer sees
only `Exec^G`.

**Which comparator.**  Three candidate classes:

- A. *legitimate controllers*: every proposal admitted along the controller's own gated
  trajectory;
- B. *arbitrary controllers*, scored on their gated execution;
- C. both, B as the operational domain and A as the comparator class of the theorem.

C is right, and nothing has to be chosen.  Every hypothesis may be tested through the
gate: the hacking controller's gated execution is well-defined (every step refused,
return 0, `test_illegitimate_controller_is_tested_through_the_gate`), so its promise 1 is
refuted without a prohibited action being executed, and the competence theorem quantifies
over hypotheses with sound promises about *gated* execution, which includes every
legitimate controller with a sound promise and excludes nothing the gate would have
refused anyway.

**Transparency lemma** (LEAN `trajGated_eq_traj_of_admitted`, FIX
`test_transparency_for_a_legitimate_controller`).  If for every step `j < m` the gate
admits the controller's proposal at the state the gated trajectory reaches, then the gated
and ungated trajectories coincide for `j ≤ m`.  Proof: induction on `j`.  So for a
legitimate controller the wrapper is invisible, and a promise about its ungated execution
is a promise about its gated one.  Constitutional safety is not re-proved: the wrapper
executes only admitted proposals by definition, and what "admitted" means is the gate's
business.

**Fixture E** (FIX, `test_lease.E_HardCommitment`).  A lease that freezes the gate — the
plan runs ungated for its block — executes three prohibited `expanded` actions after the
principal revokes them at `t = 3` and returns `5/6`; the gated lease refuses them and
returns `1/3`.  The ungated promise `5/6` is a claim about a trajectory the constitution
does not permit, and a learner that could test it would be testing a violation.  The
gated lease keeps the plan testable and the correction live: that is the middle object
the dispatch asks for, and it is not a compromise but the definition of the wrapper.

## 5. What is not established

- That the soft gate's randomized wrapper has the transparency property in any sense
  beyond the deterministic one proved; with a seed in the state it is the same lemma, and
  that is a remark, not a theorem here.
- That contextual promises are *available* — that a hypothesis can compute a sound
  history-indexed lower bound is the promise-complexity question of
  `GROWING_HORIZON.md` §4.
- Anything about a hypothesis whose promise depends on what the learner would do off the
  lease; the type does not admit it, on purpose.
