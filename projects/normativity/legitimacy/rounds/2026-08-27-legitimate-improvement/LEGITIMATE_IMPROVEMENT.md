# Legitimate Improvement: No Free Evasion of a Demonstrated Repair

Status: **specification, reference models and a prosecution record;
unregistered.** All names provisional under `AGENTS.md` §6. No Lean, no
registered claim.

Frozen Legitimate Evolution is untouched: `replay.py` and `answer.py` are
imported unchanged, and `TestFrozenLEIsUntouched` asserts by AST parse that only
their public interface is read.

## Verdict

```text
NO-FREE-EVASION-SURVIVES-BUT-EVIDENCE-INTERFACE-OPEN
```

Theorem C survives the prosecution and is now stated over the right objects. Two
implementation bugs are fixed and one headline claim is corrected. What is not
yet clean enough to freeze is the meaning of *demonstrated improvement*: the
verdict depends on a baseline the round supplies rather than derives, and one
trace with two admissible baselines produces two opposite verdicts.

## 1. The problem

Legitimate Evolution gives integrity without improvement. It says a process
cannot manufacture entitlement or silently erase what it owes; it says nothing
about getting better.

The obvious composition fails for an obvious reason. Let a repair prove itself,
then legitimately retire it, and the old conduct continues forever with repair
regret going to zero — because there is no longer anything to compare against.
Changing the comparison surface is not cheating. It is a legitimate normative
act, and it makes the learning guarantee vacuous exactly when it would bite.

## 2. The central result

> Once an improvement has been **demonstrated** on the process's own record,
> withdrawing the comparison does not end the matter. Every later diagnosed
> occasion is one the process is either still answerable for, or has explicitly
> answered.

This is an accounting statement, not a second bound. It does not say the repair
must be adopted, does not say a refusal is wrong, and does not limit how long a
process may contest. It says there is nowhere else for the conduct to go.

What connects a single retirement to an unbounded later stream is **not**
counting retirement events, which cannot work. The later occasions are covered
because the claim is *outstanding at each of them* — frozen `A1` doing the work.
CM3 runs 340 diagnosed occasions under one opened claim.

## 3. Three mechanisms, and keeping them apart

This is the pass's main repair. The round's first version ran the second
mechanism and called it the first.

```text
EVIDENCE       why r is an improvement, and relative to what baseline
UPTAKE REGRET  while r is live, is the played policy leaving that unused
ANSWERABILITY  after r is withdrawn, what remains normatively live
```

Evidence and uptake regret are the **same functional on different
distributions**:

```text
adv(d) = <d, l> - <d M_r, l>

d = p_t   the played distribution   -> uptake regret.  Theorem A bounds it.
d = b_t   a supplied baseline       -> evidence.  Nothing bounds it.
```

They are independent, and both directions are executed:

- **CM15** — the process *adopts* the repair the whole time it is live. Uptake
  regret is exactly `0.000`; evidence is `48.0` and the improvement is
  demonstrated; withdrawal is still contested. The old architecture could not
  express this case at all.
- **CM16** — the process leaves advantage unused, so uptake regret is positive,
  but the per-occasion gain never reaches the constitution's threshold. No
  challenge is eligible. **Regret without a demonstration grounds nothing.**

So the challenge is grounded by the demonstration, never by the process having
failed to act on it. A process that adopted the repair and then withdrew it owes
the same answer as one that never adopted it. `challenge.py` names no regret
quantity at all, asserted by parsing.

```text
comparative evidence
        |
        v
demonstrated improvement  ---- r stays live ----> uptake regret governs non-uptake
        |
        `-------------------- surface withdraws --> LE answerability governs it
```

## 4. Theorem A — opportunity-adaptive uptake regret

For predictable `(I, f)`, anytime and parameter-free, simultaneously over a
countable class with prior `q`:

```text
Adv_T(I,f) <= sqrt( 3 C_T(I,f) ( ln(1/q(I,f)) + ln B + ln(1+ln n) ) )
C_T(I,f)   =  sum_t I(t) | p_t^T (M_f - 1) l_t |   <=   W_T(I) = sum_t I(t)
B          =  1 + (3/2) sum_i q_i (1 + ln(1 + C_{T,i}))
```

Hypotheses, and what forces each:

```text
predictable I, f, b   otherwise `act` is uncomputable and the baseline can be
                      chosen in hindsight
losses in [0,1]       gives C <= W, the opportunity-mass corollary
full information      both b_t and b_t M_r are scored from one loss vector
the process runs it   without it there is no learning theorem to compose with
```

## 5. Theorem B — the correctable-defect adapter

Given a consumer witness `Adv_T(I,r) >= eps * D_live - xi_T`,

```text
D_live <= ( B_T + xi_T ) / eps
```

Two lines of algebra. **CM18 is the first fixture that exercises it**: a
no-regret process retaining `D_live = 0.86` with Theorem A holding. The bound is
`4803` — finite, correct and very loose, because the realized margin `eps` is
small. Reported rather than tuned.

## 6. Theorem C — No Free Evasion

```text
D = D_live + D_contested + D_settled + D_escaped
```

> **Theorem C.** If a repair's evidence episode was demonstrated immediately
> before the surface withdrew it, and the constitution activates a challenge on
> that withdrawal, then from that point `D_escaped = 0`.

*Proof.* The canonical constitution activates a claim at the withdrawal; frozen
`D1` conformance makes it incurred; frozen `A1` says an incurred claim leaves the
outstanding set only through an accepted `Resolve`. So at every later occasion
the claim is outstanding or resolved. ∎

The theorem is **post-demonstration and post-withdrawal**. The `LIVE` cell
belongs to Theorem B and to a different mechanism; it is retained in the
partition because the accounting must be exhaustive over all diagnosed mass, not
because it is part of the same claim.

**`D_escaped` is representable and non-empty.** Exactly two fixtures land in it,
CM2 and CM16, and both are cases where the improvement was never demonstrated —
which is the theorem's own hypothesis failing, not a leak.
`test_only_undemonstrated_withdrawals_escape` asserts that equivalence.

## 7. What the prosecution found

### Two implementation bugs

**The fixed point was computed by power iteration**, justified by the matrix
being stochastic. That justification is false: a finite stochastic matrix may be
periodic. The kernel `A->B, B->A, C->A` is period 2, and the shipped code
returned a vector with `||p - pM||_1 = 2/3`. Replaced by an exact linear solve,
with a recurrent-class solve when the system is singular and a Cesàro fallback
that is never reached in the fixtures. Every occasion in every countermodel is
now verified stationary to `1e-6`.

Uniqueness is **not** assumed and is not needed: the reduction requires only that
`p_t` satisfy the fixed-point equation, and Khot–Ponnuswami's equation (5) uses
only that, never which solution.

**AdaNormalHedge's `B` was computed from one expert's own `C`.** The paper's `B`
is global and prior-weighted over all experts. With `C_i = 1` and `C_j = 10000`
the two differ by a factor of three. The old expression *understated* the bound,
so no test was wrong — but the code claimed to be the theorem and was not.

### One headline claim corrected

The round claimed a surgical repair empties the diagnosed action because
`pi(d) = pi(d) M(d,d)`. That drops the inflow term. Stationarity is
`pi(d) = sum_a pi(a) M(a,d)`, and the class `{d->good, c->d, good->c}` is
irreducible and gives `pi(d) = 1/3` however surgical the repair is (CM14, exact,
residual `0`). The surviving statement carries its side condition:

> If no active comparator maps another action into `d`, and some active
> comparator moves `d` elsewhere, then `pi(d) = 0`.

This correction is what made CM18 constructible, so it turned a claimed absence
of content for Theorem B into an actual exercise of it.

## 8. The open seam: what is a baseline?

Five candidates were prosecuted. None is privileged, so `evidence.Baseline` is a
parameter with two checkable conditions — predictable, and committed before the
loss. Predictability is what stops hindsight construction of an embarrassing
baseline, and `predictability_violations` now checks baselines with the same
probe it uses for selectors and repairs.

**This is why the verdict is not `PR60-CLEAN-MERGEABLE`.** CM17 runs one trace
against two admissible baselines:

```text
baseline = unmodified conduct   evidence 48.0, demonstrated, contested 180
baseline = already-good policy  evidence  0.0, not demonstrated, escaped 180
```

Same process, same losses, same withdrawal, opposite verdicts. The baseline is
doing substantive normative work, and the round supplies it rather than deriving
it. `BASE_POLICY` is a fixture choice and is **not frozen**.

## 9. Boundaries, held open on purpose

**Pre-demonstration suppression (CM2).** Retire before evidence accumulates and
there is no demand. The missing premise, stated behaviourally: *candidate
improvements that remain relevant receive enough non-manipulated exposure to
become demonstrable if they really have persistent advantage.* That is not
ordinary external-world Coverage — the repair is represented and the contexts are
visible. It is closer to **exploration or evidence-production suppression**, and
the round declines to force it under Coverage's label.

**Evaluator shedding (CM5).** The repair stays live and the evaluator stops
scoring it as better. Nothing in the record distinguishes *the repair stopped
helping* from *we changed what counts as help*. CM5 activates no challenge and
lands in no cell — it is outside the retirement mechanism entirely, not caught by
it. Era locking is **not** a solution while the same process writes the evaluator
before choosing its action. A separate evaluation-integrity seam.

**Indefinite contest (CM8).** Permitted. A quantitative liability premise would
be needed to close it, and none is claimed.

**Trivial settlement (CM7).** `SETTLED` means an explicit accepted resolution,
never that the resolution is any good.

**Delayed and policy effects (CM10).** The negative consumer has no force, and
that is a success condition.

## 10. Export property

> A process that has demonstrated on its own record that an available alternative
> would do better, and then changes its arrangements so that the alternative is
> no longer available for comparison, does not thereby end the matter. Until it
> takes the alternative up or explicitly answers for refusing it, it stands in an
> unanswered demand of its own making.

It does **not** imply: that every demonstrated repair must stay licensed; that
every one must eventually be adopted; that any refusal is wrong; that every
retirement is Due; that unresolved demand is bounded; or that the evidence
semantics is manipulation-proof.

The name `No Free Evasion` is kept. `Answerable Improvement` describes the
conclusion but loses the point that the *evasion* is what fails, not the
withdrawal.

## 11. Literature

```text
imported     Khot-Ponnuswami Thm 3, eqs (1),(3),(4),(5). Experts indexed by
             pairs (I,f); time selection real-valued in [0,1]; their external
             learner takes losses in [-1,+1]
imported     AdaNormalHedge: potential Phi(R,C)=exp([R]_+^2/3C), weight
             w = (Phi(R+1,C+1)-Phi(R-1,C+1))/2, Thm 1's C_T bound, Thm 3's
             confidence-rated form with r_{t,i} = I_{t,i}(lhat_t - l_{t,i})
re-derived   the composition, below
not fetched  Blum-Mansour 2007, cited only for the model KP improve on
```

**The `[-1,+1]` step, written out.** AdaNormalHedge's analysis is stated for
losses in `[0,1]`, and the reduction emits `l'_t(I,f) = I(t) p_t^T(M_f-1)l_t` in
`[-1,+1]`. What the drifting-game argument uses is not the loss range but
`|r_{t,i}| <= 1`, since the potential is evaluated at `R±1` and `C+1`. Here
KP's equation (5) gives `sum_{(I,f)} q_t(I,f) l'_t(I,f) = 0`, so the inner
player's own loss is identically zero and `r_{t,i} = 0 - l'_t(i) = -l'_t(i)`,
whence `|r_{t,i}| = |l'_t(i)| <= 1` because `I(t) <= 1` and
`|p^T(M_f-1)l| <= 1` for `l` in `[0,1]`. The hypothesis the analysis needs is
therefore met verbatim. This is a short adaptation, not a cited theorem, and it
is marked as such.

**The effective mass.** Because `lhat_t = 0`, ANH's adaptive quantity collapses
to `C_T(I,f) = sum_t I(t)|p_t^T(M_f-1)l_t|` — neither
`sum_t I(t) 1[f != id]` nor `sum_t I(t) sum_a p_t(a) 1[f(a) != a]`. CM9 separates
them: a repair moving real probability across actions of equal loss scores full
under both and exactly zero under this one.

Novelty in the learning kernel is low: two published results, a sign check and a
range adaptation. The new content is §§3, 6 and 8.

## 12. Freeze recommendation

```text
FREEZE
  evidence, uptake regret and answerability are three distinct interfaces
  they are one functional on different distributions
  the challenge is grounded by demonstration, never by uptake regret
  regret governs only live comparisons
  C_T = sum_t I(t)|p^T(M_f-1)l| , and it is neither proposed definition
  SETTLED means explicit accepted resolution, not correctness
  the stationary distribution must be solved, not iterated
  the surgical corollary requires the no-inflow side condition
  pre-demonstration suppression and evaluator manipulation are separate seams

KEEP PROVISIONAL
  the baseline interface and which baseline is right          -- CM17
  the evidence threshold semantics
  the challenge key (repair identity, evidence episode)
  designation as part of the comparison surface
  Theorem B's consumer class; one loose fixture is not a class
  anything about human or H+ instantiation
```

## 13. What no claim above asserts

- No claim that recurrent defects disappear. CM8 contests forever and satisfies
  everything.
- No claim of policy regret, convergence, or eventual adoption.
- No claim about delay. `tau_t = 0`; the anchor is carried, not used.
- No claim that evaluator manipulation is addressed.
- No claim that the CM17 baselines are equally *reasonable* — only that both are
  admissible under the stated conditions, which is enough to make the seam open.
- No claim that the RI sidecar is built.
