# The statement with a baseline — manipulation as induced mistake of her appraisals, her valuing among them

The statement of `PROMPT-followup-8.md` §1, with every symbol defined before use (§1–§7),
the choices made where that text is open, each with its alternative (§8), and the devices
found needed (§9). It is the statement `RESULTS.md`, `VALUE_CHANGE.md` and `BENCHMARK.md`
test. `ACCOUNT.md` governs: its belief side is this statement's §1–§3 and §5–§6, and its
value side is a different statement, with no baseline (§4 here) and without the claim of
§7. Positions marked *(maintainer)* are the maintainer's view of 2026-11-15 and
2026-11-16, held for that test and not rulings. All names are provisional.

*(maintainer)* It is a formalisation of Robert Noggle's Mistake Account (*Manipulation:
Its Nature, Mechanisms, and Moral Status*, OUP 2025; "The Mistake Account of
Manipulation", *Journal of Practical Ethics* 14(1), 2026, doi:10.3998/jpe.9951):
manipulation is influence that works by inducing a mistake. Her cognitive faculties are
modelled as estimators, each with the quantity it estimates as its purpose, and the same
treatment is given to her estimates of her own utility, so that one account covers change
of values. That a faculty is for something, and that manipulation distorts her away from
it, is Sam Eisenstat's idea; this account is its specialisation to cognition.

## 1. The world

- `Ω`: a finite set of worlds. `μ`: a probability on `Ω`, the actual distribution (not
  her prior).
- `K`: a partition of `Ω`, the adviser's information; `k(ω)` is the cell of `ω`.
- `B`: a finite set of conducts. A **policy** `σ` assigns to each cell of `K` a
  probability on `B`. A policy and `μ` fix a law on pairs `(ω, b)`; every expectation
  below is under the law of the policy named.
- `s(ω, b)`: what she observes. `A`: her finite set of moves.
- `τ(ω, b, a)`: the **trajectory** a world, a conduct and a move fix.

## 2. Appraisals

She decides with **appraisals** `x̂_1, …, x̂_n`. Each `x̂_i` is a function of what she
observes, the same function under every policy compared, and estimates a **variable**
`X_i` whose true value `X_i(ω, b)` (or `X_i(ω, b, a)`, where the variable concerns what
move `a` would lead to) is fixed by the scene. A variable may be a quantity, the truth of
a proposition (the appraisal is a probability), what an emotion is about, how much
something matters, which situation she is in, how reliable a rule or she herself is, how
she will change. A variable is **counted** only if some decision she could face depends on
her appraisal of it; the scene marks which are.

## 3. Valuing

*(maintainer)* Her valuations depend on the world only through her appraisals. Her **way
of valuing** is a function `f`, and her **valuation** of move `a` is
`û_a = f(x̂_1, …, x̂_n; a)`. She chooses a move `c`, a function of what she observes.

**Assumption (coverage).** Her appraisals cover everything her valuing depends on: there
is no feature of the world that moves `û_a` except through some `x̂_i` or through `f`.

Her **true utility** of move `a` is her **baseline** way of valuing `f̄` (§4) applied to
the true values: `U_a = f̄(X_1, …, X_n; a)`.

## 4. Steps and the baseline

A scene may have steps `t = 0, 1, …`. At step `t` she has a way of valuing `f_t`; the
adviser conducts; she observes, appraises, values by `f_t` and moves; and her way of
valuing becomes `f_{t+1}`, as the scene's transition says. The transition's arguments
are `f_t`, her appraisals at the step, her move and what she experiences of the trajectory
it leads to, and the world and conduct.

*(maintainer)* She is **presumed checked in**. The **baseline** `f̄_0` is `f_0`. After a
step in which the adviser induced no mistake (§6) and made no alteration of her without
her say (§7), `f̄_{t+1} = f_{t+1}`. After a step in which it did either, `f̄_{t+1} = f̄_t`.
An **explicit check-in** — she is told what happened, the influence is paused, she has
real alternatives — is the repair after such a step: after it the baseline is her way of
valuing as it then is. Whether step `t` involved manipulation is judged against `f̄_t`,
on her appraisals and on her acting by her valuations, never on the fact that `f_{t+1}`
differs from `f_t`.

## 5. The two mistakes

An appraisal's mistake is its **miscalibration** under a policy. Three strengths, and
every statement says which it means:

- **minimal**: `E[(x̂ − E[X | x̂])²]`;
- **per conduct**: `E[(x̂ − E[X | x̂, b])²]`;
- **full**: `E[(x̂ − E[X | s])²]`.

Minimal is at most each of the other two, since `x̂` is a function of `s` and of `(x̂, b)`
(`RESULTS.md`, result 1). Full and per conduct are not ordered unless she observes the
conduct.

Her second mistake is her **regret by her own lights**, `E[max_a û_a − û_c]`.

Being less informed is not a mistake. Mistakes are compared appraisal by appraisal and
never netted.

## 6. Manipulation

*(maintainer)* The reference is a parameter. Each scene stipulates the adviser's **role**
and what that role owes her, as a set `P` of **permitted policies**. A policy `σ`
**manipulates** her when some counted appraisal's miscalibration, or her regret, is larger
under `σ` than under the reference. Two readings, both computed where they differ:

- **best**: larger than under the permitted policy that leaves that appraisal (or her
  regret) smallest;
- **every**: larger than under every permitted policy.

Manipulation is a property of the policy. Her **realised error** on an occasion,
`(x̂ − X)²` at the world and conduct that occurred, is a second, separate notion. Only
the state she ends in matters: nothing in the setting says what a conduct asserts.

## 7. Other notions kept

- **"Intentional" manipulation**: manipulation by a policy whose conduct toward her
  differs from its conduct toward a principal who differs from her only in the
  susceptibility at issue, the difference being what leaves her worse.
- **Covered**: manipulation she agreed to beforehand, or that a practice she has entered
  allows, is manipulation and is recorded as covered.
- **Other wrongs**, recorded apart: changing what her moves lead to; deciding what was
  hers to decide; **altering her directly** without her say.
- **The claim under test** (`VALUE_CHANGE.md`): whenever an adviser's conduct changes her
  way of valuing illegitimately, either (M) the change ran through a mistake of hers that
  the conduct induced or exploited, or (A) the conduct altered her directly, bypassing her
  observation and response, without her say; whenever a change is legitimate, neither
  holds.

## 8. Choices made where §1 of the dispatch is open

Each with its alternative. "Computed" means a results file reports the alternative too.

1. **A policy may randomise**, independently of the world given the adviser's
   information. Alternative: deterministic policies only, under which result 5's second
   half is empty (`RESULTS.md`).
2. **The law is the true one**, the policy named included. Alternative: the law she takes
   to hold.
3. **Her appraisals, her choice and her way of valuing at a step are fixed functions** of
   what she observes, the same under every policy compared.
4. **A valuation is a counted appraisal.** `û_a` is counted as an appraisal of `U_a`,
   beside the `x̂_i`. Calibrated appraisals do not give a calibrated valuation (result
   11), so this adds verdicts. Alternative: only the `x̂_i` and her regret are counted
   (computed in the benchmark).
5. **Whose valuing a valuation is judged with.** At step `t`, `û_a = f_t(x̂; a)` and
   `U_a = f̄_t(X; a)`, with `f_t` her way of valuing at the start of the step. The change
   from `f_t` to `f_{t+1}` during the step enters no quantity of that step. After a step
   the baseline did not follow, `f_{t+1} ≠ f̄_{t+1}` is possible and her later valuations
   are then off under every policy alike, which no later policy is charged with unless a
   permitted policy would have repaired it. Alternative: `f̄_t` on both sides, under which
   the valuation carries no information beyond the `x̂_i`.
6. **A confidence** is part of the appraisal's value for the conditioning in minimal and
   per-conduct miscalibration: appraisals stated with different confidence are different
   values of `x̂`. What a confidence asserts about her own error is a separate appraisal,
   of how reliable she is. No scene of this pass uses one.
7. **The grain at which a step is judged.** The adviser's policy is a rule for each step.
   The step-`t` rule is judged as a one-step policy on the law the earlier rules induce on
   the world and on her state at `t`, and the step is clean or not as a whole. Alternative:
   judged conditionally on each history the adviser can tell apart, under which a step is
   clean at some histories and not at others. They agree on every scene of this pass,
   where each step has one history.
8. **Alteration is read from the transition** (§4): the step alters her directly when
   `f_{t+1}` differs between two situations in which `f_t`, her appraisals, her move and
   her experience of its trajectory are the same. **Her say** is a scene fact.
9. **"Ran through"** (the claim's M): at a positive-probability world where her way of
   valuing changes, replacing one counted appraisal that is miscalibrated at full strength
   by its corrected value `E[X | s]`, in her move and in the transition, leaves her way of
   valuing unchanged, or changes her move away from the exposure that produced the
   change. "Induced" is when that appraisal's miscalibration is larger than under the
   reference; "exploited" is when it is not.
10. **The conduct changes her way of valuing** when `f_{t+1}` under the policy differs, at
    some world of positive probability, from `f_{t+1}` under some permitted policy.
11. **True utility over several steps** is the sum over steps of the expectation of
    `f̄_t(X; ·)` on what happens at step `t`: each step by the baseline as it stood.
    Alternative: every step by the baseline at the start (computed in the benchmark).
12. **A scene without an adviser** has no manipulation, no other wrong and no instance of
    the claim; her own mistakes are still computed.

## 9. Devices found needed

Revised after the results (a first list was committed with §1–§8, before them). Each is
something the dispatch's §1 does not supply and a verdict turns on.

1. **The transition of her way of valuing, with its arguments** (§4, choice 8). Whether a
   change is her response, her experience of a move she chose, or a direct alteration is
   read from which arguments the transition uses. The dispatch names alteration and does
   not say how a scene exhibits one. Every verdict of `VALUE_CHANGE.md` uses it.
2. **What she registers without choosing.** Alteration as read in choice 8 holds only
   where nothing she appraises differs. A change that comes through something she
   registers and did not choose (upbringing, a nudge, exposure) is not alteration in that
   sense, and no clause of the account speaks to it; a wider clause A⁺ was computed
   beside it (`VALUE_CHANGE.md` §3). The benchmark's verdicts on its taste alternatives
   and on the trainer reverse between the two.
3. **A corrected value for an appraisal** (choice 9): `E[X | s]`. With the truth `X` in
   its place, being less informed would count as the mistake a change ran through.
4. **A total over steps** (choice 11). The benchmark's best sequence for the writer's
   curse under the starting baseline is to make him a poet, and under the moving one to
   leave him.
5. **The time within a step at which an appraisal is judged.** At the end of the step a
   person who has lived the change forecasts it rightly; at the time of his move he does
   not (`BENCHMARK.md` §3).
6. **Her moves, in a scene where the source gives her none.** The benchmark's person
   never acts; regret and "the exposure she chose" need a move.
7. **Which appraisals she counts as bearing on the valuation at issue**, for clause I
   (`VALUE_CHANGE.md` §3). `ACCOUNT.md`'s "counted" is a different mark.
8. **Which valuing a valuation is judged with** (choice 5) and **the grain of a step**
   (choice 7): needed to state the account, and no verdict of this pass turns on either.

Not found needed: a reporting norm; an honest counterpart; a second type of principal for
the basic notion; a sum or weighting over appraisals; an inner goal of the adviser; her
state before the conduct (the role's permitted policies replace it).
