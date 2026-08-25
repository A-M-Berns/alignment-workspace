# Findings

Status: **round report; unregistered.** Names provisional.

## 1. Repository map, as consumed

| object | path | how used |
|---|---|---|
| Reflective Integrity core | `../2026-08-24-reflective-integrity-core/src/ri_core.py` | imported and run unmodified; supplies `L`, `R`, `N`, standing, `Std_t`, `good()` |
| RI specification | same directory, `REFLECTIVE_INTEGRITY_CORE.md` | §2 (MS), §11 (`PForce`), §33, §35 |
| reason state | `../2026-08-23-reason-representation/` | read; the defeat argument in `EXPRESSIVENESS.md` §4 rests on it |
| enforcement rows and trader | `../../../rounds/2026-08-16-traderized-enforcement/src/enforcement.py` | row sign convention and violation functional reproduced |
| deductive region | `.../src/deduction.py`, `Contrib/DeductiveRegion.lean` | the admissible-pattern construction |
| force interface | `.../src/force_api.py`, `FORCE_INTERFACE.md` | `compile_safe_force` is the path every charged date takes |
| liability | `.../src/outflow.py`, `FUNDING_AND_SAFETY.md` | `LiveDeficitCertificate.by_enumeration`, `charge`, `OutflowAccount` — imported and called, not reimplemented |
| projection | `../../../rounds/2026-08-18-projection-enforcement/src/projection.py` | the variational-inequality projection certificate |
| schedule and end-to-end theorem | `lean/Workspace/Normativity/Contrib/{ConstraintSchedule,RationalPolytope,EffectiveRepresentation}.lean` | the actual traderization hypotheses |
| Fourier-Motzkin | `Contrib/FourierMotzkin.lean` | the constraint representation, extended here with multipliers |
| Logical Induction | pinned FAF `c0d885bfb2f84054ada18c65acec672e04d6d380` | `LUV`, `expect`, `expectAffine`, `AffineCombination`, `PCWorld`, `DeductiveProcess` |

**Dependency direction.** The slice imports two sibling rounds' `src/` at run
time: the Reflective Integrity reference model, and the traderized-enforcement
sources for everything the safety layer owns — `Region`, `Row`,
`LiveDeficitCertificate`, `charge`, `OutflowAccount`, `compile_safe_force`,
`world_deficit`. **No liability quantity is reimplemented here.** The projection
certificate is the one exception and is reproduced rather than imported, with
that stated at its definition.

## 2. What the original LI machinery bought

More than expected, and this is the round's most reassuring finding.

`E_n(X)` needed no new construction. The pinned dependency already carries
`LUV.expectAffine k = sum_{i<k} (1/k) <X > i/k>` and the lemma
`expectAffine_price : (X.expectAffine (n+1)).price P n = X.expect P n`. So the
compilation of the cognitive waist to price geometry is **not a bridge this
round built** — it is a definition already in the substrate, and the waist's
job reduces to naming it.

`LUVCombination` and `meshAffine` go further: an affine combination of LUVs with
its expansion into a threshold bundle is already a type there. The operative
waist's inequality is a `LUVCombination` extended with plain sentence terms, and
`AffineCombination` — `const + sum e_i phi_i` over sentences — already subsumes
both `Prob` and the expansion of `Expect`.

Consequence for the design question: **`CognitiveQuantity` is not a new common
language, it is a naming of one that exists.** That is the strongest available
evidence that the cognitive waist is at the right level, and it is evidence of a
kind that could not have been obtained without reading the dependency.

## 3. The V / L relationship, as far as the code permits

`L_min(V)` was not needed in the strong form the dispatch anticipated, and the
reason is instructive.

Nothing in the pipeline requires an LI sentence whose propositional meaning *is*
a reason `r in V`. Reasons are consumed by `basis(a) = ReasonLeaves(D_a)`, which
compares identifiers; the compiler never sees `V` at all. What must be
representable in `L` is not `V` but three things:

1. the threshold families of every exposed quantity — `sem_L`'s and the value
   layer's shared vocabulary;
2. whatever ordinary propositions injunctions name in `Prob` terms;
3. the sentence content of settlements.

None of these is a translation of `V`. Ordinary effective coding is enough,
because the only thing crossing the boundary is a *name* — a specification id
and a query code, which determine a threshold family — and names are cheap to
code.

So the relationship the slice actually uses is weaker than `L in Ext(L_min(V))`
and is closer to: `L` must be able to code the value layer's query vocabulary and
the settlement layer's readings, and `V` is otherwise opaque to it. Whether the
richer relationship is needed is untested here, because nothing in the toy
required reasoning *about* a reason inside the market. Filed rather than
resolved.

The distinction the dispatch asked to preserve — quoting `r` versus an `L`
sentence meaning `r` — is preserved trivially: the slice never does either.

## 4. Interfaces reused, and the three added

**Reused unchanged, by import:** `ri_core` in full; `PForce` as the injunction
payload; `enforcement.Region` and `Row`; `deduction.world_deficit`;
`outflow.LiveDeficitCertificate`, `charge` and `OutflowAccount`;
`force_api.compile_safe_force`. **Reused by reproduction:** the
admissible-pattern construction, and the variational-inequality projection
certificate. `RationalPolytope` is consumed as a possibly-redundant generating
list, which is what its two fields permit.

**Added:**

- `PValue(spec_id)`, a payload constructor. Costs the interpreter nothing —
  `delta`'s three clauses write `K_i` into a fresh standing state without
  inspecting it, so `Create` and `Supersede` are payload-polymorphic and no
  clause changes. Licensed by MS's conservative-extension rule.
- `sem_L`, a third parametric interpreter in the shape of `[[.]]_S` and
  `[[.]]_D`, with assumptions E1–E3.
- `kappa_n`, the compiler, which is `expectAffine` plus bookkeeping.

**Repaired locally:** the vertical-slice projection is `O_n = {(i, J_i)}`
rather than RI §35's `{compiledClause p}`. No store, constructor or conservation
law changes; the pairing is a richer read of the same fold.

## 5. The traderization assumptions, as they actually are

`end_to_end_of_constraints_effective` takes a `RationalConstraintSchedule` —
`coords` with `nodup`, `tol` with `tol_pos`, `region : RationalPolytope
(coords n).length` with `region_in_cube` — a `Computation` certificate, a
computable deductive process, and

```text
hadm : forall n (v : PCWorld), v.ConsistentWith (DP.D n) -> C.regionPred n v.payout
```

Three consequences the slice ran into.

**The region is a V-representation and nonemptiness is in the type.**
`RationalPolytope` carries `verts_ne`. An empty region has no value of the type,
so `K^N = {}` is refused before a schedule exists. That is right, and it locates
emptiness-checking upstream of the mechanism exactly where `FORCE_INTERFACE.md`
§3 already put it.

**Changing dimension is fine.** `coords : N -> List Sentence` and
`region : forall n, RationalPolytope (coords n).length` already allow the
fragment and its dimension to move with `n`, which is what the day-indexed
expectation forces. The slice's fragments have sizes 2, 3 and 4 across three
days and nothing objects.

**`hadm` is the wall.** See §6.

## 6. The inertness dichotomy, and what it leaves

The round's central negative result, found by running the machine rather than by
reading a statement.

> If every `Sigma_n`-consistent world satisfies every compiled row, then every
> vertex of `K^D_n` lies in `K^N_n`; `K^N_n` is an intersection of half-spaces
> and so convex; so `K^D_n subset K^N_n` and `K_n = K^D_n`.

`hadm` *is* that hypothesis. So an injunction satisfies it exactly when it makes
no difference to the price region, and **every operative injunction with content
falls outside the unconditional traderization theorem.** Checked on every
non-blocking case in the suite: admissibility passes exactly when
`deductively_inert` holds, exactly when `D_t = 0`, exactly when `K` equals `K^D`.
The converse direction is the same statement read backwards, since `K^D` is the
hull of the live patterns.

The biconditional is stated only where it applies. An unsatisfiable stage and an
empty demand are both refused earlier, and that ordering is load-bearing:
`isLogicalInductor_of_stage_unsatisfiable` would otherwise let a contradiction
report as maximal safety.

This is not a defect in the theorem. It says the theorem's scope is the
zero-liability calibration case — which is what `DEDUCTION_SPECIAL_CASE.md`
already says about deduction — and that the normative layer lives entirely in the
charged branch. What is new is that world-inclusivity and *operational inertness
relative to the epistemic substrate* are the same condition, so the charged
branch is not one option among several but the only one a normative source gets.

### 6.1 The charged branch, run

The slice runs it, on the safety layer's own objects. The rows go to
`compile_safe_force`, which computes `LiveDeficitCertificate.by_enumeration`
from the region it is about to enforce, charges, debits, and only then
constructs the position:

```text
D_t = max over omega live of sum_j d_{t,j}(omega)      q_t = (eps_t + M_t) D_t / delta_t
```

An earlier draft of this round computed `sum_omega max_j d_j(omega)` and called
it the exclusion depth. That is neither the sharp aggregate nor the conservative
one and is not a quantity the safety theorem mentions; it has been removed
rather than renamed, and `test_safety.py` pins that the billed figure is the
certificate's.

On the canonical trajectory the three days cost `303/40`, `303/40` and `101/20`
against an account of `25`, which the trace displays drawing down. No price is
produced on a date the account cannot fund.

### 6.2 What settlement buys — three claims, separated

The first draft of this round asserted that a fixed injunction gets cheaper as
the record settles. **That is false**, and the repair is the more interesting
result.

**A — fixed-request monotonicity holds.** For one fixed row presentation and
support, `Omega' subset Omega` gives `D(Omega') <= D(Omega)`, because `D` is a
maximum. This is the only monotonicity available and it is a statement about one
day.

**B — the cross-day version fails, and here is the witness.** A frozen
injunction over `Expect(X)` compiles to a different row system each day, and the
two live-world sets are patterns over *different fragments* — so the cross-day
comparison is not so much a monotonicity failure as a comparison between objects
of different types. The numbers then move the wrong way. With `Expect(X) <= 1/2`
frozen and a stage settling that the quantity is at most `1/2`:

| day | `k` | live worlds read `X` at | `D_n` | `q_n` |
|---|---|---|---|---|
| 1 | 2 | at most `1/2` | `0` | `0` |
| 2 | 3 | up to `2/3` | `1/6` | `101/60` |

because the precision-`k` reading of a value `x` is `ceil(x*k)/k`, which is **not
monotone in `k`**. A free day becomes a charged day with nothing unsettled, and
the deficit still rises when the day-2 stage is made strictly larger.

**C — the charge is not the deficit.** `q_t` also carries `eps_t`, `M_t` and
`delta_t`, so `D_t` falling does not make `q_t` fall.

What survives of the original intuition is narrow and worth keeping: *at a fixed
day*, settling removes live worlds and cannot raise the deficit, and a
settlement that decides what an injunction demands makes that day free — at
which point, by the dichotomy, the injunction is also inert. The slogan the
first draft reached for — force is priced at the gap between demand and
settlement — is true of one date and false as a claim about a trajectory.

### 6.3 Two further facts about the charge

**It is presentation-dependent.** `D_t` sums across rows before maximising over
worlds, so a demand stated twice costs twice while enforcing the same prices. A
summability question is therefore about a schedule of presentations, not of
regions, and a source can make its own force arbitrarily expensive by restating
it.

**The tolerance route is bounded.** A conformance promise above `1` says nothing
about a price in `[0,1]`, and `compile_safe_force` caps relaxation at `1`. While
`delta_t <= 1`, `q_t >= (eps_t + M_t) D_t`, so summability requires
`sum_t (eps_t + M_t) D_t < inf`. `trajectories.tolerance_route` shows the charge
falling as the tolerance loosens and then going constant at the ceiling.

### 6.4 Four trajectories, two convergent

| trajectory | what carries it | verdict |
|---|---|---|
| `settlement_closes_the_gap` | settlement removes every excluded world; the tail is exactly zero | converges |
| `pressure_decays` | `eps_t + M_t = 2^-t` while a live world is excluded at every date | converges |
| `tolerance_route` | `delta_t` rises to `1` and stops | diverges |
| `nothing_decays` | nothing decays; the account is exhausted at day 2 and force is withheld | diverges |

These are synthetic and none is a normative source anyone should believe in.
What they establish is that the mechanics run from normative standing through the
exact certificate to a cumulative account, in both directions, and that the
architecture withholds force rather than overspending.

## 7. What the adversarial cases refused, and where

| case | refused at | how |
|---|---|---|
| no inequality; constant-true; constant-false | the waist, `check_wellformed` | before compilation |
| inexact coefficient; non-quantity operand | the waist | before compilation |
| uncertified or unbounded LUV | the waist / `compile_value` | `NonExposure` or `MalformedInjunction` |
| query with no legitimate LUV | `compile_value` | `NonExposure`, non-destructive |
| rewriting a frozen specification | `ValueRegistry.admit` | `ValueError` |
| rewriting a settlement's denotation | `SettlementSemantics.admit` | `ValueError` |
| one injunction demanding both bounds | feasibility, per standing | Farkas over that standing's two indices |
| two injunctions with empty intersection | joint feasibility | Farkas naming both standings |
| region incompatible with deduction | the hull system | Farkas naming the injunction and the hull |
| two settlements that conflict | stage satisfiability | minimal conflicting source sets |
| settlement against the deductive channel | stage satisfiability | attribution names both channels |
| ambiguous observation | `sem_L` | denotes `{}`; removes no world |
| unrelated language growth | nothing — it passes | coordinates, rows, regions, depth all identical |
| reflective / future-price LUV | nothing — it passes | the waist does not inspect what a LUV is about |
| an ordinary contentful injunction | the **admissibility** obligation | §6 |

The pattern: every bad case is refused by a *named* boundary, and the boundaries
are at three distinct layers — syntax at the waist, feasibility at the compiler,
admissibility at the trader. Nothing had to be caught by an ad hoc check
inserted to make the toy work.

## 8. Implications for inquiry

The forward pipeline produced five conditions that are candidate sources of
internal pressure, and all five are already computed rather than needing new
machinery:

- `K^N_n = {}` with a certificate naming the responsible standings;
- `K^N_n ∩ K^D_n = {}` with a certificate naming the injunction and the hull;
- `PC(Sigma_n) = {}` with minimal conflicting source sets;
- a `LiveDeficitCertificate` with a positive aggregate, and the charge it implies;
- a charge history whose partial sums are not settling, and an account
  approaching exhaustion — which the slice already computes, since
  `OutflowAccount` carries the ledger;
- a date on which force was **withheld**, which is a stronger signal than an
  expensive one: the demand stood and the market was not moved;
- an active injunction whose LUV names a superseded value specification.

What the forward run says the return interface must **consume** is therefore a
certificate — a Farkas multiplier map, a source set, or a depth with its
excluded worlds — rather than a diagnosis. What it must **emit**, if the
prohibitions hold, is a reason occurrence and nothing more: none of the five may
mutate `N`, and the record already forbids it, since `Std_t` changes only through
`applyEffect` on a well-formed `Norm` step.

So the minimal generic structure the toy exhibits is:

```text
pipeline certificate  ->  pressure  ->  inquiry  ->  ReasonOcc  ->  possible NormEvent
       (computed)      (not a reason)            (a Reason step)   (a Norm step)
```

with `pressure != reason != normative revision` preserved by the step types
rather than by discipline. The gap is the middle arrow: nothing here says what
inquiry does with a certificate, and the round does not attempt it.

Three things the run says about that arrow, and they narrow it usefully.

A pressure signal firing on a positive deficit would fire on every contentful
injunction, since by §6 that is all of them. The signal has to be about the
*partial sums*, which is a property of a history rather than of a date.

The deficit is not monotone across days (§6.2), so a signal watching for `D_t`
to fall is watching for something that need not happen even when inquiry is
working. What an inquiry layer can be held to is the charge history, not the
per-date number.

And withholding is the sharpest signal the forward run produces: a date on which
the account could not fund the charge is a date on which normative standing was
unchanged and had no effect, which is exactly the condition a practice ought to
be answerable for noticing.

## 9. What this round does not establish

- **No Lean, no registered claim.** Every Lean declaration named is cited for its
  hypotheses. Nothing is proved against them.
- **The inertness dichotomy is a paper derivation checked on finite instances.**
  The argument is three lines and uses only convexity, but it is not mechanized,
  and `test_composition.py` verifies the coincidence on a sample rather than
  establishing it.
- **`E3` and effective presentation are declared.** No computability statement is
  made about any `Sigma` or schedule here.
- **The safety condition is open.** §6 says every normative source needs the
  charged branch; four synthetic trajectories are exhibited, two convergent and
  two not, and **no normative source is shown summable**. This is the round's
  largest gap and it is where the architecture's safety claim now sits.
- **The cross-day counterexample is a witness, not a characterisation.** It
  refutes cross-day monotonicity of `D`; nothing here says when `D` rises.
- **The model is finite and propositional.** Sentences are propositional
  formulas, LUVs are threshold families over atoms, and the first-order content
  the pinned dependency discloses as a modelling choice is not reconstructed.
- **The V/L relationship is under-tested**, because nothing in the toy required
  the market to reason about a reason. §3 states what was used, not what is
  needed.
- **Conflict jurisprudence is out of scope by construction**, and the round
  notes without answering that an empty demand leaves the system with no region
  to enforce until an event resolves it.
- **`sampled` is not `proved` anywhere.** The suite exercises the interfaces on
  finite exact instances and refutes; it establishes no universal.

## 10. WHAT THE END-TO-END BUILD TAUGHT US

Only what was not assumed at the start.

1. **Admissibility and inertness are the same condition.** The unconditional
   traderization theorem's hypothesis is satisfied exactly by injunctions that
   change nothing. Every contentful one is in the charged branch.

2. **The precision mesh can make a frozen injunction more expensive.** The
   precision-`k` reading of a value is `ceil(x*k)/k`, which is not monotone in
   `k`, so a demand met exactly at a coarse mesh is violated at a finer one. A
   free day becomes a charged day with nothing unsettled — which kills the
   obvious conjecture that settlement makes a fixed injunction cheaper over
   time. Only the fixed-day statement survives.

3. **`DeductiveProcess` is already the general substrate.** Two fields, no
   closure, no consistency, no proof-search requirement. `Sigma = D union
   Sem_L(L)` needs no new world semantics — the union form is what the type
   accepts, and `PC` distributes over it because `ConsistentWith` is a
   universal quantifier.

4. **An unsatisfiable stage silences the guarantees rather than breaking them.**
   `isLogicalInductor_of_stage_unsatisfiable` makes the criterion vacuously true,
   admissibility vacuously pass and the depth vacuously zero. A contradiction in
   the ledger reads as maximal safety unless satisfiability is checked
   separately.

5. **Append-only settlement is forced by the type, not chosen.** Retraction
   breaks `DeductiveProcess.mono` and leaves no object to hand a trader. If
   something can turn out false it was an observation, and the fallible layer
   upstream is `RawOutcome`.

6. **The operative waist is not an extension of Reflective Integrity.**
   `PForce` already exists, `Clause` is already opaque, `O_t` is already its
   projection. The proposed `PInjunction` would have duplicated a payload.

7. **The value waist is free.** `delta`'s clauses are payload-polymorphic, so a
   new `Payload` constructor changes no clause of `applyEffect` and no existing
   term.

8. **`O_t` drops the standing identity, and two consumers need it.** Enforcement
   provenance and per-term conflict attribution both fail on a set of clauses.

9. **`Expect(X)` is a name for something already in the substrate.**
   `expectAffine` and `expectAffine_price` are in the pinned dependency; the
   cognitive waist introduces no asset and builds no bridge.

10. **Emptiness is not expressible in the schedule type.** `RationalPolytope`
    carries `verts_ne`, so `K^N = {}` is refused before a schedule exists.

11. **`nodup` is a live constraint.** Two LUVs, or a `Prob` term, can name the
    same threshold sentence; coefficients must be merged or the schedule's own
    field is violated.

12. **The stage's threshold chain must cover every day's grid.** The grid moves
    with `n` and the stage does not; a threshold the chain misses is an
    unconstrained atom, and worlds appear in which the LUV has no reading as a
    number.

13. **Fourier-Motzkin gives conflict provenance for free.** Elimination combines
    constraints by positive multiples, so the derived contradiction arrives
    holding the Farkas certificate whose support names the injunction terms. No
    separate attribution mechanism is needed.

14. **Nonconvex permissibility is refused by the execution layer's geometry, not
    by the waist.** It is a limit on the architecture in a different place than
    this round was looking.

15. **The enforcement charge is a function of the presentation, not of the
    region.** Stating one demand twice doubles `D_t` and enforces exactly the
    same prices, because the sharp aggregate sums across rows before maximising
    over worlds. Whatever the summability condition turns out to require, it is
    a condition on a schedule of presentations.

16. **The tolerance route to summability is bounded above.** A promise looser
    than `1` is vacuous on prices in `[0,1]`, so while `delta_t <= 1` the charge
    dominates `(eps_t + M_t) D_t` and loosening buys a bounded factor and then
    stops.

17. **Live-world sets at different days are not comparable.** They are patterns
    over different fragments, so "the live worlds shrank" is not a well-formed
    premise for a cross-day argument at all — which is why the cross-day
    monotonicity question needed a counterexample rather than a proof attempt.
