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
| force interface | `.../src/force_api.py`, `FORCE_INTERFACE.md` | the feasibility-witness precondition, the charge, the responsibility split |
| liability | `FUNDING_AND_SAFETY.md` | `(eps + M) . d / delta`, and the three routes to a finite sum |
| projection | `../../../rounds/2026-08-18-projection-enforcement/src/projection.py` | the variational-inequality projection certificate |
| schedule and end-to-end theorem | `lean/Workspace/Normativity/Contrib/{ConstraintSchedule,RationalPolytope,EffectiveRepresentation}.lean` | the actual traderization hypotheses |
| Fourier-Motzkin | `Contrib/FourierMotzkin.lean` | the constraint representation, extended here with multipliers |
| Logical Induction | pinned FAF `c0d885bfb2f84054ada18c65acec672e04d6d380` | `LUV`, `expect`, `expectAffine`, `AffineCombination`, `PCWorld`, `DeductiveProcess` |

**Dependency direction.** The slice reads the RI reference model at run time and
reproduces the row and projection conventions rather than importing the
traderization sources, which live under a different project and carry their own
runner. Every reproduction is named at its definition.

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

**Reused unchanged:** `ri_core` in full; `PForce` as the injunction payload;
`enforcement.Row`'s sign convention; the feasibility-witness precondition of
`compile_force`; the liability charge; the projection certificate; the
admissible-pattern construction; `RationalPolytope` as a possibly-redundant
generating list.

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

## 6. The inertness dichotomy

The round's central negative result, and it was found by running the machine
rather than by inspecting the statement.

> If every `Sigma_n`-consistent world satisfies every compiled row, then every
> vertex of `K^D_n` lies in `K^N_n`; `K^N_n` is an intersection of half-spaces
> and so convex; so `K^D_n subset K^N_n` and `K_n = K^D_n`.

`hadm` *is* that hypothesis. So an injunction satisfies it exactly when it makes
no difference to the price region. **Every operative injunction with content
falls outside the unconditional traderization theorem.**

Checked on every non-blocking case in the suite: admissibility passes exactly
when `deductively_inert` holds, exactly when the exclusion depth is zero, exactly
when `K` equals `K^D`.

This is not a defect in the theorem. It says the theorem's scope is the
zero-liability calibration case — which is what `DEDUCTION_SPECIAL_CASE.md`
already says about deduction — and that the normative layer lives entirely in the
charged branch. The corpus knew that a world-inclusive region has zero liability;
what is new is that world-inclusivity and *operational inertness relative to the
epistemic substrate* are the same condition, so the charged branch is not one
option among several but the only one a normative source ever gets.

**The corollary is the round's best positive finding.** Exclusion depth is
measured over `W_n`, and settling removes worlds. So a fixed injunction's charge
is non-increasing as the record settles, and reaches zero exactly when what it
demands is already settled — at which point it is inert. **Force is priced at the
gap between what is demanded and what is settled.** That converts the safety
condition `sum_t (eps_t + M_t) d_t / delta_t < inf` from an assumption about a
region schedule into a question about how fast normative practice settles the
things it makes demands about, which is a question the inquiry layer is the right
place to ask.

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
- a positive and non-decaying exclusion depth `d_n`, with the charge it implies;
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

One thing the run does say about that arrow. The pressure worth attending to is
not "the region is expensive" but "the region is expensive *and the gap is not
closing*", because §6's corollary makes a temporarily expensive injunction the
normal case for a demand about something not yet settled. A pressure signal that
fired on positive depth would fire on every honest injunction.

## 9. What this round does not establish

- **No Lean, no registered claim.** Every Lean declaration named is cited for its
  hypotheses. Nothing is proved against them.
- **The inertness dichotomy is a paper derivation checked on finite instances.**
  The argument is three lines and uses only convexity, but it is not mechanized,
  and `test_composition.py` verifies the coincidence on a sample rather than
  establishing it.
- **`E3` and effective presentation are declared.** No computability statement is
  made about any `Sigma` or schedule here.
- **The safety condition is untouched.** §6 says every normative source needs the
  charged branch; nothing shows any source's liability sum is finite. This is the
  round's largest gap and it is not incidental — it is where the architecture's
  safety claim now sits.
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

2. **Force is priced at the gap between demand and settlement.** Exclusion depth
   is measured over `Sigma_n`-consistent worlds, so settling makes a fixed
   injunction cheaper, and free exactly when its demand is already settled.

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
