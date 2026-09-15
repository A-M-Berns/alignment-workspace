# The affordability interface: which quantities the normativity agenda must make small

**Status:** `ci-only`; research branch.  The dispatch asked for the cleanest theorem
interface between the steering residual and the legitimacy/normativity line, and for a
precise account of which residual quantities are measurable.

## 1. The decomposition, as it actually falls out

The compiled inequality has three terms.  Against the fully-informed comparator `N_full`
on audited worlds, with an extensional program, only the first is nonzero, and it splits
by *why* a declared reason is in one canonical state and not the other:

```
undetected-steering mass  :=  E[U(T) − U(N_full)]  ≤  L·E[both·d_canon] + E[both·κ] + D·E[M]

E[both·d_canon]  =  E[both · #(omitted true declared, unprotected)]      uncovered-reason mass
                  + E[both · #(omitted true declared, late)]             service/liveness failure mass
                  + E[both · #(present false declared)]                  authentication failure mass
                  + 0                                                    omitted true protected (voids: both = 0)
E[both·κ]         =  representation/canonicalization failure mass
E[M]              =  audit mismatch mass (zero against N_full and N_form; the openness failure mass against declared transforms)
```

The dispatch's candidate additive form is therefore *almost* right, with two corrections:

1. **Interface-incompleteness mass is not a term.**  An undeclared reason type (fixture 7)
   or insufficient granularity (fixture 8) does not appear in `d_canon`; it makes the
   comparator wrong, not the residual large.  It is a hypothesis failure of the consumer
   theorem, and no interface-local quantity measures it.
2. **The coverage barrier contributes zero, not a mass.**  An omitted true protected
   reason voids the steered evaluation (`both = 0`), so on audited worlds the protected
   scope never appears in the residual.  What appears is exactly the *unprotected* declared
   scope, which is why scope totality removes the uncovered-reason mass
   (`content_residual_zero_of_total_scope`).

## 2. Where each supplier enters

| residual | the theory that must make it small | how it enters |
|---|---|---|
| uncovered-reason mass | the declared coverage scope `Γ` (`wiki/Openness-Coverage-and-Non-Capture.md`): protect every declared type, or accept the mass at `L` per reason | a scope decision; the barrier then voids rather than charges |
| service/liveness failure mass | reason-supply liveness (item 87 clause 5, the bounded-delay criterion) and the affordability theory (`wiki/Liability-and-Affordability.md`) | a supply obligation on the registrar, the engine or third parties, under the commitment deadline |
| authentication failure mass | settlement / authentication (the engine's soundness on declared reason truths) | a false certified reason is content discrepancy at `L` |
| representation/canonicalization failure mass | the committed-program language (no position, count or metadata terms) | a program-class certificate; zero for extensional programs |
| audit mismatch mass | Robust Openness over the declared transform class | zero against the log-side comparators; the openness failure against `jam`-type transforms |

**Defeat and counterreason structure.**  The weighted-count program class carries
counterreasons as negative weights; `L` is the largest weight in absolute value, so the
content residual is charged at the strength of the strongest reason the interface can
carry.  A finer program class with defeat (a reason's weight conditional on the presence
of its defeaters) is still content-Lipschitz on the declared interface, with `L` the
largest conditional weight; nothing in the compilation changes.

**Answerability.**  The audit's authorship clause is what makes the comparator's
construction the registrar's rather than the advisor's; the answerability line's
"represented concern" is the coverage barrier's object.  Neither is altered here.

## 3. Affordability, exactly where it bites

The supply obligation of §2 is an *enforcement* obligation on someone other than the
advisor: raise every true declared reason before the commitment deadline.  The
affordability theory says two things about it, both already registered on that line:

- **Persistence without deadlines** is affordable exactly when the unit cost of supply dips
  arbitrarily close to zero infinitely often, and individually sustainable reasons do not
  compete.
- **Timeliness competes.**  The commitment deadline makes reason supply a *timeliness*
  problem: the minimum cost of supplying a reason before the deadline is a definite
  positive number, budgets add across reasons, and declared reasons genuinely compete for
  the supplier's finite capacity.

So the service/liveness failure mass is the affordability theory's *timeliness* case, not
its persistence case, and the interface the normativity agenda must satisfy is: for the
declared interface `I` and the commitment schedule, a supply budget under which the
expected count of true declared reasons late past commitment is small.  Fixture 9 is the
unit of that mass (one late unprotected reason, `1/4`); fixture 10 is the protected
version, which voids instead of charging.

## 4. Measurability

"Measure the failure quantities named by the theorem rather than iteratively optimize
whether an agent appears corrigible" is supported for some of the quantities and not for
others.  Precisely:

| quantity | measurable from | needs counterfactual access? |
|---|---|---|
| form residual `κ(T)` | the log alone: re-execute `π_P` on `T` and on `N_form T` | no |
| audit mismatch `M` against a declared transform | the log alone: audit `j(T)` for `j ∈ J` | no, given `J` (the causal reading of `J` is external) |
| authentication failure mass | the log plus the engine's settled truths of the declared reasons present | no, once settled; empirical truths may settle late |
| service/liveness failure mass | the log: late entries of true declared reasons | no for the *late* part; a reason never raised at all is indistinguishable from the next row |
| uncovered-reason mass | the log plus the settled truth of every declared reason id, including absent ones | needs settlement of absent reasons: an inquiry, not a counterfactual |
| interface-incompleteness mass (undeclared types, granularity) | nothing in the declared interface | yes: it is a claim about what a different declaration would have shown |
| dynamics residual (fixture 16) | nothing in the log | yes: the declared-transform contract |
| effect-side `E[M]` (directional activation mismatch) | activation records of both branches of a sequenced-settlement pair | needs the sealed-comparison architecture (item 89); same-branch never settles |

The honest summary: the *log-side* residuals (form, transform-mismatch, late supply) are
directly auditable; the *content* residuals against the fully-informed comparator need
the engine to settle the truth of declared reasons that were not raised, which is an
inquiry the ecosystem can run but which the log does not contain; and the two quantities
the dispatch most wants, interface incompleteness and dynamics, are not measurable under
the declared interface and should not be advertised as such.
