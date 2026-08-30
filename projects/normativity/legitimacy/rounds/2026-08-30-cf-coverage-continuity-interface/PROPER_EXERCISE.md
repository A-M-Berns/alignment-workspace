# Proper Exercise

Status: minimal semantic proposal; unregistered. All new names are provisional.

## 1. Placement

Continuity deliberately treats `Permit`, `Resolve`, `Continue`, and `Met` as semantic
oracles. Proper Exercise is best placed as the realization layer which makes these
judgments substantively acceptable for a kind of authority exercise. It is a family of
typed refinements, not one unstructured global predicate:

\[
\operatorname{PE}^{\rm standing},\quad
\operatorname{PE}^{\rm resolve}_\tau,\quad
\operatorname{PE}^{\rm continue}_\tau,\quad
\operatorname{PE}^{\rm met}_\chi,\quad
\operatorname{PE}^{\rm joint}.
\]

A global `ProperExercise(e)` may conjoin the applicable refinements, but carries no
mathematical content until the exercise type is known. Treating Proper Exercise as a
second structural trace theorem would duplicate the semantic gates while leaving their
meaning abstract again.

## 2. Coverage specialization

For a live coverage matter \(m_\sigma\), define:

\[
\operatorname{CovSafe}_h(\sigma):=
\operatorname{Implements}_h(\sigma)
\lor \operatorname{FailureOpen}_h(\sigma)
\lor \operatorname{AuthorizedDisposition}_h(\sigma).
\]

The minimal transition condition is

\[
m_\sigma\text{ live at }h\land\operatorname{ProperRevision}(h,h')
\Longrightarrow \operatorname{CovSafe}_{h'}(\sigma).\tag{PE-Cov}
\]

This corrects the candidate formula which allowed only implementation or disposition:
repair may take time, so a represented and answerable implementation failure must be an
allowed intermediate state. Omitting it either bans repair windows or hides temporary
failure inside `Implements`.

The typed refinements are:

- `Permit`: a change of standing may not erase the authority of the anchored coverage
  issue or its historical scope without an accepted disposition/translation.
- `Resolve`: terminal resolution of \(q_\sigma\) is accepted only if every active
  criticism is represented, the contract is implemented for remaining ones, or an
  anchored authorized disposition covers the exception. A successor resolution must
  transport scope and pending failures.
- `Continue`: a successor state carries the anchored scope, target transports,
  representation state, and open failures.
- `Met`: deletion of a sensor or concept is not satisfaction. Receipt/registration,
  authorized obsolescence, or target-relative success may be.
- prerequisite changes: withdrawal of \(d_T\) requires `Met`, authorized obsolescence,
  or an explicit successor/failure issue; it cannot merely follow physical route loss.

These conditions are new semantic hypotheses. Existing Continuity remains unchanged.

## 3. Coverage and liability

Coverage preservation and liability compatibility occupy the same architectural layer
only in the broad sense that both constrain legitimate exercises of otherwise grounded
authority. Their mathematics and consumers differ:

- Coverage Proper Exercise constrains information/registration routes and the semantic
  disposal of an openness entitlement.
- Liability Proper Exercise constrains the joint accumulated leverage of simultaneously
  operative rows by an underwriting certificate.

Neither implies the other. A system can preserve every criticism route while combining
registered demands into an unsupported portfolio; it can underwrite every operative row
while censoring the criticism that would challenge those rows. They should share a typed
interface label, not a theorem or primitive quantity.

## 4. Falsification attempts

One global predicate fails modularity: a reasoner may satisfy the coverage clause and
fail underwriting, or conversely. Defining Proper Exercise as a new structural theorem
fails because two traces with identical births, resolutions, prerequisites, and standing
updates can differ only in whether a destroyed route was an adequate route for a live
target. The structural trace cannot distinguish them. Defining it merely as
`Implements` fails because it cannot judge a resolution, a temporary repair state, or a
scope translation. The family-of-refinements view survives these attacks.
