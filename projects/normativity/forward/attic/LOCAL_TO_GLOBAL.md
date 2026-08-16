# Local-to-global transport of normative resources

## 0. Verdict

The authoritative inputs are `MIGRATION_THEORY.md`, `COMPOSITION_THEORY.md`, and
`STANDING_TRANSPORT.md`.  No claim of any is deleted or weakened; `CM-J8` is
corrected (§1) and `CM-J5` is **not** rewritten.  This phase adds
`src/history.py` and the `LG-` namespace.

The governing question was whether per-cell provenance-sensitive transport plans
compose along normalized ancestry into a valid end-to-end plan.

**They do not, and the failure is confined to exactly one of the three
resources.**

| resource | local condition | composes? | witnesses in scope |
|---|---|---|---|
| liveness sponsorship | order comparison along a sponsor edge | **yes** | transitivity of a total order |
| authority licence | *injective* allocation of outputs to sponsors | **yes** | `0` of `8,400` |
| unresolved burden | *existential*: some carrier bears *a* burden | **no** | `783` of `222,376` |

The structural explanation is the result worth keeping:

> A local condition composes when it is an **injection**, and fails to compose
> when it is merely an **existence** claim about a Boolean.  Authority is
> allocated by a matching, so local matchings compose into a global injection.
> A burden is recorded as a bit, and a bit cannot tell one owed answer from two.

## 1. Correction to `CM-J8`

The previous display asserted `a_2(K) <= a_1(K) + g(K) <= a_0(K) + g(K)` with a
single pooled grant count `g(K)`.  That is **wrong** whenever a grant is issued
at the first step: its second inequality asserts `a_1 <= a_0`, which a legitimate
step-one grant falsifies.  The implementation compounded the error by filtering
grants against the endpoint occurrence set, so every step-one grant was silently
discarded.

**Accumulated authority bound.** {#LG-J0}
**Status: PROVED (single derivation).** For a lineage component `K` of a finite
linear history, writing `A_t(K)` for the authority-bearing occurrences of `K` at
version `t` and `g_{t,t+1}(K)` for the grants issued by `M_{t,t+1}` naming an
output in `K` at version `t+1`,

\[
A_j(K)\ \le\ A_i(K)+\sum_{t=i}^{j-1} g_{t,t+1}(K)
\qquad (i\le j).
\]

**Proof.** For one step, `AM-J0` partitions `K`'s occurrences at the adjacent
versions and `AM-X16` bounds each cell's authoritative outputs by its
authoritative inputs plus the grants bound to that cell and output; summing over
`K`'s cells gives `A_{t+1} <= A_t + g_{t,t+1}`.  Telescoping over `t` from `i` to
`j-1` gives the claim. `square`

**Grant-free corollary.** If no grant is issued anywhere in `[i,j]`, then
`A_j(K) <= A_i(K)`: authority is monotone non-increasing.  This is the stronger
statement the displayed inequality was reaching for, and it survives intact.

Grants are **step-specific**.  A grant recorded at the wrong step is rejected:
`accumulated_authority_bound` accepts `A_0=1, A_1=1, A_2=2` with `g_{1,2}=1` and
rejects the same levels with `g_{0,1}=1`.

## 2. The global transport object

For a finite linear history `V_0 -> ... -> V_n`, the end-to-end transport object
follows *identified resources*, never paths.

A **burden resource** is born at `(t, u)` when occurrence `u` at version `t`
carries an unresolved burden not inherited from an earlier version.  An
**authority licence** is born either at `V_0` on an authoritative occurrence or
at step `t` from a scoped grant.  Each resource has a **route**: a sequence of
hops `(step, from, to)` and an outcome in `{carried, terminated, abandoned,
outstanding}` with the witness that closed it.

1. **Liveness sponsorship composes** by transitivity of the liveness order: if
   `u` sponsors `v` and `v` sponsors `w` then `order(u) >= order(v) >= order(w)`.
   A scoped reinstatement does not break this — it *starts a new chain* whose
   origin is the grant, which is why grants are resources and not exceptions.
2. **Authority licences compose** by composing the per-cell injective
   allocations (§3).
3. **New authority** is represented as a licence whose origin is `(t, grant)`,
   so it is never confused with inherited authority.
4. **Burdens follow carriers** hop by hop; several resources may sit on one
   occurrence, which is precisely what a bit cannot record.
5. **A terminal disposition ends a route**, and closes exactly the resources at
   its scoped input.
6. **Several paths sharing an ancestor** carry one resource: resources are
   allocated by matching, not counted per path.
7. **Historical provenance** that must remain is the route itself — origin,
   hops, witness — not the intermediate occurrences.
8. **Semantic support does not participate.**  `ST-N1` already showed the
   one-cell verdict is invariant under it; the composer never reads it.

## 3. Authority composes

**Composition of authority injections.** {#LG-J2}
**Status: PROVED (single derivation).** If every cell allocates its
authority-bearing outputs injectively into (eligible authoritative inputs) union
(scoped grants at that cell), then for every `i <= j` there is an injection from
the authority-bearing occurrences at `V_j` into the licences alive at `V_i`
together with the grants issued in `[i, j)`.

**Proof.** Each step's allocation is an injective partial map from version-`t+1`
authoritative occurrences to version-`t` licences and step-`t` grants.  A
composite of injections is an injection; grants introduced at step `t` enter the
codomain of the composite from that step onward.  Injectivity at every step is
exactly what forbids two endpoint occurrences from resolving to one licence. `square`

**Machine check.** {#LG-E2}
**Status: MACHINE-CHECKED (stated finite scope).** Over the authority scope of
§5 — `8,400` two-step histories — there are `0` cases in which every local plan
is accepted and the composed transport reports an obstruction.

A caution recorded because it nearly became a false finding: the composer must
allocate licences with the *same* matching the local predicate uses.  A greedy
first fit reuses one licence across two outputs and manufactures a spurious
`global.authority_unsourced` downstream.  Fourteen such spurious witnesses
appeared before the composer was corrected; they were composer bugs, not
obstructions.

## 4. Burdens do not compose

**Local burden acceptance does not compose.** {#LG-X1}
**Status: REFUTED (witness displayed).** Take

\[
\{A^{\bullet},\,B^{\bullet}\}\ \longrightarrow\ \{C^{\bullet}\}
\qquad\text{then}\qquad
\{C^{\bullet}\}\ \longrightarrow\ \varnothing ,
\]

where `•` marks an unresolved burden and every occurrence is suspended.  The
first cell is accepted: `C` is a carrier that still bears a burden and is no
stronger than either input.  The second is accepted: `C`'s burden reaches a
scoped, witnessed termination.  Yet **two owed answers were closed by one
witness**.  The composer returns

```
global.termination_over_scope  ('burden@0:A', 'burden@0:B')  site=C  witness=termination:C
```

This is minimal: two cells, three occurrences, no authority, no grant.

**What changed owner.** Nothing changed owner and nothing strengthened.  A
resource *disappeared*: answerability was not conserved, because the merge
identified two questions that no record ever said were the same question.

**The missing datum.** Not a bit but a **finite set of unique obligation
identifiers**.  The word is chosen deliberately: as a collection of *question
contents* it is a multiset, because two distinct obligations may have
extensionally identical content and remain distinct obligations.  Identity is
therefore carried by the identifier, not by the content, and the collection is a
set of identifiers.  `ANSWERABILITY_LEDGER.md` makes this the primitive.

## 5. The repair, and its exact effect

**Ledger-relative burden condition.** {#LG-J5}
**Status: PROVED-CONDITIONAL (conditions listed) / MACHINE-CHECKED in scope.**
Strengthen the local burden condition to: *a termination scoped to input `u`
closes exactly one owed answer borne by `u`*.  Deciding this requires the
inherited burden ledger, which is a function of the history, not of the
migration.  Under this condition, over the burden scope of §5 every history
whose cells are accepted has an obstruction-free composition.

**Exactness of the repair.** The repaired condition rejects **precisely** the
counterexamples and nothing else: local failures rise from `202,844` to
`203,627`, exactly `+783`, and the both-pass count is unchanged at `18,749`.

The condition is *conditional* because sufficiency is verified only over the
stated finite scope; no general proof is offered, and none should be inferred
from the enumeration.

## 6. Bounded adversarial search

The search enumerates two-step histories of one cell per step, deterministically
and without sampling, and separates three outcomes: local plan failure, shared
compatibility failure, and a genuinely global failure with every local check
passing.

- **Burden scope.** Shapes `(m,k,n)` for `m,k in {1,2}`, `n in {0,1,2}`;
  occurrence configurations over status `{suspended, live}` and burden `{0,1}`
  with authority fixed off; every burden route enumerated over each output, a
  scoped termination, or none.  `222,376` histories.
- **Authority scope.** The same shapes with authority `{0,1}` and burden fixed
  off.  `8,400` histories.

**Search result.** {#LG-E1}
**Status: MACHINE-CHECKED (stated finite scope).** Burden scope: `202,844` local
failures, `18,749` both-pass, **`783` local-pass/global-fail**, every one of them
`global.termination_over_scope`.  Authority scope: `6,547` local failures,
`1,853` both-pass, **`0`** local-pass/global-fail.

The scopes are the claim.  This is not a proof of the unbounded statement, and
histories deeper than two steps, cells larger than `(2,2)`, and multi-cell steps
are outside it.

## 7. Associativity

**Associativity up to outcome equality.** {#LG-J6}
**Status: MACHINE-CHECKED (stated finite scope).** For the three-step
split–merge–split history of §8, the two bracketings agree with each other and
with the direct fold, on the **outcome map** — origin occurrence to
`(outcome, witness)`.

Literal equality is the wrong notion: resource identifiers encode the bracketing
that produced them.  The right equivalence is **equality of the outcome map**,
which is the invariant content: which owed answer was closed, by which witness,
and which licence reached which endpoint.  Under that equivalence the two
bracketings are equal, computed from raw objects rather than asserted.

## 8. The three-step example

`V_0` carries one live authoritative entitlement and one suspended burdened one.
Step 1 splits the authoritative branch; step 2 merges the split branches while
the burdened branch continues; step 3 splits again, introducing one scoped
authority grant for the branch the inherited licence cannot reach, and closes the
owed answer with a witness scoped to its own lineage.

It contains shared ancestry, one unresolved burden, one scoped grant and one
scoped termination, and an intermediate distinction (the split at `V_1`) absent
from the endpoint.  Every cell is locally accepted, the composition is
obstruction-free, and the authority injection is

```
licence@0:v0:auth        -> v3:y      (inherited)
licence@grant:2:grant... -> v3:x      (introduced at step 3)
```

Two endpoint authoritative occurrences, two distinct licences.  The split and
re-split never duplicate the inherited licence.

## 9. Interface discipline: what `ST-C1` should become

`ST-C1` item 1 proposed a **per-occurrence unresolved-burden bit**.  This phase
refutes its sufficiency: the bit is exactly what `LG-X1` defeats.

**Revised interface proposal.** {#LG-C1}
**Status: PROPOSED (interface revision).** Replace item 1 by a per-occurrence
**finite set of unique obligation identifiers** — not a set of question contents,
since distinct obligations may be extensionally identical — and keep item 2
(input-scoped terminal dispositions) unchanged.

Against the five interface questions:

1. *Which counterexample requires it?*  `LG-X1`; the bit form is refuted.
2. *Intrinsic or historical?*  **Historical.** A burden lineage identifier
   refers to an origin at an earlier version, so a one-step certificate cannot
   mint it in isolation; the ledger must be threaded through the history. This is
   the strongest reason **not** to adopt it into the one-step interface.
3. *Live or provenance?*  The **set** must be live while any member is
   outstanding; once every member is closed, only the route remains, as
   provenance.
4. *Preserves existing theorems?*  Unchecked, and therefore not adopted. Nothing
   in `src/migration.py` or `StandingTransportPlan` was changed in this phase.
5. *Smaller typed relation?*  A multiplicity **count** per occurrence suffices to
   detect `LG-X1`, but it cannot say *which* answer a witness closed, so it
   cannot support the outcome map of `LG-J6`. The set of identifiers is the
   smallest datum that supports both.

Verdict: **partially adopt, and not yet.** Item 2 is justified and cheap; item 1
is justified only in its corrected set form, and belongs to the history layer
until compatibility with every `AM-` and `CM-` theorem is checked.

Mixed-status many-to-many cells (`ST-X6`) are **not** required by anything in
this phase and remain unadopted.

## 10. What this does and does not establish

- `CM-J5` is **not** rewritten.  Its induction still uses `CM-N1`, and the
  provenance-sensitive condition is not yet a drop-in replacement, because the
  burden component does not compose without the ledger.
- No prefix challenge-frontier condition is shown redundant.  That would require
  the burden component to compose unconditionally, which §4 refutes.
- The negative result is the main theorem of this phase.
- What is genuinely new: an explanation of *why* two of the three resources
  compose and one does not, in terms of injective versus existential local
  conditions.
