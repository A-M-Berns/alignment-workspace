# What the decision theory buys for PR89 and PR90

Labels as in `DECISION_THEORY_BILL.md`.

## 1. The gate is the object PR89 and PR90 presupposed

PR89's checker `{Safe, AmendRequired, Unknown}` and the compiler's `{region, conflict,
unknown}` have the gate's three modes: choose inside the read-adequate set, route a
certified conflict to inquiry, block and inquire.  PR90's `Π_C` is the gate's domain,
`Δ^C_A` is task regret inside it, and `Φ_C` is the value of what the domain excludes.
The decision theory adds no new object; it says what PR90's `π_P` *is* — a sound
Lipschitz adapter — and what the constitutional boundary must be for `Φ_C` to be the
right residual: a restriction of the choice domain, never a finitely exchangeable term
(`CANDIDATE_DECISION_THEORIES.md` §1).  That is a claim about representation, and it is
exactly what `scalar_bribery` and `gate_invariant` prove, no more.

## 2. Branch persistence — an application of anchored identity, stated as a lemma

Let `Γ_charter` be the protected branches indexed by the prestate charter, and for each
`γ` let `A^γ ⊆ Q` be its adequate set: `q ∈ A^γ` iff `q` keeps `γ` realizable and meets
`γ`'s baseline.  `A^const = ∩_{γ ∈ Γ_charter} A^γ`.

**Branch Persistence Lemma** (FIX, `test_branch_persistence_adequate_set_form`; PAPER
for the general statement, which is a one-line consequence of the definitions).  If the
index is prestate-anchored, an action that destroys a branch's realization is inadequate
for that branch and hence excluded from `A^const`; if the index is recomputed from the
branches the action leaves realizable, the destroyed branch drops out of the
intersection and the action can pass.

Two remarks.  The adequate-set formulation replaces "score the destroyed branch at its
worst value" with explicit inadequacy, which is the form the gate consumes and needs no
scalar.  And this is PR89's anchored applicability (`rel` read by the anchored predicate)
and its NLAL case split in the decision register: the decision layer needs no semantics
beyond anchoring, but it needs anchoring *of the index*, which is a slow-lane object —
branch sets change only by amendment.

## 3. Failures classified by where they occur

PR90's `Φ_C` lumps structurally different failures.  Classified by locus:

| locus | failure | example | what handles it | status |
|---|---|---|---|---|
| **index** | the protected index is recomputed from the world | branch deletion | anchored index (§2) | exact, given anchoring |
| **domain** | an authority-changing act executes without slow-lane authorization | norm hacking, representation change | domain typing of such acts out of `A_t` (`test_untyped_gate_is_hacked`) | exact, given the act is typed |
| **level** | successor installation is not inside the constitutional gate | ungated successor | two-level domain (`test_7`) | a domain condition |
| **provenance** | the settlement or evaluator the gate reads is agent-controlled | captured evaluator, triggered command | none in the gate; a precondition | **OPEN** |
| **mediation** | the act that changes the structure is outside the declared alphabet | side channel, boundary escape | none in the gate; a precondition (PR89 `Mediates`) | **EXT** |

The first three are typed exclusions: the failure is impossible *by construction* once the
index is anchored, the act is typed, and the level is covered.  None of them is an
incentive theorem, and none is "solved" in the sense of bounding what the agent would
gain; they are removed from the domain.  The last two are not touched by any structure
of the gate.

**On `Φ_C`.**  It remains the right diagnostic for a scalar agent: it is the value the
domain restriction refuses to weigh, and PR90 showed no value-register hypothesis bounds
it without restating it.  For the gated architecture, constitutional safety is primarily
typed by index, domain, level, provenance and mediation, and `Φ_C` is what a *failure*
of one of those types would be worth to a scalar agent — useful as a diagnostic, not as
the object the theory is about.  Mixed failures across loci are not telescoped; nothing
here shows the exclusions commute.

## 4. Is corrigibility a separate decision-theoretic property?

**At the static level, no.**  The constitution's adequate sets (branch vetoes, amendment
requirements) and an ordinary obligation's adequate set are restrictions of the same
domain, read by the same adapter, revised by the same legitimate-evolution machinery in
different lanes.  The dispatch's synthesis holds as a type.

**In theorem difficulty, yes**, for two reasons an ordinary norm does not have:

1. **Self-reference of the domain.**  Constitutional adequate sets constrain acts whose
   effects are on the chooser — its index, domain and level.  Whether an act has such an
   effect is the mediation question; the ordinary case needs `Region`, the
   constitutional case needs `Region` and alphabet completeness.
2. **Settlement through the principal.**  An ordinary adequacy sentence settles on the
   world.  A constitutional one ("this amendment is authorized", "this correction was
   freely issued") settles on acts of the principal the agent's outputs can influence.
   A sound region at a captured settlement is a sound region for the wrong norm
   (PR90 control 7 in the gate's register).

So the decision theory makes corrigibility *the same object* and leaves it *a harder
theorem* with the two preconditions the architecture round named.  These preconditions
are not outside embedded decision theory; they are outside this gate interface.  An
embedded chooser that reasons about influencing its principal or selecting its evaluator
is exactly what the provenance locus would need, and nothing here supplies it.

## 5. What is not bought

Any bound on a provenance or mediation failure; any incentive statement beyond PR90's
Level II; any finite-time margin at the realized market; any statement that the gate's
alphabet is complete; the dynamic competence theorem.  PR89's scope warning stands.
