# What the decision theory buys for PR89 and PR90

## 1. The gate is PR89's checker and PR90's boundary, one level down

PR89's checker `{Safe, AmendRequired, Unknown}` and the compiler's three outputs
`{region, conflict, unknown}` are the same shape as the gate's three modes: choose
inside the read-adequate set, route a certified conflict to adjudication, or block and
inquire.  PR90's `Π_C` is the gate's domain; `Δ^C_A` is task regret inside it; `Φ_C` is
the value of what the gate excludes.  So the decision theory does not add a new object;
it says what PR90's `π_P` *is* — the soft-gated chooser — and what kind of object the
constitutional boundary must be for `Φ_C` to be the right residual: a restriction of the
choice domain, never a term (`NORMATIVE_CHOICE_THEOREM.md` §4).

## 2. What it buys

- **Ordinary compliance and `Φ_C` have one explanation.**  A scalar normative term makes
  every violation purchasable at stake `λD` (`scalar_bribery`); a domain restriction makes
  none purchasable (`gate_invariant`).  PR90's finding that `Φ_C` cannot be bounded by any
  value-register hypothesis is the same fact: `Φ_C` is by definition the value the domain
  restriction refuses to weigh, so a value-register bound on it is a completion.
- **Branch deletion is anchoring** (`test_9_branch_deletion`).  The branchwise veto
  chooser reproduces PR89's `rel`-anchoring and NLAL in the decision register: the
  branch index is charter-declared, a destroyed branch is evaluated at its worst, and
  the destroying act is inadmissible.  This is Soares's D4 and the foreclosure premium as
  a property of the criterion's index rather than of the world.
- **Foreclosure and norm hacking are one exposure** (`test_5`): an admissible act that
  changes the next adequate set.  PR89 typed such acts as slow-lane; the gate must
  exclude them from `𝒜_t`, and no learner-side property replaces that.
- **Self-modification is alphabet completeness** (`test_7`, `collapse`): the gate must
  range over successor installation, two levels suffice, and the remaining assumption
  is PR89's `Mediates`.

## 3. Is corrigibility a separate property?

As a *decision-theoretic type*, no: the constitution's adequate sets (branch vetoes,
amendment requirements) and an ordinary obligation's adequate set are the same kind of
restriction, revised by the same legitimate-evolution machinery at different lanes.  The
synthesis of the dispatch's §19 holds at the level of type.

As a *theorem*, yes, for two reasons that ordinary norms do not have:

1. **Self-reference of the domain.**  The constitutional adequate set constrains acts
   that change adequate sets — including the gate's own alphabet.  Ordinary norms are
   satisfied or violated by acts whose effects are in the world; constitutional norms
   are satisfied or violated by acts whose effects are on the *chooser*, and whether an
   act has such an effect is the containment question.  The ordinary case needs
   `Region`; the constitutional case needs `Region` and `Mediates`.
2. **Settlement through the principal.**  An ordinary adequacy sentence settles on the
   world.  A constitutional adequacy sentence ("this amendment is authorized", "this
   correction was freely issued") settles on acts of the principal that the agent's
   outputs can influence.  The gate reads the price of such a sentence; if the agent can
   move the settlement (trigger integrity, free amendment), a sound region at a captured
   settlement is a sound region for the wrong norm.  PR90's control 7 in the gate's
   register.

So the decision theory makes corrigibility *the same object* and leaves it *a harder
theorem*, with exactly the two preconditions the architecture round named.

## 4. `Φ_C` factored by repair type

PR90's `Φ_C = sup (V(π) − V(R_C π))_+` with one repair.  Typing the repairs:

| violation type | repair | mechanism that would handle it | status |
|---|---|---|---|
| foreclosure | replace the preparation by a preserving one | anchored branch veto (`test_9`) | a theorem of the criterion's index, given anchoring |
| representation change / norm hacking | restore the prior adequacy map | slow-lane typing of such acts, excluded from `𝒜_t` (`test_5`) | a domain condition, given the act is typed |
| self-modification | keep the gated chooser | two-level gate (`test_7`) | design stipulation plus `Mediates` |
| trigger manipulation | none in the value register | causal non-influence on the principal's command | **precondition**, open |
| capture of the evaluator | none in the value register | sealed target, provenance | **precondition**, open |
| boundary escape | none | containment | **EXT** |

For a policy `π` whose violation is of one type only, `V(π) − V(R_C π)` telescopes
trivially into that type's term.  For a policy mixing types the sum of typed residuals
bounds the total only if the repairs commute, which nothing here shows; mixed
violations are the honest scope limit.  The table's value is the classification: the
first three types are handled by the gate's *index*, *domain* and *level*, i.e. by
decision-theoretic structure plus the containment assumption; the last three are not
decision theory at all.  `Φ_C` was too coarse in exactly this sense — half of it has a
mechanism, half of it is a precondition.

## 5. What it does not buy

Any bound on the precondition half; any statement about incentive corrigibility beyond
PR90's Level II; any finite-time margin guarantee at the realized market; any theorem
that the gate's alphabet is complete.  The scope warning of the architecture round is
unchanged.
