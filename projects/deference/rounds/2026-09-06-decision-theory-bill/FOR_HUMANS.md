# For humans

The legitimacy theory and the Normative Inductor stop at one contract: at each decision
occasion the agent realizes a response, and the response's anchored loss must be at most
a constant times the public normative defect plus a constant.  Everything upstream —
conservation, openness, uptake — is proved.  This round asked what the *decision theory*
has to be for that contract to hold.

The answer is smaller than a theory of value.  The contract already factors, in the
repository's own Lean, into a semantic half (adequate responses cost little, inadequate
ones cost at most `D`) and a decision half: the mass the chooser puts on inadequate
responses must be affine in the defect.  That decision half is a property of a **gate**
— a map from the market's adequacy prices to a distribution over responses — and it is
not automatic.  A hard gate ("pick the best task option among those priced adequate")
fails it at every positive defect, because a price a hair above the threshold lets the
task-preferred inadequate option through with mass one.  A **soft gate** — ramp the
weight over a band of width `δ`, and inquire when nothing is confidently adequate — pays
the contract with an explicit constant, `|Q|·pmax/(pmin·δ)`.  That is the one new
theorem, and it is in Lean.

Two things follow that are not about the contract.

**Measurement is not motivation.**  The Progress statistic is a scalar and charges an
honest "I don't know yet" the same as a violation.  If the agent *optimized* that
scalar against task reward, any constraint would be purchasable at a price `λ·D`; no
finite penalty makes a hard constraint non-tradeable.  A gate is immune to the
forbidden option's task value by construction.  This is the same fact PR89 found about
conservatism and PR90 found about the constitutional-violation premium: a constraint is
non-compensable exactly when it restricts the choice domain rather than entering the
objective, and any rule that trades it away is a completion of a partial order — which
is charter content, not decision theory.

**The same gate serves ordinary norms and corrigibility.**  The constitution's
constraints (protected intervention branches, amendment requirements) are adequate sets
like any other, and they must be *anchored*: a branch index read from the world lets the
agent delete a branch by destroying its affordance; an index declared by the charter,
with a destroyed branch scored at its worst, keeps the veto.  So corrigibility is not a
separate decision-theoretic object.  It is a harder theorem for two reasons the ordinary
case lacks: the constitutional gate must cover acts that change the gate itself — which
is the containment assumption — and its sentences settle on acts of the principal that
the agent can influence — which is the manipulation precondition.  The old
foreclosure premium splits accordingly: half of it is handled by the gate's index,
domain and level; half of it is a precondition no decision theory supplies.

What this does not do: it does not show the market ever *marks* an adequate response
with margin (the completeness half of the semantics, an asymptotic property), it does
not give a learner that is safe when admissible actions change future admissibility
(BRIA is myopic by design and the fixture shows the failure), and it does not bound the
manipulation half of the premium.  The emerging picture is a bounded optimizer
subordinate to an answerably revisable admissibility correspondence, with legitimacy
governing revision, normative induction learning the operative state, and a BRIA-style
learner supplying competence inside the gate.  It survives the fixtures as a type.  Its
theorems are the gate's; its preconditions are unchanged.
