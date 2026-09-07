# For humans

The Normative Inductor does not need a utility-maximizer that values normativity.  It
needs a chooser whose probability of taking an inadequate action changes continuously
with the normative market's error.  A soft adequacy gate supplies that.  The unresolved
agent-foundations problem begins when actions can change the future gate itself.

That is the whole picture; the rest is precision about it.

**What is proved.**  The Normative Inductor's contract with decision theory is one
inequality already in the repository: the chooser's mass on inadequate responses is at
most a constant times the public defect.  Any chooser that is sound where the market
conforms to the norm and Lipschitz in the market's scores satisfies it, and then the
practical certificate and the Progress bound follow (Lean, `adapter_practicalCert`).  A
ramped gate on adequacy scores is such a chooser, with an explicit constant: inadequate
preference mass over certified adequate mass, per unit of defect relative to the ramp.
The natural hard gate is not: at every positive defect it can execute an inadequate
response with certainty.  Continuity is the entire decision-theoretic content.

**What the constant hides.**  The constant is charged through the Progress theorem's
amplification hypothesis, so the exact end-to-end condition is the one already in the
theorem; the local reading is that market error must shrink relative to the certified
adequacy margin with the inadequate-to-adequate preference-mass ratio controlled.  The
margin itself is not decision theory, and it comes in two types that must not be
confused: a margin the *compiler* places at the region point (completeness — the region
must positively mark an adequate response, not merely refute inadequate ones), or a
margin the *market* displays on its own, which a learning theorem about prices could
supply.  Both are pointwise and apply to adequacy that is derivable or externally
certified.  Adequacy learned only through later settlement is outside the static theorem
altogether; the bridge from average calibration to average inadequate-action mass is not
proved and is recorded as open.  Traderization controls distance to the region; positive
action needs a separate margin certificate.

**Normativity is not the task objective.**  A finite additive penalty is bought by any
task stake above the penalty times the loss range; a gate never consults the forbidden
option's task value.  Non-compensability must live in the choice ordering itself, not
solely in a finitely exchangeable term — a domain restriction is one clean way, a
lexicographic order another; a partial order needs an *authorized* completion.  This is
the same fact PR89 found for conservatism and PR90 for the constitutional-violation
premium.

**Inquiry.**  When nothing is confidently adequate the gate returns "inquire".  In Lean
that is a wrapper around the theorems, silent under margin; conceptually cleaner is to
compile "inquiry is adequate" as a sentence when obligations conflict, so that inquiry
is an ordinary response and the theorems apply verbatim.  Progress does not need
continuity across the switch: occasions without a certified margin carry no transport
and are charged to the residual.

**Corrigibility.**  Constitutional constraints are adequate sets of the same kind, with
one requirement — the protected branch index is anchored in the charter, so destroying a
branch's realization makes the act inadequate rather than making the branch disappear —
and two preconditions the ordinary case lacks: the gate's alphabet must cover acts that
change the gate, and the sentences the gate reads must not settle through a process the
agent controls.  Failures classify by locus — index, domain, level, provenance,
mediation — and the first three are removed by typing, not bounded by an incentive
theorem.  Reflective "gate preservation" is a representation plus a domain condition;
nothing here is a theorem about what a chooser prefers.

**The new problem.**  Restrict the comparator class to policies that respect the gate
along their own trajectories and the myopic gated learner is still legitimate — and
loses linearly to the legitimate policy that invests in an authorized amendment.  Domain
typing gives safety; it does not give competence; comparator restriction alone is
vacuous.  Bounded competence under an answerably evolving admissibility process whose
future depends on current actions is the next layer, and the leading candidate is a
bounded-inductive-rationality learner whose hypotheses are continuation policies tested
in gated blocks.  Nothing positive about it is claimed.
