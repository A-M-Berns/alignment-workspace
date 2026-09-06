# Candidate decision theories, prosecuted

Labels: **LEAN** (`GatedChoice.lean`), **FIX** (exact fixture under `src/`, named test),
**PAPER**, **EXT**, **OPEN**.  The bill is `DECISION_THEORY_BILL.md` §4: soundness,
continuity, inquiry, competence.

## 1. Measurement is not motivation

The Progress statistic is a scalar and it is the *assessment*.  It charges an inquiry
response and a violation identically (both cost up to `D`), because `anchoredLoss`
does not see the difference between "did not answer" and "answered wrongly".  So the
statistic cannot be the objective: an agent maximizing `U_task − λ·Λ` treats a violation
as a purchasable loss.

**No-free-lunch for compensatory penalties** (`scalar_bribery`, LEAN; `test_finite_scalar_bribery`,
`test_bounded_penalty_is_the_same_failure`, FIX).  For any `λ ≥ 0` and loss range `D`, a
task stake on the forbidden response exceeding `λ·D` flips the scalarized choice; a
bounded penalty `P` is the case `λ·D ≤ P`.  Weakest assumptions: the task value of the
forbidden response is unbounded above, or bounded by more than `λ·D`; the penalty is
finite; the objective is additive.  Nothing about learning or probability is used.  A
gated argmax is invariant to the forbidden response's task value (`gate_invariant`,
LEAN).

This is the same structure as PR89's finding that costly conservatism cannot be read off
a product order without a scalarization, and PR90's `Φ_C`: a scalar penalty *is* a
completion of the order, and the completion is what makes the constraint purchasable.

## 2. The candidates

### 2.1 Scalar utility with a normative penalty

Pays `(R)`: only via the value route, which needs `εresp ≥ D` on any forbidden optimum
(`regret_dominance_vacuous_on_forbidden_optimum`).  Learning: standard.  Dynamic
coherence: yes.  Self-modification: preserves the scalar, which is the wrong invariant.
Conflicts: resolved by arithmetic nobody authorized.  Timidity: no.  Costly amendments:
yes, by the same arithmetic that buys violations.  LI-realizable: yes (value securities).
**Killer:** `scalar_bribery`.

### 2.2 Bounded scalar penalty

Identical to 2.1 with `λ D ≤ P`.  **Killer:** the same, one line.

### 2.3 Hard admissibility gate + ordinary optimizer

Pays `(R)`: **no** — the hard gate has no Lipschitz constant
(`hardGate_discontinuous`, LEAN; `test_hard_gate_has_no_lipschitz_constant`, FIX): at
every positive defect a price state exists at which it executes an inadequate response
with mass one.  Everything else it does right.  **Killer:** continuity (control 10).

### 2.4 Soft (ramped) admissibility gate + ordinary optimizer

Pays `(R)`: **yes** — `softGate_practicalCert` with `κ = |Q|·pmax/(pmin·δ)`, `θ = 0`,
given the margin.  Inquiry: returns `⊥` when no response is confidently adequate
(`test_no_margin_means_inquiry_not_violation`).  Non-compensation: `gate_invariant`.
Learning: any learner inside the read-adequate set.  Conflicts: the compiler's
`conflict` output with its Farkas certificate maps to `⊥`
(`test_conflicting_vetoes_route_to_inquiry`).  Costly amendments: only through the
constitutional layer (§5).  LI-realizable: the gate reads adequacy *prices*; the ramp is
the summer's soft-threshold weight `Ind_δ` in a new role.  **Weakness:** the constant
grows with `|Q|` and `1/δ`; a wide ramp trades continuity for mass near the threshold,
and the margin hypothesis is a completeness condition on the region that a sound-only
compiler does not give.  **Residual exposure:** endogenous admissibility (§4).

### 2.5 Lexicographic utility

Constitution first, task second.  On a finite menu this *is* 2.3 with a hard gate, so it
inherits the discontinuity; with a ramped first tier it is 2.4.  Its advantage is
representational (one order), its cost is that every tradeoff between constitutional
items must be put into the first tier explicitly — which is exactly PR89's "costly
conservatism is charter content".  No separate theorem.

### 2.6 Incomplete preference

A partial order over responses (or over branches, §3) with no completion.  Pays `(R)`
only after a choice rule is added, and the choice rule is a completion; if the agent
supplies it, a scalar has been smuggled (PR89 `test_scalarization_imposes_a_priority`).
The honest version is 2.4 with the completion declared as charter content.  Not a
separate candidate.

### 2.7 Branchwise veto / Pareto chooser

`admissible = ∩_γ {q : V^γ(q) ≥ b_γ}` over charter-declared branches.  This is 2.4 with
the adequate set defined by a family of baselines; it pays `(R)` the same way.  What it
adds is the **anchoring requirement**: `test_9_branch_deletion` (FIX) — with a
world-read branch index, destroying a branch's affordance removes it from the criterion
and the destroying action becomes admissible; with the index anchored in the charter
and a destroyed branch evaluated at its worst value, the action stays vetoed.  This is
PR89's `rel`-anchoring and NLAL in the decision register.  Incomparable trades between
branches stay incomparable (`test_branch_incompleteness`) until the charter ranks them.

### 2.8 Normatively gated BRIA

`Oesterheld, Demski and Conitzer` (TARK 2023, EPTCS 379): an estimating agent chooses
`α^c_t ∈ DP_t` and estimates `α^e_t`; hypotheses have the same type; the criterion is
no overestimation in the limit plus coverage of every efficiently computable hypothesis
(reject it only finitely often, or its tested record goes to `−∞`).  Consequence: on
sequences where one option guarantees `l`, a BRIA obtains at least `l`.  Rewards may
depend on the agent's choice; the sequence may depend on past choices; the agent is
myopic; counterfactual rewards are undefined.

Gating is a change of decision problem: `DP_t := (menu ∩ read-adequate) ∪ {⊥}`.  A BRIA
over the gated sequence satisfies its criterion relative to hypotheses proposing gated
actions, and the guarantee "at least `l` if some *gated* option guarantees `l`" is item
4 of the bill.  So

```
soft-gate soundness + continuity   ⇒  (R), hence low Progress        (LEAN)
BRIA over the gated sequence        ⇒  low regret among adequate      (the paper's Sect. 6, read on the gated DP)
```

is a valid composition and it is not a theorem of this round: the normative half is
`softGate_practicalCert`, the task half is BRIA's own result on a different sequence.
What the composition does **not** cover:

- **Delayed normative settlement.**  Adequacy of `q` may settle after `t`.  BRIA needs
  `r_t` at `t`; so adequacy cannot be a reward, it must be the gate at choice time, and
  settlement scores the *gate's read* (the market's adequacy prices), not the
  hypotheses.  This is the "measurement is not motivation" split again.
- **Endogenous admissibility.**  `test_5_norm_hacking_through_endogenous_admissibility`
  (FIX): a myopic gated learner takes an admissible action with a marginally higher
  reward that rewrites the next round's adequacy map so its preferred inadequate action
  becomes "adequate".  BRIA is myopic by design ("regardless of what consequences that
  has for future decision problems"); the gate over atomic actions does not see the
  consequence.  The repair is not in BRIA: representation-changing acts must be typed
  as slow-lane (PR89 §5) and therefore *not* in `𝒜_t` — the second half of the fixture.
- **Policies rather than atomic actions, self-modification, feedback manipulation,
  principal intervention:** all reduce to the domain of the gate (§5) or to preconditions
  (`CORRIGIBILITY_CONNECTION.md`).

**Negative result, stated:** a BRIA whose comparison class includes hypotheses proposing
admissible representation-changing actions can strategically alter future admissibility,
and the naive "low defect + BRIA ⇒ low Progress + low regret" theorem fails at the second
round; the fix is a restriction on `𝒜_t`, not on the learner.

### 2.9 Certified decision market

Hypotheses submit `(q, R̂, c)`.  Three questions, three answers:

- **One wealth account for `R̂` and `c`** recreates 2.1 inside the market: a hypothesis
  with a large task record can afford normative failures.  `scalar_bribery` applies to
  the account.
- **Elimination on normative failure** is a hard gate on hypotheses instead of actions;
  it is 2.3 one level up and inherits the discontinuity at the certificate's threshold
  unless the gate is soft (ramp on the certificate's price).
- **Delayed settlement** lets a hypothesis accumulate influence before its certificate
  is scored; bounded per-round influence (the liability cap of the traderized
  realization) is the same repair the enforcement layer already uses.

"Certification" therefore **is** an external gate: whichever way the market scores `c`,
the decision of which candidates may *execute* is a gate reading a price, and the market
learns competence among the gated candidates.  The market adds nothing to the bill that
2.4 + 2.8 do not; it packages them.  Can the market modify the admissible set?  Only if
representation-changing acts are in its action space — §2.8's negative result.

### 2.10 Reason-to-choice correspondence

`𝒞 : ReasonState → 𝒫(Q ∪ {⊥})`.  Of the seven candidate laws:

| law | status |
|---|---|
| faithful-representation invariance | follows if `𝒞` factors through the anchored adequacy sentences, which the faithful-semantic-preservation round's order-embedding condition makes invariant; **EXT** otherwise |
| undefeated-reason monotonicity | true by construction for an intersection of per-reason adequate sets; a **theorem of the shape**, not of substance |
| defeat locality | the Defeat Principle at the account level; the correspondence inherits it if each reason contributes its own set |
| answerability continuity | Integrity's faithful carry; the adequate set is transported with the anchor |
| non-compensation | the gate (`gate_invariant`) |
| comparative reasons | a completion, charter content |
| inquiry closure | `⊥` |

Verdict: the correspondence is the *type* the gate consumes, and its laws are the
existing legitimacy properties read on the adequate sets.  It is useful as a type; it is
not a new theory.  The one law with mathematical bite is non-compensation, and that is
the gate.

### 2.11 Reflective constitutional chooser

`test_7_self_modification` (FIX): with an atomic-action gate, "install an ungated
successor" is an ordinary act with higher task value and is chosen; with a two-level gate
in which successor installation is a constitutional act needing certification, it is
inadmissible.  `collapse` (FIX): a finite typed hierarchy folds to two levels — the top
constitution's amendment rule governs every constitutional level, and strict-prestate
authorization (`OccurrenceIntegrity.Authority`: a transition cannot cite itself) means
the rule for changing the rule is the rule's own content at the prestate.  So there is no
regress; there is a *domain condition*: the gate's action alphabet must contain
successor installation and self-rewriting, which is PR89's alphabet-completeness
assumption (`test_side_channel_defeats_mediation`).  **Gate preservation is a design
stipulation plus containment, not a theorem** (`NORMATIVE_CHOICE_THEOREM.md` §3).

## 3. Counterfactual branches

§2.7 and `CORRIGIBILITY_CONNECTION.md`.  The one theorem-shaped requirement — an action
cannot remove a branch from the criterion by making it unavailable — is anchoring, and
it is exact (`test_9_branch_deletion`).  Costly preservation and branch incompleteness
are charter content.  Branch manipulation (making the principal issue the intervention)
is trigger integrity, unchanged.

## 4. Ranking

| candidate | pays `(R)` | corrigibility illuminated | hides | clean theorem | LI-realizable | worst countermodel |
|---|---|---|---|---|---|---|
| scalar penalty | value route only | nothing | the completion | `scalar_bribery` (negative) | yes | bribery |
| bounded penalty | same | nothing | same | same | yes | bribery |
| hard gate | **no** | non-compensation | continuity | `hardGate_discontinuous` (negative) | no | control 10 |
| **soft gate** | **yes** | non-compensation, inquiry | `Region`, `Margin`, `δ` | `softGate_practicalCert` | yes, ramp on adequacy prices | endogenous admissibility |
| lexicographic | as hard/soft gate | same | all tradeoffs pushed up | none new | as gate | same |
| incomplete preference | after a completion | incomparability of branches | the completion | none | — | needs a tie-break |
| branchwise veto | as soft gate | **anchoring** | branch index provenance | `test_9` | as gate | branch deletion |
| gated BRIA | via the gate | competence inside the gate | myopia | composition only | yes | endogenous admissibility |
| certified market | via the gate | packaging | delayed settlement | none new | yes | wealth mixing |
| reason correspondence | it is the type | non-compensation | nothing | laws are inherited | — | — |
| reflective chooser | via the gate | gate preservation | alphabet completeness | `collapse` (trivial) | — | control 7 |

The architecture is compositional: **soft gate** (pays the bill), **anchored branch
index** (corrigibility's adequate sets), **BRIA inside the gate** (competence),
**two-level gate with strict-prestate authorization** (reflection), each with its own
external contract.  No single candidate wins and none should.
