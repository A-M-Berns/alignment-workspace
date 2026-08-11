# Finish the Φ-Regret Applicability Bridge

You are working in the **Alignment Workspace** repository on the **Leverage / normative learning** research program.

## Operating instructions

Work in an **isolated git worktree and branch**. Do not modify the maintainer’s active checkout or disturb parallel work.

Start from the latest integrated `main`. Before doing research or implementation, inspect:

* `RESEARCH_STATE.md`
* `PRIORITIES.md`
* `DECISIONS.md`
* `PROVENANCE.md`
* `projects/leverage/README.md`
* the current leverage consolidation / learning-track materials
* `projects/leverage/rounds/2026-08-11-phi-regret-prep/`
* `projects/leverage/rounds/2026-08-11-phi-regret-applicability/`
* especially:

  * `PHI_REGRET_APPLICABILITY.md`
  * `RED_TEAM.md`
* any relevant tests and implementations those rounds reference.

Treat the **Near miss** verdict from the applicability audit as controlling. Do not silently revert it or claim that Φ-regret already applies.

The aim of this round is to determine whether the identified near miss can actually be repaired.

---

# Research context

The Leverage program is trying to construct a theory of **reason-guided normative learning**.

The emerging architecture distinguishes at least:

1. **Answerability** — changes remain answerable to the agent’s prior commitments and history.
2. **Reasons-responsiveness / local legitimacy** — individual changes must be licensed by reasons rather than merely selected because they are profitable under the learning objective.
3. **Genuine online learning** — over time, the learner should not systematically persist in patterns that identifiable lawful repairs would improve.

The current candidate for (3) is a Φ-regret-style theorem.

The target philosophical interpretation is deliberately limited:

> A learner has learned, in one substantive online sense, when no fixed historically lawful repair program continues to outperform its actual behavior at a positive asymptotic rate according to the charge/loss structure.

This is **not** a theorem about moral truth, convergence to a uniquely correct normative theory, or legitimacy being reducible to profitability.

The separation between legality and learning is essential.

---

# Current Φ-regret state

The previous round audited Blum & Mansour (2007), especially Theorem 18.

Current verdict:

**Near miss.**

The good news is substantive:

* causal guarded comparator programs have the right history-dependent modification-rule shape;
* Blum–Mansour Theorem 18 permits history-indexed modification rules;
* frozen filings + actual-prefix guards + no solvency/suspension coupling give an additive per-round loss object;
* full counterfactual charge vectors are available;
* losses are bounded;
* no clearly superior neighboring Φ-regret theorem was identified.

But the attempted instantiation failed on two interfaces.

## Failure 1: horizon-growing action identity

The repository currently treats responses carrying occasion-specific ledger effects as distinct global actions.

Although there are semantically only about eight local response choices, repository-native equality yields

[
N_T = 3T+5.
]

Plugging this into the Blum–Mansour bound

[
O(\ell_{\max}\sqrt{T N\log K})
]

makes the bound linear in (T).

The proposed repair is a **fixed semantic action alphabet of eight labels**, with an occasion-local decoder that constructs the corresponding repository response / ledger effect.

This repair is plausible but **not yet proved**.

## Failure 2: comparator non-capture

The theorem-facing legality adapter sanitizes callback arguments but arbitrary Python closures can capture tariff/profit data from their environment.

Thus profit-independence is currently an **audit fact about particular comparator programs**, not a structural capability guarantee.

For the finite current comparator class, a complete finite audit may be sufficient. A declarative DSL or stronger capability boundary is a possible later generalization.

---

# Controlling question

## Can we actually construct a regret-preserving fixed-eight-label interface that makes Blum–Mansour Theorem 18 apply to the frozen item-30 environment?

Do not assume the answer is yes.

Attempt to prove it.

If it fails, identify the precise mathematical obstruction and produce the smallest exact counterexample.

---

# Required construction

Define a fixed theorem-facing semantic action type

[
\Lambda
]

with the intended **eight labels**, independent of occasion (t), ledger IDs, and horizon (T).

The labels should encode only the semantic decision being made, not occasion-local bookkeeping identities.

For every occasion (t), define an occasion-local decoder

[
d_t:\Lambda_t^{\mathrm{available}}\to A_t
]

or an equivalent total/retraction formulation suitable for Blum–Mansour.

Here (A_t) is the repository-native response set.

The decoder may use public occasion-local context needed to instantiate ledger effects, obligation IDs, etc.

It must not smuggle horizon-growing identity back into the theorem-facing action alphabet.

Then determine whether each lawful comparator program (\phi) induces a corresponding theorem-facing transformation

[
\widetilde F_\phi^t(x_t):\Lambda\to\Lambda
]

such that decoding commutes appropriately with the repository-level intervention.

The key object to establish is a diagram morally of the form

[
d_t!\left(\widetilde F_\phi^t(x_t)(\lambda)\right)
==================================================

F_\phi^t(x_t)!\left(d_t(\lambda)\right),
]

with whatever qualification is actually required for unavailable labels, identity branches, or local retractions.

---

# The lemmas you should try to establish

Do not merely implement an eight-value enum. Prove the representation is mathematically harmless.

At minimum investigate and, where true, establish:

### A. Uniform finite action lemma

There exists a fixed theorem-facing action alphabet (\Lambda) with

[
|\Lambda|=8
]

for every horizon and every occasion in the frozen environment.

No ledger ID, case ID, obligation ID, date, or occasion-specific identity is part of theorem-facing action equality.

### B. Decode adequacy

Every repository-native response available at an occasion corresponds to the appropriate semantic label, up to intentionally irrelevant bookkeeping identity.

State precisely whether the decoder is bijective, surjective, partial, or uses a retraction.

Do not hide multiplicity if distinct repository responses with the same semantic label can differ in later behavior.

If such multiplicity matters, that may kill the reduction.

### C. Loss preservation

Define theorem-facing loss

[
\tilde\ell_t(\lambda)
=====================

\ell_t(d_t(\lambda)).
]

Prove that actual learner loss is unchanged by moving to the label representation.

### D. Comparator-map preservation

For every comparator in the declared finite lawful class, prove that its repository intervention factors through the semantic labels.

That is the central test.

If a comparator distinguishes two repository responses that share one semantic label in a way relevant to charge or future state, identify that explicitly.

### E. Φ-regret preservation

Prove that regret computed in the fixed-label representation equals the intended historical repair regret in the frozen repository environment:

[
R_T^{\Lambda}(\phi)
===================

R_T^{\mathrm{repo}}(\phi)
]

or state the strongest exact equality/inequality that really holds.

This is the theorem that closes the current near miss.

### F. Closure

Every induced modification rule must close on the fixed theorem-facing action set.

Unavailable semantic actions must be handled without introducing fake low-loss actions or unbounded penalties.

Reuse the previous retraction/padding result if appropriate.

### G. Additive-loss boundary

Verify rather than assume the conditions under which replay loss equals a sum of local counterfactual losses.

The intended v1 boundary is approximately:

* frozen arrivals / filings;
* actual-prefix guards;
* no suspension;
* no solvency coupling;
* no post-hoc affordability deletion;
* bounded full-information charges.

State the exact assumptions.

Do not generalize the theorem to unrestricted replay.

---

# Comparator class audit

Materialize the complete intended finite comparator class for item 30. The previous state refers to **nine programs**, with two not yet implemented.

For all nine:

1. state the comparator in human-readable mathematical terms;
2. implement/materialize it if missing;
3. verify it is fixed ex ante;
4. verify its guard is causal/predictable from the allowed pre-action state;
5. verify it closes on the fixed semantic action type;
6. verify its reasons-responsiveness/legal certification behavior;
7. verify that it does not inspect charge, tariff, profitability, account balance, future data, or other prohibited variables except insofar as the current research specification explicitly permits them.

Because arbitrary Python closures defeat argument sanitization, either:

* perform a **complete finite non-capture audit** of the nine comparator programs and make the theorem explicitly conditional on that audited finite class; or
* replace the callback interface with a genuinely non-capturing declarative/capability-safe representation.

Do **not** build a large DSL unless it is genuinely the cheapest clean solution.

For this round, a mathematically explicit finite audit is acceptable if sufficient.

---

# Blum–Mansour theorem instantiation

If and only if the fixed-action bridge succeeds, give an explicit hypothesis-by-hypothesis mapping into Blum & Mansour Theorem 18.

Use the correct dependence:

[
R_T(\phi)
=========

O!\left(
\ell_{\max}\sqrt{T,N\log(MK)}
\right).
]

For the intended configuration:

* (N=8), if proved;
* (M=1), if using the always-on selector;
* (K=|\Phi_{\mathrm{law}}|), expected currently to be 9 if all nine programs survive the audit.

Do not replace this with a bare (\sqrt{T\log K}) bound.

Distinguish carefully between:

* expected loss of the learner’s mixed action;
* realized sampled trajectory loss.

If the source theorem only gives the former, state that. Do not add concentration unless you actually prove or cite the needed result.

---

# Desired positive theorem

If everything works, formulate the strongest clean theorem of approximately this shape:

> **Frozen Lawful Φ-Regret Theorem.**
> For the specified frozen normative-learning environment and finite audited class (\Phi_{\mathrm{law}}) of fixed causal historically lawful repair programs, there exists an online learner whose expected cumulative charge regret against every (\phi\in\Phi_{\mathrm{law}}) is
>
> [
> O!\left(\ell_{\max}\sqrt{8T\log |\Phi_{\mathrm{law}}|}\right)
> ]
>
> up to the exact constants/dependence inherited from Blum–Mansour Theorem 18.

Do not use this exact wording if the hypotheses or bound require modification.

Then derive the downstream learning consequence that motivated the project:

If some fixed lawful repair (\phi) would improve charge by at least (\delta>0) on a set of rounds of asymptotic density at least (\rho>0), modulo a bounded transient (B), then cumulative regret to (\phi) grows at least

[
\rho\delta T-B.
]

Therefore a learner with (o(T)) Φ-law-regret cannot permit such a recurrent certified failure pattern indefinitely.

Formalize this carefully.

This is the candidate bridge from **low regret** to a substantive sense of **learning from recurring reasons-responsive failures**.

Keep the interpretation narrow: it retires certain recurrent correctable failure patterns relative to the chosen comparator class. It does not prove global normative adequacy.

---

# Negative-result protocol

If the fixed-eight-label reduction fails, do not patch around the failure merely to obtain a theorem.

Instead:

1. isolate the exact obstruction;
2. construct the smallest finite witness;
3. explain whether the problem comes from:

   * semantic action identity,
   * ledger state,
   * comparator factorization,
   * loss dependence,
   * future-state effects,
   * legality,
   * or something else;
4. determine whether the obstruction is:

   * specific to the current encoding,
   * specific to Blum–Mansour,
   * or evidence that ordinary Φ-regret is the wrong learning object;
5. identify the nearest replacement framework only if the failure genuinely requires one.

A clean negative result is preferable to a forced positive theorem.

---

# Verification

Build exact executable tests for all nontrivial interface claims.

At minimum include tests that would fail if:

* ledger IDs accidentally enter theorem-facing action identity;
* the number of theorem-facing actions grows with (T);
* encode/decode changes charge;
* a comparator fails to factor through labels;
* unavailable-action padding introduces artificial regret;
* a comparator can access current/future data;
* an audited comparator captures tariff/profit information;
* suspension or solvency coupling is accidentally reintroduced into the claimed theorem environment.

Use exact arithmetic where practical.

If the repository has an appropriate Lean home for the clean representation lemmas, formalize the mathematically stable pieces there. Do not force Python implementation facts into Lean merely for optics.

Run all relevant house tests, project tests, Lean build/axiom audit if touched, and `git diff --check`.

---

# Research-state reconciliation

At the end, update the workspace so a future agent can tell exactly what is established.

Update as appropriate:

* `RESEARCH_STATE.md`
* `PRIORITIES.md`
* `projects/leverage/README.md`
* the relevant theorem/evidence ledger
* provenance records
* a dedicated round directory under `projects/leverage/rounds/`
* the prompt/report directory

Do not modify `DECISIONS.md` unless an actual maintainer decision is required.

Preserve the distinction between:

* proved;
* derived;
* witness-checked;
* executable;
* audited;
* conjectured;
* open.

If positive, item 29 should be genuinely closed and item 30 should become executable/unblocked.

If negative, record exactly why.

---

# Required final report

Return a concise maintainer-facing report containing:

1. **Verdict:** repaired / still near miss / substantive failure.
2. Whether a fixed (N=8) representation exists.
3. Exact encode/decode construction.
4. Whether comparator maps factor through it.
5. Whether charge and regret are preserved.
6. Status of all nine comparator programs.
7. Status of the non-capture requirement.
8. Exact Blum–Mansour hypothesis mapping.
9. Exact regret bound actually justified.
10. Expected-vs-sampled-loss qualification.
11. Recurrent-failure corollary, if established.
12. What philosophical learning claim is now justified.
13. What remains explicitly unjustified.
14. Tests / formal verification performed.
15. Files changed.
16. Research-state items closed/opened.
17. Commit hash and draft PR URL.

Open a **draft PR** with the result.

Do not merge it.

---

## Standard of success

The point of this round is not to make Φ-regret work.

The point is to discover whether the current **Near miss is genuinely only representation/interface debt**.

A successful positive round leaves us with a precise, auditable bridge:

**historically lawful local repair programs
→ fixed causal Φ-comparators
→ sublinear charge regret
→ retirement of recurrent certified failure patterns.**

A successful negative round tells us exactly why that bridge cannot be made.

Either is scientifically useful.

**Maintainer:** A. M. Berns
**Prompt author/model:** GPT-5.6 Sol (OpenAI)
