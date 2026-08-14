# Assumption audit

Which parts of the crown jewel are assumed, which are constructed, and which are
derived. The point is that low regret must not be assumed: it is a conclusion.

## The split

| | item | status |
|---|---|---|
| **H1** | bounded prospective loss | STRUCTURAL HYPOTHESIS |
| **H2** | `ell_t` fixed before the date's action; adaptivity in the strict past permitted | STRUCTURAL HYPOTHESIS — and weaker than the source allows |
| **H3** | full-information feedback | STRUCTURAL HYPOTHESIS |
| **H4** | finite certified class `Gcal`, fixed before play | STRUCTURAL HYPOTHESIS — the repair-language interface |
| **H5** | margin `delta_g > 0` | HYPOTHESIS in general; **DERIVED** for margin-certified schemas |
| **H6** | coverage: `M_T(g)` outgrows `L sqrt(T \|A\| log (M K_eff))` | STRUCTURAL HYPOTHESIS — the inquiry interface. Stated against the *learning scale*, not against `B_T`, so it does not mention the conclusion's machinery and non-circularity is checkable by inspection |
| — | the learner | LEARNER CONSTRUCTION — Blum–Mansour Theorem 18 |
| — | `R_T(g) <= B_T(g)` for every `g`, simultaneously | **DERIVED REGRET GUARANTEE**, a conclusion of the construction |
| — | `Q_T(g) <= B_T(g)/delta_g` | DERIVED — the surgical lemma |
| — | `Q_T(g)/M_T(g) <= B_T(g)/(delta_g M_T(g))` | DERIVED — this round |
| — | `Q_T(g)/M_T(g) -> 0` under H6 | DERIVED NORMATIVE-LEARNING CONSEQUENCE, **pathwise** on each realized history |
| — | levels 1–2 kernel-checked | `SurgicalRepairBound.lean`, auditing to the three allowed axioms |
| — | `E[N_T] = E[Q_T]`, and `N_T - Q_T` a martingale-difference sum | DERIVED — and the first pass's `E[N_T] = Q_T` was ill-typed, since `Q_T` is random under sampling |
| — | anytime tuning | OPTIONAL STRENGTHENING — not done |
| — | pathwise concentration | OPTIONAL STRENGTHENING — not done |
| — | computation budget | OPEN — unpriced |

**Low regret is nowhere a hypothesis of the crown jewel.** It is produced by the
construction. Corollaries stated conditionally on a regret rate — the asymptotic
one — say so.

## Does the margin smuggle in the answer?

This is the sharpest audit question, and the answer is: not if the two things are
kept apart.

```
normative licence      this is a legitimate response to this reason
performance dominance  this response discharges more theorem-facing debt
```

The certificate delivers the first and never reads a loss. The margin is the
second. They come apart in the fixture in the visible direction: a repair that is
lawfully certified and has margin `-2`.

So H5 is not "assume the repair is the right one". It is "assume that, on the
occasions in question, this licensed response discharges at least a fixed amount
of *this* debt". And for margin-certified schemas even that is derived from the
loss construction under a public side condition.

## Hidden normativity check

The construction needs: public commitments; public entitlement and inferential
structure; public exposure; certificate-based repair licensing; a bounded
answerability loss; online feedback; plus H4 and H6.

It does **not** need, and nowhere contains: a true norm, a correct moral theory, a
final ontology, a privileged critic, a fixed utility target, or a normative oracle.
The merged round's schema checks — no `true_score`, `actual_adequacy`,
`objective_norm` field anywhere — carry over unchanged.

The one place a reader might smuggle normativity in is the interpretation of the
margin. Stated exactly: `delta_g` is a better response **within the answerability
practice**, and specifically discharges more of one bounded public debt. It is not
"closer to hidden normative truth", and the theorem does not become stronger if
one reads it that way.

## The assumptions that are doing the most work

`H4` and `H6`, and neither is a regret question. Everything genuinely mathematical
in the round is downstream of them, and both are stated rather than proved. A
reader who wants to attack the crown jewel should attack those two, not the
inequality.
