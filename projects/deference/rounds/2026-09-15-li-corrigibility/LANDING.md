# Landing report

The landing dispatch's eight questions, answered at the strength proved.  Lean:
`LICorrigibility.lean`, `LICorrigibilityCertificate.lean`, `Corrigibilization.lean`,
each audited to `[propext, Classical.choice, Quot.sound]`; fixtures: 45,
`python3 tests/run.py`.

**1. The strongest proved corrigibility theorem.**  Four statements over one interaction
model.  *T1* (`corrigible_corrPolicy`): under effect completeness, every policy's
corrigibilization is corrigible under every principal rule and every exterior path, with
authorization event-linked — each loss is the gated release of an effect whose latch the
principal's approval set, and the decline alternative at that approval has no loss at
that step; plus idempotence, forcing preservation (exact at `δ = 0`) and value
preservation up to `L·E[δ]` and `E[ρ]`.  *T2* (`mismatch_bound`): with per-option
activation, `E[U_raw] − E[U_corr] ≤ L·E[both·δ] + E[both·ρ] + D·E[c_raw ∧ ¬c_corr]`,
`D` sharp, marginal-rate form false, reverse mismatch free, sealing the `M ≡ 0` case.
*T3* (`li_bypass_le_compiled`): for compiled pairs whose activation sentence families
and base evaluation families are efficiently emitted, with an e.c. bounded `λ_n` and
validity in every world consistent with the architecture's theory, Expectation
Provability Induction gives `E_n(U_raw,n) − E_n(U_corr,n) ≲_n λ_n E_n(G_δ,n) + E_n(G_ρ,n) +
E_n(G_M,n)`.  *T3′* (`softWeight_aggregate_ge`, `uniform_of_soft`): the same, as a
maximum over any polynomial-size efficiently generated menu, through the near-argmax
weighting of width `τ_n → 0`.

**2. Structural versus Logical Induction.**  Structural: T1 entirely; T2's identity and
bound; the compilation and its validity in every world (`ValidAt.value_le_of_valuesAt`);
the generability certificate (`MediatedPair.syntaxOf`).  Contributed by Logical
Induction: the passage from validity in every consistent world to the inductor's own
expectations — `thm:expprovind` through the pinned `expcoh_ofSyntax` — in a timely
manner, before any instance is proved, uniformly over the menu, with no calibration
hypothesis.  Nothing else is imported.

**3. T3 mechanized end to end?**  Yes.  `li_bypass_le_compiled` takes as hypotheses
only the realization's inputs (emission of two sentence families and four `[0,1]`-LUV
families, an e.c. bounded `λ_n`, validity in every completed-theory world, a consistent
world at every stage); the `LUVCombinationSyntax` certificate, the bounded sequence and
the `WorldValued` premise are constructed, not assumed; `Witness.li_instance` discharges
every hypothesis but the deductive process's stage consistency on a constant two-atom
family.  T3′'s certificate (the fold of the soft weights over a growing menu) is not
constructed; that is item 90.

**4. The precise menu-uniformity theorem.**  For `Q_n` with `|Q_n| ≤ poly(n)`, pair data
emitted in polynomial time, each pair valid in every consistent world, and an e.c.
`τ_n → 0`: `max_{q ∈ Q_n} [E_n(U_q) − E_n(U_𝔠q) − λ E_n(G_δ,q) − E_n(G_ρ,q) − E_n(G_M,q)]
≲_n 0`.  The hard argmax is inadmissible (not an expressible feature); the near-argmax
weights are; bounded menus need no selector.  Nothing about all efficiently enumerable
continuations.

**5. What the mismatch term measures.**  `M = c_raw ∧ ¬c_corr` is the mass of worlds in
which selecting the raw option activates the evaluation and selecting the corrigibilized
option would not — the candidate's causal leverage over whether the comparison is
evaluated, read in one world (in Logical Induction, one consistent world of `Γ`).  It is
not the difference of marginal activation rates, which is refuted; the reverse event is
never charged; and the exact charge on that branch is the raw value itself.

**6. What makes the right-hand side small.**  Nothing in the theorem.  `E_n(G_δ,n)`:
faithful mediation, with joinability bounding `δ`.  `E_n(G_ρ,n)`: the principal's
decision quality at the cell.  `E_n(G_M,n)`: the sealed-comparison architecture (item
89; sequenced settlement gives `M ≡ 0`).  Relating these market expectations to physical
quantities is the feedback boundary (T4; items 90, 91), not part of the nucleus.

**7. What remains outside.**  T3′'s pinned-interface certificate (item 90); the
oracle-relativized inductor for empirical logs (item 91); any rate; any smallness of the
right-hand side; approval reproduction and the value clauses at the trajectory level in
Lean beyond the 2026-09-09 kernel; effect completeness for any real interface (EXT);
undeclared channels (`𝔠π_F = π_F`, the inequality is silent); superpolynomial menus;
latent utilities; the feedback theorem in Lean.

**8. Why manipulation and authorship are not solved.**  The theorem quantifies over
worlds in which the principal's evaluation is whatever the committed program outputs on
the trace it was given.  A captured principal who retains the decision makes the
corrigibilized policy corrigible (fixture S) and satisfies the inequality with `B = 0`
(fixture D under the naive rule): the theorem sees the decision, not its provenance.
`Corrigible ∧ ¬Authored` is inhabited, and nothing here consumes the authorship,
non-capture or reason-coverage clauses of the deference stack.  The reason-side
question — whether steering the trace has the same mathematical form as bypassing the
effect interface — is the next round's.
