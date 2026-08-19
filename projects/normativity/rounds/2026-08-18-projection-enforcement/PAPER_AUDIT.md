# Audit of the rest of the paper

Read against the draft of 2026-08-18
(`generalizing_and_strengthening_logical_induction_katex.md`, 1396 lines). This pass
does not rewrite the paper; this file records what a rewrite would have to fix, ranked
by whether the current text is *wrong*, *under-justified*, or merely *improvable*.

## Wrong, or missing a hypothesis it needs

### §6.4 assumes the market maker's contract at a point of `K`, which is not a world

Theorem 6.4 opens: "Suppose the MarketMaker contract gives
`⟨τ(P) + ζ_E(P), x − P⟩ ≤ ε` for some `x ∈ K`". The source's contract is stated at
**propositionally consistent worlds** — `{0,1}` valuations — and `x ∈ K` is a general
point of `[0,1]^d`. As written the theorem borrows a guarantee it has not been given.

The gap is real and it is closable, and both routes need the same fix: a strategy's
value is affine in the assessment point (`Strategy.value_eq_sum_support`), the cube is
the convex hull of the `{0,1}` assignments on the traded support, so the vertex bound
extends to every cube point. Kernel-checked here as
`ProjectionMarket.value_le_of_forall_bitWorld` and
`ProjectionMarket.marketMaker_day_value_le_cube`.

**Action: state the cube extension as a lemma before §6.4 and cite it there.** It is
one line of text and it removes an unproved step from the current spine.

### §6.4's `M` is an assumed constant that does not need to be assumed

"while the ordinary aggregate satisfies `⟨τ(P), x − P⟩ ≥ −M`" is a hypothesis with no
supplied witness. The source has a computable syntactic majorant, `Strategy.absBound`,
and `Strategy.abs_value_le` bounds the value at any cube point by it given that the
history lies in the cube — which the market's own prices do.

**Action: replace `M` by `A_t = absBound(τ_t)` throughout §6.4, §8.3 and §10.6.** This
is an improvement to the *row* theorem as much as to the projection one; it is not a
consequence of changing constructions. Kernel-checked as
`ProjectionMarket.sqDist_le_slack_add_absBound`.

## Under-justified, or stated more narrowly than the proof needs

### §8.1 requires global nesting where per-date admission suffices

The text derives `B = 0` from world-inclusivity **plus** global nesting
`S_{t+1} ⊆ S_t`. The proof actually needs only that each world assessed at horizon `n`
was admitted by *each* region up to `n`:

```
∀ k ≤ n,  W|_{Φ_k} ∈ Q_k    ⟹    NW_n(E, P, W) ≥ 0.
```

Global nesting plus world-inclusivity implies that, and is strictly stronger — a
nonmonotone support process can still admit a world at every date for reasons of its
own. Kernel-checked as `ProjectionBudget.cumValue_nonneg_of_forall_mem`.

The per-date quantifier is not decoration: `ProjectionBudget.late_admission_is_not_enough`
exhibits data satisfying every other hypothesis, with the world admitted at the final
date and cumulative value `−1/4`. **Action: state the hypothesis per-date, note that
global nesting is a sufficient condition for it, and include the witness.**

### §8.3's prospective charge is presentation-dependent and its side condition is vague

`q_t = (ε_t + M_t) D_t / δ_t` with `D_t = sup_{W ∈ S_t} Σ_j d_{t,j}(W)` charges by the
`ℓ¹` sum of *row* deficits, so two presentations of one region give two charges. And
"under sufficient temporal compatibility, `Σ_t q_t ≤ B` implies the exact preservation
hypothesis" does not say what the compatibility is.

The projection route gives the same shape with the presentation removed and no side
condition at all:

```
q_t = ρ_t · d₂(W|_{Φ_t}, Q_t) / δ_t,        ρ_t = ε_t + A_t,
B   = sup_n sup_{W ∈ S_n} Σ_{k ≤ n} q_k(W).
```

Kernel-checked as `ProjectionBudget.cumValue_ge_of_projection`. **Action: replace
§8.3 with this, and drop "temporal compatibility" — the sum is over dates `k ≤ n` with
each date assessed against its own region, which needs no compatibility.**

### §5.3's second obligation is stronger than needed

"its quantitative projection `Q_t` must admit a finite rational price-visible
presentation on the fragment being enforced" builds a presentation into the
*hypothesis*. Under the projection route the obligation is that `Q_t` be a nonempty
rational polytope in `[0,1]^{Φ_t}` — a property of the set, not of a chosen
description. **Action: weaken the obligation and note that any finite rational
presentation or vertex list exhibits it.**

## Improvable, given what this pass proved

### §9 should be demoted, not finished and not deleted

§9.2, Lemma 9.2 and Theorem 9.3 build toward `d_∞(P, K) ≤ δ` through duality, an
`ℓ¹`-net, and an exact finite dual-distance presentation. Theorem 9.3's separation
direction is the paper's Debt A and is still open.

It is no longer on the critical path. The `ℓ^∞` conclusion follows from the Euclidean
one with the **same** `δ`, because `‖x‖_∞ ≤ ‖x‖_2` and the projected point is the
witness (`ProjectionForce.sup_conformance_of_dist2`). **Action: keep §9.1 as
motivation, move §9.2–9.3 to a section on the `ℓ^∞` theory of row presentations,
mark Theorem 9.3 as open, and remove Debt A from §12's critical-path list.**

### Corollary 9.4 and Theorem 10.6 restate over `d₂`

Corollary 9.4's conclusion becomes `d₂(P_t|_{Φ_t}, Q_t) ≤ δ_t`, and Theorem 10.6's
hypothesis "the day-`t` enforcement trader uses a finite exact distance-complete
presentation of `Q_t^D`" becomes "the day-`t` enforcement trader plays the projection
position `λ_t(proj_{Q_t^D}(P_t) − P_t)` with `λ_t ≥ (ε_t + A_t)/δ_t²`". The boxed
`∃μ_t ∈ Δ(PC(D_t)) ∀φ ∈ Φ_t : |P_t(φ) − Pr_{μ_t}(φ)| ≤ δ_t` survives verbatim, and is
now a corollary rather than the primitive statement.

### §12's suggested file list and theorem surface are stale

`IntrinsicDistance.lean` in the suggested layout is the `d_∞` route. If the projection
becomes the spine, the companion artifact's modules are the five in this round plus the
existing row modules, and the public surface gains
`deductive_projection_end_to_end`, `cumValue_ge_of_projection`,
`cumValue_nonneg_of_forall_mem`, `late_admission_is_not_enough`,
`sup_conformance_of_dist2`. **Action: regenerate §12 from `THEOREM_MAP.md` rather than
by hand.**

## Notation and naming

Checked against the pinned source's vocabulary and against mathlib's, since the
companion artifact has to live in both.

* **Dates.** The paper uses `t`; the Lean development uses `n`, matching the source's
  `Strategy n`, `V n`, `marketMakerError n`. Either is fine in prose, but the paper
  should not use `n` for anything else (it currently uses `n` for the horizon in §7.1
  and `d` for the fragment size, which is consistent).
* **Fragments.** `Φ_t` throughout; do not introduce `F_t`. `F` is overloaded to the
  point of uselessness — fields, filtrations, feature families — and mathlib already
  uses `F` for functors and families.
* **`Support`.** Do not name any Lean declaration `Support`. `Function.support`,
  `Finset.support` and `Strategy.support` all exist and the last one is used in this
  development with a different meaning (the sentences a strategy trades). The paper's
  "support process" is prose; the Lean name for the same object in the merged row work
  is `AssessmentProcess`, which is why the two do not collide.
* **`π_Φ(C_t)`.** No new name is coined for it. The paper calls it `Q_t`; the Lean
  files carry it as an ordinary variable `K` with `IsNearestPoint Φ K p q` saying
  everything that is assumed about it. Nothing in the development needs it to be
  `π_Φ(C_t)` specifically, and giving it a name would suggest otherwise.
* **`S_t` versus `Q_t`.** Both are projections of `C_t` and the paper says so; the
  subscripted letters are far enough apart to keep. `S` for support is unfortunate next
  to `Strategy.support` in the artifact, which is a further reason the Lean side calls
  it an assessment process.

## Things checked and found sound

* §3.4–3.6 (generalized Budgeter, Trading Firm dominance, support-process Logical
  Induction) — merged and kernel-checked in the previous round; untouched here.
* Corollary 3.7 (exact deductive recovery) and Corollary 3.8 (properness) — the
  separating witness is `lateAllTrueLive` and the collapse condition is
  `live_subset_of_finiteDetermined`; both merged.
* §7.2 (preservation under bounded assessed downside) — generic in the added trader,
  which is exactly why the projection route reuses it unchanged. Remark 7.3 is correct
  and load-bearing.
* Remark 6.5 (positivity of `ε + M` is load-bearing) — correct, and it survives the
  move to `ρ = ε + A` because `ε_n = 2^{-(n+1)} > 0` strictly.
* §5.2's projection-loss witnesses — `Δ({00,11})` and its fibre saturation share a
  quantitative projection and differ in live worlds; still the right example.
