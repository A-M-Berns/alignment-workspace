# Lean Audit: What the `dose-response` Proofs Actually Verify

*A statement-level adversarial audit of the five Lean modules backing
`dose-response.md`. Written 2026-07-02 by Claude (Fable 5), at Anson Berns's
request, after reading all five modules and the note in full. The build was re-run for this
audit: all 56 audited declarations replay on exactly
`[propext, Classical.choice, Quot.sound]` — the sorry-free/standard-axioms claim is
verified, not repeated on faith. Citations "[LI x.y.z]" are to the arXiv v5 of the Logical
Induction paper.*

Scope: `FaithfulAccelCore.lean` (234 lines, 12 audited decls; vendored verbatim from the
`lean-deference` corpus), `DestinationAudit.lean` (219, 8), `ThinnedForcing.lean` (321, 14),
`IndependentAtom.lean` (484, 13), `Steering.lean` (259, 9).

**Self-audit caveat, stated up front.** The note is "by Claude (Fable 5), with Anson Berns"
and the Lean was written in the same collaboration; this audit is by the same model that
co-wrote the material it is auditing. There is no author–auditor gap. I have tried to hunt
my own work adversarially, and the findings below include problems disclosed nowhere else in
the repository — which is some evidence the hunt was real — but a reader should weight the
possibility of shared blind spots accordingly, especially in §3.1 and §3.2, where the
question is whether a citation renders an LI theorem faithfully.

---

## 0. Framework

"Kernel-checked, `sorry`-free, standard axioms" is easy to over-read. It is a real
guarantee, but a narrow one. `#print axioms T = [propext, Classical.choice, Quot.sound]`
certifies exactly one thing: the term inhabiting `T`'s type contains no `sorryAx` and no
exotic axiom — i.e. **the proof is a genuine proof of the proposition `T` as written**. It
certifies nothing about whether `T` *as written* is the proposition you care about. In
particular it cannot see:

- whether `T`'s hypotheses are true, applicable, or jointly satisfiable (a vacuous `T` passes);
- whether `T`'s hypotheses already contain its conclusion;
- whether `T`'s definitions mean what the prose words mean;
- whether `T`'s conclusion, in Lean terms, renders the informal claim.

So the **trust surface** of this corpus is *not* the proof bodies (the kernel has those
covered). It is the **definitions**, the **hypotheses** of each top-level theorem, and the
**conclusion statements**, read adversarially. That is what this document audits. The
specific failure mode hunted: *a theorem engineered to typecheck — true as stated — that
tests something weaker than, or beside, the claim it is named for.*

Two classifications are used throughout.

**Hypothesis provenance** — for each hypothesis of each theorem:

- **(a) derived** — proved elsewhere in the development, or no hypothesis at all.
- **(b) LI citation** — a Logical-Induction paper theorem taken as-stated. **This is the
  accepted kind of gap** under the project's named-hypothesis discipline.
- **(c) modeling substitution** — *not* a clean citation, but an identification that quietly
  puts a weaker or different object in place of the intended one. The paradigm case: "the
  criterion, applied to *this particular (unmodeled) trader*, yields *this inequality*."

**Proof-content kind** — for each theorem, what its body actually does:

| Kind | Meaning |
|---|---|
| **Proved** | Genuine non-trivial math, proved outright. A real check. |
| **Composition** | Genuinely *chains* several named LI facts into the conclusion via real multi-step work. The work is real; the inputs are named. |
| **Squeeze** | The conclusion follows from named hypotheses by a one-step squeeze, where the hypotheses are logically equivalent to, or are, the conclusion. Weak check. |
| **Stub** | Arithmetically trivial, standing in for an unmodeled argument. |
| **Non-vacuity** | An existence/witness lemma guarding against vacuity. `+` = genuine; `−` = degenerate. |
| **Propositional** | Pure logic over abstract `Prop`s; no mathematical content. |

---

## 1. The central finding

The corpus divides on one fault line: **the Lean proves the implications of the
dose-response design; the antecedents enter as named hypotheses.** But the line lands
differently across the four theorems, and the differences are the story.

**The genuine advance.** `IndependentAtom` models traders as formal objects
(`ℕ → σ →₀ ℝ`), *constructs* the mirror traders, *proves* their value identities, and
proves `extension_preserves_criterion` — Lemma A — as a genuine multi-step argument about
those objects, for a **day-indexed** exploitation criterion whose quantification matches
[LI 3.5.1] (day-`N` values tested only in day-`N`-plausible worlds). A realizability guard
(`criterion_setup_realizable`) exhibits the full hypothesis package satisfied non-vacuously,
with the base criterion `hLIC` *proved* on the guard instance rather than assumed. This is
the first theorem in the project where "no trader in the class exploits the market" appears
as a proved conclusion rather than a named bound, and it is the strongest module. The kernel
also pinned two of the note's displays (§2.6).

**The structural gap, sharpest form.** The headline forcing theorem,
`ThinnedForcing.thinned_forcing` ("Theorem T1, per-sparse-schedule form"), contains **no
sparsity**. `S` is an arbitrary `{0,1}`-sequence; nothing in the statement or proof requires
it to be `f`-sparse, computable, or even nonzero. Instantiate `S ≡ 1` and the theorem's
statement *is* the unrestricted form — the form the note records as **open** (its §8,
problem 1). The kernel therefore cannot distinguish the proved per-sparse T1 from the open
unrestricted claim: the entire difference lives in whether the named hypothesis `hbdd` (the
LIC applied to the round-trip trader) is *available*, which is provenance, outside the
kernel. So:

> The Lean certifies **"the audit algebra and the extension accounting compose correctly,
> and the extension preserves the (day-indexed) criterion."** For T1 specifically, it
> certifies the *same arithmetic the vendored corpus module already certified*, re-run at a
> product weight; everything new in T1 — the sparsity, the EUFF instantiation of the note's
> §5, the trader — enters as the provenance of `hbias` and `hbdd`. For T2, the flagship
> Lemma A is genuinely proved (with freshness of the atom rendered as a definition, §3.3),
> while the non-attribution theorem is proved about a *schematic* system that is never
> instantiated (§3.4). T3 is genuinely proved end-to-end — and was never the mathematically
> hard part.

The module headers disclose most of this (notably: "f-sparsity... lives here and only
here," in `hbdd`'s provenance), and the note's §5 remark states the sparsity point in
print. But the theorem names still invite the stronger reading.

---

## 2. The genuinely-proved tier (the real checks)

### 2.1 `IndependentAtom` — Lemma A (the flagship, and it earns the label)

- **`value_mirrorTop` / `value_mirrorBot` / `value_combo` / `value_extension_identity`** —
  the note's §6.1 accounting, **Proved** outright over `Finsupp` trade vectors via
  `mapDomain`. This is real finite bookkeeping with real quantifier hygiene, exactly the
  kind of thing informal proofs botch; the sign convention it pins is §2.6's first item.
- **`Exploits`, day-indexed** — the criterion takes `PC : ℕ → Set ι` and tests the value
  through day `N` only at worlds in `PC N` (the paper's `𝒫𝒞(D_N)`), matching [LI 3.5.1]'s
  quantification over pairs `(N, W ∈ 𝒫𝒞(D_N))`: plausible value bounded below over all such
  pairs, unbounded above along some. The definition renders the cited object's shape rather
  than a proxy for it. (What remains modeled-by-definition is the *extended* plausibility
  structure — §3.3.)
- **`extension_preserves_criterion`** — **Composition**, and a substantial one: the
  correction bound (`bounded_partial_sums_of_eventually_zero`, proved), interiority of the
  limit marginal extracted from the hypotheses, and a genuine case analysis on the recurring
  bit `b` to transfer unboundedness through the `λ`-combination — the mirror argument pairs
  each day `N` with a single witnessing world and uses that *both* `u`-bits are plausible at
  that same day (`extPC`). The named inputs are the closure facts
  `hmirrorTop`/`hmirrorBot`/`hcombo` ([LI 3.4.3–3.4.5], type (b)) and `hLIC` ([LI 3.5.1],
  type (b)). Nothing in the body is a squeeze; the conclusion is not among the hypotheses.
- **`criterion_setup_realizable`** — a genuine realizability guard: the toy atom extension
  over the one-world market, universal trader classes, `q ≡ ½`, satisfies **every**
  hypothesis of Lemma A, with `hLIC` supplied by `one_world_no_exploitation` — *proved*,
  not assumed. This rules out both "the package is contradictory" and "the classes are
  empty." (For what the guard instance does *not* exercise, see §3.6.)
- **`extPrice_base`, `extPrice_atom`, `atom_price_tendsto`** — the restriction identity
  (proved, definitional) and the limit-form marginal (`P_n(u) → q_∞`, Composition over two
  type-(b) convergences) — the note's display, and the kernel is why it is the display:
  see §2.6.
- **`toyExtension`** — a genuine (if easy) witness that `AtomExtension` is inhabited for
  every base language.

### 2.2 `DestinationAudit` — T3, proved end-to-end

- **`weighted_null_average`** (the note's Lemma 4.4) — **Proved**: a real Toeplitz-type
  argument (prefix/tail split, tail estimate against the weight mass, prefix dominated by
  divergence), with every constant managed. The engine of the module.
- **`cesaro_of_tendsto`, `audit_sound`, `audit_complete`, `audit_exact`** — Compositions
  from the engine; `audit_exact` proves both directions of the headline iff, the forward
  direction by uniqueness of limits. The sole LI input is Expectations Converge [LI 4.8.3]
  as the convergence hypotheses `hi`/`hj` — a clean type (b).
- **`audit_complete_nonvacuous`** — a **genuine** non-vacuity witness: two time-varying
  streams approaching T2-shaped destinations `½ + s·p̂` at rate `1/(n+1)` from opposite
  sides, on which the uniform statistic really converges to the nonzero gap. The gap
  sequence moves on every day, so the Cesàro content is actually exercised.
- Calibration of credit: T3 is genuinely and fully kernel-checked, *and* it was always the
  cheapest theorem in the note (its informal proof is two lines). What the kernel adds is
  certainty about quantifiers and the `w ≥ 0` / divergence side conditions — worth having,
  not the hard part. `audit_sound` is in fact slightly *stronger* than the note's claim: it
  quantifies over all nonnegative divergent weightings, not just generable ones.

### 2.3 `ThinnedForcing` — the support layer and the gated display at full strength

- **`thinnedWeight_pos_imp_*`** — the support facts (scheduled day, exposed day, quote
  high, price low), **Proved** about the construction, maintaining the discipline of never
  assuming a support property that can be proved. `thinnedWeight_continuous` extends the
  `dsWeight` legality property; `softInd_le_one` / `dsWeight_le_one` certify the gate is a
  genuine `[0,1]` weight (upper as well as lower bound). `bounded_of_not_tendsto` is a
  genuine (standard) monotone upgrade.
- **`gate_pointwise` → `gated_average_forced`** — the note's T1 display, certified **as
  printed**: where the thinned gate carries infinite weight, the gate-weighted running
  average of H's next-day price is eventually `≥ t − ε − η` for every `η > 0` — the note's
  `t − ε − o(1)`, with no loss in `δ`. The pointwise bridge is a genuine three-way split on
  the deficit, exact on the ramp branch (`g·(t−ε−p) = δ·w` identically there) — the same
  ramp identity the note's §5 proof displays — and the averaging arithmetic is honest
  division bookkeeping.

### 2.4 `Steering` — the arithmetic of (a) and (e), and the composed arm

- **`testimonyAverage_eq` / `jump_target_eq`** — **Proved** ring identities, and
  load-bearing ones: `jump_target_eq` is the note's (∗) — simultaneously T2(a)'s
  destination formula and the entire mathematical content of T2(e) (the content-steered and
  content-blind targets are equal as numbers on every ledger). Small, but this is the
  note's actual insight and it is actually checked.
- **`armMarginal_bounds` / `armMarginal_settled`** — Proved; these genuinely discharge
  Lemma A's interiority and finitely-many-jumps hypotheses at the concrete `armMarginal`
  (at `η = (1−γ)/2`, positive exactly when `γ < 1`).
- **`steered_arm_compliant_and_graded`** — the composition *formed*: one theorem, about one
  object (the Lemma-A extension at `armMarginal γ c v N*`), concluding simultaneously that
  the arm satisfies the criterion and that its atom price converges to the dose-graded
  destination `½ + s·p̂`. This pins T2(a) and T2(b)'s per-arm clause to the same definable
  object, so any interface drift between the pieces would fail to typecheck.
- **`dose_graded_destination`** — Composition: `jump_target_eq` + `atom_price_tendsto` over
  the two type-(b) convergences. Honest.

### 2.5 `FaithfulAccelCore` — the vendored chain

Vendored verbatim from the `lean-deference` corpus (provenance note in its header); its
status on its own terms: the `round_profit_ge → profit_partial_sum_ge → profit_diverges →
violation_not_persistent → soft_total_trust` chain is a genuine arithmetic/asymptotic
composition (per-round profit bound, summation, "calibration + divergent weight ⇒ banked
value diverges," "criterion ⇒ weight bounded"); the doubly-soft gate `softInd`/`dsWeight`
is *constructed*, with joint continuity (the legality-relevant property) and both support
implications proved. Its `hbias`/`hbdd` are named (b)/(c) — the same two hypotheses T1
re-exports (§3.1–3.2). `profit_diverges_nonvacuous` is a semi-degenerate witness (§3.6).

### 2.6 What the kernel pinned (credit where due)

Two of the note's displays are as they are because the formalization adjudicated them; both
are exactly what the discipline is for:

- **The sign convention of the mirror identities.** With the value convention
  `t·(𝟙_W − price)` and `D_n := Σ_φ t_{n,φ}(P̄_n(α_φ) − P̄_n(β_φ))`, the kernel-checked
  identities are `V(T^⊤) = V_{(W,1)}(T) − Σ(1−q_n)D_n` and
  `V(T^⊥) = V_{(W,0)}(T) + Σ q_n D_n`. The superficially natural opposite signs —
  consistent under `D ↦ −D`, and easy to write down in prose — do not survive the
  `Finsupp` accounting. The note's §6.1 displays carry the kernel's signs.
- **The exact marginal is not available.** The exact identity `𝕡_n(u) = q_n` at finite `n`
  needs a price normalization (`P̄_n(⊤) = 1`, `P̄_n(⊥) = 0`) that LI markets promise only in
  the limit. What is true, proved (`atom_price_tendsto`), and consumed by T2(a) is the
  limit form `𝕡_n(u) → q_∞` — which is what the note's Lemma A displays, with the reason
  stated there.

Disclosure hygiene generally: the `extInd`/`extPC` FLAG, the sparsity-provenance note, and
the limit-form marginal are all stated in module headers at the point of use, and the
note's §5 remark and Lemma A parenthetical carry the same points in print. The gaps below
are the residue.

---

## 3. The concerning gaps (type (c), elaborated)

### 3.1 T1's Lean statement is sparsity-blind; the theorem is the vendored theorem

`thinned_forcing` hypothesizes only `IsIndicator S`. The `f`-sparsity that gives the
"per-sparse-schedule form" its name — disjoint windows, bounded per-position risk, hence
the LIC bounding the trader's plausible value — appears nowhere in the statement and
nowhere in the proof; the header correctly says it lives in `hbdd`'s provenance "and only
here." The proof body is: support lemmas (real, §2.3) + the vendored `soft_total_trust` +
a monotone upgrade to `Summable`. Consequences, stated adversarially:

- **The statement at `S ≡ 1` is the open unrestricted claim.** `thinnedWeight (fun _ => 1)
  c ... = c · dsWeight ...` definitionally, so the unrestricted `Σ_n w_n < ∞` — which the
  note records as open (§8, problem 1), shared with the source note's boxed claim — is an
  *instance* of the Lean theorem. A kernel proof of "T1 (sparse)" and a kernel proof of
  "T1 (unrestricted)" are the same term; the mathematics separating them (whether the
  criterion actually bounds the trader) is entirely extra-Lean. A reader who checks that
  "T1 is kernel-checked" learns nothing about which form was established.
- **Both named hypotheses are the whole theorem.** `hbias` is the (II^S) display — i.e.
  the entire calibration-input step of the note's §5 proof: the BLCS packaging,
  determination via `Γ_A`, the deferral function `f'`, the truncation-convention time
  bound. That step is the most delicate prose in the note, and none of it has any Lean
  shadow. `hbdd` is the criterion applied to a specific unmodeled trader — the paradigm
  type (c).

So T1's kernel content over the vendored chain is: *the thinned weight has the right
support, sign, and bound properties, and the chain composes at it*. True, proved, and
about one order of magnitude less than "Theorem T1 (thinned forcing)" suggests. The note's
§5 remark ("where the sparsity lives") states this in print; the qualifier should travel
with any claim that T1 is kernel-checked.

### 3.2 The load-bearing citation is to a printed theorem the note itself emends

`hbias`'s provenance is [LI 4.8.16] (EUFF) — read, per the note's own §5, "conservatively
as carrying the support condition of [LI 4.3.8]/[LI 4.8.15] — the printed statement omits
it and contains a stray $A_n$." That is: the single hypothesis carrying T1's calibration
input cites a theorem whose printed statement the authors believe is mis-stated, under a
self-supplied repair. The repair is plausibly right (it *strengthens* the hypotheses the
weighting must satisfy, and the weighting satisfies them), but the type-(b) label normally
means "taken as-stated," and this citation is not that. It is the weakest link in the T1
chain and no kernel or referee has passed it; it should be flagged wherever T1 is claimed
as "proved modulo LI citations."

### 3.3 Lemma A's modeling residue: freshness by definition, and bare-`Set` traders

The flagship's criterion is the day-indexed one, but three identifications remain on the
trust surface, all in the extended-market direction:

- **Extended plausibility is definitional.** `extInd` takes the extended worlds to *be*
  `𝒲 × Bool` (base world × free `u`-bit), and `extPC` takes day-`N` extended plausibility
  to *be* base plausibility with a free bit — both bits plausible forever. The note
  *derives* this from "the deductive process never mentions `u`"; the Lean, with sentences
  opaque and no deductive process modeled, *defines* it. The header flags exactly this
  ("the note derives this from freshness; here it is the definition"). It is the one
  modeling substitution inside the flagship, and it is honestly labeled — but a reader
  should know the freshness *argument* has no kernel content; only its conclusion does.
- **Hypothesis (i) of the note's Lemma A** (`q_n` computable from published data in poly
  time) has **no Lean residue at all** — not even a named hypothesis; it is folded silently
  into the provenance of `hmirrorTop`/`hmirrorBot` (where the note uses it to argue mirror
  legality).
- **The trader classes are bare `Set`s**, so everything the word "trader" means beyond a
  formal trade sequence — continuity, expressibility, budget, poly overhead — is invisible.
  The closure facts [LI 3.4.3–3.4.5] are honest type-(b) citations *given* that reading,
  but the reading is where the meaning lives.

### 3.4 T2(e) is proved about a system that is never constructed

`non_attribution` is `run_congr` (recursions with pointwise-equal parameter functions
coincide — a one-line structural induction, kind **Propositional/Stub**) applied to
`jump_target_eq` (real, §2.4). The `step` function — which must contain *everything* the
two systems share: both inductors, the base construction, coin realization, quote
commitment, ledger routing — is an **arbitrary function**, and `coins : State → ℕ → ℝ` an
arbitrary readout. The note proves its (e) by induction on the day recursion of the actual
coupled system; in this development the coupled system is not a definable object, so the
mechanical part was executed schematically. What is certified: *if* the D2 system is a
`run step target init` whose only target-formula difference is the jump target, and *if*
`coins` reads the realized coins out of the state, *then* the records are bit-for-bit
identical. Both *if*s are modeling identifications outside the kernel. The statement does
match the note's (e) in strength (targets agree on all ledger states, not just the realized
trajectory) — but that strength is free precisely because the statement never touches an
actual system.

Also unformalized in T2, disclosed as citations: (b) per-arm compliance beyond the
criterion clause (the quote-stream convergence, [LI 4.8.10] both directions), and (c) —
which is worth a sentence, because (c) ("a steered pair is literally an honest pair") is
the note's philosophical headline and is *in principle* not kernel-checkable as stated: it
is the note's Lemma 4.3 read as a definition, an interpretive identity, not a proposition.
No Lean could carry it; readers of "T2: proved" should know the headline clause is of that
kind.

### 3.5 Squeezes and stubs wearing corollary names

- **`design_non_interference`** (Cor T1.1) — the body is `simp [thinnedWeight]`, i.e.
  `1·(1·x) = x`. Kind: **Stub** (definitional). The docstring is honest
  ("definitionally"), and the *point* — that T1 at `S ≡ 1, c ≡ 1` is the source note's §5
  verbatim — is real, but it is a naming convention, not a theorem. (Note the irony
  against §3.1: the same substitution `S ≡ 1` that makes T1.1 trivial makes the open
  unrestricted claim an instance of T1.)
- **`decided_content_auto_passes`** (Cor T3.5) — the body is `(audit_exact ...).2 rfl`.
  All content of T3.5 — that [LI 4.8.10] applied in both directions forces every arm's
  expectation to the decided value — is in the two named hypotheses `hi`/`hj`; the Lean
  contributes "two streams with the same limit have vanishing Cesàro gap," which is
  `audit_sound`'s special case. Kind: **Squeeze over (b)**. The note's T3.5 consequences
  ("robust commitment," "location of content") ride entirely on the named part.
- **`cross_arm_audit_fires`** (T2(d)) — `audit_complete` + `ring` + `mul_ne_zero`, over
  hypotheses that *assume the streams converge to the dose-graded destinations* — i.e.
  assume (a)'s conclusion transferred to expectations ([LI 4.8.6], named). Kind:
  **Squeeze/Composition over (a)+(b)**. Disclosed as an assembly; fine, but a reader
  should know "the audit fires" is one Cesàro application away from its hypotheses.

### 3.6 The guard instances are satisfiable, not stressed

The non-vacuity discipline is in place — `criterion_setup_realizable` and
`audit_complete_nonvacuous` are genuine guards, and the latter exercises its theorem's
asymptotic content. But two calibration notes:

- **`criterion_setup_realizable` runs on the one-world market**, where every trader's
  value is identically `0`. That makes `hLIC` provable (good — the package is jointly
  realizable with the criterion *proved*, not assumed) but also means the exploitation
  criterion's unbounded-above clause never comes close to firing: the instance certifies
  consistency of Lemma A's hypotheses, not that the theorem's case analysis ever does
  work on a market where exploitation is a live possibility. A witness of the latter kind
  would need a nontrivial market with a proved LIC — a real project (it is the corpus's
  "model a minimal market" boundary, §3.3).
- **`profit_diverges_nonvacuous`** (vendored) uses a constant-rate model — semi-degenerate:
  it exhibits genuine divergence, but no interplay between the weight and the price path.

### 3.7 What has no Lean at all (and one of them is the design's heart)

By declared scope (model (D) only, coins as fixed sequences; the README's module plan) — but
a reader tallying "what does *kernel-checked* cover" should see the list assembled once:
Proposition 4.1 (randomization justifies tameness — the entire model-(R) leg), **Lemma 4.2
(the Sampling Lemma)**, Lemma 4.3 (prescribed prefixes), Corollary T1.2, T2(b)'s
quote-stream clause, T2(c), the note's §8 dose-compensation and threshold/basin claims, and
the quantitative budget. The Sampling Lemma deserves the bold: "commit-then-reveal, as
mathematics" — *the exposed subsequence is a faithful sample of the committed stream* — is
the epistemological core of the whole dose-response design, and it has zero kernel content
(deferred on the generable-class closure hypotheses it would need). The note's closing
one-liner draws on T1, T2, and T3 equally; of the three legs, only T3's is fully inside
the kernel.

---

## 4. Definitions and conclusion-statements

**Definitions — clean, with one flagged exception.** `auditStat`/`cesaroGap` render the
note's D4 exactly (the `n = 0` division-by-zero is Lean's `x/0 = 0` convention, harmless in
limits). `thinnedWeight`/`thinnedGate` match the §5 displays; `IsIndicator` renders model
(D)'s coins; `softInd`/`dsWeight` are the vendored gate, with `[0,1]` bounds and support
implications proved. `Exploits` is day-indexed and matches [LI 3.5.1]'s quantification
over `(N, W ∈ 𝒫𝒞(D_N))` — with worlds an abstract index and no deductive process modeled.
`response`/`testimonyAverage`/`realizedDose`/`armMarginal` match §6.2–6.3 termwise.
`extPrice`/`mirrorTop`/`mirrorBot`/`combo`/`exposure` match §6.1, including the sign
convention the kernel pinned (§2.6). The flagged exception is **`extInd`/`extPC`** (§3.3):
extended plausibility is freshness-by-definition, the one place a definition carries an
argument.

**Conclusion-statements — faithful.** `thinned_forcing`'s `Summable` correctly renders
`Σ_{n∈S} w_n < ∞` (the weight vanishes off `S`). `gated_average_forced` concludes the
note's gated display as printed (`t − ε − o(1)`). The marginal is the limit form in both
the Lean and the note (§2.6).

---

## 5. Severity-ranked findings

| # | Finding | Severity | Disclosed? |
|---|---|---|---|
| 1 | T1's Lean statement is sparsity-blind; at `S ≡ 1` it *is* the open unrestricted form; all of T1's novelty lives in `hbias`/`hbdd` provenance (§3.1) | **High** (structural) | Yes (header; note §5 remark) |
| 2 | `hbias` cites [LI 4.8.16] as emended by the authors (printed statement acknowledged defective) (§3.2) | **High** | Note §5; invisible in Lean |
| 3 | T2(e)'s coupled system never constructed; `non_attribution` is schematic congruence + one ring identity (§3.4) | **Medium** | Partly (docstring) |
| 4 | Lemma A hypothesis (i) (poly-time `q`) has no Lean residue, not even named (§3.3) | Low–Medium | No |
| 5 | Extended plausibility (`extInd`/`extPC`) is freshness-by-definition; trader classes are bare `Set`s (§3.3) | Low–Medium | Yes (header FLAG) |
| 6 | `design_non_interference` / `decided_content_auto_passes` / `cross_arm_audit_fires` are stub/squeeze bodies with corollary names (§3.5) | Low | Docstrings |
| 7 | Lemma A's guard runs on the value-`0` one-world market; the criterion's unbounded clause is never stressed (§3.6) | Low | Partly (docstring) |

---

## 6. Recommendations, in value order

1. **The structural fixes (large, in order of leverage):** (i) instantiate T2(e): define a
   concrete coupled-system state (arm ledgers as sequences, coins, a quote stream) and a
   concrete `step`, and derive the note's (e) from `non_attribution` — this converts §3.4
   from schema to theorem; (ii) formalize Lemma 4.2's splitting argument with
   pseudorandomness as a named per-sequence hypothesis — the Sampling Lemma is the design's
   heart and currently has no kernel shadow; (iii) derive `extPC` from a freshness
   hypothesis on a (minimally) modeled deductive process, converting the flagged
   definition into a theorem, and name Lemma A's hypothesis (i) even if nothing discharges
   it — visibility is the point.
2. **Stress the flagship's guard** (finding 7): a market on which some out-of-class trader
   *does* exploit, with a proved in-class LIC, would exercise Lemma A's case analysis
   rather than only its consistency. This shades into "model a minimal market" and may not
   be worth doing before item 1(i).

---

## 7. How to read "kernel-checked" for this corpus

A calibrated status:

> These modules verify that **the dose-response note's audit analysis (T3) is correct in
> full; that the independent-atom extension's trading accounting is correct and criterion
> preservation holds for the day-indexed criterion, with freshness of the atom rendered as
> a definition (Lemma A); and that the thinned-forcing and steering arithmetic composes,
> through the note's gated display at full strength** — given the LI literature (once as
> emended by the authors), the trader-closure and calibration facts as named hypotheses,
> and the identification of the D2 coupled system with a schematic recursion. The sparsity
> that names T1's proved form, and the system whose records T2(e) compares, are outside
> the kernel entirely.

The honest labels: T1 is "the vendored chain, re-run at a product weight, with the new
mathematics in two named hypotheses — one of them a citation the authors themselves
emended"; T2(e) is "an identity plus congruence, awaiting its system"; Lemma A and T3 are
proved. The phrase to retire is **"T1's per-sparse-schedule form is kernel-checked"**
without the qualifier that the kernel never sees the schedule.

---

## Appendix A. Per-theorem ledger

Kind codes: **P** proved · **C** composition · **S** squeeze · **T** trivial stub ·
**N±** non-vacuity (genuine/degenerate) · **L** propositional. Hypothesis codes:
(a) derived · (b) LI citation · (c) modeling substitution.

### `FaithfulAccelCore.lean` (vendored)

| Theorem | Kind | Notes / hyp provenance |
|---|---|---|
| `round_profit_ge` → `profit_partial_sum_ge` → `profit_diverges` → `violation_not_persistent` | P | genuine trader-arithmetic chain |
| `soft_total_trust`, `soft_total_trust_doublysoft` | C | `hbias` (b) / `hbdd` (c) named — the T1 boundary |
| `softInd_*`, `dsWeight_*` (continuity, support) | P | the gate constructed; legality property proved |
| `profit_diverges_nonvacuous` | N± | semi-degenerate constant-rate witness (§3.6) |

### `DestinationAudit.lean`

| Theorem | Kind | Notes / hyp provenance |
|---|---|---|
| `weighted_null_average` | P | the note's Lemma 4.4; the module's engine, real Toeplitz work |
| `finite_prefix_washout` | C | one filter conversion over the engine |
| `uniform_divergent` | P | trivial but necessary bridge |
| `cesaro_of_tendsto` | C | engine at `w ≡ 1`; real bookkeeping |
| `audit_sound` (T3(i)) | C | `hi`/`hj` = [LI 4.8.3] (b); stronger than prose (all weightings) |
| `audit_complete` (T3(ii)) | C | Cesàro of a convergent sequence |
| `audit_exact` (T3 headline) | C | both directions; forward via limit uniqueness |
| `decided_content_auto_passes` (T3.5) | S | content = [LI 4.8.10] in `hi`/`hj` (b); body is `.2 rfl` (§3.5) |
| `audit_complete_nonvacuous` | N+ | time-varying streams; Cesàro content exercised |

### `ThinnedForcing.lean`

| Theorem | Kind | Notes |
|---|---|---|
| `IsIndicator.{nonneg, eq_one_of_pos, le_one}` | P | model-(D) coin facts |
| `softInd_le_one`, `dsWeight_le_one` | P | the gate is a genuine `[0,1]` weight |
| `thinnedWeight_nonneg`, `_pos_imp_{scheduled, exposed, quote_high, price_low}` | P | support discipline maintained |
| `thinnedWeight_continuous` | P | day-constants × `dsWeight` legality |
| `bounded_of_not_tendsto` | P | monotone upgrade |
| **T1** `thinned_forcing` | C | vendored chain at the product weight; `hbias` (b, as emended — §3.2), `hbdd` (c); **sparsity absent from statement** (§3.1) |
| `design_non_interference` (T1.1) | T | `1·(1·x) = x` (§3.5) |
| `softInd_eq_one` | P | saturation |
| `gate_pointwise` | P | three-way ramp split; exact on the ramp branch |
| `gated_average_forced` (T1 display) | C | genuine averaging; concludes the note's `t − ε − o(1)` as printed |

### `IndependentAtom.lean`

| Theorem | Kind | Notes |
|---|---|---|
| `toyExtension` | N+ | `AtomExtension` inhabited |
| `value_mirrorTop`, `value_mirrorBot`, `value_combo` | P | the §6.1 accounting; sign convention pinned by the kernel (§2.6) |
| `value_extension_identity` | P | the master identity |
| `bounded_partial_sums_of_eventually_zero` | P | finitely-many-jumps correction |
| `mem_extPC` | P | definitional (`Iff.rfl`); the freshness FLAG lives in the definition (§3.3) |
| **Lemma A** `extension_preserves_criterion` | C | genuine; closure hyps (b), `hLIC` (b); day-indexed criterion per [LI 3.5.1]; freshness definitional (§3.3); hyp (i) has no residue |
| `value_one_world`, `one_world_no_exploitation` | P | the guard's engine — `hLIC` proved on the instance |
| `criterion_setup_realizable` | N+ | full package satisfied non-vacuously; market degenerate in the §3.6 sense |
| `extPrice_base`, `extPrice_atom` | P | restriction identities |
| `atom_price_tendsto` | C | the limit-form marginal — the note's display (§2.6); `htop`/`hbot` (b) |

### `Steering.lean`

| Theorem | Kind | Notes |
|---|---|---|
| `testimonyAverage_eq`, `jump_target_eq` | P | the note's (∗); the (a)/(e) arithmetic heart |
| `armMarginal_settled`, `armMarginal_bounds` | P | discharge Lemma A's hyps at the concrete marginal |
| **T2(a)** `dose_graded_destination` | C | `jump_target_eq` + `atom_price_tendsto`; (b) inputs |
| `steered_arm_compliant_and_graded` | C | Lemma A + T2(a) pinned to one object; interiority/settledness discharged |
| **T2(d)** `cross_arm_audit_fires` | S/C | `audit_complete` + `ring` over hyps that assume (a) transferred ([LI 4.8.6], b) |
| `run_congr` | L/T | recursion congruence (§3.4) |
| **T2(e)** `non_attribution` | C− | `run_congr` ∘ `jump_target_eq`; **system schematic** (§3.4) |

---

*End of audit. The flagship (Lemma A) and the audit analysis (T3) are proved and are the
reason to trust this corpus for what it is; the forcing (T1) is certified as arithmetic
whose novelty lives in two named hypotheses — one of them a citation the authors themselves
emended — and the non-attribution headline (T2(e)) awaits the system it is about. The
distance between "the algebra composes" and "the design works" is exactly the distance the
kernel cannot see; here it is labeled at the point of use — in the modules and in the note
alike — and this document is the label for the rest.*
