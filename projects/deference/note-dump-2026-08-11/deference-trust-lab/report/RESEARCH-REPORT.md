# Deference & Trust — Research Report (Summer-Planning Deliverable)

*[Attribution note, 2026-08-10: wherever this report says "Eisenstat's fast-student/slow-teacher
merge" or similar, it names the lab's construal, whose information structure does not match what
Sam Eisenstat intended (AI reads human beliefs immediately; humans see AI beliefs only at a delay).
See `wiki/eisenstat-conjecture-attribution.md`.]*

*Synthesis of the entire lab: `findings/`, `models/`, `redteam/`, `audit/`, and the new
`lean/` corpus, read against the v2 artifact (`deference-in-logical-induction-v2.md`) and the
principal's "Research Ideas May 2026" (`AGENDA.md`). Every direction below is flagged
**PROVED** (machine- or paper-checked) / **SKETCHED** (LI-paper rigor) / **CONJECTURE** /
**BROKEN** (a red-team found the stated claim false or unearned) / **INTERPRETATION**. Lean
status is **KERNEL-CHECKED** (compiled this run, axioms `[propext, Classical.choice, Quot.sound]`,
no `sorryAx`) or **UNCHECKED**. The single most important discipline carried throughout: a Lean
theorem can kernel-check and still not mean its informal gloss — those gaps are called out
explicitly.*

---

## 1. Executive summary

The lab's through-line is a **reduction**. The question "under what conditions can humans
justifiably trust AI?" is, in the DDB tradition, the question "when does endorsement (epistemic
trust) license deference (instrumental trust)?" — and that, ported into logical induction by the
v2 artifact, collapses to **one premise**: cross-agent **LUV-Total-Trust** of a novice `N` toward
an expert `E`, the conditional martingale `𝔼_n(⌜X·w⌝) ≂ₙ 𝔼_n(⌜𝔼_E(X)·w⌝)` for every
market-generable weight `w`. For the inductor's own future self this premise is **free** (it is the
LI theorem `ccee`, 4.12.3), and Value (deference) then follows from a five-line proof whose other
four lines use only the novice's own coherence. The entire agenda — Eisenstat's fast-student/
slow-teacher merge, legitimacy/corrigibility, updateless deference, Cole Wyeth's UDT1.0⊨UDT1.1, the
diagonal "perfect alignment is impossible" result — turns out to be **the same theorem with the
expert-slot filled differently**, and the open frontier is uniformly **the same object**: *when is
cross-agent LUV-Total-Trust earned between two distinct inductors?* (v2 §10.4; orientation Q5).

Where LI gives the most leverage: (i) it supplies coherence **dynamically and for free** via the
no-Dutch-book criterion, eliminating DDB's convex-geometry machinery and any grain-of-truth
assumption; (ii) it natively handles **self-reference** — the *soft/one-sided* (`≥`, `Ind_δ`) form
of trust survives Gödel's diagonal lemma where the *hard/two-sided* (`=`) form is permanently false,
and this `=`→`≥` pivot is the precise mechanism by which a self-modeling AI can be trusted to *act*
even though its exact credences can never be adopted verbatim; (iii) it lets the trusted expert be
strictly *larger* than the truster (modesty / S4, not S5).

This run produced **11 new kernel-checked Lean files** (finite algebraic cores of every thread) and
a two-stage adversarial audit confirming the pre-existing `LeanDeference.lean` and the v2 §9 honesty
claims are sound. The red-teams downgraded several **headline** claims (not the underlying math):
the Eisenstat "no-feedback ⇒ endorsement FAILS" is really "bias fails *once it flips the menu's
argmax*"; the updateless-deference relation **does not itself discriminate** muggers (a hand-chosen
input does); the UDT1.1 "bound correction" is **formalization-dependent**; the weak-endorsement
liar contradiction leaned on an **unearned** step and must be restated as a value-vs-demand clash.
None of these is fatal; each sharpens the honest statement.

---

## 2. Ranked table of candidate research directions

Ranked by **(tractability over a summer) × (bearing on human–AI trust)**, with red-team status
folded in. "Setting" abbreviations: **LI** = logical induction; **PF** = finite probability frames;
**RP/UDT** = radical probabilism / `udt-representation-theorem/`; **RO** = reflective oracles.

| # | Direction (crisp statement) | Status | Bearing on human–AI trust | Setting | Summer tractability |
|---|---|---|---|---|---|
| **D1** | **Weakening dictionary**: weak endorsement (soft 1-sided Self-Trust) ⇒ weak deference (Value); hard 2-sided endorsement is vacuous on any self-modeler. The `=`→`≥` pivot is the Gödel-survival mechanism. | **SKETCHED** (forward arm solid, =v2 §3); finite cores **PROVED & KERNEL-CHECKED** (`weak-endorsement.lean`, `weak-endorsement-deference.lean`) | The exact line between "adopt its credence verbatim" (impossible for self-modeling AI) and "hand it decisions" (possible, =1-sided trust). | LI + PF | **High** — mostly consolidation of proved pieces + 1 small Lean already checked |
| **D2** | **Eisenstat merge**: `B_t(φ):=𝔼^A_t(⌜ℙ^H_{f(t)}(φ)⌝)`; good feedback + fast `f` discharge the §10 cross-agent premise on the feedback subsequence ⇒ `H` endorses `B` there. | **CONJECTURE**, reduces to SKETCHED under a Hop-2 hypothesis; **red-team: SALVAGEABLE** (the `wubexp` patch is the *wrong theorem*; reroute via `thm:wub` on threshold sentences) | The agenda's constructive payoff: *build* a fast-and-aligned reasoner; feedback-gated "humans trust AI" theorem with a **sharp** no-feedback boundary. | LI (2 inductors + `f`) | **Medium** — Hop-2 standpoint shift is the one true gap; the threshold-sentence reroute is the key first move |
| **D3** | **Cross-agent LUV-Total-Trust characterization** (Q5): *when does inductor `N` trust inductor `M`?* The single open object every thread routes through. Candidate: `M`-estimates `N`-generable + cross-defect→0 on every generable weight, holding on good-feedback subsequences. | **OPEN** (the lab's center of gravity) | This *is* the human–AI trust question in LI form. Closing it closes D2, D7, and the LI half of D5. | LI | **Medium-Hard** — define precisely first; full characterization is likely multi-summer, but a *sufficient condition* on feedback subsequences is summer-sized |
| **D4** | **Updateless deference relation**: `A` updatelessly-defers to `u` iff the diagonal assembly `π_u` globally maximizes `U`; reduces to endorsement on **separable** utility; fails for mugging/Newcomb. | Separable reduction **PROVED & KERNEL-CHECKED** (`updateless-deference.lean`, `UpdatelessDeference.lean`); **red-team: the discrimination is BROKEN as headlined** — `node_value` is a free input untied to `U`, so the relation classifies only hand-built instances | Which new knowledge an AI may use *updatefully* (principal control-endorses resulting policy) vs must handle *updatelessly*. Carves the safe region for value-learning. | RP/UDT | **High** for the fix (derive `node_value` as the EDT-conditional of `U`); **Medium** for the coupled characterization |
| **D5** | **Legitimacy = LUV-Total-Trust; wirehead-decline**: a pointwise-overstating "drug" successor drives the legitimacy defect ≤0, a defect `N` computes from its own data (anticipates) ⇒ abstention. Corrigibility = endorsement of the shutdown map. | Finite cores **PROVED & KERNEL-CHECKED** (`legitimacy.lean`, `legitimacy-corrigibility.lean`); **red-team: SALVAGEABLE** — "wirehead drives defect negative" needs *pointwise* overstatement, strictly stronger than "average report rises" | Formal "AI avoids wireheading the way people avoid addictive drugs." Corrigibility-as-endorsement is real but **provably bounded** (sign-flips on adversarial shutdown). | LI + PF | **High** for the finite shadows (checked); **Medium** for the witness-support characterization the red-team asks for |
| **D6** | **UDT1.0⊨UDT1.1 ⇒ ε-optimal**: a `(1-δ)`-self-belief yields `Vstar(p*)−Vstar(s) ≤ δ/(1-δ)·range`; `(1-δ)`-belief is a correlation device selecting the good Stag-Hunt equilibrium; split self-knowledge into behavioural `δ_b` (load-bearing) vs substrate `δ_m` (unused). | Finite cores **PROVED & KERNEL-CHECKED** (`UDT11Belief.lean`, `unbounded-embedded-agency.lean`, incl. the `δ_m`-agnostic split & 2×2 Stag-Hunt bridge); **red-team: SALVAGEABLE** — the `δ/(1-δ)` "correction" is specific to the R2 contaminated-objective model; under R1 (believe-your-policy) the principal's `δ·range` is right | Tiling/self-trust as a special case of human–AI deference; "concentration of self-belief ≠ correctness." | PF → RO | **High** for the checked shadows; **Medium-Hard** for the general Stag-Hunt closure (Prop 2★) and the RO lift |
| **D7** | **`endorsement⊕` via calibrated anticipation** (superconditioning): `u` is deferrable iff it lands `A` in a *calibrated anticipated* future credence; granularity of the anticipation sub-algebra `Ā` is a **dial** from "defer only to self" (S5) to a permissive class (modesty). | **SKETCHED** bridge theorem on **TRUSTED** scaffolding (`superconditioning-mismatched-ontologies.md` §§3–4) | Operational pre-deployment test: an AI's belief-update is trustworthy iff it lands in a calibrated anticipated future of the principal. Separates legitimate learning from value-corruption. | RP/UDT | **Medium** — same-ontology calibration facts are small finite measure theory, Lean-adjacent |
| **D8** | **Diagonal No-Go + maximality**: no definable self-modeling pair is "perfectly aligned" (hard 2-sided endorsement on a liar `G="E(𝟙_G)<½"`); the *strongest* diagonal-surviving schema is conjectured to be soft 1-sided Self-Trust. | No-go **SKETCHED**; finite skeleton **KERNEL-CHECKED**; **maximality CONJECTURE** (needs a partial order on schemata); **red-team: the oscillation-contradiction framing is unearned** — restate as value(0)-vs-demand(t) | "Perfect alignment is impossible" made precise *and narrow*: only value-pinning alignment is forbidden; the decision-relevant content (Value) survives. | LI vs PF | **Medium** — no-go restatement is summer-sized; maximality is genuinely open |
| **D9** | **Aumann fails under modesty**: two modest (S4, non-Euclidean) agents with a common prior can have common-knowledge-yet-distinct estimates — "agree to disagree." | **CONJECTURE**; finite negative example is **LEAN-ABLE** | Reframes "the AI disagrees with me" from red flag to expected structural phenomenon; identifies what extra condition forces agreement. | PF → LI | **Medium** — finite 3-world example is summer-sized; LI version couples to D3 |
| **D10** | **Local / value-vs-factual deference**: restrict the menu to a sub-class `𝒳_Q`; local weak endorsement ⇒ local Value (DDB open conjecture). Grant Value on `𝒳_fact` while withholding on `𝒳_val`. | **PROVED-shaped** (factual half near-trivial, `ccee` is local in `X`); asymmetry **CONJECTURE** | "Trust the AI about facts, not (yet) values" made formal; deference earned question-by-question. | LI | **High** for local Value (a near-trivial Lean specialization of `value_of_CM`); Medium for the asymmetry |
| **D11** | **Vingean agency = quantified Blackwell dominance** on an abstraction `α`: predict the *outcome* (win) not the *move*, justified because Blackwell–Geanakoplos gives value-of-info ≥0 *for the coarse variable*. Wireheading = Blackwell-anti-monotone. | **SKETCHED / INTERPRETATION** + thermostat counterexample (coarse-predictable ≠ agentic without menu-robustness) | The conceptual root of *why* the deferral function `f` (Vingean future self) is the right trust model at all; ties legitimacy to abstraction. | PF (Blackwell) | **Medium** — a finite value-of-info ≥0 lemma (discharges Q6) is Lean-adjacent; the full theory is exploratory |
| **D12** | **Legitimacy non-transitivity**: LUV-Total-Trust(H→A) ∧ (A→B) ⇏ (H→B); recovered iff `B` is `H`-observable. Trust-laundering via delegation. | **CONJECTURE** | "Alignment is not closed under delegation"; observability is a *design constraint* with teeth. | LI (3 inductors) / PF | **Medium** — finite version close to DDB Lemma 7.2.4 |

**Cross-cutting structural unifier (INTERPRETATION, strongly argued in `lateral.md` W4):** the merge
(temporal coarsening by `f`), the intentional stance (semantic coarsening by `α`), and the
size-problem evasion are *one operation* — **"coarsen-then-trust"** — which suggests D2, D3, and D11
are studying the same theorem at different coarsenings.

---

## 3. The 2–3 most promising directions, in detail

### 3.1 D1 — The weakening dictionary (`=`→`≥` is what survives Gödel) — *develop first*

**Why first.** It is the lab's mandate ("make the weak-endorsement⇒weak-deference correspondence
precise") and it is *mostly already established*: the forward arm is the v2 §3 theorem; the finite
cores are kernel-checked this run; the only genuinely new content is the dictionary-as-a-labelled-
correspondence plus one pivot lemma, which is also checked.

**Cleanest precise statement (the central schema, SKETCHED at LI-paper rigor).**
Let `𝔼_n` be any logical inductor; let an expert supply *novice-observable* (market-generable),
*uniformly bounded* estimates `E_exp(O^j_n)`. **Weak endorsement** is the soft one-sided LUV form
`𝔼_n(⌜X·w⌝) ≂ₙ 𝔼_n(⌜E_exp(X)·w⌝)` for every market-generable `w∈[0,1]` (this *is* `ccee` directed at
`E_exp`). **Then weak deference (Value, LI form) holds:** `𝔼_n(Ŝ_n) ≳ₙ 𝔼_n(O^i_n)` for the softmax
strategy. For `E_exp = 𝔼_{f(n)}` (the future self), weak endorsement is itself a theorem, so the
implication is **unconditional**. The **discharge ledger** (which LI theorem does which of the five
lines) shows lines 2/4/5 are free (Linearity 4.8.4 ×2, Provability-Induction 4.8.10 + the softmax
Gibbs bound), and only lines 3/6 use the one cross-agent premise.

**The Gödel half (SKETCHED; red-team-corrected statement).** Hard two-sided endorsement (`=`) is
unsatisfiable on a self-modeling reasoner. **Use the value-vs-demand form** the red-team recommends,
*not* the oscillation-contradiction form: hard endorsement at `t=½` *demands* the conditional value
`𝔼_n(𝟙(χ)∣ℙ_{f(n)}(χ)≥½) ≂ₙ t=½`, while LI *computes* it as `0` (the conjunction
`χ ∧ ℙ_{f(n)}(χ)≥½` is disprovable, `perkno`); `0≠½`. Both numbers are paper-licensed; the discarded
step `𝔼_n(w)>0` for an illegal (non-`ℙ`-generable) hard indicator was the unearned link. The
*soft* form is satisfiable on the same liar (Self-Trust answers `≈½`).

**Concrete Lean target — what is already machine-checked vs what remains.**
- **KERNEL-CHECKED this run:** `weak-endorsement.lean` (`equality_endorsement_implies_immodest`: hard
  conditional-martingale identity ⇒ immodesty, an independent re-proof of `CM_implies_immodest`);
  `weak-endorsement-deference.lean` (`hard_endorsement_liar_unsat`: the four scalars `0<t, 0<Ew,
  Exw=0, Exw=t·Ew` are jointly inconsistent, genuinely *using* `Ew>0`; `soft_endorsement_liar_sat`:
  the soft `≥` form is satisfiable on the same data). **Fidelity:** these are the *finite, exact,
  real-arithmetic skeletons* of the `=`-vs-`≥` pivot. They do **not** contain LUVs, the market, `≂ₙ`,
  or the diagonal lemma — those enter as scalar inputs. Non-vacuity is certified (drop `Ew>0` and the
  system is consistent; the modest-frame witness gives `<1`).
- **REMAINS INFORMAL:** the forward schema as an LI fact (trusts 4.8.4/4.12.3/4.12.1/4.8.10 from the
  paper, exactly the v2 §9 boundary); the soft⇒hard spectral-gap step (= D8/Q3); the maximality
  conjecture (no partial order on schemata yet — incomparable survivors may exist).
- **Red-team action item (cheap, high-value):** replace `hard_endorsement_liar_unsat`'s contested
  `hw:0<Ew` hypothesis with the value-vs-demand version `hard_endorsement_liar_unsat'` (`condval=t`
  vs `condval=0` ⇒ `False`), where *every* hypothesis is paper-backed. Same two-line kernel clash,
  honest labelling.

### 3.2 D2 + D3 — The Eisenstat merge and the cross-agent characterization it needs — *the agenda's center of gravity*

**Why these together.** D3 is a strict prerequisite for D2 (and for D6's LI lift and D5's external
case). The merge is *v2 §10 run with two agents and a name-swap*: novice = human `H`, expert =
`B_t(φ):=𝔼^A_t(⌜ℙ^H_{f(t)}(φ)⌝)`. The whole Value/endorsement conclusion follows from §10 by
composition **if** the one cross-agent premise can be discharged for this constructed `B`.

**Cleanest precise conjecture (the keystone, the two-hop reduction).** On an `ℙ^H`-generable
divergent weighting `w` whose support sits in `im f`, with `ℙ^H_{f(t)}(φ_t)` computable in time
`O(f(t+1))` (the "fast enough `f`" clause):
`𝔼^H_t(⌜𝟙(φ_t)·w_t⌝) ≂_w 𝔼^H_t(⌜B_t(φ_t)·w_t⌝)`, via
- **Hop 1 (free, SKETCHED):** `H`'s own `ccee`, `𝔼^H_t(⌜𝟙(φ)·w⌝) ≂ₜ 𝔼^H_t(⌜ℙ^H_{f(t)}(φ)·w⌝)`.
- **Hop 2 (the one true gap, CONJECTURE):** swap `ℙ^H_{f(t)}(φ)` for `B_t(φ)` *inside `H`'s
  expectation*; good feedback makes the residual `w`-mean-zero from `A`'s standpoint, but the
  substitution must survive the `ℙ^A`→`ℙ^H` **standpoint shift**.

**The red-team's decisive correction (must be incorporated).** The model's proposed patch — read
`thm:wubexp` (Expectation-Unbiasedness-From-Feedback) with "determined via Γ" replaced by
"`A`-decidable in `O(f(t+1))`" — **invokes the wrong theorem**: `wubexp`'s proof consumes
"determined via Γ" at the step collapsing per-world values to a single `thmval`, and `H`'s market
price has no such single value. **The honest reroute:** price the *decidable threshold sentences*
`ψ^q_t := "ℙ^H_{f(t)}(φ_t) > q"` (truth `A`-decidable by simulating `H` for `f(t)` steps), apply
`thm:wub` (the *sentence* form) verbatim, then integrate over `q`. This converts a false invocation
into a sound argument with one *smaller* residual gap (uniformity in `q`).

**Two structural facts the merge inherits, both load-bearing.**
- **The asymmetry of `f` is essential, not a convenience** (`lateral.md` §3.2, SKETCHED): symmetric
  mutual hard trust is a 2×2 liar; finite mutual soft-CM forces *both* immodest ⇒ the two agents
  *merge into one*. The deferral function pointing one way (ask `A` about `H`'s **future**) is what
  *breaks the regress* and lets `B` exist.
- **Observability is communicational** (`A` publishes `B_t`, `H` reads it as an expressible feature),
  and is *necessary* for the trust premise to even be well-typed.

**The sharp negative boundary (the honest deliverable).** Endorsement holds **only on the
good-feedback subsequence**; off it (the unobservable class — flourishing, values, ethics) `B` is
*unconstrained* and a trader knowing `A`'s bias exploits it. The red-team further sharpens the
no-feedback narrative: a *persistent bias does not by itself break endorsement* — it fails only once
it is **large enough to flip the menu's argmax** (a `−0.10` bias still passes Value in the micro-
example; the cliff is at the argmax-flip). And the **"one big lie"** (idea 6): asymptotic
endorsement is a `≂_w` *average* and is **silent about any single high-stakes round** — "humans
survive the turn intact" is the unmodeled assumption; this is structural, not a detail.

**Lean situation.** `merging-inductors.lean` is **KERNEL-CHECKED** but isolates only the orthogonal
finite mechanism (`bias_only_hurts`: the 2-option deferred return is monotone in the selector weight
when `μ≥½`, so bias-flipping-the-argmax is what hurts). It **correctly does not** attempt the
cross-agent martingale (Hop 2 is not Lean-statable without formalizing LI feedback — any stub would
smuggle the conclusion). **D3 itself has no Lean and should not until the definition is pinned.**

**Definition to pin first (D3).** "`N` LUV-Total-Trusts `M`" — candidate: `M`'s estimates are
`N`-generable **and** on every market-generable weight the cross-defect →0, conjectured to hold on
good-feedback subsequences. This single object also answers "when may a UDT1.0 inductor believe it
is UDT1.1?" (D6 §7) — the decision-theoretic and epistemic threads share one open characterization.

### 3.3 D5 — Legitimacy, the wirehead-decline, and bounded corrigibility — *the safety-facing payoff*

**Why include it.** It gives the AGENDA's flagship intuition ("AI avoids wireheading like people
avoid addictive drugs") its first formal skeleton, on the *same* cross-martingale object as ordinary
deference, with finite cores already kernel-checked — and it produces a genuine *limitative* result
about corrigibility.

**Cleanest precise statements.**
- **Legitimacy = LUV-Total-Trust** (definition + reduction, SKETCHED): naming the §10 premise.
  `Leg-defect = 0` ⇒ Value (§10.2 restated). Honest caveat: this is a *naming*, contentful only
  modulo "truth-tracking ⇒ small defect," which is the D3 open characterization.
- **Wirehead-decline (PROVED finite, KERNEL-CHECKED):** if the drugged successor *pointwise*
  overstates the target (`θ_x ≤ E_drug(θ)_x` on positive `π`-mass and positive witness weight), the
  legitimacy defect is `≤0` (strict on a strict overshoot); it is a function of novice-side data, so
  `N` *anticipates* it; the drug-trader has negative expected profit, so **abstention is
  no-Dutch-book**. The honesty contrast: the drug-self is *happier and self-coherent* yet
  *illegitimate-to-N* — separating "confident/calibrated to itself" from "truth-tracking for N,"
  which is the whole wireheading distinction.
- **Corrigibility = endorsement of the shutdown map, and its limit (PROVED finite, KERNEL-CHECKED):**
  with comply-advantage `adv(S) = Σ P_A(x) s_x (2d_x−1)`, an endorsement-faithful signal (`s·(2d−1)≥0`
  pointwise) gives `adv≥0` (comply); an adversarial signal (`s·(2d−1)≤0`) gives `adv≤0` (resist). The
  **same weighted sum flips sign** — so corrigibility-as-endorsement *cannot* be unconditional: an
  AI that defers to *every* shutdown is one a saboteur can shut down. This is the endorsement-calculus
  analog of the Soares-et-al. corrigibility-vs-utility tension, as a one-line sign flip.

**Red-team correction (must incorporate).** The headline "the wirehead drives the defect *strictly
negative*" is **false as a consequence of "average reported utility rises"**: a "euphoric-but-numb"
drug (`E_drug=(.95,.20)`, `θ=(1,0)`, `π=(½,½)`) raises the average report yet gives defect `+1/40`.
The strict-negativity needs the **pointwise** overstatement hypothesis `hover`. Also, "declines" is
honestly a **tie** (`V_now(drug)=V_now(abstain)`), i.e. "never strictly prefers the drug." The
right next step: characterize *which* `E_drug` give defect ≤0 **on the model's own witness support**
`w=Ind(E_drug>p)` — connecting directly to D3.

**Lean situation.** `legitimacy.lean` and `legitimacy-corrigibility.lean` are **KERNEL-CHECKED**
(5 theorems, standard axioms): `defect_decomp` / `comply_iff_endorsed` (pure linearity, faithful &
universal), `wirehead_declined` (pointwise hypothesis, signed-sum conclusion — a real monotonicity
step, non-vacuous), `endorsed_signal_complies` / `adversarial_signal_resists` (the sign-flip
duality — the crispest *limit* result). **All explicitly do not** model the LI asymptotic
anticipation, no-Dutch-book against *every* trader, or any updateless-precommitment content — those
are flagged SKETCHED/CONJECTURE. The decline works *only* because the agent scores with day-0
prices, i.e. is **updateless about its evaluative standard** — the Lean *encodes* this, does not
derive it (the derivation is D4/D7/Q8).

---

## 4. The Lean situation

**Pre-existing `lean-deference/LeanDeference.lean`: CONFIRMED sorry-free**, axioms
`[propext, Classical.choice, Quot.sound]` only (treated as established; not recompiled). The stage-2
**adversarial correspondence audit** re-read every declaration against the v2 prose and the
bottom line is: **v2 §9 is honest.** No declaration rates OVERSTATED, VACUOUS, or MISLEADING. The
three ways a "machine-check" section overstates — claiming the LI theorems are proved when assumed;
claiming the finite *impossibility* is verified when only an algebraic tail is; letting an all-inputs
identity masquerade as a deference result — §9 commits **none**:
- `value_asymptotic` has **exactly the five LI results as named hypotheses** (one-to-one with §3),
  conclusion is the *composite* Value, no premise equals the conclusion — it honestly verifies "the
  §3 composition is valid," not the LI theorems.
- `decomposition` is correctly billed a *keystone identity*, not a deference claim; `value_of_CM` is
  the exact (δ=0) shadow; `softmax_lower_bound` discloses its **cruder** `(card J)·δ` constant.
- **The biggest disclosed gap:** `CM_implies_immodest` proves only `hard CM ⇒ immodest` (a one-line
  tail); §5.2's actual content `soft CM (finite) ⇒ hard CM ⇒ immodest` — the **soft⇒hard spectral-gap
  step, the only place finiteness is forced and whose failure on infinite frames is the home of
  modesty — is prose only.** The doc and docstring say so. *Completing this is the single
  highest-value future Lean target (Q3).* Two reader-vigilance items (`soft_nonneg`'s name suggests
  softmax but proves argmax/δ=0; `CM_implies_immodest` as "§5.2 checked") are real but disclosed.

**New Lean this run: ALL 11 candidate files COMPILE cleanly** (serial compiles by the dedicated
Lean-verify agent; ~7 GB RAM respected), **every theorem depends only on the standard axioms — no
`sorryAx`, no `sorry`/`admit`.** The *only* change made was adding missing imports (`Real.Basic`;
ring/order/tactic modules); **no statement or proof body was altered.** Per-file, kernel-checked and
faithfulness-audited:

| file | what is now machine-checked | honest boundary (NOT checked) |
|---|---|---|
| `merging-inductors.lean` | softmax-bias monotonicity (`bias_only_hurts`); reversal at μ=0 certifies non-vacuity | `B` an inductor; cross-agent martingale (Hop 2); any `≂ₙ` |
| `legitimacy.lean` | legitimacy-defect decomposition; sign under a pointwise-overstating drug | LI anticipation; no-Dutch-book vs every trader |
| `legitimacy-corrigibility.lean` | decomposition + **corrigibility sign-flip duality** (comply/resist) | "endorsed/adversarial" are pointwise encodings, not derived |
| `weak-endorsement.lean` | equality-endorsement ⇒ immodesty (independent re-proof of §5.2 tail) | soft⇒hard spectral-gap reduction (prose) |
| `weak-endorsement-deference.lean` | hard-liar contradiction vs soft-liar satisfiability | diagonal lemma, LUVs; `Exw=0`/`0<Ew` are inputs |
| `UDT11Belief.lean` | `(1-δ)(Vstar p*−Vstar s) ≤ δ(hi-lo)` (corrected bound); δ≤½ corollary; δ=0 corner | pointwise→whole-policy bridge (in `hsel`) |
| `unbounded-embedded-agency.lean` | same + **δ_m-agnostic self/env split** (unused `δm` *is* the claim) + 2×2 Stag-Hunt bridge & converse | general Stag-Hunt closure (CONJECTURE); RO lift |
| `updateless-deference.lean` | separable ⇒ updateless=updateful (`defers_of_local_argmax`) | coupled non-deference direction; the relation does *not* discriminate muggers (red-team) |
| `UpdatelessDeference.lean` | split optimum = global optimum (independent formulation); `sup'` defeq spot checked OK | coupled case |
| `lateral-dtype.lean` | "why-ain'cha-rich" re-skin of CM ⇒ Value (`WAR_of_argmax`) | −δ log k slack; asymptotics |

**Two fidelity items a reader must keep (not bugs):** (1) `stag_hunt_select`'s `hb,hc` are **inert**
— the checked statement is the bare `hgap ⇒ c ≤ (1-δ)b`; the non-degeneracy framing is prose. (2)
Every "endorsed/separable/drug" hypothesis is a **structural or pointwise encoding** of the informal
condition — faithful and non-vacuous, but the *finite shadow* of the LI/asymptotic statement, never
the LI statement itself. This is the uniform honesty boundary, identical to `LeanDeference.lean`.

**Uniform NOT-checked across the corpus:** no LI machinery is formalized anywhere (all LI theorems
enter as named hypotheses/scalars); the soft⇒hard reduction; the cross-agent martingale (Hop 2); the
coupled non-deference direction; the pointwise→whole-policy bridge in general; the asymptotic
`≂ₙ`/`≳ₙ` layer (lives only in the confirmed `value_asymptotic`).

---

## 5. Suggested summer plan (bite-sized, formalizable, sequenced)

**Phase 0 — consolidate what is already proved (week 1).**
1. Fold the 11 checked finite cores + the audit verdict into a single "what LI deference buys, with
   honest boundaries" note. Apply the two cheap red-team Lean fixes: (a) restate
   `hard_endorsement_liar_unsat` as the value-vs-demand clash `condval=0` vs `condval=t` (all
   hypotheses paper-backed); (b) rename `merging-inductors`'s `bias_only_hurts` →
   `return_monotone_in_selector` to match what is proved.

**Phase 1 — the cheapest genuinely-new Lean targets (weeks 2–4).**
2. **Local Value (D10, Q1):** specialize `value_of_CM` to a fixed LUV sub-class `𝒳_Q`; near-trivial,
   settles a DDB open conjecture. *Lean-ready.*
3. **Soft⇒hard finite, no-spectral-gap (D8/Q3):** the one §5.2 step left as prose; elementary real
   analysis (a gap argument on finitely many values). Pairing with the existing
   `CM_implies_immodest` *completes* the finite-collapse impossibility in Lean. *Highest-value
   completion.*
4. **§10 external-expert restatement (Q2):** re-interpret `value_asymptotic` with `Ee/Eo` as an
   external expert; the statement is already expert-agnostic, so the work is purely fidelity prose +
   confirming no premise secretly requires expert=self. *Pure re-interpretation of confirmed Lean.*

**Phase 2 — the keystone reduction (weeks 4–8).**
5. **Pin D3** (the cross-agent LUV-Total-Trust definition) precisely, as a market-generability +
   cross-defect-→0 condition; this is the prerequisite for everything downstream.
6. **Eisenstat Hop 2 (D2):** prove the threshold-sentence reroute (`thm:wub` on
   `ψ^q_t="ℙ^H_{f(t)}(φ)>q"` + integrate over `q`), then resolve the Route-A (mutual feedback) vs
   Route-B (`H` trusts `A` only about `H`'s own future) dichotomy. *Resolving A-vs-B is the
   deliverable.* No Lean until the standpoint shift is settled (any earlier stub smuggles).

**Phase 3 — the safety-facing and updateless extensions (weeks 8–12, parallelizable).**
7. **Wirehead witness-support characterization (D5):** the red-team's "defect ≤0 iff `E_drug`
   overstates `θ` on the witness-firing support" — a small `Finset.sum_nonpos`-restricted Lean lemma
   matching the *real* claim, feeding D3.
8. **Derive `node_value` from `U` (D4):** define the update's local valuation as the genuine
   EDT-conditional of the *same* `U`, re-run the six examples so mugging/Newcomb non-deference becomes
   a *theorem about the EDT update*, not a hand-supplied input — the prerequisite for any honest
   updateless Total-Trust⇔Value biconditional.
9. **Calibrated-anticipation dial (D7):** Lean the same-ontology calibration/reflection facts; prove
   full-`Ā` calibration = S5/endorsement (atom-counting), establishing the modesty dial.

**Phase 4 — exploratory / higher-risk (if time):** D9 (finite Aumann-failure example, Lean-able),
D6's general Stag-Hunt closure / RO lift, D11's finite value-of-info ≥0 lemma (discharges Q6), D12
(finite non-transitivity, close to DDB 7.2.4).

---

## 6. Open problems and the most important unknowns

1. **THE central unknown (D3 / Q5): when is cross-agent LUV-Total-Trust earned between distinct
   inductors?** Free for the future self (`ccee`), *not free* otherwise. Every constructive thread
   (D2 merge, D5 legitimacy characterization, D6 LI lift, D10 value/factual asymmetry) routes through
   it. A *sufficient condition on good-feedback subsequences* is summer-sized; the full
   characterization is likely multi-summer.

2. **The Hop-2 standpoint shift (D2).** Does `A`'s good-feedback unbiasedness (an `A`-relative `≂`)
   survive substitution inside `H`'s `ℙ^H`-generable-weighted expectation? Route A (mutual feedback,
   clean/strong) vs Route B (narrow `H→A` trust about `H`'s own future, weaker but *relocates* rather
   than discharges). The threshold-sentence reroute is the first concrete move.

3. **The no-feedback wall is real and sharp.** Humans most need to trust AI on unobservables
   (flourishing, values, ethics); there the merge gives *nothing* for free. The "basin of
   corrigibility" bootstrap (a contraction `Φ` on `H`-models, idea 5) is the only proposal to
   *manufacture* feedback, but honestly it is a **stability/tiling theorem** ("if `A` starts
   aligned-enough, it stays aligned"), not bootstrapping-from-nothing — and the contraction metric may
   not exist on infinite/self-referential frames (no spectral gap), giving convergence-to-a-set, not
   a point.

4. **Asymptotic guarantees vs single-round safety.** All LI endorsement is a `≂_w` *average* and is
   **silent about any individual high-stakes round** (the "one big lie"). The gap between LI's
   asymptotic guarantees and real safety is **structural, not a detail**; a per-round bound likely
   needs a non-asymptotic refinement of LI the paper does not provide. Cautiousness/confidence-gated
   deference is the LI rendering of the AGENDA's interpretability addendum.

5. **The diagonal maximality (D8).** Is soft one-sided Self-Trust *the strongest* diagonal-surviving
   endorsement schema? Needs a partial order on threshold-conditional schemata; *incomparable*
   survivors (e.g. soft two-sided on a δ-band excluding the diagonal) may exist, so "strongest" is
   not yet well-posed.

6. **Updateless deference lacks a coupled-case characterization.** We have separable ⇒
   (UD)⇔endorsement and finite non-deference witnesses, but no clean "(UD) ⇔ [calibration of the
   anticipation kernel]" under coupling — and the red-team shows the current relation is a *thin
   wrapper around "is `π_u` a global argmax,"* blind to process, until `node_value` is tied to `U`.

7. **Mutual / recursive modeling (the "size problem," `lateral.md` §3.2).** Symmetric mutual hard
   trust is a 2×2 liar; finite mutual soft-CM forces both immodest ⇒ the agents *merge*. Whether two
   *distinct* inductors can mutually soft-trust without merging — on the same `δ_n→0` schedule — is
   open and is the Eisenstat question from the other side.

8. **R1-vs-R2 for self-belief (D6 red-team).** Whether "believe you're UDT1.1" is *cheap* (R1:
   believe-your-own-policy, principal's `δ·range` correct) or *adversarially exploitable* (R2:
   optimize a belief-contaminated objective, gap inflates to `δ/(1-δ)·range`) is itself
   trust-relevant content the lab should foreground as a dichotomy, not bury as a "correction."
