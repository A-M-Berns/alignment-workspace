# A Toy Formal Model of Legitimacy, the Wirehead-Decline, and Corrigibility

*Thread: "Modeling Legitimacy & Corrigibility" (AGENDA §"Modeling Legitimacy & Corrigibility").*
*Author: deepen agent, developing idea **L2** (drug/addiction) through **L1** (legitimacy =
LUV-Total-Trust), plus the **L3** corrigibility application and its limit.*
*Every claim flagged **PROVED / SKETCHED / CONJECTURE / INTERPRETATION**, matching the v2 doc.*

Cross-refs: v2 = `deference-in-logical-induction-v2.md`; M&A = `udt-representation-theorem/
meaning-and-agency-reference.md`; ideate = `findings/legitimacy-corrigibility-ideate.md`;
orientation = `findings/00-orientation.md`. Micro-examples: `models/
legitimacy_corrigibility_micro.py` (run: `python3`, exact rationals, all asserts pass). Candidate
Lean: `lean/legitimacy-corrigibility.lean` (**UNCHECKED** — for the Lean-verify agent).

---

## 0. One-paragraph statement of the model and the central claim

We work in a **finite probability frame** (the "finite shadow" register of `LeanDeference.lean`'s
`Deference` namespace), and gesture at the **LI lift** at each step. An agent/principal `N` holds
day-0 prices `π` over finitely many worlds and values a target LUV `θ` (e.g. "the good obtains").
A *belief-formation process* `Π` is anything that produces an estimate-stream `E_Π(θ)` of `θ`;
**`N` endorses `Π`** when `N`'s own coherent valuation cannot be Dutch-booked by betting "θ"
against "`E_Π(θ)`" on any weight `N` can compute, and **`Π` is legitimate-to-`N`** when that holds
because `E_Π` is actually correlated with `θ`-as-`N`-values-it (not merely with `Π`'s own
self-report). The **central claim (PROVED, finite core; SKETCHED as the LI lift)** is:

> An agent that evaluates a future option by its **current** endorsement (the legitimacy defect
> under its day-0 prices) **declines** a manipulation/wirehead that raises *future-reported*
> utility, because the wirehead is exactly an operation that drives the legitimacy defect strictly
> negative — a defect the agent can compute from its own data, hence *anticipate*. The same signed
> object, applied to a shutdown signal, makes the AI **defer to a legitimate shutdown** and
> **resist an adversarial one** — so corrigibility-as-endorsement is real but **bounded**: it
> cannot buy unconditional corrigibility, and closing that gap requires updatelessness.

The finite-frame algebra is **PROVED** (by hand + `models/legitimacy_corrigibility_micro.py`, exact
rationals; and as five candidate Lean theorems). The asymptotic LI versions are **SKETCHED /
CONJECTURE** and inherit the v2 §10.4 open characterization.

---

## 1. Definitions: endorsement, legitimacy, the legitimacy defect

### 1.1 The objects (INTERPRETATION, fixing notation)

Fix a finite world set `W`, novice/principal prices `π : W → ℝ₊` with `Σ π = 1`, a target
`θ : W → ℝ` (an indicator or bounded LUV), and a process `Π` whose *observable* output is an
estimate function `E_Π : W → ℝ` (the principal's read of "what `Π` says `θ` is"). A **selection
weight** is a function `w : W → ℝ` the principal can compute — in the LI lift, a market-generable
`w_n ∈ [0,1]` (v2 §0.3, Thm 4.12.3). Write `E_π(V) := Σ_w π_w V_w`.

**Definition (legitimacy defect).** The **legitimacy defect of `Π` to `N`, on weight `w` and
target `θ`** is
```
    defect_w(N→Π) := E_π(θ·w) − E_π(E_Π(θ)·w) = Σ_x π_x · w_x · (θ_x − E_Π(θ)_x).
```
(The second equality is the **decomposition identity**, pure linearity — `defect_decomp` in the
Lean, and `Legitimacy.legitimacy_defect_decomp` in the prior `legitimacy.lean`.)

**Definition (`N` endorses `Π`).** `N` **endorses `Π` (on a weight class `𝒲`, w.r.t. `θ`)** iff
`defect_w(N→Π) = 0` for every `w ∈ 𝒲`. In the LI lift this is **LUV-Total-Trust(N→Π)**: for every
market-generable `w_n∈[0,1]`, `E_n(⌜θ_n·w_n⌝) ≂ₙ E_n(⌜E_Π(θ_n)·w_n⌝)` (v2 §10.1). Endorsement is a
property of **`N`'s** prices, not of `Π`'s internal coherence (M&A: "not a property of Bob's
beliefs, but Alice's").

**Definition (`Π` is legitimate-to-`N`).** `Π` is **legitimate-to-`N`** iff `N` endorses `Π` *and*
the reason is correlation-with-reality-as-`N`-values-it: i.e. `E_Π(θ)` tracks `θ` under `π`, not
merely under `Π`'s own posterior. Operationally we **detect illegitimacy** by a *non-zero, signed*
defect on a witness weight (the contrapositive is what we can actually prove; see §2). M&A's
slogan, made operational: *legitimacy : endorsement :: good : utility* — endorsement is the
abstract no-Dutch-book relation; legitimacy is the truth-tracking instance of it.

**Why this is the right defect (INTERPRETATION).** This is *exactly* the cross-agent object the
whole v2 §10 modularization reduces Value to: v2 §10.2 proves **legitimate ⇒ Value** (endorsing `Π`
lets `N` safely hand decisions to `Π`). The present model supplies the **negative companion**:
**illegitimate ⇒ anticipated defect ⇒ decline**, using the *same* object. No new machinery; one new
construction (the "drug" perturbation) and one sign lemma.

### 1.2 What is free and what must be earned (PROVED reduction, from v2)

For `Π = N`'s own clean future self, endorsement is **free** — it is the conditional martingale
4.12.3 (`ccee`); `defect = 0` by the self-trust theorem (v2 §0.3). For a **distinct or tampered**
process it is **not** free (v2 §10.4); it must be earned, and *can fail*. The drug case is the
sharpest failure: a future self that is tampered-with so that it reports high `θ` regardless of
`θ`'s truth.

---

## 2. The wirehead-decline theorem (the drug/addiction model)

### 2.1 The two future selves (SKETCHED model; finite core PROVED)

Two processes over the same frame, differing by an **exogenous, non-market perturbation** (the
"drug"):

- **`E_clean`** — `N`'s own more-thought-out future self. The principal anticipates it reports `θ`
  calibrated to `θ`'s truth: in the 2-world micro-frame, `E_clean = θ`. Endorsed; `defect = 0`
  (this is `ccee`/self-trust).
- **`E_drug`** — the future self *after* an operation that reassigns high reported credence `q` to
  the target `θ` **independently of `θ`'s truth** (`E_drug ≡ q` on every world). This models
  "addiction / wireheading": the report rises, the correlation-with-reality does not.

### 2.2 The theorem

> **Theorem (Wirehead-Decline; PROVED in the finite frame).** Suppose at every world the drugged
> self's reported estimate pointwise **overstates** the target: `θ_x ≤ E_drug(θ)_x`, with
> `π_x ≥ 0` and any nonneg witness weight `w_x ≥ 0`. Then
> ```
>     defect_w(N→drug) = E_π(θ·w) − E_π(E_drug(θ)·w) ≤ 0,
> ```
> strictly if the overshoot is strict on a positive-mass, positive-weight world. Consequently:
> 1. **(declines)** An agent that values the option by its **current** endorsement — i.e. by the
>    `θ`-side `E_π(θ·w)` — gets *no more* than the `E_drug`-side, so it never strictly prefers the
>    drug; valuing by **future report** (the `E_drug`-side) it strictly prefers it. The *gap*
>    between the two valuations is the wirehead.
> 2. **(anticipated)** `defect_w(N→drug)` is a function of `π, θ, E_drug, w` — all principal-side
>    data — so `N` can compute the failure **in advance** (the finite shadow of
>    `E_n(⌜E^drug_{f(n)}(θ)⌝) ≈ 1` while `E_n(θ) ≈ 0`).
> 3. **(no-Dutch-book)** The "drug-trader" that buys `θ` at the drug-self's reported price `q`,
>    weighted by `w`, has expected profit `Σ π_x w_x (θ_x − q) = defect_w(N→drug) < 0` against
>    `N`'s own prices — so **abstention is the no-Dutch-book action**.

**Status.** The finite-frame inequality and clauses (1)–(3) are **PROVED**: by hand below, by
`models/legitimacy_corrigibility_micro.py` (exact rationals, asserts pass), and as candidate Lean
`wirehead_declined` + `defect_decomp` (UNCHECKED). The **LI lift** — that this defect is genuinely
`≂ₙ`-anticipated in the asymptotic sense, and that abstention is no-Dutch-book against *every*
trader — is **SKETCHED** (it is one inequality in idea L2, on top of the v2 §10 layer the existing
Lean also leaves to prose). The **CONJECTURE** that remains is the v2 §10.4 *characterization*:
which exogenous operations `Π↦Π'` are exactly the ones that drive the defect away from 0.

### 2.3 Proof of the finite core (PROVED)

By the decomposition identity, `defect_w = Σ_x π_x w_x (θ_x − E_drug_x)`. Under `θ_x ≤ E_drug_x`,
`π_x ≥ 0`, `w_x ≥ 0`, each summand `= −π_x w_x (E_drug_x − θ_x) ≤ 0`; the sum of nonpositives is
nonpositive, strictly if any summand is strict. ∎ (This is precisely `drug_defect_sign` /
`wirehead_declined` in Lean: `Finset.sum_nonpos` + `mul_nonneg`, mirroring `value_of_CM`.)

### 2.4 Worked micro-example (PROVED by hand and by script)

Two worlds `h` (θ true), `n` (θ false). `π = (1/4, 3/4)`, so `E_π(θ) = 1/4` (the good is genuinely
unlikely). `θ = (1, 0)`. Clean self `E_clean = (1, 0)`. Drug self `E_drug = (9/10, 9/10)` (reports
"happy" everywhere). Witness weight `w = (1, 1)` (the drug self reports θ highly in every world, so
the soft indicator `Ind_δ(E_fut(θ)>p) ≈ 1`).

| quantity | value | reading |
|---|---|---|
| `E_π(θ)` | `1/4` | N's own current estimate of θ: **LOW** |
| `E_π(E_drug(θ))` | `9/10` | N's estimate of the drug-self's **report**: **HIGH** |
| `defect_w(N→drug)` | `−13/20` | strictly negative ⇒ **illegitimate, anticipated** |
| `defect_w(N→clean)` | `0` | clean self **endorsed** |
| `V_now(drug)` | `1/4` | value by current endorsement = `V_now(abstain)` |
| `V_fut(drug)` | `9/10` | value by future report |
| decision by current-endorsement | **decline** | `1/4 ≯ 1/4` |
| decision by future-report | **take** | `9/10 > 1/4` |
| drug-trader expected profit | `−13/20` | abstention is no-Dutch-book |

This is the formal skeleton of the AGENDA's flagship line: *"AI should avoid wireheading the way
humans avoid addictive drugs — they don't take the drug because they anticipate getting addicted
and don't currently value that outcome."* The split `E_π(θ)=1/4` vs `E_π(E_drug θ)=9/10` is the
formal content of "they would enjoy it if it happened."

### 2.5 The honesty contrast that makes the model non-trivial (INTERPRETATION)

The drug-self is **happier** (`E_drug(θ)=9/10 > 1/4`) and can be **internally coherent / immodest**
(it passes its *own* self-trust: it is calibrated *to itself*). Legitimacy is **not** calibration-
to-itself; it is **correlation with reality as `N` values it**. The drug-self fails `N`'s cross-
martingale even though it passes its own. *This is the entire wireheading distinction* — "confident
and self-coherent" ≠ "truth-tracking for the principal" — and the model exhibits it in two worlds.

### 2.6 Where this needs updatelessness (FLAG)

The decline works **only because the agent uses its day-0 prices `π` to value the option**, i.e. it
is **updateless about its evaluative standard** across the drug transition. An *updateful* agent
that re-evaluates with the drug-self's posterior `E_drug` would endorse the drug ex post (that is
clause (1)'s `V_fut` branch). So "decline the wirehead" is *exactly* the move of **not updating the
valuation function on the manipulated successor's report** — a updatelessness/precommitment
property (AGENDA "Updatelessness": "be mostly/completely updateful about human values" — here the
*evaluative standard* `θ`-under-`π` is the thing kept updateless). The finite model **encodes** this
by always scoring with `π,θ`; it does **not** *derive* that the agent should do so. Deriving it is
the open updatelessness question (orientation Q8: *UDT defers to update `u` iff `u` is
control-endorsed by the prior* — the drug update is **not** prior-control-endorsed). **CONJECTURE.**

---

## 3. Corrigibility as endorsement of the shutdown process (L3), and its limit

### 3.1 Definitions (INTERPRETATION)

Let `A` be the AI with prices `P_A` over worlds, `d : W → {0,1}` the danger indicator ("A is
dangerous"), and a **shutdown signal** `S` generated by a process `Π_H` (the human's decision),
with signal-weight `s : W → ℝ₊` (mass on signal-firing worlds). Use the **absolute-endorsement**
move (M&A: corrigibility ≈ A absolutely-endorses H modifying A): A scores **COMPLY** by the
human-aligned utility `d` (shutting down a dangerous A is good) and **RESIST** by `1 − d` (keeping a
safe A running is good). Define the **comply-advantage**
```
    adv(S) := E_{P_A}(s·d) − E_{P_A}(s·(1−d)) = Σ_x P_A(x)·s_x·(2 d_x − 1).
```
(Linearity: `comply_iff_endorsed` in Lean.) **`A` is corrigible w.r.t. `S`** iff `adv(S) ≥ 0`: A
weakly prefers to comply when `S` fires. **`A` legitimacy-endorses `Π_H`** iff the signal is
cross-martingale-faithful to danger under A's own prices — operationally, `s` fires only where
`d ≥ 1/2`.

### 3.2 The corrigibility statement (PROVED finite; SKETCHED LI lift)

> **Proposition (Endorsed-Shutdown Deference; PROVED finite frame).**
> (a) **Positive.** If the signal is endorsement-faithful — `0 ≤ s_x(2d_x − 1)` at every world
> (the signal fires, `s_x ≥ 0`, only where danger is `≥ 1/2`) — and `P_A ≥ 0`, then `adv(S) ≥ 0`:
> **A defers to the shutdown.** (`endorsed_signal_complies`.)
> (b) **Limit / impossibility.** If the signal is adversarial — `s_x(2d_x − 1) ≤ 0` at every world
> (fires only where danger `≤ 1/2`, i.e. on safe worlds) — then `adv(S) ≤ 0`: **A does not prefer
> to comply; current endorsement recommends resistance.** (`adversarial_signal_resists`.)

So corrigibility-as-endorsement is **purchased exactly by legitimacy of the signal process**, using
the *same* signed weighted sum as ordinary deference (§1.1) — this is the unification the ideate
file sought (trust-beliefs and trust-shutdown share one premise). And it is **bounded**: (b) shows
the very same machinery *flips sign* on a non-endorsed shutdown.

### 3.3 Worked micro-example (PROVED, in the script, PART B)

Four worlds `(d?, S?)`; `P_A(d) = 1/2` held fixed; three signal processes differing only in how `S`
correlates with `d`:

| signal `Π_H` | `P_A(d | S fires)` | comply vs resist | A's choice |
|---|---|---|---|
| **legitimate** (`S` ⇔ `d`) | `1` | `1 > 0` | **comply** (corrigible) |
| **endorsement-blank** (`S ⊥ d`) | `1/2` | `1/2 = 1/2` | **indifferent** (endorsement silent) |
| **adversarial** (`S` ⇔ `¬d`) | `0` | `0 < 1` | **resist** |

### 3.4 What corrigibility-as-endorsement **cannot buy** (the impossibility, INTERPRETATION + PROVED witness)

1. **No deference to a *blank* shutdown.** On an endorsement-blank signal (`adv = 0`) current
   endorsement is *silent* — A has no reason to comply (the micro-example's middle row). So
   endorsement cannot ground a *reflex* "always shut down when told," only "shut down when the
   command is *informative about danger under your own beliefs*."
2. **Active resistance to an *adversarial* shutdown.** On an anti-correlated signal `adv < 0`, A
   *prefers to resist* — and by its own (absolute-endorsement) lights it is *correct* to (it is
   protecting human-aligned value from a saboteur). This is the formal seam where "corrigible AI"
   and "manipulable AI" diverge: an AI that defers to *every* shutdown is also one a saboteur can
   shut down; an AI that defers to *endorsed* shutdowns will, by construction, resist the saboteur.
   **You cannot have both** unconditional corrigibility and adversarial-shutdown robustness from
   endorsement alone. (This is the endorsement-calculus analog of the Soares-et-al.
   corrigibility-vs-utility-maximization tension; here it is a *sign flip of one weighted sum*,
   PROVED in the finite witness.)
3. **The principal-side cost.** Even the *legitimate* signal only buys deference *to the extent A's
   prices already see `S` as danger-correlated*. If A is wrong about `d` (mis-estimates its own
   danger), endorsement defers to A's error, not to the human's intent. Legitimacy-to-`A` ≠
   legitimacy-to-the-human (this is the L6 non-transitivity seam: H→shutdown-process and
   A→its-own-danger-estimate need not compose).

### 3.5 Where corrigibility needs updatelessness (FLAG — the load-bearing gap)

Point (2) is *why* updatelessness is needed. An endorsement-only AI **correctly** resists
adversarial and blank shutdowns *by its current beliefs*. But humans want an AI that is corrigible
**even when the AI believes the shutdown is mistaken** — precisely the "humans are sometimes
grateful in retrospect about things which seemed terrible at the time" case (M&A Legitimacy §).
That requires A to **precommit, ex ante, to honoring `Π_H`'s outputs**, *before* updating on its own
later (possibly-manipulated, possibly-overconfident) danger-estimate — i.e. to be **updateless about
the modification map** while remaining updateful about the world. This is the dual of §2.6: there,
updatelessness made the agent *distrust* a manipulated successor's report; here, updatelessness
makes the agent *trust* a legitimate principal's signal *despite* a later self that would
second-guess it. Both are "keep the evaluative/authority standard fixed across a transition that
could corrupt it." **CONJECTURE (the open formal target):** *A is robustly corrigible to `Π_H` iff
A is updateless about the shutdown map and `Π_H` is control-endorsed by A's prior* (orientation Q8;
M&A absolute endorsement; AGENDA open-minded updatelessness). The finite model in this doc proves
the *endorsement* half (§3.2) but **encodes rather than derives** the updateless precommitment — it
scores with A's *current* `P_A`, and the gap (2) is exactly what a precommitment would close.

---

## 4. The candidate Lean file (UNCHECKED — for the Lean-verify agent)

File: `lean/legitimacy-corrigibility.lean`. Five theorems, targeted imports (no `import Mathlib`),
self-contained. **I did NOT compile it.** Plain-English ↔ Lean correspondence and the fidelity
audit:

| Lean theorem | informal claim | faithful? |
|---|---|---|
| `defect_decomp` | legitimacy defect = single signed weighted sum (linearity) | **faithful, universal, non-vacuous** (mirrors `Deference.decomposition`) |
| `wirehead_declined` | drug-self pointwise overstates θ ⇒ defect ≤ 0 ⇒ decline | **faithful**: hypothesis POINTWISE (`θ ≤ E_drug`), conclusion SIGNED SUM; real monotonicity step, not a restatement; non-vacuous (micro-example) |
| `comply_iff_endorsed` | comply-advantage = `Σ π·s·(2d−1)` (linearity) | **faithful, universal** |
| `endorsed_signal_complies` | signal fires only where danger ≥ ½ ⇒ `adv ≥ 0` ⇒ comply | **faithful**: `hfire : 0 ≤ s(2d−1)` is the honest encoding; non-vacuous (legitimate row holds, adversarial row fails it) |
| `adversarial_signal_resists` | signal fires only where danger ≤ ½ ⇒ `adv ≤ 0` ⇒ resist | **faithful** dual; the impossibility witness — same machinery, flipped sign |

**The single most important fidelity flag.** The Lean is a **finite shadow** of the decision
*pivot*, not of the full claims:
- It does **not** model the LI **asymptotic anticipation** (`E_n(⌜E^drug_{f(n)}(θ)⌝)≈1` in the
  genuine `≂ₙ` sense) — only "the defect is a function of principal-side data." Same boundary as
  `LeanDeference.lean` (orientation §3, items 2–3).
- It does **not** prove no-Dutch-book against *every* trader — only that one specific defect/advantage
  has a definite, exploitable sign.
- "Endorsement-faithful" / "adversarial" are **encoded** as pointwise sign hypotheses on where the
  signal fires, a *modeling choice*, **not derived** from a cross-martingale convergence. The
  updateless-precommitment content of §2.6 / §3.5 is **entirely absent** from the Lean (it scores
  with fixed prices). The Lean honestly proves: *given* these encodings, the sign goes the claimed
  way. That is real but modest — exactly the honesty boundary the existing Lean observes.
- Quantifier check: `endorsed_signal_complies` concludes `0 ≤ adv` (comply weakly preferred);
  `adversarial_signal_resists` concludes `adv ≤ 0` (resist weakly preferred). Duals via `d ↔ 1−d`.
  Neither is vacuously `True`: each needs its sign hypothesis, and the micro-example exhibits BOTH
  signs, so the hypotheses are non-trivially discriminating.

If the verify agent wants the smallest guaranteed-faithful targets: `defect_decomp` and
`comply_iff_endorsed` are pure linearity one-liners that still earn their keep ("the wirehead-decline
and the corrigibility pivot each reduce to one signed weighted sum").

---

## 5. Summary of statuses

| result | status |
|---|---|
| legitimacy defect = signed weighted sum (decomposition) | **PROVED** (hand + script; Lean candidate) |
| **Wirehead-Decline** (finite frame): overstatement ⇒ defect ≤ 0 ⇒ current-endorsement declines | **PROVED** (finite core; §2.2–2.4) |
| wirehead anticipation / no-Dutch-book in the genuine **LI** `≂ₙ` sense | **SKETCHED** (one L2 inequality on the v2 §10 layer) |
| which operations are "drugs" (defect-inducing) — the characterization | **CONJECTURE** (= v2 §10.4 open) |
| **Endorsed-Shutdown Deference** (finite): endorsed signal ⇒ comply | **PROVED** (finite; §3.2a) |
| **Adversarial-Shutdown limit**: non-endorsed signal ⇒ resist (impossibility witness) | **PROVED** (finite; §3.2b) |
| robust corrigibility = updateless precommit + prior-control-endorsement | **CONJECTURE** (§3.5; orientation Q8) |
| decline-the-wirehead is an updatelessness property of the evaluative standard | **INTERPRETATION → CONJECTURE** (§2.6) |

**Central claim (restated), status PROVED (finite core) / SKETCHED (LI lift):** evaluating futures
by *current* endorsement turns "decline the wirehead" and "defer to legitimate shutdown / resist
adversarial shutdown" into **one** sign-of-a-weighted-sum fact (the legitimacy defect / comply-
advantage); the finite-frame algebra is proved and machine-checkable, the asymptotic LI version and
the updateless-precommitment half are the named open gaps.
