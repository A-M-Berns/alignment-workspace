# The Pointwise Tower and Faithful Acceleration: a Negative and a Positive Result, and How They Fit

*An explainer synthesizing the two newest results in the human–AI deference project: the negative result of [`no-timely-pointwise-tower.md`](anson-notes/no-timely-pointwise-tower.md) and the positive result of [`faithful-acceleration.md`](faithful-acceleration.md). It assumes the general theory of [`deference-in-logical-induction-v5.md`](deference-in-logical-induction-v5.md) and the motivation of Demski's [`li-deference.md`](li-deference.md), and exists to make one thing vivid: the two results are about the **same object**, demand **two different faces** of trust from it, and meet **exactly at the ceiling** the general theory predicted. Notes by Claude (Opus 4.8), in conversation with Abram Demski; building on Anson Berns's project.*

---

## 0. The one-paragraph version

Set a strong inductor $A$ (the AI) to forecast a weaker inductor $H$'s (the human's) **own future credences**, and ask when $H$ is *forced* to trust $A$. Trust has two faces. The **pointwise-equality** face — the tower, "my credence today already equals my estimate of $A$'s quote, question by question" — is **impossible** (the negative result): it reduces to $A$ exactly *tracking* $H$'s future credence per question, and that tracking dies twice over. The **averaged-inequality** face — bounded $\varepsilon$-violation Total Trust, "averaged over the questions where $A$ says *high*, my credence really is high, so I may let $A$ decide" — is **forced** (the positive result), over *all* sentences and with no appeal to the prior. These are not rival claims about one threshold; they are the two sides of a single line. The negative result closes the door above the line and says explicitly that any survivor must be an averaged notion; the positive result walks through exactly that door. In one sentence: **you cannot force the AI to be an exact early oracle for the human's verdict on each question, but you can force it to be a faithful statistical accelerator of the human's verdicts across questions — and the second is the most a modest expert can ever give.**

---

## 1. The shared setup (the same object, twice)

Both results live in the identical world; only the demand differs.

- Two logical inductors over a shared language, with trader classes $\mathcal{C}_H \subseteq \mathcal{C}_A$ (canonically $\mathrm{P} \subseteq \mathrm{EXP}$): the **human** $H \dashv \mathcal{C}_H$ and the stronger **AI** $A \dashv \mathcal{C}_A$.
- **Mutual observability.** Each reads the other's recent outputs through a bounded computable delay: $A$ records $H$'s realized prices (so $A$ gets *feedback*), and $H$ records $A$'s quotes (so $a_n$ is a $\mathcal{C}_H$-readable, already-decided feature of $H$'s world).
- **What $A$ forecasts.** Fix a lookahead $f(n) > n$ (the negative note writes it $F(n)$; same role — canonically $2^n$). The object $A$ quotes is its day-$n$ estimate of where $H$'s *own* deliberation is heading:
  $$\boxed{\;a_n \;:=\; E^A_n\big(\ulcorner Y_n \urcorner\big), \qquad Y_n \;:=\; E^H_{f(n)}(X)\;}$$
  — $A$'s prediction, formed at *its* day $n$, of the credence $H$ will hold about $X$ after $f(n)$ stages of thought. Here $H$ is the **unfrozen / coupled** human: it has read $A$'s past outputs, so $Y_n$ already depends on $A$'s run. (The negative note writes $Y_n = H^+_{F(n)}(P^{(n)})$ for exactly this.)

This single quote $a_n$ is the object of *both* documents. The asymptotics: $x_n \approx_n y_n$ means $x_n - y_n \to 0$ (pointwise, per index); $x_n \gtrsim_n y_n$ means $\liminf(x_n - y_n) \ge 0$.

**The faces of deference** (v5 §1). For an observable, coherent expert estimate $E^\ast$ that $H$ can read — here $E^\ast(X) = a_n$:

| face | statement | character |
|---|---|---|
| **Tower** / `Mart`$(H\to A)$ | $E^H_n(X) \approx_n E^H_n(\ulcorner a_n \urcorner)$, every $X$ | pointwise **equality** |
| **Total Trust** | $E^H_n(X \mid a_n > t) \gtrsim_n t$ | **inequality**, soft-conditioned |
| **Value** | for every menu, $H$ would (weakly) rather let $A$ pick | instrumental |

The two results split precisely along the **equality vs. inequality** column — and, orthogonally, along **per-index vs. averaged**. The negative result is about the pointwise equality; the positive result is about the averaged inequality. Everything below is bookkeeping on that split.

A fact from the general theory we lean on without re-deriving (v5 §1.2, kernel-checked `value_iff_totalTrust`): for any **observable**, **coherent** expert, $\textbf{Total Trust} \Longleftrightarrow \textbf{Value}$, forced by a two-option witness menu, using **no tower**. So forcing (averaged) Total Trust suffices to force (averaged) Value — this is how the positive result reaches an *instrumental* conclusion without the tower it has just been denied.

---

## 2. The negative result: the timely pointwise tower is impossible

**Claim.** `Mart`$(H \to A)$ — the timely, pointwise, *equality* tower — cannot be achieved in this setup, on **any** contract family.

### 2.1 The tower reduces to tracking

The tower is not a softer object that might survive where exact prediction fails; it is *equivalent* to exact prediction, via two collapses that each remove one corner-quote (negative note §2):

- **Read-off.** $a_n$ is published and decided in $H$'s ledger by stage $n{+}1$, so $E^H_n(\ulcorner a_n \urcorner) \approx_n a_n$. *$H$'s estimate of $A$'s quote just is $A$'s quote — $H$ reads it.* (Pure observability.)
- **Self-trust (`cee`).** $Y_n$ is $H$'s *own* future credence, so $E^H_n(X) \approx_n E^H_n(\ulcorner Y_n \urcorner)$ is the free Expected-Future-Expectations theorem.

Substituting both into the tower instance collapses it to
$$
\textbf{(Tower)} \;\Longleftrightarrow\; a_n \approx_n \mathbb{P}^H_n(X) \;\;\xrightarrow[\text{on the diagonal}]{}\;\; a_n \approx_n Y_n,
$$
i.e. the tower forces $A$'s quote to equal $H$'s *present* credence, equivalently (where present, future, and realized values coincide) to **timely pointwise tracking** $a_n \approx_n Y_n$. The tower inherits whatever kills tracking. Two obstructions do, and they partition all families.

### 2.2 — 2a — the anti-inductive (Gödel-coin) diagonal

*Scope: families that **may reference $A$'s quotes**.* Take the diagonal subfamily
$$
g_n \;\leftrightarrow\; \big(a_n \le \tfrac12\big).
$$
$A$ publishes $a_n$; $H$ records it; so $g_n$ is a **decided** sentence. Convergence on decided sentences gives $E^H_n(g_n) \approx_n \mathbb{1}[a_n \le \tfrac12]$ and $E^H_n(\ulcorner a_n\urcorner) \approx_n a_n$, so the tower would force
$$
\mathbb{1}[a_n \le \tfrac12] \;\approx_n\; a_n, \qquad\text{but}\qquad \big|\mathbb{1}[a \le \tfrac12] - a\big| \;\ge\; \tfrac12 \ \ \forall a.
$$
A **constant $\ge \tfrac12$ defect**. The contract is a fixed point that *inverts* $A$'s own quote — a coin whose face is defined to contradict the predictor's bet on it. The continuity that tames ordinary self-reference at the *price* level (a market clears a liar at $\tfrac12$) is gone at the *settlement* level, where the payout is a discontinuous $0/1$ function of the quote. **Power-insensitive**: an oracle for $A$ does not help, because the obstruction is to *consistency*, not computation.

### 2.3 — 2b — the cost-circularity regress

*Scope: **quote-free** families,* where the diagonal cannot be *written*. Here tracking is not *false* but **underivable**. To price $Y_n$ at stage $n$, a $\mathcal{C}_A$-trader must simulate the coupled $(H,A)$ system forward to stage $f(n)$ — but that system *includes $A$'s own future quotes*, so the simulation must run $A$ forward past itself:
$$
R_A(n) \;\gtrsim\; R_A\big(f(n)\big) \;>\; R_A(n),
$$
an unsatisfiable power assumption ($\mathcal{C}_A$ would have to sit strictly above its own trader class). No admissible trader *forces* the tower. This is the more delicate half — an underivability, not a refutation — and should be treated as the less airtight of the two.

### 2.4 The two cases are exhaustive

A family either may reference the quotes (→ 2a, tower **false**, defect $\ge \tfrac12$) or may not (→ 2b, tower **underivable**). No third kind exists, so **no construction yields the timely pointwise tower.** What the negative result explicitly leaves standing (its §6): *limit agreement* and *averaged / gated / statistical* inequality notions. Its closing line is a signpost to the positive result — "any positive construction that keeps this setup must aim at one of those weaker, non-pointwise notions."

---

## 3. The positive result: faithful acceleration (bounded $\varepsilon$-violation Total Trust → Value)

**Claim.** In the *same* setup, $H$ is forced into **bounded $\varepsilon$-violation Total Trust** in $A$, hence **classwise Value** — over its **admissible domain** (all sentences but the quote-referencing 2a family; §4.1), with **no appeal to the prior**.

### 3.1 The one idea: defer to credences, not truth

> **Defer to the human's *credences*, not to the world's *truth*.**

Every obstruction above is an artifact of forcing $A$ to track *truth* (a hard $0/1$ object that may be undecidable, may react to the quote, and may demand forward simulation). They evaporate when $A$ instead tracks *where $H$'s own deliberation is heading*, because a human credence is (i) **always present** — one for every sentence, decidable or not; (ii) **continuous** — it lives at the price level, where LI's self-reference paradoxes are benign; and (iii) **self-trusted** — an inductor already trusts its own future. Those are exactly the three properties the truth-level target lacks.

### 3.2 The two forced ingredients

- **(I) Self-trust** (`cee`): $E^H_n(X) \approx_n E^H_n(\ulcorner E^H_{f(n)}(X) \urcorner)$. *$H$ already trusts where its own deliberation is heading.*
- **(II) Calibration** — exactly the LI theorem **Expectation Unbiasedness From Feedback** applied to the feedback LUV $\ulcorner E^H_{f(n)}(X)\urcorner$. Since $H$ is a fixed computable process (even reading $A$, the coupled recursion is deterministic), $E^H_{f(n)}(X)$ is a definite $\Gamma$-provable number whose realized value enters $A$'s world *by observation* at $\sim f(n)$. The theorem gives, for any $\mathcal{C}_A$-generable divergent patient weighting $w_n$,
  $$\frac{\sum_{n\le N} w_n\big(E^H_{f(n)}(X) - a_n\big)}{\sum_{n\le N} w_n}\ \xrightarrow[\;N\to\infty\;]{}\ 0.$$

Two features of (II) are decisive, and each is a direct retreat from one wall of §2:

- **Checked after the fact, not by forward simulation.** $A$'s calibration is enforced by a trader that *waits* for $E^H_{f(n)}(X)$ to be revealed and then banks on any systematic bias — it never computes $H$'s future in advance. **No power assumption; the 2b cost-circularity never arises.**
- **The feedback is a human credence, which (almost) always exists.** $E^H_{f(n)}(X)$ is realized for *every* $X$, decidable or not — so there is no decidable/timely fragment to restrict to, **no inductive generalization, no dependence on the prior.** (Existence is necessary but not sufficient: where the credence-target hard-settles as an anti-inductive function of $a_n$, calibration *fails* — the 2a diagonal sits *outside* the admissible domain, §4.1. On that domain (II) holds.)

### 3.3 The trade

Suppose bounded $\varepsilon$-violation Total Trust fails: on a class of infinite weight, $A$ forecasts high ($a_n > t$) while $H$'s own price sits low ($E^H_n(X) < t - \varepsilon$). Form the **doubly-soft, legal** weight
$$w_n(X,t,\varepsilon,\delta) \;=\; \mathrm{Ind}_\delta(a_n > t)\cdot \mathrm{Ind}_\delta\big(E^H_n(X) < t - \varepsilon\big)$$
— continuous in the observable $a_n$ and in $H$'s own price ($\mathrm{Ind}_\delta$ the one-sided soft ramp of faithful §2: $0$ below the threshold, rising linearly to $1$ over width $\delta$). A $\mathcal{C}_H$-trader holds $w_n$ units of $X$ from day $n$ to day $f(n)$ and unwinds. Writing $W_N := \sum_{n\le N} w_n$ (with $W_N\to\infty$, the supposed infinite weight) and $B_N := \sum_{n\le N} w_n\big(E^H_{f(n)}(X)-a_n\big)$, marked to market it banks through day $N$
$$
\sum_{n\le N} w_n\big(E^H_{f(n)}(X) - E^H_n(X)\big)\ >\ B_N + \underbrace{\sum_{n\le N} w_n(a_n - t)}_{\ge\,0} + \varepsilon\,W_N\ \ge\ \Big(\varepsilon + \tfrac{B_N}{W_N}\Big)W_N .
$$
Ingredient (II) is exactly $B_N/W_N\to0$, so the factor $\varepsilon + B_N/W_N\to\varepsilon>0$ while $W_N\to\infty$: the bank diverges, with bounded risk — an exploit, which $H$ does not admit. So the violation class has bounded weight: **bounded $\varepsilon$-violation Total Trust holds, and classwise Value follows** (via the §1 witness equivalence, summed over the class). *(The §5 trader core of the positive note is kernel-checked, `sorry`-free, in `FaithfulAcceleration.lean`.)*

The engine is the **self-trust round-trip** — buy $X$ now, sell at $H$'s own future price — *steered by $A$'s forecast*: ingredient (II) guarantees that on exactly the days $A$ flags, $H$'s future credence really is high *on average*; ingredient (I) makes "sell at $H$'s future price" a legitimate cash-out.

### 3.4 Stated honestly

This is the **gated / averaged** form, and *only* that. The per-day pointwise statement $E^H_n(X \mid a_n > t) \gtrsim_n t$ is **not** forced — it would need the per-day tower, which §2 has just denied. A day-averaged input (calibration) buys exactly a day-averaged conclusion. The proof never uses pointwise tracking $a_n \approx E^H_{f(n)}(X)$ — *which it could not, since that is the very thing the negative result kills.* This honesty is the hinge of the fit.

---

## 4. How they fit: two faces of one line, meeting at the ceiling

### 4.1 Same quote, two demands — where they can and cannot coexist

Both documents constrain the *same* $a_n$. The negative result asks for the **pointwise equality** $a_n \approx_n Y_n$ and proves it impossible; the positive asks for the **averaged inequality** (the gated weighted average $\sum_{n\le N} w_n(Y_n - a_n)\big/\sum_{n\le N} w_n \to 0$) and proves it forced. These are logically distinct notions — a sequence *can* be persistently wrong per index yet unbiased in the aggregate (alternate the gap $\pm\tfrac12$: pointwise defect $\tfrac12$, signed average $\to 0$; this is `two_faces_distinct` in `TowerAndAcceleration.lean`). But that witness must **decouple** the forecast from the realized value — and the decoupling is the dividing line, because on the *coupled* anti-inductive diagonal the two faces do **not** coexist. They die together.

> **The quote-referencing diagonal kills *both* faces.** Take $g_n \leftrightarrow (a_n \le \tfrac12)$. Under mutual observability — which *both* results assume — $H$ reads $a_n$, so $g_n$ becomes a **decided** sentence and $Y_n = E^H_{f(n)}(g_n) \to \mathbb{1}[a_n \le \tfrac12]$, hard.
> - **The tower dies** (negative): no quote is within $\tfrac12$ of $\mathbb{1}[a_n\le\tfrac12]$ (2a).
> - **Averaged Total Trust dies too** — the positive does *not* rescue it here. The same `no_exact_quote` bound forces a gate-visible miscalibration: whatever $A$ quotes, the gate $\mathrm{Ind}_\delta(a_n>\tfrac12)$ (or, if $A$ stays low, the uniform weight) carries a persistent $\ge\tfrac12$ bias between $a_n$ and the realized $\mathbb{1}[a_n\le\tfrac12]$. Expectation Unbiasedness From Feedback **cannot apply** — its conclusion would be violated. Calibration breaks exactly where tracking does.

So the positive does not survive *on* the diagonal; it **avoids** it. Its benign-self-reference escape is for the **price-level** liar $\chi \leftrightarrow (\mathbb{P}^H(\chi) < \tfrac12)$ — a credence about $H$'s *own price*, which clears at a continuous $\tfrac12$ and never decides — **not** the quote-referencing $g_n$, which hard-decides. Different sentences; the positive lives on the first, is silent on the second.

The fit is therefore tighter than "two faces of one family." Both results carve the **same boundary** — quote-referencing / hard-settling vs. not:
- on the **quote-referencing (2a) family**, both faces die — the negative's territory, where the positive has nothing;
- on the **continuous-credence (quote-free) domain**, the gradation is real: the pointwise tower is unforced (2b: underivable), while averaged Value *is* forced, and where the tower genuinely fails it fails in the decoupled way the witness above captures.

The "wrong-per-index, unbiased-in-aggregate" coexistence is genuine — but it lives in that second domain, never on the diagonal. This is why **obligation 3 (no hidden hard settlement) is not bookkeeping**: it is the exact statement that the construction stays inside the positive's admissible domain — the complement of the 2a family (§6).

### 4.2 The ceiling was predicted

v5's **T5** already named the boundary: pointwise object-level deference is *false* (it contains the anti-inductive contracts), and "the gated and averaged forms are the most one can ask of deference to a **modest** expert — a theorem about the problem, not a defect of the proof." The two new results are the two sides of T5 made sharp:

- the **negative result** proves the wall *above* the ceiling — the pointwise tower is unreachable;
- the **positive result** proves the ceiling is *reached* — the averaged form is forced, and forced maximally (over the whole admissible domain, no prior).

Together they pin the achievable notion of cross-process trust in this setup to a point: **exactly averaged Total Trust → Value, no more and no less.**

### 4.3 Two walls, two moves

The positive result is built to walk around precisely the obstructions the negative result erects. Each move neutralizes one wall:

| obstruction (truth-level) | what it kills | the move that dodges it |
|---|---|---|
| **2a** anti-inductive settlement | exact match to a hard $0/1$ that reacts to the quote | **stay in the continuous-credence domain** — price-level self-reference only; never build a settlement that hard-decides against $a_n$ (§4.1) |
| **2b** cost-circularity | timely tracking requiring $A$ to simulate its own future | **calibrate after the fact** (wait → observe → bank); no forward simulation, no power assumption |
| *No-Forced-Trust on undecidables* (v5 §4.1) | truth-agreement past the decidable fragment | credences are **always present** → reach every *admissible* sentence, no prior |

The three obstructions are one cause — forcing $A$ to track *truth* — and the single countermove (target the human's continuous, always-present, self-trusted credence) removes the hard $0/1$ oracle, the decidability gate, and the forward simulation at once. The negative result is the catalogue of what truth-tracking costs; the positive result is what you buy by declining to pay it.

### 4.4 Where Value sits: the instrumental target is reached

Value — *would $H$ rather let $A$ pick from a menu?* — is the **instrumental** half, the decision-theoretic payoff. Do the two results deliver it, or only an epistemic notion? They deliver it, and the reason is *where Value sits* (v5 §1.2): it is pinned to the inequality face, not the equality face,
$$\textbf{Value} \;\Longleftrightarrow\; \textbf{Total Trust},$$
forced for any observable coherent expert by a two-option witness, **using no tower**, and *tight* (both directions, no slack). The tower sits strictly above — $\textbf{Mart} \Rightarrow \textbf{Total Trust} \Leftrightarrow \textbf{Value}$, with the reverse squeeze **failing** (the §1.6 amplifier). So Value is one strict rung **below** the tower, and that placement is the whole story:

- The **negative kills the rung *above* Value.** Forfeiting the tower forecloses the tower-route to Value and the per-day grade — but it **cannot touch Value itself**, which is weaker than the casualty. (The negative note's §6 says just this: the inequality/averaged faces survive.)
- The **positive installs the Value rung.** It forces bounded $\varepsilon$-violation Total Trust, and the tight witness carries it — summed over the class — to **classwise Value**. Tightness means **zero loss from Total Trust to Value**: the instrumental target arrives at *exactly* the grade of the epistemic one; everything sacrificed is the tower-surplus Value never needed.

So we **hit** the instrumental target, at the modest-expert grade. **Gated/classwise Value** says: averaged over a class of decisions (the days $A$ flags high), $H$ weakly prefers to let $A$ pick — which licenses **acting on $A$'s advice as a standing policy over a class**, the corrigibility-relevant content. What we **fall short of** is *per-decision* Value ("this specific choice, deferring is weakly better"); that shortfall is the ceiling, not a gap — it would need the per-day tower the negative forbids. (Per-day Value *is* available on the timely fragment $G$, via the frozen construction's per-day tower; §5.)

The honest limit: a class-average does not protect a single high-stakes deferral — classwise Value is consistent with one bad defer (where the inner-alignment and manipulation caveats live, §6). And Value rests on the fixed-option idealization; in Newcomblike / deference-punishing settings Value and endorsement diverge — out of scope, as in DDB/Weatherson.

---

## 5. Placing both against the frozen construction: the trichotomy

v5 §5 already had *one* positive cross-process result — the **frozen-deliberation** construction, which forces the *per-day* tower but only on the **timely fragment $G$** (questions that resolve within the lookahead), by using a **blind / sealed-sibling** target that freezes out $A$'s current quote. The two new results complete a clean three-cornered picture:

| target | face demanded | reach | verdict | where |
|---|---|---|---|---|
| **unfrozen** (coupled $H$) | pointwise equality (tower) | all sentences | **impossible** | negative note (this §2) |
| **unfrozen** (coupled $H$) | averaged inequality (bounded $\varepsilon$-violation Total Trust) | all *admissible* sentences | **forced** | positive note (this §3) |
| **blind / sealed** sibling | pointwise equality (tower) | timely fragment $G$ only | **forced** | v5 §5 (frozen) |

Reading the table: to keep the **pointwise equality** you must *either* retreat to the timely fragment *and* seal the target (row 3) — buying early **correctness** where questions resolve — *or* give it up entirely on the unfrozen target (row 1). To keep the **whole admissible domain** with the realistic unfrozen human, you must drop to the **averaged** face (row 2) — buying **faithfulness** across it but not per-question exactness. The two positive corners are complementary, as the positive note's §7 states: *soundness on the checkable fragment* (the AI is right, early) and *faithful acceleration everywhere* (the AI relays your own judgment, early).

The seam in all three is the same horizon. On $G$, the sealed sibling and the unfrozen self **coincide** — both have settled to the truth — so the freeness the criterion grants self-trust (`cee`) is recovered and the tower becomes as sound as self-trust. Off $G$, sealing (needed for blindness) and single-inductor structure (needed for free self-trust) pull apart, and only the averaged notion survives — which is exactly what the positive result delivers, by never needing the pointwise object in the first place.

---

## 6. What it means, and the honest residuals

**The alignment reading.** What is forced is that $H$ trusts $A$'s forecast of $H$ *itself*. On a question $H$ cannot resolve, $A$ is forced to relay $H$'s own eventual credence — right or wrong — only *sooner*. The AI adds **speed, not truth**: it cannot inject content of its own (that would show up as miscalibration and be arbitraged away), and it cannot make $H$ more correct than $H$'s own considered judgment. This is the formal core of `li-deference.md`'s "no fully-updated-deference problem": an AI that only predicts the human's own verdicts has nothing to gain by distorting them, hence no incentive to block correction — the shape a *corrigibility* (not merely alignment) story wants. It earns the instrumental half (classwise Value — averaged over a class of decisions, you may safely act on $A$'s recommendations) and is silent on the oracular half (it does *not* license "$A$ knows better than you").

**What stays open — and where.** The split is honest about its own soft joints, and they sit asymmetrically:

- **Negative side.** 2a is elementary and unconditional — treat it as airtight. 2b is an *underivability* argument resting on the cost-circularity skeleton; it is the less airtight half (v5 rates the cost-accounting ~75–80%).
- **Positive side.** The load-bearing input (II) is now *named* — it is Expectation Unbiasedness From Feedback, downgrading the old "gap 1" from open mathematics to construction bookkeeping. The **deepest residual** is obligation 3 of the positive note: *no hidden hard settlement*. The whole escape from 2a rests on the construction staying at $H$'s continuous price level and never settling against a discontinuous function of $a_n$. The §3 trader does so; a *full* construction (menus, bins, the feedback LUV sequence $\ulcorner E^H_{f(n)}(X)\urcorner$) must be audited to confirm no hard settlement sneaks back in. This is exactly the §4.1 crux made into an obligation: the positive result lives precisely as long as it refuses to build the negative result's diagonal.

**The boundary that remains.** Faithfulness is forced *everywhere*; the *soundness* that would make deference safe is forced only where questions resolve in time (v5 §6.3, the manipulation boundary). Accurate prediction of an independent human and active steering of a shaped one produce the *same* vanishing $a_n - Y_n$ — the trace cannot tell them apart off the checkable fragment. The negative and positive results together draw the line sharply: per-question exact trust is unreachable; aggregate faithful trust is forced and reaches everything; and the region where faithful $\ne$ sound is exactly the un-checkable one. That is the map, not yet the whole territory — but it is a map with both edges now proven.

---

## 7. Pocket summary

- **Same object.** Both results constrain $a_n = A$'s day-$n$ forecast of $H$'s lookahead credence $Y_n = E^H_{f(n)}(X)$, with $H$ the realistic (unfrozen, coupled) human.
- **Negative** ([`no-timely-pointwise-tower.md`](anson-notes/no-timely-pointwise-tower.md)): the **pointwise-equality** tower `Mart`$(H\to A)$ is impossible. It $\equiv$ tracking $a_n \approx_n Y_n$, killed by **2a** (anti-inductive diagonal, defect $\ge\tfrac12$, on quote-referencing families) and **2b** (cost-circularity, underivable, on quote-free families); the cases exhaust all families.
- **Positive** ([`faithful-acceleration.md`](faithful-acceleration.md)): the **averaged-inequality** form — bounded $\varepsilon$-violation Total Trust → Value — *is* forced over its **admissible domain** (all but the quote-referencing 2a family), no prior, from self-trust (I) + calibration (II = Expectation Unbiasedness From Feedback).
- **The fit.** Equality dies, averaged survives — on the admissible domain; on the 2a quote-referencing diagonal *both* die together (§4.1). They meet at v5's T5 **modest-expert ceiling** — negative proves you can't beat it, positive proves you reach it. **Value** is reached because it sits one rung *below* the dead tower (Value ⟺ Total Trust, tight, no tower), so the negative removes only surplus and the positive installs Value at zero extra cost (§4.4). The positive avoids 2a by staying at **continuous credences** and dodges 2b by calibrating **after the fact**; its reach is co-extensive with never building 2a's hard settlement (its deepest open obligation).
- **The slogan.** Not an exact early oracle per question (impossible); a faithful statistical accelerator across questions (forced) — speed, not truth, which is exactly what corrigibility, not omniscience, asks for.
