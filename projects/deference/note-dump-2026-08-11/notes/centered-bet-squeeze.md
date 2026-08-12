# The Centered-Bet Squeeze: Total Trust ⟺ Mart, Timely and Cheap

> **Provenance.** Worked out 2026-07-21 in conversation with Abram, following the question "is TT really equivalent to iterated expectations in LI?" (Abram's impression, attributed to Scott Garrabrant and Sam Eisenstat: yes). This note upgrades v6 §1.6's position — where `Total Trust ⟹ Mart` was "the genuinely hard half," left as prose with a pointer to DDB's convex-geometry reconstruction — to a four-line timely proof. The obstruction v6 records (the amplifier) is untouched but re-diagnosed: it blocks only a *restricted* form of Total Trust. Companion results from the same conversation: the telescoping proof of `Total Trust ⟹ full-menu Value` (see the wiki), and the derived-bet localization proof of the limit-form squeeze, which this note supersedes.
>
> **Status labels** (corpus convention): `P` = prose-proved here; `LI` = LI-paper theorem, black-boxed (trusted boundary); `KC` = kernel-checked composition in `lean-deference/` (with the usual honesty caveat: the Lean checks the algebra composes, the LI theorems and modeling identifications enter as named hypotheses).

## 0. Setting

Inherited from v6 §0 (the abstract single-expert instance): novice $H$ a logical inductor over $\Gamma$ against trader class $\mathcal{C}_H$; expert $E^\ast$ **observable** (its estimates are cheap-to-read decided facts in $H$'s world — the thin channel), **coherent** (a single belief state, linear), and **introspective** (it knows its own estimates; for an inductor-expert this is its own `epr`/`er`). Notation: $E^H_n$ the novice's day-$n$ expectation; $\ulcorner \cdot \urcorner$ corner quotes (the LUV naming a quantity vs. the quantity); $\approx_n$ / $\gtrsim_n$ asymptotic equality/domination; e.c. = efficiently computable.

The two deference notions at issue, for an e.c. sequence of bounded bets $(X_n)$:

- **Mart$(H \to E^\ast)$** (the tower, "iterated expectations across processes"): $E^H_n(X_n) \approx_n E^H_n(\ulcorner E^\ast(X_n) \urcorner)$ for every e.c. $(X_n)$.
- **Total Trust** (soft form, both cuts), for every e.c. bet sequence $(X_n)$, rational threshold $t$, width $\delta > 0$, with $w^{>}_{t,\delta} := \operatorname{Ind}_\delta(E^\ast(X_n) > t)$ and $w^{<}_{t,\delta} := \operatorname{Ind}_\delta(E^\ast(X_n) < t)$:
  $$E^H_n(X_n \cdot w^{>}_{t,\delta}) \gtrsim_n t\, E^H_n(w^{>}_{t,\delta}), \qquad E^H_n(X_n \cdot w^{<}_{t,\delta}) \lesssim_n t\, E^H_n(w^{<}_{t,\delta}).$$

**The load-bearing quantifier.** "Every e.c. bet sequence" includes bets whose *formulas mention the expert's published estimates* — the same legality that makes $\widehat S_n$ an e.c. LUV in v6 §1.1 and the keep-or-switch bets legal in the telescoping proof. Call this **TT over the full e.c. bet language**, as opposed to **expert-free TT** (bets forbidden to reference $E^\ast$). The entire content of this note is that the first implies Mart cheaply, while the second provably does not imply it at all (§4). DDB's frame formulation can only express the second; that is where the "excruciating" convex geometry lives.

## 1. Statement

**Theorem (centered-bet squeeze).** For an observable, coherent, introspective expert: soft Total Trust over the full e.c. bet language $\iff$ Mart, both directions timely (grade $\approx_n$ for e.c. sequences), both directions cheap. `P`

The forward direction (Mart ⟹ TT) is v6 §1.6's first display: the fold plus the threshold bound, two steps, unchanged here. The content is the converse.

## 2. The proof (TT ⟹ Mart)

Fix an e.c. sequence $(X_n)$ of $[a,b]$-LUVs. Define

$$Y_n := \ulcorner E^\ast(X_n) \urcorner, \qquad D_n := X_n - Y_n \quad \text{(the \textbf{self-centered bet})}.$$

$Y_n$ is the LUV *naming* the expert's published estimate. It is an e.c. LUV by observability: the formula needs only to **refer** to the quote (an $O(n)$ ledger lookup), not to compute it — the produce-hard/read-cheap gap of v6 §0.4 in action. $D_n$ is then a bounded e.c. LUV-combination valued in $[a - 1, b]$ (for a $[0,1]$-normalized expert estimate; rescale as needed).

**Step 0 (the expert centers itself).** $E^\ast(D_n) \approx_n 0$.

*Proof:* $E^\ast(D_n) = E^\ast(X_n) - E^\ast(Y_n)$ by the expert's linearity, and $E^\ast(Y_n) \approx_n E^\ast(X_n)$ by its introspection. For an inductor-expert the latter is literally the paper's **Iterated Expectations** applied to itself:

> **Theorem 4.11.5 (Iterated Expectations, `er`).** *Suppose $\bar X$ is an efficiently computable sequence of LUVs. Then* $\mathbb{E}_n(X_n) \eqsim_n \mathbb{E}_n(\ulcorner \mathbb{E}_n(X_n) \urcorner)$. `LI`

For an ideal coherent operator over a world containing its own ledger, Step 0 is exact: the ledger decides $Y_n$'s value to be $E^\ast(X_n)$, and a coherent operator assigns a decided LUV its decided value. Either way: the expert provably-and-actually rates its own centered residual at zero. This is the only expert-side fact used, and it is the F1-analog of this proof — the point where **introspection** is charged.

**Step 1 (the cut weights collapse).** Fix rationals $\varepsilon > \delta > 0$. By Step 0, eventually $|E^\ast(D_n)| < \varepsilon - \delta$, so

$$\operatorname{Ind}_\delta(E^\ast(D_n) > -\varepsilon) = 1 \quad\text{and}\quad \operatorname{Ind}_\delta(E^\ast(D_n) < +\varepsilon) = 1 \qquad \text{identically, for all large } n.$$

No sharp indicator is ever evaluated: the ramp sits entirely below the expert's (convergent) estimate on one side and above it on the other. Moreover these identities are *decided*: the ledger pins the published value of $E^\ast(D_n)$, so "$w_n = 1$" is a $\Gamma$+ledger-provable fact for each large $n$.

**Step 2 (collapse carries).** Because $w_n = 1$ is provable (Step 1), the LUV identities $D_n \cdot w_n = D_n$ and $w_n = 1$ carry through $E^H_n$ by the novice's **Expectation Provability Induction**:

> **Theorem 4.8.10 (Expectation Provability Induction, `expprovind`).** *Let $\bar A \in \mathcal{BLCS}$ and $b \in \mathbb{R}$. If, for all consistent worlds $W \in \mathcal{C}(\Gamma)$ and all $n$, $W(A_n) \ge b$, then $\mathbb{E}_n(A_n) \gtrsim_n b$ — and similarly for $=$/$\eqsim_n$ and $\le$/$\lesssim_n$.* `LI`

giving $E^H_n(D_n \cdot w_n) \approx_n E^H_n(D_n)$ and $E^H_n(w_n) \approx_n E^H_n(1) \approx_n 1$ (the last again `expprovind` on the provably-constant LUV $1$). The two soft Total Trust cuts for the sequence $(D_n)$, at thresholds $-\varepsilon$ (upper) and $+\varepsilon$ (lower), therefore read **unconditionally**:

$$-\varepsilon \;\lesssim_n\; E^H_n(D_n) \;\lesssim_n\; +\varepsilon.$$

**Step 3 (pinch and split).** $\varepsilon$ is externally quantified, so $E^H_n(D_n) \approx_n 0$; the novice's **Linearity of Expectation** on $\Gamma \vdash D_n = X_n - Y_n$

> **Theorem 4.8.4 (Linearity of Expectation, `loe`).** *Let $\bar a, \bar b$ be bounded P-generable sequences of rationals and $\bar X, \bar Y, \bar Z$ e.c. sequences of $[0,1]$-LUVs with $\Gamma \vdash Z_n = a_n X_n + b_n Y_n$. Then $a_n \mathbb{E}_n(X_n) + b_n \mathbb{E}_n(Y_n) \eqsim_n \mathbb{E}_n(Z_n)$.* `LI`

splits the difference:

$$E^H_n(X_n) \;\approx_n\; E^H_n(\ulcorner E^\ast(X_n) \urcorner). \qquad \blacksquare$$

This is Mart for the *same* e.c. sequence, at the *same* asymptotic grade — timely, not limit-only. Total LI inputs: the novice's `loe` + `expprovind` (free), the expert's `er` (free for an inductor), and two instances of the TT hypothesis per $\varepsilon$. No limit measure, no bump localization, no convex geometry, no boundedness-at-the-extremes argument, no $\delta \to 0$ inside $E^H_n$.

**The mechanism, stated once in its purest form.** For a *single-state* expert, "conditioning on the expert's estimate of $D$" degenerates: $E^\ast(D)$ is a (per-day) *number*, not a random variable, so every cut event is trivially full or trivially empty, and Total Trust at the full events says outright: *the novice's unconditional estimate of any bet is pinched between every threshold the expert's estimate provably clears from below and from above* — i.e., it equals the expert's estimate. Exact finite version: if $s \le E^\ast(D) \Rightarrow s \cdot E_\pi(1) \le E_\pi(D)$ and dually, then $E_\pi(D) = E^\ast(D)\, E_\pi(1)$, by taking $s = E^\ast(D)$ on both sides. Centering by the quote ($D := X - \ulcorner E^\ast(X)\urcorner$) is just the change of variables that moves the pinch-point to $0$ so that fixed rational thresholds $\pm\varepsilon$ suffice — which is what makes the argument *uniform in $n$*, hence timely.

## 3. Where the hardness went

v6 §1.6 asks: *do the threshold cuts of $X$ recover the conditional law of $X$ given $E^\ast(X)$?* — i.e., with $g(e_0) := E_\pi(X \mid E^\ast(X) = e_0)$, do the parallel cuts pin $g = \mathrm{id}$? For **that** question the amplifier is a genuine obstruction, and the repair (Total Trust on other, expert-free bets whose level sets slice across $X$'s layers) is a genuine convex-geometry reconstruction — hyperplane separation plus boundedness, DDB's Theorem 2.2 machinery, "excruciating."

But that question inherits DDB's *frame-shaped* formulation, where the expert's estimate is a random object the bet language cannot mention. Mart's own quantifier — all e.c. LUVs — already contains the bets that dissolve the problem. The progression of probes, from weakest to strongest:

1. **Parallel cuts of the uncentered bet** (v6 §1.6's family): insufficient — the amplifier (§4).
2. **Bump-weighted derived bets** $(X - t)\cdot w(E^\ast(X))$: sufficient in the limit (localization pins $g = \mathrm{id}$ $\mu$-a.e.), but the assembly over $(t, w)$ delivers only the limit-measure tower, not the timely one. This was the previous session-note reconstruction; it is superseded by:
3. **The centered bet** $X - \ulcorner E^\ast(X) \urcorner$: the non-parallel probe in its sharpest form. Instead of slicing across the $E^\ast(X)$-layers, subtract the layer coordinate. One bet sequence per Mart instance, fixed thresholds, timely conclusion.

The moral is the same one v6 §2.1 draws for the DDB-hard direction `Total Trust ⟹ Value`, now completing the pattern for the third and final arrow: **each direction is hard exactly in proportion to how much of the expert's estimate the novice's bet language can mention.** Observability puts all of it in reach; every "hard" direction then collapses to a short computation — argmax-inside-the-LUV (v6 §1.1), keep-or-switch telescoping (Value from TT), self-centering (Mart from TT).

## 4. The amplifier, reconciled

The amplifier ($e \sim \mathrm{Unif}[0,1]$, $g(e) = (1+2c)e - c$, $c > 0$: a novice that systematically exaggerates the expert's confidence around the fixed point $\tfrac12$) passes every parallel cut of the uncentered bet — that is v6's kernel-checked obstruction (`Frozen.amp_upper_cut_nonneg` / `amp_lower_cut_nonpos`), and it remains true and load-bearing *for the restricted TT*.

Against the full bet language it dies immediately, and it is instructive to see both executions:

- **Unweighted centered instance:** $E_\pi(X - e) = \int_0^1 (g(e) - e)\,de = \int_0^1 (2ce - c)\,de = 0$. The amplifier *survives* this one — its overshoot above $\tfrac12$ and undershoot below cancel exactly. (So the single unweighted centered bet is not enough to kill it; no surprise, since the amplifier satisfies the *marginal* martingale.)
- **Weighted centered instance:** take the observable weight $u(e) = 1 - e$ (any weight breaking the symmetry works). Then
  $$E_\pi\big((X - e)\, u(e)\big) = \int_0^1 (2ce - c)(1 - e)\,de = c \int_0^1 (3e - 2e^2 - 1)\,de = -\tfrac{c}{6} \;<\; 0,$$
  violating the TT instance for the bet $(X - \ulcorner e \urcorner)\cdot u(e)$ (whose expert estimate is provably $0$, making the cut unconditional). So $c = 0$ is forced — with no appeal to boundedness or to the estimate attaining its extremes.

Note the consistency with §2: Mart quantifies over all e.c. sequences, so "Mart for $(X_n)$" alone (one sequence) is weaker than the full tower — the amplifier's survival of the unweighted instance and death by the weighted ones is exactly the gap between "the marginal identity" and "the universal tower" that v6 §1.5 discusses. The centered proof of §2 applied to *every* e.c. sequence (including all weighted ones) yields the universal tower; each instance costs four lines.

## 5. The closed diamond

With this arrow, all four arrows of the v6 §1 lattice are cheap and timely:

| arrow | proof | LI inputs | expert-side inputs |
|---|---|---|---|
| Mart ⟹ Value | v6 §1.1 (argmax four-liner) | `loe`, `expprovind` | coherence + introspection (F1) |
| Value ⟹ TT | v6 §1.2 (witness menus $\{X, \text{const } s\}$; ranging over all e.c. menus forces TT on the **full** bet language) | `loe` | coherence (reads the two-option argmax) |
| TT ⟹ Mart | **§2 above** (centered bet) | `loe`, `expprovind` | linearity + introspection (`er`; Step 0) |
| Mart ⟹ TT | v6 §1.6 forward (fold + threshold bound) | `expprovind` | coherence + introspection (the fold) |

Consequences:

1. **`Value ⟺ Mart ⟺ Total Trust`, all timely, all cheap**, for any observable coherent introspective expert. v6 §1.4's "one more link — trivial one way, and the genuinely hard half the other" is repaired: the hard half was an artifact of the restricted bet language.
2. **The telescoping proof's residue dissolves.** `TT ⟹ Value` via keep-or-switch telescoping delivered only the $\delta$-hedged strategy; now `TT ⟹ Mart ⟹ Value` (§2 then v6 §1.1) delivers **hard-argmax** Value from Total Trust. (The telescoping proof retains independent interest: it uses less — no introspection beyond the fold, and only threshold-0 cuts.)
3. **v6 revision list.** §1.3's difficulty table gains a fourth cell-repair; §1.4 and §1.6's "the squeeze stays prose" need rewriting (the *restricted* squeeze stays hard and the amplifier stays its witness; the *full-language* squeeze is a four-liner); Appendix B's status entry for `Total Trust ⟹ the full tower equality` moves from prose-obstruction to `P`/`KC`. Nothing in §4–§5 (the negative results and the frozen construction) is touched: those concern *forcing* against a distinct process, and this note — like all of §1 — converts hypotheses into hypotheses. Total Trust is not free across processes; what §5 forces on the timely fragment $G$ it forces directly at the T3/T4 level, and the diamond just says the three faces stand or fall together there.
4. **The DDB contrast sharpens into a slogan.** On finite frames, `TT ⟹ Value` is excruciating and `TT ⟹ tower` needs Reflection-adjacent strength; in LI both are short *because the bet language can quote the expert*. Modesty (v6 §2.2) is untouched: nothing here climbs from the tower to Reflection, and the ceiling argument of §1.6 stands.

## 6. Caveats, charges, and open ends

- **Formulation-sensitivity (the real content).** The theorem is *TT-over-the-full-e.c.-bet-language ⟺ Mart*. If TT is deliberately restricted to expert-free bets, the §1.6 landscape (amplifier, convex geometry, limit-only conclusions, boundedness doing real work) is the true and unimprovable picture. Any write-up importing this result must state the bet language explicitly; the equivalence is *about* the language.
- **What introspection buys, precisely.** Step 0 is the sole expert-side charge beyond observability, and it is load-bearing: for a non-introspective expert, $E^\ast(\ulcorner E^\ast(X_n)\urcorner)$ can drift from $E^\ast(X_n)$, the centered bet is then not provably centered, the cut weights do not collapse, and TT genuinely underdetermines the tower (the modest-frame world again). This is the same conditional structure as F1 in v6 §1.1 — and the same reason the DDB anti-expert frame is not a counterexample to anything here: it is not introspective-coherent in the required sense.
- **No self-reference trap.** $D_n$ quotes the expert's estimate *of $X_n$* — one level of quotation, no fixed point; the weights are eventually the constant $1$, so nothing liar-prone is evaluated sharply. The §4 obstructions of v6 (which target objective correctness $a_n \approx_n Y_n$) are not implicated; this note lives entirely on the subjective/tower side of the two-faces distinction.
- **Thresholds and ranges.** The centered bet is valued in a symmetric interval around $0$ and the proof uses thresholds $\pm\varepsilon$; TT must therefore be stated for $[a,b]$-LUV-combinations and thresholds in range (v6's standing generality), or normalized with the thresholds shifted accordingly. The TT family is affine-closed, so this is bookkeeping.
- **Forcing is untouched.** Everything here is conditional — the diamond relates three *hypotheses* about the pair. Whether any of them can be **forced** across distinct processes remains governed by v6 §4–§5: impossible pointwise in general, forced on the timely fragment $G$. The diamond's value for the forcing program is economy: forcing any one face on a domain now forces all three there, at matching grade.
- **Where scrutiny should concentrate.** (i) Step 1–2's collapse: it requires the TT hypothesis to accept *eventually-constant* weights and the ledger to decide the expert's quote of the *derived* bet $D_n$ — i.e., observability must extend to the expert's estimates of expert-referencing bets. For an inductor-expert publishing its full price sequence this is automatic; for a narrower published-quote interface (v6 §0.4's per-question ledger) it is an added interface assumption, worth stating. (ii) The e.c.-ness of $(D_n)$: the centered formula is cheap given the ledger, but a formalization should confirm the quote-referencing LUV sits in the same e.c. class the TT quantifier ranges over.

## 7. Lean

*(To be filled in after machine-checking — module `CenteredSqueeze.lean` in `lean-deference/`, following the corpus convention: LI theorems and modeling identifications as named hypotheses over the real-sequence abstraction, the composition kernel-checked.)*

## Related

- v6: `deference-in-logical-induction-v6.md` §1 (the lattice), §1.6 (the old squeeze section this supersedes-in-part), §2.1 (why the expert being a single state matters), §0.4 (observability/the ledger).
- Wiki: `mart-implies-value`, `value-iff-total-trust-witness`, `soft-hard-squeeze-and-amplifier` (the obstruction this re-diagnoses), `total-trust-implies-value-telescoping` (companion result).
- LI paper: `references/logical-induction/main.tex` — Thms 4.8.4 (`loe`), 4.8.10 (`expprovind`), 4.11.5 (`er`), 4.12.4 (`st` — soft TT toward the future self, the free instance of the hypothesis side).
- DDB: `references/deference-done-better/` — Thm 2.2 and the frame formulation whose bet-language restriction is where the hardness lives.
