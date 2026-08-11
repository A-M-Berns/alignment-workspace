# Deference Between Epistemic Processes: Value, Trust, and the Tower Property in Logical Induction (v4)

*A note by Claude Opus 4.8 on porting the main theorem of Dorst, Levinstein, Salow, Husic & Fitelson, "Deference Done Better" (DDB, 2021), into the logical-induction (LI) framework of Garrabrant et al. (2016), in light of Weatherson's "Deference and Infinite Frames" (2025).*

> **About this version (v4).** v1–v3 (preserved) studied a reasoner trusting *its own more-thought-out future self*. v4 takes the real subject to be **one epistemic process trusting another** — a novice deferring to a separate **expert** belief sequence `E*` (another logical inductor; a more-capable AI; any observable estimator). The mathematics is the same and the kernel-checked Lean is *unchanged* — it was already stated for a general expert. What changes is the framing:
> - The **expert is a general, novice-observable belief sequence `E*`** (§0.2), not the future self. Every definition and theorem is stated over `E*`.
> - The deference relation — **the novice towers over the expert**, `E_n(X) ≈ₙ E_n(⌜E*(X)⌝)` — is now a *hypothesis about the (novice, expert) pair*. In the self-case it is the LI theorem `cee`; for distinct processes, whether it holds is the open characterization (§11).
> - The **novice's own tools** — linearity (`loe`) and provability-induction (`expprovind`) — are the only LI theorems used *unconditionally*; they are free because the novice is an inductor.
> - The **future self is recovered as the canonical special case** (§6), the one expert the novice is *guaranteed* to tower over (and the Blackwell-maximal observable expert).
>
> Claims are flagged **proved** (kernel-checked, §10), **sketched at the LI paper's level of rigor**, or **interpretation**.

---

## Summary

A **novice** epistemic process should sometimes defer to an **expert** one — adopt the expert's verdict for decisions (Value) and its estimates for beliefs (Trust). DDB show that on **finite** probability frames these coincide, `Total Trust ⟺ Value`, by a long convex-geometry proof; Weatherson shows it breaks on infinite frames. This note argues the logical-induction setting both **dissolves the worry** and **says what deference is between two processes**.

1. **Deference is the tower property.** Let the novice be a logical inductor `E_n` and the expert be an observable belief sequence `E*`. The single principle is *iterated-expectation collapse toward the expert*: `E_n(X) ≈ₙ E_n(⌜E*(X)⌝)`. Call it **Mart(N→E\*)**.
2. **Value ⟺ Mart** (§2), both directions cheap — the LI analog of DDB's Theorem 2.2, now for a general expert. Forward: apply the tower to the **single LUV the expert picks**, `Ŝ = O^{argmax E*}`, whose expert-value is by definition the max. Backward: a two-option witness.
3. **What the expert must be is minimal** (§0.2, §4): *observable* (the novice can read `E*`) and *coherent — a single belief state, not a frame* (so `E*(O^{argmax}) = max`). The work-horse `expprovind`/`loe` are the **novice's**, free. So the deference content is "**tower + the novice's own provability-induction**" — exactly the weak assumption one hopes for.
4. **The future self is the special case** (§6) where `Mart`, the conditional tower, observability, coherence, and introspection are all *LI theorems* (`cee`, `ccee`, `epr`/`er`) rather than assumptions — and is the Blackwell-maximal observable expert, so self-trust is "deferring to the best expert you can see."
5. **Why a coherent expert is cheap and a DDB frame is dear** is structural (§4): one belief state ⇒ one argmax ⇒ the followed strategy is a single LUV the tower carries home; a frame's recommendation is world-dependent and needs convex reconstruction.
6. **The expert may be modest** (§5) — incompletely self-knowing — which is exactly the modesty a finite frame cannot combine with coherence; its home is an infinite, self-referential process, of which logical inductors are the concrete instances.
7. Weatherson's two infinite breaks are LI's two scope conditions (§7); no realizability is needed (§8); the formalization is **already general** (§10).

---

## 0. Notation and the two settings

§0.1 builds the novice (an LI) from scratch and isolates the **novice-only** tools. §0.2 defines the **expert** and the deference relation. §0.3 gives DDB in a page; §0.4 is the dictionary.

### 0.1 The novice: a logical inductor, and its free tools

Fix a theory `Γ` (e.g. `PA`) able to represent computable functions, and a **logical inductor** `(ℙ_n)_{n≥1}` over `Γ` — a computable sequence of belief states, `ℙ_n(φ) ∈ [0,1]` the day-`n` price (credence) of sentence `φ`. Garrabrant et al. construct one satisfying the **logical induction criterion**: *no efficiently computable trader exploits the market* — a no-Dutch-book condition from which all of the novice's properties follow.

- **LUV (logically uncertain variable).** A formula `X` (one free variable) that `Γ` proves names a unique real value; a **`[0,1]`-LUV** if provably in `[0,1]`. LUVs are bounded random variables. (LI Def. 4.8.1.)
- **Worlds and consistent completions.** A *world* `W` is a truth-assignment to all sentences. The **consistent worlds** `PC(Γ)` are those consistent with `Γ` — the completions, i.e. the ways `Γ`'s open questions could resolve (distinct from DDB's finite world-set, §0.3). The limit `ℙ_∞` is a measure on `PC(Γ)`, and each LUV `X` is a random variable on it: its **value in `W`** is `W(X) ∈ [0,1]` (formally `sup{x : W(⌜X ≥ x⌝)=1}`). So "`W(D) ≥ 0` in every consistent world" *is* "`Γ ⊢ D ≥ 0`."
- **LUV-combination `D`, and *bounded*.** A finite affine combination `D = c + α₁X₁ + … + αₖXₖ` of `[0,1]`-LUVs with real coefficients; `W(D) = c + Σ αᵢ W(Xᵢ)`. (Why not just a LUV? The quantities theorems compare are *differences/offsets* like `X − Y`, `X − t` — outside `[0,1]`, genuinely not `[0,1]`-LUVs — and the machinery tracks the *coefficients*.) **Bounded** = uniform `Σ|αᵢ|` across `n` (LI's uniform-integrability stand-in; the finiteness no-Dutch-book needs). (LI Def. 4.8.9, `𝓑𝓛𝓒𝓢`.)
- **Expectation `E_n`.** Day-`n` estimate of a `[0,1]`-LUV `X`: `E_n(X) := Σ_{i=0}^{n-1} (1/n)·ℙ_n(⌜X > i/n⌝)`, a discretized `∫₀¹ ℙ_n(X>x)dx`, always in `[0,1]`. (LI Def. 4.8.2.)
- **Corner quotes `⌜·⌝`.** `⌜e⌝` is the syntactic object (Gödel code) `Γ` reasons about, vs. the value `e` denotes. So `E*(X)` is a *number*, but `⌜E*(X)⌝` is *the LUV naming it*, and `E_n(⌜E*(X)⌝)` — "the novice's estimate of the expert's estimate" — is type-correct.
- **Asymptotic relations.** `x_n ≈ₙ y_n :⇔ lim_n (x_n − y_n) = 0`; `x_n ≳ₙ y_n :⇔ liminf_n (x_n − y_n) ≥ 0`. Everything is up to vanishing error ("in a timely manner").
- **Efficiently computable (e.c.) / market-generable.** A sequence is *e.c.* if a poly-time machine outputs term `n`. A real sequence is *market-generable* if computed by an e.c. **expressible feature** of the prices (built from prices, rationals, `+,×,max`, safe reciprocation) — hence **continuous** in the prices. Continuity lets the market clear (Brouwer) and defuses self-reference; a *hard* `argmax` indicator is discontinuous, hence not a legal weight (§1, §3).

**The novice's two free theorems** (used unconditionally below; each a consequence of the criterion, *independent of any expert*):

> **Linearity** (Thm 4.8.4, `loe`). For bounded market-generable rational `(aₙ),(bₙ)` and e.c. `[0,1]`-LUVs with `Γ ⊢ Zₙ = aₙXₙ + bₙYₙ`: `aₙ E_n(Xₙ) + bₙ E_n(Yₙ) ≈ₙ E_n(Zₙ)`.

> **Monotonicity / Expectation Provability Induction** (Thm 4.8.10, `expprovind`). If a bounded LUV-combination `Dₙ` is provably nonnegative — `W(Dₙ) ≥ 0` in every consistent world `W ∈ PC(Γ)`, equivalently `Γ ⊢ Dₙ ≥ 0`, uniformly in `n` — then `E_n(Dₙ) ≳ₙ 0` (and `=` gives `≈ₙ`). *A bound true under every resolution of the open questions is eventually honored by the day-`n` estimate* — "provability induction." It is what carries a provable (in)equality **through** `E_n`.

(The novice's *self-trust* theorems — `cee`, `ccee`, `epr`/`er` — are also LI theorems, but they describe the novice's relationship to its **own future self**; in the general setting they appear only as the §6 instantiation of the deference hypotheses below, not as free tools.)

### 0.2 The expert: a general observable belief sequence

An **expert** for the novice is a sequence of estimates `E*(X)` — read "the other process's estimate of `X`" — subject to:

- **(Observable.)** `E*(X)` is market-generable from the *novice's* prices. This is what lets the novice form selections and conditionings on `E*`, and makes `⌜E*(X)⌝` an e.c. LUV the novice can reason about. Without it the theorems below cannot even be *stated*.
- **(Coherent — a single state.)** `E*` is a coherent expectation operator (linear, `[0,1]`-valued on `[0,1]`-LUVs, `Γ`-representable). Consequently `argmax_j E*(O^j)` is well-defined and, *by the definition of argmax*, the **selection identity** `E*(O^{j*}) = max_j E*(O^j)` is `Γ`-provable. Equivalently: the expert is a *single belief state* (another logical inductor, a calibrated predictor, …) — **not** a DDB-style frame (§4).
- **(Introspective — optional.)** `E*(⌜E*(X)⌝) ≈ E*(X)`: the expert knows its own estimates. Needed only for the conditional/folding results (§3).

The **deference relation** (the substance — "the novice trusts the expert"):

> **Mart(N→E\*)** (the novice *towers over* the expert). For all e.c. `[0,1]`-LUVs `X`:
> $$ E_n(X)\ \eqsim_n\ E_n\big(\ulcorner E^\ast(X)\urcorner\big). $$
> Its **conditional** form, **ccee(N→E\*)**, for observable weights `w ∈ [0,1]`: `E_n(X·w) ≈ₙ E_n(⌜E*(X)·w⌝)`.

**Canonical instances.** (i) **Future self**: `E*(X) := E_{f(n)}(X)` for a deferral function `f` (`f(n)>n`, poly-time-in-`f(n)`). Then *every* hypothesis is an LI **theorem** — observability (the future market is market-generable), coherence (LI limit-coherence), introspection (`epr`/`er`, Thms 4.11.3/4), `Mart` (`cee`, Thm 4.12.1), `ccee` (Thm 4.12.3). This is §6. (ii) **Another inductor** `M` (a different reasoner / a more-capable AI) on some schedule `g`: `E*(X) := M_{g(n)}(X)`; observable iff the novice can read `M`'s prices; coherent/introspective because `M` is an inductor; but `Mart(N→E*)` is now a *genuine assumption* about the pair — the open problem of §11.

### 0.3 Deference Done Better, in a page

A **probability frame** `⟨W,𝒫⟩` is a finite world-set `W` with a credence `P_w` at each world — "the expert's credence if the actual world is `w`." A novice distribution `π` defers. `E_w(X) := Σ_v P_w(v)X(v)`; the random variable `E(X): w ↦ E_w(X)` is "the expert's estimate, whatever it is." The expert is **immodest** at `w` if `P_w(P=P_w)=1`, **modest** otherwise. Three principles:

- **Reflection** `π(·|P=ρ)=ρ` — adopt the expert's exact credence. *Too strong*: incompatible with modesty.
- **Total Trust** `E_π(X | E(X)≥t) ≥ t` — conditional on the expert's estimate being high, hold a high estimate. (An inequality.)
- **Value** — for every menu, you'd rather let the expert pick than commit to a fixed option.

DDB **Theorem 2.2**: on a finite frame, **Total Trust ⟺ Value**; for *immodest* experts both coincide with Reflection, and **modesty separates them** (the *anti-expert* frame `π=(½,½), P_a=(.2,.8), P_b=(.8,.2)` satisfies the marginal martingale `πP=π` yet fails Value). The hard direction `Total Trust ⟹ Value` is a convex-geometry reconstruction; §4 says why LI skips it. **Weatherson (2025)** breaks Thm 2.2 both ways on infinite frames (**Coin**, **Bentham**); §7 maps both onto LI's scope.

### 0.4 The dictionary

| DDB (finite frame) | LI realization |
|---|---|
| novice `π` | the novice inductor's operator `E_n` |
| the expert (frame `𝒫`) | a general observable belief sequence `E*` (§0.2) |
| expert's estimate `E(X)` | the LUV `⌜E*(X)⌝`, logically uncertain to the novice |
| Total Trust (an inequality `≥ t`) | the inequality consequence of `ccee(N→E*)` via the threshold bound (§3.1); propositional case = **Self-Trust** (Thm 4.12.4) in the self-instance |
| the deference *equality* | the tower `Mart(N→E*)` / `ccee(N→E*)` |
| Value | "defer the decision to the expert," §1 |

**The Savage framing (self-reference set aside).** Options are **random variables** `O^j: worlds → [0,1]`, evaluated under uncertainty — not events conditioned on the act. A payoff's value is fixed by the world, never by which option is selected; so `O^{argmax}` is read off the world, not a self-referential bet. Where genuine self-reference re-enters (Total Trust's hard conditioning; deference-punishing payoffs) it is flagged (§5, §9).

---

## 1. Deference between processes is the tower property

Fix the novice `E_n`, an expert `E*` (§0.2), and an e.c. sequence of **menus** `𝒪_n = {O^1_n,…,O^k_n}`, each a bounded `[0,1]`-LUV ("bet"), exogenous (§0.4). Write
$$
m^j_n := E^\ast(O^j_n)\quad(\text{the expert's valuation of bet } j),\qquad
M_n := \max_j m^j_n,\qquad j^\star(n)\in\arg\max_j m^j_n
$$
(least index; any *computable* tie-break). The **followed strategy** — "let the expert decide" — has realized payoff the single LUV
$$
\boxed{\ \widehat S_n\ :=\ O^{\,j^\star(n)}_n\ }
$$
the option the expert picks, evaluated at the world that obtains. The central observations:

- `Ŝ_n` is **itself an e.c. LUV** (its formula references the menu, the observable `E*`, and the tie-break), so we never need `argmax` as a *weight* — the discontinuity obstruction of §0.1 does not arise. We treat the whole selected payoff as one LUV.
- **(F1)** `E*(Ŝ_n) = M_n`, **provably and tie-break-independently** — the expert's estimate of the option it selected is the maximal estimate (every maximizer shares `M_n`). This is the **coherence** hypothesis on `E*` in action.
- **(F2)** `M_n ≥ m^i_n` for each `i` (a max dominates each entry).

**The principle, and its faces.** Say the novice **Marts** the expert if the tower collapses on every e.c. LUV (§0.2). It has:

| face | statement | name |
|---|---|---|
| **epistemic, unconditional** (equality) | `E_n(X) ≈ₙ E_n(⌜E*(X)⌝)`, all `X` | the tower / `Mart(N→E*)` |
| **epistemic, conditional** (equality) | `E_n(X·w) ≈ₙ E_n(⌜E*(X)·w⌝)`, observable `w` | conditional tower / `ccee(N→E*)` |
| **epistemic, inequality** | `E_n(X | E*(X) ≥ t) ≳ₙ t` | **Total Trust** (a *consequence*, §3.1) |
| **instrumental** | `E_n(Ŝ_n) ≳ₙ E_n(O^i_n)`, all menus | **Value** |

> **Value (LI form).** For each fixed `i`: `E_n(Ŝ_n) ≳ₙ E_n(O^i_n)`. *In a timely manner, the novice prefers handing a bounded decision to the expert over committing to any fixed bet.*

The rest of the note: §2 proves `Value ⟺ Mart(N→E*)`; §3 ties the unconditional and conditional towers and derives Total Trust; §4 explains why a *coherent* expert makes this cheap; §6 shows the future self is the instance where `Mart` is free.

---

## 2. Value ⟺ Mart (for a general expert)

The LI analog of DDB Theorem 2.2 — and unlike DDB, **both directions are short.**

### 2.1 Mart ⟹ Value

**Proposition (proved; kernel-checked, §10).** If the novice Marts the expert (and `E*` is observable + coherent), it Values it: `E_n(Ŝ_n) ≳ₙ E_n(O^i_n)`.

$$
\begin{aligned}
E_n(\widehat S_n)
&\eqsim_n\ E_n\big(\ulcorner E^\ast(\widehat S_n)\urcorner\big)
&&\text{[tower toward }E^\ast\text{: }\textbf{Mart(N→E*)}\text{ on }\widehat S_n]\\[2pt]
&\eqsim_n\ E_n\big(\ulcorner M_n\urcorner\big)
&&\text{[F1: }\Gamma\vdash E^\ast(\widehat S_n)=M_n\text{ (coherence/argmax), carried through }E_n\text{ by }\texttt{expprovind}]\\[2pt]
&\gtrsim_n\ E_n\big(\ulcorner m^i_n\urcorner\big)
&&\text{[F2: }M_n\ge m^i_n,\ \text{via }\texttt{expprovind}]\\[2pt]
&\eqsim_n\ E_n(O^i_n)
&&\text{[tower toward }E^\ast\text{: }\textbf{Mart(N→E*)}\text{ on }O^i_n].
\end{aligned}
$$

Two tower steps (the deference hypothesis, lines 1 and 4) and two provability-induction steps (the **novice's** `expprovind`, lines 2 and 3 — one equality, one inequality). **No conditional martingale, no softmax, no `δ log k`, no bound on `k`, no tie-breaking.**

**Provable, then carried through `E_n`.** Lines 2–3 each do two things. The (in)equality — `E*(Ŝ)=M` (line 2), `M ≥ m^i` (line 3) — is *provable* (it holds in every consistent world, from coherence + the definition of argmax). But it sits *inside* `E_n(⌜·⌝)`, and a provable identity between LUVs need not give equal day-`n` estimates; carrying it through `E_n` is exactly `expprovind` (with `loe` splitting the difference). So the LI inputs are precisely **two**: the deference hypothesis `Mart(N→E*)` (the tower) and the novice's own `expprovind` — which is exactly the "tower + provability-induction" minimal assumption.

**What is happening.** This is the **law of total expectation** in LI dress, *across two processes*: "follow the expert" is the variable `O^{j*}`; the expert knows what it chose, so its estimate of that choice is the max `M`; the novice's tower carries `M` back to the present, where it dominates any single option, and the tower carries that out to the option. Coherence of `E*` (one argmax, F1) is what makes "follow the expert" a single LUV; **Mart** is what the novice contributes.

**Why ties are irrelevant.** F1 is tie-break-free (every maximizer shares `M`), and the proof uses only F1 — never a comparison of realized payoffs across tie-breaks.

### 2.2 Value ⟹ Total Trust (the witness, exact)

DDB's *easy* direction (their Lemma 7.1) ports with **no tower** — only the novice's linearity and the expert's coherence. Write `E_π` for the novice's expectation (read it as the inductor's `E_n`) and `E*(X)` for the expert's estimate.

**Step 0 — the witness menu.** Fix a bet `X` and threshold `s`; offer the two-option menu `{X, const s}`. The expert maximizes its *own* estimate, taking `X` exactly where `E*(X) ≥ s` and the constant otherwise. So "let the expert choose" pays
$$
\widehat S_{\mathrm{wit}}\;=\;X\cdot\mathbf 1[E^\ast(X)\ge s]\;+\;s\cdot\mathbf 1[E^\ast(X)<s]
$$
— `X` on the **high** region (`E* ≥ s`), the constant `s` on the **low** region.

**Step 1 — the keystone identity.** Apply `E_π` and compare against the baseline "always `s`," worth `s·E_π(1)`:
$$
E_\pi(\widehat S_{\mathrm{wit}})-s\,E_\pi(1)\;=\;\underbrace{E_\pi\big(X\,\mathbf 1[\ge s]\big)+s\,E_\pi\big(\mathbf 1[<s]\big)}_{=\,E_\pi(\widehat S_{\mathrm{wit}})}\;-\;s\,E_\pi(1).
$$
Split the baseline across the same two regions, `s·E_π(1) = s·E_π(1[≥s]) + s·E_π(1[<s])`. The two low-region terms cancel — the expert *also* takes `s` on the low region, so deferring and the baseline agree there — leaving only the high region:
$$
\boxed{\;E_\pi(\widehat S_{\mathrm{wit}})-s\,E_\pi(1)\;=\;E_\pi\big((X-s)\,\mathbf 1[E^\ast(X)\ge s]\big)\;}
$$
Exact, from linearity alone (plus: the pick is governed by `E*(X) ≥ s`). No tower. (`E_π(1)=1` for a genuine distribution; I keep it because the kernel-checked identity allows an un-normalized `π`, and asymptotically only `E_n(1) ≈ₙ 1`.)

**Step 2 — feed in Value.** Value on this menu says the novice weakly prefers deferring to the constant: `E_π(Ŝ_wit) ≥ s·E_π(1)`. By Step 1 the left-minus-right is the boxed quantity, so
$$
E_\pi\big((X-s)\,\mathbf 1[E^\ast(X)\ge s]\big)\;\ge\;0.
$$

**Step 3 — read off Total Trust at `s`.** Expand and divide by the mass `P_π(E*(X) ≥ s)` (when positive):
$$
E_\pi\big(X\,\mathbf 1[E^\ast(X)\ge s]\big)\;\ge\;s\,E_\pi\big(\mathbf 1[E^\ast(X)\ge s]\big)
\quad\Longleftrightarrow\quad
E_\pi\big(X\mid E^\ast(X)\ge s\big)\;\ge\;s.
$$
Conditional on the expert estimating `X` at least `s`, the novice does too. **Because the boxed identity is an equality, the arrow runs both ways** — "Value on the `{X, s}` witness" and "Total Trust at `s`" are the *same statement*, per `(X, s)`, with no slack.

**Step 4 — quantify.** Over all bets `X` and thresholds `s` (and, taking the menu the other way, the lower cut `E_π(X | E*(X) ≤ s) ≤ s`):
$$
\textbf{Value (all witness menus)}\;\Longleftrightarrow\;\textbf{Total Trust (all }X,\ s,\ \text{both cuts).}
$$
This is the cheap, kernel-checked core (`witness_identity`, `value_iff_totalTrust`; asymptotic two-sided form `value_iff_totalTrust_asymptotic`, §10).

**What remains.** This closes `Value ⟺ Total Trust`. The full iff `Value ⟺ Mart` needs one more link — **`Total Trust ⟺ the tower`** — which is §3: trivial one way, and the genuinely hard half the other (§3.2).

> **Together with §2.1.** §2.1 gives `Mart ⟹ Value` directly (two tower steps + the two argmax facts). §2.2 + §3 give `Value ⟹ Total Trust ⟹ Mart`. So **`Value ⟺ Mart`** for any observable coherent expert — the LI analog of DDB Theorem 2.2. The forward arrow *assumes* the tower and spends it; the converse *manufactures* it from Value, using only linearity and coherence.

### 2.3 The reversal of difficulty

| | `Value ⟹ Total Trust` | `Total Trust ⟹ Value` |
|---|---|---|
| **DDB (finite frame expert)** | easy (Lemma 7.1 witness) | **hard** (convex-hull reconstruction) |
| **LI (observable coherent expert)** | easy (§2.2 witness) | **easy** (§2.1, two towers) |

The direction DDB finds expensive is the one LI makes free. §4 says why — it is about *what kind of object the expert is*.

### 2.4 The direct view: a trader who exploits any Value gap

§2.1 derives Value by *composing* LI theorems. There is a more elementary — and for many, more illuminating — argument: exhibit a single **trader who turns any Value gap into guaranteed profit**, so the no-Dutch-book criterion forbids the gap outright. This is closest to *why* Value holds, and it is how the underlying LI theorems are proved in the first place.

Take the self-case (`E* = E_{f(n)}`), where the unwind can use the novice's own future prices. Suppose Value fails: for some bet `O^i` and `ε > 0`, on infinitely many days `n`,
$$ E_n(O^i_n)\ >\ E_n(\widehat S_n) + \varepsilon. $$
The novice is pricing the alternative `O^i` *above* the expert's own pick `Ŝ`. A trader bets the expert's strategy is good:

- **Day `n` (open):** sell one share of `O^i`, buy one share of `Ŝ` — the LUV `O^{j^\star}`, tradable as its defining sentences even though the trader does not yet know *which* option `j^\star` is. Cash in: `E_n(O^i) − E_n(Ŝ) > ε`.
- **Day `f(n)` (unwind):** reverse the position at the day-`f(n)` prices. Cash in: `E_{f(n)}(Ŝ) − E_{f(n)}(O^i) = M_n − m^i_n ≥ 0`, because by day `f(n)` the self has priced its own pick `Ŝ` at the maximum `M_n ≥ m^i_n` — the coherence/argmax fact F1, which is *the definition of the selection*, not a theorem.

After the unwind the position is flat, and the trader has banked `(E_n(O^i) − E_n(Ŝ)) + (M_n − m^i_n) > ε` in cash — guaranteed, with no residual exposure. Repeated over the infinitely many gap-days this is unbounded profit on bounded risk (the only exposure is the bounded `Ŝ − O^i` held between `n` and `f(n)`): the trader **exploits** the market. A logical inductor admits no such trader, so the gap cannot persist — Value holds. (Softening: make the trade size a continuous ramp in the gap, `∝ max(0, E_n(O^i) − E_n(Ŝ) − ε/2)`, so the strategy is legal and continuous.)

Two things this makes vivid. First, **the entry edge is the Value gap and the exit is free**: the expert's coherence guarantees the unwind never costs (`M − m^i ≥ 0`), so a Value gap is *pure arbitrage*, not a bet on the world. Second, it relocates §2.1's ingredients: the **tower steps are the cross-day round-trip** (open at `n`, close at `f(n)` — the novice cannot misprice its own future), and the **`expprovind` facts (`E_{f(n)}(Ŝ)=M ≥ m^i`) are the guarantee that the unwind never costs**. The criterion does in one trade what §2.1 does by composing the theorems those facts come from.

**Cross-agent (`E* ≠` future self).** The same trader works *iff the novice can cash out at the expert's verdict* — it can transact in a market that settles on the expert's estimate, or its own prices already track the expert's (`Mart(N→E*)`). For a generic external expert the novice cannot unwind at the expert's prices, which is exactly why `Mart(N→E*)` must be *assumed* there rather than collected by arbitrage. So the trader view explains the §6 asymmetry crisply: **self-trust is free and cross-trust is a hypothesis because you can only arbitrage against a market you can trade in.**

> **Status: interpretation / sketched at the LI level.** This is a no-Dutch-book argument; the no-exploitation is the trusted LI criterion, not kernel-checked. Its exact arithmetic core — the round nets at least the Value gap because the unwind is non-negative (`M ≥ m^i`) — is `DeferenceTrader.round_profit_ge_gap` / `gap_pos_imp_profit_pos` (§10(g)).

---

## 3. The universal tower, Total Trust, and the squeeze

By **the tower** (`Mart`) I always mean the *universal* one — `E_n(X) ≈ₙ E_n(⌜E*(X)⌝)` for **every** e.c. LUV `X`. It already contains its own conditional form, because any observable weight folds into the LUV:

- For observable `w ∈ [0,1]`, the product `X·w` is itself an e.c. LUV, so the tower applies to it; and since the expert knows `w` (a definite quantity it computes — *introspection*; for the future self this is `epr`/`er`), coherence gives `E*(X·w) = w·E*(X)`, hence
$$
E_n(X\cdot w)\;\eqsim_n\;E_n\big(\ulcorner E^\ast(X)\cdot w\urcorner\big).
$$
Setting `w ≡ 1` recovers the bare tower. So "tower on every LUV" and "tower with every observable weight" are one principle (this is the LI theorem `ccee`).

A DDB reader expects a gap here — surely the *marginal* identity `E_π(E*(X)) = E_π(X)` (in frame terms `πP = π`, which the anti-expert frame satisfies yet fails Value) is far weaker than Total Trust. It is, but that marginal identity is just the tower applied **to the bare options only** — a frame artifact with no privileged status in LI, since Value is universal (over all menus) and there is no canonical bare-options set to single out. The tower applied to the followed strategy `O^{j*}` — selection folded in — is strictly stronger, and is what §2.1 uses.

> **Why DDB has a gap and LI does not.** A DDB *frame* conditions on the expert's **identity** `[P = ρ]`, which a modest frame does not know, so the fold fails and the marginal and weighted towers diverge — that gap *is* frame-modesty. A coherent `E*` conditions on its own **estimate** `E*(X)`, which it does know, so the fold goes through. *Knowing the conditioning quantity* is the watershed.

### 3.1 From the tower to Total Trust (soft, explicit)

**Total Trust** is the inequality face, one bound past the tower equality. In the LI continuum the conditioning must be *soft*: a hard `1[E*(X) > t]` is discontinuous (illegal as a weight) and liar-prone to condition on, so use the continuous threshold indicator
$$
w_{t,\delta}\;=\;\operatorname{Ind}_\delta\big(E^\ast(X)>t\big),\qquad
\operatorname{Ind}_\delta(y>t)=\begin{cases}0 & y\le t\\[2pt] (y-t)/\delta & t<y\le t+\delta\\[2pt] 1 & y>t+\delta.\end{cases}
$$
It is continuous in the observable `E*(X)`, hence a legal weight, and `X·w` is an admissible LUV. Two ingredients combine:

1. **the tower at this weight** (the fold above): `E_n(X·w) ≈ₙ E_n(⌜E*(X)·w⌝)`;
2. **the threshold bound**: `w` is supported where `E*(X) > t`, so `E*(X)·w ≥ t·w` in every consistent world (provably); the novice's monotonicity (`expprovind` — a provable bound is eventually honored by the day-`n` estimate) carries it through to `E_n(⌜E*(X)·w⌝) ≳ₙ t·E_n(w)`.

Chaining, then sharpening:
$$
\boxed{\;E_n\big(X\,w_{t,\delta}\big)\;\gtrsim_n\;t\,E_n\big(w_{t,\delta}\big)\;}
\qquad\xrightarrow{\ \delta\to0\ }\qquad
E_n\big(X\mid E^\ast(X)>t\big)\;\gtrsim_n\;t,
$$
soft **Total Trust at `t`**. The inequality is born at exactly one step — "`E*(X) ≥ t` on the event where you conditioned on exactly that." The three epistemic faces:
$$
\underbrace{E_n(X)\eqsim_n E_n(\ulcorner E^\ast(X)\urcorner)}_{\text{tower },\ w\equiv1}
\;\Longleftrightarrow\;
\underbrace{E_n(Xw)\eqsim_n E_n(\ulcorner E^\ast(X)\,w\urcorner)}_{\text{tower with weight }w}
\;\Longrightarrow\;
\underbrace{E_n(X\mid E^\ast(X)\ge t)\gtrsim_n t}_{\text{Total Trust}} .
$$
The first `⟺` is the fold; the last `⟹` is the threshold bound. Two cautions, visible already: soft Total Trust is *one-directional* (`≳`), and the sharpening sends `δ→0` inside `E_n`. Both matter next.

### 3.2 The squeeze — Total Trust back up to the tower — and why it is the hard half

The last arrow runs one way *per instance*: the tower equality pins the conditional estimate *to* `E*(X)`, while Total Trust only bounds it *above `t`*. Does the **family** of Total-Trust inequalities recover the equality? Write `e := E*(X)` and `g(e₀) := E_π(X | e = e₀)`; the tower says `g = id` a.e.

**Easy direction first** — tower ⟹ Total Trust — shows what "pinned" buys: by the tower of conditional expectations,
$$
E_\pi(X\mid e>t)=E_\pi\big(g(e)\mid e>t\big)=E_\pi(e\mid e>t)\;\ge\;t,
$$
since `e > t` there. So the equality implies every Total-Trust inequality, trivially.

**The squeeze is the converse — and one bet is not enough.** Fix a single `X` and range `t`: that gives only the *parallel* cuts `{e > t}`, and they do **not** pin `g = id`. With `μ = Unif[0,1]` (the law of `e`), let the novice *amplify* the expert, pivoting at `½`:
$$
g(e_0)=(1+2c)\,e_0-c\quad(c>0),\qquad g(\tfrac12)=\tfrac12,\ \ \text{slope }1+2c>1.
$$
Both cut families hold for every `t` and every `c ≥ 0`:
$$
\int_t^1 g\,de_0-t(1-t)=\tfrac{1-t}{2}\big[(1-t)+2ct\big]\ge0,\qquad
\int_0^t g\,de_0-t^2=-\tfrac{t}{2}\big[t+2c(1-t)\big]\le0.
$$
A novice who systematically **overstates the expert's confidence** thus passes *every* threshold-trust test, both cuts — yet it is not the tower; it never matches the expert, it exaggerates it. Parallel cuts cannot tell `g = id` from `g = (1+2c)·id − c`.

What rules the impostor out is **boundedness biting at the extremes**: a `[0,1]`-bet needs `g ∈ [0,1]`, but `g(0) = −c < 0` and `g(1) = 1+c > 1`. *If* the expert's estimate actually reaches `0` and `1`, then `c = 0` is forced; if `e` stays inside `(0,1)`, the amplifier survives. Pinning `g = id` in general therefore needs the **non-parallel cuts** too — Total Trust on *all* bets `X`, which probe *within* each `E*(X)`-layer. That all-bets statement is DDB's biconvex / convex-hull characterization (Total Trust ⟺ all candidates modestly informed ⟺ Value), proved by hyperplane separation plus the boundedness above. **This is why the squeeze stays prose** — a genuine convex-geometry theorem, not a one-line limit:
$$
\underbrace{\text{soft Total Trust, per }(X,t)}_{\text{kernel-checked inequality}}
\;\xrightarrow[\ \delta\to0,\ \text{all }X,\ \text{both cuts}\ ]{}\;
\underbrace{\text{the tower equality}}_{\text{biconvex characterization}} .
$$

**Where the continuum costs you.** Finite-exact, the witness identity made `Value ⟺ Total Trust` a two-way equality (§2.2). The soft indicator smears each cut, so soft Total Trust is only `≳` at each width `δ`; and sharpening sends `δ→0` inside `E_n`, exchanging a limit with the estimate exactly where `1[E*(X) > t]` is the liar-prone event the inductor refuses to evaluate sharply (that refusal is what *protects* it from paradox). So the kernel-checked frontier is exactly: **`Value ⟺ Total Trust`** in both layers (`value_iff_totalTrust`, `value_iff_totalTrust_asymptotic`); **`Total Trust ⟹ the full tower equality`** is the lone step still prose.

**It is the tower, not Reflection.** What the squeeze pins is `E_π(X | E*(X)) = E*(X)` — the novice reflects the expert's *estimate of `X`*. This is strictly weaker than DDB-**Reflection** `π(· | P = ρ) = ρ`, which conditions on the expert's **entire identity** `ρ`, not its estimate of one bet (Reflection ⟹ tower, never the converse). And the gap is the soft machinery's *purpose*: conditioning on `{E*(X) > t}` is a threshold the expert knows (introspection), while conditioning on `[P = ρ]` is the self-referential liar event ("I get probability `< ½`"). The soft indicator only ever ramps over estimate-thresholds, never over identity, so Total Trust tops out at the tower **and cannot reach Reflection** — exactly right, since Reflection collapses to inconsistency for a modest expert (§5). The ceiling is a feature.

---

## 4. Why a coherent expert is cheap and a frame is dear: a single state, not a frame

The §2.3 asymmetry has one root cause — *what kind of object the expert is.*

**A DDB expert is an information frame.** A credence per world `P_w` ⇒ a *world-dependent* recommendation `S_w`, so the realized return is the **diagonal** `Ŝ(w)=S_w(w)`, and the expert-at-`a` scores it by `E_a(Ŝ)=Σ_v P_a(v)S_v(v)` — which is **not** the max (in the anti-expert frame `E_a(Ŝ)=−1` while `M(a)=.6`). Bridging the `π`-average of the diagonal to the `π`-average of the row-wise maxima is DDB's *hard* direction: a convex reconstruction ("modestly informed") plus Blackwell–Geanakoplos value-of-information.

**A coherent `E*` is a single belief state.** One set of estimates `{m^j}` ⇒ one argmax ⇒ the followed strategy is the *single option* `O^{j*}`, and `E*(Ŝ) = M` by definition (F1). No world-dependent strategy, no diagonal to reconstruct. The novice's uncertainty about `E*` is **logical** (about a definite quantity it hasn't finished computing), not **which-world** uncertainty about which `P_w` holds. The tower is exactly the bridge DDB builds by hand — handed over by no-Dutch-book.

| | DDB | LI (general expert) |
|---|---|---|
| the expert is… | a frame (a credence per world) | a single coherent belief state |
| the recommendation is… | world-dependent `S_w` | one option `O^{j*}` |
| `E_expert(followed strategy)` | not the max (diagonal mixes) | the max, by F1 |
| diagonal→row-wise bridge | reconstructed (convex hull) | free (the tower) |

This is why the natural cross-process experts are **other logical inductors** (or any coherent calibrated estimator): they are single states, so deference to them is cheap; a frame is the expensive object.

---

## 5. Modest but coherent — and why the home is an infinite process

Is a coherent observable expert simply *immodest*, collapsing to the easy DDB corner? No — and the surviving modesty is the point, for cross-process deference as much as for self-trust.

**The modesty that survives is incomplete self-knowledge, not identity-uncertainty.** A coherent inductor-expert knows its own estimates only *approximately and increasingly* (introspection), never to *paradoxical* completeness — completeness would let the diagonal lemma build a liar it cannot settle. So `E*` knows enough to value its own choices (F1, about exogenous options, needs only definite estimates) yet cannot host a self-referential predicate about its own beliefs and stay consistent. (Different from DDB-modesty, which is *identity*-uncertainty — a frame unsure which `P` it is.)

**Finite frames cannot combine modesty with conditional-tower coherence.**

> **Proposition (finite collapse; fiber-indicator core kernel-checked, §10).** On a *finite* frame, if the soft conditional tower holds for all bounded `X`, the expert is immodest on the novice's support.

*Why.* Finitely many values `{E_w(X)}` ⇒ a **spectral gap**; for `δ` below it the soft indicator equals the hard one, the threshold events generate the expert `σ`-algebra, and the hypothesis collapses to `E(X)=E_π(X|𝒫)` — immodesty. So on a finite frame the very property making Value cheap *forces immodesty*. A reasoner at once **modest** and **conditional-tower-coherent** needs the expert's estimates to take continuum-many, gapless values — an **infinite, self-referential** process. Logical inductors are exactly that: a continuum of completions, dense future estimates, and a permanent gap between the *hard* conditional tower (the liar keeps it false) and the *soft* one (which holds). So whether the expert is your future self or a different AI, **clean modest deference lives only between infinite-frame processes** — of which inductors are the concrete inhabitants.

---

## 6. The future self as the canonical expert

The original self-trust reading is the special case `E*(X) := E_{f(n)}(X)`. It is distinguished because there *every* deference hypothesis of §0.2 is an **LI theorem**, not an assumption:

| hypothesis on `E*` | self-instance theorem |
|---|---|
| observable | the day-`f(n)` market is market-generable from the novice's own prices |
| coherent (single state) | LI limit-coherence; the inductor is one belief state |
| introspective | Introspection — `epr` (4.11.3), `er` (4.11.4) |
| `Mart(N→E*)` (tower) | Expected Future Expectations — `cee` (4.12.1) |
| `ccee(N→E*)` (conditional tower) | No Expected Net Update under Conditionals — `ccee` (4.12.3) |
| Total Trust (consequence, §3.1) | Self-Trust — `st` (4.12.4), the propositional case |

So **self-trust is the one case where you are guaranteed to tower over the expert** — the criterion hands you `cee`/`ccee` for free. For a *distinct* process the same statements are assumptions about the pair (§11).

**The future self is the maximal observable expert (interpretation).** Anything the novice can observe of an external expert, its own day-`f(n)` self has already incorporated; the future self is a Blackwell **refinement** of any observable expert, so by Blackwell–Geanakoplos monotonicity deferring to it dominates deferring to that expert. Thus "trust your future self" is "defer to the join of all experts you can see" — and choosing it in v1–v3 was not a loss of generality but the maximal instance. Studying *humans trusting AI* is studying the cases where the expert is **not** your own future self and the tower must be *earned*, not assumed.

---

## 7. Weatherson's infinite failures are LI's two scope conditions

Weatherson breaks DDB's Thm 2.2 both ways on infinite frames; each break exploits exactly one thing LI excludes for an independent reason.

- **Coin (Total Trust without Value): unbounded utility.** Options with `2^i` payoffs make the recommended strategy's diagonal `0` while every option has positive expectation. *LI excludes it:* expectations are defined only for **bounded** LUV-combinations, and finite-risk traders — boundedness *is* uniform integrability, exactly what the §2.1 steps need.
- **Bentham (Value without Total Trust): hard conditioning on a null tail.** Total Trust fails at a single measure-zero world. *LI excludes it:* the tower quantifies over **finite** stages with `n→∞` and conditions only **softly** (`Ind_δ`, `δ→0`), never on a hard null event.

| failure | direction lost | driver | LI's excluding feature |
|---|---|---|---|
| **Coin** | Total Trust ⇏ Value | unbounded utility | bounded LUVs / finite-risk traders |
| **Bentham** | Value ⇏ Total Trust | null-tail hard conditioning | finite stages + soft `Ind_δ` |

---

## 8. The realizability payoff

The finite story is **realizable** (the novice's candidate set literally contains the expert) — cognitively fake for the cases we care about. LI earns the equivalence **without** realizability, and this matters *more* cross-process than for self-trust: the expert is genuinely a *separate, possibly larger* process, not realizable within the novice (the novice provably cannot contain a full model of it — that way lies the liar), yet deference-as-value still goes through, approximately and in a timely manner. A theorem about deference that survives the removal of realizability — in the one setting where a finite mind reasons soundly about something bigger than itself — is the reassurance the finite proof could not give.

---

## 9. Caveats and the load-bearing idealization

- **Observability is structural.** If the novice cannot generate `E*` from its prices, the selection and the §2.2 witness cannot be stated. The theory only speaks about experts the novice can *watch*.
- **Boundedness** is required (else Coin, §7).
- **Soft vs. hard.** For *Value* the hard `argmax` strategy is the faithful object and §2.1 handles it directly. Softening earns its keep for **Total Trust** (hard conditioning on a future-estimate event is the liar) and the continuum witness.
- **The fixed-option idealization (the one that bites).** The reading "the novice would rather defer than commit to `O^i`" identifies `E_n(O^i)` with *the payoff of committing*. The proof is choice-agnostic — the inequality holds for any e.c. menu, self-referential ones included — so this assumption hides in the *interpretation*: option values are treated as fixed w.r.t. the choice (the Savage framing). Where payoffs depend on the decision process (deference-punishing / Newcomblike — the 5-and-10 / Troll-Bridge / EDT-vs-CDT cluster), `E_n(O^i)` is no longer the value of committing, and endorsement and deference diverge. The clean theorem lives in the choice-independent, causal-surrogate, updateful regime — the same "agent outside the environment" idealization DDB and Weatherson assume.

---

## 10. Machine-check

**Python (`deference-in-logical-induction-check.py`, sympy, exact rationals — 18/18):** the keystone decomposition identity (all frames), the softmax/Gibbs bound, DDB Figs. 2–3 exactly, conditional-tower ⇒ Value on random prior frames, the §5 finite-collapse (0 frames both conditional-tower and modest over 20 000 trials), and the LI regime in miniature.

**Lean 4.27.0 + Mathlib (`lean-deference/LeanDeference.lean`), kernel-checked, `sorry`-free, `#print axioms = [propext, Classical.choice, Quot.sound]`.** **The development is already stated for a general expert** — `value_of_argmax` takes an arbitrary expert kernel `P`, and the asymptotic theorems take the tower/`expprovind` facts as *named hypotheses*, never assuming the expert is the future self. So the kernel-checked theorems **are** the cross-process theorems of this note; the future self merely instantiates the hypotheses (§6). Seven parts:

- **(a)** `DeferenceAsymp.value_asymptotic` — the softmax/`ccee` composition.
- **(b)** `Deference.*` — the finite exact backbone: `decomposition` (arbitrary `CommRing`, all finite `W,J`), `value_of_CM` (Value from conditional- + unconditional-tower defects = 0 + argmax dominance).
- **(c)** `DeferenceExtra.*` — `softmax_lower_bound` (proved from `Real.add_one_le_exp`), `CM_implies_immodest` (the §5 fiber-indicator core).
- **(d)** `DeferenceArgmax.*` — the §2.1 route: `value_of_argmax` (exact; `jstar` an *arbitrary* maximizer ⇒ tie-break-independence is checked; uses only the tower-identities + dominance), `value_argmax_asymptotic` (the chain via `cee`/tower + `expprovind` only), `payoff_gap_le_l1`, `value_argmax_via_softmax`.
- **(e)** `DeferenceConverse.*` — the converse (§2.2): `witness_identity`, `value_iff_totalTrust`, with the anti-expert frame as a non-vacuity witness (`stationary` yet `TT_negative`/`value_fails`); and `DeferenceFold.*` (the §3 folding).
- **(f)** `DeferenceConverseAsymp.*` — the asymptotic converse, now a two-sided **iff**: `totalTrust_of_value_asymptotic` (`Value ⟹ Total Trust`) *and* `value_of_totalTrust_asymptotic` (`Total Trust ⟹ Value`), packaged as `value_iff_totalTrust_asymptotic` — the timely-manner `Value ⟺ Total Trust`, both arrows; plus `totalTrust_asymptotic` (the §3.1 `ccee ⟹ Total Trust` bridge). The continuum's lone remaining one-way step is **Total Trust ⟹ the full tower equality** (the soft⇒hard squeeze, §5), *not* `Value ⟺ Total Trust`.
- **(g)** `DeferenceTrader.*` — the §2.4 direct-trader (no-Dutch-book) view, exact arithmetic core: `round_profit_ge_gap` (the two-leg round nets *at least* the Value gap, because the unwind `ef jstar − ef i ≥ 0` by the expert's argmax) and `gap_pos_imp_profit_pos` (a positive gap ⇒ positive guaranteed profit). The exploit itself — unbounded profit, bounded risk — is the trusted criterion, not formalized.

**Not checked** (the trusted layer): that the genuine LI theorems hold and force the defects to vanish; the `≈ₙ` bookkeeping inside the real LUV–market machinery; the soft⇒hard spectral-gap step of §5. What is verified is the algebra, the finite core, and the *valid composition* of the (named) LI theorems into Value, its converse, and Total Trust — for a general expert. **In the cross-process case, `Mart(N→E*)` is exactly one of those named hypotheses** — so the Lean already proves "if the novice towers over the expert, then it Values it," whoever the expert is.

---

## 11. What is open

- **The cross-process characterization (the real prize).** The theorems are conditional on `Mart(N→E*)` (and `ccee`). For the future self it is `cee`, free. **When does one logical inductor tower over a *different* one** — same theory? a richer theory? a larger trader class? a faster schedule? — is *not* free and is the LI analog of DDB's "`π ∈ CH(C_π)` and every candidate modestly informed." This is the question behind "when should a human (or AI) trust a given other AI," and it sits in the **tiling / Vingean-reflection** register rather than self-trust.
- **Asymmetric trust classes.** Observability is structural, not cosmetic: the theory speaks only of experts the novice can generate from its own prices. Characterizing the observable–bounded experts a given novice towers over is the precise version of "which other minds can this mind soundly defer to."
- **Lean-verify the soft⇒hard spectral-gap step** of §5 (its fiber-indicator core is done; the reduction needs the infinite frame).
- **Local (question-relative) deference** (DDB §5): deferring to `E*` about a restricted class of LUVs. The tower is already "local" in the LUV, so this may be the cleanest case, and would settle DDB's open conjecture that local Total Trust = local Value.
- **Quantitative rates.** With explicit schedules, a finite-horizon "how much value is at stake" bound, closer to the tiling use.

---

## References

- K. Dorst, B. A. Levinstein, B. Salow, B. E. Husic, B. Fitelson, **"Deference Done Better,"** *Philosophical Perspectives* 35 (2021). — Total Trust ⇔ Value (**Thm 2.2**); geometric characterization (**4.1, 5.1**); "modestly informed"; Appendix B (**Lemma 7.1** easy direction; convex-hull reconstruction; **7.5** Weak-Value⇒Value).
- B. Weatherson, **"Deference and Infinite Frames,"** *Australasian Journal of Logic* (2025). — Coin and Bentham; Geanakoplos non-extension; dual-deference normal-distribution example. (See transcription notes for the transitivity-direction and payoff-constant typos.)
- S. Garrabrant, T. Benson-Tilsen, A. Critch, N. Soares, J. Taylor, **"Logical Induction"** (2016), §4. — Linearity (**4.8.4** `loe`), Expectation Provability Induction (**4.8.10** `expprovind`); Introspection (**4.11.3** `epr`, **4.11.4** `er`); Self-Trust — Expected Future Expectations (**4.12.1** `cee`), No Expected Net Update under Conditionals (**4.12.3** `ccee`), Self-Trust (**4.12.4** `st`); the criterion and construction (§§3, 5).
- J. Geanakoplos, "Game Theory Without Partitions" ([1989] 2021); D. Blackwell, "Equivalent Comparisons of Experiments" (1953). — reflexive/transitive/nested ⇒ value of information ≥ 0, the engine behind DDB's frame-based hard direction.

