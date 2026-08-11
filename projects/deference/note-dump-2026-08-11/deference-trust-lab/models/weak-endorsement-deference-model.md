# A toy formal model: weak endorsement ⇒ weak deference, and the Gödel wall

*Thread: "weak endorsement ⇒ weak deference; self-reference / Gödel." Develops Idea 1 (the
weakening dictionary) + Idea 2 (the diagonal no-go) of `findings/weak-endorsement-deference-ideate.md`
into a precise toy model. Companion artifacts: a hand-checkable Python micro-example
(`models/weak-endorsement-deference-check.py`, runs, no deps beyond `fractions`) and a candidate
Lean file (`lean/weak-endorsement-deference.lean`, **UNCHECKED — for the Lean-verify agent**).*

Every claim is flagged **PROVED** (machine/paper-checked) / **SKETCHED** (LI-paper rigor) /
**CONJECTURE** / **INTERPRETATION**. Cross-refs: v2 §0.3 (theorem statements), §2/§3 (Value LI
form + proof), §5.2 (finite collapse), §10 (external experts); LI paper §4.12 (`thm:cee/ccee/st`,
the liar eq. at lines 2117–2128).

---

## 0. The two notions, stated once

Fix a logical inductor `(ℙ_n)` over a theory `Γ`, present operator `𝔼_n`, deferral function `f`
(`f(n)>n`), and an **expert** estimate operator `E_exp` that is **novice-observable** (its outputs
are `ℙ`-generable from the novice — for the self-trust case `E_exp = 𝔼_{f(n)}`). All relations are
`≂ₙ / ≳ₙ` (converge-together / liminf-≥, v2 §0.2). "Weight" always means a market-generable
`w_n ∈ [0,1]`.

**ENDORSEMENT (two flavours), as conditional-martingale schemata.** For a `[0,1]`-LUV `X`, a
threshold `t`, and the conditioning weight `w`:

| name | schema | flavour |
|---|---|---|
| **HARD endorsement** at `t` | `𝔼_n(X · 𝟙[E_exp(X)=t]) ≂ₙ t · 𝔼_n(𝟙[E_exp(X)=t])` | two-sided `=`, hard `𝟙` |
| **WEAK endorsement** | `𝔼_n(X · Ind_δ(E_exp(X)>t)) ≳ₙ t · 𝔼_n(Ind_δ(E_exp(X)>t))`, all `δ↓0, t` | one-sided `≳`, soft `Ind_δ` |

WEAK endorsement is exactly the **LUV lift of Self-Trust** (`thm:st`, 4.12.4): take `X = 𝟙(φ)`,
`E_exp = ℙ_{f(n)}` and it *is* `thm:st`; for general `X` it is `thm:ccee` (4.12.3) used with the
soft weight `w = Ind_δ(E_exp(X)>t)` (v2 §2, "Total Trust (LI form)").

**DEFERENCE (two flavours), as decision-handover.** Menu `𝒪_n = {O^1_n,…,O^k_n}` of bounded
`[0,1]`-LUV bets; selection weights `α^j_n`; strategy return `Ŝ_n := Σ_j α^j_n O^j_n` (v2 §2):

| name | schema | selection |
|---|---|---|
| **HARD deference** | `𝔼_n(Ŝ_n) ≳ₙ 𝔼_n(O^i_n)` with `α^j = 𝟙[j = argmax_j E_exp(O^j)]` | hard argmax |
| **WEAK deference (= Value, LI form)** | `𝔼_n(Ŝ_n) ≳ₙ 𝔼_n(O^i_n)` with `α^j = softmax(E_exp(O^·)/δ_n)`, `δ_n↓0` | soft softmax |

"Weak deference" is **Value (LI form)** of v2 §2. (The conclusion form is the same inequality; the
*difference* is hard-argmax vs soft-softmax selection. Soft selection is exactly what `thm:ccee`'s
soft weights license; hard argmax is the `δ→0` limit and is paradox-/tie-prone, §3 below.)

---

## 1. The central theorem schema

> ### Theorem schema (weak-endorsement ⇒ weak-deference). **SKETCHED** (LI-paper rigor; finite algebraic core **PROVED**, see §5/§6).
>
> Let the novice be any logical inductor `𝔼_n`. Let an expert supply estimates `E_exp(O^j_n)` that
> are (i) **novice-observable** (market-generable, so the softmax weights `α^j_n` are legal inputs
> to `thm:ccee`) and (ii) **uniformly bounded** (its valuations are `[0,1]`-LUVs). **If** the
> novice–expert pair satisfies **WEAK endorsement** in the LUV form
> $$
> \text{(WE)}\qquad \mathbb E_n\big(\ulcorner X_n\, w_n\urcorner\big)\ \eqsim_n\ \mathbb E_n\big(\ulcorner E_{\mathrm{exp}}(X_n)\, w_n\urcorner\big)\quad\text{for every market-generable }w_n\in[0,1],
> $$
> **then WEAK deference (Value, LI form) holds:** `𝔼_n(Ŝ_n) ≳ₙ 𝔼_n(O^i_n)` for the softmax
> strategy, for each fixed `i`. The easy converse (Value ⇒ WE-on-thresholds) uses only the novice's
> own coherence (two-option witness, v2 §1.1), so on the observable–bounded class the two are
> **equivalent**.

Note (WE) is precisely **`thm:ccee` directed at `E_exp`**; v2's §10 isolates it as the unique
expert-specific premise (its soft-conditioning specialization `w=Ind_δ(E_exp(X)>t)` is the
threshold form in §0). I keep the LUV form (WE) as the hypothesis because it is what the proof
literally uses; the threshold/soft-indicator form is the human-readable face.

### 1.1 The discharge ledger — exactly which LI theorems do which work

This is the heart of the model: *the schema is conditional on (WE), and every other step is a
named LI theorem about the novice alone.* The five-line proof (v2 §3) audited line-by-line:

| line | claim | engine | who must supply it |
|---|---|---|---|
| 2 | `𝔼_n(Ŝ_n) ≂ₙ Σ_j 𝔼_n(α^j O^j)` | **Linearity 4.8.4** (`thm:loe`) | **novice's own coherence — FREE** |
| 3 | `Σ_j 𝔼_n(α^j O^j) ≂ₙ Σ_j 𝔼_n(α^j E_exp(O^j))` | **`thm:ccee` = (WE)** at `w=α^j` | **ASSUMED** (the one premise) |
| 4 | `Σ_j 𝔼_n(α^j E_exp(O^j)) ≂ₙ 𝔼_n(Σ_j α^j E_exp(O^j))` | **Linearity back 4.8.4** | **novice's own — FREE** |
| 5 | `𝔼_n(Σ_j α^j E_exp(O^j)) ≳ₙ 𝔼_n(E_exp(O^i)) − δ_n log k` | **softmax gap** (algebraic, holds in *every* consistent world) **+ Provability Induction 4.8.10** (`thm:expprovind`) | **novice's own — FREE** (the softmax gap is a real-number identity in the prices) |
| 6 | `𝔼_n(E_exp(O^i)) ≂ₙ 𝔼_n(O^i)` | **`thm:cee` (4.12.1)** = (WE) at `w≡1` | **ASSUMED**, but it is line 3's premise at constant weight |

**So the schema is discharged by:** Linearity (4.8.4) ×2, Provability Induction (4.8.10), the
softmax Gibbs bound (now also `DeferenceExtra.softmax_lower_bound`, confirmed Lean) — all *free,
about the novice only* — plus the **single** cross-agent premise (WE) = `thm:ccee` toward `E_exp`
(line 6 being its `w≡1` shadow). For the **self-trust** case `E_exp = 𝔼_{f(n)}`, (WE) is itself a
theorem (`thm:ccee` is *about* the future self), so the whole schema is **unconditional**: every
logical inductor weakly-defers to its own future self. For an **external** expert, (WE) is *not*
free (v2 §10.4) and is the thing to be earned (Eisenstat merge / good feedback — orientation Q4/Q5).

**Status:** the *composition* of the five LI results into Value is machine-checked
(`DeferenceAsymp.value_asymptotic`, confirmed Lean, §9 of v2); the genuine LI theorems 4.8.4 /
4.12.3 / 4.12.1 / 4.8.10 are trusted from the paper, not re-derived. So the schema is **SKETCHED**
at the LI-paper level, with its algebra/composition **PROVED**.

---

## 2. The impossibility: hard endorsement + hard deference is jointly unsatisfiable (the Gödel wall)

The schema above is the *weak* arm. The model's other half is the **no-go** that bounds the
dictionary: strengthen "weak" to "hard" on both sides and a single Gödel/Löb sentence detonates it.

### 2.1 The liar / Löb sentence

By the diagonal lemma form a sequence of self-referential sentences (LI paper, eq. before 2118):
$$
\chi_n \ :=\ \ulcorner \mathbb P_{f(n)}(\chi_n) < \tfrac12\urcorner
\qquad\text{(``my future self will give me probability }<\tfrac12\text{'')}.
$$
This is the probabilistic liar / unexpected-hanging sentence. Set `X = 𝟙(χ_n)`, threshold
`t = 1/2`, conditioning event `[E_exp(X) ≥ 1/2] = [ℙ_{f(n)}(χ_n) ≥ 1/2]`, hard weight
`w = 𝟙[ℙ_{f(n)}(χ_n) ≥ 1/2]`.

> ### No-Go (diagonal). **SKETCHED** (it is LI paper lines 2117–2128 reorganized as an impossibility).
>
> **HARD endorsement** at `t=1/2` on `χ_n` is contradictory. Proof. The conjunction
> `χ_n ∧ (ℙ_{f(n)}(χ_n) ≥ 1/2)` is **disprovable** (it asserts both `<1/2` and `≥1/2`), so by
> `thm:perkno` (4.8) its probability vanishes:
> $$
> \text{(★)}\qquad \mathbb E_n\big(\ulcorner \mathbf 1(\chi_n)\cdot w\urcorner\big)\ =\ \mathbb P_n\big(\chi_n\wedge \mathbb P_{f(n)}(\chi_n)\ge\tfrac12\big)\ \eqsim_n\ 0.
> $$
> HARD endorsement demands `𝔼_n(𝟙(χ_n)·w) ≂ₙ t·𝔼_n(w) = (1/2)·𝔼_n(w)`. With (★) this forces
> `𝔼_n(w) ≂ₙ 0` — the present self is *certain* its future self never reaches `≥1/2` on `χ_n`. But
> by **recurring-unbiasedness** (`thm:recurringunbiasedness`, 4.5.10) the future prices on the liar
> oscillate across `1/2` infinitely often, so `[ℙ_{f(n)}(χ_n)≥1/2]` has *non-vanishing* present
> credence: `𝔼_n(w) ≳ₙ c > 0`. Contradiction. ∎

Read decision-theoretically: HARD endorsement is HARD deference's witness condition (the two-option
construction, v2 §1.1, builds a menu whose recommended-strategy value tracks exactly the
conditional `𝔼_n(X | E_exp(X)≥t)`). So the liar makes **hard endorsement + hard deference jointly
unsatisfiable** — there is no coherent present credence completing both. *This is the precise sense
of "perfect alignment is, in a certain sense, impossible" (AGENDA "Representational Issues"): the
value-pinning, exhaustively-introspective form of trust has a diagonal counterexample.*

### 2.2 The soft version IS satisfiable

Replace the hard `w` by the Lipschitz ramp `w_soft = Ind_δ(ℙ_{f(n)}(χ_n) > p)` and `=` by `≳`.
Now Self-Trust (`thm:st`) *holds* on `χ_n`: conditioning *softly*, the inductor answers `≈ 1/2`
(LI paper line 2130, "extremely close to 0.5 ⇒ roughly 0.5"), and
$$
\mathbb E_n\big(\ulcorner\mathbf 1(\chi_n)\,w_{\mathrm{soft}}\urcorner\big)\ \gtrsim_n\ p\cdot \mathbb E_n\big(\ulcorner w_{\mathrm{soft}}\urcorner\big)
$$
is consistent (for `p ≤ 1/2`). **No contradiction.** The mechanism: the hard indicator's
discontinuity at the threshold *has no clearing market price* on a self-referential sentence
(§0.3-the liar has no fixed point for a hard buy-low/sell-high trader); the ramp restores a fixed
point. The *one-sidedness* `≳` is what lets the answer sit *at* `1/2` rather than be pinned to a
contradictory exact value: `≥ p` permits `1/2`, whereas `= p` with the disprovable conjunction
forbids it.

### 2.3 The one-sentence mechanism (INTERPRETATION)

> Going from **`=`** to **`≥`** trades *pinning the exact value* (which Gödel forbids on the
> diagonal — the band `{E_exp(X)=t}` is exactly where the liar lives and has no clearing price) for
> *pinning a lower bound* (which Gödel permits, because `[E_exp(X)>t]` is **directed** — one-sided
> learning moves credence monotonically and the soft ramp has a fixed point). DDB *noticed* this
> informally ("the asymmetric 'at least degree t' can only favour `q` further"); LI **proves** it,
> with `Ind_δ` doing the defusing and `χ_n` the live witness.

So the dictionary is: **HARD/`=`/Reflection survives only off the diagonal (finite, immodest, S5,
realizable); WEAK/`≥`/Self-Trust survives on it (infinite, modest, S4, non-realizable) — and the
weak arm still implies deference** (§1), while the hard arm is *vacuous on any self-modeling
reasoner* (no inhabitant). That is the content of "weak-reflection : Reflection :: weak-deference :
Value."

---

## 3. Why the *finite-frame* shadow says the same thing (the collapse, PROVED core)

The liar argument is intrinsically infinite (self-reference). Its **finite shadow** is the
collapse of v2 §5.2, which needs no self-reference and is fully algebraic:

> **Finite collapse.** **PROVED** (finite algebraic core: `DeferenceExtra.CM_implies_immodest`,
> confirmed Lean; the soft⇒hard spectral-gap reduction is prose). On a *finite* frame, if HARD
> endorsement (the hard conditional-martingale identity `E_w(X)=E_π(X∣\text{fiber }w)` for all `X`)
> holds at `w∈W_π`, then the expert is **immodest** there: `P_w(P=P_w)=1`.

So on finite frames HARD endorsement is available *only* in the S5/partitional/immodest/realizable
corner — exactly where Reflection lives and modesty is excluded. A *modest* finite reasoner
**violates** hard endorsement (micro-example Check 3 below). The two no-gos are the same wall seen
twice: **finitely**, hard endorsement ⇒ immodesty (so modest+hard is empty); **infinitely** (with
self-reference), hard endorsement ⇒ contradiction on the liar (so any self-modeler+hard is empty).
The escape in both cases is the *same* relaxation: soft, one-sided `≥`, which is compatible with
modesty (finite shadow) and with self-reference (the liar), and which still yields deference (§1).

---

## 4. The dictionary, as a loss/gain table (INTERPRETATION, the deliverable spine)

Rung-for-rung correspondence (DDB ladder ↔ LI ladder; full version in
`findings/weak-endorsement-deference-ideate.md` §0):

| feature | HARD (Reflection / `=`) | WEAK (Self-Trust / `≥`) |
|---|---|---|
| two-sidedness | `=t` pins both directions | only `≳t`; the band `{E=t}` is **never** pinned (liar: future `=0.5` ⇒ now `0`) — **LOST** |
| self-reference | inconsistent (liar, §2.1) — **LOST** | survives; `Ind_δ` smooths the no-clearing-price discontinuity — **GAINED** |
| modesty | forces immodesty / S5 (§3) — **LOST** | compatible with modesty / S4 non-Euclidean — **GAINED** |
| realizability | needs expert ∈ novice's finite candidate set — **LOST** | expert may be strictly *larger* than novice (v2 §7) — **GAINED** |
| decision content | Reflection ⇏ Value under modesty (DDB Fig.3) | WE ⇔ Value (§1) — **GAINED** |
| conditionable events | any (hard σ-algebra) | only **directed** threshold events `[E(X)>t]` — **restricted** |

The single non-free premise (for external experts) is the *top* row "weak endorsement holds at
all" = cross-agent (WE); every "GAINED" row uses only the novice's own coherence + observability
(v2 §10). This *localizes* the trust burden to one premise — the safety-relevant fact.

---

## 5. Worked micro-example (hand-checkable; Python `models/weak-endorsement-deference-check.py`)

All numbers exact (`fractions.Fraction`); the script **runs and prints CONTRADICTION/CONSISTENT
verdicts**. Three checks, each a small enough computation to verify by hand.

**Check 1 — Gödel/liar, HARD endorsement UNSATISFIABLE.** Inputs: `t=1/2`;
`E_now(𝟙(χ)·w)=0` (disprovable conjunction, ★). Hard endorsement demands `0 = t·E_now(w)`, so for
**any** `E_now(w)=q>0` we get `0 = q/2 ≠ 0`. Table (script output):

```
q=1/10: demands 1/20, actual 0 -> CONTRADICTION
q=1/3 : demands 1/6 , actual 0 -> CONTRADICTION
q=1/2 : demands 1/4 , actual 0 -> CONTRADICTION
q=9/10: demands 9/20, actual 0 -> CONTRADICTION
```
The only escape `q=0` is forbidden by the liar's oscillation (`≥1/2` infinitely often). **Hard
endorsement + liar: jointly unsatisfiable.** (This is precisely the Lean lemma (A), §6.)

**Check 2 — SOFT version satisfiable.** Ramp `Ind_δ(x>p)` at the cluster value `x=1/2`, `p=1/2−δ/2`,
LI conditional value `c=1/2`. For `δ∈{1/4,1/8,1/100}` the one-sided
`E_now(𝟙(χ)·w_soft)=c·w ≥ p·w=E_now(w_soft)·p` holds (`0.25 ≥ 0.1875, 0.2188, 0.2475`). **Soft +
liar: satisfiable**, witness `≈1/2`. (Lean lemma (B).)

**Check 3 — finite collapse on a modest frame (DDB Fig. 2).** `π=(½,½)`, `P_a=(.2,.8)`,
`P_b=(.8,.2)` — modest (`P_a(a)=P_b(b)=1/5≠1`). The hard conditional-martingale identity at `X=𝟙[fiber w]`
demands `E_w(𝟙[w])=E_π(𝟙[w]∣\text{fiber})`: LHS `=P_w(w)=1/5`, RHS `=1` (novice conditioned on `{w}`
is certain). `1/5 ≠ 1` → **VIOLATED**. So this modest frame cannot satisfy hard endorsement; only
the soft form is available. (This is the finite shadow `CM_implies_immodest`, confirmed Lean.)

These three are the model in miniature: the *same* hard schema is contradictory on the liar
(Check 1), unavailable under finite modesty (Check 3), while the soft schema is consistent on both
(Check 2) and (by §1) still implies deference.

---

## 6. The Lean candidate — `lean/weak-endorsement-deference.lean` (UNCHECKED)

Captures the **algebraic core of the §2 impossibility** (Check 1) — distinct from the existing
`weak-endorsement.lean`, which captured the §3 *finite-collapse* core (Check 3). Two/four lemmas:

- **(A) `hard_endorsement_liar_unsat`** — plain English: *"hard endorsement + the liar are jointly
  unsatisfiable."* Hypotheses (all faithful inputs, none smuggling the conclusion):
  `ht : 0 < t`; `hw : 0 < Ew` (oscillation, `E_now(w)>0`); `hdisprov : Exw = 0` (the disprovable
  conjunction ★); `hendorse : Exw = t * Ew` (HARD two-sided endorsement). Conclusion: `False`.
  The proof derives `t·Ew = 0` from the two equations and clashes with `0 < t·Ew` — **so it
  genuinely uses `hw`**, which is what makes the impossibility non-vacuous (drop `hw`, allowing
  `Ew=0`, and the system is consistent: `0 = t·0`).
- **(B) `soft_endorsement_liar_sat`** + two witnesses — plain English: *"the one-sided soft
  constraint has a model on the same data"* (`p ≤ c, 0 ≤ wsoft ⟹ c·wsoft ≥ p·wsoft`). With
  `c=1/2` (LI liar value), this exhibits SOFT satisfiability — proving (A)'s impossibility is a
  property of `=`, not of the liar. Rules out the "(A)'s hypotheses were vacuously contradictory"
  failure mode.

**Fidelity audit (the load-bearing concern).** The Lean is the *finite, exact, real-valued
skeleton* of the clash; it does **NOT**:
- prove `Exw = 0` from the diagonal lemma / `perkno` (that is the INPUT `hdisprov`, flagged);
- prove `0 < Ew` from recurring-unbiasedness (INPUT `hw`, flagged);
- contain any LUVs, market/trader, `≂ₙ`, or the diagonal lemma.
What it **does** verify is that *given* the two liar facts (★ and oscillation), HARD endorsement is
algebraically impossible while SOFT endorsement is consistent — i.e. the `=`-vs-`≥` pivot, in
arithmetic. The single-band (non-universal) form of (A) is the *conservative* choice for an
impossibility: one instance of the liar already refutes hard endorsement, so universal
quantification would only weaken the result's honesty (it would make the hypothesis stronger). The
quantifier on (B) over `p,c,wsoft` matches "for the soft constraint to be satisfiable it suffices
that the conditional value clears the threshold."

**Status of the Lean: UNCHECKED.** Targeted imports (`Algebra.Order.Field.Basic`,
`Tactic.Linarith`, `Tactic.Positivity` — all `.olean`-confirmed present in the prebuilt Mathlib).
Proofs use `nlinarith [mul_pos ht hw]` (A), `mul_le_mul_of_nonneg_right` (B), `norm_num`
(witnesses) — all standard. Expected axioms: `[propext, Classical.choice, Quot.sound]`, no
`sorryAx`. **The Lean-verify agent must confirm this.** If `nlinarith`/the lemma name drifts, the
math is a two-line clash (`t·Ew=0` vs `t·Ew>0`) and trivially re-provable.

---

## 7. What is PROVED / SKETCHED / CONJECTURE / open

| claim | status |
|---|---|
| §1 schema *composition* (weak endorsement ⇒ Value, given the 5 LI theorems) | **PROVED** (`value_asymptotic`, confirmed Lean) |
| §1 schema as an LI fact (with 4.8.4/4.12.3/4.12.1/4.8.10 trusted) | **SKETCHED** (LI-paper rigor, v2 §3) |
| §1 self-trust case is *unconditional* (every inductor weakly-defers to its future self) | **SKETCHED** (because (WE) = `thm:ccee` is a theorem there) |
| §2 No-Go: HARD endorsement + liar ⇒ contradiction | **SKETCHED** (= LI paper lines 2117–2128 as impossibility); algebraic core **candidate-Lean (UNCHECKED)** |
| §2.2 SOFT version satisfiable | **SKETCHED** (= `thm:st` on the liar); algebraic contrast **candidate-Lean (UNCHECKED)** |
| §3 finite collapse: HARD endorsement ⇒ immodesty (finite) | **PROVED** core (`CM_implies_immodest`); soft⇒hard step prose |
| §4 loss/gain dictionary | **INTERPRETATION** |
| Idea-2 "maximality" (soft one-sided Self-Trust is the *strongest* diagonal-surviving schema) | **CONJECTURE** (needs a partial order on schemata; the gap is incomparable survivors, e.g. soft two-sided on a δ-band excluding the diagonal) |
| (WE) for a *distinct* inductor (not self) — its characterization | **OPEN** (v2 §10.4; orientation Q5; the Eisenstat-merge prerequisite) |

### Central claim and its status

> **Central claim (SKETCHED; finite algebraic core PROVED, candidate-Lean for the new liar nugget):**
> In the logical-induction setting, **weak endorsement (the soft, one-sided LUV form of Self-Trust,
> `thm:ccee`/`thm:st`) implies weak deference (Value, LI form)** — discharged by Linearity (4.8.4),
> Provability Induction (4.8.10) and the softmax bound (all free, novice-only) plus the *single*
> cross-agent premise (WE); for the self-trust case (WE) is itself a theorem, so the implication is
> unconditional. Meanwhile **hard endorsement + hard deference is jointly *unsatisfiable*** on the
> probabilistic liar `χ_n="ℙ_{f(n)}(χ_n)<½"` (hard-conditioning on `[ℙ_{f(n)}(χ_n)≥½]` gives 0, not
> ½), with the *same* relaxation — soft, one-sided `≥` — restoring satisfiability and still
> yielding deference. The `=`→`≥` weakening is exactly the Gödel-survival mechanism.

### Proof skeleton + named gaps (for the SKETCHED parts)

- **Forward schema (§1):** the five-line v2 §3 chain, with line 3 = (WE). *Gap:* the genuine LI
  theorems 4.8.4/4.12.3/4.12.1/4.8.10 and the `≂ₙ`-bookkeeping linking the asymptotic layer to the
  finite core are trusted from the paper, not formalized (same boundary as v2 §9). The *external*-
  expert case additionally assumes (WE) toward `E_exp`, whose characterization is **OPEN**.
- **No-Go (§2):** disprovability of `χ_n ∧ (ℙ_{f(n)}(χ_n)≥½)` ⇒ (★) via `perkno`; hard endorsement
  + (★) ⇒ `E_now(w)=0`; oscillation (`recurringunbiasedness`) ⇒ `E_now(w)>0`. *Gap:* the two LI
  inputs (★ and oscillation) are paper facts taken as hypotheses in the Lean; the diagonal-lemma
  construction of `χ_n` is not formalized.
- **Maximality (CONJECTURE):** *Gap:* no partial order on threshold-conditional schemata is fixed,
  so "strongest surviving" is not yet well-posed; plausibly *incomparable* maxima exist.
