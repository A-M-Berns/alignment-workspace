# Lean-audit, stage 1 — MAP of `lean-deference/LeanDeference.lean`

*Per-declaration correspondence between the kernel-checked Lean and the informal claims of
`deference-in-logical-induction-v2.md`. This is a **map**, not a re-verification: the build is
already established `sorry`-free with axioms `[propext, Classical.choice, Quot.sound]` (v2 §9; I did
NOT recompile). For each declaration: (1) the **exact Lean statement** with hypotheses + conclusion
in plain words, (2) the **precise informal claim** from the v2 doc it is meant to capture, (3) a
**fidelity flag** and any **non-obvious-mapping** note. Flags: PROVED = kernel-checked by the
existing build; the fidelity verdict (faithful / faithful-partial / weaker-constant) is my
INTERPRETATION of the Lean↔prose correspondence.*

File structure: three namespaces.
- `Deference` — finite **exact** algebraic backbone (defects taken as literally `0`).
- `DeferenceAsymp` — the honest §3 asymptotic chain (`≂ₙ`/`≳ₙ` modeled as real-sequence limits; the
  five LI theorems enter as **named hypotheses**, not proved).
- `DeferenceExtra` — two supporting facts now **proved** (not assumed): the softmax bound and the
  §5.2 immodesty core.

The line `import Mathlib` at the top is why this file is heavy to compile; the audit treats the
build as given.

---

## Quick index

| # | Lean decl | informal source | fidelity | mapping obvious? |
|---|---|---|---|---|
| 1 | `Deference.decomposition` | v2 §9 keystone identity; sympy check **A** | faithful & strong (universal) | yes |
| 2 | `Deference.value_of_defects` | §9 "the three terms vanish ⇒ Value" (δ=0 shadow) | faithful | yes |
| 3 | `Deference.soft_nonneg` | §3 soft-max gap, argmax case; lemma feeding `value_of_CM` | faithful (argmax, not softmax) | **partly — see note** |
| 4 | `Deference.value_of_CM` | §9 check **D**: conditional martingale ⇒ Value (finite exact) | faithful | yes |
| 5 | `Approx`/`AsympLE` + 6 calculus lemmas | §0.2 asymptotics `≂ₙ`,`≳ₙ`,`≲ₙ`; §9(a) "calculus modeled as real-sequence asymptotics" | faithful **modeling choice**, see caveats | **partly** |
| 6 | `DeferenceAsymp.value_asymptotic` | §3 clean proof of Value; §9(a) | faithful to "composition is valid", NOT to LI theorems | **yes, with the standard caveat** |
| 7 | `DeferenceExtra.softmax_lower_bound` | §3 "soft-max gap"; §9(c) | faithful, **weaker constant** | yes |
| 8 | `DeferenceExtra.CM_implies_immodest` | §5.2 finite-collapse, the one-line step | faithful but **partial** (soft⇒hard left as prose) | **partly — see note** |

---

## 1. `Deference.decomposition`

**Exact Lean statement.** Over any commutative ring `K`, any finite index types `W` (worlds) and
`J` (menu options), for **all** functions `π : W → K`, `P : W → W → K`, `O : J → W → K`,
`α : J → W → K`, and any fixed `i : J`:

```
(∑ w, π w * (∑ j, α j w * O j w))  −  (∑ w, π w * O i w)
   =   (∑ w, π w * (∑ j, α j w * (O j w − ∑ v, P w v * O j v)))          -- D_CM
     + ((∑ w, π w * (∑ v, P w v * O i v)) − (∑ w, π w * O i w))          -- D_UM_i
     + (∑ w, π w * ((∑ j, α j w * (∑ v, P w v * O j v)) − (∑ v, P w v * O i v)))  -- soft_i
```

In words: the **Value gap** `gap_i := E_π(Ŝ) − E_π(O^i)` (where `E_π(Y) = ∑_w π_w Y_w`,
`Ŝ = ∑_j α^j O^j`) equals exactly `D_CM + D_UM_i + soft_i`, where the **expert posterior at world
`w`** is encoded as the matrix row `P w · = (P_{wv})_v`, so `(∑_v P w v · O j v) = E_w(O^j)` plays
the role of the future-self estimate `E(O^j)`. Proof: `simp only [mul_sub,
Finset.sum_sub_distrib]; ring` — pure ring linearity, **no hypothesis on the frame** (`π`, `P`
need not be probabilities; `K` need not be ordered).

**Informal claim captured.** v2 §9 (and `check.py` check **A**): the exact identity
`Value gap = D_CM + D_UM + soft`, "holds **symbolically for all frames** (sympy `expand` = 0)".
The Lean **upgrades** the sympy result from sampled shapes (≤ 4×3) to a universal statement over
arbitrary `Fintype W, J` and arbitrary `CommRing`.

**Fidelity: faithful and strong; mapping obvious.** This is the strongest correspondence in the
file. The three summands are written exactly as the §9 underbraces:
`D_CM = ∑_w π_w ∑_j α^j_w (O^j_w − E_w(O^j))`, `D_UM_i = E_π(E(O^i)) − E_π(O^i)`,
`soft_i = E_π(∑_j α^j E(O^j) − E(O^i))`. No probabilistic hypotheses are smuggled in, which is
correct: it is a linearity identity, true before any frame axioms. Non-vacuous (it is an equation
between two genuinely different syntactic expressions, closed only by `ring`).

---

## 2. `Deference.value_of_defects`

**Exact Lean statement.** Over a `LinearOrder`ed strictly-ordered `Field` `K`, finite `W, J`, for
all `π, P, O, α`, `i`, **assuming**:
- `hCM`: `D_CM = 0` (the `∑_w π_w ∑_j α^j_w (O^j_w − E_w O^j)` term is exactly 0),
- `hUM`: `D_UM_i = 0` (i.e. `E_π(E O^i) − E_π(O^i) = 0`),
- `hsoft`: `0 ≤ soft_i`,

then `0 ≤ gap_i`, i.e. `0 ≤ E_π(Ŝ) − E_π(O^i)`. Proof: rewrite by `decomposition`, kill the two
zero terms, conclude from `hsoft`.

**Informal claim captured.** v2 §9: "The LI theorems are exactly the statements that the three
terms vanish (`D_CM, D_UM → 0` …; the softmax term ≥ −δ log k), whence Value." This is the
**δ = 0 / defects-= 0 shadow**: the exact-arithmetic version where the two martingale defects are
literally zero and the soft term is nonnegative.

**Fidelity: faithful; mapping obvious.** Hypotheses are taken as **assumptions**, which is the
honest move: `D_CM = 0` and `D_UM = 0` are precisely what the LI theorems `thm:ccee`/`thm:cee`
deliver (only asymptotically in reality — captured separately by `value_asymptotic`; here they are
exact). Nothing circular: the conclusion `0 ≤ gap` is **not** among the hypotheses. Note the
ordered-field requirement is needed only for `0 ≤ …`; the underlying identity needs only a ring.

---

## 3. `Deference.soft_nonneg`

**Exact Lean statement.** Same ordered-field, finite setting. **Assuming**:
- `hπ`: `∀ w, 0 ≤ π w` (the novice weights are nonnegative — `π` is a sub-probability-ish weight),
- `hmax`: `∀ w, (∑_v P w v · O i v) ≤ ∑_j α^j_w (∑_v P w v · O j v)`, i.e. at every world `w`,
  `E_w(O^i) ≤ ∑_j α^j_w E_w(O^j)` — the chosen option's future-estimate is **≤** the
  α-weighted average of all options' future-estimates, *worldwise*,

then `0 ≤ soft_i = ∑_w π_w (∑_j α^j_w E_w(O^j) − E_w(O^i))`. Proof: `Finset.sum_nonneg` +
`mul_nonneg`.

**Informal claim captured.** The §3 **soft-max gap** step, specialized: §3 shows
`∑_j α^j E(O^j) ≥ max_j E(O^j) − δ log k ≥ E(O^i) − δ log k`. The Lean lemma is the **δ = 0 /
exact** form of the *conclusion* of that step: it takes the worldwise inequality
`E_w(O^i) ≤ ∑_j α^j_w E_w(O^j)` as a **hypothesis** and integrates it against `π ≥ 0`.

**Fidelity: faithful, but NON-OBVIOUS MAPPING — flag.** Two gaps between this and §3 prose:
1. **`hmax` is the argmax (δ→0) bound, not the softmax-with-error bound.** §3's actual inequality
   has a `− δ log k` slack (`∑_j α^j E O^j ≥ E O^i − δ log k`); here the slack is **zero**
   (`E_w(O^i) ≤ ∑_j α^j_w E_w(O^j)` outright). This exact bound holds when `α` is the true argmax
   selector (so `∑_j α^j E O^j = max_j E O^j ≥ E O^i`), i.e. the `δ = 0` limit. So `soft_nonneg`
   lives in the same δ=0 shadow as `value_of_defects`/`value_of_CM`; the softmax error term is
   handled **separately** by `softmax_lower_bound` (decl 7) and threaded through the *asymptotic*
   layer (`value_asymptotic`'s `hSoft`), **not** here. This separation is correct but means
   `soft_nonneg` alone does NOT capture the "softmax" content — it captures only "argmax of the
   future-estimates weakly dominates any fixed option, integrated against π ≥ 0."
2. `hmax` is stated at the level of the **inner sums** `∑_v P w v · O j v` (= `E_w(O^j)`), i.e. it
   is an inequality among **future-self estimates**, matching §3's `m_j = E_{f(n)}(O^j)`. Faithful,
   but a reader must unfold `∑_v P w v · O j v = E_w(O^j)` to see it.

Non-vacuous: `hmax` is a real constraint (false for a badly-chosen `α`), and the conclusion is a
genuine nonnegativity, not `True`.

---

## 4. `Deference.value_of_CM`

**Exact Lean statement.** Ordered field, finite `W, J`, all `π,P,O,α`, `i`. **Assuming**
`hπ : ∀ w, 0 ≤ π w`, `hCM : D_CM = 0`, `hUM : D_UM_i = 0`, and
`hmax : ∀ w, E_w(O^i) ≤ ∑_j α^j_w E_w(O^j)`, conclude `0 ≤ gap_i = E_π(Ŝ) − E_π(O^i)`. Proof:
`value_of_defects … (soft_nonneg …)` — i.e. decls 2 ∘ 3.

**Informal claim captured.** v2 §9 check **D**: "**conditional martingale ⇒ Value**, 3 000 random
prior frames, 0 counterexamples; `D_CM = D_UM = 0` exactly." This is the headline finite-exact
implication: a reasoner whose conditional martingale defect vanishes (and whose unconditional
defect vanishes, and whose α argmax-dominates) values deference. The "conditional martingale"
naming attaches to `hCM`; `hUM` is the unconditional companion `thm:cee`.

**Fidelity: faithful; mapping obvious** *given* the decl-3 caveat. This is the exact (`δ=0`)
shadow of the §3 Value proposition; it is **not** the asymptotic theorem (that is decl 6). The
honest reading: it certifies the **finite algebraic implication** "defects 0 + argmax ⇒ Value gap
≥ 0," which is exactly what `check.py` D samples. The `hmax` carries the same argmax-vs-softmax
caveat as decl 3 — fine here because this is the exact shadow.

---

## 5. `DeferenceAsymp.Approx` / `AsympLE` and the six calculus lemmas

**Exact Lean definitions.**
- `Approx a b := Tendsto (fun n => a n − b n) atTop (𝓝 0)` — i.e. `(a_n − b_n) → 0`. **Models LI's
  `a ≂ₙ b`.**
- `AsympLE a b := ∀ ε > 0, ∀ᶠ n in atTop, a n ≤ b n + ε` — i.e. `a_n ≤ b_n + o(1)`. The doc's
  reading: **`b ≳ₙ a` is `AsympLE a b`.**

**Calculus lemmas (all PROVED from Mathlib `Filter`/`Tendsto`):** `Approx.rfl'` (reflexivity),
`Approx.symm` (symmetry), `Approx.trans` (transitivity), `Approx.asympLE` (`≂ₙ` refines `≲`),
`AsympLE.trans` (transitivity of `≲`), `AsympLE.trans_approx` (`≲` then `≂ₙ` gives `≲`), and
`approx_sum` (finite sums respect `≂ₙ`).

**Informal claim captured.** v2 §0.2 defines `x_n ≂ₙ y_n :⇔ lim(x_n − y_n) = 0`,
`x_n ≳ₙ y_n :⇔ liminf(x_n − y_n) ≥ 0`, `x_n ≲ₙ y_n :⇔ limsup(x_n − y_n) ≤ 0`. §9(a): "the
`≂ₙ`/`≳ₙ` calculus is modeled honestly as real-sequence asymptotics." `approx_sum` "packages
thm:loe's additivity over the menu" (§9 caption).

**Fidelity: faithful modeling choice — but flag two NON-OBVIOUS points:**
1. **`AsympLE` is NOT literally `limsup ≤ 0`; it is the ε/eventually form.** `AsympLE a b ⇔
   ∀ε>0 ∃N ∀n≥N, a_n ≤ b_n + ε`. For real sequences this is **equivalent** to
   `limsup(a_n − b_n) ≤ 0` (= the doc's `a ≲ₙ b`), *provided* `a_n − b_n` is bounded above or one
   reads `limsup` in `[−∞,∞]`. The ε-form is the robust choice (no `limsup` finiteness needed) and
   is the standard "eventually within ε" rendering of `≲`; I judge it a **faithful** model of `≲ₙ`,
   but it is a definitional choice a reader should confirm rather than a verbatim transcription.
2. **`≳ₙ` is never defined directly; only its mirror `≲` (`AsympLE`) is.** The doc's `b ≳ₙ a`
   becomes `AsympLE a b`. Correct (liminf(b−a) ≥ 0 ⇔ limsup(a−b) ≤ 0 in the ε-form), but the
   orientation flip is a place to be careful when reading the conclusion of `value_asymptotic`.

`approx_sum`: faithful packaging of "linearity over a **fixed finite** menu `J : Fintype`"; note it
sums over the *full* `Finset.univ` of `J`, matching §3's fixed-`k` menu. The finiteness is genuine
(uses `tendsto_finset_sum`), so this does **not** silently extend to `k_n → ∞`; that scope
condition is exactly §3's "for bounded menu size."

---

## 6. `DeferenceAsymp.value_asymptotic`

**Exact Lean statement.** For a `Fintype J`, fixed `i : J`, sequences `ES, c, δ : ℕ → ℝ` and
families `a, b, Eo, Ee : J → ℕ → ℝ`. The intended readings (from the doc-comment):
`ES = E_now(Ŝ)`, `Eo j = E_now(O^j)`, `Ee j = E_now(E_later O^j)`, `a j = E_now(α^j O^j)`,
`b j = E_now(α^j E_later O^j)`, `c = E_now(∑_j α^j E_later O^j)`, `δ` = softmax gap → 0.
**Assuming the five LI results as hypotheses**:
- `hAdd1 : Approx ES (fun n => ∑ j, a j n)` — `E_now(Ŝ) ≂ₙ ∑_j E_now(α^j O^j)` [thm:loe, "out"];
- `hCcee : ∀ j, Approx (a j) (b j)` — `∀j, E_now(α^j O^j) ≂ₙ E_now(α^j E_later O^j)` [**thm:ccee**];
- `hAdd2 : Approx (fun n => ∑ j, b j n) c` — `∑_j E_now(α^j E_later O^j) ≂ₙ E_now(∑_j α^j E_later O^j)`
  [thm:loe, "back"];
- `hCee : ∀ j, Approx (Ee j) (Eo j)` — `∀j, E_now(E_later O^j) ≂ₙ E_now(O^j)` [thm:cee];
- `hδ : Tendsto δ atTop (𝓝 0)` — `δ_n → 0`;
- `hSoft : ∀ᶠ n, Ee i n ≤ c n + δ n` — eventually `E_now(E_later O^i) ≤ E_now(∑_j α^j E_later O^j)
  + δ_n` [thm:expprovind ∘ softmax bound].

**Conclusion** `AsympLE (Eo i) ES`, i.e. `E_now(O^i) ≲ E_now(Ŝ)`, i.e. **`E_now(Ŝ) ≳ₙ E_now(O^i)`
= Value (LI form)** (v2 §2's definition, §3's proposition). Proof: the §3 chain verbatim —
`ES ≂ₙ ∑a ≂ₙ ∑b ≂ₙ c`, then `Ee i ≲ c` from `hSoft + hδ`, then
`Eo i ≂ₙ Ee i ≲ c ≂ₙ ES`.

**Informal claim captured.** v2 §3 "The clean proof of Value": the five-line chain
`E_n(Ŝ) ≂ₙ ∑_j E_n(α^j O^j) ≂ₙ ∑_j E_n(α^j E_{f(n)} O^j) ≂ₙ E_n(∑_j α^j E_{f(n)} O^j) ≳ₙ
E_n(E_{f(n)} O^i) − δ log k ≂ₙ E_n(O^i)`, concluding `E_n(Ŝ) ≳ₙ E_n(O^i)`.

**Fidelity: faithful TO WHAT IT CLAIMS, with the standard and correctly-disclosed caveat.** This
is the central correspondence and the place to be most careful:
- **What it proves:** the *composition* of the five LI results is asymptotically valid — i.e. *if*
  you grant `thm:loe`, `thm:ccee`, `thm:cee`, `thm:expprovind`(∘softmax) as the named hypotheses,
  Value follows in the `≂ₙ`/`≳ₙ` calculus. The doc (§9(a)) states exactly this: "This is the sense
  in which the §3 proof is machine-checked: **its composition of the LI theorems is valid**."
- **What it does NOT prove:** the LI theorems themselves. `hCcee, hCee, hAdd*, hSoft` are **inputs**.
  This is the honest boundary (§9 "Not checked") and is **not** smuggling: the conclusion (Value)
  is genuinely distinct from any single hypothesis; no hypothesis says `AsympLE (Eo i) ES`.
- **One subtle faithfulness point to flag — `hSoft` vs §3 line 4.** §3 line 4 is
  `∑_j α^j E_later O^j ≳ₙ E_later O^i − δ log k` followed by passing to `E_now` via thm:expprovind.
  In the Lean, `hSoft` is stated *already at the `E_now` level*: `E_now(E_later O^i) ≤
  E_now(∑_j α^j E_later O^j) + δ_n`, i.e. `Ee i ≤ c + δ`. So the Lean **folds thm:expprovind +
  softmax bound + the inner inequality into a single hypothesis `hSoft`**. This is faithful (it is
  the *net* effect of §3 line 4), but a reader should note: the Lean does not separately witness the
  worldwise softmax inequality nor the thm:expprovind pass-through; both are bundled into `hSoft`.
  Decl 7 (`softmax_lower_bound`) discharges the *softmax* half of that bundle as a standalone proof,
  but the thm:expprovind pass-through (worldwise bound ⇒ `E_now` bound) remains an assumption — as
  it must, absent a formalization of LI.
- **Non-vacuity check:** all hypotheses are satisfiable simultaneously (e.g. take every sequence
  constant-equal so all `Approx` hold by `rfl'`, `δ ≡ 0`, and `Ee i = c`), and in that witness the
  conclusion is a real inequality, so the theorem is not vacuously true and not `True`-style.
- **Generality bonus (ties to §10):** the statement **never mentions "future self."** `Ee`, `c`,
  etc. are arbitrary sequences constrained only by the hypotheses. So the theorem is *already*
  expert-agnostic — exactly the §10.1 observation. (That is a property of the **statement**, not an
  extra claim proved here; flagged because it is the bridge an §10 Lean target would exploit.)

---

## 7. `DeferenceExtra.softmax_lower_bound`

**Exact Lean statement.** For `Fintype J` `[Nonempty J]`, `m : J → ℝ`, `δ : ℝ` with `0 < δ`, and
any `i : J`:

```
m i − (Fintype.card J : ℝ) * δ  ≤  ∑ j, (exp (m j / δ) / ∑ k, exp (m k / δ)) * m j.
```

In words: the **temperature-δ softmax-weighted mean** of the values `m` is at least
`m_i − (card J)·δ` for every option `i` (equivalently, within `(card J)·δ` of the max). Proof:
per-option bound `w_j·(M − m_j) ≤ δ` via `Real.add_one_le_exp` (where `M = max m`), summed.

**Informal claim captured.** v2 §3 "The soft-max gap": `∑_j α^j m_j ≥ max_j m_j − δ log k ≥
m_i − δ log k`, with `m_j = E_{f(n)}(O^j)`, `α^j = softmax`. §9(c): "discharges the analytic half
of `hSoft`."

**Fidelity: faithful, WEAKER CONSTANT — flag (disclosed in the doc).** The note's tight bound is
`δ · log(card J)` (the entropy/Gibbs bound `L = m̄ + δ H(α)`, `H ≤ log k`). The Lean proves the
**cruder** `(card J) · δ`. Since `card J · δ → 0` whenever `δ → 0` for fixed (bounded) `J`, this is
all the `δ → 0` limit in `value_asymptotic` needs. Two honest notes:
1. The cruder constant is **worse for large `J`** (`card J` vs `log(card J)`), so for the `k_n → ∞`
   regime mentioned in §3 ("any `k_n` with `δ_n log k_n → 0`") this Lean bound would require the
   stronger `δ_n · card J_n → 0`, not `δ_n log k_n → 0`. For **fixed bounded menus** (the
   `value_asymptotic` setting, `J : Fintype`) the distinction is immaterial. This is the one place
   the Lean is genuinely **weaker** than the prose, and it is correctly disclosed (§9(c)).
2. The statement is about the **softmax** map explicitly (`exp (m j / δ) / ∑ exp (m k / δ)`), so —
   unlike `soft_nonneg` (decl 3), which assumed an abstract worldwise inequality — this one
   actually proves the softmax content. Non-vacuous and not circular.

---

## 8. `DeferenceExtra.CM_implies_immodest`

**Exact Lean statement.** For `Fintype W`, `π : W → ℝ`, `P : W → W → ℝ`, with `hπ : ∀ v, 0 ≤ π v`,
a world `w` with `hw : 0 < π w`, and the **hypothesis**

```
hCM : ∀ X : W → ℝ,
   (∑ v, P w v * X v)
   = (∑ v, π v * 1[P v = P w] * X v) / (∑ v, π v * 1[P v = P w])
```

(where `1[P v = P w]` is `if P v = P w then 1 else 0`), conclude

```
(∑ v, P w v * 1[P v = P w]) = 1.
```

In words: **if** the expert's estimate at world `w`, `E_w(X) = ∑_v P_{wv} X_v`, equals the novice's
**conditional** expectation given the fiber `{v : P_v = P_w}` (i.e. `E_π(X | fiber w)`) **for every
`X`**, **then** the expert is **immodest** at `w`: `P_w(fiber w) = 1` (the row `P_w` puts all its
mass on its own fiber). Proof: instantiate `hCM` at the fiber indicator `X = 1[P · = P w]`; the
indicator is idempotent, the RHS collapses to `den/den = 1`.

**Informal claim captured.** v2 §5.2 finite-collapse, **the one-line step**: "Taking
`X = 1[P = P_w]` yields `P_w(P = P_w) = 1`." The surrounding Proposition is "soft conditional
martingale on a finite frame ⇒ immodesty"; this Lean captures only the **final algebraic move**
from the *hard* conditional-martingale identity to immodesty.

**Fidelity: faithful but PARTIAL — important flag (disclosed in doc, but the gap is the whole point
of §5.2).**
- **What it captures:** the hard identity `E_w = E_π(· | fiber w)` ⇒ `P_w(fiber w) = 1`. That is
  exactly §5.2's last sentence, and it is faithful: `hCM` is the *hard* (δ→0) conditional-martingale
  identity, and the conclusion is genuine immodesty (mass 1 on the own fiber).
- **What it does NOT capture (the load-bearing part):** §5.2's actual Proposition assumes the
  **soft** martingale `E_π(X·Ind_δ(E(X)>t)) = E_π(E(X)·Ind_δ(E(X)>t))` *for all small δ* and derives
  the **hard** identity via the **spectral-gap** argument (finite ⇒ values gapped ⇒ for δ below the
  gap soft = hard; threshold events generate the σ-algebra). **None of that is in the Lean.** The
  Lean *starts* from the hard identity `hCM`. So the Lean proves `hard CM ⇒ immodest`, while §5.2's
  content is `soft CM (finite) ⇒ hard CM ⇒ immodest`; the **soft⇒hard / no-spectral-gap reduction —
  the step that genuinely needs the frame to be finite, and whose *failure* on infinite frames is
  the home of modesty — is left entirely as prose** (§9(c), §5.2 explicitly say so). This is the
  single most important fidelity caveat in the file: the Lean does **not** establish the finite-frame
  *impossibility*; it establishes only the trivial-once-you-have-the-hard-identity tail.
- **`hCM ∀ X` is strong.** Requiring the identity for **all** `X : W → ℝ` (not just indicators) is
  more than §5.2 strictly needs for the final step (instantiating at one indicator suffices), so the
  hypothesis is, if anything, *stronger* than necessary — meaning the lemma is **easy** and does not
  smuggle. It is **non-vacuous** in the right way: `hw : 0 < π w` guarantees the fiber denominator is
  positive (the kernel of the proof — `w` sees itself), so the conclusion is a real constraint, not
  vacuously satisfied.
- **Encoding note (NON-OBVIOUS MAPPING):** "expert posterior" `E_w` is the matrix row `P w ·`; the
  "fiber of `w`" is `{v : P v = P w}` (worlds with the *same expert posterior row*). "Immodesty"
  `P_w(P = P_w) = 1` is rendered as `∑_v P_{wv} · 1[P_v = P_w] = 1`. A reader must accept this
  encoding of "the expert's σ-algebra cell" as the set of rows equal to `P_w`; it is the standard
  partition-by-posterior and faithful to §5.2's "`P_w = π(· | P = P_w)`."

---

## Cross-cutting observations / where the mapping is least obvious

1. **The `δ = 0` shadow vs the asymptotic layer.** `Deference.*` (decls 1–4) is the **exact** world
   where defects are literally 0 and `α` is the argmax; `DeferenceAsymp.*` (decls 5–6) is the
   **honest** asymptotic world where defects → 0 and the softmax slack `δ → 0`. The two are NOT
   linked in Lean (§9 "Not checked" point: that `thm:ccee/cee` force `D_CM, D_UM → 0` is not
   machine-checked). So a reader should not conflate `value_of_CM` (finite exact) with
   `value_asymptotic` (asymptotic, LI theorems assumed) — they capture *different rigor levels of
   the same §3 proof* and stand independently.

2. **`hSoft` is a bundle.** In `value_asymptotic`, `hSoft` silently bundles (i) the worldwise
   softmax inequality, (ii) thm:expprovind's worldwise⇒`E_now` pass-through. `softmax_lower_bound`
   (decl 7) re-proves only (i) as a standalone fact; (ii) remains assumed (unavoidable without LI).

3. **`soft_nonneg` (decl 3) is argmax, not softmax** — the only finite-layer lemma whose name could
   mislead. Its `hmax` is the δ=0 dominance, with the softmax error living elsewhere (decl 7).

4. **`CM_implies_immodest` (decl 8) is the tail, not the body, of §5.2.** It assumes the *hard*
   identity and concludes immodesty in one line; the soft⇒hard spectral-gap reduction — the actual
   impossibility content and the only place infinitude is forced — is **prose only**. This is the
   highest-value red-team target for a future Lean: complete §5.2 by proving `soft CM (finite) ⇒
   hard CM` (orientation-map Q3).

5. **`value_asymptotic` is expert-agnostic in its hypotheses** (never says "future self") — the
   §10.1 modularization is already visible at the type level. Confirming "no premise secretly
   requires expert = self" is the §10/Q2 Lean target; this audit confirms the *statement* permits it
   (the work would be purely re-interpretational).

**Axiom audit (from the file's `#print axioms`, established by the existing build, not re-run):**
all five audited theorems (`decomposition`, `value_of_CM`, `value_asymptotic`,
`softmax_lower_bound`, `CM_implies_immodest`) depend only on `[propext, Classical.choice,
Quot.sound]` — no `sorryAx`. (`value_of_defects`, `soft_nonneg` are lemmas feeding `value_of_CM`;
the `Approx`/`AsympLE` calculus lemmas feed `value_asymptotic`; all on the same axiom base.)
