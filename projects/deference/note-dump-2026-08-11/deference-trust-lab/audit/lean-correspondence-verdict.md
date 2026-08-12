# Lean-audit, stage 2 — ADVERSARIAL CORRESPONDENCE VERDICT

*Read-only audit. I re-read the actual source `lean-deference/LeanDeference.lean` (not just the
stage-1 map) and checked each declaration's hypotheses/conclusion/quantifiers against the v2-doc
prose it is meant to capture (§3, §5.2, §9). For each: is the hypothesis **faithful** or
**stronger-than-stated** (conclusion-smuggling)? Is it **vacuous/trivial** (a `True`-style or
all-inputs identity dressed up as a deference fact)? Do the **quantifiers** match the prose? Ratings:
**FAITHFUL** / **OVERSTATED** / **VACUOUS** / **MISLEADING**. The build itself is taken as
established (`sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`); I did NOT recompile.*

I confirm the stage-1 map's transcriptions are **exact** — every Lean hypothesis and conclusion it
quotes matches the source line-for-line (decomposition lines 27–31; value_of_defects 42–45;
soft_nonneg 54–56; value_of_CM 66–70; Approx/AsympLE 81–84; value_asymptotic 153–159;
softmax_lower_bound 188–190; CM_implies_immodest 249–254). My job here is the *adversarial* layer:
not "does the map describe the Lean" (it does) but "does the Lean **mean** the deference claim."

---

## Per-declaration verdicts

### 1. `Deference.decomposition` — **FAITHFUL** (with one honest-status caveat below)

- **Hypotheses:** none beyond types (`CommRing K`, `Fintype W J`). No frame/probability assumption.
- **Smuggling check:** impossible — there are no hypotheses to smuggle into. The conclusion is a
  bare equation closed by `ring`.
- **Vacuity check — the key adversarial question for an *identity*.** An identity "true for all
  inputs" is exactly the shape a misleading audit would dress up as a theorem. Here the honest
  reading is the right one: the LHS `(∑π·∑α·O) − (∑π·O^i)` and the RHS three-term sum are
  *syntactically distinct* expressions, and the content is that their **difference is identically 0**.
  That is genuine algebraic content (it is `check.py` A upgraded to universal `Fintype`), not
  `True`-style. But note what it does and does **not** assert: it asserts the *bookkeeping* (gap =
  D_CM + D_UM + soft) is correct; it asserts **nothing** about deference, Value, or any term being
  small. A reader must not mistake "the decomposition is valid" for "deference holds." The v2 doc is
  careful about this (§9 calls it the "keystone identity," and the Value conclusion is drawn only in
  *other* theorems). So: **FAITHFUL to the keystone-identity claim; correctly NOT presented as a
  deference theorem on its own.**
- **Quantifiers:** universal over all `π,P,O,α,i` — matches §9's "holds symbolically for all
  frames." ✔. The Lean is strictly **stronger** than `check.py` A (arbitrary `Fintype`/`CommRing`
  vs sampled ≤4×3 over ℚ), and being stronger in the *premise-free* direction cannot smuggle.

### 2. `Deference.value_of_defects` — **FAITHFUL**

- **Hypotheses:** `hCM : D_CM = 0`, `hUM : D_UM_i = 0`, `hsoft : 0 ≤ soft_i`. **Conclusion:**
  `0 ≤ gap_i`.
- **Smuggling check.** This is the decl most exposed to the smuggling charge, because two of its
  three hypotheses are *equalities setting defects to 0*. Is `0 ≤ gap_i` secretly among them? No:
  the conclusion is an **inequality on a fourth quantity** (`gap_i`), and the proof is
  `rw[decomposition,hCM,hUM]; simpa using hsoft` — i.e. the conclusion is genuinely *derived* from
  the identity plus the three premises, not assumed. The premises `D_CM=0, D_UM=0` are honest stand-ins
  for "the LI theorems make these → 0" (here taken exactly, δ=0 shadow). **Not circular.**
- **Vacuity check.** The premises are simultaneously satisfiable with `gap_i > 0` strictly (e.g.
  argmax `α`, generic `O`), so the conclusion is not vacuously forced. ✔
- **Honest-limit point:** this is the **exact (δ=0)** version; the doc does not claim the LI theorems
  *prove* `hCM`/`hUM` hold exactly — only asymptotically (decl 6). v2 §9 states this boundary
  explicitly ("Not checked … that the genuine theorems force D_CM, D_UM → 0"). Faithful to that
  framing.

### 3. `Deference.soft_nonneg` — **FAITHFUL but NAME-MISLEADING** (rate: FAITHFUL-with-flag)

- **Hypotheses:** `hπ : ∀w, 0 ≤ π w`; `hmax : ∀w, E_w(O^i) ≤ ∑_j α^j_w E_w(O^j)` (worldwise
  argmax-dominance). **Conclusion:** `0 ≤ soft_i`.
- **Smuggling check.** `hmax` is a *worldwise* inequality among future-self estimates; the
  conclusion is the *π-integrated* nonnegativity. The proof (`sum_nonneg` + `mul_nonneg`) genuinely
  *uses* `hπ ≥ 0` to push the worldwise bound through the integral. The conclusion is NOT a
  restatement of `hmax` (integrating against a signed measure could flip the sign — `hπ` is what
  prevents that, and is load-bearing). **Not smuggling.**
- **The adversarial catch (this is the real one for decl 3):** the *name* `soft_nonneg` and the
  docstring ("argmax selection, ∑α m = max m") invite reading this as the **softmax** content of §3.
  It is **not.** §3's actual line-4 inequality carries a `−δ log k` slack; `hmax` here has **zero**
  slack (it is the δ→0 / true-argmax limit). So this lemma captures *only* "argmax weakly dominates a
  fixed option, integrated against π≥0," **not** "softmax is within δ log k of the max." The softmax
  content lives entirely in decl 7. A careless reader could over-credit decl 3 with the softmax
  result. The map flags this; I **confirm and elevate** it: the gap between `hmax` (exact dominance,
  *assumed*) and the real softmax bound (*proved*, decl 7) is the single most name-deceptive spot in
  the file. Not an honesty failure of the *theorem* (the statement is exactly what it is), but a spot
  where the docstring "argmax = max ≥ m_i" papers over the δ=0 specialization.
- **Quantifiers:** `∀w` worldwise — matches §3's "in every consistent world." ✔ Non-vacuous (`hmax`
  is false for a badly chosen `α`).

### 4. `Deference.value_of_CM` — **FAITHFUL** (inherits decl-3's argmax-vs-softmax caveat)

- = decls 2 ∘ 3. Hypotheses `hπ, hCM=0, hUM=0, hmax`; conclusion `0 ≤ gap_i`.
- **Smuggling check.** Same as decl 2: conclusion is a derived inequality, not assumed. The name
  "CM ⇒ Value" is apt: `hCM` is literally the conditional-martingale defect set to 0. **Not
  circular.** Matches `check.py` D ("D_CM=D_UM=0 exactly, 0 counterexamples"). ✔
- **Caveat:** carries decl-3's "hmax is δ=0 argmax, not softmax-with-slack." This is the **exact
  finite shadow**, NOT the asymptotic LI theorem (decl 6) — the doc keeps these two rigor levels
  separate and unlinked, which is honest (§9: the implication "LI theorems force defects→0" is *not*
  machine-checked).

### 5. `Approx` / `AsympLE` + 6 calculus lemmas — **FAITHFUL modeling choice** (one definitional flag)

- **Definitions:** `Approx a b := (a_n − b_n) → 0` (= `≂ₙ`); `AsympLE a b := ∀ε>0, ∀ᶠn, a_n ≤ b_n+ε`
  (= `≲`, so `b ≳ₙ a`). Six lemmas (rfl/symm/trans/refines/trans/trans_approx/sum) all PROVED.
- **Adversarial check on `AsympLE`.** The doc (§0.2) defines `≲ₙ` via `limsup(a−b) ≤ 0`; the Lean
  uses the ε-eventually form. For real sequences these coincide *up to* the `limsup`-in-[−∞,∞]
  reading; the ε-form is the robust standard rendering and is, if anything, the *cleaner* primitive.
  This is a **faithful modeling choice**, not a weakening that smuggles: it is neither stronger nor
  weaker in a way that affects the one use site (`value_asymptotic`), where only `trans`/`trans_approx`
  are invoked. **Flag, not a fault:** a reader verifying §0.2 ↔ Lean must accept ε-form = limsup-form;
  the map's caveat is correct.
- **`approx_sum`:** sums over the *full* `Finset.univ` of a `Fintype J` — i.e. **fixed finite menu**.
  This faithfully matches §3's fixed-`k` linearity and does **not** silently cover `k_n → ∞`. Honest.
- **Vacuity:** the lemmas are real filter facts (not `True`), and `rfl'` shows the predicates are
  inhabited. ✔

### 6. `DeferenceAsymp.value_asymptotic` — **FAITHFUL** (the central case; honest "modulo LI")

This is where an overstatement would matter most, so I checked it hardest.

- **Exactly six hypotheses, and they are exactly the LI inputs the prose names — nothing more:**
  `hAdd1` (thm:loe out), `hCcee` (thm:ccee, ∀j), `hAdd2` (thm:loe back), `hCee` (thm:cee, ∀j), `hδ`
  (δ→0), `hSoft` (the softmax/expprovind bound, eventually). I cross-checked the source (lines
  153–158) against §3's five-line chain (lines 449–458) and §9's hypothesis table (lines 715–718):
  the correspondence is **one-to-one**. There is **no sixth structural assumption** and **no hidden
  premise** equivalent to the conclusion. ✔ This is a genuine "Value holds **modulo** the five LI
  results" theorem.
- **Smuggling check — decisive.** The conclusion is `AsympLE (Eo i) ES`. **No** hypothesis is
  `AsympLE (Eo i) ES` or any relabeling of it: `hCee` relates `Ee i ↔ Eo i`, `hSoft` relates
  `Ee i ↔ c`, the `Add`/`Ccee` chain relates `ES ↔ c`; the conclusion is the *composite* `Eo i ≲ ES`,
  assembled by the proof (line 171). The five LI facts are *inputs*, exactly as an "if you trust the
  LI paper, then Value" claim should have them. **Not circular.**
- **`hSoft` is a bundle — confirmed and important.** `hSoft : ∀ᶠn, Ee i n ≤ c n + δ n` is stated
  *already at the `E_now` level*, so it folds together (i) the worldwise softmax inequality and (ii)
  thm:expprovind's worldwise⇒E_now pass-through. §3 splits these (line 4 + thm:expprovind);
  the Lean merges them into one hypothesis. This is **faithful to the net effect** but means the Lean
  does *not* independently witness the expprovind pass-through (it *can't*, absent a formalization of
  LI). Decl 7 discharges half (i) of this bundle as a standalone proof; (ii) remains assumed. The doc
  (§9 row for `hδ,hSoft`, plus footnote "softmax half now proved — see (c)") states this honestly.
- **Quantifiers / orientation.** Conclusion `AsympLE (Eo i) ES` unfolds to `E_now(O^i) ≲ E_now(Ŝ)`
  ⇔ `E_now(Ŝ) ≳ₙ E_now(O^i)` = Value (§2). The `≳ₙ`-via-mirror-flip is correct (decl 5 flag). ✔
- **Non-vacuity.** Witnessed: all-constant sequences with `δ≡0`, `Ee i = c` satisfy every hypothesis
  while the conclusion is a real (non-`True`) inequality. So **not vacuous.** ✔
- **§10 bonus, correctly *not* over-claimed.** The statement never says "future self" — `Ee, c` are
  arbitrary sequences. So it is *already* expert-agnostic at the type level. The map notes this is a
  property of the **statement**, not an extra theorem proved; I confirm — no §10 claim is smuggled in
  as "proved."

**Verdict FAITHFUL.** It proves precisely "the §3 composition of the LI theorems is valid," which is
what §9(a) claims and no more.

### 7. `DeferenceExtra.softmax_lower_bound` — **FAITHFUL, weaker constant (DISCLOSED)**

- **Statement:** for genuine softmax weights `exp(m_j/δ)/∑exp(m_k/δ)`, the weighted mean
  `≥ m_i − (card J)·δ`. Proof from `Real.add_one_le_exp` only.
- **Smuggling/vacuity:** the bound is about the *explicit softmax map* (unlike decl 3's abstract
  `hmax`), so it genuinely proves softmax content; not circular, not `True`.
- **The one honest weakening.** Proves cruder `(card J)·δ` vs the note's tight `δ·log(card J)`. For
  the **fixed-bounded-J** setting of `value_asymptotic` this is immaterial (both → 0 as δ→0). It is
  genuinely **weaker for `k_n → ∞`** (would need `δ_n·card J_n → 0`, stronger than `δ_n log k_n → 0`).
  v2 §9(c) discloses exactly this ("the cruder (card J)·δ proved here is all the δ→0 limit needs").
  **No overstatement.** ✔

### 8. `DeferenceExtra.CM_implies_immodest` — **FAITHFUL to a PARTIAL claim** (the load-bearing red-team gap)

This is the most important honesty test in the file, and the place a reader is most likely to
over-credit the formalization.

- **Hypothesis `hCM` is the HARD identity, not a disguised immodesty.** `hCM : ∀X, E_w(X) =
  E_π(X | fiber w)`. Adversarially: is `hCM` secretly the conclusion `P_w(fiber)=1`? **No.** `hCM`
  is the *conditional-martingale identity* (expert estimate = novice conditional given the fiber); the
  conclusion `∑_v P_w v · 1[P_v=P_w] = 1` is *derived* by instantiating `hCM` at the fiber indicator
  and using idempotence + `den/den=1` (lines 265–271). They are distinct: one could imagine `hCM`
  failing while the conclusion holds or vice versa. **Not circular.** ✔
- **`hCM ∀X` is STRONGER than needed** (only the indicator instance is used). That makes the lemma
  *easier*, which is the opposite of smuggling — a stronger hypothesis cannot inflate the result.
  Honest. ✔ (`hw : 0 < π w` is load-bearing for `hden > 0`, making the conclusion non-vacuous: the
  fiber denominator is genuinely positive because *w sees itself*.)
- **The decisive limitation — confirmed.** §5.2's actual *Proposition* assumes the **soft**
  conditional martingale (∀ small δ) and derives the hard identity via the **spectral-gap /
  no-gap** argument (finite values ⇒ gapped ⇒ soft=hard below the gap ⇒ threshold events generate
  the σ-algebra). **None of that is in the Lean.** The Lean *starts from* the hard identity. So:
  - Lean proves: **hard CM ⇒ immodest** (a one-line algebraic tail).
  - §5.2 claims: **soft CM (finite) ⇒ hard CM ⇒ immodest** — and the *impossibility* content, the
    *only* place finiteness is forced and whose failure on infinite frames is the home of modesty,
    is precisely the **soft⇒hard spectral-gap step**, which is **prose only.**
  The Lean therefore does **NOT** establish the finite-frame *impossibility* (the structural heart of
  the paper); it formalizes the trivial-once-you-have-the-hard-identity end. v2 §9(c) and the Lean
  docstring (lines 245–247) **explicitly say so** ("the soft-⇒-hard 'no spectral gap' reduction … is
  left as §5.2's prose"). So the *theorem* is FAITHFUL to its narrow claim, and the *doc* is honest
  about the narrowness — but a reader skimming "CM_implies_immodest, finite collapse, machine-checked"
  could badly overestimate coverage. **This is the file's biggest fidelity caveat, and it is
  correctly disclosed rather than hidden.** I rate the theorem FAITHFUL-PARTIAL and flag that the
  *headline framing* ("finite collapse, core of §5.2") leans on the disclosure footnote to stay
  honest. Highest-value future-Lean target: prove `soft CM (finite) ⇒ hard CM`.

---

## Overall verdict on v2 §9's honesty

**§9 is honest.** Adversarially, the three ways a "machine-check" section overstates are: (i) claim
the LI theorems are *proved* when they're assumed; (ii) claim the finite *impossibility* is verified
when only an algebraic tail is; (iii) let a true-for-all-inputs identity masquerade as a deference
result. §9 commits **none** of these:

- It states the LI results enter as **explicit hypotheses** ("we trust the paper, we don't re-prove
  it") and has an explicit **"Not checked"** paragraph (lines 735–742) naming exactly what is *not*
  verified: that thm:ccee/cee force `D_CM, D_UM → 0`, and the `≂ₙ` bookkeeping. This forecloses
  overstatement (i). The hypothesis/LI-result table (715–718) is one-to-one with the Lean.
- For `CM_implies_immodest` it explicitly carves out the soft⇒hard spectral-gap step as **prose**
  (line 733, and the Lean docstring), so it does **not** claim the impossibility is checked —
  forecloses (ii). This is the most load-bearing disclosure and it is present and clear.
- It labels `decomposition` a *keystone identity* and draws Value only via the *other* theorems,
  and it correctly bills `softmax_lower_bound` as proving the **cruder** constant — forecloses (iii)
  and the constant-inflation trap.
- The sole self-description I'd police is the summary sentence "this verifies the proof's *algebra
  and its finite mathematical core* … but not the asymptotic LI layer." That is **accurate**: the
  Lean verifies (a) the asymptotic *composition* is valid given the LI hypotheses, (b) the exact
  finite identity + CM⇒Value δ=0 shadow, (c) the softmax bound and the immodesty *tail*. It does NOT
  verify the LI theorems, the soft⇒hard reduction, or that defects actually vanish — and §9 says so.

**Net:** every Lean theorem means what §9 says it means; no conclusion-smuggling; no vacuity dressed
as content; quantifiers match (universal where prose says "all frames," fixed-finite menu where prose
says fixed-`k`). The two spots a *reader* could over-credit — `soft_nonneg`'s name vs the softmax
bound, and `CM_implies_immodest` as "§5.2 checked" — are both real, both flagged in the map, and both
**explicitly disclosed in §9/the docstrings**, so they are reader-vigilance items, not honesty
failures of the doc. **§9's claims are honest and appropriately scoped.**

---

### Rating summary

| # | declaration | rating |
|---|---|---|
| 1 | `decomposition` | FAITHFUL (identity, not a deference claim on its own — correctly so) |
| 2 | `value_of_defects` | FAITHFUL (no smuggling; δ=0 shadow) |
| 3 | `soft_nonneg` | FAITHFUL, NAME-MISLEADING (argmax/δ=0, not softmax; disclosed) |
| 4 | `value_of_CM` | FAITHFUL (inherits decl-3 argmax caveat; = check.py D) |
| 5 | `Approx`/`AsympLE` + calculus | FAITHFUL modeling choice (ε-form = limsup-form flag) |
| 6 | `value_asymptotic` | FAITHFUL (exactly 5 LI hyps; honest "modulo LI"; no smuggling) |
| 7 | `softmax_lower_bound` | FAITHFUL, weaker constant (disclosed) |
| 8 | `CM_implies_immodest` | FAITHFUL-PARTIAL (hard-identity tail only; soft⇒hard is prose — biggest gap, disclosed) |

No declaration rates OVERSTATED, VACUOUS, or MISLEADING-as-written. All caveats are reader-vigilance
items that v2 §9 and the Lean docstrings disclose.
