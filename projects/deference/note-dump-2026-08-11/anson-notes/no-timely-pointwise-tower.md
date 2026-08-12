# No Timely Pointwise Tower: How 2a and 2b Block Cross-Process `Mart` in the A-predicts-H Setup

*A self-contained summary of the negative result. It establishes that the **timely, pointwise tower property** — `Mart(H→A)` in the port of "Deference Done Better" to logical induction — is **unattainable** in any construction where a stronger inductor `A` predicts a weaker inductor `H`'s own future credences. The two self-reference obstructions (here called **2a**, the anti-inductive/Gödel-coin diagonal, and **2b**, the cost-circularity regress) are exactly the obstructions, and they partition the contract families between them.*

*⚠ Setting caveat (2026-08-10): the mutual-legibility setup below has `H` recording `A`'s quotes by stage `n+1` — an **immediate** human-side view of the AI. Sam Eisenstat's intended setup for his conjecture has the delay on exactly that side (humans learn AI beliefs only at a delay; AI reads human beliefs immediately), and 2a's diagonal leans on the prompt ledger (§3's "decided by stage n+1"). So this result refutes the tower for the corpus construal, not for Eisenstat's conjecture as he intends it — see [[eisenstat-conjecture-attribution]].*

---

## 0. Setup and notation

Two logical inductors over a shared language, with trader classes `𝒞_H ⊆ 𝒞_A` (canonically `P ⊆ EXP`):

- `H` — the **novice** (the human), `H ⊣ 𝒞_H`, expectation operator `E^H_n`, credence `ℙ^H_n`.
- `A` — the **expert** (the AI), `A ⊣ 𝒞_A`, stronger.

`A` is set up to **predict `H`'s own future credences**. Fix a computable deferral schedule `F(n) > n`. For an effectively computable (e.c.) family of contract sentences `P^(n)`, the contract `C_n` **settles** against

$$
Y_n \;:=\; H^+_{F(n)}\big(P^{(n)}\big),
$$

the credence `H` (having read `A`'s outputs up to that point — the **unfrozen / self-referential** target) assigns to `P^(n)` after `F(n)` stages of deliberation. `A`'s day-`n` quote for that contract is

$$
a_n \;:=\; E^A_n\big(\ulcorner Y_n \urcorner\big).
$$

**Mutual legibility.** `A` records `H`'s realized prices (so `A` gets feedback on its forecasts); `H` records `A`'s quotes `a_n` (so `a_n` is a `𝒞_H`-readable feature, decided in `H`'s ledger by stage `n+1 ≤ F(n)`).

**Asymptotics.** `x_n ≈_n y_n` means `x_n − y_n → 0`. A relation holds **timely / pointwise** if it holds in this `≈_n` (per-index, with the index) sense — as opposed to merely in the limit, or merely on average over a weighting.

**The tower property (`Mart`).** The deference relation ported from DDB. For an observable, coherent expert estimate `E*`, the novice *towers over* the expert when, for all e.c. `[0,1]`-LUVs `X`,

$$
\textbf{Mart(H→E*)}:\qquad E^H_n(X) \;\approx_n\; E^H_n\big(\ulcorner E^*(X) \urcorner\big).
$$

With `E*(X) = a_n` (the expert is `A`'s prediction of `H`'s future self), the instance at a contract sentence `P^(n)` is

$$
\textbf{(Tower)}\qquad E^H_n\big(P^{(n)}\big) \;\approx_n\; E^H_n\big(\ulcorner a_n \urcorner\big).
$$

This is the object whose impossibility is the subject of this note. It is the **equality / pointwise** face of deference; it is strictly stronger than the inequality faces (Total Trust) and than any merely-in-the-limit agreement.

---

## 1. The result, in one line

> **The timely pointwise tower `Mart(H→A)` cannot be achieved in the A-predicts-H setup.**
>
> - On contract families that **may reference `A`'s quotes**, it fails by an explicit anti-inductive counterexample (**2a**): the defect is `≥ ½` on a `𝒞_H`-computable subfamily.
> - On **quote-free** contract families, the diagonal cannot be written, but the property is still not derivable, because *timely* tracking of the coupled target requires a power assumption that is self-defeating (**2b**).

The two cases are exhaustive (a family either may reference the quotes or may not), so no family of contracts yields the timely pointwise tower.

The deeper point: **the tower is equivalent to timely pointwise tracking** (§2), and timely pointwise tracking is exactly what 2a and 2b kill. So even though perfect tracking (`a_n ≈_n Y_n`) is not something one needs *for its own sake*, the reflection-style trust property one *does* want — the tower — inherits its impossibility.

---

## 2. The tower reduces to tracking (why the obstructions transfer)

The tower is not a softer object that might survive where tracking fails. It is **equivalent** to timely pointwise tracking, via two collapses, each removing one corner-quote.

**Read-off (right corner-quote).** `a_n` is published and decided in `H`'s ledger by stage `n+1`. So `⌜a_n⌝` is a decided sentence for `H`, and convergence on decided sentences gives

$$
E^H_n\big(\ulcorner a_n \urcorner\big) \;\approx_n\; a_n.
$$

`H`'s estimate of `A`'s quote *is* `A`'s quote — `H` can just read it. (Pure observability; uses no tower.)

**Self-trust (left corner-quote).** `Y_n = H^+_{F(n)}(P^(n))` is `H`'s **own** future credence, so the self-instance of the tower is the free logical-induction self-trust theorem `cee` (Expected Future Expectations):

$$
E^H_n\big(P^{(n)}\big) \;\approx_n\; E^H_n\big(\ulcorner Y_n \urcorner\big).
$$

**Combine.** Substituting both into (Tower):

$$
E^H_n\big(\ulcorner Y_n \urcorner\big) \;\approx_n\; a_n.
$$

So the tower says: `H`'s present estimate of its own future credence equals `A`'s quote. Two consequences, depending on which side one reads:

- **Unconditionally**, by `cee`, the left side equals `H`'s present credence, giving the clean equivalence
  $$
  \textbf{(Tower)} \;\Longleftrightarrow\; a_n \approx_n \mathbb{P}^H_n\big(P^{(n)}\big)
  $$
  — *the tower forces `A`'s quote to match `H`'s present credence.*
- Where `H`'s present estimate of `Y_n` is itself accurate against the realized `Y_n` (which holds whenever `Y_n`'s value is e.c., e.g. on the §3 diagonal), this is further equivalent to
  $$
  \textbf{(Tower)} \;\Longleftrightarrow\; a_n \approx_n Y_n
  $$
  — *the tower forces timely pointwise tracking.*

Either reading suffices for the impossibility: **2a** attacks the present-credence form (the diagonal is decided at stage `n`, so present credence, future credence, and realized value coincide there), and **2b** attacks the tracking form on families where they do not coincide.

---

## 3. Obstruction 2a — the anti-inductive (Gödel-coin) diagonal

**Scope.** Families that **may reference `A`'s quotes** (i.e. the contract language contains atoms expressing "`A`'s quote `a_n` is `≤ k`"). This is the trigger for 2a; it is essential and explicit.

**Construction.** Take the diagonal subfamily

$$
P^{(n)} \;:=\; g_n, \qquad g_n \;\leftrightarrow\; \big(a_n \le \tfrac{1}{2}\big).
$$

The truth value of `g_n` is a function of `A`'s own published quote.

**Theorem (no timely tower on the diagonal).**

> For the family above, the timely tower fails:
> $$
> \liminf_n \big| E^H_n(g_n) - E^H_n(\ulcorner a_n \urcorner) \big| \;\ge\; \tfrac{1}{2}.
> $$

**Proof.** `A` publishes `a_n` and `H` records it by stage `n+1 ≤ F(n)`, so both `⌜a_n⌝` and `g_n` are **decided sentences** in `H`'s process. Convergence on decided sentences gives, timely,

$$
E^H_n(\ulcorner a_n \urcorner) \approx_n a_n, \qquad E^H_n(g_n) \approx_n \mathbb{1}\!\left[a_n \le \tfrac{1}{2}\right].
$$

If the tower held, substituting both sides would force

$$
\mathbb{1}\!\left[a_n \le \tfrac{1}{2}\right] \;\approx_n\; a_n.
$$

But for every `a ∈ [0,1]`,

$$
\Big| \mathbb{1}\!\left[a \le \tfrac{1}{2}\right] - a \Big| \;\ge\; \tfrac{1}{2}
$$

(if `a ≤ ½`: `|1 − a| = 1 − a ≥ ½`; if `a > ½`: `|0 − a| = a > ½`), so the difference cannot tend to `0`. Contradiction. ∎

**Why it works — the anti-inductive structure.** The contract is a fixed point that *inverts* `A`'s own quote: it pays out as if `A` were wrong. Any quote `a_n` near `1` settles the contract near `0`, and any quote near `0` settles it near `1`; the unique consistent point would be `a_n = ½`, but there the *settlement* is the hard value `𝟙[½ ≤ ½] = 1`, a full `½` away. The continuity that tames ordinary self-reference at the *price* level (a market can clear a liar sentence at `½`) is unavailable at the *settlement* level, where the payout is a discontinuous `0/1` function of the quote. This is the "Gödel-coin": a coin whose face is defined to contradict the predictor's bet on it.

**Key features of 2a.**

- **Power-insensitive.** The argument uses only that `H` can *read* `A`'s quote and that the diagonal is decided once read. It is independent of `A`'s computational strength — *an oracle for `A` does not help*, because the obstruction is to consistency, not to computation. A same-strength `A` dies exactly as hard as a much stronger one.
- **No future target needed.** Routed through `H`'s present credence: `g_n` is decided at stage `n`, so `E^H_n(g_n) ≈_n 𝟙[a_n ≤ ½]` with no appeal to `Y_n` and no efficient-computability assumption. The present/future distinction collapses on the diagonal.
- **A fortiori.** Failure of this single subfamily refutes the universal tower `Mart(H→A)` and any local (question-relative) deference whose LUV class contains `g_n`.

---

## 4. Obstruction 2b — the cost-circularity regress

**Scope.** **Quote-free** families — contracts `P^(n)` drawn from the base language, with no atoms referencing `a_n`. Here the diagonal of §3 cannot be *written*, so 2a does not apply. The obstruction is different in kind: not a refutation by counterexample, but the **underivability** of the timely tower from any satisfiable hypothesis.

**The setup of the difficulty.** Even quote-free, the target `Y_n = H^+_{F(n)}(P^(n))` depends on `A`'s run, because `H^+`'s stage-`F(n)` deliberation has absorbed `A`'s quotes through the coupled `(H, A)` recursion. For the tower to hold *timely*, `A`'s quote `a_n` must be an accurate day-`n` estimate of this coupled stage-`F(n)` object — i.e. there must be a `𝒞_A`-trader that, by stage `n`, prices `Y_n` correctly.

**The regress.** To compute (or force a price for) `Y_n` at stage `n`, a trader must simulate the coupled system forward to stage `F(n)`. But that system **includes `A` itself** — its own future quotes feed back into `H^+`'s deliberation. So the simulation must include `A`'s own run up to `F(n)`. Writing `R_A(·)` for the resource cost of `A`'s computation, timely prediction would require a `𝒞_A`-computation at stage `n` of cost

$$
R_A(n) \;\gtrsim\; R_A\big(F(n)\big) \;>\; R_A(n),
$$

since `F(n) > n` and costs are increasing. The required power assumption — that `𝒞_A` contains the composite `R_A ∘ F` (a trader that times-out `A`'s own future) — is **unsatisfiable**: the market would have to sit strictly above its own trader class in the simulability preorder. There is no `𝒞_A`-trader that forces timely tracking, so the tower is not derivable.

**Key features of 2b.**

- **Power-insensitive in the same way.** Making `A` "faster" (a deeper schedule, larger budget per stage) does not escape the regress: the circularity is structural (the system must simulate its own future, including the simulator), not a matter of the growth rate of `F` or the size of `A`'s budget.
- **It is an underivability result, not a refutation.** 2b shows no admissible trader *forces* the timely tower on quote-free families; it does not exhibit a family on which the tower is outright false. (In particular there can be a degenerate way to satisfy the tower-equation — e.g. `A` echoing `H`'s present credence and forgoing prediction — which is why the quote-free case is genuinely weaker than 2a. The diagonal of §3 is precisely what rules out that degenerate escape; quote-free families lack it.)
- **Confidence.** 2a is an elementary, unconditional refutation. 2b is the more delicate of the two and should be treated as the less airtight half.

---

## 5. Why the two cases are exhaustive

A contract family either contains atoms referencing `A`'s quotes or it does not.

- **Quote-referencing families** → **2a** applies: the diagonal `g_n ↔ (a_n ≤ ½)` is constructible, decided at stage `n`, and forces `𝟙[a_n ≤ ½] ≈_n a_n`, impossible by `≥ ½`. The tower is **false** (defect `≥ ½`).
- **Quote-free families** → **2b** applies: the diagonal is unconstructible, but `Y_n` still depends on the coupled run, and timely tracking would require the unsatisfiable power assumption `𝒞_A ∋ R_A ∘ F`. The tower is **underivable**.

There is no third kind of family, so no construction in the A-predicts-H setup yields the timely pointwise tower.

---

## 6. What is and is not ruled out

**Ruled out:** the **timely, pointwise, equality** tower — `Mart(H→A)` — for the cross-process pair, on every contract family. This is exactly the reflection-style trust property the port identifies as the substance of deference (the `Value ⟺ Mart` equivalence runs through it). In the port's vocabulary, this is the open §11 cross-process tower instantiated at the self-referential target; the result resolves that instance **negatively**.

**Not addressed here (and not ruled out by this argument):**

- **Limit agreement** — `lim_n a_n = lim_n Y_n` — is a strictly weaker, in-the-limit statement; the diagonal is consistent with it (both sides sit at `½` in the limit) even as the timely tower fails by `½`. It is therefore not touched by 2a/2b.
- **Averaged / statistical / gated trust** — inequality (Total Trust) faces, holding on a weighting rather than per-index. These are day-averaged objects; a day-averaged input cannot be refuted by a pointwise diagonal, and they remain available.

The precise content of the negative result is thus: *the pointwise equality face dies (2a/2b); the in-the-limit and averaged/inequality faces are not what this argument addresses.* Any positive construction that keeps the A-predicts-H setup must therefore aim at one of those weaker, non-pointwise notions — the pointwise tower itself is closed.

---

## 7. One-paragraph summary

In the setup where a stronger inductor `A` forecasts a weaker inductor `H`'s own future credences, the timely pointwise tower `Mart(H→A)` — `H`'s present expectation of `X` matching its expectation of `A`'s quote, per index — is equivalent (via read-off of the published quote and free self-trust `cee`) to `A`'s quote matching `H`'s present credence, equivalently to timely pointwise tracking `a_n ≈_n Y_n`. That tracking is impossible: on families that may reference `A`'s quotes, the anti-inductive diagonal `g_n ↔ (a_n ≤ ½)` is decided once `H` reads the quote and forces `𝟙[a_n ≤ ½] ≈_n a_n`, contradicted by a uniform `≥ ½` gap (**2a**, power-insensitive, an oracle for `A` included); on quote-free families the diagonal cannot be written, but timely tracking of the coupled target would require `A` to simulate its own future, an unsatisfiable power assumption `𝒞_A ∋ R_A ∘ F` (**2b**). These two cases exhaust all families, so the timely pointwise tower is unattainable — only weaker, non-pointwise notions of cross-process trust (in-the-limit agreement, or averaged/gated Total Trust) can survive.
