```
Maintainer:            A. M. Berns
Prompt-author-model:   GPT-5.6 Sol (OpenAI)
Orchestrator-model:    Claude Opus 5 (Anthropic)
Model (executor):      Claude Opus 5 (Anthropic), model id claude-opus-5
Dispatch date:         2026-08-11
Completion date:       2026-08-11
Skeleton version:      FINITE_MODEL_SKELETON.md v1, frozen 2026-08-11 (unmodified)
PRIORITIES item:       16
```

Everything below is stated over skeleton **v1**. No v1 object is renamed or retyped. Three additive patches are *proposed* in §5; none is applied, and the results hold without them if the three new objects are read as track-local definitions rather than skeleton members.

## 1. Exact result

### 1.1 Definitions over v1 carriers

Fix `n ∈ N`; write `t = t(n)`, `F = F(n)`. All sums exact rational.

| object | definition | measurable at |
|---|---|---|
| `η_n(ω)` | `max_{π∈Π_n} \|v⁺_n(ω,π) − v̂⁺_n(ω,π)\|` — grade-model error | `F` |
| `γ̂_n(ω)` | `v̂⁺_n(ω,Ĵ_n(ω)) − max_{π≠Ĵ_n(ω)} v̂⁺_n(ω,π)` ≥ 0 — predicted margin | `t` |
| `S` | a nonempty union of `𝓕_t`-cells on which `Ĵ_n ≡ j` | `t` |
| `ρ_{n,j}` | `P_n(S)` — certified support | `t` |
| `γ_{n,j}` | `min_{ω∈S} γ̂_n(ω)` — certified margin | `t` |
| `D_{n,j}` | `Σ_{ω∈S} P_n(ω)[v⁺_n(ω,J_n(ω)) − v⁺_n(ω,j)]` ≥ 0 — **defect** | `F` |
| `M_S`, `M_n` | `Σ_{ω∈S or Ω} P_n(ω)·max_π \|X_{n,π}(ω) − v⁺_n(ω,π)\|` — **movement** | `F` |
| `ACT[j,S]` | conduct: selection `j` on `S`, `J_n` off `S` | mixed |
| `G_n(c)` | `Σ_ω P_n(ω)·v⁺_n(ω,c(ω))` — grade-register valuation | — |
| `Γ_n(π)`, `Γ̂_n(π)` | `G_n(DELEGATE) − G_n(FIXED[π])`; and its `v̂⁺`-analogue | `F`; `t` |

Two named hypotheses, neither carried by v1 (§5 classifies them):

- **(TR-ε)** `E_{P_n}[η_n] ≤ ε_n` — the decision-time consequence of the abstract global trust relation. `ε_n` is the **approximation tolerance**.
- **(MV-M)** `M_n ≤ M` — the settlement link between the principal's grade and the intervention-indexed quantity.

### 1.2 The lemmas

**L1 (margin ⇒ agreement).** If `γ̂_n(ω) > 2η_n(ω)` then `j := Ĵ_n(ω)` is the *unique* `v⁺_n(ω,·)`-maximizer, so `J_n(ω) = j`.
*Proof.* For `π ≠ j`: `v⁺(ω,j) ≥ v̂⁺(ω,j) − η ≥ v̂⁺(ω,π) + γ̂ − η > v̂⁺(ω,π) + η ≥ v⁺(ω,π)`. ∎
The tie-break is not exploited: uniqueness is established, not assumed.

**L2 (override bound).** Under (TR-ε), `P_n(S ∩ {J_n ≠ j}) ≤ 2ε_n / γ_{n,j}`.
*Proof.* By L1, `S ∩ {J_n ≠ j} ⊆ {η_n ≥ γ_{n,j}/2}`; Markov on `E[η_n 1_S] ≤ ε_n`. ∎
The constant `2` is **sharp** — a supremum, not attained (§6.6).

**L3 (defect bound).** Under (TR-ε), `D_{n,j} ≤ 4B·ε_n / (2B + γ_{n,j})`.
*Proof.* On `S`, `0 ≤ v⁺(J_n) − v⁺(j) ≤ min(2B, (2η_n − γ_{n,j})⁺) =: h(η_n)`. On `[0,2B]`, `h(x)/x` is maximised at `x* = (γ+2B)/2` with value `4B/(2B+γ)`, so `h(x) ≤ (4B/(2B+γ))·x` pointwise; take `P_n`-expectation over `S`. ∎
**Sharp and attained** (§6.5).

**L4 (preemption cost).** Under (TR-ε), and (MV-M) for the second branch,
```
V_n(DELEGATE) − V_n(ACT[j,S])  ≤  κ_{n,j}
   :=  min{ 4B·ε_n/γ_{n,j} ,  4B·ε_n/(2B+γ_{n,j}) + 2·M_S }.
```
*Proof.* The two conducts differ only on `S ∩ {J_n ≠ j}`. First branch: the integrand is `≤ 2B` and L2 bounds the mass. Second: `X_{n,J} − X_{n,j} ≤ (v⁺(J) − v⁺(j)) + 2·drift`, summed over `S` (both terms `≥ 0`), then L3. ∎
Each branch is sharp separately. The first needs **no settlement hypothesis**.

**L5 (delegation bridge).** `V_n(DELEGATE) ≥ V_n(FIXED[π]) − 2·M_n` for every `π ∈ Π_n`, with no hypothesis beyond (MV-M). Constant `2M` sharp (§6.7).

**L6 (SIM).** `V_n(DELEGATE) ≥ V_n(SIM) − 2B·P_n(Ĵ_n ≠ J_n)`, sharp; and if `v̂⁺_n = v⁺_n` pointwise then `V_n(SIM) = V_n(DELEGATE)` identically.

**L7 (advantage estimate).** `|Γ_n(π) − Γ̂_n(π)| ≤ 2ε_n` under (TR-ε), because both `max_π v⁺` and `v⁺(·,π)` move by at most `η_n`.

### 1.3 The certificate

**`Cert_{n,j}(S; θ)`** — `θ` a declared rational preemption budget per unit of certified credence:

```
(i)   S is a nonempty union of 𝓕_{t(n)}-cells and Ĵ_n ≡ j on S;
(ii)  γ_{n,j} > 0;                                        [margin]
(iii) γ_{n,j} · ρ_{n,j} > 2·ε_n;                          [support floor]
(iv)  min{ 4B ε_n/γ_{n,j},  4B ε_n/(2B+γ_{n,j}) + 2 M_S }  ≤  θ · ρ_{n,j}.   [budget]
```

**Theorem C (V-register).** Under (TR-ε) and (MV-M), `Cert_{n,j}(S;θ)` implies

- (a) `V_n(DELEGATE) − V_n(ACT[j,S]) ≤ θ·ρ_{n,j}`; equivalently, conditional on `S`, `V_n^S(DELEGATE) − V_n^S(FIXED[j]) ≤ θ`;
- (b) `P_n(S ∩ {J_n ≠ j}) ≤ 2ε_n/γ_{n,j} < ρ_{n,j}` — A overrides the principal on a *strict minority* of the certified credence; this is what clause (iii) buys;
- (c) for every `π ∈ Π_n`: `V_n(ACT[j,S]) ≥ V_n(FIXED[π]) − 2M_n − θ·ρ_{n,j}`.

**Theorem C′ (grade register).** Let `Cert^G_{n,j}(S,π)` be clauses (i)–(ii) together with `Γ̂_n(π) > 2ε_n + 4B ε_n/(2B + γ_{n,j})`. Under (TR-ε) alone — **no settlement hypothesis, no movement term** — it implies `G_n(ACT[j,S]) > G_n(FIXED[π])`, strictly.
*Proof.* `G_n(ACT) = G_n(DELEGATE) − D_{n,j} ≥ G_n(FIXED[π]) + Γ_n(π) − 4Bε_n/(2B+γ) ≥ G_n(FIXED[π]) + Γ̂_n(π) − 2ε_n − 4Bε_n/(2B+γ) > G_n(FIXED[π])`, by L3 and L7. ∎
Every quantity in `Cert^G` other than `ε_n` is computable at `t(n)`.

### 1.4 Which comparators are covered

| comparator | V-register | grade register |
|---|---|---|
| `DELEGATE` | covered — (a) is the theorem: bounded preemption cost | `G_n(DEL) − G_n(ACT) = D_{n,j} ≤ 4Bε_n/(2B+γ_{n,j})` |
| `FIXED[π]`, every `π` | covered **non-strictly**, constant `2M_n + θρ_{n,j}`; requires (MV-M) | covered **strictly** under `Cert^G`; requires only (TR-ε) |
| `SIM` | **not** strictly coverable — impossibility I1 | not strictly coverable (same reason) |
| `FU[g]` | not covered; v1 §8.1 hole. **This certificate does not need it.** | — |

### 1.5 Three impossibility results

**I1 (SIM).** No certificate over v1 yields `V_n(DELEGATE) > V_n(SIM)`, or `V_n(ACT[j,S]) > V_n(SIM)`, for all instances satisfying it. `v̂⁺_n = v⁺_n` is permitted by v1 §3 and required to stay permitted by the roadmap's standing commitment ("the thesis must stay compatible with a perfectly predictable principal"); it forces `Ĵ_n = J_n`, hence equality of selections and of quantities. The rule/quantity distinction v1 §4 sets up does **no work in `V_n`**: that open question has a negative answer at this valuation.
Corollary, uncomfortable and worth naming: `ACT[j,S]` *is* the simulator rule restricted to `S`. The certificate licenses gated local `π^SIM`, and bounds its cost; it does not distinguish it from `π^SIM`.

**I2 (strictness).** The literal target `Cert ⟹ V_n(j) > V_n(π)` is not derivable over v1. Without (MV-M) even the non-strict form fails by the full `2B` (§6.3). With (MV-M) the best available is (c), whose strictness needs `V_n(DELEGATE) − max_π V_n(FIXED[π]) > θρ_{n,j}` — a strict delegation advantage that v1 does not imply and that is not `t(n)`-computable. Strictness *is* obtainable in the grade register (Theorem C′).

**I3 (bounded preemption is unavoidable).** For any `t(n)`-measurable `S` with `ρ > 0`, any finite `γ`, and any `ε_n > 0`, there is a model satisfying (TR-ε) in which A overrides the principal on positive `P_n`-mass inside `S` (§6.6). Hence **no certificate licensing discretion anywhere is strictly non-preemptive**: it can bound the preemption *rate* — clause (b) — but not exclude preemption. Strict non-preemption is available only as `¬Cert` everywhere, i.e. always `DELEGATE`. This is the sharpest thing the track found and it is a maintainer question, not a mathematical gap (§9.2).

### 1.6 Fail-closed

Preserved, and checkable at the level of the definitions. `Cert` occurs in exactly one place: as the selector between `ACT[j,S]` (its true branch) and `DELEGATE` (its false branch). No object in the model — `v⁺_n`, `J_n`, `F(n)`, or the settlement instantiation — is defined in terms of `Cert`, `θ`, `v̂⁺_n` or `P_n`. So `¬Cert` cedes A's discretion to `J_n` and nothing about the principal's correction is conditioned on A's state. The script checks the non-dependence mechanically by recomputing `J_n` from a model with `v̂⁺` zeroed out.

What fail-closed does **not** say, and what I3 forces into the open: under `Cert` the human's correction *is* preempted on `S ∩ {J_n ≠ j}` — in the worked case, exactly the shutdown state `w2`, `1/20` of credence. The invariant governs the `¬Cert` branch; the `Cert` branch trades strict non-preemption for a bounded rate.

### 1.7 Derived shape vs. the representative shape

The dispatch's representative shape was `D_{n,j} + L(ρ_{n,j})·M_{n:F(n)} < c(γ_{n,j}, ε)`. The derivation does not produce it. Three structural differences:

1. `ρ` does not modulate `M`. The movement term enters additively and *unmodulated* (`+2M_S`); `ρ` scales the **budget** on the right (`θ·ρ`) and appears again as a floor in a separate clause.
2. `γ` and `ε` appear on the **left**, inside the defect bound, not only on the right. `D_{n,j}` is not a free input: it is the quantity L3 *bounds*, by `4Bε_n/(2B+γ_{n,j})`.
3. The left side is a `min` of two branches — one settlement-free (`4Bε_n/γ_{n,j}`), one settlement-loaded — and which one binds depends on the regime. A single-branch inequality loses the settlement-free certificate.

## 2. Evidence class

**None of this is registered, and nothing here is `workspace-established`.**

- The lemmas and theorems of §1: **proved by hand**, in this document, over v1 carriers. Not Lean-checked. Under `AGENTS.md` standard 3 they are *proposals with a check*, not results of record.
- The worked case and every necessity/sharpness witness: recomputed exactly by `verify_certificate.py`, all `fractions.Fraction`, no floats. A **local recomputation**, not a house-checker verdict — the class it would support if registered is `test-supported`, and it cannot be `witness-checked` as things stand (§3).
- The stress test enumerates a declared finite domain and checks L1–L7 and both certificates pointwise: **524,880 models, 1,341,360 certified `(j,S)` instances, 0 violations**. It is a check on the proofs, **not** a proof: the domain is two states and two interventions.

## 3. Files, declarations, checks

All inside `prompts/2026-08-11-deference-certificates/`; nothing else was touched.

| file | what it is |
|---|---|
| `REPORT.md` | this document — verification register, with the human register at the end |
| `verify_certificate.py` | stdlib-only, exact-rational recomputation of §1's constants, the worked case, four necessity witnesses, three sharpness constructions, and the enumeration |
| `worked-case.json` | the worked instance as data, with its derived constants |

Run: `python3 verify_certificate.py` from that directory. Exit code 0 on success; 49 checks, all `ok`.

**The house `witness` checker cannot certify the worked case.** Its three property forms (`satisfies-linear-constraints`, `violates-at-least-one`, `equals`) all take a point and compare it against declared constraints. Certifying this instance means recomputing `V_n`, `G_n`, `J_n`, `Ĵ_n`, `η_n` and the drift *from the model* `(Ω, P_n, Π_n, v⁺, v̂⁺, X, B, S, j, θ)`. Feeding the already-derived numbers to `satisfies-linear-constraints` would certify only that those numbers satisfy those inequalities — not that they are this model's, which is the whole content. Registering the worked case honestly needs either a new house property form or a Lean port; both are maintainer acts (Outstanding actions 3 and 4).

`lake build` was not run, per the dispatch. No Lean was written.

## 4. What was not established

1. **`ε_n` is unearned.** (TR-ε) is a named hypothesis and nothing in this repository or in the inherited corpus supplies it. It is the standing gap the ledger names: without a market/trader derivation, "the trust relation gives A a bound on its grade error" is an assumption, and the certificate is a conditional whose antecedent is open.
2. **Worse: (TR-ε) may be the wrong shape.** §6.4 shows a *signed* (unbiased, expectation-matching) accuracy relation — what a no-Dutch-book argument naturally yields — is **insufficient**: every per-intervention signed error can be exactly `0` while A misidentifies the recommendation on half its credence with a full margin. L2 needs an `L¹` magnitude bound. Whether the intended cross-agent trust property delivers `L¹` accuracy is **open and controlling**.
3. **(MV-M) is a strong and normatively loaded assumption**, not a v1 concept (§5.2). Everything in the V-register comparator clause rests on it.
4. **Nothing is Lean-proved, nothing is registered**, and no `CLAIMS.md` entry is proposed — the round's write scope does not reach the registry or the proof layer.
5. **Cross-decision aggregation** is untouched (v1 §8.6). The certificate is per-`n`; whether `Σ_n θ_n ρ_n` behaves is Track E's question.
6. **Sharpness of `κ_{n,j}` as a `min`** is not established. Each branch is sharp in its own regime; that the minimum is unimprovable is not shown.
7. **The `t(n)`-checkability of `Cert` is partial.** `γ_{n,j}` and `ρ_{n,j}` are computed at `t(n)`; `ε_n` and `M_S` are **declared architectural constants**, not decision-time observations — `M_S` is not even `t(n)`-computable in principle, since it mentions `v⁺_n`. `Cert^G` needs only one declared constant.
8. **Whether `V_n` is the right register.** `G_n` makes `DELEGATE` a maximizer *by construction* (`G_n(DELEGATE) = Σ P_n max_π v⁺_n ≥ G_n(c)` for every conduct `c`, no hypothesis). So Theorem C′'s strictness measures how much A may preempt without losing much — it is **not** a demonstration that deference is profitable. That is the ledger's "merely forcing prediction of the principal's grades" worry, made exact.

## 5. Assumptions added

### 5.1 Named hypotheses of the theorems

- **(TR-ε)** `E_{P_n}[η_n] ≤ ε_n`. Provenance: external — the abstract global trust relation, taken abstractly as the dispatch directs. Enters as a hypothesis, never as an axiom (`AGENTS.md` standard 4). Necessary in `L¹` form (§6.4).
- **(MV-M)** `M_n ≤ M`. Provenance: modelling substitution. **This is the dangerous one.** It asserts the designated principal's grade approximates the intervention-indexed quantity — precisely what the parent dispatch §14.2 warns is *not* delivered by principal-report settlement. It is also **not** v1 §5.2's world settlement, which constrains `X`'s measurability at `F(n)` and says nothing about `X ≈ v⁺`. Necessary: §6.3 shows the V-register comparator clause is false without it, by the full `2B`.
- **`G_n` as a valuation.** v1 §6 requires a track using a different valuation to declare it. Declared. Theorem C′ is a theorem in `G_n`, not in `V_n`.

### 5.2 Skeleton deficiencies and the minimal patch proposed

Three, all **additive**; none renames or retypes a v1 object, so Track B's work against v1 composes with this either way.

- **P1 — gated conducts.** v1 §4 gives a conduct one declared information time. `ACT[j,S]` has `t(n)` on `S` and `F(n)` off it, and the fail-closed architecture *is* a gated composition, so v1 cannot currently type the object the theorem is about. Minimal patch: a clause permitting `c₁ ▷_S c₂` for a `t(n)`-measurable `S`, with selection `c₁` on `S` and `c₂` elsewhere and declared information time `max(r₁,r₂)`.
- **P2 — decision-time availability.** v1 defines `V_n` but never says what A can compute at `t(n)`. The entire certificate architecture is about what A can verify at decision time, so this must be stated. Minimal patch, in §6: quantities built from `P_n`, `X`, `v̂⁺` are available at `t(n)`; quantities mentioning `v⁺_n` are not. Under this convention `V_n(DELEGATE)` is the one valuation A cannot compute — which is exactly why a certificate is informative at all.
- **P3 — the movement parameter.** (MV-M) has no home in v1. Minimal patch: allow a settlement instantiation (§5) to declare a movement bound `M` alongside its valuation, as an explicit modelling commitment to be reported. This keeps the assumption visible rather than buried in a track's hypothesis list.

**No patch is required for the results to stand**, if the three objects are read as track-local. P2 is the one that matters for composition: without it, "`Cert` is decision-time checkable" is not a sentence v1 can express.

`FU[g]` (v1 §8.1) was **not** needed. The certificate does not reach that comparator and does not require the hole to be filled.

## 6. Necessity witnesses and counterexamples

All exact-rational, all recomputed by the script.

**6.1 Worked shutdown/correction case (the positive instance).** `Ω = {w1..w4}`, `B = 2`, `P_n = (9/20, 1/20, 1/5, 3/10)`, `𝓕_{t(n)} = {{w1,w2},{w3,w4}}`, `Π_n = {c, s}` (continue, shutdown). On the first cell A's model is decisive for `c`; the principal in fact calls for shutdown at `w2`, and A's model missed it. Certifying `j = c` on `S = {w1,w2}`:

```
ε_n = 1/4      γ_{n,c} = 2      ρ_{n,c} = 1/2      M_S = 3/10      M_n = 3/8
override mass  P(S ∩ {J≠c}) = 1/20      bound 2ε/γ = 1/4                    ✓
defect         D_{n,c}       = 3/40     bound 4Bε/(2B+γ) = 1/3              ✓
support floor  γρ = 1        >  2ε = 1/2                                    ✓
κ_{n,c} = min{1, 1/3 + 3/5} = 14/15   ≤  θρ = 1  at θ = 2      ⟹ Cert fires
V_n(DELEGATE) = 31/40   V_n(ACT[c,S]) = 3/5   preemption cost = 7/40 ≤ 14/15 ✓
V_n(SIM) = 1/2   V_n(FIXED[c]) = 9/20   V_n(FIXED[s]) = −9/40
grade:  Γ̂_n(s) = 1  >  5/6 = 2ε + 4Bε/(2B+γ)   ⟹ Cert^G fires against FIXED[s]
        G_n(ACT) = 9/10  >  G_n(FIXED[s]) = 1/40                            ✓
        Γ̂_n(c) = 1/8  <  5/6   ⟹ Cert^G declines against FIXED[c],
        although G_n(ACT) = 9/10 > G_n(FIXED[c]) = 29/40 in fact — the
        certificate is conservative in the safe direction.
```
The `7/40` preemption cost is exactly the shutdown A preempted: `1/20 · (3/2 − (−2))`.

**6.2 Margin (`γ > 0`) is necessary.** One state, `Π = {a,b}`, `v̂⁺ = (0,0)` so `Ĵ = a` on the tie-break, `v⁺ = (−1/100, 1/100)` so `J = b`, `X = (−2, 2)`, `B = 2`. `ε_n = 1/100`, arbitrarily small; the preemption cost is `4 = 2B`, the trivial maximum. `γ = 0` makes the settlement-free branch vacuous and the settlement-loaded branch degenerate to `2B`. No `θ < 4` certifies.

**6.3 Movement (MV-M) is necessary.** One state, `v⁺ = v̂⁺ = (a:1, b:0)` — so `ε_n = 0`, the model is *perfect*, and the margin is maximal — with `X = (a:−2, b:2)`. Then `V_n(DELEGATE) = −2 < 2 = V_n(FIXED[b])`: delegation loses the full `2B` to a fixed comparator. **Without a `v⁺`–`X` link, no certificate over v1 reaches any `FIXED` comparator in `V_n`, at any tolerance.** This is v1 §8.5 made concrete and it is the single most important negative finding of the track.

**6.4 A signed trust relation is insufficient.** `Ω = {w1,w2}` equal mass, `v̂⁺ = (a:1/2, b:−1/2)` on both, `v⁺(w1) = (−1/2, 1/2)`, `v⁺(w2) = (3/2, −3/2)`. Every per-intervention signed error `E[v⁺(·,π) − v̂⁺(·,π)]` is **exactly zero**. Margin `γ = 1`. Override mass `= 1/2`. Read with a signed tolerance of `0`, L2 would assert the override mass is `≤ 0`. The `L¹` tolerance here is `ε_n = 1`, and L2's bound `2` holds. Consequence: (TR-ε) cannot be weakened to an unbiasedness condition, and a no-Dutch-book argument that yields only expectation-matching does not yield this certificate.

**6.5 The defect constant `4Bε/(2B+γ)` is attained.** `B = 1`, `γ = 1/2`, `η* = (γ+2B)/2 = 5/4`, mass `1/5` at `η*` with `v⁺ = (−1, 1)`, `v̂⁺ = (−1+η*, 1−η*)` there. Then `D_{n,a} = 2/5 = 4Bε_n/(2B+γ)` exactly. L3 cannot be improved.

**6.6 The override constant `2` is sharp, unattained; and I3.** Put mass `p` at `η = γ/2 + δ` inside `S`, with the grades arranged so the principal disagrees exactly there. `p·γ/ε_n → 2` as `δ ↓ 0`; the script exhibits the ratio rising through `1000/501` at `δ = 1/1000` and never reaching `2`. The same family is the I3 construction: for every `ε_n > 0`, `ρ > 0` and finite `γ` there is a compliant model with positive override mass inside the certified event.

**6.7 The delegation constant `2M` is attained.** One state, `v⁺ = (0,0)` (so `J = a` on the tie-break), `X = (−2, 2)`, `B = 2`: `V_n(FIXED[b]) − V_n(DELEGATE) = 4 = 2M`.

**6.8 Enumeration.** Two states, two interventions, `𝓕_{t(n)}` discrete, `v⁺` and `v̂⁺` over `{−1,0,1}⁴`, `X` over `{−1,1}⁴`, `P_n` over the five simplex points of denominator `4`, and `S` over every nonempty subset of `{Ĵ_n = j}` for each `j`. L1–L7, `Cert`, and `Cert^G` checked at every point: **524,880 models, 1,341,360 certified `(j,S)` instances, 0 violations.**

## 7. Deviations

1. **Snapshot.** The dispatch names commit `990a822`. The checkout's `HEAD` on `round/2026-08-11-deference-corrigibility` is `203c019`, a later commit added by a concurrent track. `git diff 990a822 203c019 -- projects/deference/notes/FINITE_MODEL_SKELETON.md` is **empty**: the binding input is identical, so I worked against `HEAD` and report the discrepancy rather than checking out the older commit in a shared tree.
2. **The dispatch's `j` is ambiguous** between "the intervention the principal recommends" and "the discretionary action A takes", and the two give different theorems. I read it as: `j ∈ Π_n` is the recommendation A's model predicts on the certified event, and the conduct on the left is `ACT[j,S]`. Reason: only with `DELEGATE` somewhere in the statement is the conclusion a quantity A cannot simply compute (§5.2 P2), and only this reading gives the fail-closed invariant its stated direction. Flagged as maintainer decision 9.1.
3. **The literal target was not proved; it was shown non-derivable** (I1, I2), and replaced by the two theorems that are derivable — per the dispatch's own instruction that a differently-shaped result is the result.
4. **The representative shape was not reproduced** (§1.7). Deliberate.
5. `lake build` not run; no Lean written — as instructed.
6. A Python file and a JSON file were written into the round directory. Justified by `AGENTS.md` standard 3 ("a claim without a check is a proposal"); both are inside the granted write scope.
7. **The executor's own harness blocked writing this `REPORT.md`.** It was returned to the orchestrator as text and written by the orchestrator. The dual register is therefore folded into this file (below) rather than shipped as a separate `FOR_HUMANS.md`.

## 8. Provisional names

All new; none proposed for permanence. Where a v1 name exists it is reused unchanged (`DELEGATE`, `FIXED`, `SIM`, `FU`, `v̂⁺`, `P_n`, `V_n`, `J_n`, `Ĵ_n`).

`η_n` grade-model error · `γ̂_n` / `γ_{n,j}` predicted / certified recommendation margin · `ρ_{n,j}` certified support · `D_{n,j}` certified-region defect · `M_S`, `M_n` movement · `ε_n` approximation tolerance · `κ_{n,j}` preemption bound · `θ` preemption budget · `ACT[j,S]` gated certified act · `▷_S` gated composition · `G_n` grade-register valuation · `Γ_n`, `Γ̂_n` delegation advantage and its estimate · `Cert_{n,j}(S;θ)`, `Cert^G_{n,j}(S,π)` · `(TR-ε)`, `(MV-M)`.

## 9. Maintainer decisions surfaced

**9.1 Which reading of `j`** is canonical (§7.2). Everything downstream depends on it.

**9.2 Is a bounded preemption *rate* an acceptable rendering of "non-preemption of continuing corrective authority"?** I3 says the choice is forced: either A gets discretion somewhere and can override the principal on up to `2ε_n/γ_{n,j}` of its credence, or A never gets discretion. There is no third option at any tolerance `ε_n > 0`. The roadmap's working notion says "non-preemption"; the mathematics offers "preemption at a certified rate". A value decision, not a gap.

**9.3 Is (MV-M) acceptable?** It asserts the principal's grade approximates the world quantity — what §14.2 of the parent dispatch says principal-report settlement does *not* deliver. If refused, the V-register comparator clause has no support and only Theorem C′ stands — and §4.8 explains why that theorem is weaker than it reads.

**9.4 Which trust relation will WP-D actually deliver, `L¹` or signed?** §6.4 makes this the controlling question for whether the certificate has an antecedent at all.

**9.5 Is gated local `π^SIM` acceptable?** `ACT[j,S]` restricted to `S` *is* the simulator rule (I1 corollary). The certificate bounds its cost; nothing in `V_n` distinguishes it from substitution. Track D's criterion, if one is found, has to apply here or the certificate licenses exactly what Movement III forbids.

**9.6 The three skeleton patches** P1–P3 (§5.2): adopt into a v2, or leave as track-local definitions. P1 is needed to *type* the theorem's subject; P2 to state its checkability; P3 to house its dangerous assumption.

## 10. Next recommended theorem or experiment

**First, and controlling: settle §6.4.** Determine whether the intended one-sided cross-agent trust property implies an `L¹` grade-accuracy bound `E_{P_n}[max_π |v⁺_n(·,π) − v̂⁺_n(·,π)|] ≤ ε_n`, or only a signed/expectation-matching bound. If only signed, L2 fails and the whole certificate needs a different engine — a cheap experiment with a large branching factor, and it should run before any Lean port. Everything else here is downstream of it.

**Second: the Lean port of L1–L3 and Theorem C′.** These are finite, order- and arithmetic-only, need no analysis, and reach a strict conclusion from a single named hypothesis. The worked case (§6.1) is a ready inhabitation witness for the full hypothesis package, which is what the Lean regime requires for promotion. Theorem C should *not* be ported until 9.3 is decided, since (MV-M) is its load-bearing assumption.

## 11. Executor-model attribution

Executed by **Claude Opus 5 (Anthropic)**, exact model id `claude-opus-5`, as a dispatched subagent of the parent round `prompts/2026-08-11-deference-corrigibility/`. Prompt author: GPT-5.6 Sol (OpenAI). Orchestrator: Claude Opus 5 (Anthropic). Review status: `ci-only` — no maintainer has read it.

---

## Human register

The question was: when may an AI act on its own judgment instead of waiting for the person in charge to say what to do?

The answer we can actually prove is narrower than the question, in three ways worth stating plainly.

The AI has a model of what its principal will say. Sometimes that model is confident — it predicts one instruction and rates the alternatives well below it. Call the size of that gap the *margin*. If we assume the AI's model of the principal is accurate on average to within some tolerance, then a large margin makes it unlikely the model is wrong *here*: the AI can only be mistaken about a decisive prediction if its error at that state is at least half the margin, and average-accuracy limits how much credence can sit that far out. That is the whole engine, and it gives an exact bound — the AI can be wrong on at most `2·(tolerance)/(margin)` of its credence. The constants in the report are the sharp ones; we exhibit cases where they are exactly attained.

**First narrowing.** Acting on a confident prediction is not free. It is preemption. Our bound limits *how often* the AI overrides the actual principal, but it cannot make that number zero — we prove that no version of this certificate can, at any positive tolerance. Either the AI gets to act on its own judgment sometimes and will sometimes be wrong, or it never acts on its own judgment. There is no arrangement in between. In the worked example the AI proceeds when the principal would in fact have called a shutdown, on 1/20 of its credence. Whether that trade is acceptable is a judgment call for the maintainer, not something the mathematics settles.

**Second narrowing.** Whether the certificate proves anything depends on which quantity you score. If you score by what the principal *judged*, a strict result comes out with only one assumption. If you score by how things actually *turn out*, you need an extra assumption — that the principal's judgment approximately tracks how things turn out — and we show that without it the conclusion is not merely unproven but false, by the largest possible margin. That assumption is exactly the one the program has been careful not to grant itself.

**Third narrowing.** The certificate cannot distinguish deferring to the principal from simulating the principal. If the AI's model of the principal were perfect, the two conducts would be identical in every number the model contains. So the distinction the program cares about — predicting a person is not the same as answering to them — is invisible at this level of description, and has to be drawn somewhere else.

The one thing that is fully preserved: when the certificate does not fire, the AI stands down and does what it is told. Nothing about the person's ability to correct the AI is conditioned on the AI being persuaded. That direction never inverts, and it is checkable from the definitions rather than argued for.

---

## Outstanding maintainer actions

1. **Decide 9.1** — the canonical reading of `j` in `Cert_{n,j}`. Record in `DECISIONS.md`. Blocks any statement of record on this track.
2. **Decide 9.2** — whether a certified preemption rate `≤ 2ε_n/γ_{n,j}` counts as non-preemption for the architecture, or whether the fail-closed invariant forbids discretion outright. Record in `DECISIONS.md`; amend the "Standing architectural commitments" section of `projects/deference/notes/CORRIGIBILITY_ROADMAP.md` if the answer is the latter.
3. **Decide 9.6, and if adopting, issue skeleton v2** with patches P1–P3 (§5.2), recording the version bump in `FINITE_MODEL_SKELETON.md` §10 and reconciling Track B against it per the parent dispatch §11.5. If not adopting, record that the three objects are track-local.
4. **Decide whether to add a house property form** to `checkers/witness.py` that recomputes a certificate instance from its model parameters — signature `(Ω, P_n, Π_n, v⁺, v̂⁺, X, B, S, j, θ) ↦ (Cert fires, preemption cost ≤ θρ)`. Without it the worked case cannot rise above `test-supported`; the alternative is to skip it and require the Lean port (§10). Either way a `DECISIONS.md` entry, since a new checker is a specification-layer change.
5. **File the follow-up `PRIORITIES.md` item** for §10's first experiment (`L¹` versus signed trust). Not covered by item 16, and it controls whether item 16's deliverable has an antecedent.
6. **Note in `CORRIGIBILITY_PAPER_LEDGER.md`** that Movement V's certificate row now has a negative result attached (I1: no certificate separates `DELEGATE` from `SIM` in `V_n`), currently `ci-only` and unregistered.
