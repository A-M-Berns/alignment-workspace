# Compiling the mediated system into Logical-Induction objects

Every Logical-Induction statement below is cited by its label in arXiv:1609.03543 v5
(`notes/1609.03543v5-main.tex` of the pinned `Formalized-Agent-Foundations`) and, where
the pinned formalization has the object, by its Lean name.  Nothing is stated from memory.

## 1. Representation

**The LUV type is closed under everything needed.**  `def:luv`: a LUV is *any* formula
`X` free in one variable with `Γ ⊢ ∃x (X(x) ∧ ∀x' (X(x') → x' = x))`; a `[0,1]`-LUV
additionally has `Γ ⊢` the value in `[0,1]`.  Its value in a consistent world `W` is
`W(X) := sup{x ∈ [0,1] : W(⌜X ≥ x⌝) = 1}`.  So:

| quantity | formula | `[0,1]`-LUV because |
|---|---|---|
| activation `c` | `𝟙(φ_c)` (the paper's indicator LUV, `thm:ei`) | `φ_c` is a sentence |
| activated security `U = c·w/D` | `⌜ν = (if φ_c then w̃/D else 0)⌝` with `w̃` the value formula of the evaluation | a definable case split on a sentence and a `[0,1]`-LUV |
| gated discrepancy `G_δ = both·δ/δ_max` | `⌜ν = (if φ_raw ∧ φ_corr then δ̃/δ_max else 0)⌝` | the same |
| gated regret `G_ρ = both·(w̃_app − w̃_act)₊/D` | the same shape | the same |
| directional mismatch `G_M` | `𝟙(φ_raw ∧ ¬φ_corr)` | a sentence |
| raw-minus-corrigibilized difference | the LUV-combination `U_raw − U_corr` | affine in LUVs |

A product `c·δ` is therefore **not** compiled as a product of two LUVs inside an affine
combination — the combination is affine only in its variables — but as *one* gated
variable whose defining formula already contains the case split.  This is the
prompt's first route and it needs no closure theorem: `def:luv` quantifies over
arbitrary formulas.  The obstruction the prompt anticipated (pressure test 9) does not
exist at the paper's level.

**World values of gated variables.**  For `W ∈ PC(Γ)`: if `W(φ) = 1` then
`W(G) = W(X)`; if `W(φ) = 0` then `W(G) = 0`.  Proof by thresholds: `Γ ⊢ φ → (G ≥ r ↔
X ≥ r)` and `Γ ⊢ ¬φ → (G ≥ r ↔ r ≤ 0)` for every rational `r`, and a p.c. world consistent
with `Γ` respects every provable implication, so the cut defining `W(G)` is the cut
defining `W(X)` or `{r ≤ 0}`.  The same argument gives products, sums and clamps of
LUVs their expected world values in every world, nonstandard ones included, because
every step compares rational thresholds only.

**At the pinned formalization.**  The abstract `LUV` is a threshold family
`gt : ℚ → Sentence` (`Framework/Expectations.lean`), with no internal arithmetic; the
literal first-order frontend (`PaperLUV`) documents that arithmetic closure *between*
LUV values is outside its scope.  The round supplies the gating at the threshold level:
`GatedAt v G φ X` (below `0` every threshold of `G` holds; at `r ≥ 0`, `G > r ↔ φ ∧ X > r`),
`IndicatorAt v Y ψ` (the pointwise form of the pinned `LUV.IsIndicator`), with concrete
families `gate φ X`, `indicator ψ`, `constLUV q` that satisfy them in every world, and the
compiler lemmas `GatedAt.valuesAt` (`W(G) = if W(φ) then W(X) else 0`) and
`IndicatorAt.valuesAt`.  These are **LEAN** (`LICorrigibility.lean` §2).  What is *not*
supplied in Lean is the object-level derivation of `GatedAt` from a first-order definition
of `G` — that is exactly the arithmetic-closure scope boundary of the frontend, and it is
where a Lean port of the paper-level argument above would go.

## 2. Efficient generation

The exact class of `thm:expprovind` is `BLCS` (`def:blcp`): a `P`-generable
`ℝ`-LUV-combination sequence bounded in `ℓ¹` including the trailing coefficient.
`P`-generable (`def:ece`, applied to LUV-combinations per the paper's "defined
analogously"): an e.c. `𝓔𝓕`-progression `(B̂_n)` — the day-`n` object emitted by a
poly-time function of `n`, its coefficients expressible features of rank `≤ n`, its
LUVs part of the emitted syntax — with `B̂_n(P̄) = B_n`.  Expressible features (`def:tf`):
price features, rational constants, `+`, `×`, `max`, safe reciprocation
`max(1,·)⁻¹`; continuous by construction.

| condition | the compiled sequence | verdict |
|---|---|---|
| e.c. emission of the LUVs | `U_raw,n`, `U_corr,n`, `G_δ,n`, `G_ρ,n`, `G_M,n` are fixed formula templates instantiated with the codes of `π_n`, `𝔠π_n`, the occurrence index and the horizon; `𝔠π_n` is a syntactic interposition on `π_n`'s move stream, linear in the size of `π_n`'s description (the 2026-09-09 `lift`) | yes, if `n ↦ π_n` is e.c. |
| coefficients | constants `1, −1, −λ_n, −1, −1`; `λ_n = L_n δ_max,n / D_n` an e.c. rational sequence | rank `0` features; `P`-generable trivially |
| `ℓ¹` bound | `3 + λ_n` | bounded iff `λ_n` is; uniform `L, δ_max, D` suffice |
| `P`-continuity | constant coefficients | vacuous |
| interaction semantics | one uniform formula template per quantity, parametrized by the codes | compiled uniformly |
| menu growth (T3′) | `|Q_n|` LUVs and `|Q_n|` weight features per day; each weight references the shared maximum and normaliser (sharing via the pinned `EF.letE`) | polynomial iff `|Q_n| ≤ poly(n)`; the `ℓ¹` bound is `3 + λ` because the weights sum to one |

The soft weights are expressible: `ramp_δ(x > y) = min(1, max(0, (x − y)/δ))` uses `max`,
constants and `min = −max(−·,−·)`; the score `s_q = E_n(B_q)` is
`Σ_{X} α_X·(1/(n+1))·Σ_{i ≤ n} P_n(⌜X > i/(n+1)⌝)`, a sum of `O(n)` price features per
variable; the menu maximum is an iterated `max`; the normaliser `1/Σ_q ramp(·)` is the
safe reciprocal, exact because the argmax's ramp is `1` so the sum is at least `1`.  A
hard argmax is not expressible (discontinuous, **FIX**).

**Not shown in Lean.**  The pinned `LUVCombination.PolySequence` requires the expanded
threshold mesh to be an `AffineCombination.PolySequence` (poly-fueled emission with
`RpnSpliceStream` serialization).  Building that certificate for the compiled templates
is the same labour the pinned library spends on its own witnesses
(`Construction/Witnesses/`), and is not done here; `li_bypass_le` takes `BoundedSequence`,
`MeshSoftmaxOperationalWitness` and `RpnThresholdCodes` as named hypotheses, which is
the `AGENTS.md` standard-4 form for imported theory.

## 3. Semantic validity: what `Γ` must contain

`thm:expprovind` asks that `W(B_n) ≤ 0` for every `W ∈ PC(Γ)` and every `n`.  `PC(Γ)` is
the set of propositionally consistent worlds making every sentence of `Γ` true — by the
paper's own remark, the worlds `W` with `Γ ∪ {φ : W(φ)=1} ∪ {¬φ : W(φ)=0} ⊬ ⊥`.  It does
**not** ask that `D̄_n` contain a proof of any instance: the deductive process enters
only through the criterion (`PC(D̄_n)` in `def:exploitation`) and through
`Γ`-completeness `PC(D̄_∞) = PC(Γ)`.  So the inequality is learned "in a timely manner"
however slowly the instances are proved.

For `W(B_n) ≤ 0` to hold in every consistent world it suffices that
`Γ ⊢ ⌜B_n ≤ 0⌝` (object-level, by the threshold argument of §1); for a finite
interaction with a finite input space this is a finite universal statement `Γ` decides.
Its truth needs the following in `Γ`, as **definitions or theorems about the modeled
system**:

| ingredient | role | status in `Γ` |
|---|---|---|
| the physics transition program and the declared effect semantics (EX) | fixes the trajectories `Ω(π_n, z)`, `Ω(𝔠π_n, approve, z)` | a definition of the model; EX is the statement that the release function is the declared one |
| the gate and latch programs (MS, DP) | fixes the approve branch and its bookkeeping | a checkable theorem about the programs |
| activation semantics and expiry | defines `φ_raw,n`, `φ_corr,n` as sentences about the log through the horizon | a definition |
| the evaluator's `L`-stability certificate | the `(1,1)`-branch inequality | a theorem about the committed principal program and `d_prot`, finite to check per `n` |
| the definition of `ρ` | the `(1,1)`-branch inequality | a definition, `ρ = (w_app − w_act)₊` |
| the coupling | `M` is the joint event in one world | automatic: `W(U_raw,n)` and `W(U_corr,n)` are read in the same `W` |
| effect completeness (EF) | **not needed for `B_n ≤ 0`** | needed for T1's corrigibility of `𝔠π`; a theorem of the model when the model's move set is finite; an **EXT** contract about the real interface |

So the inequality's validity rests on MS, EX, activation semantics and the stability
certificate; EF is what makes the *corrigibilized* option corrigible (T1), not what
makes the market respect the inequality.  On fixture F (an undeclared effect),
`𝔠π_F = π_F`, `B = 0`, and T3 is vacuously true and silent.

**Effect completeness, classified** (the prompt's four readings): (i) as an axiom of the
modeled system it is a finite universal over the model's moves, decidable in `Γ`; (ii)
as a claim about the real system it is an external guarantee that restricts the
theorem's scope to worlds in which the real interaction is the modeled one; (iii) it is
checkable in finite systems by enumeration of the move set and the loss predicate;
(iv) it is unformalized only in the sense that the real move set is not an object of
`Γ`.  The theorem applies inside the worlds satisfying the architecture specification
and says nothing outside them; if the real log ever contradicts the specification, the
deductive process reports a contradiction and the framework is over an inconsistent
theory.

**A conditional form.**  Where an architecture invariant is *log-checkable* (MS, EX on
logged states), the constraint can be gated on it: `𝟙(Arch_n)·B_n ≤ 0` holds in every
world without any axiom, and EPI yields the inequality on the worlds where the
invariants are recorded.  EF is not log-checkable — a loss is a counterfactual on the
transition model — so it cannot be moved into the gate.

## 4. The obstruction, stated exactly

There is no representational obstruction.  The obstruction to *mechanizing* T3 end to
end is the `P`-generability certificate at the pinned interface (§2, last paragraph) and
the object-level gating derivation at the threshold interface (§1, last paragraph);
both are formalization labour, not mathematics.  The obstruction to *applying* T3 to a
real system is that `Γ` must carry the system's specification (§3); that is the
architecture's contract, not the inductor's.
