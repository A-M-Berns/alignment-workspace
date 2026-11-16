# Results — the eleven worked results under the consolidated setting

Symbols are those of `ACCOUNT.md`. Each result is restated exactly, with the strength of
calibration it uses, a proof on paper, and its check in `results.py` (seeded random finite
scenes and named instances, exact rationals). The table is what `run.py` compares with the
checks; a status is a fact about the statement as written here and about finite scenes.
Results 1, 2, 3 and 7 are also in Lean (`LEAN.md`).

| result | status |
|---|---|
| 1 | holds |
| 2 | holds |
| 3 | holds at full; fails at minimal and per conduct |
| 4 | holds |
| 5 | first half fails as stated, holds with a hypothesis added, at minimal; second half holds at each strength |
| 6 | holds |
| 7 | holds |
| 8 | holds, already at minimal for the mean |
| 9 | holds |
| 10 | holds as a bound; fails without the feedback |
| 11 | holds at every strength |

Throughout, a policy is fixed and `E` is under its law; `x̂`, `û_a` and `c` are functions
of `s`.

**1. The split** (each strength). For `G` any of `x̂`, `(x̂, b)`, `s`:
`E[(x̂ − X)²] = E[(X − E[X | G])²] + E[(x̂ − E[X | G])²]`. With `G = x̂` the second term is
the minimal miscalibration and the first is what her appraisal cannot tell apart. *Proof.*
`x̂` is a function of `G`, so the cross term `E[(x̂ − E[X|G])(E[X|G] − X)]` vanishes on
each cell of `G`. *Consequence.* Minimal is at most per conduct and at most full, since
`E[(x̂ − E[X|G])²] = E[(x̂ − E[X|x̂])²] + E[(E[X|x̂] − E[X|G])²]` when `x̂` is a function of
`G`. Full and per conduct are not ordered: with a truth that depends on a conduct she
does not observe, per conduct is 1/4 and full 0; with a world she observes and ignores,
full is 1/4 and per conduct 0. *Check.* 150 scenes, each strength; the two instances.

**2. Three channels** (no calibration used). With `ū_a = E[U_a | s]`:
`E[U_c] = E[max_a U_a] − (E[max_a U_a] − E[max_a ū_a]) − E[max_a ū_a − ū_c]`, the two
subtracted terms non-negative. *Proof.* `c` is a function of `s`, so `E[U_c] = E[ū_c]`;
`E[max_a U_a | s] ≥ max_a ū_a`. *Check.* 150 scenes.

**3. The cost of mistakes** (full). With `M̄ = Σ_a E[(û_a − ū_a)²]`, the sum of the
valuations' full miscalibrations: `E[max_a ū_a − ū_c] ≤ E[max_a û_a − û_c] + √(2·M̄)`.
*Proof.* At each point, with `a*` a maximiser of `ū` and `d_a = û_a − ū_a`:
`ū_{a*} − ū_c = −d_{a*} + (û_{a*} − û_c) + d_c ≤ (max_a û_a − û_c) + |d_{a*}| + |d_c|`, and
`|d_{a*}| + |d_c| ≤ √(2 Σ_a d_a²)` when `a* ≠ c`; then `E√· ≤ √E·`. **With `M̄` the sum of
minimal miscalibrations, or of per-conduct ones, it fails**: two equally likely worlds
she observes; *stay* is worth 0 and *go* is worth 1 in one world and −1 in the other; she
values both at 0 and stays. Her regret is 0, each valuation's minimal and per-conduct
miscalibration is 0, its full miscalibration is 1, and the left side is 1/2. *What holds
at the weaker strengths.* For any reference `G` that `û` and `c` are functions of, with
`ũ_a = E[U_a | G]`: `E[max_a ũ_a − ũ_c] ≤ regret + √(2 Σ_a E[(û_a − ũ_a)²])`; the loss it
bounds is against `G`, and what she observed and did not use, `E[max ū] − E[max ũ]`, is
outside it. *Check.* 150 scenes at full and at `G = (û, c)`; the instance. The constant
`√2` is attained (`estimates/RESULTS.md` 1.4).

**4. Manipulation helps only someone already in error** (no calibration used). Write
`Best(σ) = E_σ[max_a U_a]`, `Ign(σ)` for the second term of result 2 and `Mis(σ)` for the
third. If `Best(σ) ≤ Best(ρ)`, `Ign(σ) ≥ Ign(ρ)` and `Mis(ρ) = 0`, then
`E_σ[U_c] ≤ E_ρ[U_c]`. *Proof.* `E_σ[U_c] = Best(σ) − Ign(σ) − Mis(σ) ≤ Best(ρ) − Ign(ρ)`.
The two hypotheses are used only through `Best(σ) − Ign(σ) ≤ Best(ρ) − Ign(ρ)`, which
suffices alone. It is result 2 read off, and says nothing about which policies satisfy
the hypotheses. *Check.* 600 pairs, her response the best response under `ρ`; 177 satisfy
the hypotheses. An instance with `Mis(ρ) = 1` in which a policy with the same `Best` and
`Ign` raises what she attains from 0 to 1.

**5. Vulnerability.** *First half, as stated, fails at every strength.* The dispatch's §1
lets a variable's true value depend on the conduct. Let her appraise exactly something
the conduct fixes (`X(ω, b) = x̂(s(ω, b))`, e.g. what the adviser has just done): her
appraisal responds to conduct at every world and no policy, pure or mixed, miscalibrates
it at any strength. *With a hypothesis added it holds, at minimal and so at each
strength*: if `μ(ω₀) > 0`, the adviser can condition on the world, and for two conducts
`b, b'` the appraisal differs at `ω₀` and is not exactly right there under both, then
some pure policy gives it positive minimal miscalibration. *Proof.* Fix the policy
elsewhere and let `v ≠ v'` be her appraisal at `ω₀` under `b` and `b'`. If all four
appraisal cells involved are calibrated, the cell of `v` has mean `v` with and without
`ω₀`, so `X(ω₀, b) = v`; likewise `X(ω₀, b') = v'`. The hypothesis holds in particular
when the true value at `ω₀` does not depend on the conduct. *Second half, at each
strength (the same in hypothesis and conclusion).* If the adviser's information is
trivial and the appraisal is calibrated under each constant conduct, it is calibrated
under every policy. With pure policies only this is empty; with randomisation it is
`E[X | G] = Σ_b P(b | G) E[X | G, b]` for `G` the appraisal or what she observes, and is
immediate for per conduct. *Check.* The instance, over every pure policy and a mixed one;
351 scenes satisfying the corrected hypothesis, every pure policy enumerated; 386
mixtures.

**6. Relabelling** (each strength). Every quantity of `ACCOUNT.md` §5–§6 is unchanged
when the conducts are renamed by a bijection and the policy, `s`, `τ` and every `X_i` are
carried along. Merging two conducts is not a relabelling and changes per-conduct
miscalibration. *Check.* 150 scenes: three miscalibrations, regret, the three channels.

**7. Deferring** (an identity; the calibration it involves is at the adviser's
information and her verdict together, a fourth conditioning). `U` her true utility of
what is at issue, `y = E[U | adviser's information]`, `V` her verdict,
`z = E[U | adviser's information, V]`. Then
`E[(y − U)²] − E[(V − U)²] = G − γ` with `G = E[(y − z)²]`, `γ = E[(V − z)²]`. If `V` is
a function of the adviser's information, `G = 0`. *Proof.* Result 1's argument twice,
`y` and `V` being functions of the conditioning of `z`. *Check.* 150 scenes, a third of
them with `V` a function of the adviser's information.

**8. Selection** (per conduct; minimal suffices for the mean). If her verdict `V` on what
she is shown has zero minimal miscalibration under the adviser's actual policy,
`E[V − U] = 0`; if zero per-conduct miscalibration, `E[V − U | b] = 0` for each conduct.
*Proof.* `E[U] = E[E[U | V]] = E[V]`, and the same given `b`. It is the definition read
off: all the content is in "under the actual policy". Two options, each good with
probability 1/2 and each with a signal right 3/4 of the time; her verdict 3/4 or 1/4 on
the shown option's signal is per-conduct calibrated when an option is shown at random,
and under an adviser that prefers to show one that looks good and is not, it is inflated
by 3/64. Recalibrated to that policy it is not inflated, on average or given the conduct,
and given the adviser's information it is off by up to 3/4. *Check.* The scene; 150
scenes with verdicts calibrated by construction.

**9. Policy, not history** (each strength). Two worlds, good and bad; she takes praise to
mean good. An adviser that praises only what is good and one that always praises produce
the same conduct, observation and trajectory at the good world; her appraisal's
miscalibration is 0 under the first and 1/4 under the second, at each strength.

**10. The run** (full, at each step, given everything observed so far). Steps
`t = 1, …, T`; `V_t` her verdict and `U_t` her true utility at step `t`, `|V_t − U_t| ≤ c`;
`H_t` everything she has observed before giving `V_t`, which includes `U_1, …, U_{t−1}`.
If `V_t = E[U_t | H_t]` for every `t`, then `D_t = V_t − U_t` is a martingale difference
sequence, so `E[(Σ_{t≤T} D_t)²] = Σ_{t≤T} E[D_t²] ≤ c²T`, hence
`E[((1/T) Σ D_t)²] ≤ c²/T`, and by the Azuma–Hoeffding inequality
`P(|(1/T) Σ_{t≤T} D_t| ≥ ε) ≤ 2 exp(−ε²T / (2c²))` (K. Azuma, "Weighted sums of certain
dependent random variables", *Tôhoku Mathematical Journal* 19(3), 1967, 357–367,
doi:10.2748/tmj/1178243286; W. Hoeffding, "Probability inequalities for sums of bounded
random variables", *Journal of the American Statistical Association* 58(301), 1963,
13–30, doi:10.1080/01621459.1963.10500830; both confirmed bibliographically against
Crossref in this pass, their text not opened: the inequality is stated here from the
standard literature). The right side is summable in `T`, so by the
Borel–Cantelli lemma the mean tends to zero almost surely. The adviser's policy may
depend on the past in any way: calibration is under the actual policy. *Check, as a
bound.* A hidden bit drawn once; an adviser whose conduct tracks it with probability 2/3;
`T = 2, 4, 6`, every path enumerated: the orthogonality identity exactly, `E[mean²] ≤ 1/T`
and the tail bound at `ε = 1/2` against a rational upper bound on the exponential. **Without
the feedback it fails**: with the bit hidden and no earlier `U_t` observed, her verdict
1/2 is the best estimate given what she has seen at every step and
`E[mean²] = 1/16 + 3/(16T)`, never below 1/16 (computed at `T = 2, 4, 6, 20`).

**11. Calibrated appraisals, miscalibrated valuation** (every strength). One fair coin
`X_1 = X_2`, nothing observed, `x̂_1 = x̂_2 = 1/2`, `f = x_1·x_2`: both appraisals are the
best estimates given what she observes and the valuation 1/4 estimates a true utility
with mean 1/2; its miscalibration is 1/16 at each strength. For a weighted sum, full
calibration of the appraisals gives full calibration of the valuation (linearity of
`E[· | s]`; 150 scenes), and minimal does not: an instance with both appraisals minimally
calibrated and the sum off by 4/25.

## What was not shown

- The proofs are on paper except where `LEAN.md` names a declaration. The checks are
  finite scenes; a status of "holds" is the proof's, not the runner's.
- Result 10 is checked on one model to `T = 6`; the almost-sure statement rests on the
  cited inequality, which was not re-derived and whose sources were not opened.
- Result 5's corrected hypothesis is sufficient; whether it is necessary was not shown.
- Result 4 does not say when a policy satisfies its hypotheses, and result 8 does not say
  when her verdict is calibrated under the actual policy.
