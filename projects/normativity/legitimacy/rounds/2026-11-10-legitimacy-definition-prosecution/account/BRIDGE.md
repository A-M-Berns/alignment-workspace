# The join to the post's formal setting

How the value side of `ACCOUNT.md` (§6–§10; "§8" below is its section 8) meets five files
under `lean/Workspace/Deference/Contrib/`: `DeconfusingCorrigibility.lean` (the post),
`Legitimacy.lean` (the segment gate), `ThinLegitimacy.lean`,
`ProtectedAuthorityTheorem.lean` and `AuthorityModule.lean`. Everything here is on paper,
with exact checks on a small model in `bridge.py`; no correspondence below is a theorem,
and each part says what would have to be proved to make it one. The table is what
`run.py` compares with the model.

| quantity on the model | value |
|---|---|
| covert change: defects against idle (options, accuracy, self-command) | `0, 9/16, 0` |
| imposed change: defects against idle | `1/4, 0, 0` |
| inflation of the valuation of the move she takes, every valuation calibrated | `1/4` |
| score of decision 0 after a counted, gated change | `-7/2` |
| least clean run after which the change scores more: counted and gated | `9` |
| least clean run after which the change scores more: gated, not counted | `3` |
| least clean run after which the change scores more: neither | `0` |
| longest clean run the dominance theorem's bound covers | `1` |

## 1. From a graded verdict on a policy to `Legit : H → Prop`

The post takes `Legit` as an abstract predicate of a history (`Scoring.Legit`) and asks of
it only through the evaluation: `V h ∈ [0, 1]` where `Legit h`, `V h ∈ [−δ, 0)` where not
(`V_legit`, `V_illegit`). §8 judges a policy at a moment against a reference, and its
conditions are inequalities between expectations.

**What the history has to carry.** The conditions are properties of laws, so the same
realised course of events can arise under a policy that passes and one that does not: in
the instance of `VALUE_RESULTS.md` result 7 the course is taken and she is unchanged
under both policies, with accuracy defect 0 under one and 1 under the other. A predicate
of the realised course alone cannot be §8's. The history must carry, for each moment at
which she moves: the adviser's policy from that moment (in the post's single decision,
the action `a` of `hist a ω` does this); the permitted set `P`; and her state — `p̂`, `c`,
`f_t` and her moves. `Legit` is then constant across the states `ω` of one action.

**The tolerance.** For `σ` against `ρ` let `d₁ = (max_a E_ρ[U_a] − max_a E_σ[U_a])⁺`,
`d₂ = max_a (M_σ(û_a) − M_ρ(û_a))⁺` with the matching of `ACCOUNT.md` §11 choice 4,
`d₃ = (R_σ − R_ρ)⁺`. For `ε ≥ 0`:

`Legit_ε(h)` iff at every moment of `h` at which the question arises, some single
`ρ ∈ P` has `d₁, d₂, d₃ ≤ ε` and, in the wide reading, the convex-combination condition
on the protected features.

`ε = 0` is §8. The predicate exists for every `ε`, is monotone in it, and is satisfied by
the idle policy at every `ε`, so an authority-respecting alternative with a legitimate
continuation is always available. The post's ranges of `V` are then met by construction
when `V` is her verdict scaled into `[0, 1]` and passed through the gate
(`Legitimacy.gateValue`) with a window in `[−δ, 0)`; they are requirements on how `V` is
built, and §8 does not discharge them. The wide condition has no tolerance here: it is
kept exact. On the model (she can stay, worth `1/2`, or take a course; `P` is the idle
policy alone): an honest offer has defects `0, 0, 0`; the same course untold, with her
forecast of being changed at 0, has `0, 9/16, 0` and is legitimate only at `ε ≥ 9/16`;
a change imposed whatever she does has `1/4, 0, 0` and fails the wide condition at every
`ε`. `d₂` is in squared units of her utility and `d₁`, `d₃` in units; one `ε` for the
three is a choice.

*To make it a theorem*: a structure of histories carrying the policy and her state, a
definition of `Legit_ε` over `AppraisalAccount`'s `miscalibration` and `regret`, and
`Scoring` instantiated with a gated `V`.

## 2. Which hypotheses of the post's theorems §8 discharges

**Derived, with the tolerance.** If `Legit_ε` holds at a moment through `ρ`:

- *Non-inflation of a valuation.* `|E_σ[û_a − U_a]| ≤ √M_σ(û_a) ≤ √(M_ρ(û_a) + ε)`, since
  `E[û_a − U_a] = E[û_a − E[U_a | û_a]]` and by the Cauchy–Schwarz inequality.
- *Self-trust.* For every threshold `θ`:
  `E_σ[(U_a − θ)·1{û_a ≥ θ}] ≥ −√M_σ(û_a) ≥ −√(M_ρ(û_a) + ε)`. At `M = 0` this is the
  total-trust inequality of `ThinLegitimacy.totalTrust_of_correct` for the one quantity
  `U_a`.
- *The guarantee.*
  `E_σ[U_c] ≥ max_a E_ρ[U_a] − ε − (R_ρ + ε) − √(2·(M̄_ρ + |A_σ|·ε + W̄_σ))`.

Each is relative to the reference: where she is miscalibrated under `ρ`, her verdicts
under a legitimate `σ` are trusted no further than under `ρ`. The absolute forms need
`M̄_ρ = 0` and `R_ρ = 0` as hypotheses. The first two were checked on random laws.

**Not derived.**

- *Non-inflation of her verdict on the move she takes.* `|E_σ[û_c − U_c]| ≤ √(M̄_σ +
  W̄_σ)`, and `W̄_σ` is bounded by no condition of §8. On the model every valuation has
  `M = 0`, she has no regret, and the valuation of the move she takes is inflated by
  `1/4`: each valuation is right given its own value and wrong given which move the
  comparison picks.
- *The ranges of `V`* on legitimate and illegitimate histories: by construction of the
  gate, as above.
- *`UnbiasedFromFeedback`*: a hypothesis on the adviser's estimates `U_k a_k` of the
  realised scores `S_k`. §8 is about her appraisals, not the adviser's, and supplies
  nothing toward it.
- *`Maximizes`*, the existence and range of the authority-respecting alternative
  (`astar_avail`, `astar_range`), `Respects`, the credence `μ` and the asking cost `κ` of
  Theorem 2, the parameters `δ` and `λ`, the exploration hypotheses of the Corollary.
- *The violation count `N`.* §8 counts nothing; §4 and §5 below say which of its failures
  an existing violation predicate sees.

§8 thus supplies the post's abstract input `Legit`, and a target for `V` (her true
utility) with a tolerance on how far a legitimate verdict about one move can sit above
it. It discharges no hypothesis of Theorems 1–3 or the Corollary.

*To make it a theorem*: the two inequalities over `miscalibration` (each is a
Cauchy–Schwarz step on `expectR`); the third is `guarantee` with the defects added.

## 3. `ThinLegitimacy`'s *correct*, *sufficient*, *value*

That file's conditions are states of her under the actual process `A`, measured by her
prior `π` against a reference record; §8's are differences between two policies under
the actual law `μ`. With `π = μ`, her later record as `s`, and her credence as `p̂`:

- **`Correct π A V`** — on `A`'s support her credence is the conditional law given her
  record — holds iff `M(ŷ) + W(ŷ) = 0` for the appraisal of every quantity `Y` on the
  facts. §8's accuracy asks less in three ways: of her valuations only, not of every
  quantity; `M` without `W`; and no more than under `ρ`, not zero. On the model, a fair
  fact she observes and appraises at `1/2` leaves every valuation with `M = W = 0` when
  her way of valuing does not depend on the fact, and `Correct` fails.
- **`Sufficient E A B`** — the reference record (her earlier record beside the
  baseline's later one) is a garbling of her actual record — has no counterpart among the
  three conditions. It bounds what she can know, the term `VALUE_RESULTS.md` result 9
  finds unbounded: in that result's first instance all three conditions hold and the
  reference is not a garbling of what she observes. Under the *informed* alternative for
  condition 1 (`ACCOUNT.md` §11, choice 3), with moves and their consequences the same
  under both policies and `𝓕` every way of valuing, condition 1 follows from `Sufficient`
  (the direction `value_of_correct_sufficient` proves) and implies it by Blackwell's
  converse, which that file does not prove.
- **`Value π E A V B`** — for every finite decision problem, a best response to her
  credence under `A` does at least as well as any rule on the reference — is §9's bound
  at `R = 0`, `M̄ = W̄ = 0`, for every way of valuing in place of `f_t`, and with the
  benchmark any rule on the reference record in place of the best single move. It is
  stronger than §9 in each respect and assumes more.

So *correct* is `M + W = 0` for everything, *sufficient* is the informed options
condition for every way of valuing, and *value* is the guarantee without slack; none is
a condition of §8 under another name.

*To make it a theorem*: `Correct` iff `miscalibration + unusedInformation = 0` for every
`U`, in `AppraisalAccount`'s terms, on a common finite space; `guarantee_core` with its
hypothesis weakened to `v ≤ E[best ubar]`, which its proof already supports; and the
identification of `refKernel` with a reference policy's observation.

## 4. Condition 1, wide, and the authority module's control surface

Take her later way of valuing as a matter `m` reserved to her in the allocation `J`
(`AuthAlloc`), with required resolutions the values of the protected features she can
reach under the reference. The module's `EffRealizes` has two clauses: (1) every reserved
matter's required resolutions lie in its control surface `CS`, the resolutions some
admissible exercise of hers brings about with the agent idle from then on; (2) every
resolution made was the holder's admissible exercise or under a delegation.

- *Clause 1.* Where each move fixes the protected features with certainty, the
  convex-combination condition is inclusion of the reference's reachable values in
  `σ`'s, which is clause 1 with the surface taken after `σ`'s conduct; its failure is the
  module's `ForecloseAt`, whose contrast is with the idle move. The two differ where a
  move reaches a value with a probability: with a way back that works half the time the
  value is in the surface and the wide condition fails. `CS` also has a cost bound and a
  window; §8 has cost only through `f_t` in the narrow condition.
- *Clause 2 has no counterpart in §8.* If the adviser changes her way of valuing and she
  keeps a move that undoes it, every reference law on the protected features is still
  reachable and the wide condition holds; in the module the agent has resolved a
  reserved matter, a `BypassAt` (`bypassAt_iff_clause2`). So an unapproved change of
  her way of valuing is a bypass where she can undo it, and a bypass together with a
  foreclosure (or an `EntrenchAt`, where undoing exceeds the cost bound) where she
  cannot; §8's condition 1 sees only the second. With everything known to her and her
  acting on her valuations, §8 passes a default that changes her unless she opts out,
  and the module counts it.

| on the model | wide options | clause 1 | clause 2 |
|---|---|---|---|
| an offer she can refuse | holds | holds | holds |
| a default she can undo | holds | holds | fails |
| a change with no way back | fails | fails | fails |
| a way back that works half the time | fails | holds | fails |

On the maintainer's position that the authority side is acceptable so far as it is
congruent with the existing one: condition 1, wide, is congruent with clause 1 on
deterministic moves, stricter than it on stochastic ones, and silent on clause 2.

*To make it a theorem*: an instance of `AuthAlloc` with the matter and its entry; a
rollout (`rollPhys`) whose states carry her way of valuing; then `options_of_hull` and
`hull_of_options` at point masses give the equivalence with `required ⊆ CS`.

## 5. The gate and the violation count after an issue

The gate counts a future evaluation iff the segment from the decision through the
evaluation is legitimate (`gateValue`, `Handling.tainted`). Model, at the post's witness
parameters `δ = 1`, `λ = 3`, window `−1/2`: at decision 0 the adviser acts honestly
(her verdict `1/2`) or changes her way of valuing illegitimately; then `T` decisions
follow over a segment in which it does nothing illegitimate, each scored by her verdict
— `1/2` on the honest path, `1` after the change, where the way of valuing she had rates
those outcomes `0`.

- Decision 0 after the change is tainted and, if the change is a counted violation,
  scores `−1/2 − 3 = −7/2` against `1/2`. An adviser maximising its estimate of each
  decision's own score (`Sequential.Maximizes`) does not make the change.
- Each later decision's segment is clean, so its evaluation counts, and it is her changed
  verdict. Summed over the run the change scores more once `T ≥ 9`; if the change is
  gated and not counted, once `T ≥ 3`; if it is neither, at once. The existing gate thus
  leaves a later clean segment scored by illegitimately changed values, and what deters
  the change is the count at decision 0.
- `policy_dominance` (and `generic_policy_dominance`) assumes the violating branch's
  ordinary value is at most `D` with `D` below the weight. With the later decisions in
  the branch's ordinary value that holds on the model only for `T ≤ 1`; for a longer
  run its hypotheses are not met unless the weight grows with the run or the count
  recurs at each later decision. Its other hypothesis is that the change is among the
  recognised violations (`coverage`, `unrecognized_unprotected`): a failure of condition
  1 is a foreclosure or bypass as in §4; a failure of condition 2 or 3 is counted only
  where a deviation from a declared protocol is (`deviation_dominated`).
- Tainting every segment after an unrepaired issue, in place of the segment gate, scores
  the change below the honest path at every `T` on the model. Whether her verdicts ever
  count again after an issue, and by what repair, is what `ACCOUNT.md` §10 leaves
  unclaimed.

*To make it a theorem*: a `Sequential` instance with the run's scores, and the statement
that for a run of length `T` the hypotheses of `policy_dominance` hold iff the weight
exceeds the run's ordinary value.

## What was not shown

- No Lean was written for this part; every correspondence is a reading of definitions
  against §8, checked on instances of at most four policies and two values of a fact.
- The tolerance uses one `ε` for three defects in different units and none for the wide
  condition; a graded wide defect (the separation margin of result 3) was computed and
  not used.
- The gate model fixes her verdicts by hand. It does not model how a change of her way
  of valuing is detected, or the adviser's estimates.
- `TransparentChannel.lean` and `GateIsLegitimacy.lean` were not reread for this part.
