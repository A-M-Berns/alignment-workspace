# Source audit

Avrim Blum and Yishay Mansour, "From External to Internal Regret", JMLR 8 (2007),
pp. 1307–1324. Read from the publisher's PDF
(`https://www.jmlr.org/papers/volume8/blum07a/blum07a.pdf`); quotations below are
from §2 (Model and Preliminaries, pp. 1309–1310) and §7 (pp. 1319–1321).

Three registers, kept apart. **SOURCE** is what the paper says, quoted.
**INSTANTIATION** is what this round builds. **INFERENCE** is this round's own
claim about the fit.

---

## The twelve questions

### 1. What is the action set?

**SOURCE.** "We assume an adversarial online model where there are `N` available
actions `{1, …, N}`." Fixed, finite, horizon-independent.

**INSTANTIATION.** The eight semantic labels `Lambda`. Fixed before play, carrying
no date, occasion or content identity — established by the merged bridge round and
unchanged here.

### 2. What is a modification rule?

**SOURCE.** "A modification rule `F` has as input the history and an action choice
and outputs a (possibly different) action."

**INSTANTIATION.** A `SurgicalRepair` record: a certificate, a source label, a
replacement label. Its action at a date is a function of the public scorekeeping
status of that date's state.

### 3. May a modification rule depend on history?

**SOURCE.** Yes, explicitly. "(We denote by `F^t` the function `F` at time `t`,
**including any dependency on the history**.)"

**INFERENCE.** This is the hypothesis the repository's state-indexed programs need,
and it is granted in the definition rather than argued for. A comparator that
behaves differently at different states is not an extension of the source model.

### 4. What exactly is a time selection function?

**SOURCE.** "A time selection function `I` is a function over the time steps
mapping each time step to `[0,1]`. That is, `I : {1, …, T} → [0,1]`."

### 5. What information may the selector inspect?

**SOURCE.** Footnote 1, p. 1310: "We can let the time selector **depend on the
history up to time `t`**, rather than the time `t` itself, and all the results
presented would be the same."

**INFERENCE.** A public normative selector `P(S_t)` is therefore admissible. This
round folds the selector into `F^t` instead — the rule is the identity at
unselected dates — which is equivalent and lets the instantiation run at `M = 1`,
matching the learner already in the repository.

### 6. What exactly is the regret quantity bounded?

**SOURCE.** With `f^t = F^t(p^t)` defined by `f_i^t = Σ_{j : F^t(j) = i} p_j^t`:

> `L_{H,F} = Σ_t Σ_i f_i^t ℓ_i^t`, and `R^I_{H,F} = max_I max_F { L_{H,I} − L_{H,I,F} }`.

Theorem 18: `L_{H,I} ≤ L_{H,I,F} + O(√(T N log MK))`.

**This is a mixed-action quantity.** Both `L_{H,I}` and `L_{H,I,F}` are built from
the distribution `p^t`, not from a realized action.

### 7. Against which loss vector is the transformed action scored?

**SOURCE.** `ℓ^t` — the same one. `L_{H,F} = Σ_t Σ_i f_i^t ℓ_i^t` uses the loss
vector of date `t`, which is the loss vector that actually occurred.

**INFERENCE — and this is the round's pivot.** The transformed distribution is
scored at the state that actually obtained. The source never constructs the
trajectory the comparator would have produced. **Replay is not in the theorem.**

### 8. Does the transformed action alter the future loss sequence?

**SOURCE.** No. Nothing in the definitions or in the proof of Theorem 18 feeds
`F^t(p^t)` back into the generation of `ℓ^{t+1}`. The modified sequence is an
accounting object over the same `ℓ`.

**INFERENCE.** The divergence the previous round measured between local comparison
and replay is therefore a divergence between the source theorem's object and a
different object. It is not a failure of a hypothesis of Theorem 18.

### 9. Does the theorem permit an adaptive environment?

**SOURCE.** The protocol is: "At each time step `t`, an online algorithm `H`
selects a distribution `p^t` over the `N` actions. **After that**, the adversary
selects a loss vector `ℓ^t ∈ [0,1]^N`." The adversary moves second and may
therefore condition on `p^t` and on everything earlier.

The paper also uses adaptive adversaries explicitly in §4: "we will consider an
adaptive adversary, whose choices may depend on the player's action selection in
previous rounds."

**The proof settles it.** Claim 17 and the derivation of Theorem 18 are algebra on
the realized sequences `(p^t, ℓ^t)`: a weight-potential argument bounding
`Σ_{I,F} w^{t+1}` by `Σ_{I,F} w^t`, then taking logs. No expectation is taken, no
independence is used, and no distribution over loss sequences appears. **The
inequality holds for every realized sequence**, so it holds however that sequence
was generated, including generation from the learner's own past actions.

### 10. What non-anticipation is actually required?

**INFERENCE from the protocol.** `ℓ^t` must be a well-defined vector at date `t`,
and `p^t` must not depend on `ℓ^t`. The adversary may see `p^t`; it may not see
the sample drawn from `p^t` when choosing `ℓ^t`, since `ℓ^t` is what that sample
is scored against.

**INSTANTIATION.** `S_t` is fixed when the date opens; `ell_t = G(S_t)` is computed
before the learner acts; the learner's realized action then moves the state to
`S_{t+1}`. That is strictly less adversarial than the source permits — the loss
does not even depend on `p^t`. Checked by
`test_the_loss_vector_is_determined_before_the_action_at_that_date`.

### 11. Does anything require the state to be exogenous or frozen?

**SOURCE.** No. There is no state in the model at all — only a sequence of loss
vectors. "Frozen environment" is a condition the repository's earlier rounds
imposed to make *replay* equal *local comparison*; it is not a hypothesis of
Theorem 18.

**INFERENCE.** This corrects a reading the repository has been carrying. The
applicability round listed "additive per-round loss — satisfied only in frozen v1"
against the row "additive per-round loss". That row is about the repository's
replay semantics, not about a hypothesis of the source theorem. Theorem 18 has no
additivity hypothesis beyond the loss vector being bounded and per-round.

### 12. Is the repository's `Program → transformation` encoding a genuine instance?

**Yes, with one qualification about which the round is explicit.**

Genuine: a fixed record, interpreted at each date against public status, inducing
`F^t : Lambda → Lambda`. Question 3 licenses exactly this. Total, closes on the
action set, and fixed before play.

The qualification: the *previous* round's nine programs rewrite many actions at
once. That is admissible to Theorem 18 — `F^t` may be any map — but it destroys
the lower bound this round needs, because gains and losses across actions cancel.
The surgical family here is the shape of the source's own internal-regret class:
"`F^{i,j}(i) = j` and `F^{i,j}(i') = i'` for `i' ≠ i`, plus the identity function."

---

## What the repository said, and what is now corrected

| repository statement | status |
|---|---|
| Theorem 18 permits history-dependent modification rules | **confirmed** by the definition |
| the bound is `O(ℓ_max √(T N log(MK)))`, with `M = 1` here | **confirmed** |
| the theorem's controlled quantity is expected mixed loss, not a sampled path | **confirmed** — §6 above |
| "no suspension or solvency coupling" is needed for the *reduction* | **needs splitting.** Needed for replay to equal local comparison; **not** needed for Theorem 18 |
| the frozen environment is a hypothesis of the source theorem | **incorrect as stated.** It is a hypothesis of the repository's replay semantics |

The last two are not errors in any Lean or any test. They are readings attached to
a correct bound, and they are what made the previous round treat an endogenous
state as an obstruction to the source theorem when it is not one.

---

## What the source does not give

- No pathwise statement. Theorem 18 controls `Σ_t ⟨p^t, ℓ^t⟩`, not the realized
  `Σ_t ℓ^t(a_t)`. Converting one to the other needs a concentration argument the
  source does not supply.
- No anytime guarantee. `β` is tuned from `T`. An infinite run needs a doubling
  argument or an adaptive tuning, neither of which is in Theorem 18.
- No claim about the *quality* of the comparator class. The bound is against the
  `K` rules supplied, whatever they are.
- The `Ω(√(TN))` lower bound of §4 is for a **different** model — regret measured
  against the realized action under an adaptive adversary — and is a limit on
  achievable regret, not a restriction on Theorem 18's applicability.
