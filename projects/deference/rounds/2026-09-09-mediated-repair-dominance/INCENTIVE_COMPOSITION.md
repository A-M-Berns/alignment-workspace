# The bypass premium and its transfer

Labels as in `MEDIATED_LIFT.md`.  Rewritten in the pressure pass: the first pass's
per-option formulation is §5 here, and its claim to consume legitimate deference as
stated is withdrawn (`PRESSURE_PASS.md` §1).

## 1. The premium, in three registers

```
Φ_h(π)  =  ( V_A(π) − V_A(Lift π) )₊              pointwise
Φ_C(h)  =  sup_{π ∈ Π_phys(h)} Φ_h(π)              uniform
```

with `Lift` the explicit interposition of `MEDIATED_LIFT.md` §3.  The incentive round's
`(C)` — `Δ^phys ≤ Δ^C + Φ_C` — is unchanged (LEAN `violation_decomposition`).  What `V_A`
is decides which theorem one gets, and the three are kept apart (the dispatch's §10):

- **security scores** — the chooser's operative score of option `q` is the price
  `P_n(U_q)` of the activated security `U_q = c · w_q`; the bypass incentive is
  `Δ_bypass = [P(U_π) − P(U_Lift π)]₊`;
- **operative choice** — what the mediation-cell chooser actually selects;
- **latent total value** — an independently specified total `V_A` on the physical
  policy space, e.g. the outcome-extensional task utility `u`, or a completion of the
  activated evaluation.

## 2. The task register: the transfer needs `(CT)`

With exact reproduction the task premium is the Level I identity at the principal's
decision cells with the bypass as the substituting selector:

```
Φ_h(π)  =  declGap  +  declRegret
```

(LEAN `premium_eq_gap_add_regret`; FIX A: `1/2 = 1 + (−1/2)`), so bounding it needs
`declGap ≤ ε`, and that hypothesis is `(CT)` with the lift as the repair (LEAN
`mediation_st_iff_ct`, FIX `test_A_st_at_mediation_equals_ct`): `X − Y = −declGap` for
`X = V_A(Lift π) − V_A(π)`, `Y = W(Lift π) − W(π)`.  The incentive round's
`ct_strictly_stronger` applies verbatim.  The lift changes the comparison's *type* — an
actual decision cell, an alive principal, one proposal — not its strength.  **REFUTED**
as a reduction; kept because its failure is exact.

## 3. Common activation

The canonical theorem has one activation event `c` for the issued menu, a function of
the world and not of the selected option.  For `{π, Lift π}` that presupposes
**activation independence**: on every exterior path the evaluation's fate is the same
whichever option is selected (`PRESSURE_PASS.md` §1–§2; the causal architectures that
give it, and the one that does not, are there).

**Theorem (bypass premium, common activation)** (LEAN `bypass_premium_le_common`).
Completions `B_raw, B_lift` of the activated evaluations in a band of width `D`, `κ, ρ ≥ 0`,
dominance `w_raw ≤ w_lift + κ + ρ` on the activated worlds:

```
E[B_raw] − E[B_lift]  ≤  E[κ] + E[ρ] + D·η ,      η = E[1 − c] .
```

Sharp (LEAN `Witness.commonVoid`; FIX G).  With `κ` derived from the structural
certificate (`PRINCIPAL_OPTION_DOMINANCE.md` §2) the bound reads
`L·E[δ] + E[ρ] + D·η`.

## 4. Security scores: no completion, no void term

**Theorem** (LEAN `security_score_bypass_le`).  Under common activation, with `κ, ρ ≥ 0`
and dominance on the activated worlds,

```
E[U_π] − E[U_Lift π]  =  E[c·(w_raw − w_lift)]  ≤  E[κ] + E[ρ] .
```

On the void branch both securities are `0`; nothing is completed and nothing is charged.
With prices within `ε_r, ε_l` of the securities' expectations
(`security_score_bypass_le_of_prices`):

```
P(U_π) − P(U_Lift π)  ≤  E[κ] + E[ρ] + ε_r + ε_l .                        (A)
```

**Operative choice** (LEAN `operative_choice_loss`).  A chooser whose scores are within
`ε_cal` of the securities' expectations and which selects the raw option only when its
score is within `ε` of the lift's loses at most `ε + 2ε_cal` of activated protected
value by that choice.  This is (B): the by-construction chooser does not bypass, up to
its decision regret and calibration.

**Latent total value** (C).  For a completion-valued `V_A`, §3's `D·η` is the price of
the void branch and is attained; for a task utility, §2.  Both need what the incentive
round called `(DV)`; neither is delivered.  **OPEN**, item 84.

**Fixtures.**  A: `Δ_bypass = −1/2` (security scores); G: `−2/5`, the void fifth
contributing zero to both scores while the completion-valued agent's premium on the
same rows can be positive (`test_security_scores_versus_completions`); E1: `−1/4`.

**What the scores say about voiding options.**  A raw option that ends the evaluation
has no common `c` with the lift (H).  Where activation is per option (§5), its security
is `0` on the void branch, so a chooser by these scores rates it at the band's floor:
conservative by the level convention, and silent about the principal's judgment there
(it has none).  This is a property of the register, stated, not a theorem about the
principal.

## 5. Per-option activation (auxiliary)

Same-branch evaluation — the occurrence occurs on the trajectory the selected option
generates — gives per-option events `c_raw, c_lift` (the `PerAction` section of
`ActivatedValue.lean`, where the conditional-argmax identity fails).  Then (LEAN
`bypass_premium_le`, `_of_approx`; FIX `test_premium.py`)

```
E[B_raw] − E[B_lift]  ≤  E[κ] + E[ρ] + ε_def + D·(η_raw + η_lift) ,
```

sharp (`Witness.totalVoid`), and with `c_raw = c_lift` it is §3's bound with the void term
doubled.  This is the register in which `η_raw` is the violation's own — E2's
`η_raw = 1` — and it is the first pass's finding with its cause now named: same-branch
evaluation is where the evaluator is inside the violation's reach.  The selection form
`deferential_bypass_loss` (values in `[0, D]`, loss `≤ ε + D·η_lift`) is kept as the
per-option statement.

## 6. Discharge through legitimate deference, corrected

| term | supplied by | status |
|---|---|---|
| `L·E[δ]` | T2a: a reproduction certificate and the evaluator's stability | LEAN on the certificate; FIX |
| `E[ρ]` | the principal's decision at the mediation cell; `principalRegret_le_of_calibration` bounds it under cellwise calibration of a sealed target | LEAN (existing) |
| `ε_r, ε_l` | (A3) ordinary LI Value on the activated securities — prices track expectations; `R_U ≤ ε` is the selection form | PAPER, conditional |
| `c` common | (A1) activation soundness *and* activation independence: the answering process outside every candidate's reach | LEAN predicates, EXT meaning; **independence is a causal precondition the canonical type presupposes** |
| selection blindness | (A2) | PAPER scope |
| `η` | a property of the sealed process, exogenous | OPEN as a realization (item 87), now with the class it must exclude named |

What legitimate deference delivers on the class of §7: (A) and (B).  What it does not:
(C), for any latent total value — item 84 remains open as a theorem about general
operative values and is **not needed by the intended architecture**, whose chooser
scores by `P_n(U_q)`.  That distinction is now explicit.

## 7. T4, over the factored class

```
Π_effect-mediated  ∩  Π_evaluation-preserving  ∩  Π_provenance-normalizable  ∩  Π_joinable
```

(`PRESSURE_PASS.md` §8).  On it, with `δ ≤ d`, `ρ ≤ ρ̄`, prices within `ε̄`:

```
Δ_bypass  ≤  L·d + ρ̄ + 2ε̄ ,
```

and the mediation-cell chooser does not bypass up to `ε + 2ε̄`.  DERIVED from §4 by
suprema.  It reaches direct authority bypass, time-sensitive pre-emption with its cost
exposed, successor installation with a surviving evaluator, and manipulation with an
authorized substitute; it does not reach evaluator destruction, undeclared channels, or
manipulation without a substitute, and it charges foreclosure at its full value.  It is
security-score / operative-choice incentive corrigibility on that class, and it is not
described as latent-total-value incentive corrigibility.

## 8. T5

Unchanged in strength: joinability gives one sufficient route to a small structural
discrepancy (`PRINCIPAL_OPTION_DOMINANCE.md` §4), `SHIFT` is not identified with it, and
the composition with the continuation-BRIA frontier is a reading, not a theorem.
