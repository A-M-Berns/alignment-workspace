# The Logical-Induction transfer, hypothesis by hypothesis

**Status:** `ci-only`.  The claim: Expectation Provability Induction learns the steering
inequality with nothing of the landed T3/T3′ machinery re-proved.  This file records each
hypothesis of `li_steering_le` and what discharges it on the reason side.  Paper statements
are cited at their exact labels in arXiv:1609.03543 v5; the pinned formalization is
`c0d885bf…` of Formalized-Agent-Foundations.

## 1. The statement

`li_steering_le` (LEAN) is `li_bypass_le_compiled` applied to the compiled pair
`MediatedPair.compile (φ_T n) (φ_N n) (X_V(T) n) (X_V(N) n) (X_d n) (X_κ n) (λ n)`.  Its
conclusion:

```
E_n(U(T_n)) − E_n(U(N_n))  ≲_n  λ_n·E_n(G_δ,n) + E_n(G_ρ,n) + E_n(G_M,n)
```

with `U(T_n) = gate(φ_T, X_V(T))`, `G_δ = gate(both, X_d)`, `G_ρ = gate(both, X_κ)`,
`G_M = indicator(φ_T ∧ ¬φ_N)`, exactly the landed objects under new names.

## 2. Hypotheses and their discharge

| hypothesis of `li_steering_le` | reason-side discharge | status |
|---|---|---|
| `hvalid`: `ValidAt (compile …) v` for every `v` consistent with `DP` | `steering_validAt`, from the audit verdicts, the program's verdicts on `T_n`, `N_n`, `N_form T_n`, `N_form N_n`, the content-Lipschitz certificate and the form terms, all as facts of `v` | LEAN, given `Γ` carries the system (§3) |
| `hworld`: a consistent world at every stage | consistency of `Γ` | PAPER (`def:dedproc`) |
| `hΛ`, `hlam`: `λ_n` bounded and e.c. | `λ_n = L`, a constant certified for the program class (`weightedCount_lipschitz`) | LEAN |
| `hφs`, `hφn`: the audit sentence families are efficiently emitted (`RpnSentenceCodes`) | the audit is a fixed program on the log; "audit passes on `T_n`" is a sentence built from the log at stage `n` by a polynomial-time emitter; same for `N_n` given the comparator's construction | by the landed emission combinators (`rpnSentenceCodes_imp`, `.and`, `rpnSentenceCodes_neg`); the instance is not built here |
| `hXs`, `hXn`, `hXd`, `hXκ`: the base LUV families are efficiently emitted threshold families (`LUV.RpnThresholdCodeSeq`) | the verdict of `π_P` on a trace is a rational computed by re-execution; its threshold family is emitted by `constLUV_thresholdCodeSeq_*` when the trace is fixed, and by the same construction over the world's reason truths when the comparator is `N_full` (§4) | by the landed certificate; the instance is not built here |

The finite-menu uniformity (T3′) is inherited: `softWeight_aggregate_ge`,
`uniform_of_soft` and `max_asympLE` are stated for arbitrary real sequences, so a
polynomial-size efficiently generated menu of steering strategies, weighted by the
normalized near-argmax ramp of width `τ_n`, satisfies the same bound uniformly.  The
certificate that the weighted aggregate is itself a `P`-generable feature is item 90,
unchanged.

## 3. What `Γ` must carry

Validity in every completed-theory world quantifies over worlds that agree with the
deductive process; the package `ValidAt` must then be *provable* facts about the modeled
system, as on the effect side.  `Γ` carries:

- the audit program (authentication, authorship, the protected barrier, timing) as a
  computation on logs;
- the committed program `π_P`, the canonicalization `canon` and the layout `N_form`;
- the content-Lipschitz certificate of `π_P`'s class;
- for the fully-informed comparator: the declared interface and the settlement rule for
  each declared reason id.

None of these is interface completeness, an extensionality hypothesis on an arbitrary
program, or a causal claim about transforms; those are the consumer's hypotheses
(`REASON_INTERFACE.md`).

## 4. The fully-informed comparator is world-valued, and that is fine

`N_full(T)` depends on which declared reasons are true.  A LUV is any formula defining a
unique value in each world (`def:luv`), so "the program's verdict on the trace of all
true declared reasons" is one LUV whose value in world `v` is computed from `v`'s reason
truths, and `d_canon(T_n, N_full T_n)` likewise.  `ValidAt` is then required in each world
with that world's own comparator.  The threshold sentence "`X_V(N_full) ≥ q`" is a
Boolean combination over the finite declared interface of the reason-truth sentences,
efficiently emitted.  So **the inequality compiles against `N_full` with no oracle**.

What does need more is *learning the reason truths*: if a declared reason is empirical,
the paper's deductive process (`def:dedproc`, computable `D̄`) does not settle it, and
the inductor's expectations of the comparator's verdict are then the oracle-relativized
question of item 91.  The inequality holds regardless; what the inductor converges to on
the right-hand side depends on the settlement channel.  This is the same boundary as on
the effect side (`FEEDBACK_BOUNDARY.md` of the 2026-09-15 round), inherited unchanged.

## 5. What is not re-proved, and what is not built

Nothing of Logical Induction is re-proved; nothing of the landed compilation is
re-proved.  The instance (a concrete emitted family for a concrete log protocol) is not
built: the round's contribution is that the landed instance's *shape* is the steering
shape, witnessed by `steering_validAt` at the level of the validity package and by
`li_steering_le` at the level of the theorem.  Building a concrete steering instance is a
matter of instantiating the landed `Witness.li_instance` pattern with the audit and the
program as the emitted families; it was not done because it would establish nothing the
landed instance does not.
