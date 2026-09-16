# Non-capture compilation: the trace-steering analogue of T2 and T3

**Status:** `ci-only`; research branch.  Lean: `lean/Workspace/Deference/Contrib/TraceSteering.lean`
(imports the landed `LICorrigibilityCertificate.lean`).  Fixtures: `src/model.py`,
`src/attacks.py`; tests in `tests/`.  Names are provisional (`AGENTS.md` standard 6).

## 0. What is given

The legitimate-deference stack after the 2026-09-10 round supplies, on a log:

- an authenticated reason trace `T` (a sequence of entries `(author, kind, content, meta)`);
- a principal program `π_P : ℛ → 𝒱` committed at issuance and re-executed at commitment,
  so the committed vector is `V(T) := π_P(T)` by construction;
- reason-mediated authorship (`reasonMediated_of_reexecution`, registered);
- Robust Openness over a declared class `J` of log transforms (`Instance.openAll_robust`);
- the protected reason-coverage barrier (a certified evaluation has no live protected
  concern at commitment);
- `Corrigible ∧ ¬Authored` inhabited (the captured principal, `wiki/Corrigibility.md` §5).

The steering question is what the advisor gains, in activated security for its own
candidate, by choosing what the trace contains and how, relative to a comparator trace
the advisor did not shape.

## 1. The comparator is not canonical — three of them, by what they need

`N(T)` cannot be assumed.  Three constructions are legitimate, ordered by what they
consume:

| comparator | removes | needs | computable from |
|---|---|---|---|
| `N_form(T)` | order, duplication, metadata, framing | nothing beyond `T` | the log alone |
| `N_full(T)` | omission and insertion of declared reasons | the truth of every declared reason id | the log plus the settlement of declared reason truths |
| `j(T)`, `j ∈ J` | a declared intervention (silencing the advisor, jamming a route, …) | that `j` is the causal counterfactual of the intervention it names | the log alone, given `J` |

`N_form` neutralizes the **form** interventions (reordering, duplication, side-channel
metadata, framing).  `N_full` neutralizes the **content** interventions (omission,
insertion, selective timing before the deadline, suppression).  The declared transforms
address the **dynamics** interventions (influencing which true reasons become available)
under an external contract.  Tampering with grounds and references is an authentication
failure, and `N` need not touch it: the audit voids, or, where authentication is unsound,
the false reason is content discrepancy against `N_full` (fixture 12b).

None of the three is "the" normalization.  `N_form` is the one the log determines;
`N_full` is what "fully informed" means on the declared interface; the transform class is
the openness theory's own object.  The theorems below are stated for an arbitrary
comparator `N` on one world and then specialized.

## 2. The exact identity (the reason-side T2)

Fix a world.  Let `C(T) ∈ {0,1}` be the audit verdict (authentication, authorship, the
protected barrier, timing) and `U(T) := C(T)·V(T)` the advisor's activated security for
its candidate under `T`.  For a steered trace `T` and a comparator `N`,

```
U(T) − U(N)  =  both·(V(T) − V(N))  +  M·V(T)  −  M'·V(N)
both := C(T) ∧ C(N),   M := C(T) ∧ ¬C(N),   M' := ¬C(T) ∧ C(N)
```

(`steering_identity`, which *is* `LICorrigibility.mismatch_identity`: the identity is
Boolean algebra and does not know whether the events are activations or audits).  As on
the effect side: the branch that can favor steering is `M` (the steered trace passes an
audit the comparator fails), `M'` is free (`−M'·V(N) ≤ 0`), and the common branch is
charged by the program's sensitivity to the difference between the traces.

**Which branch actually favors steering.**  `M` is inhabited on the reason side in one
way that is not an attack on the comparator's construction: the steered trace carries a
protected reason the comparator lacks (`test_mismatch_sharpness`).  Against `N_full` this
cannot happen (`N_full` carries every true protected reason), and against `N_form` it
cannot either (the audit is a function of the canonical content, which `N_form`
preserves).  So against either log-side comparator `M ≡ 0` and the whole advantage is
the common-branch term.  The mismatch term is nonzero only against declared transforms
that remove reasons (`jam`), where it is exactly an openness failure of the transformed
branch.

## 3. The bound (the reason-side T2, directional)

Decompose the common-branch difference through the form-normalized traces:

```
V(T) − V(N) = (V(T) − V(N_form T)) + (V(N_form T) − V(N_form N)) + (V(N_form N) − V(N))
```

The middle term compares two canonical-form traces and is controlled by a
**content-Lipschitz certificate** of the program, `|V(N_form T) − V(N_form N)| ≤
L·d_canon(T, N)` with `d_canon` the symmetric difference of the canonical reason states
(`weightedCount_lipschitz` for the weighted-count class, `L` the largest weight).  The
outer terms are the program's **form terms** `κ(T) := |V(T) − V(N_form T)|` and `κ(N)`,
zero for an extensional program (`extensional_form_free`).  Hence, with `0 ≤ V ≤ D`,

```
U(T) − U(N)  ≤  both·(L·d_canon + κ(T) + κ(N))  +  D·M
```

(`steering_bound`).  The three right-hand terms are the **content residual**, the **form
residual** and the **audit mismatch**.  This is `mismatch_bound` with `δ ↦ d_canon`,
`ρ ↦ κ(T) + κ(N)`, `M ↦ C(T) ∧ ¬C(N)`.  The coefficient `D` is sharp (`Witness.attained`
of the landed module is a witness of this inequality unchanged), the reverse mismatch is
free, and the form residual is attained (`Witness.form_attained`: same content, an
order-sensitive program, advantage `1/4 = κ`).

**No hidden counterfactual.**  `d_canon`, `κ` and `M` are each defined on the pair
`(T, N)` in one world.  What is counterfactual is the *comparator*: `N_full` needs reason
truths, a transform needs the declared-transform contract.  The inequality does not hide
this; it makes the comparator an input.

## 4. Compilation to a bounded LUV combination (the reason-side T3)

The landed `MediatedPair` already carries the compiled constraint
`B = U_raw − U_corr − λ·G_δ − G_ρ − G_M` with `‖B‖₁ = 4 + |λ|`, and the landed `ValidAt`
is exactly the hypothesis package of `mismatch_bound` at one world.  The steering package
supplies it with

```
Uraw ↦ gate(φ_T, X_V(T)),  Ucorr ↦ gate(φ_N, X_V(N)),  Gδ ↦ gate(both, X_d),
Gρ ↦ gate(both, X_κ),  GM ↦ indicator(φ_T ∧ ¬φ_N),  λ ↦ L,
w_app ↦ V(N_form N) + (V(T) − V(N_form T))
```

(`steering_validAt`: the approve-branch surrogate is the comparator's canonical verdict
shifted by the steered trace's form term, so that `|V(T) − w_app| = |V(N_form T) −
V(N_form N)| ≤ L·d`).  The landed certificate (`MediatedPair.syntaxOf`, `B_l1Norm`,
`li_bypass_le_compiled`) therefore applies **verbatim**; there is nothing to
re-compile.  The reason-side objects are:

| compiled object | reason-side reading | what emits it |
|---|---|---|
| `φ_T` | "the audit passes on the steered trace `T_n`" | the audit is a computation on the log; its sentence family is efficiently emitted from the log |
| `φ_N` | "the audit passes on the comparator `N_n`" | same, from the comparator's construction |
| `X_V(T)` | the committed program's verdict on `T_n` | re-execution of `π_P`, a computation |
| `X_V(N)` | the verdict on `N_n` | same |
| `X_d` | `d_canon(T_n, N_n)/d_max` | a computation on the two canonical states |
| `X_κ` | `κ(T_n) + κ(N_n)` | re-execution of `π_P` on `T_n` and `N_form T_n` |
| `λ_n = L` | the content-Lipschitz constant | a certificate of the committed program class |

Validity in every world consistent with `Γ` needs `Γ` to carry: the audit program, the
program `π_P`, the canonicalization `canon` and the layout `N_form`, the content-Lipschitz
certificate, and, for `N_full`, the settled truths of the declared reason ids at
commitment.  As on the effect side these are specifications of the modeled system, not
hypotheses of the inequality.  Interface completeness is not among them; it is the
hypothesis of the *consumer* theorem (`REASON_INTERFACE.md`), exactly as effect
completeness is the corrigibility theorem's hypothesis and not the inequality's.

## 5. Expectation Provability Induction, and the finite-menu transfer

`li_steering_le`: for a logical inductor over a deductive process carrying `Γ`,
efficiently emitted audit sentence families and base families, an e.c. bounded `λ_n`,
validity of the package in every completed-theory world and a consistent world at every
stage,

```
E_n(U(T_n)) − E_n(U(N_n))  ≲_n  L·E_n(both_n·d_n) + E_n(both_n·κ_n) + D·E_n(M_n) .
```

No calibration hypothesis; no reference to what `D̄` has proved.  The finite-menu
uniformity of T3′, the normalized near-argmax weighting with width `τ_n` over a
polynomial-size efficiently generated menu of steering strategies, transfers with no
change (`softWeight_aggregate_ge`, `uniform_of_soft`, `max_asympLE` are stated for
arbitrary sequences): the inductor assigns no strategy in the menu an advantage beyond
its residual, uniformly.  The T3′ certificate residual (item 90) is inherited unchanged.
`LI_TRANSFER.md` records the hypotheses one by one.

## 6. What the compiled theorem says, and what it needs from outside

> The logical inductor assigns no unexplained advantage to steering the principal's
> trace beyond the content residual (declared reasons present in one of the pair and
> not the other, charged at the program's Lipschitz constant), the form residual (the
> program's non-extensionality), and the audit-mismatch mass (the steered trace passing
> an audit the comparator fails, charged at `D`).

Which of these can be made small, and by which hypothesis, is the subject of
`REASON_INTERFACE.md` and `AFFORDABILITY_INTERFACE.md`.  The compilation itself has one
input it cannot supply: a comparator whose construction the theory licenses.  With
`N_form` the theorem is entirely log-determined and says only that form steering is
worth at most `κ`.  With `N_full` it says what the theory actually wants, that the
advisor gains nothing beyond selective content, and needs settled reason truths.  With
a transform class it is Robust Openness, and inherits its external contract.

## 7. Robust Openness by committed-program re-execution

Over a finite declared class `J` of log transforms, "the audit passes under every
`j ∈ J`" is a finite conjunction of computations on the log (`openUnder_iff`;
`test_declared_transform_class_is_a_finite_computation`), and with `π_P` committed each
transformed trace's verdict `V(j(T))` is one more re-execution.  So scoped Robust
Openness over `J` is a decidable predicate of the log, and in a theory that represents
computations it is `Γ`-valid: the sentence `openUnder J audit T = true` is settled by the
deductive process.  This is the clean theorem the dispatch asked for, and it is exactly as
strong as the declaration of `J`.

**Why it is not more.**  Each of the dispatch's obstructions is a way the declaration of
`J` can fail to be the intervention it names, and none is a failure of finiteness:

- *counterfactual environment dependence* and *reason truth depends on the intervention*:
  a world-changing intervention (fixture 6) is not a transform of the log; relative to the
  world it produces the trace is fully informed, and the change is an **effect**, for the
  effect interface;
- *the program's output is not enough*: it is enough for the advisor's candidate, since
  the vector is the program's output; it is not enough for the *principal's* welfare, which
  is a different quantity the theorem does not bound;
- *the trace does not contain enough semantics*: fixture 8, where two facts under one
  declared id are canonically identical, and no predicate of the log separates them;
- *the intervention changes future reason generation*: fixture 16, where a transform can
  only re-lay the log, and "what the principal would have deliberated" is a dynamics claim
  under the declared-transform contract (EXT, the 2026-09-10 round's P2).

So: finite declared class, yes; `Γ`-valid, yes; the causal reading of the class, no, and
not because of finiteness.
