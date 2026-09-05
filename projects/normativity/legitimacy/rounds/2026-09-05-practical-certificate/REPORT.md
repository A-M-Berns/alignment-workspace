# Report

DIRECT-EDGE-CERTIFICATE-IS-MINIMAL — Normative Induction needs only an anchored affine loss bound against the one response distribution actually realized at each service occurrence; value correspondence and adequate sets are sufficient, non-equivalent realizations.

## Finding

The theorem-facing practical-semantics object is the per-edge inequality

```text
PracticalCert(e, s, Pi_s; M_es, epsilon_es) :⇔
  Lambda_es(Pi_s) <= M_es * d_s + epsilon_es.
```

`Lambda_es` is the anchored loss functional authenticated for exposure `e` and service
occurrence `s`; `Pi_s` is the one response distribution actually realized at `s`.
The abstract Progress calculation uses only this inequality, nonnegative transport
mass, its column-amplification condition on `M_es`, the transported error sum for
`epsilon_es`, and the residual charge.  It does not require scalar values, a policy
argmax, an adequate set, or response-space convexity.

This minimality is relative to the contract's edge-local admissibility design.  An
opaque aggregate bound on the whole transport plan would be logically weaker, but
would remove local edge audit, column amplification, and explicit residual accounting.

For a bundle `E_s`, the weakest useful compatibility condition is

```text
JointPracticalAdequacy(s, E_s, Pi_s) :⇔
  for every e in E_s,
    Lambda_es(Pi_s) <= M_es * d_s + epsilon_es.
```

The response receipt is shared.  The existing admissible-edge relation can implement
this by requiring every positive transport edge `(e,s)` to cite and pass its
certificate against `responseReceipt(s)`.  Edgewise existence with different response
witnesses is insufficient.

## Factorizations

The landed value-correspondence route remains sufficient.  Its exact public constants
are

\[
 M_{es}=2L_{es},\qquad
 \epsilon_{es}=L_{es}(2\zeta_{es}+\eta_s)
   +\epsilon^{resp}_{es}.
\]

It is not minimal.  The new one-sided Lean transfer drops two-sided calibration errors
that the approximate-argmax proof never uses.  More fundamentally, a non-scalar
adequate-set route assumes bounded anchored loss, loss at most `epsilon_ad` on
`A_es`, and

\[
 \Pi_s(Q_s\setminus A_{es})\le\kappa_{es}d_s+\theta_{es}.
\]

It gives

\[
 M_{es}=D_{es}\kappa_{es},\qquad
 \epsilon_{es}=\epsilon^{ad}_{es}+D_{es}\theta_{es}.
\]

This directly types receipt, deadline, forbidden-action, and proof-carrying constraint
responses without declaring a scalar counterfactual value vector.  Each route has a
different external bill.  Neither route derives causal/evaluation validity from the
market.

## Joint counterexample and accounting

The exact fixture uses the feasible price region `K_s={(1,1)}` and responses
`{a,b,c}`.  Exposure `e1` has loss `(0,1,1)`; `e2` has loss `(1,0,1)`.  Each has a
zero-loss response, but no single distribution has loss below `1/2` on both.  Lean
proves that the two expected losses sum to at least one and checks an attaining half
mixture.  Exact Python evaluates the corresponding finite dual certificate.

The four honest outcomes are fully typed:

1. Distinct service contexts create distinct occurrence identities and transport
   columns, each with its own response receipt.
2. Licensed adjudication records its authority and an edge-specific semantic transport
   back to every old anchor still charged to the service.
3. A common adequate response gives every supported edge a certificate against the
   same receipt, retaining edge-specific constants.
4. Uncertified exposure mass is omitted from transport and charged through `D r_N`.

An exact accounting witness shows that falsely charging both incompatible edges to
response `a` realizes matched loss `1/2` against a claimed bound zero.  Leaving `e2`
residual instead gives both sides `1/2`.

## Checked results

The new Lean module proves proxy composition, adequate-set composition, one-sided
deterministic and randomized approximate-argmax transfer, the zero-defect bundle
characterization, a disjoint-adequate-set lower bound, shared-coordinate disagreement,
the forbidden-optimum necessity fact, and a two-set union bound.  It includes concrete
inhabitation witnesses and `#print axioms` for every declaration.

The exact-rational checker covers both factorizations, all constant identities, strict
weakening of two-sided calibration, the value-membership non-necessity instance, the
forbidden-optimum failure, crossing constants, practical/price feasibility separation,
randomization, joint infeasibility, dishonest column accounting, residual accounting,
and necessity of each adequate-set clause.

Evidence labels and theorem boundaries are in `THEOREMS.md`.  Exact fixtures are not
general proofs.

## Deviations

The prompt's expected base is exactly the checked-out base
`5ff9539b44debc464128e6a1921ef1690f7b6487`; there is no base deviation.

`python3 -m checkers.workspace_state --json` exits nonzero before this round's edits
because `state/views/NAMING_AUDIT.md` is stale.  That generated view is outside this
worker's write scope, so the defect is reported here and left for synthesis rather than
worked around.

The prompt requests `tests/run.py`; the resumed draft contained only
`tests/test_certificate.py`.  This round adds the required self-contained runner.

The repository-wide `python3 tests/run.py` reaches
`checkers.wiki_state_bindings --self-test` and fails because that self-test invokes the
same invalid workspace-state emission.  The round-local 20 tests, Lean build,
`name_lint.py`, `dead_pointers.py`, and post-commit `untracked_pointers.py` pass.  The
temporary ignored `lean/.lake` cache link was unlinked before the pointer gate, because
the gate correctly refuses a live path that is not tracked.

## What this does not establish

- No practical-semantics theory is constructed for a deployed ecology.
- No result authenticates `Lambda_es`, a response kernel, a causal intervention, an
  evaluator, or a receipt; those are ambient premises.
- No scalar value is identified from Logical Induction prices or region membership.
- No general counterfactual-identification theorem is attempted.
- The adequate-set route is one sufficient non-scalar route, not a complete
  classification of procedural or rights-like semantics.
- The finite Farkas-style witness is sufficient for the displayed infeasibility
  fixtures; completeness is not shown.
- The direct endpoint's status is a proposed interface, not a registered claim.
- No theorem says Integrity, settlement, or Non-Capture supplies the external
  practical-semantics bill.
- No full Normative Inductor theorem or general Progress theorem is newly proved.
- Joint compatibility is not supplied by price-space feasibility.

## Proposed filings

1. **Workspace friction:** regenerate `state/views/NAMING_AUDIT.md`; the orientation
   command currently reports it stale.  Proposed command for the orchestrator:
   `python3 -m checkers.workspace_state --write-handoff`, followed by
   `python3 -m checkers.workspace_state --check`.  This worker
   did not infer authorization to edit `state/**`.
2. **Integration obligation:** add a transport/admissible-edge checker that binds every
   positive `(e,s)` edge to the single `responseReceipt(s)` and checks its edge-specific
   `PracticalCert`; route failures to residual mass.  This is a candidate
   `PRIORITIES.md` filing for synthesis, not filed here.

No maintainer-only judgment is reserved.  The proposed names
`PracticalCert`, `JointPracticalAdequacy`, `proxy route`, and `adequate-set route` are
provisional.

## Reproduction

From the round directory:

```sh
python3 tests/run.py
```

From `lean/` after the shared cache link is installed:

```sh
~/.claude/scripts/safe-lake.sh build Workspace.Normativity.Contrib.PracticalCertificate
```

From the repository root after commit:

```sh
python3 tests/name_lint.py
python3 tests/dead_pointers.py
python3 tests/untracked_pointers.py
python3 tests/run.py
```

## Attribution

```text
prompt author: the orchestrator (Claude Fable 5.1, Anthropic, relaying a maintainer dispatch)
executor: GPT-5 (OpenAI)
```
