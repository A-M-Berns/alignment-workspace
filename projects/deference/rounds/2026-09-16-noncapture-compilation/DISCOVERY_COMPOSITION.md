# Composition after discovery: actual → discovered → full

**Status:** `ci-only`; third pass.  Lean: `ReasonDiscovery.lean` §4 (`li_noncapture_chain`).

## 1. The identity

For the actual serviced trace `T`, the discovered comparator `N_disc` and the
fully-informed comparator `N_full`,

```
U(T) − U(N_full)  =  [U(T) − U(N_disc)]  +  [U(N_disc) − U(N_full)] .
```

On the branch where all three audits hold the first bracket is the service (plus
authentication) loss and the second is the discovery residual `V(Disc) − V(Truth)`
(`tests/test_discovery.py::Chain`).  Each bracket is itself a steering pair of the
first-pass shape, so each is bounded by the second-pass theorem with its own content
bound.

## 2. The chain, literally

```
Discovery theorem     ⟹  V(Disc_n) − V(Truth_n) ≤ β_n on the audited branch, in every
(DISCOVERY_THEOREM.md)    world of the declared hypothesis space     [β_n := the cell gap,
                          or the budgeted minimax value, a computation on the declared
                          repertoire and the program]

Supply theorem        ⟹  V(T_n) − V(Disc_n) ≤ α_n                    [second pass]

Canonicalization      ⟹  κ = 0 on both pairs

Sealed audit          ⟹  φ_T → φ_disc → φ_full in every consistent world

li_noncapture (×2)    ⟹  𝔼ₙ(U_T) − 𝔼ₙ(U_disc) ≲ₙ L·α ,   𝔼ₙ(U_disc) − 𝔼ₙ(U_full) ≲ₙ L·β

li_noncapture_chain   ⟹  𝔼ₙ(U_T) − 𝔼ₙ(U_full) ≲ₙ L·(α + β)
```

`li_noncapture_chain` (LEAN) takes the two compiled pairs `(φ_T, φ_disc, X_T, X_disc, …)`
and `(φ_disc, φ_full, X_disc, X_full, …)` with the middle family shared, the two content
bounds `a/b` and `a'/b'`, extensionality and sealing on both, and concludes the sum.  The
middle expectation cancels because both pairs are compiled from the same `gate φ_disc
X_disc`.  Authentication enters as part of `α` (a served reason failing authentication
is charged there); with a separate `γ` it is a third pair of the same shape.

## 3. Whether `β_n` is `Γ`-valid

The second pass could not certify the content term against `N_full` because "which true
reasons nobody raised" is a world fact.  What changes now is the *declared hypothesis
space*: the engine declares the finite space `Ω` of reason states it can distinguish and
the repertoire it can run; the cell gap and the minimax value are then **computations on
that declaration and the program**.  So "`V(Disc_n) − V(Truth_n) ≤ β_n` for every world
of `Ω`" is a `Γ`-valid sentence, relative to the declaration.  The sentence family is
emitted from the declaration as the audit and verdict families are.

What remains world-dependent and *not* certified is whether the actual world is in `Ω`,
i.e. whether the declared representation is adequate.  That is the ontology wall and it
is where it should be.  `N_full` is therefore a bounded ideal comparator without an
oracle: bounded by `β_n` relative to the declared space, with adequacy of the space
external.

## 4. The end-to-end non-capture statement

Relative to a declared reason representation with a declared hypothesis space and inquiry
repertoire, under trace mediation by re-execution, an extensional program, an independent
inquiry engine (evidence-sound outcomes, engine-owned policy and stopping, exogenous
costs, engine-owned candidate generation) with certified cell gap or minimax value
`β_n`, an independent supplier (advisor-proof capacity, exogenous costs) with certified
service loss `α_n`, sound authentication, and a content-monotone audit:

```
𝔼ₙ(U_T) − 𝔼ₙ(U_full)  ≲ₙ  A_tot·(α_n + β_n) .
```

When the suffix-cut condition holds on the docket (`α_n = 0`) and the repertoire
separates what the verdict separates within the budget (`β_n = 0`), the right-hand side
is zero, and the bounded agent assigns asymptotically no advantage to steering the
principal's deliberative inputs over the fully-informed trace on the declared interface.

## 5. What does not compose

The step from `Ω` to the world.  No theorem here says the declared space contains the
truth, that the declared repertoire's outcome functions are the physical ones, or that
the interface's granularity carries the distinctions that matter.  These are the
representation and causal-contract walls, unchanged from the first pass, and the
theorem names them as hypotheses rather than residuals.
