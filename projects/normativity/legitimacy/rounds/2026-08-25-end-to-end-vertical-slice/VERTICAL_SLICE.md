# The end-to-end vertical slice

Status: **specification and reference model; unregistered.** All names are
provisional under `AGENTS.md` §6. Nothing here is Lean-checked or registered.
The statements are paper derivations exercised by finite exact histories in
`src/` and `tests/`.

Tags: `[DEF]` true by representation or type · `[THM]` derived · `[ASM]` an
assumption on a parameter · `[OBL]` an obligation left to another layer.

---

## 1. The pipeline

```text
Gamma -> L -> R -> N -> O_n -> kappa_n -> K^N_n -> K_n = K^D_n ∩ K^N_n -> trader -> P_n
                     |                                    ^
                     +--> Values_n --> compileValue -----> |  (via certified LUVs)
                L --> sem_L --> Sigma_n --> PC(Sigma_n) -->+
```

Reflective Integrity supplies everything to the left of `O_n` and is consumed
unchanged. This document specifies the four objects to its right — the value
waist, the cognitive waist, the operative waist, and the compiler — plus the
settlement semantics that feeds the epistemic channel.

## 2. What is taken from Logical Induction, verbatim

At the commit `lean/lakefile.toml` pins,
`c0d885bfb2f84054ada18c65acec672e04d6d380`:

| object | declaration |
|---|---|
| `PCWorld`, `Holds`, `payout`, `ConsistentWith` | `Framework/Criterion.lean` |
| `DeductiveProcess` — `D : N -> Finset Sentence`, `mono` | `Framework/Criterion.lean` |
| `LUV` — `gt : Q -> Sentence` | `Framework/Expectations.lean` |
| `LUV.expect P n = expectApprox (P n) (n+1)` | `Framework/Expectations.lean` |
| `LUV.expectAffine k` and `expectAffine_price` | `Properties/ExpectationAffine.lean` |
| `AffineCombination`, `LUVCombination`, `meshAffine` | `Framework/Affine.lean`, `Properties/ExpectationProperties.lean` |
| `PCWorld.ValuesAt`, `ExactTheoryPresentation` | `Framework/Expectations.lean`, `Properties/ExpectationProperties.lean` |
| `RationalConstraintSchedule`, `RationalPolytope` | `lean/Workspace/Normativity/Contrib/` |
| `end_to_end_of_constraints_effective` | `Contrib/EffectiveRepresentation.lean` |

**No new security is introduced.** The whole of `Expect(X)`'s compilation is
`expectAffine`, which is already there, and `expectAffine_price` is already the
statement that its day-`n` price is `E_n(X)`.

## 3. The value waist

```text
ValueSpec  = ( spec_id , payload : opaque , exposures : QueryCode -> Exposure )
Exposure  ::= CertifiedLUV | NonExposure(reason)
CertifiedLUV = ( luv : LUV , code_witness , values : World -> Q , origin )

compileValue : ValueSpecCode x QueryCode -> Exposure          -- total into the sum
```

`code_witness` names the threshold-code efficiency certificate
(`RpnThresholdCodes` / `PolyThresholdCodes`); `values` is the world-value
presentation (`ExactTheoryPresentation.value`). Those two are exactly what the
pinned expectation theorems consume, and the waist carries them and nothing
else.

**V1 — the specification is opaque.** `payload` is read by nothing. It need not
be a utility function, be scalar, be complete, or be comparable across
dimensions. `[DEF]`

**V2 — quantities are named by the specification, not by what is active.**
`compileValue(v, q)` produces a LUV whose threshold family is determined by `v`
and `q`. There is no argument meaning "the specification currently in force", so
a historical quantity has no expression that could reinterpret it. `[DEF]`

**V3 — the registry is write-once.** Admitting `spec_id` twice is refused. `[DEF]`

**V4 — non-exposure is a value.** A query with no legitimate LUV returns
`NonExposure`, leaves every other exposure of the specification intact, and is
not an error. `[DEF]`

**V5 — boundedness is checked.** An exposure whose certified values leave
`[0,1]` is refused, because `LUV` is a `[0,1]`-quantity and the expectation's
`[0,1]` bounds are proved from the price bounds only for such a quantity. `[DEF]`

Several value specifications may be active. Nothing downstream reads the value
projection, so plurality costs the operative layer nothing.

## 4. The cognitive waist

```text
CognitiveQuantity ::= Prob (phi : Sentence) | Expect (X : CertifiedLUV)

[[Prob(phi)]]_n   = P_n(phi)
[[Expect(X)]]_n   = E_n(X) = (X.expectAffine (n+1)).price P n
```

**C1 — `Expect` is derived, not primitive.** Its day-`n` denotation is the price
of a bundle of ordinary sentences the market already prices. `[DEF]`

**C2 — origin is invisible downstream.** Two `CertifiedLUV`s with the same
`luv` compile identically regardless of `origin`, so a value-generated quantity
and an ordinary LUV are interchangeable. `[THM]`, `test_value_waist.py`

## 5. The operative waist

Standing carries an injunction through **`PForce`**, which Reflective Integrity
already has. No new payload constructor is introduced for it, and `O_t` reads
one constructor rather than two.

```text
Ineq       = ( atoms : (Q x CognitiveQuantity)* , const : Q , rhs : Q , label )
             read as   sum_i c_i q_i + const <= rhs
Injunction = ( injunction_id , ineqs : Ineq* )
```

**O1 — operative terms only.** The payload holds coefficients, quantities and
right-hand sides. It holds no authority, reason, derivation, predecessor,
budget, tolerance, intensity or liability. `[DEF]`

**O2 — well-formedness is syntactic and prior to compilation.** An injunction
with no inequality, a constant-true or constant-false inequality, an inexact
coefficient, a non-quantity operand, or an uncertified LUV is refused at the
waist. `[DEF]`

**O3 — the payload's reference fields are inert.** `PForce`'s `commitRef` and
`schemaRef` are not read by `kappa`. Why an injunction was issued is recovered
through its standing's minted id, which stamps the `tau` of the issuing event.
`[THM]`, `test_operative_waist.py`

## 6. The projection

```text
O_n = { (i, J_i) : Std_n(i) = (Active, _, PForce(_, _, J_i)) }
```

**P1 — the projection is the graph, not the image.** Reflective Integrity's
§35 projection is `O_t = { compiledClause p : ... }`, a set of clauses. Two
distinct active standings carrying equal payloads collapse in it, and no member
of it resolves to an event. Both enforcement provenance and per-term conflict
attribution need the identity, so the slice consumes the pairing. **This is a
local repair to the vertical-slice interface and not to any store, constructor
or conservation law of the core.** `[DEF]`

**P2 — the projection is boring.** No reason is reinterpreted, no current value
is substituted for a historical reference, nothing is optimised away, nothing is
weakened to preserve feasibility, and no conflict is silently prioritised.
`[DEF]`

## 7. The compiler

```text
kappa_n : O_n -> ( coords : Sentence* , rows : CompiledRow* )
```

Each `Expect(X)` expands to `sum_{i<n+1} (1/(n+1)) <X > i/(n+1)>`; each
`Prob(phi)` to `phi`. Coefficients on repeated sentences are summed. Each
inequality `sum c_i q_i + const <= rhs` becomes one row `(-a) . p >= const - rhs`
in the sign convention of `enforcement.Row`, tagged with its standing id and
inequality index.

**K1 — compilation exactness.** For every price vector over the day's fragment,
a compiled row's slack equals `rhs` minus the inequality's own left-hand side
evaluated through `[[.]]_n`. `[THM]`, `test_compilation.py`

**K2 — the fragment has no repeats.** Two LUVs sharing a threshold sentence, or
a `Prob` term naming one, contribute one coordinate with summed coefficients.
This is `RationalConstraintSchedule.nodup`, and it is a real condition rather
than a formality. `[THM]`

**K3 — semantic rigidity, stated on values.** A frozen payload compiles at day
`n` to a system in `|coords_n|` dimensions and at day `n+1` to one in more. The
rigidity is not syntactic identity of the rows — they demonstrably differ — but
that at every day the compiled row's slack is the same function of
`([[q]]_n)_q`. `[THM]`, `test_compilation.py`

```text
K^N_n = { p in [0,1]^coords : every row holds }
```

## 8. The epistemic channel

```text
sem_L    : SettleId -> Finset Sentence                         -- total, rigid
Sigma_n  = D_n  union  { sem_L(l) : l in L_n }
W_n      = PC(Sigma_n) = { v : forall phi in Sigma_n, v.Holds phi }
K^D_n    = conv { v|_coords : v in W_n }
```

`sem_L` is the round's third parametric interpreter, in the shape the core uses
for `[[.]]_S` and `[[.]]_D`. `SETTLEMENT_SEMANTICS.md` carries the audit; the
assumptions are:

| | assumption |
|---|---|
| **E1** | `sem_L` is a function of the settlement's identity alone, fixed at admission, and reads no reason, standing or normative event `[ASM]` |
| **E2** | `sem_L(l)` is a finite set of sentences; the empty set is admissible and denotes nothing `[ASM]` |
| **E3** | `n |-> Sigma_n` is computable `[OBL]` |

**E4 — monotonicity is a theorem.** `L` is append-only and `sem_L` is per-entry
and rigid, so `Sigma_n subset Sigma_{n+1}`, which is
`DeductiveProcess.mono`. `[THM]`, `test_settlement.py`

**E5 — the stage's threshold chain covers every day's grid.** A threshold no
chain sentence mentions is an unconstrained atom, and a world may then hold
`X > 3/4` while denying `X > 1/3`. Since the day's grid moves and the stage does
not, the chain a trajectory needs is the one over the union of the grids it will
be inspected at. `[THM]`, `test_settlement.py`

## 9. Conflict

Four states, each detected and certified, none resolved.

| state | condition | certificate |
|---|---|---|
| **A-malformed** | a payload fails O2 | the failing clause, named |
| **A-self-inconsistent** | one injunction's rows plus the cube are infeasible | Farkas multipliers over that standing's indices |
| **B-empty-intersection** | individually satisfiable, jointly not | Farkas multipliers naming each standing |
| **C-incompatible** | `K^N_n != {}`, `K^D_n != {}`, intersection empty | Farkas multipliers naming the injunction and the hull |
| **D-stage-unsatisfiable** | `PC(Sigma_n) = {}` | minimal conflicting source sets |

**F1 — infeasibility certificates carry provenance.** Fourier-Motzkin combines
constraints by positive multiples, so multipliers compose linearly and the
derived contradiction arrives holding `lambda >= 0`, `sum lambda_j a_j = 0`,
`sum lambda_j b_j < 0`. The support names compiled rows, and a compiled row
names its standing and inequality index. `[THM]`, `test_conflict.py`

**F2 — the certificate is rechecked, not trusted.** `conflict.certify`
recomputes both identities against the original rows. `[DEF]`

**F3 — an empty demand emits no region.** No relaxation, no dropping, no
priority rule. `[DEF]`

## 10. Composition

```text
K_n = K^D_n ∩ K^N_n
```

**X1 — the channels are independent.** `K^D_n` is a function of `Sigma_n` and
the fragment and reads no injunction; the compiled rows are a function of `O_n`
and the day and read no world. `[THM]`, `test_composition.py`

**X2 — composition is decided in barycentric coordinates.** `K^D_n` arrives as
a vertex list, and turning one into rows is facet enumeration the repository
declines to perform. A point of the intersection is `sum_v lambda_v v` with
`lambda` in an explicit polytope, so nonemptiness, a Farkas certificate and a
generating vertex list for `K_n` all come from the weight system. `[DEF]`

## 11. Traderization

The obligations, each named against the declaration that asks for it:

| obligation | source |
|---|---|
| priceable, in traded coordinates | `RationalConstraintSchedule.coords` |
| each coordinate listed once | `RationalConstraintSchedule.nodup` |
| tolerance strictly positive | `RationalConstraintSchedule.tol_pos` |
| nonempty, with a witness | `RationalPolytope.verts_ne`, `force_api.compile_force` |
| vertices are credences | `RationalConstraintSchedule.region_in_cube` |
| effective presentation | `RationalConstraintSchedule.Computation` `[OBL]` |
| **admissibility** | `end_to_end_of_constraints_effective`, hypothesis `hadm` |
| bounded cumulative liability | `force_api.compile_safe_force` `[OBL]` |

**T1 — emptiness is not expressible in the schedule type.** `RationalPolytope`
carries `verts_ne`, so a region with no vertices has no value of the type. An
empty `K_n` is refused before a schedule exists, which is the feasibility
adapter's job and not the mechanism's. `[DEF]`

**T2 — the inertness dichotomy.** `[THM]`

> Let `K^N_n` be an intersection of half-spaces and `K^D_n = conv(W_n|_coords)`.
> If every world of `W_n` satisfies every row — which is `hadm` — then every
> vertex of `K^D_n` lies in `K^N_n`; `K^N_n` is convex, so `K^D_n subset K^N_n`,
> so `K_n = K^D_n`.

*Contrapositive, which is the operative statement:* **an injunction that changes
the price region at all falls outside the hypothesis of the unconditional
traderization theorem.** Admissibility and deductive inertness are the same
condition, and `test_composition.py` checks that they coincide on every
non-blocking case in the suite.

**T3 — what is left is the charged branch.** A region excluding live worlds is
enforceable, at `(eps_t + M_t) . d_t / delta_t` per date charged against a
finite account, and safe when `sum_t` of that is finite. That sum's finiteness
is a property of the source's trajectory and is established here for nothing.
`[OBL]`

**T4 — settlement is what makes force cheap.** The exclusion depth is measured
over `W_n`, and settling removes worlds, so a fixed payload's charge is
non-increasing as the record settles and reaches zero exactly when what it
demands is already settled — at which point, by T2, it is inert. `[THM]`,
`test_composition.py`

## 12. The resulting cognitive state

`P_n` is the projection of the incoming price vector onto `K_n`, certified by
the variational inequality against the generating vertices. This is the `target`
of the schedule, and the conformance half of the traderization theorem bounds
the displayed price's distance from it by the day's tolerance.

**R1 — the readings are the quantities.** `[[Prob(phi)]]_n` and
`[[Expect(X)]]_n` read off `P_n` satisfy every compiled row. `[THM]`,
`test_toy.py`

## 13. What this does not establish

- Nothing is Lean-checked and nothing is registered. The Lean declarations named
  above are cited for their *hypotheses*; no theorem here is proved against them.
- `E3` and the effective-presentation obligation are **declared, not proved**.
  The round's schedules are computable by construction and no `Primrec`
  statement is made.
- **T3 is the open one.** No normative source in this repository is shown to
  have summable enforcement liability, and T2 says every contentful one needs it.
- The reference model is finite, propositional, and exact. Its `Sentence` is a
  propositional formula and its LUVs are threshold families over atoms; the
  first-order content the pinned dependency discloses as modelling choices is
  not reconstructed here either.
- `sem_L` totality is argued from the type of `DeductiveProcess`, not from a
  survey of what settlements can be.
- The infeasibility search is complete for the systems it is run on and is
  budgeted; a budget overrun raises rather than answering.
