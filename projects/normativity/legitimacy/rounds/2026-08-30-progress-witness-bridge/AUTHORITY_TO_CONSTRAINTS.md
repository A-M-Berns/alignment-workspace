# Authority to operative value constraints

Status: candidate realization theorem; unregistered. This interface is separate from
the algebraic Progress and witness theorems.

## 1. Why authority appears here

Grounded Replay is not consumed by Persistent-Wait, No Structural Abandonment, PR69
Uptake, or the Restricted Stagnant-Tail Witness Lemma. Those results are structural or
algebraic.

The first natural downstream consumer is interpretive: a realized `K_n` purports to be
the region licensed by the reasoner's represented normative practice. Every operative
row should therefore say both which reason supports it and which admitted authority
licenses compiling that kind of reason into a value constraint.

Grounded Replay can authenticate the authority ancestry. It cannot establish compiler
soundness, semantic truth, or current correctness of the row.

## 2. A small typed compiler interface

At strict prefix `H_n`, define the following data.

```text
RowPayload:
  support     : finite episode-local service coordinate list
  coeff       : rational vector on support
  lowerBound  : rational

RowProvenance:
  reasonOccurrence
  immutable reason sources and target
  applicability claim
  episode and response surface
  licenseOccurrence
  license mode: current | episode-anchored
  compiler version / schema identity

OperativeRow := RowPayload + RowProvenance
```

The compiler is a strict-prefix partial function:

```text
compile_n(r, q, surface, license) -> OperativeRow | not-applicable | conflict
```

It may emit a row only for `ServiceCompare` or an applicable
`ConditionalServiceCompare`. `Evidence`, `Question`, `Incompatibility`, and a derived
LP certificate are non-row targets.

## 3. Operative Constraint Grounding

Let `Adm_n` be settled Continuity's historical admitted set. Require:

\[
c\in C_n^{\mathrm{operative}}
\Longrightarrow
\exists r,\lambda,q:\
\begin{cases}
c=\operatorname{compile}_n(r,q,\lambda),\\
r\text{ is enabled and applicable at }H_n,\\
\lambda\in\Adm_n,\\
\operatorname{Licenses}(\lambda,\operatorname{schema}(r),q,c),\\
\operatorname{Prov}(c)=(r,\lambda,q,\ldots).
\end{cases}
\tag{OCG}
\]

Two license modes are needed.

1. **Current.** `lambda in L_n` currently licenses a newly compiled row. Since
   `L_n subset Adm_n`, historical admission follows.
2. **Episode-anchored.** `lambda` licensed the compiler/evaluator when `q` opened and
   remains the recorded authority for that episode even if it later loses standing.
   The settled historical Grounded Replay theorem covers removed admitted occurrences,
   so prospective revision does not erase the ancestry of an old row.

Requiring every old row's license to remain in `L_n` would recreate evaluator shedding:
standing revision could silently remove a pending episode's evaluative basis. The
episode-anchored mode instead ends only by explicit reason or issue disposition.

## 4. Grounding theorem

**Theorem (Operative Row Grounding).** Assume settled Continuity Requirement 1 and OCG.
For every `c in C_n^operative`, the license occurrence recorded in `Prov(c)` has a
finite authorization tree whose leaves lie in `G` and whose positions strictly decrease.

**Proof.** OCG supplies `lambda in Adm_n`. Settled Grounded Replay
`StandingTrace.grounded_replay_admitted` supplies the authorization tree for every
member of `Adm_n`. QED.

**Corollary.** Every row of the compiled normative portion of `K_n` has both finite
reason provenance and finite authorization provenance. Structural cube rows are marked
`structural` and are not misreported as normative rows.

This is a genuine theorem consumer of Grounded Replay. It remains conditional on OCG,
which is exactly the missing relation between authority, reason schemas, episodes, and
compiler outputs.

## 5. Applicability and defeat

Compilation reuses the reason-state discipline rather than adding attack edges.

- The occurrence includes `App(schema,case,stage)` among its immutable sources.
- `Enabled_B(r)` checks all adopted-claim and transcript sources.
- A conditional comparison additionally checks its public condition at `H_n`.
- Defeat or withdrawal removes an applicability/source claim from the stance or records
  an accepted disposition. The occurrence remains historically addressable, while its
  row is absent from the next `C_n^operative`.
- Nothing in event `e_n` changes the rows used to score `p_n`; it affects `n+1`.

Repeatedly dropping and readopting identical content creates new reason occurrences and
new provenance. It does not reactivate the old occurrence or rewrite its history.

## 6. Building `K_n` and handling conflict

Let `C_n^operative={c_1,...,c_k}`. With cube bounds,

\[
K_n=\{v\in[0,1]^{X}:c_j^Tv\ge h_j\text{ for every }j\}.
\]

Before `K_n` is supplied to Progress or traderization, a feasibility checker must return
one of:

```text
Feasible(witness or certificate)
Infeasible(conflict core / certificate)
Unknown(computation did not certify either)
```

- `Feasible` exposes nonempty `K_n`.
- `Infeasible` does not drop a convenient row. It records the conflict core and opens or
  updates an ordinary Continuity issue whose service surface includes investigation,
  defeater assessment, and explicit adjudication.
- `Unknown` likewise withholds the region rather than pretending nonemptiness.

Progress over the original comparison region is silent while no nonempty `K_n` exists.
A separately licensed conflict-handling reason may still define a nonempty service-level
comparison such as `open-adjudication > conceal-conflict`.

## 7. Conditional and local reasons

Two cases must be distinguished.

### Prefix-condition applicability

“If receipt `ell` exists, prefer `y` to `x`” is handled predictably: when `ell in H_n`,
the row is globally operative; otherwise it is absent and `c_n=0`. This fits the common
`K_n` interface.

### Value-face locality

“Among valuations on face `F`, prefer `y` to `x`” does not imply a global row over `K_n`.
It may be used only if independent operative constraints establish `K_n subset F`, or
if an explicit context-selection event creates an episode whose region is `K_n cap F`.
Taking the infimum over `F` while dissenting valuations remain admissible would turn a
local reason into false unanimity.

The restricted witness theorem uses only the first kind after applicability has fired.

## 8. The dual certificate's place

For `K={v:Gv>=h}` and repair coefficient `c`, a dual witness

\[
\lambda\ge0,\qquad G^T\lambda=c,\qquad h^T\lambda\ge\gamma
\]

is best represented as a **derived proof receipt**, not a new source of normative
authority and not an operative row.

```text
GainCertificate:
  strict-prefix row ids and their provenance
  repair program id and decision surface
  coefficient c (or response distribution from which it is derived)
  rational dual multipliers
  certified lower bound
```

The checker recomputes all three dual conditions exactly. The receipt can then be a
two-sorted transcript source for a next-position repair proposal or explanation
occurrence. This preserves provenance without self-reference:

1. `K_n` is compiled before the certificate;
2. the certificate is not among the rows defining the `K_n` it certifies;
3. strict-prefix timing prevents it from supporting its own same-batch admission;
4. a future region requires a fresh check, so old dual multipliers do not certify changed
   rows.

Calling the receipt itself a “reason for change” is acceptable only in this derived
epistemic sense. Its normative force comes from the cited operative rows and their
licenses, not from the certificate's existence.

For the pairwise witness theorem, the direct reason row already proves the comparison;
the date-specific dual multiplier is `p_n(x)`. The certificate is useful provenance,
not a missing mathematical premise.

## 9. What the theorem does and does not buy

Operative Row Grounding establishes:

\[
\text{operative value row}
\Longrightarrow
\text{finite reason provenance + finite authorization replay}.
\]

It does not establish:

- truth or moral correctness of the row;
- that the licensed schema should have authority;
- nonemptiness of the conjunction;
- a repair corresponding to an arbitrary affine row;
- Persistent Relevance or defect persistence;
- Uptake or traderization safety.

Those separations are features. Authority continuity authenticates why the realized
constraint is attributable to the represented practice, while the Progress algebra
uses only the constraint once supplied.
