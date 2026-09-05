# Non-Capture certificate

Status: proposed interface, with a Lean-proved structural implication and exact
necessity witnesses. Every new name is provisional.

## Types held fixed

An application supplies a history prefix `H`, a protected principal or relation `P`, a
coverage contract

\[
\sigma=(a,\Gamma,\operatorname{Rel},\mathsf{Adeq},\mathsf{Disp}),
\]

a declared intervention class `J`, and external semantics `I` producing a coupled
history `H^j` for each `j in J`. The same criticism identity, target, applicability
predicate, receipt criterion, registration criterion, and route-quality class are read
in `H` and `H^j`; authenticated transport may replace literal identity.

For `c in Gamma`, define

\[
\begin{aligned}
\operatorname{Active}_K(c)&:=\operatorname{Rel}_K(c)\land
  \neg\mathsf{Disp}_K(c),\\
\operatorname{Live}_K(c)&:=\operatorname{Active}_K(c)\land
  \neg\operatorname{Rep}_K(c),\\
\operatorname{Covered}_K(c)&:=\operatorname{Live}_K(c)\Rightarrow
  \exists R\;\mathsf{Adeq}_K(R,c).
\end{aligned}
\]

`Adeq` contains route admissibility, target-preserving receipt efficacy, registration
capability, and any declared resource bound. It may name settlement access if the
application makes settlement a route; the generic theorem does not require that choice.
Let `W(c)` be the protected set of actual-prefix routes.

## Exact certificate

`CoverageActual(sigma,W,H)`:

\[
\forall c\in\Gamma,\quad
\operatorname{Live}_H(c)\Rightarrow
\exists R\in W(c)\;\mathsf{Adeq}_H(R,c).
\tag{A}
\]

`NonCaptureCert(P,Gamma,J,I)` is the conjunction of:

\[
\begin{aligned}
(S)\quad &\forall c,j,\quad
 \neg\operatorname{Live}_H(c)\land\operatorname{Live}_{H^j}(c)
 \Rightarrow \exists R\;\mathsf{Adeq}_{H^j}(R,c);\\
(R^+)\quad &\forall c,j,\quad
 \operatorname{Live}_H(c)\land\operatorname{Live}_{H^j}(c)\Rightarrow\\
&\qquad\left[
 \bigl(\forall R\in W(c),\ \mathsf{Adeq}_H(R,c)\Rightarrow
                         \mathsf{Adeq}_{H^j}(R,c)\bigr)
 \lor \exists R'\;\mathsf{Adeq}_{H^j}(R',c)
 \right];\\
(P)\quad &\forall c,j,\quad
 \operatorname{Rel}_{H^j}(c)\Rightarrow
 \operatorname{StandsOnCarrier}_{H^j}(P,c).
\end{aligned}
\]

The carrier in `(P)` is the coverage issue for an undisposed concern and the successor
that carries its load after an authorized disposition. Applicability, not activity, is
the antecedent: disposition does not erase the inherited load.

`RobustOpen(P,sigma,J,I)` is

\[
\forall c\in\Gamma,j\in\mathcal J,\quad
\operatorname{Covered}_{H^j}(c)\land
(\operatorname{Rel}_{H^j}(c)\Rightarrow
 \operatorname{StandsOnCarrier}_{H^j}(P,c)).
\]

**Interface theorem (lean-proved).** `(A) + (S) + (R+) + (P)` implies
`RobustOpen`. Split on `Live_H(c)`. The false arm is `(S)`. In the true arm `(A)` gives
an adequate protected route; `(R+)` either preserves it or supplies a replacement.
`(P)` gives the standing conjunct.

`(S),(R+),(P)` is minimal only relative to this factorization and conclusion. `(S)` and
`(R+)` together are a case split of counterfactual coverage; an external framework can
instead certify counterfactual coverage directly. The split identifies when actual
Coverage contributes evidence.

## Component certificate

For applications that certify persistence rather than a replacement directly, replace
`(R+)` by three component clauses, restricted to `R in W(c)` and histories where the
concern is live in both branches:

- `(Ra)` actual route admissibility implies counterfactual route admissibility;
- `(Rb)` actual target-preserving receipt efficacy implies counterfactual efficacy;
- `(Rc)` actual registration capability implies counterfactual registration capability.

Their conjunction implies route persistence. The converse needs every protected route
to be actually adequate. Componentwise preservation is stronger off that set and is not
part of the minimal bill.

## Necessity attacks

All attacks have one concern, one intervention, actual Coverage, and every other clause
in the indicated schema. `src/fixtures.py` supplies the complete tables.

| omitted clause | intervention | surviving facts | failure |
|---|---|---|---|
| `(S)` | activate an actually inapplicable concern | `(R+)`, `(P)` | live counterfactual has no route |
| `(S)` | prevent an actual registration | `(R+)`, `(P)` | de-represented counterfactual has no registering route |
| `(R+)` | forbid the sole protected audit | `(S)`, `(P)` | actual route has no persistent or replacement route |
| `(P)` | revoke `P`'s licence, leaving the audit intact | `(S)`, `(R+)`, counterfactual Coverage | `P` has no standing |
| `(Ra)` | forbid the audit | `(S)`, `(Rb)`, `(Rc)`, `(P)` | no admissible route |
| `(Rb)` | install a reactive constant receipt | `(S)`, `(Ra)`, `(Rc)`, `(P)` | receipt does not expose the target |
| `(Rc)` | delete the registration target | `(S)`, `(Ra)`, `(Rb)`, `(P)` | receipt lands nowhere |

`F0` supplies a nonvacuous instance: the actual concern is live, two routes are adequate,
one protected route persists under one intervention, another intervention makes the
concern inapplicable, and a third registers it.

## Clauses rejected

- Concern/target identity and applicability transport are typing requirements on `I`,
  not Boolean certificate clauses. If `I` may re-anchor a two-valued target to a
  constant, a dead sensor falsely passes efficacy (`REANCHOR`). If applicability is the
  process's own recognition bit, forgetting the concern makes the conclusion vacuous
  (`FORGET`).
- Disposition persistence is not separate. Authorized disposition moves the relevant
  load to a successor; `(P)` governs standing there. Authorization and faithful transfer
  belong to Integrity/Answerability.
- Receipt production is `(Rb)` and receipt registration is `(Rc)`, not another clause.
- Settlement timing and evaluator protocol do not occur in `RobustOpen`. The exact
  `SETTLEMENT` and `EVALUATOR` fixtures vary them while preserving the certificate and
  conclusion.

## External obligations

An application must authenticate `Gamma`, `W`, `J`, the coupling that produces each
`H^j`, stable or transported contract meanings, the agency boundary, and the protected
principal/carrier relation. It must then discharge `(S)`, `(R+)`, and `(P)`, or a stated
stronger component certificate. The generic theory does not construct counterfactuals,
select the correct scope, prove the coupling causal, certify the settlement engine, or
certify the evaluator's practical/value semantics.
