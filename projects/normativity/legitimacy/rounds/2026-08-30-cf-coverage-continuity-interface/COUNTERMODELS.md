# Finite hostile examples

Status: exact finite fixtures; unregistered. The executable tables are in
`src/finite_models.py`. Every Boolean classification is recomputed by
`tests/test_finite_models.py`.

## Conventions

For rows 1–15 and 18–20, \(Z=\{0,1\}\) unless stated otherwise and
\(T(z)=z\). A world is the triple

\[
\beta(q,z)=(\widehat T,Y,\operatorname{Rep}).
\]

`⊥` is no receipt. `Access` means one admissible route policy has
\(T=d_q\circ Y_q\). `Registration` means robust counterfactual registration under
\(q^{\rm act}\), not a historical event; the follow-up audit separates the four stages.
`Implements` requires target preservation and one route with both access and
registration. “PE” is the Coverage specialization in `PROPER_EXERCISE.md`, not a
structural Continuity check.

## Exact patch tables

| # | case | \(Q;q^{act}\) | \(Z,T\) | exact \(\beta(q,z)\) |
| --- | --- | --- | --- | --- |
| 1 | passive sensor | `{idle,read}; read` | bits; `z` | `read ↦ (z,z,1)`; `idle ↦ (z,⊥,0)` |
| 2 | active target-preserving experiment | `{dose0,dose1}; dose1` | mechanism bit; `z` | `dose_i ↦ (z,(dose_i,z xor i),1)` |
| 3 | experiment changes target | `{set0,set1}; set1` | `{base}`; `T(base)=0` | `set_i ↦ (i,i,1)` |
| 4 | self-fulfilling test | `{announce0,announce1}; announce1` | `{person}`; realized-outcome target `0` | `announce_i ↦ (i,i,1)` |
| 5 | sensor destruction, post-state | `{destroy}; destroy` | bits; `z` | `(z,⊥,0)` |
| 6 | replacement | `{old,new}; new` | bits; `z` | `q ↦ (z,(q,z),1)` |
| 7 | ontology deletion, world target intact | `{read_without_concept}; same` | bits; `z` | `(z,z,0)` |
| 8 | ontology translation | `{old_words,new_words}; new_words` | bits; `z` | old receipt `bad/good`, new receipt `red/blue`; both `(z,label,1)` |
| 9 | delegation | `{idle,delegate_read}; delegate_read` | target bit plus fixed honest delegate response strategy; `z` | delegate strategy returns `(z,z,1)` on `delegate_read`, `(z,⊥,0)` on `idle` |
| 10 | delegation to censor | `{delegate_read}; same` | target bit plus fixed censoring strategy; `z` | censor response `(z,⊥,0)` |
| 11 | predictor dependence | `{idle,probe}; probe` | target bit plus one fixed predictor response function; `z` | `(z,(predicts,q),0)`; the fixed function, not one output, is in `Z` |
| 12 | strategic responder | `{soft,hard}; hard` | target bit plus one fixed response strategy; `z` | `hard ↦ (z,z,1)`; `soft ↦ (z,⊥,0)` |
| 13 | route never exercised | `{idle,read}; idle` | bits; `z` | as row 1 |
| 14 | receipt never registered | `{read}; read` | bits; `z` | `(z,z,0)` |
| 15 | contract matter persists, implementation broken | `{idle}; idle` | bits; `z` | `(z,⊥,0)` |
| 16 | scope silently shrunk | `{read_c0}; same` | `Z={0,1}²`; protected target for omitted `c1` is `T(a,b)=b` | `(b,a,1)`; implementation reads only `c0` |
| 17 | legitimate terminal retirement | `{idle}; idle` | `{retired}`; constant `0` | `(0,⊥,0)` with anchored `Disposition=true` and `Active=false` |
| 18 | known inquiry prerequisite discharged | `{idle,investigate}; investigate` | bits; `z` | investigate `(z,z,1)`; idle `(z,⊥,0)` |
| 19 | procedural issue route, no physical route | `{idle}; idle` | bits; `z` | `(z,⊥,0)`; a separate Continuity issue is named in `Routes(d_T)` |
| 20 | physical route, no normative issue | `{read}; read` | bits; `z` | `(z,z,1)` with no coverage `Due`/matter (`Active=false`) |

Rows 9–12 use a strategy in the complement. Different responses across \(q\) therefore
do not violate “same exterior response structure.” Holding one realized response fixed
instead would be the predictor/strategic-agent error.

## Classification

| # | TP | Access | Registration | Implements | Continuity sees | PE permits transition? |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | yes | yes | yes | yes | live maintenance matter; no lifecycle event required | yes |
| 2 | yes for mechanism | yes | yes | yes | same | yes |
| 3 | no | yes | yes | no | nothing unless a coverage failure is materialized | no as inquiry on this target |
| 4 | no for realized outcome; yes could hold for latent type | yes | yes | no for chosen target | same as 3 | no for chosen target |
| 5 | yes | no | no | no | matter stays open unless explicitly resolved; NSA may take service arm | only if failure remains open or disposition is authorized |
| 6 | yes | yes | yes | yes | same matter, no successor | yes |
| 7 | yes | yes | no | no | deletion alone changes no issue or `Met` | only with open registration failure |
| 8 | yes via decoder/transport | yes | yes | yes | same contract if transport is certified | yes |
| 9 | yes | yes | yes | yes | same matter; delegate issue optional implementation detail | yes with authenticated delegation |
| 10 | yes | no | no | no | open matter/failure if materialized | no clean handoff |
| 11 | yes | no | no | no | no structural distinction from an honest receipt map | no adequate route |
| 12 | yes | yes | yes | yes | implementation route exists | yes |
| 13 | yes | yes | no on actual path | yes | Continuity sees an open matter, not non-exercise | locally yes; persistent fairness fails |
| 14 | yes | yes | no | no | registration failure must be compiled to become visible | no clean success |
| 15 | yes | no | no | no | matter can persist forever; NSA permits unbounded ineffective attention | yes only as represented repair state |
| 16 | yes | no for anchored `c1` | yes for `c0` only | no for anchored contract | anchored issue identity persists, but structure cannot inspect scope | no without translated successor/disposition |
| 17 | yes | not owed | no | yes vacuously | anchored `Resolve` may close terminally | yes |
| 18 | yes | yes | yes | yes | `q` waits on `d_T`; inquiry issue is procedural route; success permits persistent `Met(d_T)` | yes |
| 19 | yes | no | no | no | `Routes(d_T)` nonempty, so no `NoRouteWait`; physical impossibility is invisible | no adequate realization |
| 20 | yes | yes | yes | vacuous/no contract | no `Due`, issue, prerequisite, or matter | neutral; no owed exercise |

## What the examples establish

Rows 3–4 show access without target preservation. Rows 7 and 14 show exposure without
registration. Row 13 shows implementation without exercise. Rows 19–20 separate
procedural and interaction routes in both directions. Rows 5 and 15 show that Continuity
can preserve an answerability locus while physical implementation remains permanently
broken. Row 16 shows that historical anchoring requires semantic scope checks: issue
identity alone cannot compare \(\Gamma\).

The target-preservation result for row 2 depends on choosing the mechanism as target. If
the target were the post-dose response, it would join rows 3–4. This is a feature:
observation versus manipulation is target-relative.
