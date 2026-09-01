# Countermodels

Status: exact finite fixtures; unregistered. Definitions are in `src/audit_models.py`.

## Locality

Every row satisfies `(CFP)` definitionally with \(Z=R\times E\).

| case | \(Q\) | \(R\) | \(E\) | residual observation | RP | BL | result |
| --- | --- | --- | --- | --- | --- | --- | --- |
| whole-agent replacement | red/blue complete agents | unit | calm/hostile | agent mission | yes, vacuously | no | `(CFP)+(RP)` permits total replacement |
| fake RP | bits | one residual label | bits | first policy coordinate | yes, canonical second projection | no | named coordinate does not protect behavior |
| extensional local query | idle/query | guard/serve | calm/hostile | residual mode plus exterior | yes | yes | receipt changes; residual behavior does not |
| predictor dependence | idle/query | serve | two predictor truth tables | residual service | yes | yes | fixed response function yields query-dependent prediction |
| strategic exterior | soft/hard | mission | two opponent strategies | mission | yes | yes | fixed strategy yields different actions |
| self-modifying policy | keep/upgrade sensor continuations | serve/guard | quiet/attack | residual mode plus exterior | yes | yes | inquiry self-edit leaves residual continuation fixed |
| delegate in query factor | delegate A/B | task | normal | controller identity | yes | no | decomposition changes protected controller |
| delegate in residual factor | idle/ask | delegate A/B | normal | controller identity | yes | yes | only inquiry instruction changes |
| no nontrivial patch | policy 0/1 | unit | bits | policy mission | yes, vacuously | no | every query difference changes protected residual behavior |

The predictor and strategic examples hold the exterior response *function* fixed, not its
realized output. The delegation pair uses the same kind of world table and changes only
which coordinate the contract protects, showing that CF does not select the boundary.

## NCSS relevance

Let the matter be live before, leave the carrier unresolved, and have no route or
registration after. If `post_active=false` because the monitored factual condition has
genuinely ceased, then `post_live=true` but `post_implements=true`. This is the direct
countermodel to PR71's inference from pre-transition activity.

The necessity suite also contains:

| removed hypothesis | finite transition |
| --- | --- |
| pre-live | no carrier exists before or after |
| post-active | unrepresented/no-route criticism is obsolete; `(IMP)` true |
| post-unrepresented | criticism is registered; `(IMP)` true |
| no post-route | replacement route is adequate; `(IMP)` true |
| local close adequacy | last carrier terminally resolves despite post-defect |
| resolution continuity | unresolved carrier silently disappears |
| fresh successor ancestry | resolution names a non-descendant; matter has no live carrier |

## Registration stages

One four-position trace separates all stages:

| position | capable route | exercised | receipt | registered |
| --- | --- | --- | --- | --- |
| 0 | yes | no | no | no |
| 1 | yes | yes | no | no |
| 2 | yes | yes | yes | no |
| 3 | yes | yes | yes | yes |

`Implements` is true at every position because the route remains capable; only the final
position satisfies `Rep`. Exercise and compiler fairness are outside NCSS.
