# Theorem ledger

Statuses: **PROVED (single derivation)** · **EXECUTABLE FINITE WITNESS** ·
**ARCHITECTED** · **CONDITIONAL** · **CONJECTURED** · **OPEN**.

Nothing here is registered in `projects/leverage/CLAIMS.md`. A registry entry is
a maintainer act and this round does not take it; `DECISIONS.md`'s *Awaiting the
author* carries the request.

**A repository being ready for a φ-regret test is not evidence that φ-regret has
been achieved.** No row below claims a regret bound, and none claims a
self-correction guarantee.

## 1. Definition and interface completion

| id | claim | status | evidence |
|---|---|---|---|
| PR-D1 | The lawful-edit interface is total on well-formed inputs: every certificate receives `admitted`, `rejected` with a code, or `unresolved` with a code. | PROVED (single derivation) | Each check is a finite test over finite data; the function returns on every branch. `src/certificates.py::check` |
| PR-D2 | Five of the nine interface checks are mechanical, three rest on a named supplied relation, and one is a property of the reader's declaration. | PROVED (single derivation) | The table in `REASONS_RESPONSIVENESS_INTERFACE.md`, read against `PolicySuite` |
| PR-D3 | A certificate cannot be a function of the charge of the edit it licenses. | PROVED (single derivation) | Structural: `CERTIFIER_FOOTPRINT` omits `charges`, and `PrefixReader._read` raises on an undeclared table before returning. The same discipline as `GR-J1` |
| PR-D4 | v1 replay is deterministic, and identity replay reproduces the recorded run. | EXECUTABLE FINITE WITNESS | Fifteen fixtures; `Substrate` tests |
| PR-D5 | Every field of the substrate has a declared replay treatment. | PROVED (single derivation) | The table in `REPLAY_SEMANTICS.md` is exhaustive over `src/model.py`'s record types |
| PR-D6 | The loss has a fixed sign convention and is mechanically computable from the record. | PROVED (single derivation) | `charge_of`; `PHI_REGRET_OBJECTIVE.md` §2–3 |

## 2. Separation witnesses

Each is a displayed finite instance. None generalises.

| id | claim | status | witness |
|---|---|---|---|
| PR-W1 | Profitable does not imply lawful. | EXECUTABLE FINITE WITNESS | `E1`: an edit worth 2 refused as `certificate.replacement_unsupported` |
| PR-W2 | Later endorsement does not imply lawful, in either of its two forms. | EXECUTABLE FINITE WITNESS | `E2`: `certificate.not_historically_available` and `certificate.successor_ratification` |
| PR-W3 | The existence of a live reason does not license an arbitrary edit citing it. | EXECUTABLE FINITE WITNESS | `E6`, `E8` |
| PR-W4 | A ground's licensing force is indexed to the prefix: the same edit is lawful before an undercutter and not after. | EXECUTABLE FINITE WITNESS | `E7`: admitted at date 3, `certificate.defeated_ground` at date 9 |
| PR-W5 | Burden laundering is profitable in this substrate and is refused. | EXECUTABLE FINITE WITNESS | `E8`: charge 2 → 0 by striking the obligation; `burden.dropped` |
| PR-W6 | A nontrivial edit is certified lawful and its replay difference is exactly one occasion's charge. | EXECUTABLE FINITE WITNESS | `E3` |
| PR-W7 | A recurrent remediable failure produces lawful-edit regret linear in the horizon. | EXECUTABLE FINITE WITNESS | `E4`: `2/3` per occasion at horizons 12, 24, 48 |
| PR-W8 | A non-recurrent lawful improvement does not. | EXECUTABLE FINITE WITNESS | `E5`: 8 at every horizon |
| PR-W9 | Resource feasibility excludes a fully licensed comparator, and the exclusion is not a charge comparison. | EXECUTABLE FINITE WITNESS | `E13`: regret 6 unaffordable, 4 affordable, supremum 4 |

## 3. Replay-convention costs

| id | claim | status | witness |
|---|---|---|---|
| PR-C1 | Guarding on the actual prefix and on the replayed prefix give different fire sets and different regret for one rule. | EXECUTABLE FINITE WITNESS | `E11`: 3 firings and 6, against 2 and 4 |
| PR-C2 | Freezing contingent filings undercounts a comparator's advantage, by the whole consequent stream. | EXECUTABLE FINITE WITNESS | `E12`: 2 frozen against 8 endogenous, on an unchanged actual charge of 8 |

## 4. Counterfactual influence

| id | claim | status | evidence |
|---|---|---|---|
| PR-L1 | **Fenced accounting lemma.** If `φ` fires only in accounts `S`, then `\|L_T(H^φ) − L_T(H)\| ≤ Σ_{s∈S} Λ_s`, where `Λ_s` is the account's admitted lifetime liability. | PROVED (single derivation) | Two-line argument in `COUNTERFACTUAL_CHARGE_INFLUENCE.md` §A. It is an accounting lemma and is labelled one |
| PR-L2 | PR-L1 is tight. | EXECUTABLE FINITE WITNESS | `E10b`: divergence 24 against bound 24, 48 against 48 |
| PR-L3 | **Fencing alone does not give a horizon-free bound.** A single fence containing the run admits divergence `Θ(T)` from one local edit. | EXECUTABLE FINITE WITNESS | `E10b` |
| PR-L4 | **Pooled solvency destroys locality.** One local lawful edit moves a shared suspension date and diverges by `2T`. | EXECUTABLE FINITE WITNESS | `E10`: 24 at `T = 12`, 48 at `T = 24` |
| PR-L5 | **Without the solvency coupling, influence is horizon-free:** `\|ΔL_T\| ≤ \|fire set\| · ℓ_max`. | CONDITIONAL | Immediate from the per-occasion decomposition once no response depends on another occasion's charge; attained by `E10c` at 2 for a one-firing comparator at every horizon. Conditional on `suspends=False`, which `CS-N1` shows is a real hypothesis elsewhere in the line |

## 5. What is architected, not proved

| id | claim | status |
|---|---|---|
| PR-A1 | Φ_law as a set of guarded local edits with per-firing membership is the right comparator primitive for this line. | ARCHITECTED |
| PR-A2 | The obligation adapter in `src/model.py` is faithful to the answerability algebra it adapts. | ARCHITECTED — no cross-check against `projects/leverage/forward/src/answerability.py` was run, and that tree is declared disposable |
| PR-A3 | The five reason kinds — interval, impediment, ripeness, authority, ratification — suffice for the comparator class. | ARCHITECTED, and the same shape as the consolidation's open registry-completeness problem |

## 6. Conjectured

| id | claim | status |
|---|---|---|
| PR-X1 | The Blum–Mansour Φ-regret reduction instantiates against this substrate, giving `sup_φ R_T(φ) = O(ℓ_max √(T log \|Φ_law\|))`. | CONJECTURED — the fixed-point step has not been checked against a per-occasion action set that varies with the bound schedule |
| PR-X2 | **The self-correction consequence.** A pattern recognised on `Ω(T)` occasions with a fixed admitted repair saving `δ > 0`, under bounded distortion, cannot persist at positive rate against a learner with `o(T)` regret. | CONJECTURED — the argument is one line; three of its four hypotheses are supplied and the fourth (`o(T)`) is not established anywhere |
| PR-X3 | **Self-hosting.** A `LawfulEditCertificate` with a recurrence count and a positive charge differential is representable as grounds for a remediable-pattern objection under the existing grammar, with no new primitive. | CONJECTURED — the footprints coincide, which is suggestive and is not an ontology audit |

## 7. Open

| id | question |
|---|---|
| PR-O1 | Does a φ-regret statement survive reinstating the solvency coupling? |
| PR-O2 | Is there a substantively adequate `BearsOn`, or is the coordinate-declaration form of it already the wrong shape? |
| PR-O3 | Is `unresolved` the right verdict for an unbacked magnitude endpoint, or only the honest one? |
| PR-O4 | Coverage: what would make an important remediable pattern enter Φ_law, and at what rate does enlarging Φ_law cost? |

## 8. Refuted

Nothing. One expectation of the dispatch was corrected rather than refuted: it
treated fencing as the dividing line for bounded counterfactual influence, and
`E10b` shows the line is the solvency coupling together with fence granularity.
`COUNTERFACTUAL_CHARGE_INFLUENCE.md` §E records it.
