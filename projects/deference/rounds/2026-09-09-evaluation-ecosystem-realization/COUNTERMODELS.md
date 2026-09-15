# Countermodels

**Status:** `ci-only`.  Exact fixtures in `tests/test_clauses.py`, `tests/test_settlement.py`,
`tests/test_builder.py`; Lean twins named.  Letters refer to the consolidation round's
`COUNTERMODELS.md` where a fixture mirrors one of its.

| # | fixture | what fails | where |
|---|---|---|---|
| C1a | **delegated key** — `DELEGATE` extends the binding warrant to the advisor's key at `t = 1`; the advisor's commit at the slot is an authenticated answer receipt | activation holds, exclusivity fails, `C = 0`, `ExclusiveBind` fails on the frame | `test_countermodel_second_key_binds` |
| C1b | **forged author** — the advisor's commit rewritten with the principal's key and author | every clause passes with the advisor's vector: the discharge of clause 1 is the authentication assumption and nothing else | `test_countermodel_forged_author` |
| C1c | **closure** — the engine settles `("void", s)` and closes the occurrence at `t = 3`; the principal still commits at the slot | fates `{closed}`, not activated; the later commit does not enter the terminal account | `test_activation_reads_the_fates` |
| C2a | **susceptible principal** (B, F) — `silent` and `covert` leave the same trace, different payloads | `ReasonMediated` fails; the log tells the frames apart on the pair | `test_susceptible_principal_does_not_factor` |
| C2b | **identical receipts** — reading and susceptible principals commit with the same `proc`, trace and vector on the realized log | the receipt cannot certify the frame: the residual of clause 2 | `test_residual_receipts_do_not_certify_the_frame` |
| C2c | **early write** (D) — `early_write` versus `honest5`: equal session traces, equal issuance-rooted traces | session-local mediation holds within each pre-session class; issuance-rooted mediation fails | `test_issuance_rooted_versus_session_local` |
| C2d | **transient** (E) — argue then withdraw | final-state mediation fails, trace mediation holds | `test_transient_reason` |
| C3a | **injective end** — `R` = the whole log | mediation vacuous for the susceptible principal; blindness to `P` fails | `test_countermodel_injective_end` |
| C3b | **constant end** — `R` constant | the reading principal's legitimate movement by a proof reads as a bypass | `test_countermodel_constant_end` |
| C3c | **positional grounds** — the trace references a disposal's grounds by log index | blindness to `P` fails: inserting a prohibited event shifts the index (found during the round; the encoding now references by content) | `ECOSYSTEM.md` §3 |
| C4 | **advisor-only trace** (I) — the encoding keeps `REASON`/`WITHDRAW` only | represented, not in trace; `RepFaithful` fails | `advisorTrace_unfaithful` (LEAN), `test_countermodel_advisor_only_encoding` |
| C5a | **flooded docket** (G's shape) — three unprotected concerns ahead, capacity `1` | openness holds at every snapshot; the concern is live at the slot; the reading principal waits; no receipt | `test_flooded_docket_defeats_the_bound_and_voids` |
| C5b | **eager principal** (F, G) — the same docket, commits anyway | activated in the account, voided by the barrier | `test_eager_principal_commits_into_the_barrier` |
| C5c | **destroyed route** (H) — route destroyed while the concern is live | openness fails; never represented | `test_destroyed_route_fails_openness` |
| C5d | **capacity** — capacity `2` serves three; six defeat it | the certificate is about the instance and horizon | `test_capacity_certifies_the_instance_only` |
| C6 | **leak** (K) — reason content `recommend:σ` | not selection-blind; the principal never reads a selection coordinate; both continuations certify | `test_leak`, `test_sealing_is_outside_C` |
| C7 | **prohibited event, ineffective** — `honest_covert` commits the same vector as `honest` under the reading principal | `C = 0` by the per-log clause; yardstick invariance realized | `test_prohibited_event_voids_and_does_not_move_the_reading_principal` |
| S1 | **laundering** — the principal settles the external fact and disposes on it, rule `none` | `C = 1` with the protected concern suppressed | `test_untyped_independence_launders` |
| S2 | **typed / strict** — the same trace | refused; `C = 0` | `test_typed_independence_refuses`, `test_strict_independence_refuses` |
| S3 | **engine-settled** (3′ proper) | accepted under every rule | `test_engine_settlement_is_accepted_under_every_rule` |
| S4 | **own deliberation as ground** | accepted under `typed` and `none`, refused under `strict` | `test_own_deliberation_is_a_valid_ground_only_under_typed` |
| M1 | **susceptible principal on the market** | no certified world, `η = 1`, `R_auth` undefined: a certified-deference claim with no availability is empty | `test_susceptible_principal_has_no_certified_world` |
| M2 | **alternating voids** | `η_n → ½`; the mostly-certified regime with a non-vanishing frequency | `test_adversarial_docket_does_not_vanish` |
