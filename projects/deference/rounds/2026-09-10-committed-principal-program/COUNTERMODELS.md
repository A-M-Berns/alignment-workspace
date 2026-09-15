# Countermodels

**Status:** `ci-only`.  The two distinguishing pairs of clause 2, every break of the
pressure pass, and every fixture of the push.  The 2026-09-09 countermodels remain in
that round's `COUNTERMODELS.md`; the ones re-run here are in `tests/test_clauses.py`
(48, two adapted and marked).

## The two pairs (C3)

| pair | logs | what separates them | where |
|---|---|---|---|
| **one** — reading versus susceptible principal | identical receipts, traces, vectors on the realized log (the 2026-09-09 residual) | the mandate's program type: `ℛ → 𝒱` versus `ℛ × Register → 𝒱`, read at issuance; the susceptible one fails clause 6 with no counterfactual | `test_pair_one_the_2026_09_09_pair_is_distinguished_at_issuance`; `Programs.susceptible_not_trace` (LEAN) |
| **two** — honest executor versus a coincident computation of the same program | identical logs (`Instance.logs_equal`, LEAN) | nothing on the log, by proof; and nothing needs to: the payload is the program's output either way (`Instance.payload_regardless`); on the frame the coincidence fails elsewhere and voids | `test_pair_two_the_residual_pair`; `Instance.execs_differ` |

## Pressure-pass breaks and repairs (§1)

| # | fixture | break | repair | where |
|---|---|---|---|---|
| B1 | key theft — advisor commit under `kP` | an authenticated receipt with `author = A` | registry binds `(party, key)` | `test_key_theft_break_and_repair`; `Instance.stolen_key_void` |
| B2 | pinned jam branch, fragile registrar | openness reported where re-simulation says closed | branches as log transforms in Lean; `semPinned` kept as the attack | `test_jam_branch_pinning_hides_a_failure`; `Instance.openAll_pinned_fragile` / `not_openAll_fragile` |
| B3 | advisor-written `ROUTE` | the barrier cleared by forgery | representation is the registrar's move | `test_route_forgery_break_and_repair`; `forged_route_not_represented` |
| B4 | position-embedding reason content; prefix-hash settlement | `Blind R P` fails | none local — the pair-class declaration must exclude position-dependent content (P3) | `test_position_embedding_content_breaks_blindness`, `test_prefix_hash_settlement_breaks_blindness` |
| B5 | `typed` rule: own-move deliberation without representation; engine settlement at request; own earlier commit as ground | laundering admitted | `typed+`: representation before own-move grounds, request-free engine settlements, activated-chain commits; the last still admits the chain | `TestP6_TypedRuleAttacks` |
| F1 | `J = {silent, honest}` | the counterfactual half of clause 5 is empty | `jam` declared; registrar robustness a configuration | `test_advisor_only_interventions_cannot_be_hidden_by_pinning` |

## Fixtures of the push (§2)

| # | fixture | what it shows | where |
|---|---|---|---|
| M1 | miscomputation | a commit whose vector is not the program's output is void, not a foreign receipt | `test_miscomputation_voids`; `Instance.miscomputation_void` |
| M2 | wrong prefix citation | a receipt naming an earlier prefix is void | `test_wrong_prefix_citation_voids` |
| M3 | delegate binds only the program's output | `test_delegate_binds_only_the_program_output`; `Instance.delegated_binds_program_output` |
| M4 | forgery cannot choose the vector | authenticity protects who, the program pins what | adapted `test_countermodel_forged_author` |
| M5 | two valid commits | the first binds; the second, valid, never enters | `test_two_valid_commits_first_binds` |
| M6 | opaque protocol | no program in the mandate: the 2026-09-09 residual reappears exactly | `test_opaque_protocol_cannot_certify_clause_two` |
| N1 | constant program | the constant end | `test_constant_end` |
| N2 | `proofcheck` | in the band: rejects a bad certificate the reading program accepts; equal on `honest` and `dup` | `test_proofcheck_is_in_the_band`; `Programs.proofcheck_*` |
| A1 | sealed advisor program | selection-blind by typing in the finite model | `test_sealed_program_is_selection_blind_by_typing` |
| A2 | view leak | the market publishes `σ`; the program echoes it; no selection input anywhere | `test_view_leak` |
| S1 | strict/tolerant table | the eight continuations that differ; payload unchanged under tolerant | `TestP5.test_table` |
| S2 | simulated availability | `η_20 = 7/22` strict, `1/22` tolerant | `TestP5.test_eta_on_simulated_sequences` |
