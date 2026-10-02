# Fixture notes (written by tests/test_graph.py on 2026-10-02; the ranking as derived, for the record)

- research first: begin with vet tt-mart-repair-via-bounds-transfer
- the decision term would reorder 4 units; shown, not applied
- world model: [corrigibility-anti-natural, instrumental-convergence: 8 variables, 256 worlds]; [deference-toward-bounded-agents, tt-mart-repair-via-bounds-transfer: 1 variables, 2 worlds]; [li-deference-collapse: 10 variables, 1024 worlds]; [policy-level-total-trust: 1 variables, 2 worlds]; [step-asymptotic-to-finite-time: 1 variables, 2 worlds]; [step-legitimacy-conditioned-trust: 1 variables, 2 worlds] (cap 32768 per component)

1. vet tt-mart-repair-via-bounds-transfer (S, ~33/1 min; bits 0.722; D 7/100)
2. map-read tt-mart-repair-via-bounds-transfer (S, ~8/1 min; bits 0.077; D 0/1)
3. vet step-legitimacy-conditioned-trust (L, ~240/1 min; bits 0.934; D 7/100)
4. vet corrigibility-anti-natural.complete (S, ~33/1 min; bits 0.114; D 0/1)
5. vet step-asymptotic-to-finite-time (L, ~240/1 min; bits 0.769; D 9/200)
6. vet correction-changes-objective (S, ~33/1 min; bits 0.099; D 0/1)
7. vet ic-informal.complete (S, ~33/1 min; bits 0.075; D 0/1)
8. map-read step-legitimacy-conditioned-trust (L, ~60/1 min; bits 0.108; D 0/1)
9. vet a1-fixed-objective-maximizer (M, ~85/1 min; bits 0.145; D 0/1)
10. map-read corrigibility-anti-natural.complete (S, ~8/1 min; bits 0.015; D 0/1)
11. map-read step-asymptotic-to-finite-time (L, ~60/1 min; bits 0.084; D 0/1)
12. map-read correction-changes-objective (S, ~8/1 min; bits 0.013; D 0/1)
13. vet a2-monotone-in-resources (S, ~33/1 min; bits 0.038; D 0/1)
14. vet a4-no-binding-counter-drive (M, ~85/1 min; bits 0.081; D 0/1)
15. map-read ic-informal.complete (S, ~8/1 min; bits 0.009; D 0/1)
16. map-read a1-fixed-objective-maximizer (M, ~25/1 min; bits 0.018; D 0/1)
17. vet a3-self-and-operators-modelled (S, ~33/1 min; bits 0.017; D 0/1)
18. map-read a4-no-binding-counter-drive (M, ~25/1 min; bits 0.01; D 0/1)
19. map-read a2-monotone-in-resources (S, ~8/1 min; bits 0.003; D 0/1)
20. map-read a3-self-and-operators-modelled (S, ~8/1 min; bits 0.001; D 0/1)
21. vet expert-knows-own-estimates (S, ~33/1 min; bits 0.001; D 0/1)
22. vet mart-implies-value-kernel.complete (S, ~33/1 min; bits 0.001; D 0/1)
23. vet li-deference-collapse.complete (S, ~33/1 min; bits 0.001; D 0/1)
24. map-read expert-knows-own-estimates (S, ~8/1 min; bits 0.0; D 0/1)
25. map-read mart-implies-value-kernel.complete (S, ~8/1 min; bits 0.0; D 0/1)
26. map-read li-deference-collapse.complete (S, ~8/1 min; bits 0.0; D 0/1)
27. vet tt-implies-mart-gap-bets (M, ~85/1 min; bits 0.0; D 0/1)
28. vet bet-class-gap-closed (S, ~33/1 min; bits 0.0; D 0/1)
29. map-read tt-implies-mart-gap-bets (M, ~25/1 min; bits 0.0; D 0/1)
30. vet mart-implies-value-kernel.bridge (S, ~33/1 min; bits 0.0; D 0/1)
31. vet tie-break-ledger-decided (S, ~33/1 min; bits 0.0; D 0/1)
32. map-read bet-class-gap-closed (S, ~8/1 min; bits 0.0; D 0/1)
33. vet mart-implies-value-kernel.record (S, ~33/1 min; bits 0.0; D 0/1)
34. vet novice-expprovind (S, ~33/1 min; bits 0.0; D 0/1)
35. map-read mart-implies-value-kernel.bridge (S, ~8/1 min; bits 0.0; D 0/1)
36. map-read tie-break-ledger-decided (S, ~8/1 min; bits 0.0; D 0/1)
37. map-read mart-implies-value-kernel.record (S, ~8/1 min; bits 0.0; D 0/1)
38. map-read novice-expprovind (S, ~8/1 min; bits 0.0; D 0/1)
39. map-read a1-fixed-objective-maximizer.partition (S, ~8/1 min; bits 0.0; D 0/1)
40. map-read tt-implies-mart-gap-bets.partition (S, ~8/1 min; bits 0.0; D 0/1)
41. vet a1-fixed-objective-maximizer.partition (S, ~33/1 min; bits 0.0; D 0/1)
42. vet tt-implies-mart-gap-bets.partition (S, ~33/1 min; bits 0.0; D 0/1)

- unranked: admit a1-fixed-objective-maximizer/pic-N-a1-residual (load 1)
- unranked: admit a1-fixed-objective-maximizer/pic-T-kk-training-compatible-goal (load 1)
- unranked: admit a1-fixed-objective-maximizer/pic-T-rest-no-single-objective (load 1)
- unranked: admit tt-implies-mart-gap-bets/pic-A-parallel-cuts-amplifier (load 1)
- unranked: admit tt-implies-mart-gap-bets/pic-D-asymptotic-introspection (load 1)
- unranked: admit tt-implies-mart-gap-bets/pic-N-tt-mart-residual (load 1)
- unranked: admit tt-implies-mart-gap-bets/pic-U-exact-introspection (load 1)

- corrigibility-anti-natural: open; Pr no belief; value no belief; gestalt 9/20; cost 184/1
- deference-toward-bounded-agents: open; Pr 4/5; value 4/5; gestalt None; cost 33/1; programme over tt-mart-repair-via-bounds-transfer, step-asymptotic-to-finite-time, policy-level-total-trust, step-legitimacy-conditioned-trust
- instrumental-convergence: open; Pr no belief; value no belief; gestalt 29/40; cost 302/1
- li-deference-collapse: open; Pr no belief; value no belief; gestalt 1/8; cost 382/1
- policy-level-total-trust (in deference-toward-bounded-agents): open; Pr 17/40; value no belief; gestalt 17/40; cost inf
- step-asymptotic-to-finite-time (in deference-toward-bounded-agents): open; Pr 9/40; value 9/40; gestalt 9/40; cost 240/1
- step-legitimacy-conditioned-trust (in deference-toward-bounded-agents): open; Pr 7/20; value 7/20; gestalt 7/20; cost 240/1
- tt-mart-repair-via-bounds-transfer (in deference-toward-bounded-agents): open; Pr 4/5; value 4/5; gestalt 4/5; cost 33/1

- valuation default-trajectory (outside option): 0/1 (provisional)
- valuation undescribed-failure (undescribed failure): -1/4 (provisional)

## The table case (a two-row table on a2, filed by a new contributor on a scratch copy)
- passes in 0.25 s; components: [corrigibility-anti-natural, instrumental-convergence: 9 variables, 512 worlds]; [deference-toward-bounded-agents, tt-mart-repair-via-bounds-transfer: 1 variables, 2 worlds]; [li-deference-collapse: 10 variables, 1024 worlds]; [policy-level-total-trust: 1 variables, 2 worlds]; [step-asymptotic-to-finite-time: 1 variables, 2 worlds]; [step-legitimacy-conditioned-trust: 1 variables, 2 worlds]
- a2: conceded by pic-B-bounded-objective; ic-informal: conceded; instrumental-convergence: open (None)
- stale leaf range(s) kept as suggestions: smithy-verity-027, tester-000
