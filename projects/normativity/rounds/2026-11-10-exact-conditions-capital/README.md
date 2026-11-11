# Exact conditions on a price history — the account that pays for them

Verdict: EXACT-CONDITIONS — a condition the prices satisfy exactly (finitely many demanded bets per day) is carried by a dual-certified market, whose cost is one scalar account; the account is at most 2 + ε at live worlds, and if it is bounded below no efficiently computable trader exploits; conditions every live world satisfies cost nothing; a prefix reserve bounds the account below by −U(1 − r)/r at a profile retaining mass r; against any history satisfying a condition, a staking whose account is bounded above and unbounded below makes the seller of the demanded bets exploit, and two floor conditions have one; under a frequency hypothesis on the realized normalized stakes the account of one fresh floor per day is bounded; every schedule of one floor per day has a dual-certified market, built from the pinned market maker by reparametrizing the day's prices. Open: the general polytope, computability of the market, efficiency of the sellers, the frequency hypothesis, and the converse of preservation.

Read `REPORT.md` first. `THEOREM.md` carries the statements of record with their assumption
ledgers. Lean: `lean/Workspace/Normativity/Contrib/ExactConditions.lean` (interface, ceiling,
preservation, entailment, obstruction, counterexamples), `ExactConditionsReserve.lean`
(reserve bound, conditional bridge), `ExactConditionsFloor.lean` (the floor market and the
inhabitants). No Python is theorem-bearing in this round.

Dispatch: `prompts/2026-11-10-exact-conditions-capital/PROMPT.md`.
