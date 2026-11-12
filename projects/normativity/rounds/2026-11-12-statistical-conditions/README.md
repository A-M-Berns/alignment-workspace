# Statistical conditions on a floor market — losses, stakes and slack floors

Verdict: STATISTICAL-FLOORS — for one floor per day at strength c on a fresh sentence settled the next day: with at most R false instances the account of a dual-certified market is at least −U((1 − c)^-(R+1) − 1), and on sequences a compounding staker attains the bound; unit-stake and market-stake accounts are each bounded without the other, and agree in boundedness for stakes of bounded variation; with outcomes favourable at c given the past and predictable stakes, the settled account reaches −K with probability at most U/(U + K); the multipliers are slack where the price clears the floor, so a floor cleared by a margin from some day on costs a bounded account; under realized frequency at least c + γ along the one weighting that reads whether the price is within δ < γ of the floor, either the account is bounded below or the buyer near the floor exploits; the conditional bridge's frequency hypothesis is the summability of the normalized stakes; on sequences a geometric mixture of finitely supported stakers has an unbounded account exactly when its weight ratio is at least 1 − c. Open: which disjunct holds in the floor market on a sequence with infinitely many false instances, efficiency of the buyer, the generable-weighting form for one trader, and an assessment driven by random observations.

Read `REPORT.md` first. `THEOREM.md` carries the statements of record with their assumption
ledgers. Lean: `lean/Workspace/Normativity/Contrib/StatisticalConditions.lean` (losses, stakes,
slack floors, the table mixture, the buyer near the floor) and
`StatisticalConditionsVille.lean` (the capital bound with a probability). `toy/floor_toy.py` is
exploration in exact rationals; no theorem depends on it.

Dispatch: `prompts/2026-11-12-statistical-conditions/PROMPT.md`. Second opinion: `prompts/2026-11-12-statistical-conditions/REVIEW-astra.md`.
