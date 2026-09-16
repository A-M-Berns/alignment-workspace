# The fused criterion: statement and obstruction

No Lean.  Everything here is a statement on file and one obstruction.

## 1. The three criteria as they stand

- **Assessment-relative Logical Induction** (`li.assessment.criterion`): no efficiently
  computable trader exploits the market relative to the assessment process.  The
  enforcer is one more trader in the aggregate the market maker prices against; it is not
  required to be efficiently computable and the criterion does not quantify over it
  (`wiki/Progress.md`, the withdrawn uptake claim; `wiki/Normative-Inductor.md`).
- **Legitimacy** on record evolutions: Integrity (no occurrence disappears, receipts
  persist, content transported faithfully) and Robust Openness at every state
  (`wiki/Legitimacy.md`).  A predicate on the docket's history; it mentions no price.
- **Continuation BRIA** on the decision layer: the learner's weighted realized score is
  asymptotically at least its covered hypotheses' claims (`wiki/Glossary.md`,
  *continuation BRIA*).  A statement about the adapter's realized losses, not about
  prices.

## 2. The fused candidate, stated

Fix a reasoner `N = MarketMaker(TradingFirm + Enforcer[K_t]) + Adapter` over an
assessment process, a docket `𝒪` of objections, and a settled chain `F_t`.

1. **Objection securities.**  For each objection occurrence `o` filed at date `s`, and
   each `n ≥ s`, a security `χ_{o,n}` paying `1` if `o` is unanswered at `n` and `0`
   otherwise, where "answered at `n`" is decided by the answer receipt or closure in the
   log prefix of length `n` — a finitely adjudicated event.  The per-period charge is
   `Σ_{o} χ_{o,n}`.
2. **The docket is in the assessment.**  The assessment process settles `χ_{o,n}` by
   receipts, so the market prices `χ_{o,n}` and a challenger who trades it is an
   ordinary trader.  `li.assessment.criterion` then applies to those prices.
3. **The adapter under BRIA with charges as loss.**  The adapter's realized score at
   block `k` is minus its charges over the block; continuation BRIA holds against the
   class of continuation hypotheses whose claims are statements about charges.  A
   reasoner whose market prices `χ_{o,n}` near `0` ("will be answered") while the
   adapter leaves `o` unanswered is overestimating in BRIA's sense once "I answer `o`" is
   a covered hypothesis.

**Fused criterion:** `N` satisfies (LI over the augmented assessment) ∧ (Legitimacy on
the log) ∧ (BRIA on the adapter with charges as loss).

**Candidate consequence (a):** every reasoner satisfying it has displayed prices on the
unsettled normative fragment in `K(S ∪ W_t, F_t)` from `STATICS.md`, in the limit.

## 3. The obstruction — (b), decisive

The fused criterion constrains three things: prices of objection securities, the
docket's evolution, and whether objections get answered.  It does not constrain the
price of an unsettled normative sentence `φ` relative to `K`, and the place where it
fails to is exact:

**The adapter has no write access to prices.**  `wiki/Normative-Inductor.md`: the
decision adapter *consumes* the market state, "is not another trader and does not feed
back into prices".  BRIA on the adapter therefore forces the adapter to *answer* — to
produce answer receipts, or to stop incurring charges — and an answer is whatever the
protocol's adequacy predicate accepts.  Whether an adequate answer to "your price on `φ`
violates row `r`" *is* a price movement is the adequacy predicate's semantic content,
which is the protocol's typed input, not the criterion's.

**The only price-writer that is not the ordinary firm is the enforcer**, and the enforcer
is exactly the position the LI criterion does not quantify over.  Folding the docket
into the assessment makes the *objection securities* priced — it does nothing to `φ`.
A reasoner with enforcement intensity zero satisfies all three clauses: its market is
an ordinary logical inductor over the augmented assessment (the enforcer is a trader with
zero position and zero liability), its docket is answerable, its adapter answers on time
— and its prices on `φ` are whatever the trading firm makes them, anywhere in the cube.

So the withdrawn uptake argument recurs at the same joint: pressure enters through the
enforcer's position, which no criterion sees, and the fused criterion moves the pressure
from "answer the objection" onto the adapter, which cannot move a price.

**Two ways the obstruction could be evaded, and why each is construction, not
criterion.**

1. *Define adequacy as membership.*  Let the adequate answer to a price objection be
   `checkCompiled (forcedBundle …) (P_n) = true` at the next date — computable, so the
   receipt is a finite event.  Then the adapter can only discharge the charge by the
   enforcer trading, and the criterion now quantifies over prices *because the protocol
   was written to*.  The limit behaviour is then the affordability theory's: the region
   is reached to tolerance at the rate the enforcer's liability allows, and not at all
   when it is unaffordable (`wiki/Liability-and-Affordability.md`).  That is the
   enforcer's guarantee, relabelled as a receipt.
2. *Link the objection security's payoff to the price of `φ`.*  Then challengers bet on
   the reasoner's own future price; by LI's reflection results the market predicts its
   own violation accurately, and "I will violate `r`" priced at `1` exploits nobody.
   Charges accrue to an account outside the LI criterion.

## 4. Consequence for the seed program

Limit behaviour is **construction-relative**.  A statement "a reasoner starting from seed
`S` ends up with prices in `K(S ∪ W_∞, F_∞)`" is a statement about a named enforcer with
a named liability schedule, a named discovery class `𝒟` and a named settlement chain —
never about a criterion the reasoner satisfies.  What the seed theory can say is what is
*forced* (`STATICS.md`), for whom it is forced (`CONFINEMENT.md`), and whether the forced
region settles down as the docket and the world move (`STABILIZATION.md`).  Which
constructions bring prices to it is the force layer's question, already answered there
in the conditional form, and this round adds nothing to it.
