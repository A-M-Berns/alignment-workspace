import Cleanroom.Fa.FaForcingTrader.B.Certificate

/-!
# `fa-forcing-trader` · angle B · Open: the two statements left with `sorry`

Both are listed in `run/wp/fa-forcing-trader/fa-forcing-trader-B-open.txt` with their reasons;
the report (`fa-forcing-trader-report-B.md`) records what was tried.

* `exists_gridCertificate_of_marketComputation` — angle B's certificate on the controllable
  instance: a market with a `MarketComputation` admits an evaluation-sparse `DeferralFunction`
  along which the grid truth of its deferred expectations is machine-certified
  ([[route-sparse-schedule]] §3 Lemma 1 (b)–(d), in FAF's machine model).
* `exists_twoMarket_legible_pair` — the mandate's T11: two-market non-vacuity of (L).
-/

namespace Cleanroom.Fa.FaForcingTrader.B

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- **OPEN. The evaluation-sparse schedule and its certificate, for a computable market**
([[route-sparse-schedule]] §3 Lemma 1 (b)–(d)). For `H` with a `MarketComputation` (every
`IsLogicalInductor` has one — `IsLogicalInductor.marketComputable`), an e.c. source family `X`
and a lookahead `f`, there is a strictly increasing `DeferralFunction d`, window-disjoint for
`f`, along which the grid truth `gridTruth (realized H f X)` — `(1/2)·(1/(d k+1))·#{i ≤ d k :
i/(d k+1) < 𝔼^H_{f (d k)}(X_{d k})}`, a rational of `H`'s day-`f (d k)` quotes — is written as a
`MachineDigits`-metered code stream at the paired index `⟨k, d (k+1)⟩`
(`FeedbackTruthComputation`). The real sequence is immediate (`d (k+1) := max (f (d k) + 1,
the halting fuel of `H`'s program on day `f (d k)`)`); what is open is `d.graph_fp` and the
`MachineDigits` field: Lemma 1(c)/(d)'s truncation argument ("iterate the step while the value
stays `≤ m`") needs a capped-iteration ruler for a *clocked* `evaln` step, and FAF's fuel calculus
has no universal simulator with polynomial `evaln` overhead (li-coupled-pair B's finding), while
its one timeout-tolerant FP run (`TraderMachine.traderOutput_mem_FP`) does not keep the output
block-complete on timeouts. Credence that the statement is provable in FAF with a dedicated
machine construction: ~0.8 (it is the corpus's Lemma 1, whose mathematics is routine; the cost is
FAF plumbing, not an obstruction). Its consequence, once closed: `quoteSide_fullLimit_grid` at
`A` with (b) `C` discharged to (a) on the controllable pair.
Source: [[route-sparse-schedule]] §3 Lemma 1 (vq-wiki-046), §9 trap 3; mandate § Attempt angles (B); lean-deference-2-010
Kind: OPEN
Fidelity: exact (Lemma 1 on the grid truth; the paper's `O(g(k+1))` relaxed to FAF's poly-in-the-pair, as FAF's `FeedbackTruthComputation` docstring records)
Hyps: (a) `M`, `hX` -/
theorem exists_gridCertificate_of_marketComputation {H : History} (M : MarketComputation H)
    (f : DeferralFunction) (X : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X) :
    ∃ d : DeferralFunction, WindowDisjoint f d ∧
      Nonempty (FeedbackTruth.FeedbackTruthComputation (gridTruth (realized H f X)) d) := by
  sorry

/-- **OPEN (T11). Two-market non-vacuity of the (L) package.** Two *distinct* logical inductors
`A ≠ H`, a quote package tying `A`'s family `Y` to `H`'s realized expectations, `A`'s process
satisfiable, the quote legible on `H` (`LegibleOn H (quoteSeq Y A)`), and the quote not eventually
constant. No inhabitant is known: an LIA's prices are not poly-time computable, so (L) with `A` a
LIA has no known `PGenerableWeighting` of `H`'s market denoting them (`li-quote-lane` F2,
`readability_fails_without_generability`); the same-market instance (`legibleOn_schedGate_self`)
violates `A ≠ H`. Credence that it holds: ~0.5 — a *clocked* ledger (li-coupled-pair B's
`clockedSeq`) publishes the quote as decided atoms of `H`'s process, but a decided atom's price is
`≈ₙ` the value, not equal to it, and `LegibleOn` asks for equality on every day.
Source: mandate T11; lean-deference-2-011 (a); vq-wiki-048 (c); root-fa-017
Kind: OPEN
Fidelity: exact
Hyps: n/a -/
theorem exists_twoMarket_legible_pair :
    ∃ (A H : History) (DPA DPH : DeductiveProcess) (f : DeferralFunction) (X Y : ℕ → LUV),
      IsLogicalInductor A DPA ∧ IsLogicalInductor H DPH ∧ CrossQuotePackage H DPA f X Y ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) ∧
      LegibleOn H (quoteSeq Y A) ∧ A ≠ H ∧
      ¬ ∃ c : ℝ, ∀ᶠ n in atTop, quoteSeq Y A n = c := by
  sorry

end Cleanroom.Fa.FaForcingTrader.B
