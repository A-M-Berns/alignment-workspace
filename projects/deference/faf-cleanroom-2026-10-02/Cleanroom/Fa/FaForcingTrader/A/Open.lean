import Cleanroom.Fa.FaForcingTrader.A.TheoremSS

/-!
# `fa-forcing-trader` · angle A · Open: the two-market non-vacuity of the (L) package (T11)

The one statement this angle leaves open, with `sorry`, listed in
`run/wp/fa-forcing-trader/fa-forcing-trader-A-open.txt`. Everything T6/T7 prove is over the
hypothesis `hL : LegibleOn H (quoteSeq Y A)` — the corpus's (L). Its same-market instance is a
theorem (`legibleOn_quote_self`); a **two-market** instance with `A ≠ H` and a non-constant quote
is what would make Theorem SS bite on a real pair, and none is known: an LIA's prices are not
known to be polynomial-time computable, so the quote stream of an LIA `A` has no known
`PGenerableWeighting` certificate on another market (li-quote-lane F2,
`readability_fails_without_generability`). The negation is **not** claimed either: nothing here
rules out a pair with a cheap `A` (angle B's certificate route, or a non-LIA inductor). Credence
and what resisted: report §T11.
-/

namespace Cleanroom.Fa.FaForcingTrader.A

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Cleanroom.Fa.FaForcingTrader
  Filter Topology

/-- **T11 (OPEN). A two-market inhabitant of the (L) package**: two inductors `A ≠ H` over their
processes, a lookahead `f`, an e.c. `[0,1]`-LUV family `X` of `H`'s language and a quote family
`Y` with a `CrossQuotePackage`, both worlds satisfiable, such that `A`'s quote
`a_n = 𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝)` is a legal feature progression of `H`'s market
(`LegibleOn H (quoteSeq Y A)`) and the quote is not eventually constant (so that the gate of
Theorem SS can have content). Not proved: no inhabitant is known (an LIA's price stream has no
known polynomial-time certificate on another market), and no refutation is claimed.
Scope: two-way in the sense that `H`'s market sees `A`'s numbers; the statement is existential.
Source: lean-deference-2-011 (a); vq-wiki-048 (c); root-fa-017; li-quote-lane F2
Kind: OPEN
Fidelity: exact (the existence the package's (c) needs)
Hyps: n/a -/
theorem exists_twoMarket_legible_pair :
    ∃ (A H : History) (DPA DPH : DeductiveProcess) (f : DeferralFunction) (X Y : ℕ → LUV),
      IsLogicalInductor A DPA ∧ IsLogicalInductor H DPH ∧
      CrossQuotePackage H DPA f X Y ∧ LUV.MachineThresholdCodeSeq X ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) ∧
      LegibleOn H (quoteSeq Y A) ∧ A ≠ H ∧
      ¬ (∃ c : ℝ, ∀ᶠ n in atTop, quoteSeq Y A n = c) := by
  sorry

end Cleanroom.Fa.FaForcingTrader.A
