import Cleanroom.Fa.FaForcingTrader.A.Open
import Cleanroom.Fa.FaForcingTrader.B.Open

/-!
# `fa-forcing-trader` · Open: the package's open statements of record (T11, the certificate)

Both `sorry`s live in the attempts (`A/Open.lean`, `B/Open.lean`); the package-namespace names
below are proved `:= A.…` / `:= B.…` and therefore rest on the same `sorry`, so both names are
listed in `run/wp/fa-forcing-trader/fa-forcing-trader-open.txt` (the precedent of
`li-coupled-pair`). The two angles stated T11 independently; angle A's shape is the one of record
because it pins the **full** hypothesis package of T6 (the e.c. certificate of `X` and `H`'s
world), and B's statement follows from it by dropping two conjuncts. Credences (reports): A ~0.25
for an inhabitant with `A` an LIA, ~0.6 for some inductor `A`; B ~0.5; neither angle states the
negation.
-/

namespace Cleanroom.Fa.FaForcingTrader

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Filter Topology

/-- **T11 (OPEN, of record). A two-market inhabitant of the (L) package**: two inductors `A ≠ H`
over their processes, a lookahead `f`, an e.c. LUV family `X` of `H`'s language and a quote family
`Y` with a `CrossQuotePackage`, both worlds satisfiable, such that `A`'s quote
`a_n = 𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝)` is a legal feature progression of `H`'s market
(`LegibleOn H (quoteSeq Y A)`) and the quote is not eventually constant. Angle A's statement,
restated (`:= A.exists_twoMarket_legible_pair`, where the `sorry` is). Not proved: an LIA's price
stream has no known polynomial-time certificate on another market (li-quote-lane F2,
`readability_fails_without_generability`); no refutation is claimed either (a pair with a cheap
`A`, or angle B's certificate route, is not ruled out). Findings F-B4: a decided-atom ledger gives
`≈ₙ`, not the equality `LegibleOn` asks, and T9 (ii) shows `≈ₙ` does not suffice on a sparse
schedule.
Scope: existential; `H`'s market sees `A`'s numbers.
Source: lean-deference-2-011 (a); vq-wiki-048 (c); root-fa-017; li-quote-lane F2; mandate T11
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
      ¬ (∃ c : ℝ, ∀ᶠ n in atTop, quoteSeq Y A n = c) :=
  A.exists_twoMarket_legible_pair

/-- **T11, strengthened (OPEN, repair round 1; audit r1 adversarial N1).** The statement of record
above does not exclude a degenerate inhabitant whose quote carries no information about `H`: a
family `Y n` determined via `DPA`'s theory at a computable, non-eventually-constant rational is
legible on *any* market, and only `pkg.reflected`'s exact equality
`𝔼^H_{f n}(X_n) = q n` (an inductor's realized price is not controllable) happens to block it.
This form adds the clause the auditor asked for: `H`'s expectation of `X_n` is a genuine market
price infinitely often — `X_n` is **not** determined via `H`'s own theory at any value, frequently.
A closure of this statement, unlike one of `exists_twoMarket_legible_pair`, would be about (L).
Not proved; not refuted; implies the statement of record by dropping the last conjunct (`twoMarket_legible_pair_of_genuine` below, sorry-free; repair round 2).
Scope: existential; `H`'s market sees `A`'s numbers.
Source: audit r1 adversarial N1; lean-deference-2-011 (a); vq-wiki-048 (c); li-quote-lane F2
Kind: OPEN
Fidelity: stronger: adds non-determinacy of `X` via `DPH` on infinitely many days
Hyps: n/a -/
theorem exists_twoMarket_legible_pair_genuine :
    ∃ (A H : History) (DPA DPH : DeductiveProcess) (f : DeferralFunction) (X Y : ℕ → LUV),
      IsLogicalInductor A DPA ∧ IsLogicalInductor H DPH ∧
      CrossQuotePackage H DPA f X Y ∧ LUV.MachineThresholdCodeSeq X ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) ∧
      LegibleOn H (quoteSeq Y A) ∧ A ≠ H ∧
      ¬ (∃ c : ℝ, ∀ᶠ n in atTop, quoteSeq Y A n = c) ∧
      (∃ᶠ n in atTop, ¬ ∃ y : ℝ, LUV.DeterminedVia (X n) DPH y) := by
  sorry

/-- **OPEN (of record). The evaluation-sparse schedule and its grid certificate for a computable
market** ([[route-sparse-schedule]] §3 Lemma 1 (b)–(d) in FAF's machine model): for `H` with a
`MarketComputation`, an e.c. family `X` and a lookahead `f`, a window-disjoint `DeferralFunction`
`d` along which the grid truth `gridTruth (realized H f X)` is a `FeedbackTruthComputation`. Angle
B's statement, restated (`:= B.exists_gridCertificate_of_marketComputation`, where the `sorry`
is). Once closed, it discharges the (b) certificate of `theoremSS_fullLimit_gridCert` on the
controllable pair. What resists (angle B's report § Certificate): a capped-iteration ruler for a
clocked `evaln` step, and a `MachineDigits` certificate for a clocked run that stays block-complete
on timeouts — FAF plumbing, not mathematics (credence ~0.8).
Source: [[route-sparse-schedule]] §3 Lemma 1 (vq-wiki-046), §9 trap 3; lean-deference-2-010; mandate § Attempt angles (B)
Kind: OPEN
Fidelity: exact (Lemma 1 on the grid truth; the paper's `O(g(k+1))` relaxed to FAF's poly-in-the-pair)
Hyps: (a) `M`, `hX` -/
theorem exists_gridCertificate_of_marketComputation {H : History} (M : MarketComputation H)
    (f : DeferralFunction) (X : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X) :
    ∃ d : DeferralFunction, WindowDisjoint f d ∧
      Nonempty (FeedbackTruth.FeedbackTruthComputation (B.gridTruth (realized H f X)) d) :=
  B.exists_gridCertificate_of_marketComputation M f X hX


/-- **The strengthened T11 implies the statement of record** (audit r2 adversarial N5; the
auditor's probe `GenuineImplies.lean` adopted): drop the last conjunct. Sorry-free, so a dependent
can cite `twoMarket_legible_pair_of_genuine exists_twoMarket_legible_pair_genuine` for the
record's shape once the strengthened form is closed.
Source: audit r2 adversarial N5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem twoMarket_legible_pair_of_genuine
    (hg : ∃ (A H : History) (DPA DPH : DeductiveProcess) (f : DeferralFunction) (X Y : ℕ → LUV),
      IsLogicalInductor A DPA ∧ IsLogicalInductor H DPH ∧
      CrossQuotePackage H DPA f X Y ∧ LUV.MachineThresholdCodeSeq X ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) ∧
      LegibleOn H (quoteSeq Y A) ∧ A ≠ H ∧
      ¬ (∃ c : ℝ, ∀ᶠ n in atTop, quoteSeq Y A n = c) ∧
      (∃ᶠ n in atTop, ¬ ∃ y : ℝ, LUV.DeterminedVia (X n) DPH y)) :
    ∃ (A H : History) (DPA DPH : DeductiveProcess) (f : DeferralFunction) (X Y : ℕ → LUV),
      IsLogicalInductor A DPA ∧ IsLogicalInductor H DPH ∧
      CrossQuotePackage H DPA f X Y ∧ LUV.MachineThresholdCodeSeq X ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) ∧
      LegibleOn H (quoteSeq Y A) ∧ A ≠ H ∧
      ¬ (∃ c : ℝ, ∀ᶠ n in atTop, quoteSeq Y A n = c) := by
  obtain ⟨A, H, DPA, DPH, f, X, Y, h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := hg
  exact ⟨A, H, DPA, DPH, f, X, Y, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end Cleanroom.Fa.FaForcingTrader
