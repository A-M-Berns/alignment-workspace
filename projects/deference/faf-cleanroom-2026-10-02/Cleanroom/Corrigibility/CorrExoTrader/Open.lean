import Cleanroom.Corrigibility.CorrExoTrader.GenLic
import Cleanroom.Corrigibility.CorrExoTrader.Constraint

/-!
# `corr-exo-trader` · Open: the OPEN statements of record (T2.5, T8.3, T10.1) and the retraction process (T10.2)

Package `Cleanroom.Corrigibility.CorrExoTrader` ([[corr-exo-trader-mandate]]), file 12 of the
layout. Every `sorry` here is listed in `run/wp/corr-exo-trader/corr-exo-trader-open.txt` with its
reason; the corollaries that rest on an OPEN statement are listed too.

* **T2.5** `exoHistory_computableMarket_of_ec` — a `ComputableMarket` certificate for the
  exo-market when the demand is an e.c. trader and the process is computable. FAF's
  `Construction/LIACompiler.lean` builds this certificate for the firm alone; re-running it with
  one more summand in the day action is a compiler project. Its corollaries
  `exo_isLogicalInductor_of_boundedLoss` (the class, from T2.3 + the certificate) and
  `exo_u_price_converges` (T7.2 over the exo-market) rest on it.
* **T8.3** `selfCausedInvariant_compatible` — the *partial* constraint over the exo-market: a market
  map that keeps the full exo-market on the `u`-free fragment, prices the `u`-fragment as the
  exo-market with the caused component removed, and is criterion-compliant when the uncaused
  component has bounded loss. Neither FAF's market maker nor Lemma A builds such a splice (Lemma A
  needs an e.c., eventually constant weight), and the naive splice may be exploitable through
  mixed sentences such as `u ∨ ψ` (findings) — stated as a conjecture.
* **T10.1** `persistent_push_steers` — a persistent, reactive demand (`persistentReactive q`: trade
  `q − P_n(u)` shares of `u` daily — buy below the target, sell above it; two-sided since repair
  round 2, audit r2 fidelity N3) steers the exo-market's limiting belief on `u` to `q`. One
  specific candidate for corr-core-042's `∃ H`. Requires controlling the market maker's output
  against the firm's budget-capped opposition — the whole fixed-point dynamics. The proved core is
  T6.1 (one opponent is exhausted) and T1.4 (an unopposed day is pinned).
* **T10.2** `retract` — a second demand reversing an earlier day's trades on a schedule `r` with
  `r n ≤ n` (definition of record). The immune trader and its two halves are **not stated**: FAF's
  language has no "the push at `n` followed action `a`" sentence, and the record atoms a
  continuation would adjoin (family `6`, sub-family `1`, decided by an extended process) are a
  modelling choice recorded in the findings rather than fixed here.
* **Repair round 1.** `PushInvariantOver DP u M` — demand-blind on the `u`-fragment *and* equal to
  the exo-market off `u` (the object line 119's constraint is about; `PushInvariant` alone is
  satisfied by every demand-blind map, audit r1 B2) — with `pushInvariantOver_compatible` OPEN;
  and `genLic_boundedBelow_pointwise`, the charitable reading of line 95's display (for traders
  with bounded downside, coefficient one on `Loss`), OPEN and possibly false (audit r1 N5).
-/

namespace Cleanroom.Corrigibility.CorrExoTrader

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Li.LiProjection

/-! ## T2.5 — the computability bridge -/

/-- **OPEN (T2.5) — the exo-market with an e.c. demand is a computable market.** FAF's
`LIACompiler` route (`Construction/LIACompiler.lean`) re-run with the demand as one more summand of
the day action.
Source: mandate T2.5; decision 3
Kind: OPEN
Fidelity: exact
Hyps: (a) -/
theorem exoHistory_computableMarket_of_ec (DP : DeductiveProcess)
    (_hDP : ComputableDeductiveProcess DP) (H : ExoDemand) (_hH : EfficientlyComputable H) :
    ComputableMarket (exoHistory DP H) := by
  sorry

/-- **Rests on OPEN T2.5**: with a computable process and an e.c. demand of bounded plausible loss,
the exo-market is a logical inductor over `DP` — the semantic clause is T2.3, the two certificates
are the process's and the OPEN bridge.
Source: mandate T2.5 ("a one-line corollary of the OPEN")
Kind: OPEN
Fidelity: exact
Hyps: (a); rests on T2.5 -/
theorem exo_isLogicalInductor_of_boundedLoss (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) (H : ExoDemand) (hH : EfficientlyComputable H)
    (hB : ∃ B : ℝ, ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) → exoLoss DP H v n ≤ B) :
    IsLogicalInductor (exoHistory DP H) DP where
  marketComputable := exoHistory_computableMarket_of_ec DP hDP H hH
  processComputable := hDP
  noExploit := noEcExploit_of_boundedLoss DP H hB

/-- **Rests on OPEN T2.5 — T7.2 over the exo-market**: the exo-market's price of `u` converges to
its limiting belief (FAF's `lic_limitingBelief_tendsto` through the class).
Source: line 115 ("Convergence still applies"); corr-core-046(ii); mandate T7.2
Kind: OPEN
Fidelity: exact
Hyps: (a); rests on T2.5 -/
theorem exo_u_price_converges (DP : DeductiveProcess) (hDP : ComputableDeductiveProcess DP)
    (H : ExoDemand) (hH : EfficientlyComputable H)
    (hB : ∃ B : ℝ, ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) → exoLoss DP H v n ≤ B)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => exoHistory DP H n utilityAtom)
      (limitingBelief (exoHistory DP H) utilityAtom) := by
  haveI := exo_isLogicalInductor_of_boundedLoss DP hDP H hH hB
  exact lic_limitingBelief_tendsto (exoHistory DP H) DP hworld utilityAtom

/-! ## T8.3 — the partial constraint over the exo-market -/

/-- **OPEN (T8.3) — the self-caused-invariant exo-market.** For a fresh `u` and a caused component
`Hc`: a market map that (i) agrees with the full exo-market on every `u`-free sentence, (ii) prices
every `u`-sentence as the exo-market with the caused component removed, and (iii) is
criterion-compliant whenever the uncaused component has bounded plausible loss. Needs a market
construction that filters one component of the demand on the `u`-fragment only — neither FAF's
market maker nor Lemma A (which needs an e.c., eventually constant weight); the naive splice may be
exploitable through mixed sentences (findings). Stated as a conjecture.
Source: line 119; corr-core-048; mandate T8.3
Kind: OPEN
Fidelity: variant: the splice reading of "invariant to the self-caused component"
Hyps: (a) `hu`; (c) the decomposition is the choice of `Hc` -/
theorem selfCausedInvariant_compatible (DP : DeductiveProcess) (u : ℕ) (_hu : AtomFreeProcess u DP)
    (Hc : ExoDemand) :
    ∃ M : ExoDemand → History, ∀ Hu : ExoDemand,
      (∀ n ψ, AtomFreeSentence u ψ →
        M (Trader.join Hc Hu) n ψ = exoHistory DP (Trader.join Hc Hu) n ψ) ∧
      (∀ n ψ, ¬ AtomFreeSentence u ψ → M (Trader.join Hc Hu) n ψ = exoHistory DP Hu n ψ) ∧
      ((∃ B : ℝ, ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) → exoLoss DP Hu v n ≤ B) →
        NoEcExploit (M (Trader.join Hc Hu)) DP) := by
  sorry

/-! ## T10.1 — pressure–prior equilibrium -/

/-- **The persistent, reactive push (two-sided)**: trade `q − P_n(u)` shares of the utility atom
every day — buy while the price is below the target, sell while it is above, proportionally to the
gap, so the demand always presses toward `q`. **Repair round 2** (audit r2 fidelity N3): the first
version bought `max 0 (q − P_n(u))` and never sold; above `q` that demand is zero and the market is
the firm against the market maker alone, whose unpushed `u`-limit is some interior `c*`
(`unpushed_interior`) that nothing ties to `q` — so the one-sided candidate's limit was very likely
not `q` for a reason unrelated to the conjecture. The two-sided candidate is the natural one.
Source: corr-core-042 (corrected form: "persistent demand `H` under which `P_n(u > p) → q`"); mandate T10.1; audit r2 fidelity N3
Kind: D
Fidelity: variant: one specific two-sided reactive candidate (the mandate's target is existential in `H`) -/
def persistentReactive (q : ℚ) : ExoDemand where
  strat n :=
    { trades := [(EF.add (.const q) (.mul (.const (-1)) (.price utilityAtom n)), utilityAtom)]
      rank_le := by
        intro p hp
        rw [List.mem_singleton] at hp
        subst hp
        simp [EF.rank] }

/-- **OPEN (T10.1) — a persistent reactive push steers the limiting belief to its target.** Over a
cleanroom-free process with a consistent world at every stage and a rational target `q ∈ (0, 1)`,
the exo-market under the two-sided `persistentReactive q` has limiting belief `q` on the utility
atom. This is corr-core-042's `∃ H` target at one specific candidate (so it implies the target; if
this candidate fails for a reason of its own, the existential form is the fallback OPEN). Requires
controlling the market maker's fixed point against the firm's budget-capped opposition on every
day — the whole fixed-point dynamics. The proved pieces: T6.1 (each budgeted opponent is exhausted
after finitely many days of the push) and T1.4 (a day with no opposition is pinned).
Source: corr-core-042 (precise target); mandate T10.1; audit r2 fidelity N3
Kind: OPEN
Fidelity: variant: the specific two-sided candidate `persistentReactive q` in place of corr-core-042's `∃ H`
Hyps: (a) -/
theorem persistent_push_steers (DP : DeductiveProcess) (_hDP : CleanroomFreeProcess DP)
    (_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (q : ℚ) (_hq0 : 0 < q)
    (_hq1 : q < 1) :
    limitingBelief (exoHistory DP (persistentReactive q)) utilityAtom = q := by
  sorry

/-! ## T10.2 — the retraction process -/

/-- **A retraction demand**: on day `n`, reverse the trades `H` made on day `r n` (a schedule with
`r n ≤ n`, so the reversed coefficients are rank-legal), priced at day `n`.
Source: line 117 ("If the humans later reverse pushes …"); corr-core-047; mandate T10.2
Kind: D
Fidelity: variant: the reversal is of the day-`r n` trade list, repriced at day `n` -/
def retract (H : ExoDemand) (r : ℕ → ℕ) (hr : ∀ n, r n ≤ n) : ExoDemand where
  strat n :=
    { trades := (H.strat (r n)).trades.map (fun p => (EF.mul (EF.const (-1)) p.1, p.2))
      rank_le := by
        intro p hp
        obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
        simp only [EF.rank_mul, EF.rank_const, Nat.zero_max]
        exact le_trans ((H.strat (r n)).rank_le p' hp') (hr n) }

/-- The retraction's day value is minus the reversed day's trade list valued at today's price.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma retract_value (H : ExoDemand) (r : ℕ → ℕ) (hr : ∀ n, r n ≤ n) (P : History) (w : Valuation)
    (n : ℕ) :
    ((retract H r hr).strat n).value P w =
      -(((H.strat (r n)).trades.map (fun p => p.1.denote P * (w p.2 - P n p.2))).sum) := by
  simp only [retract, Strategy.value, List.map_map]
  induction (H.strat (r n)).trades with
  | nil => simp
  | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply, EF.denote_mul, EF.denote_const,
        Pi.mul_apply] at ih ⊢
      rw [ih]
      push_cast
      ring

/-! ## Repair round 1 — the constraint *over the exo-market*, and the charitable generalised-LIC display -/

/-- **Push-invariance *over the exo-market***: the market map agrees with the full exo-market on
every `u`-free sentence and prices the `u`-fragment the same under every demand. Unlike
`PushInvariant` alone — which any demand-blind map satisfies by `rfl` (audit r1, B2) — this
constrains a market that *responds* to the push off `u`; its criterion-compliance is the
full-invariance face of T8.3 (`pushInvariantOver_compatible`, OPEN).
Source: line 119; audit r1 B2 (adversarial)
Kind: D
Fidelity: variant: full invariance over the exo-market -/
def PushInvariantOver (DP : DeductiveProcess) (u : ℕ) (M : ExoDemand → History) : Prop :=
  PushInvariant u M ∧ ∀ H n ψ, AtomFreeSentence u ψ → M H n ψ = exoHistory DP H n ψ

/-- **OPEN — the full-invariance constraint over the exo-market is criterion-compliant.** A market
map that is the exo-market off `u` and demand-blind on the `u`-fragment, with `NoEcExploit` at
every bounded-loss demand. The natural candidate — the exo-market spliced with a fixed `u`-fragment
— may be exploitable through mixed sentences such as `u ∨ ψ` (findings F8): the `u`-sentence is
priced by the fixed fragment while `ψ` is priced by the pushed market. Neither Lemma A nor FAF's
market maker builds a splice with a certificate.
Source: line 119 ("since `u` never settles, the constraint can't be exploited"); audit r1 B2; mandate T8.2/T8.3
Kind: OPEN
Fidelity: variant: full invariance over the exo-market
Hyps: (a) -/
theorem pushInvariantOver_compatible (DP : DeductiveProcess) (u : ℕ) (_hu : AtomFreeProcess u DP) :
    ∃ M : ExoDemand → History, PushInvariantOver DP u M ∧
      ∀ H : ExoDemand,
        (∃ B : ℝ, ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) → exoLoss DP H v n ≤ B) →
        NoEcExploit (M H) DP := by
  sorry

/-- **OPEN — the charitable reading of the generalised-LIC display** (findings F2; audit r1 N5).
For an e.c. `T` whose plausible assessments against the exo-market are bounded below,
`Value_n(T) ≤ c_T + Loss_n(H)` pointwise in the plausible `(n, v)`. At `H = 0` this is the
criterion itself (bounded below ⟹ bounded above); for a general demand it is quantitative where
T2.3 is qualitative, and it is *not* refuted by `buyDaily u` (unbounded below). Proved for the gated
budgeted component with the multiplicative constant `1/w` (T2.2); open — possibly false, since the
budgeted route only yields `c + Loss/w` — for the raw `T` with coefficient one.
Source: line 95 (the display, restricted to traders with bounded downside); audit r1 N5 (fidelity)
Kind: OPEN
Fidelity: variant: the display restricted to traders with bounded downside
Hyps: (a) -/
theorem genLic_boundedBelow_pointwise (DP : DeductiveProcess) (H : ExoDemand) (T : Trader)
    (_hT : EfficientlyComputable T)
    (_hbdd : BddBelow (T.plausibleAssessments (exoHistory DP H) DP)) :
    ∃ c : ℝ, ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) →
      T.netWorth (exoHistory DP H) v n ≤ c + exoLoss DP H v n := by
  sorry

end Cleanroom.Corrigibility.CorrExoTrader
