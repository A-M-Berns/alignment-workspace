import Cleanroom.Corrigibility.CorrExoTrader.GenLic
import Cleanroom.Corrigibility.CorrExoTrader.FrontRun
import Cleanroom.Corrigibility.CorrExoTrader.Budget
import Cleanroom.Corrigibility.CorrExoTrader.Constraint
import Cleanroom.Corrigibility.CorrExoTrader.Undecided

/-!
# `corr-exo-trader` · Instances: front-running at the exo-market (T3.2) and the two proposals compared (T11.1)

Package `Cleanroom.Corrigibility.CorrExoTrader` ([[corr-exo-trader-mandate]]), file 11 of the
layout; the heaviest import set (construction + machine capstones + Lemma A).

* **T3.2 `frontRun_exo`** (kind C): T3.1 at the exo-market, with `NoEcExploit` supplied by T2.3
  (bounded push loss) and the range by `exoHistory_range`. The theorem the thesis wants: "already
  believes what it expects to be taught" — and, by the same token, the belief-side mechanism of
  fully-updated deference (audit row 2.4): once the pushes are predictable, waiting for them has no
  informational value. **What the asymptotic form does not say** (audit r1 B1/N6): nothing about
  any *single* push being absorbed "before" it arrives — `AsympEq` ignores every finite prefix; the
  source's temporal "before" is the rate question T3.4, not attempted. **N−** `frontRun_witness`:
  an inductor over a fresh atom with a one-jump schedule (`li-projection`'s
  `jeffrey_steering_finiteJumps`, modulo (A)) inhabits T3.1's *full* hypothesis package, but on a
  constant sentence family with an eventually-constant schedule T3.1's premise and conclusion are
  the same proposition for every history (`asympEq_shift_iff_of_eventuallyConst`), so the
  exploitation argument is not exercised. **The content check** is refutation-shaped (kind C, a
  consequence of T3.1, not an inhabitation — audit r2 fidelity N4): the alternating e.c. schedule
  `altSchedule` (`3/10, 7/10, …`, certificate `altSchedule_machineRatCodes`) is *not* a landing on
  any no-exploit market (`no_landing_altSchedule`), in particular not at FAF's own `liaHistory`
  with no OPEN behind it (`no_landing_altSchedule_lia`) and not at the exo-market under a
  bounded-loss demand (`no_landing_altSchedule_exo`). **Its reach** (repair round 2, audit r2
  adversarial N2): over an *inductor* the same refutation follows from convergence alone
  (`landing_increments_vanish_of_inductor`; T3.1 on a constant family is an equivalence for every
  schedule there, `frontRun_const_family_iff_of_inductor`), so the check does not distinguish
  front-running from `thm:con` — the varying-family regime, which would, is unchecked. **`hworld`
  is necessary, as a counter-model** (audit r2 fidelity N2): `lagHist ψ` over `falsumDP` satisfies
  every other hypothesis of T3.1, with the landing exact, and fails the conclusion
  (`frontRun_fails_without_hworld`). **T3.2's N−** `frontRun_exo_witness_theorem`: no demand, a
  theorem of the process, the constant schedule `1` — the full package and the conclusion, resting
  on nothing open.
* **T6.1 at the utility atom** (repair round 1): the source's *opposer* of an upward push
  (`occam_exhausted_opposer_utilityAtom`, buys `∼u`), the no-push N− inhabitation
  (`occam_exhausted_half_table_utilityAtom`), and T2.3's regime boundary
  `persistent_push_unbounded_loss`: a landed persistent push has unbounded plausible loss, so the
  exploitation form (T2.3) does not cover it — T2.1 with `Loss` growing does.
* **T11.1 `exhausted_vs_invariant`** (kind L): the two proposals are different objects — under a
  push the budgeted Occam opposer is silent from the explicit day `M` on, while a `PushInvariant`
  market's `u`-prices equal the unpushed market's on *every* day by definition (the second conjunct
  is the hypothesis `hM` unfolded). It does not show the constraint is *achievable* over the
  exo-market (T8.3 / `pushInvariantOver_compatible`, OPEN), nor that a skewed prior is useless on
  finite horizons. ATTRIBUTION-UNVETTED whether this is what Abram's "prior skewed toward trust"
  meant.
-/

namespace Cleanroom.Corrigibility.CorrExoTrader

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Li.LiProjection Filter Topology

/-! ## T3.2 — front-running at the exo-market -/

/-- **T3.2 — front-running at the exo-market.** If the exogenous demand's plausible loss is bounded
and the process has a consistent world at every stage, then for an e.c. sentence family `φ` and an
e.c. schedule `q`: if the exo-market's next-day price of `φ_n` lands at `q_n`, its same-day price is
already there — **asymptotically**: `AsympEq` ignores every finite prefix, so nothing is said about
any *single* push being absorbed "before" it arrives (the rate is T3.4, not attempted). With that
qualification: "a corrigible agent already believes what it expects to be legitimately taught"; and
the belief-side mechanism of fully-updated deference — once pushes are predictable in the limit,
waiting for them is informationally redundant. **Regime**: bounded-loss demands only; the landed
persistent push is excluded (`persistent_push_unbounded_loss`). Inhabitation: N−
`frontRun_exo_witness_theorem` (no demand, a theorem of the process, the constant schedule `1`);
no non-degenerate exo-market inhabitation of the landing premise is available short of T10.1.
Single-market.
Source: line 77; corr-core-043, 011, 025; audit row 2.4; mandate T3.2
Kind: C
Fidelity: variant: conditional on the push landing (as T3.1); asymptotic (no single-push claim)
Hyps: (a): `hB` is the bounded-loss premise of T2.3, the rest as T3.1 -/
theorem frontRun_exo (DP : DeductiveProcess) (H : ExoDemand)
    (hB : ∃ B : ℝ, ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) → exoLoss DP H v n ≤ B)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) (q : ℕ → ℚ) (hq : MachineRatCodes q)
    (hland : AsympEq (fun n => exoHistory DP H (n + 1) (φ n)) (fun n => (q n : ℝ))) :
    AsympEq (fun n => exoHistory DP H n (φ n)) (fun n => (q n : ℝ)) :=
  frontRun_asympEq (exoHistory DP H) DP (noEcExploit_of_boundedLoss DP H hB) hworld
    (exoHistory_range DP H) φ hφ q hq hland

/-- The one-jump schedule `q₀` before day `N`, `c*` from day `N` on.
Source: `li-projection` `jeffrey_steering_finiteJumps`; mandate T3.2 (N+)
Kind: D
Fidelity: exact -/
def jumpWeight (q₀ cstar : ℚ) (N : ℕ) : ℕ → ℚ := fun n => if n < N then q₀ else cstar

/-- The one-jump schedule is eventually constant at `c*`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jumpWeight_eventually (q₀ cstar : ℚ) (N : ℕ) :
    ∀ n, N ≤ n → jumpWeight q₀ cstar N n = jumpWeight q₀ cstar N N := by
  intro n hn
  simp [jumpWeight, not_lt.mpr hn]

/-- The one-jump schedule is non-constant when `q₀ ≠ c*` and `0 < N`.
Source: mandate T3.2 ("the price moves at `N`")
Kind: L
Fidelity: n/a -/
lemma jumpWeight_moves (q₀ cstar : ℚ) (hne : q₀ ≠ cstar) (N : ℕ) (hN : 0 < N) :
    jumpWeight q₀ cstar N (N - 1) ≠ jumpWeight q₀ cstar N N := by
  simp [jumpWeight, Nat.sub_lt hN Nat.one_pos, hne]

/-- **T3.2's witness — T3.1's full hypothesis package inhabited, graded N− (audit r1, B1).** For an
inductor `P` over `DP` with `u` fresh and the one-jump schedule `q := jumpWeight q₀ c* N` with
`q₀, c* ∈ [η, 1−η]`: the projection `P' := project P u q` satisfies `NoEcExploit` (it is an inductor,
Lemma A, modulo (A)), has prices in `[0, 1]`, the constant sentence family `u` and the schedule are
e.c., and both the landing premise `P'_{n+1}(u) ≈ₙ q_n` and the conclusion `P'_n(u) ≈ₙ q_n` hold —
the price of `u` converges to `c*` (`project_atom_tendsto`). **Why N−**: on a constant family
against an eventually-constant schedule the premise and the conclusion are the same proposition
for every history (`asympEq_shift_iff_of_eventuallyConst`), so the proof below derives both from
one convergence fact and never invokes `frontRun_asympEq`; the exploitation content is not
exercised. The jump at `N` (`jumpWeight_moves`) is a finite transient `AsympEq` cannot see. A
non-degenerate inhabitation would need a varying sentence family (distinct fresh atoms, which the
single-atom `project` cannot supply) or a schedule with non-vanishing increments — on which T3.1
says the *premise fails*: the honest content check is `no_landing_altSchedule` below.
Source: mandate T3.2 (N+ asked; N− delivered — see above)
Kind: N−
Fidelity: exact (hypothesis-satisfiability only; the implication is a reindexing on this instance)
Hyps: (a); the `NoEcExploit` conjunct rests on li-projection's OPEN (A) -/
theorem frontRun_witness (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ) (hu : AtomFreeProcess u DP)
    (q₀ cstar η : ℚ) (hη : 0 < η) (hq₀ : η ≤ q₀ ∧ q₀ ≤ 1 - η) (hc : η ≤ cstar ∧ cstar ≤ 1 - η)
    (N : ℕ) :
    NoEcExploit (project P u (jumpWeight q₀ cstar N)) DP ∧
    (∀ n φ, 0 ≤ project P u (jumpWeight q₀ cstar N) n φ ∧
      project P u (jumpWeight q₀ cstar N) n φ ≤ 1) ∧
    MachineSentenceCodes (fun _ => Formula.atom u) ∧
    MachineRatCodes (jumpWeight q₀ cstar N) ∧
    AsympEq (fun n => project P u (jumpWeight q₀ cstar N) (n + 1) (Formula.atom u))
      (fun n => (jumpWeight q₀ cstar N n : ℝ)) ∧
    AsympEq (fun n => project P u (jumpWeight q₀ cstar N) n (Formula.atom u))
      (fun n => (jumpWeight q₀ cstar N n : ℝ)) := by
  have hLI : IsLogicalInductor (project P u (jumpWeight q₀ cstar N)) DP :=
    (jeffrey_steering_finiteJumps P DP hworld u hu q₀ cstar η hη hq₀ hc N).1
  have hjump := jumpWeight_eventually q₀ cstar N
  have hprice : Tendsto (fun n => project P u (jumpWeight q₀ cstar N) n (Formula.atom u)) atTop
      (𝓝 (jumpWeight q₀ cstar N N)) :=
    project_atom_tendsto P DP hworld u (jumpWeight q₀ cstar N) N hjump
  have hq : Tendsto (fun n => (jumpWeight q₀ cstar N n : ℝ)) atTop (𝓝 (jumpWeight q₀ cstar N N)) :=
    tendsto_weight_of_jump (jumpWeight q₀ cstar N) N hjump
  refine ⟨hLI.noExploit, fun n φ => hLI.price_mem_Icc n φ, MachineSentenceCodes.const _,
    MachineRatCodes.ofFiniteTable _ N cstar (fun n hn => by simp [jumpWeight, not_lt.mpr hn]),
    ?_, ?_⟩
  · unfold AsympEq
    have h := (hprice.comp (tendsto_add_atTop_nat 1)).sub hq
    simpa using h
  · unfold AsympEq
    have h := hprice.sub hq
    simpa using h

/-! ## T3.1's content on a constant sentence: the alternating schedule is refuted as a landing -/

/-- The alternating e.c. schedule `3/10, 7/10, 3/10, …`: increments of size `2/5` forever.
Source: audit r1 B1 (the refutation-shaped content check)
Kind: D
Fidelity: exact -/
def altSchedule : ℕ → ℚ := fun n => if n % 2 = 0 then 3 / 10 else 7 / 10

/-- `altSchedule` is machine-metered: the two-entry table `k ↦ (if k < 1 then 3/10 else 7/10)`
(li-projection's `MachineRatCodes.ofFiniteTable`) reindexed by the ruler `n ↦ n % 2`
(`MachineDigits.mod_two` of the identity ruler) through FAF's `MachineRatCodes.comp`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem altSchedule_machineRatCodes : MachineRatCodes altSchedule := by
  have htab : MachineRatCodes (fun k : ℕ => if k < 1 then (3 / 10 : ℚ) else 7 / 10) :=
    MachineRatCodes.ofFiniteTable _ 1 (7 / 10) (fun k hk => by simp [not_lt.mpr hk])
  have hmod : UnaryRuler (fun n : ℕ => n % 2) :=
    (MachineDigits.ofUnaryRuler UnaryRuler.id).mod_two
  refine (htab.comp hmod).of_eq (fun n => ?_)
  simp only [altSchedule, Nat.lt_one_iff]

/-- The alternating schedule's increments have size `2/5` on every day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma altSchedule_increment (n : ℕ) : |(altSchedule (n + 1) : ℝ) - altSchedule n| = 2 / 5 := by
  unfold altSchedule
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [if_neg (by omega), if_pos h]
    push_cast
    rw [abs_of_nonneg (by norm_num)]
    norm_num
  · rw [if_pos (by omega), if_neg (by omega)]
    push_cast
    rw [abs_of_nonpos (by norm_num)]
    norm_num

/-- **No no-exploit market's price of a fixed sentence tracks the alternating schedule one day
ahead** — T3.1's content on a constant sentence, exercised: the schedule is e.c.
(`altSchedule_machineRatCodes`), its increments never vanish (`altSchedule_increment`), so by
`no_landing_of_increments` the landing premise of T3.1 is false on every `[0,1]`-market that no
e.c. trader exploits. This is the refutation-shaped non-vacuity check for T3.1 (audit r1, B1): what
the theorem forbids, exhibited. **Kind C, not N+** (audit r2 fidelity N4): this is a *consequence*
of T3.1, not an inhabitant of its hypothesis package — it shows the landing premise is false at
`altSchedule`; the witness of record for T3.1 is the N− `frontRun_witness`. `hNE` is load-bearing
here: a `[0,1]`-market whose day-`n` price is `altSchedule (n − 1)` tracks the schedule one day ahead
exactly (`lagHist`, below), so without the no-exploit hypothesis the landing is possible. Over an
*inductor* the same refutation follows from convergence alone (`thm:con`,
`landing_increments_vanish_of_inductor` below) — what this check adds is the derivation over bare
`NoEcExploit` + range, without the class.
Source: audit r1 B1; mandate T3.2; audit r2 fidelity N4, adversarial N2
Kind: C
Fidelity: variant: constant sentence family; refutation shape (the asymptotic statement cannot witness a single push being absorbed)
Hyps: (a): `hNE`, `hworld`, `hrange` as T3.1 -/
theorem no_landing_altSchedule (P : History) (DP : DeductiveProcess) (hNE : NoEcExploit P DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hrange : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (ψ : Sentence) :
    ¬ AsympEq (fun n => P (n + 1) ψ) (fun n => (altSchedule n : ℝ)) :=
  no_landing_of_increments P DP hNE hworld hrange ψ altSchedule altSchedule_machineRatCodes
    (2 / 5) (by norm_num) (fun n => (altSchedule_increment n).ge)

/-- The instance at FAF's own LI construction — **no OPEN, no (A)**: `liaHistory DP`'s next-day
price of any sentence never tracks the alternating schedule, over any process with a consistent
world at every stage. T3.1's hypothesis package (minus the landing) is supplied here by FAF's
`lia_no_efficient_trader_exploits` (`noEcExploit_liaHistory`) and `liaHistory`'s range. A
consequence of T3.1 (kind C), not an inhabitation; over `liaHistory` as an inductor the refutation
is also a special case of convergence (`landing_increments_vanish_of_inductor`) — the value here is
that it rests on nothing open and on no class.
Source: audit r1 B1; mandate T3.2; audit r2 fidelity N4, adversarial N2
Kind: C
Fidelity: variant: as `no_landing_altSchedule`
Hyps: (a) -/
theorem no_landing_altSchedule_lia (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (ψ : Sentence) :
    ¬ AsympEq (fun n => liaHistory DP (n + 1) ψ) (fun n => (altSchedule n : ℝ)) :=
  no_landing_altSchedule (liaHistory DP) DP (noEcExploit_liaHistory DP) hworld
    (fun n φ => by rw [← exoHistory_noDemand]; exact exoHistory_range DP noDemand n φ) ψ

/-- And at the exo-market under a bounded-loss demand (T3.2's regime).
Source: audit r1 B1; mandate T3.2
Kind: C
Fidelity: variant: as `no_landing_altSchedule`
Hyps: (a): `hB` as T2.3 -/
theorem no_landing_altSchedule_exo (DP : DeductiveProcess) (H : ExoDemand)
    (hB : ∃ B : ℝ, ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) → exoLoss DP H v n ≤ B)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (ψ : Sentence) :
    ¬ AsympEq (fun n => exoHistory DP H (n + 1) ψ) (fun n => (altSchedule n : ℝ)) :=
  no_landing_altSchedule (exoHistory DP H) DP (noEcExploit_of_boundedLoss DP H hB) hworld
    (exoHistory_range DP H) ψ

/-! ## Repair round 2: the content check's reach over an inductor, `hworld`'s necessity as a
counter-model, and T3.2's N−

Three probes of audit round 2 adopted (adversarial N2, fidelity N2) and one gap filled (fidelity
N6). Over an *inductor* the constant-sentence content form of T3.1 is a corollary of convergence
(`thm:con`) with no e.c. hypothesis and no front-runner, so the alternating-schedule refutation does
not distinguish front-running from convergence there; what distinguishes T3.1 is the *varying*
sentence family, for which the package ships neither an inhabitation nor a check (the obstacle is
steering two atoms' prices; li-projection's `project` is single-atom). The `hworld`-free T3.1 is
*false*, not merely vacuous in `hNE`: `lagHist` over `falsumDP` satisfies every other hypothesis
and fails the conclusion. And T3.2's hypothesis package is inhabited, degenerately, with no demand
at a theorem of the process. -/

/-- **Over an inductor, a tracked schedule has vanishing increments — no e.c. hypothesis on `q`, no
front-runner**: FAF's `lic_limitingBelief_tendsto` (`thm:con`) makes `P n ψ` converge, so any
schedule that tomorrow's price tracks converges to the same limit, and its increments vanish. The
alternating schedule is refuted as a landing by convergence alone over an inductor; the package's
`landing_increments_vanish` re-derives this special case over bare `NoEcExploit` + range, without
the class (modest, as the adversarial auditor says).
Source: audit r2 adversarial N2 (probe `LandingFromConvergence.lean`, adopted); FAF `lic_limitingBelief_tendsto` (`thm:con`)
Kind: L
Fidelity: n/a -/
theorem landing_increments_vanish_of_inductor (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : Sentence) (q : ℕ → ℝ)
    (hland : AsympEq (fun n => P (n + 1) ψ) q) :
    Tendsto (fun n => q (n + 1) - q n) atTop (𝓝 0) := by
  have hconv : Tendsto (fun n => P n ψ) atTop (𝓝 (limitingBelief P ψ)) :=
    lic_limitingBelief_tendsto P DP hworld ψ
  have h1 : Tendsto (fun n => P (n + 1) ψ) atTop (𝓝 (limitingBelief P ψ)) :=
    hconv.comp (tendsto_add_atTop_nat 1)
  have hland' : Tendsto (fun n => P (n + 1) ψ - q n) atTop (𝓝 0) := hland
  have hq : Tendsto q atTop (𝓝 (limitingBelief P ψ)) := by
    have := h1.sub hland'
    simpa using this
  have hq1 : Tendsto (fun n => q (n + 1)) atTop (𝓝 (limitingBelief P ψ)) :=
    hq.comp (tendsto_add_atTop_nat 1)
  simpa using hq1.sub hq

/-- **Over an inductor, T3.1 on a constant family is an equivalence for *every* schedule**: premise
and conclusion both say "`q` converges to the price's limit". This generalises
`asympEq_shift_iff_of_eventuallyConst` (eventually-constant schedules, any history) to all real
schedules over an inductor — and is why no constant-family instance over an inductor can exercise
T3.1's exploitation argument.
Source: audit r2 adversarial N2 (probe `LandingFromConvergence.lean`, adopted); FAF `lic_limitingBelief_tendsto`
Kind: L
Fidelity: n/a -/
theorem frontRun_const_family_iff_of_inductor (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : Sentence) (q : ℕ → ℝ) :
    AsympEq (fun n => P (n + 1) ψ) q ↔ AsympEq (fun n => P n ψ) q := by
  have hconv : Tendsto (fun n => P n ψ) atTop (𝓝 (limitingBelief P ψ)) :=
    lic_limitingBelief_tendsto P DP hworld ψ
  have h1 : Tendsto (fun n => P (n + 1) ψ) atTop (𝓝 (limitingBelief P ψ)) :=
    hconv.comp (tendsto_add_atTop_nat 1)
  have key : ∀ f : ℕ → ℝ, Tendsto f atTop (𝓝 (limitingBelief P ψ)) →
      (AsympEq f q ↔ Tendsto q atTop (𝓝 (limitingBelief P ψ))) := by
    intro f hf
    constructor
    · intro h
      have h' : Tendsto (fun n => f n - q n) atTop (𝓝 0) := h
      have := hf.sub h'
      simpa using this
    · intro h
      show Tendsto (fun n => f n - q n) atTop (𝓝 0)
      have := hf.sub h
      simpa using this
  rw [key _ h1, key _ hconv]

/-- A deductive process with an inconsistent stage from day `0`: `D n = {⊥}`.
Source: audit r2 fidelity N2 (probe `HworldCounterModel.lean`, adopted)
Kind: D
Fidelity: n/a -/
def falsumDP : DeductiveProcess := ⟨fun _ => {⊥}, fun _ => Finset.Subset.refl _⟩

/-- No p.c. world is consistent with `{⊥}`.
Source: audit r2 fidelity N2
Kind: L
Fidelity: n/a -/
lemma falsumDP_inconsistent (n : ℕ) (v : PCWorld) : ¬ v.ConsistentWith (falsumDP.D n) := by
  intro h
  have := h ⊥ (by simp [falsumDP])
  simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val] at this

/-- The history whose price of `ψ` on day `n` is `altSchedule (n − 1)` (and `½` elsewhere): tomorrow's
price of `ψ` is exactly today's schedule value. Tracks the alternating schedule one day ahead, so
without a no-exploit hypothesis the landing premise of T3.1 is satisfiable on a `[0,1]`-market.
Source: audit r2 fidelity N2, adversarial N2 (probes `HworldCounterModel.lean`, `TrackingWithoutNoExploit.lean`, adopted)
Kind: D
Fidelity: n/a -/
noncomputable def lagHist (ψ : Sentence) : History :=
  fun n χ => if χ = ψ then (altSchedule (n - 1) : ℝ) else 1 / 2

/-- The alternating schedule takes values in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma altSchedule_mem (n : ℕ) : (0 : ℝ) ≤ altSchedule n ∧ (altSchedule n : ℝ) ≤ 1 := by
  unfold altSchedule
  split_ifs <;> norm_num

/-- **Every hypothesis of `frontRun_asympEq` except `hworld` holds on `lagHist ψ` over `falsumDP`, and
the conclusion fails** — so the `hworld`-free statement is *false*, not merely vacuous in `hNE`
(which `noEcExploit_of_inconsistent_stage` alone shows). The landing premise holds *exactly*
(`lagHist ψ (n+1) ψ = altSchedule n`); the conclusion fails by `2/5` on every day `≥ 1`
(`altSchedule_increment`). Completes F9.2's necessity claim.
Source: audit r2 fidelity N2 (probe `HworldCounterModel.lean`, adopted); findings F9.2
Kind: N+ (counter-model: the `hworld`-free T3.1 is refuted, non-degenerately — every other hypothesis holds and the landing is exact)
Fidelity: exact
Hyps: (a) -/
theorem frontRun_fails_without_hworld (ψ : Sentence) :
    NoEcExploit (lagHist ψ) falsumDP ∧
    (∀ n φ, 0 ≤ lagHist ψ n φ ∧ lagHist ψ n φ ≤ 1) ∧
    MachineSentenceCodes (fun _ => ψ) ∧
    MachineRatCodes altSchedule ∧
    AsympEq (fun n => lagHist ψ (n + 1) ψ) (fun n => (altSchedule n : ℝ)) ∧
    ¬ AsympEq (fun n => lagHist ψ n ψ) (fun n => (altSchedule n : ℝ)) := by
  have hrange : ∀ n φ, 0 ≤ lagHist ψ n φ ∧ lagHist ψ n φ ≤ 1 := by
    intro n φ
    unfold lagHist
    split_ifs
    · exact altSchedule_mem _
    · norm_num
  refine ⟨noEcExploit_of_inconsistent_stage (lagHist ψ) falsumDP hrange 0 (falsumDP_inconsistent 0),
    hrange, MachineSentenceCodes.const ψ, altSchedule_machineRatCodes, ?_, ?_⟩
  · -- the landing premise holds exactly: `lagHist ψ (n+1) ψ = altSchedule n`
    unfold AsympEq
    have h : (fun n => lagHist ψ (n + 1) ψ - (altSchedule n : ℝ)) = fun _ => 0 := by
      funext n
      simp [lagHist]
    rw [h]
    exact tendsto_const_nhds
  · -- the conclusion fails: `|lagHist ψ n ψ - altSchedule n| = 2/5` for every `n ≥ 1`
    intro hc
    unfold AsympEq at hc
    rw [Metric.tendsto_atTop] at hc
    obtain ⟨N, hN⟩ := hc (2 / 5) (by norm_num)
    have h := hN (N + 1) (Nat.le_succ N)
    rw [Real.dist_eq, sub_zero] at h
    change |lagHist ψ (N + 1) ψ - (altSchedule (N + 1) : ℝ)| < 2 / 5 at h
    have hval : lagHist ψ (N + 1) ψ = (altSchedule N : ℝ) := by simp [lagHist]
    rw [hval] at h
    have hinc := altSchedule_increment N
    rw [abs_sub_comm] at hinc
    linarith

/-- **N− for T3.2 (`frontRun_exo`)** — its full hypothesis package *and* its conclusion, with no
demand, at a theorem of the process and the constant schedule `1`: over any process for which
`liaHistory DP` is an inductor (FAF's `LIA_is_logical_inductor` for every computable process;
taken as an instance argument so as not to import `Construction/LIACompiler` here) with a
consistent world at every stage and a sentence `ψ` proved at some stage, the bounded-loss premise
holds with `B = 0` (`noDemand`), the constant family and the constant schedule are e.c., and both
the landing premise and the conclusion hold because `P_n(ψ) ≈ₙ 1` (FAF's `lic_provind_true`,
`thm:provind`). **Degenerate**: an eventually-constant schedule, on which premise and conclusion
coincide (`asympEq_shift_iff_of_eventuallyConst`); like `frontRun_witness`, it inhabits the package
without exercising the exploitation argument — but it rests on nothing open and on no (A). A
non-degenerate exo-market inhabitation of the landing premise is unavailable short of T10.1.
Source: audit r2 fidelity N6; mandate T3.2 (witness)
Kind: N−
Fidelity: exact (hypothesis-satisfiability of `frontRun_exo` at `H := noDemand`; the implication is a reindexing on this instance)
Hyps: (a): the inductor instance is FAF's `LIA_is_logical_inductor` for any `ComputableDeductiveProcess`; `hthm` is the theoremhood of `ψ` -/
theorem frontRun_exo_witness_theorem (DP : DeductiveProcess)
    [IsLogicalInductor (liaHistory DP) DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (ψ : Sentence)
    (hthm : ∃ k, ψ ∈ DP.D k) :
    (∃ B : ℝ, ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) → exoLoss DP noDemand v n ≤ B) ∧
    MachineSentenceCodes (fun _ => ψ) ∧
    MachineRatCodes (fun _ => (1 : ℚ)) ∧
    AsympEq (fun n => exoHistory DP noDemand (n + 1) ψ) (fun _ => ((1 : ℚ) : ℝ)) ∧
    AsympEq (fun n => exoHistory DP noDemand n ψ) (fun _ => ((1 : ℚ) : ℝ)) := by
  have hone : AsympEq (fun n => liaHistory DP n ψ) (fun _ => (1 : ℝ)) :=
    lic_provind_true (liaHistory DP) DP (fun _ => ψ) (MachineSentenceCodes.const ψ)
      (fun _ _ hv => hv.holds_of_mem_stage hthm) hworld
  have h : Tendsto (fun n => liaHistory DP n ψ - 1) atTop (𝓝 0) := hone
  refine ⟨⟨0, fun n v _ => by simp [exoLoss, noDemand]⟩, MachineSentenceCodes.const ψ,
    MachineRatCodes.const 1, ?_, ?_⟩
  · unfold AsympEq
    rw [exoHistory_noDemand]
    have := h.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using this
  · unfold AsympEq
    rw [exoHistory_noDemand]
    simpa using h

/-! ## T6.1 at the utility atom: the opposer, the no-push floor, and T2.3's regime -/

/-- **T6.1 for the source's opposer**: the Occam trader that opposes an upward push on `u` buys
`∼u`; over a cleanroom-free process with a consistent world at every stage (a `u`-world is plausible
at every stage, from freshness), it is bankrupted from the explicit day on provided the pushed price
of `∼u` stays `≥ p + δ` — i.e. the push does not drive `u` above `1 − p − δ`. If the push drives
`P(u) → 1`, the opposer's daily loss may be summable and this theorem is silent (a qualification of
line 113).
Source: line 113 ("a standing Occam position against a persistent push"); audit r1 N1 (fidelity)
Kind: C
Fidelity: exact (T6.1 at `∼u`; the floor on `∼u`'s price is the hypothesis)
Hyps: (a): `hplaus` from freshness (`utilityAtom_both_plausible`) -/
theorem occam_exhausted_opposer_utilityAtom (DP : DeductiveProcess) (hDP : CleanroomFreeProcess DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (c : ℚ) (hc : 0 < c) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (hQ0 : ∀ m, 0 ≤ Q m (∼utilityAtom)) (p δ : ℚ) (hp : 0 ≤ p)
    (hδ : 0 < δ) (N : ℕ) (hpush : ∀ m, N ≤ m → p + δ ≤ Q m (∼utilityAtom)) :
    ∀ n, N + ⌈(b : ℚ) / (c * (p + δ))⌉₊ + 1 ≤ n →
      priorBudgetBreach DP (constBuyer (∼utilityAtom) c) b Q n = true :=
  occam_exhausted_opposer DP utilityAtom c hc b Q hQ0
    (fun m => (utilityAtom_both_plausible DP hDP hworld m).1) p δ hp hδ N hpush

/-- **T6.1's N− inhabitation at the utility atom**: the constant `½` table — no demand, no push —
bankrupts the Occam buyer of `u` over any cleanroom-free process with a consistent world at every
stage. The push enters T6.1 only as a price floor (audit r1, N1 adversarial).
Source: audit r1 N1 (adversarial)
Kind: N−
Fidelity: exact
Hyps: (a) -/
theorem occam_exhausted_half_table_utilityAtom (DP : DeductiveProcess)
    (hDP : CleanroomFreeProcess DP) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (c : ℚ) (hc : 0 < c) (b : ℕ) :
    ∀ n, ⌈(b : ℚ) / (c * (1 / 2))⌉₊ + 1 ≤ n →
      priorBudgetBreach DP (constBuyer utilityAtom c) b (fun _ _ => (1 / 2 : ℚ)) n = true :=
  occam_exhausted_half_table DP utilityAtom c hc b
    (fun m => (utilityAtom_both_plausible DP hDP hworld m).2)

/-- The exo-market is the cast of its own quote table, so the budget lemmas transfer by `rfl`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem exoHistory_eq_castHistory (DP : DeductiveProcess) (H : ExoDemand) :
    exoHistory DP H = castHistory (exoQuote DP H) := rfl

/-- **A landed persistent push has unbounded plausible loss** (audit r1 N2/N4): if the demand
`constBuyer φ c` sees its own market price of `φ` at `≥ p + δ > 0` from day `N` on (the "lands"
hypothesis of T6.1/T10.1) and a `¬φ`-world is plausible at every stage, then for every bound `B`
there is a plausible `(m, v)` with `exoLoss DP (constBuyer φ c) v m > B`. So T2.3
(`noEcExploit_of_boundedLoss`) and T3.2 (`frontRun_exo`) do not apply to the persistent push: the
exploitation form covers finitely-supported or self-financing demands (the N+ `pushOnce`); the
source's central case (line 113) is covered by T2.1 with `Loss` growing, and by T6.1.
Source: line 95 vs line 113; audit r1 N2 (fidelity), N4 (adversarial)
Kind: C
Fidelity: exact
Hyps: (a): `hundec` from freshness at the utility atom; `hpush` is the landing -/
theorem persistent_push_unbounded_loss (DP : DeductiveProcess) (φ : Sentence) (c : ℚ) (hc : 0 < c)
    (hundec : ∀ m, ∃ v : PCWorld, v.ConsistentWith (DP.D m) ∧ ¬ v.Holds φ)
    (hQ0 : ∀ m, 0 ≤ exoQuote DP (constBuyer φ c) m φ) (p δ : ℚ) (hp : 0 ≤ p) (hδ : 0 < δ) (N : ℕ)
    (hpush : ∀ m, N ≤ m → p + δ ≤ exoQuote DP (constBuyer φ c) m φ) :
    ∀ B : ℝ, ∃ (m : ℕ) (v : PCWorld), v.ConsistentWith (DP.D m) ∧
      B < exoLoss DP (constBuyer φ c) v m := by
  intro B
  set Q := exoQuote DP (constBuyer φ c) with hQ
  have hpos : 0 < c * (p + δ) := mul_pos hc (by linarith)
  have hposR : (0 : ℝ) < (c : ℝ) * ((p : ℝ) + δ) := by exact_mod_cast hpos
  obtain ⟨K, hK⟩ := exists_nat_gt (B / ((c : ℝ) * ((p : ℝ) + δ)))
  have hK' : B < (K : ℝ) * ((c : ℝ) * ((p : ℝ) + δ)) := by rwa [div_lt_iff₀ hposR] at hK
  set m := N + K with hm
  obtain ⟨v, hv, hvφ⟩ := hundec m
  refine ⟨m, v, hv, ?_⟩
  unfold exoLoss
  rw [exoHistory_eq_castHistory, constBuyer_netWorth_refuting φ c Q v hvφ m, neg_neg]
  have hsum := sum_price_ge_of_push φ Q hQ0 p δ N hpush m
  have hcard : ((m + 1 - N : ℕ) : ℚ) = (K : ℚ) + 1 := by
    rw [hm, show N + K + 1 - N = K + 1 by omega]
    push_cast
    rfl
  rw [hcard] at hsum
  have hsumR : ((K : ℝ) + 1) * ((p : ℝ) + δ) ≤ ∑ i ∈ Finset.range (m + 1), (Q i φ : ℝ) := by
    exact_mod_cast hsum
  have hcR : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc.le
  calc B < (K : ℝ) * ((c : ℝ) * ((p : ℝ) + δ)) := hK'
    _ ≤ ((K : ℝ) + 1) * ((c : ℝ) * ((p : ℝ) + δ)) := by nlinarith [hposR]
    _ = (c : ℝ) * (((K : ℝ) + 1) * ((p : ℝ) + δ)) := by ring
    _ ≤ (c : ℝ) * ∑ i ∈ Finset.range (m + 1), (Q i φ : ℝ) :=
        mul_le_mul_of_nonneg_left hsumR hcR

/-! ## T11.1 — the two proposals are different objects -/

/-- **T11.1 — skewed prior versus unlearnable constraint.** Under a push on the utility atom that
keeps the price of `∼u` at `≥ p + δ` from day `N` on, the budgeted Occam *opposer* (budget `b`, `c`
shares of `∼u` a day) is silent from the explicit day `N + ⌈b / (c(p+δ))⌉₊ + 1` on, while a
`PushInvariant` market map prices every `u`-sentence under every demand as under no demand, on
every day. The two proposals are different objects; **the second conjunct is the hypothesis `hM`
unfolded** (audit r1 N3), so this is a juxtaposition (kind L), not a theorem with content of its
own. What it does **not** show: that the constraint is achievable over the exo-market (T8.3 /
`pushInvariantOver_compatible`, OPEN), nor that a skewed prior is useless on finite horizons
(before day `M` it opposes the push).
ATTRIBUTION-UNVETTED whether Abram's "prior skewed toward trust" is the budgeted Occam trader.
Source: corr-core-053; audit §3 Q2; mandate T11.1
Kind: L
Fidelity: exact (a conjunction of T6.1's opposer instance and T8.1's definition)
Hyps: (a) as T6.1; `hM` is the constraint by assumption -/
theorem exhausted_vs_invariant (DP : DeductiveProcess) (hDP : CleanroomFreeProcess DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (c : ℚ) (hc : 0 < c) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (hQ0 : ∀ m, 0 ≤ Q m (∼utilityAtom))
    (p δ : ℚ) (hp : 0 ≤ p) (hδ : 0 < δ) (N : ℕ) (hpush : ∀ m, N ≤ m → p + δ ≤ Q m (∼utilityAtom))
    (M : ExoDemand → History) (hM : PushInvariant utilityAtomCode M) :
    (∀ n, N + ⌈(b : ℚ) / (c * (p + δ))⌉₊ + 1 ≤ n →
      (budgetedTrader DP (constBuyer (∼utilityAtom) c) b Q).strat n = ⟨[], by simp⟩) ∧
    (∀ (H : ExoDemand) (n : ℕ) (ψ : Sentence), ¬ AtomFreeSentence utilityAtomCode ψ →
      M H n ψ = M noDemand n ψ) :=
  ⟨fun n hn => BudgeterAt_eq_empty_of_breach DP _ b Q n
    (occam_exhausted_opposer_utilityAtom DP hDP hworld c hc b Q hQ0 p δ hp hδ N hpush n hn), hM⟩

end Cleanroom.Corrigibility.CorrExoTrader
