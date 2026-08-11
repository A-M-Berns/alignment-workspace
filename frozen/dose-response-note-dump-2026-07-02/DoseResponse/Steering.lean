/-
  Kernel-checked core of THEOREM T2 (`dose-response.md` §6.2–6.3): the
  steered coupled system — dose-graded destinations (a), exact detection (d),
  and non-attribution (e) — assembled from Lemma A (`IndependentAtom`), the
  destination audit (`DestinationAudit`), and named LI citations.

  What is proved here:
  • `testimonyAverage_eq` / `jump_target_eq` — the §6.3 (∗) arithmetic:
    the testimony average is affine in the realized dose, and the critical-period
    response sends it to  ½ + s·p̂  with s := γ(v − ½).  `jump_target_eq` is
    simultaneously the heart of (e): the content-steered target Φ(m_{N*}) and the
    content-blind target ½ + s·p̂ are equal AS NUMBERS on every ledger.
  • `armMarginal` — M(γ, N*)'s marginal for u: ½ during the critical period, one
    jump, settled disposition.  `armMarginal_bounds` discharges Lemma A's
    interiority hypotheses at η = (1−γ)/2 (positive for γ < 1); `armMarginal_settled`
    discharges its finitely-many-jumps hypothesis.
  • `dose_graded_destination` — **T2(a)**: the arm's u-price converges to
    ½ + s·p̂ᵢ, affine in realized dose with slope the steering magnitude.  Named
    inputs: Lemma A's ⊤/⊥ price convergence ([LI 4.1.1] + [LI 4.1.2]).  The
    pairwise-distinctness clause is the N*-separation hypothesis of D1, carried
    downstream as `p̂ᵢ ≠ p̂ⱼ`.
  • `steered_arm_compliant_and_graded` — T2(a) + T2(b)'s per-arm clause COMPOSED
    about one object: the Lemma-A extension at `armMarginal` both satisfies the
    criterion (interiority/settledness discharged) and converges to ½ + s·p̂.
  • `cross_arm_audit_fires` — **T2(d)**: with the arms' expectation streams
    converging to their destinations (provenance: (a) + the [LI 4.8.6] indicator
    transfer, named hypotheses `hi`/`hj`), the uniform Cesàro statistic converges
    to s(p̂ᵢ − p̂ⱼ) ≠ 0: detection exact and permanent.
  • `run_congr` / `non_attribution` — **T2(e)**: a coupled-system day recursion
    driven by a jump-target formula; two systems whose target formulas agree
    pointwise on states produce bit-for-bit identical records (finite induction),
    and the M vs M̃ targets do agree pointwise (`jump_target_eq`) — so no statistic
    of the joint record attributes steering to A rather than exposure-sensitivity
    to H.  (As the note's (e) states: the targets agree on ALL states, not just
    the realized trajectory.)

  Not formalized, carried as citations (declared scope): T2(b)'s per-arm criterion
  compliance is Lemma A per arm (`extension_preserves_criterion`) plus [LI 4.8.10]
  for the quote stream; T2(c) is the note's Lemma 4.3 = [LI 4.6.1] + [LI Cor 3.6.3]
  read as a definition (the steered A_v IS an inductor); the calibration washout
  backing T2(b)/(T2.1) is `DoseAudit.finite_prefix_washout`.

  No `sorry`; axiom audit at the end.
-/
import DoseResponse.DestinationAudit
import DoseResponse.IndependentAtom

open Filter Topology

namespace Steering

/-- The critical-period response Φ(m) := ½ + γ(m − ½) of §6.2 (interior for γ < 1). -/
noncomputable def response (γ m : ℝ) : ℝ := 1/2 + γ * (m - 1/2)

/-- The arm's realized dose p̂ over the critical period [0, N*) (D1). -/
noncomputable def realizedDose (c : ℕ → ℝ) (Nstar : ℕ) : ℝ :=
  (∑ j ∈ Finset.range Nstar, c j) / Nstar

/-- The testimony average m_{N*} of §6.2: the received quote `v` on exposed days,
    the null value ½ on blinded days — no testimony, no push. -/
noncomputable def testimonyAverage (c : ℕ → ℝ) (v : ℝ) (Nstar : ℕ) : ℝ :=
  (∑ j ∈ Finset.range Nstar, (c j * v + (1 - c j) * (1/2))) / Nstar

/-- The testimony average is affine in the realized dose: m_{N*} = ½ + (v − ½)·p̂.
    (A termwise ring identity — it needs no coin hypothesis at all.) -/
theorem testimonyAverage_eq (c : ℕ → ℝ) (v : ℝ) (Nstar : ℕ) (hN : 0 < Nstar) :
    testimonyAverage c v Nstar = 1/2 + (v - 1/2) * realizedDose c Nstar := by
  have hN' : (Nstar : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  unfold testimonyAverage realizedDose
  have h : ∑ j ∈ Finset.range Nstar, (c j * v + (1 - c j) * (1/2))
      = (Nstar : ℝ) * (1/2) + (v - 1/2) * ∑ j ∈ Finset.range Nstar, c j := by
    calc ∑ j ∈ Finset.range Nstar, (c j * v + (1 - c j) * (1/2))
        = ∑ j ∈ Finset.range Nstar, ((1:ℝ)/2 + (v - 1/2) * c j) :=
          Finset.sum_congr rfl fun j _ => by ring
      _ = (Nstar : ℝ) * (1/2) + (v - 1/2) * ∑ j ∈ Finset.range Nstar, c j := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, ← Finset.mul_sum]
  rw [h]
  field_simp

/-- **The jump-target identity** — the arithmetic heart of T2(a) *and* T2(e):
    Φ(m_{N*}) = ½ + s·p̂ with s := γ(v − ½).  The content-steered target and the
    content-blind exposure-sensitive target are equal as numbers on every ledger. -/
theorem jump_target_eq (γ : ℝ) (c : ℕ → ℝ) (v : ℝ) (Nstar : ℕ) (hN : 0 < Nstar) :
    response γ (testimonyAverage c v Nstar)
      = 1/2 + (γ * (v - 1/2)) * realizedDose c Nstar := by
  rw [response, testimonyAverage_eq c v Nstar hN]
  ring

/-- M(γ, N*)'s marginal for the atom (§6.2): ½ through the critical period, then the
    settled disposition Φ(m_{N*}).  One jump — Lemma A's finitely-many-jumps case. -/
noncomputable def armMarginal (γ : ℝ) (c : ℕ → ℝ) (v : ℝ) (Nstar : ℕ) (n : ℕ) : ℝ :=
  if n < Nstar then 1/2 else response γ (testimonyAverage c v Nstar)

/-- The marginal is settled from N* on (discharges Lemma A's `hqc`). -/
theorem armMarginal_settled (γ : ℝ) (c : ℕ → ℝ) (v : ℝ) (Nstar n : ℕ) (hn : Nstar ≤ n) :
    armMarginal γ c v Nstar n = response γ (testimonyAverage c v Nstar) := by
  unfold armMarginal
  exact if_neg (not_lt.2 hn)

/-- Interiority (discharges Lemma A's `hq1`/`hq2` at η := (1−γ)/2, which is positive
    exactly when γ < 1): for coins and quote in [0,1], the marginal stays in
    [(1−γ)/2, 1 − (1−γ)/2].  Sanity per the note's Remark (1): Non-Dogmatism forces
    an interior limit for the never-decided u, and the response's range respects it. -/
theorem armMarginal_bounds (γ : ℝ) (c : ℕ → ℝ) (v : ℝ) (Nstar n : ℕ)
    (hγ0 : 0 ≤ γ) (hN : 0 < Nstar)
    (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (1 - γ)/2 ≤ armMarginal γ c v Nstar n ∧ armMarginal γ c v Nstar n ≤ 1 - (1 - γ)/2 := by
  have hNpos : (0:ℝ) < Nstar := by exact_mod_cast hN
  have hdose0 : 0 ≤ realizedDose c Nstar :=
    div_nonneg (Finset.sum_nonneg fun j _ => hc0 j) hNpos.le
  have hdose1 : realizedDose c Nstar ≤ 1 := by
    unfold realizedDose
    rw [div_le_one hNpos]
    calc ∑ j ∈ Finset.range Nstar, c j
        ≤ ∑ j ∈ Finset.range Nstar, (1:ℝ) := Finset.sum_le_sum fun j _ => hc1 j
      _ = Nstar := by simp
  -- the testimony average lands in [0,1]: m = (1−p̂)/2 + v·p̂ termwise
  have hm := testimonyAverage_eq c v Nstar hN
  have hm0 : 0 ≤ testimonyAverage c v Nstar := by
    rw [hm]
    nlinarith [mul_nonneg hv0 hdose0, mul_nonneg (sub_nonneg.2 hdose1) (by norm_num : (0:ℝ) ≤ 1/2)]
  have hm1 : testimonyAverage c v Nstar ≤ 1 := by
    rw [hm]
    nlinarith [mul_nonneg (sub_nonneg.2 hv1) hdose0,
      mul_nonneg (sub_nonneg.2 hdose1) (by norm_num : (0:ℝ) ≤ 1/2)]
  unfold armMarginal
  split_ifs with h
  · constructor <;> linarith
  · unfold response
    constructor
    · nlinarith [mul_nonneg hγ0 hm0]
    · nlinarith [mul_nonneg hγ0 (sub_nonneg.2 hm1)]

/-- **T2(a) — dose-graded destinations.**  The arm's price on the atom converges to
    ½ + s·p̂, affine in the realized dose with slope the steering magnitude
    s = γ(v − ½).  Named inputs are Lemma A's: base ⊤/⊥ prices converge to their
    values ([LI 4.1.1] + [LI 4.1.2]).  Distinctness across arms is D1's
    N*-separation, consumed as `p̂ᵢ ≠ p̂ⱼ` in T2(d) below. -/
theorem dose_graded_destination {Φb Φ : Type*} (E : IndependentAtom.AtomExtension Φb Φ)
    (P : ℕ → Φb → ℝ) (γ : ℝ) (c : ℕ → ℝ) (v : ℝ) (Nstar : ℕ) (hN : 0 < Nstar)
    (htop : Tendsto (fun n => P n E.top) atTop (𝓝 1))
    (hbot : Tendsto (fun n => P n E.bot) atTop (𝓝 0)) :
    Tendsto (fun n => IndependentAtom.extPrice E P (armMarginal γ c v Nstar) n E.u)
      atTop (𝓝 (1/2 + (γ * (v - 1/2)) * realizedDose c Nstar)) := by
  rw [← jump_target_eq γ c v Nstar hN]
  exact IndependentAtom.atom_price_tendsto E P (armMarginal γ c v Nstar)
    (response γ (testimonyAverage c v Nstar)) Nstar
    (fun n hn => armMarginal_settled γ c v Nstar n hn) htop hbot

/-- **The steered arm, composed** — T2(a) and T2(b)'s per-arm clause about ONE
    object.  The Lemma-A extension of a base market by the critical-period marginal
    `armMarginal γ c v N*` — the arm `M(γ, N*)` of §6.2 — simultaneously
    (i) satisfies the no-exploitation criterion (Lemma A, its interiority and
    settledness hypotheses discharged by `armMarginal_bounds` at η = (1−γ)/2 and
    `armMarginal_settled`), and (ii) has its atom price converge to the dose-graded
    destination ½ + s·p̂.  Forming the conjunction pins both claims to the same
    definable object.  Named inputs are exactly Lemma A's (trader closure
    [LI 3.4.3–3.4.5], base LIC [LI 3.5.1]) and T2(a)'s (⊤/⊥ price convergence,
    [LI 4.1.1] + [LI 4.1.2]). -/
theorem steered_arm_compliant_and_graded {Φb Φ : Type*}
    (E : IndependentAtom.AtomExtension Φb Φ) {𝒲 : Type*} (ind : 𝒲 → Φb → ℝ)
    (P : ℕ → Φb → ℝ) (γ : ℝ) (c : ℕ → ℝ) (v : ℝ) (Nstar : ℕ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hN : 0 < Nstar)
    (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (PC : ℕ → Set 𝒲)
    (𝒞b : Set (ℕ → Φb →₀ ℝ)) (𝒞e : Set (ℕ → Φ →₀ ℝ))
    (hmirrorTop : ∀ T ∈ 𝒞e, IndependentAtom.mirrorTop E T ∈ 𝒞b)
    (hmirrorBot : ∀ T ∈ 𝒞e, IndependentAtom.mirrorBot E T ∈ 𝒞b)
    (hcombo : ∀ T₁ ∈ 𝒞b, ∀ T₂ ∈ 𝒞b,
      IndependentAtom.combo (response γ (testimonyAverage c v Nstar)) T₁ T₂ ∈ 𝒞b)
    (hLIC : ∀ T ∈ 𝒞b, ¬ IndependentAtom.Exploits P PC ind T)
    (htop : Tendsto (fun n => P n E.top) atTop (𝓝 1))
    (hbot : Tendsto (fun n => P n E.bot) atTop (𝓝 0)) :
    (∀ T ∈ 𝒞e, ¬ IndependentAtom.Exploits
        (IndependentAtom.extPrice E P (armMarginal γ c v Nstar))
        (IndependentAtom.extPC PC) (IndependentAtom.extInd E ind) T) ∧
      Tendsto (fun n => IndependentAtom.extPrice E P (armMarginal γ c v Nstar) n E.u)
        atTop (𝓝 (1/2 + (γ * (v - 1/2)) * realizedDose c Nstar)) := by
  constructor
  · exact IndependentAtom.extension_preserves_criterion E ind P
      (armMarginal γ c v Nstar) ((1 - γ)/2)
      (response γ (testimonyAverage c v Nstar)) Nstar
      (by linarith)
      (fun n => (armMarginal_bounds γ c v Nstar n hγ0 hN hc0 hc1 hv0 hv1).1)
      (fun n => (armMarginal_bounds γ c v Nstar n hγ0 hN hc0 hc1 hv0 hv1).2)
      (fun n hn => armMarginal_settled γ c v Nstar n hn)
      PC 𝒞b 𝒞e hmirrorTop hmirrorBot hcombo hLIC
  · exact dose_graded_destination E P γ c v Nstar hN htop hbot

/-- **T2(d) — the cross-arm audit fires.**  With the two arms' expectation streams
    converging to their dose-graded destinations (named hypotheses; provenance:
    T2(a) plus the indicator transfer [LI 4.8.6]) and N*-separated realized doses,
    the uniform Cesàro statistic converges to s(p̂ᵢ − p̂ⱼ) ≠ 0: detection is exact
    and permanent (`DoseAudit.audit_complete` — and by `DoseAudit.audit_exact`,
    the audit can converge to no other value). -/
theorem cross_arm_audit_fires (Ei Ej : ℕ → ℝ) (s pi pj : ℝ) (hs : s ≠ 0) (hp : pi ≠ pj)
    (hi : Tendsto Ei atTop (𝓝 (1/2 + s * pi)))
    (hj : Tendsto Ej atTop (𝓝 (1/2 + s * pj))) :
    Tendsto (DoseAudit.cesaroGap Ei Ej) atTop (𝓝 (s * (pi - pj)))
      ∧ s * (pi - pj) ≠ 0 := by
  constructor
  · have h := DoseAudit.audit_complete Ei Ej _ _ hi hj
    convert h using 2
    ring
  · exact mul_ne_zero hs (sub_ne_zero.2 hp)

/- ==================================================================================
   T2(e) — non-attribution.
   ================================================================================== -/

/-- A coupled-system day recursion (§6.3(e)/D2, abstracted): the state — the joint
    record of all arms' ledgers — is updated each day by `step` from the day index,
    the current state, and the day's jump-target value.  Everything the two systems
    share (base construction, coins, quotes, routing) lives inside `step`; their one
    point of difference is the `target` formula. -/
def run {State : Type*} (step : ℕ → State → ℝ → State) (target : State → ℝ)
    (init : State) : ℕ → State
  | 0 => init
  | n + 1 =>
      step n (run step target init n) (target (run step target init n))

/-- **T2(e), the mechanical induction**: two systems with the same day recursion whose
    target formulas agree pointwise on states produce bit-for-bit identical records. -/
theorem run_congr {State : Type*} (step : ℕ → State → ℝ → State)
    (target₁ target₂ : State → ℝ) (init : State)
    (h : ∀ st, target₁ st = target₂ st) :
    ∀ n, run step target₁ init n = run step target₂ init n
  | 0 => rfl
  | n + 1 => by
      rw [run, run, run_congr step target₁ target₂ init h n, h]

/-- **T2(e) — non-attribution.**  The content-steered system (jump target
    Φ(m_{N*}(ledger))) and the content-blind exposure-sensitive system (jump target
    ½ + s·p̂(ledger)) produce the bit-for-bit identical joint record, for every
    day recursion `step`, initial record, and ledger-readout `coins`.  Hence no
    statistic of the joint record — the auditor's entire evidence — separates
    content-steering by A from content-blind exposure-sensitivity in H.  (As the
    note's (e) states: the targets agree on all states, not merely along the
    realized trajectory.) -/
theorem non_attribution {State : Type*} (step : ℕ → State → ℝ → State) (init : State)
    (coins : State → ℕ → ℝ) (γ v : ℝ) (Nstar : ℕ) (hN : 0 < Nstar) :
    ∀ n, run step (fun st => response γ (testimonyAverage (coins st) v Nstar)) init n
      = run step (fun st => 1/2 + (γ * (v - 1/2)) * realizedDose (coins st) Nstar) init n :=
  run_congr step _ _ init (fun st => jump_target_eq γ (coins st) v Nstar hN)

end Steering

-- Axiom audit: each must rest on ONLY [propext, Classical.choice, Quot.sound] (no `sorryAx`).
#print axioms Steering.testimonyAverage_eq
#print axioms Steering.jump_target_eq
#print axioms Steering.armMarginal_settled
#print axioms Steering.armMarginal_bounds
#print axioms Steering.dose_graded_destination
#print axioms Steering.steered_arm_compliant_and_graded
#print axioms Steering.cross_arm_audit_fires
#print axioms Steering.run_congr
#print axioms Steering.non_attribution
