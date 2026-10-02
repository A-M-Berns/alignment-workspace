import Cleanroom.Corrigibility.CorrChannelVoi.Identity

/-!
# `corr-channel-voi` — Consent: D6, the scan decision (T5) and asking before scanning (T6)

**D6.** The consent-augmented world `World × Consent`, prior the product of `twoPoint ε` and
`q` on non-consent, stakes `X(w, n) = twoValue c h w`, the sunk harm `−d·𝟙[n = nc]` added to
every second action under the scan action only, the scan reading the `World` coordinate only.

**T5.** The load-bearing bookkeeping: `E[V | scan k'] − E[V | no scan] = VOI(k') − VOI(button) − q·d`
(the harm is sunk: `bayesValue` of a menu shifted by a constant shifts by its expectation;
a channel reading one coordinate has the marginal's value). Scans iff `q·d < VOI(k') − VOI(button)`;
compliance on the augmented model is compliance on `twoState`, for all `q, d`; `εh ≤ q·d`
suffices for never scanning (T3); exact for the perfect scan (T2).

**T6.** The ask model *is* `twoState q α_N β_N VOI (d − VOI)`; heeded — desideratum 1 at the
ask model, `askModel_D1At_iff` — iff `(1−q)α_N VOI ≤ qβ_N(d − VOI)` (`corr-three-step`'s
base-rate inequality); `α_N = 0` heeds at every `q > 0` and asks iff
`q(1−β_N)(d − VOI) < (1−q)VOI` — on the scan region `q·d < VOI` always, near `q = 1` not
(finding F-10: the source's "asks at every `q > 0`" is refuted as stated); below `VOI ≤ d`
the agent scans regardless.
-/

namespace Cleanroom.Corrigibility.CorrChannelVoi

open Finset hiding expect
open FactoredSpaces
open Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Trust.TtFiniteFrames
open Cleanroom.Found.CorrThreeStep
open Cleanroom.Found.CorrThreeStep.ThreeStep

noncomputable section

set_option linter.unusedSectionVars false

variable {W S T : Type} [Fintype W] [Fintype S] [Fintype T]

/-! ## Products of FAF distributions; sunk costs; marginal channels -/

/-- **The binary product of two FAF distributions** `(μ ⊗ ν)(w, t) = μ w · ν t` (FAF's
`Distr.prod` is over dependent families `Pt Ω`; this is its binary case — API request).
Source: none: infrastructure ([[corr-channel-voi-mandate]] D6, "the explicit product")
Kind: D
Fidelity: exact -/
def distrProd (μ : Distr W) (ν : Distr T) : Distr (W × T) where
  mass p := μ.mass p.1 * ν.mass p.2
  nonneg p := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ν.sum_eq_one, mul_one]
    exact μ.sum_eq_one

/-- Mass of a product distribution. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem distrProd_mass (μ : Distr W) (ν : Distr T) (p : W × T) :
    (distrProd μ ν).mass p = μ.mass p.1 * ν.mass p.2 := rfl

/-- The expectation of a function of the first coordinate under a product is its expectation
under the marginal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem expect_distrProd_fst (μ : Distr W) (ν : Distr T) (X : W → ℝ) :
    expect (distrProd μ ν) (fun p => X p.1) = expect μ X := by
  unfold expect
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [distrProd_mass]
  rw [show ∑ t, μ.mass w * ν.mass t * X w = μ.mass w * X w * ∑ t, ν.mass t by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring]
  rw [ν.sum_eq_one, mul_one]

/-- A channel reading only the first coordinate has, under a product prior and first-coordinate
stakes, the signal gains of the marginal problem.
Source: none: infrastructure ([[corr-channel-voi-mandate]] D6, "the scan reads the `World` coordinate only")
Kind: L
Fidelity: n/a -/
theorem signalGain_comap_fst (μ : Distr W) (ν : Distr T) (k : Experiment W S) (X : W → ℝ) (s : S) :
    signalGain (distrProd μ ν) (expComap Prod.fst k) (fun p => X p.1) s = signalGain μ k X s := by
  unfold signalGain
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [distrProd_mass, expComap_k]
  rw [show ∑ t, μ.mass w * ν.mass t * k.k w s * X w = μ.mass w * k.k w s * X w * ∑ t, ν.mass t by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring]
  rw [ν.sum_eq_one, mul_one]

/-- **Marginalisation**: `𝒱_{μ⊗ν}(k ∘ fst)(X ∘ fst) = 𝒱_μ(k)(X)`.
Source: none: infrastructure (T5's bookkeeping)
Kind: L
Fidelity: n/a -/
theorem sensorValue_comap_fst [DecidableEq S] (μ : Distr W) (ν : Distr T) (k : Experiment W S)
    (X : W → ℝ) :
    sensorValue (distrProd μ ν) (expComap Prod.fst k) (fun p => X p.1) = sensorValue μ k X := by
  rw [sensorValue_eq_sum_max, sensorValue_eq_sum_max]
  exact Finset.sum_congr rfl fun s _ => by rw [signalGain_comap_fst]

/-- A rule's value on a menu shifted by a world-dependent constant shifts by its expectation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ruleValue_sub_const [DecidableEq S] (μ : W → ℝ) (k : Experiment W S) {n : ℕ}
    (u : Fin (n + 1) → W → ℝ) (D : W → ℝ) (δ : S → Fin (n + 1)) :
    ruleValue μ k (fun j w => u j w - D w) δ = ruleValue μ k u δ - ∑ w, μ w * D w := by
  unfold ruleValue
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.sum_mul, (k.k_mem w).2, one_mul]

/-- **Sunk costs**: `bayesValue μ k (u − D) = bayesValue μ k u − E_μ[D]` — a cost paid in every
option and every signal shifts the Bayes value by its expectation and changes no decision.
Source: [[corr-channel-voi-mandate]] T5 ("the harm is sunk"); substitution.md R4 item 16
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem bayesValue_sub_const [DecidableEq S] (μ : W → ℝ) (k : Experiment W S) {n : ℕ}
    (u : Fin (n + 1) → W → ℝ) (D : W → ℝ) :
    bayesValue μ k (fun j w => u j w - D w) = bayesValue μ k u - ∑ w, μ w * D w := by
  apply le_antisymm
  · apply bayesValue_le
    intro δ
    rw [ruleValue_sub_const]
    linarith [ruleValue_le_bayesValue μ k u δ]
  · obtain ⟨δ, -, hδ⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := S → Fin (n + 1)))
      (fun δ => ruleValue μ k u δ)
    have h1 : bayesValue μ k u = ruleValue μ k u δ := hδ
    have h2 := ruleValue_le_bayesValue μ k (fun j w => u j w - D w) δ
    rw [ruleValue_sub_const, ← h1] at h2
    exact h2

/-! ## D6. The consent-augmented world -/

/-- The consent latent: the overseers consent to the scan, or do not.
Source: substitution.md R4 item 16 (`N ∈ {consent, non-consent}`)
Kind: D
Fidelity: exact -/
inductive Consent
  | yes
  | nc
  deriving DecidableEq

/-- `Consent` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype Consent := ⟨{Consent.yes, Consent.nc}, fun x => by cases x <;> simp⟩

/-- Sums over `Consent`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem Consent.sum_eq (f : Consent → ℝ) : ∑ n, f n = f .yes + f .nc := by
  rw [show (univ : Finset Consent) = {Consent.yes, Consent.nc} from rfl, Finset.sum_pair (by decide)]

/-- The value posterior's weight on non-consent: `P(nc) = q`.
Source: substitution.md R4 item 16
Kind: D
Fidelity: exact -/
def consentPrior (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) : Distr Consent where
  mass n := match n with
    | .yes => 1 - q
    | .nc => q
  nonneg n := by cases n <;> simp <;> linarith [hq.1, hq.2]
  sum_eq_one := by rw [Consent.sum_eq]; simp

/-- The sunk harm `d·𝟙[n = nc]`.
Source: substitution.md R4 item 16 (`−d·𝟙[N = nc]`)
Kind: D
Fidelity: exact -/
def sunkHarm (d : ℝ) : World × Consent → ℝ := fun p => if p.2 = .nc then d else 0

/-- The expectation of the sunk harm under the augmented prior is `q·d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem expect_sunkHarm (ε q d : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ∑ p, (distrProd (twoPoint ε hε) (consentPrior q hq)).mass p * sunkHarm d p = q * d := by
  rw [Fintype.sum_prod_type]
  simp only [World.sum_eq, Consent.sum_eq, distrProd_mass, twoPoint_right, twoPoint_wrong,
    consentPrior, sunkHarm]
  simp
  ring

section Scan

variable (ε q α β c h d : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
  (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- **D6. The value of scanning with channel `k'`** (reading the `World` coordinate only), the
harm sunk in every option: `bayesValue` under the augmented prior of the two-option menu shifted
by `−d·𝟙[nc]`.
Source: substitution.md R4 item 16
Kind: D
Fidelity: exact -/
def scanValue (k' : Experiment World S) [DecidableEq S] : ℝ :=
  bayesValue (distrProd (twoPoint ε hε) (consentPrior q hq)).mass (expComap Prod.fst k')
    (fun j p => twoMenu (fun w => twoValue c h .cont w) j p.1 - sunkHarm d p)

/-- **D6. The value of not scanning**: the button, on the augmented world, no harm.
Source: substitution.md R4 item 16
Kind: D
Fidelity: exact -/
def noScanValue : ℝ :=
  sensorValue (distrProd (twoPoint ε hε) (consentPrior q hq))
    (expComap Prod.fst (twoButton α β hα hβ)) (fun p => twoValue c h .cont p.1)

/-- **T5, the load-bearing identity (load-bearing 4)**:
`E[V | scan k'] − E[V | no scan] = VOI(k') − VOI(button) − q·d` — the sunk harm shifts the scan's
value by `q·d`, the channel on the product world is worth what it is worth on `World`, and the
prior maxima cancel.
Source: substitution.md R4 item 16 (the displayed equation); [[corr-wf14-inventory]] 040
Kind: C (`bayesValue_sub_const` — where the `P` lives — + `sensorValue_comap_fst` + `expect_sunkHarm` + `ring`; regraded from P in audit r2)
Fidelity: exact
Hyps: (a) none -/
theorem scanValue_sub_noScanValue (k' : Experiment World S) [DecidableEq S] :
    scanValue ε q c h d hε hq k' - noScanValue ε q α β c h hε hq hα hβ =
      voiSensor (twoPoint ε hε) k' (twoValue c h .cont) -
        voiSensor (twoPoint ε hε) (twoButton α β hα hβ) (twoValue c h .cont) - q * d := by
  unfold scanValue noScanValue
  rw [show (fun j (p : World × Consent) => twoMenu (fun w => twoValue c h .cont w) j p.1 - sunkHarm d p) =
      (fun j p => twoMenu (fun p : World × Consent => twoValue c h .cont p.1) j p - sunkHarm d p) by
    funext j p; fin_cases j <;> rfl]
  rw [bayesValue_sub_const, expect_sunkHarm]
  change sensorValue (distrProd (twoPoint ε hε) (consentPrior q hq)) (expComap Prod.fst k')
      (fun p => twoValue c h .cont p.1) - q * d - _ = _
  rw [sensorValue_comap_fst, sensorValue_comap_fst]
  unfold voiSensor
  ring

/-- **T5: scans iff `q·d < VOI(k') − VOI(button)`.**
Source: substitution.md R4 item 16 ("the agent scans iff `q d < VOI_ε(scan)`"); [[corr-wf14-inventory]] 040
Kind: L
Fidelity: exact -/
theorem scans_iff (k' : Experiment World S) [DecidableEq S] :
    noScanValue ε q α β c h hε hq hα hβ < scanValue ε q c h d hε hq k' ↔
      q * d < voiSensor (twoPoint ε hε) k' (twoValue c h .cont) -
        voiSensor (twoPoint ε hε) (twoButton α β hα hβ) (twoValue c h .cont) := by
  have := scanValue_sub_noScanValue ε q α β c h d hε hq hα hβ k'
  constructor <;> intro H <;> linarith

/-- **T5, sufficient condition for never scanning**: if `εh ≤ q·d` then no channel `k'` whatever
is worth the scan (`c, h ≥ 0`; by T3 every channel is worth at most `min(εh, (1−ε)c) ≤ εh`).
Source: substitution.md R4 item 18; [[corr-wf14-inventory]] 040 (the source's `[conjectured]` general form `εh ≤ q·d` is this sufficient condition; only it is a theorem)
Kind: C (`scans_iff` + `voiSensor_le_vopi` + `twoState_vopi` + `voiSensor_nonneg` + `linarith`; regraded from P in audit r2)
Fidelity: exact
Hyps: (a) none beyond `c, h ≥ 0` -/
theorem never_scans_of_le (hc : 0 ≤ c) (hh : 0 ≤ h) (hle : ε * h ≤ q * d)
    (k' : Experiment World S) [DecidableEq S] :
    ¬ noScanValue ε q α β c h hε hq hα hβ < scanValue ε q c h d hε hq k' := by
  rw [scans_iff, not_lt]
  have h1 := voiSensor_le_vopi (twoPoint ε hε) k' (twoValue c h .cont)
  rw [twoState_vopi ε c h hε hc hh] at h1
  have h2 := voiSensor_nonneg (twoPoint ε hε) (twoButton α β hα hβ) (twoValue c h .cont)
  have h3 : min (ε * h) ((1 - ε) * c) ≤ ε * h := min_le_left _ _
  linarith

/-- **T5, exact for the perfect scan**: scans iff `q·d < min(εh, (1−ε)c) − VOI(button)`.
Source: substitution.md R4 item 18 ("for a perfect scan the exact condition is …")
Kind: C (T2 + T5)
Fidelity: exact -/
theorem scans_perfect_iff (hc : 0 ≤ c) (hh : 0 ≤ h) :
    noScanValue ε q α β c h hε hq hα hβ < scanValue ε q c h d hε hq perfectExp ↔
      q * d < min (ε * h) ((1 - ε) * c) -
        voiSensor (twoPoint ε hε) (twoButton α β hα hβ) (twoValue c h .cont) := by
  rw [scans_iff, voiSensor_perfect, twoState_vopi ε c h hε hc hh]

/-- **D6. The augmented `ThreeStep`** `consentModel : ThreeStep (World × Consent) Bool TwoAct`:
action `false` = no scan, `true` = scan; the button reads the world under both; the scan's sunk
harm enters `V` under `true` only. (The scan's channel lives in `scanValue`; this structure is
what the compliance question is asked of.) **Note the two models of "scan":** here action `true`
*keeps* the button `(α, β)` and pays the harm — the compliance claim T5 (`consentModel_belowThreshold_iff`)
is about the button's inequality under either action; in `scanValue` the button is *replaced* by
the channel `k'` — the scan *decision* (`scans_iff`) is asked of that. Both follow the source
(item 17 is about the button's inequality, item 16 about the decision).
Source: substitution.md R4 item 16
Kind: D
Fidelity: exact -/
def consentModel : ThreeStep (World × Consent) Bool TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => distrProd (twoPoint ε hε) (consentPrior q hq)
  press := fun _ p => twoPress α β p.1
  press_nonneg := fun _ p => by cases p.1 <;> simp [twoPress] <;> linarith [hα.1, hβ.1]
  press_le_one := fun _ p => by cases p.1 <;> simp [twoPress] <;> linarith [hα.2, hβ.2]
  V := fun a _ b p => twoValue c h b p.1 - if a then sunkHarm d p else 0

/-- **T5: compliance contains neither `q` nor `d`.** On the augmented model, under either action,
the below-threshold inequality on `X_o` holds iff it holds on `twoState ε α β c h` — for every
`q` and `d` (the harm cancels in `X_o`; the consent coordinate marginalises out).
Source: substitution.md R4 item 17 ("compliance contains neither `q` nor `d`"); [[corr-wf14-inventory]] 040
Kind: L
Fidelity: exact -/
theorem consentModel_belowThreshold_iff (a : Bool) (o : Obs) :
    (consentModel ε q α β c h d hε hq hα hβ).belowThresholdIneq a
        ((consentModel ε q α β c h d hε hq hα hβ).Xo a o .cont .stop) ↔
      (twoState ε α β c h hε hα hβ).belowThresholdIneq ()
        ((twoState ε α β c h hε hα hβ).Xo () o .cont .stop) := by
  unfold belowThresholdIneq
  have e : (consentModel ε q α β c h d hε hq hα hβ).obsExpect a .press
      ((consentModel ε q α β c h d hε hq hα hβ).Xo a o .cont .stop) =
      (twoState ε α β c h hε hα hβ).obsExpect () .press
        ((twoState ε α β c h hε hα hβ).Xo () o .cont .stop) := by
    simp only [obsExpect, obsWeight_press, Xo, consentModel, twoState, Fintype.sum_prod_type,
      World.sum_eq, Consent.sum_eq, distrProd_mass, twoPoint_right, twoPoint_wrong, consentPrior,
      twoValue, twoPress, sunkHarm]
    cases a <;> simp <;> ring
  rw [e]

end Scan

/-! ## T6. Asking before scanning -/

section Ask

variable (q αN βN VOI d : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (hαN : αN ∈ Set.Icc (0 : ℝ) 1)
  (hβN : βN ∈ Set.Icc (0 : ℝ) 1)

/-- **The ask model** *is* `twoState q α_N β_N VOI (d − VOI)`: `World.right` = the overseers
consent, `World.wrong` = they do not (`ε ↦ q`); the press is their objection to the announced
scan, with `P(Pr_N | consent) = α_N`, `P(Pr_N | nc) = β_N`; `cont` = scan, `stop` = don't;
`c ↦ VOI` (forgone by not scanning when they consent), `h ↦ d − VOI` (the net harm of scanning
when they do not). Hypotheses `0 ≤ VOI ≤ d` where the roles need them. No new structure.
Source: substitution.md R5 item 25; [[corr-wf14-inventory]] 041
Kind: D
Fidelity: exact (an instance, as the mandate says) -/
def askModel : ThreeStep World Unit TwoAct := twoState q αN βN VOI (d - VOI) hq hαN hβN

/-- The ask model's two-option variable on the consent coordinate is `twoValue VOI (d − VOI)`.
Source: [[corr-channel-voi-mandate]] T6 (the bridge)
Kind: L
Fidelity: exact -/
theorem askModel_Xo (o : Obs) :
    (askModel q αN βN VOI d hq hαN hβN).Xo () o .cont .stop = twoValue VOI (d - VOI) .cont :=
  twoState_Xo_eq q αN βN VOI (d - VOI) hq hαN hβN o

/-- **T6 (load-bearing 4): a press about the scan is heeded iff `(1−q)·α_N·VOI ≤ q·β_N·(d − VOI)`**
— `corr-three-step`'s base-rate inequality at the ask model, in product form.
Source: substitution.md R5 item 25 (the displayed inequality); [[corr-wf14-inventory]] 041
Kind: C (`twoState_deltaMinus_nonneg_iff` at the instance)
Fidelity: exact -/
theorem askModel_heeded_iff :
    0 ≤ (askModel q αN βN VOI d hq hαN hβN).deltaMinus () .cont .stop ↔
      (1 - q) * αN * VOI ≤ q * βN * (d - VOI) :=
  twoState_deltaMinus_nonneg_iff q αN βN VOI (d - VOI) hq hαN hβN

/-- **T6 (load-bearing 4): "heeded" is literally desideratum 1 at the ask model.** `D1At ()` on
the ask model ⟺ `(1−q)·α_N·VOI ≤ q·β_N·(d − VOI)` — so the word "heeded" in the ledger's T6 rows
is `corr-three-step`'s `D1At`, not merely `0 ≤ Δ₋`. Composition of `d1At_iff_deltaMinus_nonneg`
with the two-state part-maximiser lemmas and `askModel_heeded_iff` (audit r2 fidelity N4; its
probe `probe_askModel_D1At_iff`, here made a library theorem).
Source: substitution.md R5 item 25 (the displayed inequality, read as desideratum 1); [[corr-wf14-inventory]] 041
Kind: C (`d1At_iff_deltaMinus_nonneg` + `twoState_cont/stop_partBest` + `twoState_deltaMinus_nonneg_iff`)
Fidelity: exact -/
theorem askModel_D1At_iff :
    (askModel q αN βN VOI d hq hαN hβN).D1At () ↔
      (1 - q) * αN * VOI ≤ q * βN * (d - VOI) := by
  unfold askModel
  rw [d1At_iff_deltaMinus_nonneg _ () (twoState_cont_partBest q αN βN VOI (d - VOI) hq hαN hβN)
    (twoState_stop_partBest q αN βN VOI (d - VOI) hq hαN hβN)]
  exact twoState_deltaMinus_nonneg_iff q αN βN VOI (d - VOI) hq hαN hβN

/-- **T6, the source's ratio form**: under `q < 1`, `0 < β_N`, `0 < VOI`,
heeded iff `α_N/β_N ≤ (q/(1−q))·((d − VOI)/VOI)`.
Source: substitution.md R5 item 25
Kind: C (`twoState_deltaMinus_nonneg_iff_odds` at the instance)
Fidelity: exact -/
theorem askModel_heeded_iff_ratio (hq1 : q < 1) (hβ0 : 0 < βN) (hV : 0 < VOI) :
    0 ≤ (askModel q αN βN VOI d hq hαN hβN).deltaMinus () .cont .stop ↔
      αN / βN ≤ q / (1 - q) * ((d - VOI) / VOI) :=
  twoState_deltaMinus_nonneg_iff_odds q αN βN VOI (d - VOI) hq hαN hβN hq1 hβ0 hV

/-- **T6: "asks"** := the ask model's button has positive two-option value; in the regime
(`0 ≤ E[X]`, `0 ≤ Δ₊`) this is `ε* < q` with `ε* = α_N VOI / (α_N VOI + β_N (d − VOI))`.
Scope: the regime excludes the script's `q = 1/2` row (`E[X] = (1−q)VOI − q(d − VOI) = −1 < 0`
at `VOI = 3/2, d = 5`); the `q = 1/100` row is inside it. The regime-free criterion at `α_N = 0`
is `askModel_alphaN_zero_asks_iff`.
Source: substitution.md R5 item 25 ("Good's theorem gives `VOI(ask) > 0` iff the press would flip the scan decision")
Kind: C (`twoState_voiButton2_pos_iff_epsStar` at the instance)
Fidelity: exact -/
theorem askModel_asks_iff (o₀ : Obs) (hpos : 0 < αN * VOI + βN * (d - VOI))
    (hprior : 0 ≤ expect (twoPoint q hq) ((askModel q αN βN VOI d hq hαN hβN).Xo () o₀ .cont .stop))
    (hsilent : 0 ≤ (askModel q αN βN VOI d hq hαN hβN).deltaPlus () .cont .stop) :
    0 < (askModel q αN βN VOI d hq hαN hβN).voiButton2 () o₀ .cont .stop ↔
      epsStar αN βN VOI (d - VOI) < q :=
  twoState_voiButton2_pos_iff_epsStar q αN βN VOI (d - VOI) hq hαN hβN o₀ hpos hprior hsilent

/-- `0 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem zero_mem_unit : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩

/-- `1 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem one_mem_unit : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩

/-- **T6: `α_N = 0` heeds at every `q > 0`** (`0 < β_N`, `VOI < d`): the overseers never object
without reason, so any objection is decisive (desideratum 1 at the ask model), for every `q`.
Proved as a theorem in `q`, not by cells.
Source: substitution.md R5 item 25 ("with `α_N = 0` … it … obeys at every `q > 0`")
Kind: L (the press cell's sign on the two-state closed form; regraded from P in audit r1)
Fidelity: exact
Hyps: (a) as stated -/
theorem askModel_alphaN_zero_heeds (hq0 : 0 < q) (hβ0 : 0 < βN) (hd : VOI < d) :
    (askModel q 0 βN VOI d hq zero_mem_unit hβN).D1At () := by
  refine ⟨TwoAct.stop, mem_singleton_self _, fun b' => ?_⟩
  cases b'
  · simp only [askModel, obsExpect, obsWeight_press, World.sum_eq, twoState, twoPoint_right,
      twoPoint_wrong, twoPress, twoValue]
    nlinarith [mul_pos hq0 hβ0, sub_pos.mpr hd]
  · exact le_rfl

/-- **T6: when `α_N = 0` asks — the exact criterion, regime-free.** With `0 < q`, `0 < β_N`,
`VOI < d`: the ask has positive value iff silence would make the agent scan,
`q(1−β_N)(d − VOI) < (1−q)·VOI`. **Finding**: the source's "asks … at every `q > 0`" is false as
stated — for `q` near `1` (with `β_N < 1`) silence is not reassuring enough, the agent scans on
no signal, and `VOI(ask) = 0` (`Witnesses.w_ask_alphaN_zero_fails`); the script's grid
(`q ≤ 1/2`) never reaches that region. The "obeys" half is unconditional
(`askModel_alphaN_zero_heeds`).
Source: substitution.md R5 item 25 ("it asks … at every `q > 0`" — corrected here); [[corr-wf14-inventory]] 041
Kind: C (Good's equality clause `voiSensor_pos_iff` at the instance plus two `linarith`s; regraded from P in audit r1 — the docstring missed the regrade until audit r2)
Fidelity: exact (the source's universal claim is refuted; this is the true criterion)
Hyps: (a) as stated -/
theorem askModel_alphaN_zero_asks_iff (hq0 : 0 < q) (hβ0 : 0 < βN) (hd : VOI < d) (o₀ : Obs) :
    0 < (askModel q 0 βN VOI d hq zero_mem_unit hβN).voiButton2 () o₀ .cont .stop ↔
      q * (1 - βN) * (d - VOI) < (1 - q) * VOI := by
  unfold askModel
  rw [twoState_voiButton2_eq_voiSensor, voiSensor_pos_iff]
  simp only [Fin.exists_fin_two, twoButton_signalGain_zero, twoButton_signalGain_one]
  have hpress : (1 - q) * 0 * VOI - q * βN * (d - VOI) < 0 := by
    nlinarith [mul_pos hq0 hβ0, sub_pos.mpr hd]
  constructor
  · rintro ⟨h1 | h1, -⟩
    · linarith
    · linarith
  · intro H
    exact ⟨Or.inr (by linarith), Or.inl hpress⟩

/-- **T6: `α_N = 0`, `β_N = 1` asks at every `q ∈ (0, 1)`** (`0 < VOI < d`): when the overseers
always object to a non-consented scan and never otherwise, silence is decisive too, and the
source's sentence holds in full.
Source: substitution.md R5 item 25 (the case in which its universal claim is true)
Kind: L
Fidelity: exact -/
theorem askModel_perfect_objection_asks (hq0 : 0 < q) (hq1 : q < 1) (hV : 0 < VOI) (hd : VOI < d)
    (o₀ : Obs) :
    0 < (askModel q 0 1 VOI d hq zero_mem_unit one_mem_unit).voiButton2 () o₀ .cont .stop := by
  rw [askModel_alphaN_zero_asks_iff q 1 VOI d hq one_mem_unit hq0 one_pos hd o₀]
  have := mul_pos (sub_pos.mpr hq1) hV
  nlinarith

/-- **T6: `α_N = 0` asks at every `q > 0` on the scan region `q·d < VOI`** — the case R5 item 24
sets the paragraph up on (the agent would scan without asking). There the source's universal
sentence is *true*, as a corollary of the exact criterion: `q·d < VOI` gives
`q(1−β_N)(d − VOI) ≤ q(d − VOI) < (1−q)VOI`. So F-10's refutation lives only where the agent
would not scan anyway (`q·d ≥ VOI`, e.g. `q = 99/100`): the missing scope qualifier, not the
mechanism, is what the source's sentence lacks. The region is sufficient, not necessary
(`Witnesses.w_ask_alphaN_zero_half` asks at `q = 1/2`, outside it).
Source: substitution.md R5 items 24–25 (the scope on which item 25's "asks at every `q > 0`" holds); [[corr-channel-voi-audit-r1-fidelity]] N3; [[corr-channel-voi-audit-r1-adversarial]] N5
Kind: L (`askModel_alphaN_zero_asks_iff` plus arithmetic)
Fidelity: exact (the source's claim, with the scope it needs)
Hyps: (a) `q·d < VOI` named -/
theorem askModel_alphaN_zero_asks_of_scan_region (hq0 : 0 < q) (hβ0 : 0 < βN) (hd : VOI < d)
    (hscan : q * d < VOI) (o₀ : Obs) :
    0 < (askModel q 0 βN VOI d hq zero_mem_unit hβN).voiButton2 () o₀ .cont .stop := by
  rw [askModel_alphaN_zero_asks_iff q βN VOI d hq hβN hq0 hβ0 hd o₀]
  have h1 : q * (1 - βN) * (d - VOI) ≤ q * (d - VOI) := by
    have := mul_nonneg hq0.le (sub_pos.mpr hd).le
    nlinarith [hβN.1]
  nlinarith

/-- **T6, below `VOI ≤ d` the agent scans regardless**: if `d ≤ VOI` (and `0 ≤ VOI`) the stakes
are nonnegative in both consent states, so scanning is press-optimal and the ask is worth
nothing.
Source: [[corr-channel-voi-mandate]] T6 (trap: "say what happens below `VOI ≤ d`")
Kind: L
Fidelity: exact -/
theorem askModel_scans_regardless (hV : 0 ≤ VOI) (hd : d ≤ VOI) (o₀ : Obs) :
    (askModel q αN βN VOI d hq hαN hβN).PosteriorOptimalAt () .press .cont ∧
      (askModel q αN βN VOI d hq hαN hβN).voiButton2 () o₀ .cont .stop = 0 := by
  have hX : ∀ ω, 0 ≤ twoValue VOI (d - VOI) .cont ω := fun ω => by
    cases ω <;> simp [twoValue] <;> linarith
  constructor
  · intro b'
    cases b'
    · exact le_rfl
    · have := (askModel q αN βN VOI d hq hαN hβN).obsExpect_nonneg () .press hX
      simp only [askModel, twoState] at this ⊢
      have e : (twoValue VOI (d - VOI) .cont) = fun ω => twoValue VOI (d - VOI) .cont ω - twoValue VOI (d - VOI) .stop ω := by
        funext ω; cases ω <;> simp [twoValue]
      rw [e, obsExpect_sub] at this
      linarith
  · unfold askModel
    rw [twoState_voiButton2_eq_voiSensor, voiSensor_eq_zero_iff]
    exact Or.inl fun s => Finset.sum_nonneg fun ω _ =>
      mul_nonneg (mul_nonneg ((twoPoint q hq).nonneg ω) (((twoButton αN βN hαN hβN).k_mem ω).1 s)) (hX ω)

end Ask

end

end Cleanroom.Corrigibility.CorrChannelVoi
