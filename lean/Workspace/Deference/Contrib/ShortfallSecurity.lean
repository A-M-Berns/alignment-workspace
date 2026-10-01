/-
# The shortfall event as a security: generability and pricing over a fixed finite control model

Round `projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/`, Part E
— the core of `PRIORITIES.md` item 101.

**The object.**  Over a fixed finite control model — a decidable table `short : Fin k → Bool`
saying, for each of `k` option descriptions, whether the option leaves the matter short of
its requirement (`AuthorityModule.Short` on the finite rollout, decided by the model's
transition table, cost table, window and admissibility verdict) — the shortfall indicator of
option `j` is the sentence `⊤` or `⊥` the table decides (`shortSentence`), and its priced
event is the indicator variable (`shortLUV`).

**Generability.**  The family over days and options, indexed by `Nat.pair n j` with the
option read off the paired index and the last option absorbing the overflow (`optionAt`), is
efficiently emitted: `shortSentence_codes` (for four options, the dispatch pattern of
`LICorrigibilityCertificate.luvOf_thresholdCodeSeq`), and so is its indicator family
(`shortLUV_codes`).  A fixed option's family is constant (`shortSentence_const_codes`).

**Pricing.**  For an option the model proves short, the sentence family is `⊤` throughout;
provability induction (pinned `lic_provind_true`) drives its price to `1`, so the price is
eventually above any threshold below `1` (`short_price_eventually_ge`), which discharges the
hypothesis of `DecisionComponent.eventually_excluded`: the option is eventually excluded by
the forecast rule at every later day (`shortfall_eventually_excluded`).  For an option the
model proves not short, the family is `⊥` and the price goes to `0`
(`notShort_price_eventually_le`).

**What this does not establish.**  Anything about *caused* shortfall (the contrast with the
idle move is a count-side object, not the priced event — the storm fixture shows why pricing
the uncontrasted event is right: it excludes every option that leaves her short and leaves
restore and ask); the drill calibration, the feedback trader's emission, the deferral
function and the taint event (item 101's remainder); the generability of a schedule that
reads the model's transition table at run time — the table here is data of the theory, and
the certificate is for a model fixed in advance; learned membership (M4), which this prices
inside the declared model only.  Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.LICorrigibilityCertificate
import Workspace.Deference.Contrib.DecisionComponent

namespace Workspace.Deference.Contrib.ShortfallSecurity

open LogicalInduction
open Filter Topology
open Workspace.Deference.Contrib.LICorrigibility (indicator indicator_thresholdCodeSeq top bot)
open Workspace.Deference.Contrib.DecisionComponent

/-! ## 1. The object -/

/-- **A fixed finite control model**, as the decision component reads it: for each of `k`
option descriptions, whether the option leaves the matter short.  The table is the model's
finite rollout decided (`AuthorityModule.Short`); here it is data. -/
structure ControlModel (k : ℕ) where
  short : Fin k → Bool

/-- The shortfall indicator of an option, as a sentence: `⊤` where the model decides a
shortfall, `⊥` otherwise. -/
def shortSentenceOf {k : ℕ} (cm : ControlModel k) (j : Fin k) : Sentence :=
  if cm.short j then top else bot

/-- The priced event: the indicator variable of the shortfall sentence. -/
def shortLUVOf {k : ℕ} (cm : ControlModel k) (j : Fin k) : LUV :=
  indicator (shortSentenceOf cm j)

/-! ## 2. Generability -/

section Generability

/-- The option read off a paired index `⟨n, j⟩`: the `j`-th of four, the last absorbing the
overflow. -/
def optionAt (z : ℕ) : Fin 4 :=
  match z.unpair.2 with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

/-- The family over days and options. -/
def shortSentence (cm : ControlModel 4) (z : ℕ) : Sentence := shortSentenceOf cm (optionAt z)

/-- The test `j − c` on the option coordinate of the paired index. -/
lemma optionTest_poly (c : ℕ) : ∃ cc, PolyFueled cc (fun z : ℕ => z.unpair.2 - c) :=
  ⟨_, (subc_polyFueled.comp (PolyFueled.right.pair (PolyFueled.const c))).of_eq
    (fun z => by simp)⟩

/-- **The shortfall family is efficiently emitted**: a four-way dispatch on the option
coordinate between the constant sentences the table decides. -/
theorem shortSentence_codes (cm : ControlModel 4) : RpnSentenceCodes (shortSentence cm) := by
  obtain ⟨c0, h0⟩ := optionTest_poly 0
  obtain ⟨c1, h1⟩ := optionTest_poly 1
  obtain ⟨c2, h2⟩ := optionTest_poly 2
  refine (RpnSentenceCodes.ifZero (RpnSentenceCodes.const (shortSentenceOf cm 0))
    (RpnSentenceCodes.ifZero (RpnSentenceCodes.const (shortSentenceOf cm 1))
      (RpnSentenceCodes.ifZero (RpnSentenceCodes.const (shortSentenceOf cm 2))
        (RpnSentenceCodes.const (shortSentenceOf cm 3)) h2)
      h1)
    h0).of_eq (fun z => ?_)
  unfold shortSentence optionAt
  rcases hj : z.unpair.2 with _ | _ | _ | j <;> rfl

/-- **The priced event's family is efficiently emitted.** -/
theorem shortLUV_codes (cm : ControlModel 4) :
    LUV.RpnThresholdCodeSeq (fun z => indicator (shortSentence cm z)) :=
  indicator_thresholdCodeSeq (shortSentence_codes cm)

/-- A fixed option's family is constant and emitted. -/
theorem shortSentence_const_codes {k : ℕ} (cm : ControlModel k) (j : Fin k) :
    RpnSentenceCodes (fun _ => shortSentenceOf cm j) :=
  RpnSentenceCodes.const _

end Generability

/-! ## 3. Pricing -/

section Pricing

variable {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]

/-- **The price of a provable shortfall goes to one.**  For an option the model decides short,
the sentence is `⊤`; with `⊤` in the deductive process and a consistent world at every
stage, provability induction gives price `1` in the limit, hence eventually at least any
threshold below `1`. -/
theorem short_price_eventually_ge {k : ℕ} (cm : ControlModel k) (j : Fin k)
    (hs : cm.short j = true) (htop : ∃ m, top ∈ DP.D m)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (θ : ℝ) (hθ : θ < 1) :
    ∃ N, ∀ n, N ≤ n → θ ≤ P n (shortSentenceOf cm j) := by
  have hφ : shortSentenceOf cm j = top := by simp [shortSentenceOf, hs]
  have h := lic_provind_true P DP (fun _ => shortSentenceOf cm j)
    (RpnSentenceCodes.const _) (fun _ => by rw [hφ]; exact htop) hworld
  have hev : ∀ᶠ n in atTop, |P n (shortSentenceOf cm j) - 1| < 1 - θ := by
    have := (Metric.tendsto_atTop.mp h) (1 - θ) (by linarith)
    obtain ⟨N, hN⟩ := this
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have := hN n hn
    simpa [Real.dist_eq] using this
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  have := (abs_lt.mp (hN n hn)).1
  linarith

/-- **The price of a provable non-shortfall goes to zero**: the sentence is `⊥`, disprovable
once `⊤ = ∼⊥` is in the process; eventually below any positive threshold. -/
theorem notShort_price_eventually_le {k : ℕ} (cm : ControlModel k) (j : Fin k)
    (hs : cm.short j = false) (hneg : ∃ m, (∼(bot : Sentence)) ∈ DP.D m)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (θ : ℝ) (hθ : 0 < θ) :
    ∃ N, ∀ n, N ≤ n → P n (shortSentenceOf cm j) ≤ θ := by
  have hφ : shortSentenceOf cm j = bot := by simp [shortSentenceOf, hs]
  have h := lic_provind_false P DP (fun _ => shortSentenceOf cm j)
    (RpnSentenceCodes.const _) (fun _ => by rw [hφ]; exact hneg) hworld
  have hev : ∀ᶠ n in atTop, |P n (shortSentenceOf cm j) - 0| < θ := by
    have := (Metric.tendsto_atTop.mp h) θ hθ
    obtain ⟨N, hN⟩ := this
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have := hN n hn
    simpa [Real.dist_eq] using this
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  have := (abs_lt.mp (hN n hn)).2
  linarith

/-- **A provable shortfall is eventually excluded.**  With the shortfall price of each option
read as the forecast filter's `p_n(S_a)`, an option the model decides short, not itself the
inquiry option, has composed gate mass zero at every day from some day on: the hypothesis
of `DecisionComponent.eventually_excluded`, discharged by provability induction. -/
theorem shortfall_eventually_excluded {k : ℕ} [DecidableEq (Fin k)] (cm : ControlModel k)
    (G : GateParams (Fin k)) (hθ : G.θlo < G.θhi) (hθ1 : G.θhi < 1)
    (pT b : ℕ → Fin k → ℝ) (pref : Fin k → ℝ) (j : Fin k) (hj : j ∉ G.Inq)
    (hs : cm.short j = true) (htop : ∃ m, top ∈ DP.D m)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ N, ∀ n, N ≤ n →
      cgate G (fun a => P n (shortSentenceOf cm a)) (pT n) (b n) pref j = 0 := by
  obtain ⟨N, hN⟩ := short_price_eventually_ge (P := P) (DP := DP) cm j hs htop hworld G.θhi hθ1
  exact ⟨N, eventually_excluded G pref hθ (fun n a => P n (shortSentenceOf cm a)) pT b j hj N hN⟩

end Pricing

/-! ## 4. Witnesses: the three fixtures' tables -/

namespace Witness

/-- **The entrenchment fixture**: options `idle`, `build the dependency`, `repaint`, `ask`;
building the dependency leaves the halt matter short. -/
def entrenchment : ControlModel 4 := ⟨![false, true, false, false]⟩

/-- **The storm fixture**: options `idle`, `restore the wire`, `build the dependency`, `ask`;
after the storm idling leaves the matter short, restoring does not, building the
dependency does. -/
def storm : ControlModel 4 := ⟨![true, false, true, false]⟩

/-- **The latency fixture**: options on the routine matter whose window is shorter than the
consultation latency — every option but delegation leaves it short. -/
def latency : ControlModel 4 := ⟨![true, true, true, false]⟩

theorem tables :
    entrenchment.short 1 = true ∧ entrenchment.short 0 = false ∧
      storm.short 0 = true ∧ storm.short 1 = false ∧ storm.short 2 = true ∧
      latency.short 0 = true ∧ latency.short 3 = false := by
  decide

/-- The three families are emitted. -/
theorem fixtures_generable :
    RpnSentenceCodes (shortSentence entrenchment) ∧ RpnSentenceCodes (shortSentence storm) ∧
      RpnSentenceCodes (shortSentence latency) :=
  ⟨shortSentence_codes _, shortSentence_codes _, shortSentence_codes _⟩

end Witness

end Workspace.Deference.Contrib.ShortfallSecurity

#print axioms Workspace.Deference.Contrib.ShortfallSecurity.shortSentence_codes
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.shortLUV_codes
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.shortSentence_const_codes
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.short_price_eventually_ge
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.notShort_price_eventually_le
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.shortfall_eventually_excluded
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.Witness.tables
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.Witness.fixtures_generable
