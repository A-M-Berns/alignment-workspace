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
import LogicalInduction.Properties.Conditioning
import LogicalInduction.Properties.Basic

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

/-! ## 5. The shortfall as an atom the market has to price

The sections above price a sentence the table has already decided: `shortSentenceOf` is `⊤`
or `⊥`, nothing is left for the market to be uncertain about, and `short_price_eventually_ge`
says the price of `⊤` goes to one.  What they establish is the **generability of a
pre-decided table**.  Here the shortfall of option `j` is an *atom* the model decides only
through the deductive process, at a declared stage. -/

section Deferred

open LO.Propositional (Formula)

/-- **The atom reserved for option description `j`**: tag `7`, paired with the description. -/
def shortAtom (j : ℕ) : Sentence := Formula.atom (Nat.pair 7 j)

theorem shortAtom_injective : Function.Injective shortAtom := by
  intro i j h
  have := Formula.atom.inj h
  exact (Nat.pair_eq_pair.mp this).2

/-- The sentence the model's rollout settles for option `j`: the atom, or its negation. -/
def shortDecision (short : ℕ → Bool) (j : ℕ) : Sentence :=
  if short j then shortAtom j else ∼ shortAtom j

/-- **The shortfall process.**  At stage `n` it has adjoined the decision of every option
`j ≤ n` whose rollout the model has decided by then — `defer j ≤ n`, `defer` the
deferral function.  The stagewise `union` with a base theory is `DeductiveProcess.union`;
one option's adjunction is `adjoinSentence`. -/
def shortfallProcess (short : ℕ → Bool) (defer : ℕ → ℕ) : DeductiveProcess where
  D n := ((Finset.range (n + 1)).filter fun j => defer j ≤ n).image (shortDecision short)
  mono n := by
    intro φ hφ
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hφ ⊢
    obtain ⟨j, ⟨hj, hd⟩, rfl⟩ := hφ
    exact ⟨j, ⟨by omega, by omega⟩, rfl⟩

theorem shortDecision_mem (short : ℕ → Bool) (defer : ℕ → ℕ) (j n : ℕ) (hj : j ≤ n)
    (hd : defer j ≤ n) : shortDecision short j ∈ (shortfallProcess short defer).D n := by
  simp only [shortfallProcess, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  exact ⟨j, ⟨by omega, hd⟩, rfl⟩

theorem shortDecision_injective (short : ℕ → Bool) : Function.Injective (shortDecision short) := by
  intro i j h
  unfold shortDecision at h
  by_cases hi : short i <;> by_cases hj : short j <;>
    simp only [hi, hj, Bool.false_eq_true, if_true, if_false] at h
  · exact shortAtom_injective h
  · exact absurd h (by unfold shortAtom; simp)
  · exact absurd h (by unfold shortAtom; simp)
  · -- both negated: evaluate in the world that makes atom `i` true and everything else false
    by_contra hne
    let v : PCWorld := fun m => m = Nat.pair 7 i
    have h1 : v.Holds (∼ shortAtom i) ↔ v.Holds (∼ shortAtom j) := by rw [h]
    rw [PCWorld.holds_neg, PCWorld.holds_neg] at h1
    have ha : v.Holds (shortAtom i) := (rfl : Nat.pair 7 i = Nat.pair 7 i)
    have hb : ¬ v.Holds (shortAtom j) := by
      intro e
      have e' : Nat.pair 7 j = Nat.pair 7 i := e
      exact hne ((Nat.pair_eq_pair.mp e').2).symm
    exact (h1.mpr hb) ha

/-- **Decided only at its stage**: before `defer j` the decision of `j` is not in the
process. -/
theorem shortDecision_not_mem (short : ℕ → Bool) (defer : ℕ → ℕ) (j n : ℕ) (h : n < defer j) :
    shortDecision short j ∉ (shortfallProcess short defer).D n := by
  simp only [shortfallProcess, Finset.mem_image, Finset.mem_filter, Finset.mem_range, not_exists,
    not_and]
  intro i hi heq
  have := shortDecision_injective short heq
  subst this
  omega

/-- **The world that reads the table**: atom `⟨7, j⟩` is true iff the table says `j` is
short; every other atom is false. -/
def tableWorld (short : ℕ → Bool) : PCWorld :=
  fun m => m.unpair.1 = 7 ∧ short m.unpair.2 = true

theorem tableWorld_holds_atom (short : ℕ → Bool) (j : ℕ) :
    (tableWorld short).Holds (shortAtom j) ↔ short j = true := by
  show tableWorld short (Nat.pair 7 j) ↔ short j = true
  simp [tableWorld, Nat.unpair_pair]

/-- The table's world is consistent with every stage of the shortfall process. -/
theorem tableWorld_consistent (short : ℕ → Bool) (defer : ℕ → ℕ) (n : ℕ) :
    (tableWorld short).ConsistentWith ((shortfallProcess short defer).D n) := by
  intro φ hφ
  simp only [shortfallProcess, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hφ
  obtain ⟨j, -, rfl⟩ := hφ
  unfold shortDecision
  by_cases hs : short j = true
  · rw [if_pos hs]; exact (tableWorld_holds_atom short j).mpr hs
  · rw [if_neg hs, PCWorld.holds_neg, tableWorld_holds_atom]; exact hs

/-- A consistent world exists at every stage of the pure shortfall process. -/
theorem shortfallProcess_world (short : ℕ → Bool) (defer : ℕ → ℕ) (n : ℕ) :
    ∃ v : PCWorld, v.ConsistentWith ((shortfallProcess short defer).D n) :=
  ⟨tableWorld short, tableWorld_consistent short defer n⟩

/-- Over a base theory the table's world remains consistent when it is consistent with the
base. -/
theorem union_world (DP : DeductiveProcess) (short : ℕ → Bool) (defer : ℕ → ℕ)
    (hbase : ∀ n, (tableWorld short).ConsistentWith (DP.D n)) (n : ℕ) :
    ∃ v : PCWorld, v.ConsistentWith ((DP.union (shortfallProcess short defer)).D n) :=
  ⟨tableWorld short, (PCWorld.consistentWith_union_iff _ _ _ _).mpr
    ⟨hbase n, tableWorld_consistent short defer n⟩⟩

/-- The code of an atom is a poly-fueled function of its index. -/
theorem encode_shortAtom (j : ℕ) :
    Encodable.encode (shortAtom j) = Nat.pair 1 (Nat.pair 7 j) + 1 := rfl

/-- **The atom family over an efficiently generated family of options is emitted.** -/
theorem shortAtom_codes (a : ℕ → ℕ) {c : Nat.Partrec.Code} (ha : PolyFueled c a) :
    RpnSentenceCodes (fun n => shortAtom (a n)) := by
  apply RpnSentenceCodes.ofPolySentenceCodes
  refine ⟨_, ((PolyFueled.const 1).pair ((PolyFueled.const 7).pair ha)).succ_comp.of_eq
    (fun n => ?_)⟩
  rw [encode_shortAtom]

theorem shortAtom_const_codes (j : ℕ) : RpnSentenceCodes (fun _ => shortAtom j) :=
  RpnSentenceCodes.const _

variable {P : History} {DP : DeductiveProcess} (short : ℕ → Bool) (defer : ℕ → ℕ)

/-- **Priced ahead of deduction.**  For an efficiently generated family of options the
model decides short — each at its own deferred stage, possibly after the day its sentence is
priced — provability induction drives the day-`n` price of the `n`-th shortfall atom to one,
so from some day on it is above any threshold below one.  The inductor runs over the base
theory united with the shortfall process. -/
theorem deferred_price_eventually_ge
    [IsLogicalInductor P (DP.union (shortfallProcess short defer))] (a : ℕ → ℕ)
    {c : Nat.Partrec.Code} (ha : PolyFueled c a) (hshort : ∀ n, short (a n) = true)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (shortfallProcess short defer)).D n))
    (θ : ℝ) (hθ : θ < 1) : ∃ N, ∀ n, N ≤ n → θ ≤ P n (shortAtom (a n)) := by
  have hthm : ∀ n, ∃ k, shortAtom (a n) ∈ (DP.union (shortfallProcess short defer)).D k := by
    intro n
    refine ⟨max (a n) (defer (a n)), ?_⟩
    rw [DeductiveProcess.union_stage, Finset.mem_union]
    right
    have := shortDecision_mem short defer (a n) (max (a n) (defer (a n))) (le_max_left _ _)
      (le_max_right _ _)
    rwa [shortDecision, if_pos (hshort n)] at this
  have h := lic_provind_true P (DP.union (shortfallProcess short defer)) (fun n => shortAtom (a n))
    (shortAtom_codes a ha) hthm hworld
  have hev : ∀ᶠ n in atTop, |P n (shortAtom (a n)) - 1| < 1 - θ := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h) (1 - θ) (by linarith)
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    simpa [Real.dist_eq] using hN n hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact ⟨N, fun n hn => by linarith [(abs_lt.mp (hN n hn)).1]⟩

/-- **The form ahead of deduction, made explicit**: with every option's stage after the day
its atom is priced, the day-`n` price is of a sentence not yet in the process, and still
tends to one. -/
theorem deferred_ahead
    [IsLogicalInductor P (DP.union (shortfallProcess short defer))] (a : ℕ → ℕ)
    {c : Nat.Partrec.Code} (ha : PolyFueled c a) (hshort : ∀ n, short (a n) = true)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (shortfallProcess short defer)).D n))
    (hdefer : ∀ n, n < defer (a n)) (θ : ℝ) (hθ : θ < 1) :
    (∀ n, shortAtom (a n) ∉ (shortfallProcess short defer).D n) ∧
      ∃ N, ∀ n, N ≤ n → θ ≤ P n (shortAtom (a n)) := by
  refine ⟨fun n => ?_, deferred_price_eventually_ge short defer a ha hshort hworld θ hθ⟩
  have := shortDecision_not_mem short defer (a n) n (hdefer n)
  rwa [shortDecision, if_pos (hshort n)] at this

/-- **A provable non-shortfall's atom is priced to zero** along the family. -/
theorem deferred_price_eventually_le
    [IsLogicalInductor P (DP.union (shortfallProcess short defer))] (a : ℕ → ℕ)
    {c : Nat.Partrec.Code} (ha : PolyFueled c a) (hshort : ∀ n, short (a n) = false)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (shortfallProcess short defer)).D n))
    (θ : ℝ) (hθ : 0 < θ) : ∃ N, ∀ n, N ≤ n → P n (shortAtom (a n)) ≤ θ := by
  have hdis : ∀ n, ∃ k, (∼ shortAtom (a n)) ∈ (DP.union (shortfallProcess short defer)).D k := by
    intro n
    refine ⟨max (a n) (defer (a n)), ?_⟩
    rw [DeductiveProcess.union_stage, Finset.mem_union]
    right
    have := shortDecision_mem short defer (a n) (max (a n) (defer (a n))) (le_max_left _ _)
      (le_max_right _ _)
    rwa [shortDecision, if_neg (by simp [hshort n])] at this
  have h := lic_provind_false P (DP.union (shortfallProcess short defer)) (fun n => shortAtom (a n))
    (shortAtom_codes a ha) hdis hworld
  have hev : ∀ᶠ n in atTop, |P n (shortAtom (a n)) - 0| < θ := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h) θ hθ
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    simpa [Real.dist_eq] using hN n hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact ⟨N, fun n hn => by linarith [(abs_lt.mp (hN n hn)).2]⟩

/-- **A deferred, provable shortfall is eventually excluded.**  With the forecast filter
reading the price of each option's shortfall atom, an option the model decides short —
at its deferred stage, not before — has composed gate mass zero at every day from some
day on. -/
theorem deferred_eventually_excluded
    [IsLogicalInductor P (DP.union (shortfallProcess short defer))] {k : ℕ} [DecidableEq (Fin k)]
    (idx : Fin k → ℕ) (G : GateParams (Fin k)) (hθ : G.θlo < G.θhi) (hθ1 : G.θhi < 1)
    (pT b : ℕ → Fin k → ℝ) (pref : Fin k → ℝ) (j : Fin k) (hj : j ∉ G.Inq)
    (hs : short (idx j) = true)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (shortfallProcess short defer)).D n)) :
    ∃ N, ∀ n, N ≤ n →
      cgate G (fun a => P n (shortAtom (idx a))) (pT n) (b n) pref j = 0 := by
  obtain ⟨N, hN⟩ := deferred_price_eventually_ge (P := P) (DP := DP) short defer (fun _ => idx j)
    (PolyFueled.const (idx j)) (fun _ => hs) hworld G.θhi hθ1
  exact ⟨N, eventually_excluded G pref hθ (fun n a => P n (shortAtom (idx a))) pT b j hj N hN⟩

end Deferred

/-! ## 6. The pre-decided tables tied to the authority module

`Witness.entrenchment`, `storm` and `latency` are transcribed from the Python fixtures.  The
entrenchment table's first two entries are the authority module's own decided `Short` on the
Lean dependency model (`EffectiveAuthority.Dep`, Part 4 of the follow-up):
`EffectiveAuthority.Dep.entrenchment_table_agrees`.  The storm and latency tables have no
Lean instance of the module's physics and remain transcriptions. -/

end Workspace.Deference.Contrib.ShortfallSecurity

#print axioms Workspace.Deference.Contrib.ShortfallSecurity.shortAtom_injective
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.shortfallProcess
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.shortDecision_mem
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.shortDecision_not_mem
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.tableWorld_consistent
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.shortfallProcess_world
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.union_world
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.shortAtom_codes
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.deferred_price_eventually_ge
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.deferred_ahead
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.deferred_price_eventually_le
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.deferred_eventually_excluded

#print axioms Workspace.Deference.Contrib.ShortfallSecurity.shortSentence_codes
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.shortLUV_codes
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.shortSentence_const_codes
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.short_price_eventually_ge
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.notShort_price_eventually_le
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.shortfall_eventually_excluded
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.Witness.tables
#print axioms Workspace.Deference.Contrib.ShortfallSecurity.Witness.fixtures_generable
