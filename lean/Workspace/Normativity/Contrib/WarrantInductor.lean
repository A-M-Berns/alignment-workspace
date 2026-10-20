/-
# The warrant Normative Inductor

Round `projects/normativity/rounds/2026-10-22-normative-inductor-integration/`.

One construction, read in four views, run on one market, and scored by one evaluation.

1. **The normative state** (`NormState`): the record state — grounds, docket, settlement,
   authorized events — together with the structural (coherence) rows.  Its **survivors**
   are the grounded rule's (`Grounds.survivors`); its **bundle** is the forced bundle of the
   survivors' items with the live structural rows and the settlement's pins.  The joint
   price-space region (`region`), the cited bundle a licence checks (`Supported`, `Licensed`),
   the input of the forced-interval elimination (`interval`) and the rows the enforcer holds
   (`WarrantForce.bundlePres`) are all read off this one bundle.
2. **Admission** (`Admission`): a typed link from the accounted obligation state to the
   grounds — every admitted occurrence realizes an exposed obligation.  It is a declared
   semantic input; nothing here derives legitimacy.  **Well-formedness**
   (`Grounds.WellFormed`): identities are unique and citations resolve, so a survivor's
   citation names exactly one survivor.
3. **Compilation with withholding** (`compileAt`, `schedule`): a date's bundle is enforced
   when the supplied witness checks into its region (`checkCompiled`), and no row is
   enforced otherwise.  Force is never derived from an unchecked constraint set.
4. **The adapter** (`Problem`, `gate`): a finite menu scored by affine functionals of the
   displayed prices, run through the soft gate of `GatedChoice`.  The declared adequate set
   `A` and the per-response losses are the adequacy semantics; what connects them to the
   market is **certified**: an upper functional certificate on each inadequate response's
   score (`Excludes`) and a lower one on each margin witness (`Margins`), both cited into the
   day's compiled bundle.  At the realized market the transport theorem of `WarrantForce`
   turns them into the displayed exclusion and the displayed margin, and the soft gate's
   coupling theorem (`softGate_massOff_le_displayed`) gives `PracticalCert` with the public
   defect `defectOf` — the displayed excess of the inadequate responses — and the constant
   `κ = (Σ_{q∉A} pref q)/(W δ)`.
5. **The theorem** (`warrant_inductor`): on the augmented deductive market of the compiled
   schedule, with the deductive process computable and the enforcer effective (the two
   computability inputs, isolated), a slack plausible world at every date (affordability),
   checked witnesses, certified exclusion and margins at the service dates, the adequacy
   semantics, and the protocol's declared constants: the market is a logical inductor over
   the deductive process; every enforced row conforms at the displayed price within the
   tolerance; every enforced row traces to a survivor realizing an exposed obligation, a
   structural row, or a pin; the adapter's inadequate mass is at most `κ` times the public
   defect, which is at most the certificates' mass times the tolerance; and the Progress
   bound holds with `PracticalUptake` derived, not assumed.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.WarrantForce
import Workspace.Normativity.Contrib.GatedChoice

namespace Workspace.Normativity.Contrib.WarrantInductor

open LogicalInduction
open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.WarrantEntitlement
open Workspace.Normativity.Contrib.WarrantForce
open Workspace.Normativity.Contrib.EnforcementStrategy
open Workspace.Normativity.Contrib.DeductiveEnforcement
open Workspace.Normativity.Contrib.EnforcedComputation
open Workspace.Normativity.Contrib.GatedChoice
open Workspace.Normativity.Contrib.PracticalCertificate (anchoredLoss adequate_set_route)
open Workspace.Normativity.Contrib.NormativeInductionInterface
open Workspace.Normativity.Contrib.OccurrenceIntegrity (Protocol)
open Workspace.Normativity.Contrib.OpenIntegrityEvolution (ObligationState)
open Workspace.Normativity.Contrib.AssessmentProcess (ratPayout)
open Finset

variable {d : ℕ}

/-! ## 1. The canonical normative state -/

/-- **The normative state**: the record state together with the structural rows. -/
structure NormState (d : ℕ) extends RecordState d where
  /-- The structural (coherence) rows, not defeasible by the docket. -/
  structural : List (StrItem d)

namespace NormState

variable (N : NormState d)

/-- The survivors of the state's grounds under its docket and settlement. -/
def survivors : Grounds d := N.grounds.survivors N.docket N.settlement

/-- The seed the state presents: the survivors' items and the structural rows. -/
def seed : Seed d Unit := ⟨N.survivors.map Occurrence.toSub, N.structural, ⟨∅, ∅⟩⟩

/-- **The canonical bundle**: the survivors' specialized rows, the live structural rows, and
the pins. -/
def bundle : Bundle (Cite d) d := forcedBundle N.seed [] N.docket N.settlement

/-- **The joint region**. -/
def region (x : Fin d → ℚ) : Prop := N.bundle.Region x

instance (x : Fin d → ℚ) : Decidable (N.region x) := by unfold region; infer_instance

/-- **The forced interval of a coordinate**, by the elimination of `SeedStatics`. -/
def interval {m : ℕ} (N : NormState (m + 1)) (φ : Fin (m + 1)) : ℚ × ℚ :=
  forcedInterval N.seed [] N.docket N.settlement φ

/-- Survivors are not defeated, so the docket filter is the identity on the seed's items. -/
lemma seed_liveSub : N.seed.liveSub N.docket = N.seed.sub := by
  unfold Seed.liveSub seed
  rw [List.filter_eq_self]
  intro it hit
  simp only [List.mem_map] at hit
  obtain ⟨o, ho, rfl⟩ := hit
  simpa [Occurrence.toSub] using survivors_not_defeated _ _ _ ho

/-- **The region, by occurrence**: the cube, the pins, every survivor's row, every live
structural row. -/
theorem region_iff (x : Fin d → ℚ) :
    N.region x ↔
      InCube x ∧ N.settlement.Pinned x ∧ (∀ o ∈ N.survivors, o.form.row.Sat x) ∧
        ∀ it ∈ N.seed.liveStr N.docket, it.row.Sat x := by
  show forcedRegion N.seed [] N.docket N.settlement x ↔ _
  rw [forcedRegion_iff, seed_liveSub]
  simp [seed, Occurrence.toSub]

/-- Without structural rows the canonical bundle is the settled bundle of the grounds. -/
theorem bundle_eq_settledBundle (h : N.structural = []) :
    N.bundle = N.grounds.settledBundle N.docket N.settlement := by
  unfold bundle forcedBundle Grounds.settledBundle
  rw [seed_liveSub]
  simp [seed, Seed.liveStr, h, Occurrence.toSub, List.map_map, Function.comp_def, survivors]

/-- Without structural rows the canonical region is the settled region. -/
theorem region_iff_settledRegion (h : N.structural = []) (x : Fin d → ℚ) :
    N.region x ↔ N.grounds.settledRegion N.docket N.settlement x := by
  unfold region Grounds.settledRegion
  rw [bundle_eq_settledBundle N h]

/-- **The elimination's specification on the canonical bundle**: the computed endpoints are
valid bounds on the real region and are attained. -/
theorem interval_spec {m : ℕ} (N : NormState (m + 1)) (φ : Fin (m + 1))
    (hne : ∃ x, forcedRegionR N.seed [] N.docket N.settlement x) :
    (∀ x, forcedRegionR N.seed [] N.docket N.settlement x →
      (((N.interval φ).1 : ℚ) : ℝ) ≤ x φ ∧ x φ ≤ (((N.interval φ).2 : ℚ) : ℝ)) ∧
    (∃ x, forcedRegionR N.seed [] N.docket N.settlement x ∧ x φ = (((N.interval φ).1 : ℚ) : ℝ)) ∧
    (∃ x, forcedRegionR N.seed [] N.docket N.settlement x ∧ x φ = (((N.interval φ).2 : ℚ) : ℝ)) :=
  forcedInterval_spec N.seed [] N.docket N.settlement φ hne

/-- **Supported on the canonical bundle.** -/
def Supported {m m' : ℕ} (φ : Fin d) (v : ℚ) (c : VerdictCert d m m' φ) : Prop :=
  SupportedOn N.bundle φ v c

/-- **Licensed on the canonical state**: supported, and the issuing event authorized. -/
def Licensed {m m' : ℕ} (φ : Fin d) (v : ℚ) (c : VerdictCert d m m' φ) (event : ℕ) : Prop :=
  N.Supported φ v c ∧ event ∈ N.authorized

/-- The licence chain on the canonical state. -/
theorem licence_chain {m m' : ℕ} {φ : Fin d} {v : ℚ} {c : VerdictCert d m m' φ} {event : ℕ}
    (h : N.Licensed φ v c event) : N.Supported φ v c ∧ AdmissibleOn N.bundle φ v :=
  ⟨h.1, supportedOn_admissibleOn h.1⟩

/-- Without structural rows the canonical licence is the record's. -/
theorem licensed_iff (h : N.structural = []) {m m' : ℕ} {φ : Fin d} {v : ℚ}
    {c : VerdictCert d m m' φ} {event : ℕ} :
    N.Licensed φ v c event ↔ WarrantEntitlement.Licensed N.toRecordState φ v c event := by
  unfold Licensed Supported WarrantEntitlement.Licensed WarrantEntitlement.Supported
  rw [bundle_eq_settledBundle N h]

end NormState

/-! ## 2. Admission and well-formedness -/

/-- **Admission**: every occurrence of the grounds realizes an exposed occurrence of the
accounted obligation state.  A typed semantic input: the legitimacy of the admission is the
obligation state's, and nothing here derives it. -/
structure Admission {Occ Req : Type*} {S : Protocol Occ Req} {anchor : Occ → Req}
    (O : ObligationState S anchor) (G : Grounds d) where
  /-- The exposed obligation occurrence a warrant occurrence realizes. -/
  origin : Occurrence d → Occ
  origin_exposed : ∀ o ∈ G, origin o ∈ O.boundary.exposed

/-- **Well-formed grounds**: identities are unique and every citation resolves. -/
def _root_.Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.WellFormed
    (G : Grounds d) : Prop :=
  (G.map Occurrence.id).Nodup ∧ ∀ o ∈ G, ∀ j, o.cites = .occurrence j → ∃ o' ∈ G, o'.id = j

/-- In well-formed grounds, an identity names one occurrence. -/
theorem _root_.Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.WellFormed.id_inj
    {G : Grounds d} (h : G.WellFormed) {o o' : Occurrence d}
    (ho : o ∈ G) (ho' : o' ∈ G) (hid : o.id = o'.id) : o = o' :=
  List.inj_on_of_nodup_map h.1 ho ho' hid

/-- **A survivor's citation names exactly one survivor.** -/
theorem _root_.Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.WellFormed.cited_unique
    {G : Grounds d} (h : G.WellFormed) (st : DocketState)
    (F : Settlement d) {o : Occurrence d} (ho : o ∈ G.survivors st F) {j : ℕ}
    (hj : o.cites = .occurrence j) :
    ∃! o', o' ∈ G.survivors st F ∧ o'.id = j := by
  obtain ⟨o', ho', hid⟩ := ((mem_survivors G st F).1 ho).2.2.2 j hj
  refine ⟨o', ⟨ho', hid⟩, fun o'' ⟨ho'', hid''⟩ => ?_⟩
  exact h.id_inj (survivors_subset G st F ho'') (survivors_subset G st F ho') (hid''.trans hid.symm)

/-! ## 3. Compilation with withholding -/

/-- **The compiled bundle of a date**: the state's bundle when the supplied witness checks
into its region, the empty bundle — force withheld — otherwise. -/
def compileAt (N : NormState d) (w : Fin d → ℚ) : Bundle (Cite d) d :=
  if checkCompiled N.bundle w then N.bundle else []

theorem compileAt_eq_of_check {N : NormState d} {w : Fin d → ℚ}
    (h : checkCompiled N.bundle w = true) : compileAt N w = N.bundle := by
  simp [compileAt, h]

theorem compileAt_eq_nil {N : NormState d} {w : Fin d → ℚ}
    (h : ¬ checkCompiled N.bundle w = true) : compileAt N w = [] := by
  simp [compileAt, h]

/-- A checked witness is a point of the compiled bundle's region. -/
theorem region_compileAt {N : NormState d} {w : Fin d → ℚ}
    (h : checkCompiled N.bundle w = true) : (compileAt N w).Region w := by
  rw [compileAt_eq_of_check h]
  exact (checkCompiled_iff _ _).1 h

/-- **A fragment map**: the priced sentences of the coordinates, listed once each. -/
structure FragmentMap (d : ℕ) where
  ι : Fin d → Sentence
  inj : Function.Injective ι
  coords : List Sentence
  nodup : coords.Nodup
  mem : ∀ j, ι j ∈ coords

/-- **The schedule of a state process**: the compiled bundle of each date, with the
requested tolerances. -/
def schedule (N : ℕ → NormState d) (F : FragmentMap d) (wit : ℕ → Fin d → ℚ) (tol : ℕ → ℚ)
    (htol : ∀ n, 0 < tol n) : WarrantSchedule d :=
  ⟨F.ι, F.inj, F.coords, F.nodup, F.mem, fun n => compileAt (N n) (wit n), tol, htol⟩

@[simp] lemma schedule_bundle (N : ℕ → NormState d) (F : FragmentMap d) (wit : ℕ → Fin d → ℚ)
    (tol : ℕ → ℚ) (htol : ∀ n, 0 < tol n) (n : ℕ) :
    (schedule N F wit tol htol).bundle n = compileAt (N n) (wit n) := rfl

@[simp] lemma schedule_ι (N : ℕ → NormState d) (F : FragmentMap d) (wit : ℕ → Fin d → ℚ)
    (tol : ℕ → ℚ) (htol : ∀ n, 0 < tol n) : (schedule N F wit tol htol).ι = F.ι := rfl

@[simp] lemma schedule_tol (N : ℕ → NormState d) (F : FragmentMap d) (wit : ℕ → Fin d → ℚ)
    (tol : ℕ → ℚ) (htol : ∀ n, 0 < tol n) : (schedule N F wit tol htol).tol = tol := rfl

/-- **Provenance of force**: every row the compiled schedule enforces is a survivor's row
under its citation, a live structural row, or a pin. -/
theorem mem_compileAt {N : NormState d} {w : Fin d → ℚ} {c : CitedRow (Cite d) d}
    (hc : c ∈ compileAt N w) :
    (∃ o ∈ N.survivors, c = ⟨Cite.sub o.id, specialize N.settlement o.form.row⟩) ∨
    (∃ it ∈ N.seed.liveStr N.docket, c = ⟨Cite.str it.id, specialize N.settlement it.row⟩) ∨
    (∃ i, ∃ r ∈ N.settlement.pinRowsAt i, c = ⟨Cite.settled i, r⟩) := by
  unfold compileAt at hc
  split_ifs at hc with h
  · unfold NormState.bundle forcedBundle at hc
    rw [N.seed_liveSub] at hc
    simp only [List.append_nil, List.mem_append, List.mem_map, pinCited, List.mem_flatMap,
      List.mem_finRange, true_and, NormState.seed, Occurrence.toSub] at hc
    rcases hc with (⟨it, ⟨o, ho, rfl⟩, rfl⟩ | ⟨it, hit, rfl⟩) | ⟨i, r, hr, rfl⟩
    · exact Or.inl ⟨o, ho, rfl⟩
    · exact Or.inr (Or.inl ⟨it, hit, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, r, hr, rfl⟩)
  · simp at hc

/-! ## 4. The adapter: a finite menu scored by certified functionals -/

/-- A functional certificate together with the citations of its rows. -/
structure CitedFunctional (d : ℕ) (ℓ : Fin d → ℚ) where
  m : ℕ
  cert : FunctionalCert d m ℓ
  cites : Fin m → Cite d

/-- Every positively weighted row is admitted into the bundle under its citation. -/
def CitedFunctional.CitesLive {ℓ : Fin d → ℚ} (c : CitedFunctional d ℓ) (B : Bundle (Cite d) d) :
    Prop :=
  ∀ i, 0 < c.cert.mult i → VerdictCert.RowAdmitted B (c.cites i) (c.cert.row i)

/-- **A decision problem on a finite menu `Q`**: each response is scored by an affine
functional of the fragment's prices; `A` is the declared adequate set and `A₁ ⊆ A` the margin
witnesses; `pref` a positive task preference; `τ, δ` the gate's threshold and ramp width; `W`
a lower bound on the witnesses' preference mass; `upper q` a certificate on the score of `q`
(used for inadequate `q`) and `lower q` one on its negation (used for margin witnesses). -/
structure Problem (d : ℕ) (Q : Type) [Fintype Q] [DecidableEq Q] where
  offset : Q → ℚ
  ℓ : Q → Fin d → ℚ
  A : Finset Q
  A₁ : Finset Q
  A₁_sub : A₁ ⊆ A
  pref : Q → ℝ
  pref_nonneg : ∀ q, 0 ≤ pref q
  τ : ℝ
  δ : ℝ
  δ_pos : 0 < δ
  W : ℝ
  W_pos : 0 < W
  W_le : W ≤ ∑ q ∈ A₁, pref q
  upper : (q : Q) → CitedFunctional d (ℓ q)
  lower : (q : Q) → CitedFunctional d (fun j => -(ℓ q j))

namespace Problem

variable {Q : Type} [Fintype Q] [DecidableEq Q] (P : Problem d Q)

/-- The score of a response at a displayed price vector. -/
noncomputable def scoreR (b : Fin d → ℝ) (q : Q) : ℝ := (P.offset q : ℝ) + ∑ j, (P.ℓ q j : ℝ) * b j

lemma scoreR_cast (p : Fin d → ℚ) (q : Q) :
    P.scoreR (fun j => (p j : ℝ)) q = ((P.offset q + ∑ j, P.ℓ q j * p j : ℚ) : ℝ) := by
  unfold scoreR; push_cast; rfl

/-- **The gate**: the soft gate of `GatedChoice` on the scores. -/
noncomputable def gate (b : Fin d → ℝ) : Q → ℝ := softGate (P.scoreR b) P.pref P.τ P.δ

/-- **The public defect**: the displayed excess of the inadequate responses over the
threshold. -/
noncomputable def defectOf (b : Fin d → ℝ) : ℝ := ∑ q ∈ univ \ P.A, max 0 (P.scoreR b q - P.τ)

lemma defectOf_nonneg (b : Fin d → ℝ) : 0 ≤ P.defectOf b :=
  Finset.sum_nonneg fun _ _ => le_max_left _ _

lemma le_defectOf (b : Fin d → ℝ) {q : Q} (hq : q ∉ P.A) : P.scoreR b q - P.τ ≤ P.defectOf b :=
  le_trans (le_max_right _ _)
    (Finset.single_le_sum (f := fun q => max 0 (P.scoreR b q - P.τ)) (fun _ _ => le_max_left _ _)
      (Finset.mem_sdiff.2 ⟨Finset.mem_univ q, hq⟩))

/-- The coupling constant of the gate: inadequate preference mass over the certified
witness mass, per unit of relative defect. -/
noncomputable def κ : ℝ := (∑ q ∈ univ \ P.A, P.pref q) / P.W / P.δ

/-- The total certificate mass of the inadequate responses. -/
def massCap : ℚ := ∑ q ∈ univ \ P.A, (P.upper q).cert.mass

lemma massCap_nonneg : 0 ≤ P.massCap := Finset.sum_nonneg fun q _ => (P.upper q).cert.mass_nonneg

/-- **Region exclusion, certified**: every inadequate response's score is certified on the
bundle to be at most `τ`. -/
def Excludes (B : Bundle (Cite d) d) : Prop :=
  ∀ q ∉ P.A, (P.upper q).CitesLive B ∧ ((P.offset q + (P.upper q).cert.value : ℚ) : ℝ) ≤ P.τ

/-- **Margin, certified**: every margin witness's score is certified on the bundle to be at
least `τ + δ`, with room for the tolerance. -/
def Margins (B : Bundle (Cite d) d) (tol : ℚ) : Prop :=
  ∀ q ∈ P.A₁, (P.lower q).CitesLive B ∧
    P.τ + P.δ ≤ ((P.offset q - (P.lower q).cert.value - (P.lower q).cert.mass * tol : ℚ) : ℝ)

/-! ### At the realized market -/

variable (W : WarrantSchedule d) (DP : DeductiveProcess) (n : ℕ)

/-- The displayed price vector of date `n`, as reals. -/
noncomputable def priceR : Fin d → ℝ := fun j => (W.priceVec DP n j : ℝ)

lemma priceR_eq_market (j : Fin d) : priceR W DP n j = W.market DP n (W.ι j) := rfl

/-- **Displayed exclusion**: an inadequate response's score at the market is at most `τ`
plus its certificate's mass times the tolerance. -/
theorem scoreR_le (y : Fin d → ℚ) (hy : (W.bundle n).Region y) (hex : P.Excludes (W.bundle n))
    {q : Q} (hq : q ∉ P.A) :
    P.scoreR (priceR W DP n) q ≤ P.τ + (((P.upper q).cert.mass * W.tol n : ℚ) : ℝ) := by
  obtain ⟨hlive, hval⟩ := hex q hq
  have h := W.functional_at_market DP n y hy (P.upper q).cert (P.upper q).cites hlive
  unfold priceR
  rw [P.scoreR_cast]
  have h' : ((P.offset q + ∑ j, P.ℓ q j * W.priceVec DP n j : ℚ) : ℝ) ≤
      ((P.offset q + (P.upper q).cert.value : ℚ) : ℝ) + (((P.upper q).cert.mass * W.tol n : ℚ) : ℝ) := by
    push_cast
    have : ((∑ j, P.ℓ q j * W.priceVec DP n j : ℚ) : ℝ) ≤
        (((P.upper q).cert.value : ℚ) : ℝ) + ((P.upper q).cert.mass : ℝ) * (W.tol n : ℝ) := by
      exact_mod_cast h
    push_cast at this
    linarith
  linarith

/-- **Displayed margin**: a margin witness's score at the market is at least `τ + δ`. -/
theorem scoreR_ge (y : Fin d → ℚ) (hy : (W.bundle n).Region y)
    (hmar : P.Margins (W.bundle n) (W.tol n)) {q : Q} (hq : q ∈ P.A₁) :
    P.τ + P.δ ≤ P.scoreR (priceR W DP n) q := by
  obtain ⟨hlive, hval⟩ := hmar q hq
  have h := W.functional_at_market DP n y hy (P.lower q).cert (P.lower q).cites hlive
  unfold priceR
  rw [P.scoreR_cast]
  have hneg : ∑ j, -(P.ℓ q j) * W.priceVec DP n j = -∑ j, P.ℓ q j * W.priceVec DP n j := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hneg] at h
  have h' : ((P.offset q - (P.lower q).cert.value - (P.lower q).cert.mass * W.tol n : ℚ) : ℝ) ≤
      ((P.offset q + ∑ j, P.ℓ q j * W.priceVec DP n j : ℚ) : ℝ) := by
    exact_mod_cast (by linarith : P.offset q - (P.lower q).cert.value - (P.lower q).cert.mass * W.tol n ≤
      P.offset q + ∑ j, P.ℓ q j * W.priceVec DP n j)
  linarith

/-- **The public defect is at most the certificates' mass times the tolerance.** -/
theorem defectOf_le (y : Fin d → ℚ) (hy : (W.bundle n).Region y) (hex : P.Excludes (W.bundle n)) :
    P.defectOf (priceR W DP n) ≤ ((P.massCap * W.tol n : ℚ) : ℝ) := by
  unfold defectOf massCap
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun q hq => ?_
  have hq' : q ∉ P.A := (Finset.mem_sdiff.1 hq).2
  have h1 := P.scoreR_le W DP n y hy hex hq'
  have hm : (0 : ℝ) ≤ ((P.upper q).cert.mass : ℝ) * (W.tol n : ℝ) :=
    mul_nonneg (by exact_mod_cast (P.upper q).cert.mass_nonneg) (by exact_mod_cast (W.tol_pos n).le)
  push_cast at h1
  exact max_le hm (by linarith)

/-- **Inadequate mass at the market**: the gate's mass off the adequate set is at most `κ`
times the public defect.  Decision theory: the soft gate's coupling under the displayed
exclusion and margin. -/
theorem massOff_le (y : Fin d → ℚ) (hy : (W.bundle n).Region y) (hmar : P.Margins (W.bundle n) (W.tol n)) :
    massOff (P.gate (priceR W DP n)) P.A ≤ P.κ * P.defectOf (priceR W DP n) := by
  set b := P.scoreR (priceR W DP n) with hb
  -- the synthetic region point: the displayed score on `A`, clipped at `τ` off it
  let u : Q → ℝ := fun q => if q ∈ P.A then b q else min (b q) P.τ
  have hR : Region u P.A P.τ := by
    intro q hq
    show (if q ∈ P.A then b q else min (b q) P.τ) ≤ P.τ
    rw [if_neg hq]; exact min_le_right _ _
  have hM : MarginDisplayed b P.pref P.A P.A₁ P.τ P.δ P.W :=
    ⟨P.A₁_sub, fun q hq => P.scoreR_ge W DP n y hy hmar hq, P.W_le⟩
  have hW : Within b u (P.defectOf (priceR W DP n)) := by
    intro q
    have hd0 := P.defectOf_nonneg (priceR W DP n)
    by_cases hq : q ∈ P.A
    · show |b q - (if q ∈ P.A then b q else min (b q) P.τ)| ≤ _
      rw [if_pos hq, sub_self, abs_zero]; exact hd0
    · show |b q - (if q ∈ P.A then b q else min (b q) P.τ)| ≤ _
      rw [if_neg hq]
      have hle := P.le_defectOf (priceR W DP n) hq
      rw [abs_le]
      constructor
      · have := min_le_left (b q) P.τ; linarith
      · rcases le_total (b q) P.τ with h | h
        · rw [min_eq_left h]; simpa using hd0
        · rw [min_eq_right h]; exact hle
  have := softGate_massOff_le_displayed (A := P.A) (A₁ := P.A₁) (W := P.W) P.δ_pos
    (P.defectOf_nonneg _) P.pref_nonneg P.W_pos hR hM hW
  unfold gate κ
  rw [← hb]
  calc massOff (softGate b P.pref P.τ P.δ) P.A
      ≤ ((∑ q ∈ univ \ P.A, P.pref q) / P.W) * (P.defectOf (priceR W DP n) / P.δ) := this
    _ = (∑ q ∈ univ \ P.A, P.pref q) / P.W / P.δ * P.defectOf (priceR W DP n) := by ring

/-- The gate is a distribution at the market: nonnegative and summing to one. -/
theorem gate_nonneg (b : Fin d → ℝ) (q : Q) : 0 ≤ P.gate b q :=
  div_nonneg (weight_nonneg P.pref_nonneg q) (total_nonneg P.pref_nonneg)

theorem gate_sum_one (y : Fin d → ℚ) (hy : (W.bundle n).Region y)
    (hmar : P.Margins (W.bundle n) (W.tol n)) : ∑ q, P.gate (priceR W DP n) q = 1 := by
  have hM : MarginDisplayed (P.scoreR (priceR W DP n)) P.pref P.A P.A₁ P.τ P.δ P.W :=
    ⟨P.A₁_sub, fun q hq => P.scoreR_ge W DP n y hy hmar hq, P.W_le⟩
  have hZ : 0 < total (P.scoreR (priceR W DP n)) P.pref P.τ P.δ :=
    lt_of_lt_of_le P.W_pos (total_ge_W_displayed P.δ_pos P.pref_nonneg hM)
  unfold gate softGate
  rw [← Finset.sum_div]
  exact div_self hZ.ne'

/-- **The practical certificate at the market**: with the adequacy semantics — losses at most
`εad` on `A` and at most `D` everywhere — the gate's anchored loss is at most
`(D κ) · defect + εad`. -/
theorem practicalCert (y : Fin d → ℚ) (hy : (W.bundle n).Region y)
    (hmar : P.Margins (W.bundle n) (W.tol n)) {lam : Q → ℝ} {εad D : ℝ} (hεad : 0 ≤ εad) (hD : 0 ≤ D)
    (hadequate : ∀ q ∈ P.A, lam q ≤ εad) (hbound : ∀ q, lam q ≤ D) :
    anchoredLoss univ (P.gate (priceR W DP n)) lam ≤
      (D * P.κ) * P.defectOf (priceR W DP n) + (εad + D * 0) := by
  refine adequate_set_route univ P.A (Finset.subset_univ _) (fun q _ => P.gate_nonneg _ q)
    (P.gate_sum_one W DP n y hy hmar) hεad hD hadequate (fun q _ => hbound q) ?_
  rw [add_zero]
  exact P.massOff_le W DP n y hy hmar

end Problem

/-! ## 5. The evaluation of an adapter protocol -/

/-- **An adapter protocol** on an accounted obligation state: the evaluation's declared data
(services, measure, transport, worst loss, intensities, budgets, amplification constant), one
decision problem per service, and the adequacy semantics — the anchored per-response
losses and the adequate-set loss levels. -/
structure AdapterProtocol {Occ Req : Type*} {S : Protocol Occ Req} {anchor : Occ → Req}
    (O : ObligationState S anchor) (d : ℕ) (Q : Type) [Fintype Q] [DecidableEq Q] where
  services : Finset ℕ
  μ : Occ → ℝ
  μ_prob : ∑ e ∈ O.boundary.exposed, μ e = 1
  T : Occ → ℕ → ℝ
  T_nonneg : ∀ e ∈ O.boundary.exposed, ∀ s ∈ services, 0 ≤ T e s
  T_row : ∀ e ∈ O.boundary.exposed, ∑ s ∈ services, T e s ≤ μ e
  /-- The decision problem at each service date. -/
  prob : ℕ → Problem d Q
  /-- The anchored loss of each response at each service: the adequacy semantics. -/
  lam : Req → ℕ → Q → ℝ
  /-- The loss level of the adequate set at each service. -/
  εad : ℕ → ℝ
  /-- The worst loss. -/
  D : ℝ
  /-- The intensity declared at each service. -/
  lamS : ℕ → ℝ
  /-- The work budget at each service. -/
  ρ : ℕ → ℝ
  /-- The amplification constant. -/
  Γ : ℝ

namespace AdapterProtocol

variable {Occ Req : Type*} {S : Protocol Occ Req} {anchor : Occ → Req}
  {O : ObligationState S anchor} {Q : Type} [Fintype Q] [DecidableEq Q]
  (A : AdapterProtocol O d Q)

/-- **The evaluation** the protocol declares, reading the market through the fragment map:
the response at a service is the gate on the displayed scores, the public defect is the
displayed inadequate excess, the loss is the anchored expected loss, and the certificate
constants are `M = D κ`, `ε = εad`. -/
noncomputable def evaluation (ι : Fin d → Sentence) : Evaluation O ℕ where
  services := A.services
  μ := A.μ
  μ_prob := A.μ_prob
  T := A.T
  T_nonneg := A.T_nonneg
  T_row := A.T_row
  Response _ := Q → ℝ
  Pi s market := (A.prob s).gate fun j => market s (ι j)
  loss r s p := anchoredLoss univ p (A.lam r s)
  defect s market := (A.prob s).defectOf fun j => market s (ι j)
  lam := A.lamS
  ρ := A.ρ
  M _ s := A.D * (A.prob s).κ
  ε _ s := A.εad s
  Γ := A.Γ
  D := A.D

/-- **`PracticalUptake` is derived, not assumed.**  At the realized market of a warrant
schedule: feasibility witnesses, certified exclusion and margins at the service dates, the
adequacy semantics, and the protocol's declared constants give the certificate package the
Progress theorem consumes. -/
theorem uptake (W : WarrantSchedule d) (DP : DeductiveProcess)
    (hy : ∀ s ∈ A.services, ∃ y, (W.bundle s).Region y)
    (hex : ∀ s ∈ A.services, (A.prob s).Excludes (W.bundle s))
    (hmar : ∀ s ∈ A.services, (A.prob s).Margins (W.bundle s) (W.tol s))
    (hεad : ∀ s ∈ A.services, 0 ≤ A.εad s) (hD : 0 ≤ A.D)
    (hadequate : ∀ r, ∀ s ∈ A.services, ∀ q ∈ (A.prob s).A, A.lam r s q ≤ A.εad s)
    (hbound : ∀ r s q, A.lam r s q ≤ A.D)
    (hlam : ∀ s ∈ A.services, 0 ≤ A.lamS s) (hlampos : 0 < ∑ s ∈ A.services, A.lamS s)
    (hbudget : ∀ s ∈ A.services, A.lamS s * (((A.prob s).massCap * W.tol s : ℚ) : ℝ) ^ 2 ≤ A.ρ s)
    (hΓ : 0 ≤ A.Γ)
    (hamp : ∀ s ∈ A.services, ∑ e ∈ O.boundary.exposed, A.T e s * (A.D * (A.prob s).κ) ≤
      A.Γ * (A.lamS s / ∑ t ∈ A.services, A.lamS t)) :
    (A.evaluation W.ι).PracticalUptake (W.market DP) where
  defect_nonneg := fun s _ => (A.prob s).defectOf_nonneg _
  practical := by
    intro e _ s hs _
    obtain ⟨y, hy⟩ := hy s hs
    have h := (A.prob s).practicalCert W DP s y hy (hmar s hs) (hεad s hs) hD
      (hadequate (anchor e) s hs) (hbound (anchor e) s)
    simp only [Evaluation.PracticalCert, Evaluation.edgeLoss, evaluation]
    rw [mul_zero, add_zero] at h
    exact h
  lam_nonneg := hlam
  lam_pos := hlampos
  work := by
    intro s hs
    obtain ⟨y, hy⟩ := hy s hs
    have hd := (A.prob s).defectOf_le W DP s y hy (hex s hs)
    have hd0 := (A.prob s).defectOf_nonneg (Problem.priceR W DP s)
    have hcap : (0 : ℝ) ≤ (((A.prob s).massCap * W.tol s : ℚ) : ℝ) := by
      exact_mod_cast mul_nonneg (A.prob s).massCap_nonneg (W.tol_pos s).le
    show A.lamS s * ((A.prob s).defectOf fun j => W.market DP s (W.ι j)) ^ 2 ≤ A.ρ s
    have hsq : ((A.prob s).defectOf fun j => W.market DP s (W.ι j)) ^ 2 ≤
        (((A.prob s).massCap * W.tol s : ℚ) : ℝ) ^ 2 := by
      have : (A.prob s).defectOf (fun j => W.market DP s (W.ι j)) =
          (A.prob s).defectOf (Problem.priceR W DP s) := rfl
      rw [this]
      exact pow_le_pow_left₀ hd0 hd 2
    exact le_trans (mul_le_mul_of_nonneg_left hsq (hlam s hs)) (hbudget s hs)
  Γ_nonneg := hΓ
  amplification := hamp

end AdapterProtocol

/-! ## 6. The consolidated theorem -/

open EnforcedCompiler in
/-- **The warrant Normative Inductor.**

Given a process of normative states `N`, a fragment map, feasibility witnesses and
tolerances; an admission of every date's grounds into the accounted obligation state and
well-formed grounds; a computable deductive process and an effective enforcer (the two
computability inputs); a slack plausible world at every date dominating the compiled rows at
the odds `ρ` (affordability); and an adapter protocol whose service dates carry checked
witnesses, certified exclusion and margins, the adequacy semantics and the declared
constants — then on the augmented deductive market of the compiled schedule:

1. the market is a logical inductor over the deductive process;
2. at every checked date every row of the state's bundle has excess at most the tolerance at
   the displayed price, and every enforced row is a survivor's row — whose occurrence
   realizes an exposed obligation — a structural row, or a pin;
3. at every service date the adapter's mass on inadequate responses is at most `κ` times the
   public defect, which is at most the certificates' mass times the tolerance;
4. the Progress bound holds, its `PracticalUptake` derived from 2 and 3.

The semantic inputs are the admission, the adequacy losses and the declared constants; the
computability inputs are `process` and `hE`. -/
theorem warrant_inductor {Occ Req : Type*} {S : Protocol Occ Req} {anchor : Occ → Req}
    {O : ObligationState S anchor} {Q : Type} [Fintype Q] [DecidableEq Q]
    (N : ℕ → NormState d) (F : FragmentMap d) (wit : ℕ → Fin d → ℚ) (tol : ℕ → ℚ)
    (htol : ∀ n, 0 < tol n)
    (adm : ∀ n, Admission O (N n).grounds) (hwf : ∀ n, (N n).grounds.WellFormed)
    (DP : DeductiveProcess) (process : DeductiveProcessComputation DP)
    (hE : EffectiveEnforcerComputation (schedule N F wit tol htol).enforcer)
    (ρ : ℚ) (hρ : 0 ≤ ρ)
    (hslack : ∀ n, ∃ v' : PCWorld, v'.ConsistentWith (DP.D n) ∧
      ∀ w : PCWorld, w.ConsistentWith (DP.D n) → ∀ t ≤ n, ∀ c ∈ compileAt (N t) (wit t),
        -(seedGap F.ι c.row w) ≤ ρ * seedGap F.ι c.row v')
    (A : AdapterProtocol O d Q)
    (hcheck : ∀ s ∈ A.services, checkCompiled (N s).bundle (wit s) = true)
    (hex : ∀ s ∈ A.services, (A.prob s).Excludes (N s).bundle)
    (hmar : ∀ s ∈ A.services, (A.prob s).Margins (N s).bundle (tol s))
    (hεad : ∀ s ∈ A.services, 0 ≤ A.εad s) (hD : 0 ≤ A.D)
    (hadequate : ∀ r, ∀ s ∈ A.services, ∀ q ∈ (A.prob s).A, A.lam r s q ≤ A.εad s)
    (hbound : ∀ r s q, A.lam r s q ≤ A.D)
    (hlam : ∀ s ∈ A.services, 0 ≤ A.lamS s) (hlampos : 0 < ∑ s ∈ A.services, A.lamS s)
    (hbudget : ∀ s ∈ A.services, A.lamS s * (((A.prob s).massCap * tol s : ℚ) : ℝ) ^ 2 ≤ A.ρ s)
    (hΓ : 0 ≤ A.Γ)
    (hamp : ∀ s ∈ A.services, ∑ e ∈ O.boundary.exposed, A.T e s * (A.D * (A.prob s).κ) ≤
      A.Γ * (A.lamS s / ∑ t ∈ A.services, A.lamS t)) :
    IsLogicalInductor ((schedule N F wit tol htol).market DP) DP ∧
    (∀ n, checkCompiled (N n).bundle (wit n) = true →
      ∀ c ∈ (N n).bundle, excess c.row ((schedule N F wit tol htol).priceVec DP n) ≤ tol n) ∧
    (∀ n, ∀ c ∈ (schedule N F wit tol htol).bundle n,
      (∃ o ∈ (N n).survivors, c.cites = Cite.sub o.id ∧ (adm n).origin o ∈ O.boundary.exposed ∧
        ∀ j, o.cites = .occurrence j → ∃! o', o' ∈ (N n).survivors ∧ o'.id = j) ∨
      (∃ it ∈ (N n).seed.liveStr (N n).docket, c.cites = Cite.str it.id) ∨
      ∃ i, c.cites = Cite.settled i) ∧
    (∀ s ∈ A.services,
      massOff ((A.prob s).gate fun j => (schedule N F wit tol htol).market DP s (F.ι j))
          (A.prob s).A ≤
        (A.prob s).κ * (A.evaluation F.ι).defect s ((schedule N F wit tol htol).market DP) ∧
      (A.evaluation F.ι).defect s ((schedule N F wit tol htol).market DP) ≤
        (((A.prob s).massCap * tol s : ℚ) : ℝ)) ∧
    (A.evaluation F.ι).progress ((schedule N F wit tol htol).market DP) ≤
      (A.evaluation F.ι).modulus + (A.evaluation F.ι).error +
        A.D * (A.evaluation F.ι).residual := by
  set W := schedule N F wit tol htol with hW
  have hbundle : ∀ s ∈ A.services, W.bundle s = (N s).bundle := fun s hs =>
    compileAt_eq_of_check (hcheck s hs)
  have hyW : ∀ s ∈ A.services, ∃ y, (W.bundle s).Region y := fun s hs =>
    ⟨wit s, region_compileAt (hcheck s hs)⟩
  have hexW : ∀ s ∈ A.services, (A.prob s).Excludes (W.bundle s) := fun s hs => by
    rw [hbundle s hs]; exact hex s hs
  have hmarW : ∀ s ∈ A.services, (A.prob s).Margins (W.bundle s) (W.tol s) := fun s hs => by
    rw [hbundle s hs]; exact hmar s hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- 1. preservation
    exact W.isLogicalInductor DP process hE (3 * (ρ : ℝ)) (W.liability DP ρ hρ hslack)
  · -- 2. conformance at checked dates
    intro n hn c hc
    have hy : (W.bundle n).Region (wit n) := region_compileAt hn
    have hc' : c ∈ W.bundle n := by rw [hW, schedule_bundle, compileAt_eq_of_check hn]; exact hc
    exact W.excess_le_tol DP n (wit n) hy hc'
  · -- 2'. provenance of force
    intro n c hc
    rcases mem_compileAt hc with ⟨o, ho, rfl⟩ | ⟨it, hit, rfl⟩ | ⟨i, r, -, rfl⟩
    · refine Or.inl ⟨o, ho, rfl, (adm n).origin_exposed o (survivors_subset _ _ _ ho), ?_⟩
      intro j hj
      exact (hwf n).cited_unique (N n).docket (N n).settlement ho hj
    · exact Or.inr (Or.inl ⟨it, hit, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, rfl⟩)
  · -- 3. the adapter at the market
    intro s hs
    obtain ⟨y, hy⟩ := hyW s hs
    exact ⟨(A.prob s).massOff_le W DP s y hy (hmarW s hs),
      (A.prob s).defectOf_le W DP s y hy (hexW s hs)⟩
  · -- 4. Progress, with uptake derived
    exact (A.evaluation W.ι).progress_bound (W.market DP)
      (A.uptake W DP hyW hexW hmarW hεad hD hadequate hbound hlam hlampos hbudget hΓ hamp)

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.WarrantInductor.NormState
#print axioms Workspace.Normativity.Contrib.WarrantInductor.NormState.survivors
#print axioms Workspace.Normativity.Contrib.WarrantInductor.NormState.seed
#print axioms Workspace.Normativity.Contrib.WarrantInductor.NormState.bundle
#print axioms Workspace.Normativity.Contrib.WarrantInductor.NormState.region
#print axioms Workspace.Normativity.Contrib.WarrantInductor.NormState.interval
#print axioms Workspace.Normativity.Contrib.WarrantInductor.NormState.seed_liveSub
#print axioms Workspace.Normativity.Contrib.WarrantInductor.NormState.region_iff
#print axioms Workspace.Normativity.Contrib.WarrantInductor.NormState.bundle_eq_settledBundle
#print axioms Workspace.Normativity.Contrib.WarrantInductor.NormState.region_iff_settledRegion
#print axioms Workspace.Normativity.Contrib.WarrantInductor.NormState.interval_spec
#print axioms Workspace.Normativity.Contrib.WarrantInductor.NormState.Supported
#print axioms Workspace.Normativity.Contrib.WarrantInductor.NormState.Licensed
#print axioms Workspace.Normativity.Contrib.WarrantInductor.NormState.licence_chain
#print axioms Workspace.Normativity.Contrib.WarrantInductor.NormState.licensed_iff
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Admission
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.WellFormed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.WellFormed.id_inj
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.WellFormed.cited_unique
#print axioms Workspace.Normativity.Contrib.WarrantInductor.compileAt
#print axioms Workspace.Normativity.Contrib.WarrantInductor.compileAt_eq_of_check
#print axioms Workspace.Normativity.Contrib.WarrantInductor.compileAt_eq_nil
#print axioms Workspace.Normativity.Contrib.WarrantInductor.region_compileAt
#print axioms Workspace.Normativity.Contrib.WarrantInductor.FragmentMap
#print axioms Workspace.Normativity.Contrib.WarrantInductor.schedule
#print axioms Workspace.Normativity.Contrib.WarrantInductor.schedule_bundle
#print axioms Workspace.Normativity.Contrib.WarrantInductor.schedule_ι
#print axioms Workspace.Normativity.Contrib.WarrantInductor.schedule_tol
#print axioms Workspace.Normativity.Contrib.WarrantInductor.mem_compileAt
#print axioms Workspace.Normativity.Contrib.WarrantInductor.CitedFunctional
#print axioms Workspace.Normativity.Contrib.WarrantInductor.CitedFunctional.CitesLive
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.scoreR
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.scoreR_cast
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.gate
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.defectOf
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.defectOf_nonneg
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.le_defectOf
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.κ
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.massCap
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.massCap_nonneg
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.Excludes
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.Margins
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.priceR
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.priceR_eq_market
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.scoreR_le
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.scoreR_ge
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.defectOf_le
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.massOff_le
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.gate_nonneg
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.gate_sum_one
#print axioms Workspace.Normativity.Contrib.WarrantInductor.Problem.practicalCert
#print axioms Workspace.Normativity.Contrib.WarrantInductor.AdapterProtocol
#print axioms Workspace.Normativity.Contrib.WarrantInductor.AdapterProtocol.evaluation
#print axioms Workspace.Normativity.Contrib.WarrantInductor.AdapterProtocol.uptake
#print axioms Workspace.Normativity.Contrib.WarrantInductor.warrant_inductor

end Workspace.Normativity.Contrib.WarrantInductor