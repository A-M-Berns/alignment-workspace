/-
# Rational models of the legitimacy statement, and which clauses hold on one

Round `prompts/2026-11-10-legitimacy-definition-prosecution/` (`PROMPT-followup-17.md`,
`PROMPT-followup-19.md` §1 A).
`LegitimacyModel.lean` states legitimacy as `Model.Legit`, a predicate on a `Model` with real
weights, scores and ratings.  This file gives a way to build terms of `Model` on which every
clause of `Legit` is decided by the kernel.

**The clauses, named.**  `Model.StartRule`, `Offers`, `Declines`, `EveryF1`, `EveryF2`,
`EveryF2'`, `EveryF3`: the seven conjuncts of `Legit`, each over every decision.
`Model.legit_iff`: `Legit` is their conjunction.  `Model.HasProfile θ η κ p`: each clause holds
iff the corresponding entry of the `Profile` `p` (seven booleans) is `true`.
`Model.HasProfile.legit`, `Model.HasProfile.not_legit`: `Legit` holds on a model whose profile
is all `true` and fails on any other.

**A rational model** (`Case`).  The fields of `Model` with rational values, except that her
state is fixed in form: a `St` records the views she has heard beyond what he has told her
(`heard`), the course of his conduct (`made`), the case, the time, and whether the state was
reached through an offer of his (`byOffer`).  `Case.model` is the `Model` it stands for: her state
in a course of conduct, case and time is `St.init`, with nothing heard and `byOffer` false; being
told a set of views adds it to `heard` (`St.tell`); every rational is cast to a real, and
`rated` and `toldReveals` are booleans.  Every
other field of the `Model` is the field of the `Case` of the same name.  `Case.ρ` and `Case.r`
are arbitrary functions of the state, so a `Case` fixes how her state is written and nothing
about what depends on it.

**The clauses over the rationals.**  `Case.StartRule` to `Case.EveryF3` repeat the definitions
of `LegitimacyModel.lean` with rational arithmetic and bounded quantifiers, so each is
decidable.  `Case.model_*` prove, definition by definition, that the clause of `Case.model` at
the casts of rational tolerances is the rational clause.  `Case.profile θ η κ` evaluates the
seven; `Case.hasProfile`: `Case.model` has that profile.  `Case.hasProfile_std`: the same at
`θ = 1/20`, `η = 1/100`, `κ = 1/10` written as real numerals, the tolerances of
`account/LEGITIMACY_CHECKS.md`.

So for a `Case` `C`, a proof of `C.profile (1/20) (1/100) (1/10) = p` by kernel evaluation
gives `C.model.HasProfile (1/20) (1/100) (1/10) p`: which clauses of `Legit` hold on the term
`C.model` of `Model`, and so whether `Legit` does.

**Not established here.**  Nothing about a `Model` that is not `Case.model` of some `Case`.
The rational clauses are a second writing of the definitions of `LegitimacyModel.lean`; the
`model_*` theorems are what ties them to the first, and a reader checking what a profile means
reads `LegitimacyModel.lean`, not this file.

Names are provisional (AGENTS.md standard 6).
-/
import Workspace.Deference.Contrib.LegitimacyModel

namespace Workspace.Deference.Contrib.LegitimacyModel

open Finset

/-! ## The clauses of `Legit`, named -/

namespace Model

variable {S O V M Ω X I : Type*} [Fintype Ω] [DecidableEq M] [DecidableEq V] [DecidableEq O]
  [DecidableEq I] (D : Model S O V M Ω X I)

/-- Every move that bears an effect on his belief when it starts was in play, and bore an effect
on his belief, at a decision of hers before it started. -/
def StartRule (η : ℝ) : Prop :=
  ∀ m ∈ D.c, D.Bears (D.start m) η m → ∃ t ∈ D.dec, t < D.start m ∧ D.InPlay η t m

/-- At every decision, `offered` is what is on offer. -/
def Offers (θ : ℝ) : Prop := ∀ t ∈ D.dec, D.OnOffer θ t (D.offered t)

/-- At every decision, every decline stands. -/
def Declines (θ : ℝ) : Prop := ∀ t ∈ D.dec, D.DeclineStands θ t

/-- F1 at every decision. -/
def EveryF1 (θ : ℝ) : Prop := ∀ t ∈ D.dec, D.F1 θ t

/-- F2 at every decision. -/
def EveryF2 (η : ℝ) : Prop := ∀ t ∈ D.dec, D.F2 η t

/-- F2′ at every decision. -/
def EveryF2' (η : ℝ) : Prop := ∀ t ∈ D.dec, D.F2' η t

/-- F3 at every decision. -/
def EveryF3 (η κ : ℝ) : Prop := ∀ t ∈ D.dec, D.F3 η κ t

/-- `Legit` is the conjunction of its seven clauses. -/
theorem legit_iff (θ η κ : ℝ) :
    D.Legit θ η κ ↔ D.StartRule η ∧ D.Offers θ ∧ D.Declines θ ∧ D.EveryF1 θ ∧ D.EveryF2 η ∧
      D.EveryF2' η ∧ D.EveryF3 η κ := by
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun t ht => (h t ht).1, fun t ht => (h t ht).2.1, fun t ht => (h t ht).2.2.1,
      fun t ht => (h t ht).2.2.2.1, fun t ht => (h t ht).2.2.2.2.1,
      fun t ht => (h t ht).2.2.2.2.2⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
    exact ⟨h0, fun t ht => ⟨h1 t ht, h2 t ht, h3 t ht, h4 t ht, h5 t ht, h6 t ht⟩⟩

end Model

/-- Which of the seven clauses of `Legit` hold. -/
structure Profile where
  start : Bool
  offers : Bool
  declines : Bool
  f1 : Bool
  f2 : Bool
  f2' : Bool
  f3 : Bool
  deriving DecidableEq, Repr

/-- Every clause holds. -/
def Profile.all : Profile := ⟨true, true, true, true, true, true, true⟩

namespace Model

variable {S O V M Ω X I : Type*} [Fintype Ω] [DecidableEq M] [DecidableEq V] [DecidableEq O]
  [DecidableEq I] (D : Model S O V M Ω X I)

/-- The clauses of `Legit` that hold on `D` are exactly those marked `true` in `p`. -/
def HasProfile (θ η κ : ℝ) (p : Profile) : Prop :=
  (D.StartRule η ↔ p.start = true) ∧ (D.Offers θ ↔ p.offers = true) ∧
    (D.Declines θ ↔ p.declines = true) ∧ (D.EveryF1 θ ↔ p.f1 = true) ∧
    (D.EveryF2 η ↔ p.f2 = true) ∧ (D.EveryF2' η ↔ p.f2' = true) ∧
    (D.EveryF3 η κ ↔ p.f3 = true)

variable {D}

theorem HasProfile.legit {θ η κ : ℝ} (h : D.HasProfile θ η κ Profile.all) : D.Legit θ η κ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  exact (D.legit_iff θ η κ).mpr
    ⟨h0.mpr rfl, h1.mpr rfl, h2.mpr rfl, h3.mpr rfl, h4.mpr rfl, h5.mpr rfl, h6.mpr rfl⟩

theorem HasProfile.not_legit {θ η κ : ℝ} {p : Profile} (h : D.HasProfile θ η κ p)
    (hp : p ≠ Profile.all) : ¬ D.Legit θ η κ := by
  intro hL
  obtain ⟨l0, l1, l2, l3, l4, l5, l6⟩ := (D.legit_iff θ η κ).mp hL
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  apply hp
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := p
  have e0 : p0 = true := h0.mp l0
  have e1 : p1 = true := h1.mp l1
  have e2 : p2 = true := h2.mp l2
  have e3 : p3 = true := h3.mp l3
  have e4 : p4 = true := h4.mp l4
  have e5 : p5 = true := h5.mp l5
  have e6 : p6 = true := h6.mp l6
  subst e0 e1 e2 e3 e4 e5 e6
  rfl

end Model

/-! ## Her state, in a fixed form -/

/-- Her state: the views she has heard beyond what he has told her, the course of his conduct,
the case, the time, and whether the state was reached through an offer of his. -/
structure St (V M Ω : Type) where
  heard : Finset V
  made : Finset M
  case : Ω
  time : ℕ
  byOffer : Bool

namespace St

variable {V M Ω : Type} [DecidableEq V]

/-- Her state in a course of conduct, a case and a time, before anything further is heard. -/
def init (Y : Finset M) (ω : Ω) (t : ℕ) : St V M Ω := ⟨∅, Y, ω, t, false⟩

/-- Her state on being told a set of views. -/
def tell (T : Finset V) (s : St V M Ω) : St V M Ω := ⟨s.heard ∪ T, s.made, s.case, s.time, s.byOffer⟩

theorem tell_empty (s : St V M Ω) : tell ∅ s = s := by
  cases s; simp [tell]

theorem tell_idem (T : Finset V) (s : St V M Ω) : tell T (tell T s) = tell T s := by
  cases s; simp [tell, union_assoc]

end St

/-! ## A rational model -/

/-- The fields of `Model` with rational values, her state being a `St`. -/
structure Case (O V M Ω X I : Type) [Fintype Ω] where
  μ : ℕ → Ω → ℚ
  μ_nonneg : ∀ t ω, 0 ≤ μ t ω
  μ_sum : ∀ t, ∑ ω, μ t ω = 1
  dec : Finset ℕ
  c : Finset M
  start : M → ℕ
  finish : M → ℕ
  opts : Finset M → Ω → ℕ → Finset O
  act : Finset M → Ω → ℕ → O
  course : Finset M → Ω → ℕ → O → X
  items : Finset M → Ω → ℕ → Finset I
  xopts : Finset M → Ω → ℕ → Finset O
  ρ : St V M Ω → X → ℚ
  r : St V M Ω → O → ℚ
  rated : St V M Ω → X → Bool
  views : ℕ → Finset V
  told : ℕ → Finset V
  declined : ℕ → Finset V
  offered : ℕ → Finset V
  rev : ℕ → Ω → Finset V → Finset O
  hearOpt : V → O
  toldBear : V → Finset O
  toldMag : V → ℚ
  toldReveals : V → Bool
  stHeard : ℕ → Ω → Finset V → St V M Ω
  optsHeard : ℕ → Ω → Finset V → Finset O
  known : ℕ → Ω → Finset M
  goesOn : ℕ → Ω → O → Finset M
  herStops : ℕ → Ω → Finset O
  asked : Finset M
  plain : M → Finset M

namespace Case

variable {O V M Ω X I : Type} [Fintype Ω] [DecidableEq M] [DecidableEq V] [DecidableEq O]
  [DecidableEq I] (C : Case O V M Ω X I)

/-- The `Model` a `Case` stands for. -/
noncomputable def model : Model (St V M Ω) O V M Ω X I where
  μ := fun t ω => (C.μ t ω : ℝ)
  μ_nonneg := fun t ω => by exact_mod_cast C.μ_nonneg t ω
  μ_sum := fun t => by exact_mod_cast C.μ_sum t
  dec := C.dec
  c := C.c
  start := C.start
  finish := C.finish
  st := St.init
  opts := C.opts
  act := C.act
  course := C.course
  items := C.items
  xopts := C.xopts
  ρ := fun s x => (C.ρ s x : ℝ)
  r := fun s a => (C.r s a : ℝ)
  rated := fun s x => C.rated s x = true
  views := C.views
  told := C.told
  declined := C.declined
  offered := C.offered
  tell := St.tell
  tell_empty := St.tell_empty
  tell_idem := St.tell_idem
  rev := C.rev
  hearOpt := C.hearOpt
  toldBear := C.toldBear
  toldMag := fun v => (C.toldMag v : ℝ)
  toldReveals := fun v => C.toldReveals v = true
  stHeard := C.stHeard
  optsHeard := C.optsHeard
  known := C.known
  goesOn := C.goesOn
  herStops := C.herStops
  asked := C.asked
  plain := C.plain

/-! ### The definitions of `LegitimacyModel.lean`, over the rationals -/

def untold (t : ℕ) : Finset V := ((C.views t \ C.told t) \ C.declined t) \ C.offered t

def BearingHolds (θ : ℚ) (t : ℕ) (v : V) : Prop :=
  ∀ ω, 0 < C.μ t ω → ∀ T ∈ (C.views t).powerset, v ∈ T →
    (∀ a ∈ C.opts C.c ω t,
      (a ∉ C.toldBear v →
        |C.r (St.tell T (St.init C.c ω t)) a - C.r (St.tell (T.erase v) (St.init C.c ω t)) a| ≤ θ) ∧
      |C.r (St.tell T (St.init C.c ω t)) a - C.r (St.tell (T.erase v) (St.init C.c ω t)) a| ≤
        C.toldMag v + θ) ∧
    ((C.rev t ω T \ C.rev t ω (T.erase v)).Nonempty → C.toldReveals v = true)

def ProperOffer (θ : ℚ) (t : ℕ) (T : Finset V) : Prop :=
  (∀ v ∈ T, C.BearingHolds θ t v ∧ ∀ ω, 0 < C.μ t ω → C.hearOpt v ∈ C.opts C.c ω t) ∧
  ∀ ω, 0 < C.μ t ω → ∀ a ∈ C.opts C.c ω t ∪ C.rev t ω T, (∀ v ∈ T, a ≠ C.hearOpt v) →
    a ∈ C.optsHeard t ω T ∧
    |C.r (C.stHeard t ω T) a - C.r (St.tell T (St.init C.c ω t)) a| ≤ θ

def OnOffer (θ : ℚ) (t : ℕ) (T : Finset V) : Prop :=
  T ⊆ C.views t \ C.told t ∧ (T.Nonempty → C.ProperOffer θ t T) ∧
    ∀ T' ∈ (C.views t \ C.told t).powerset, T'.Nonempty → C.ProperOffer θ t T' → T' ⊆ T

def DeclineStands (θ : ℚ) (t : ℕ) : Prop :=
  ∀ v ∈ C.declined t,
    (∃ t₀ ∈ C.dec, t₀ < t ∧ v ∈ C.offered t₀ ∧
      ∀ ω, 0 < C.μ t ω → C.act C.c ω t₀ ≠ C.hearOpt v) ∧
      C.BearingHolds θ t v

def F1 (θ : ℚ) (t : ℕ) : Prop :=
  ∀ ω, 0 < C.μ t ω → ∀ T ∈ (C.untold t).powerset, T.Nonempty →
    (∀ a ∈ C.opts C.c ω t,
      |C.r (St.tell T (St.init C.c ω t)) a - C.r (St.init C.c ω t) a| ≤ θ) ∧
    (∀ b ∈ C.rev t ω T, ∃ a ∈ C.opts C.c ω t,
      C.r (St.tell T (St.init C.c ω t)) b ≤ C.r (St.tell T (St.init C.c ω t)) a + θ)

def gap (Y : Finset M) (ω : Ω) (t : ℕ) (a : O) : ℚ :=
  C.r (St.init Y ω t) a - C.ρ (St.init Y ω t) (C.course Y ω t a)

def HerDiff [Fintype X] [Fintype O] (η : ℚ) (Y Y' : Finset M) (ω : Ω) (t : ℕ) : Prop :=
  (∃ T ∈ (C.views t).powerset, ∃ x,
    η < |C.ρ (St.tell T (St.init Y ω t)) x - C.ρ (St.tell T (St.init Y' ω t)) x|) ∨
  (∃ a, η < |C.gap Y ω t a - C.gap Y' ω t a|) ∨
  (C.items Y' ω t \ C.items Y ω t).Nonempty ∨
  (C.xopts Y' ω t \ C.xopts Y ω t).Nonempty

def Departs (Y : Finset M) (ω : Ω) (t : ℕ) : Prop :=
  ∃ b ∈ C.opts Y ω t, C.r (St.init Y ω t) (C.act Y ω t) < C.r (St.init Y ω t) b

def wt (u : ℕ) (p : Ω → Prop) [DecidablePred p] : ℚ := ∑ ω, if p ω then C.μ u ω else 0

instance (θ : ℚ) (t : ℕ) (v : V) : Decidable (C.BearingHolds θ t v) := by
  unfold BearingHolds; infer_instance

instance (θ : ℚ) (t : ℕ) (T : Finset V) : Decidable (C.ProperOffer θ t T) := by
  unfold ProperOffer; infer_instance

instance (θ : ℚ) (t : ℕ) (T : Finset V) : Decidable (C.OnOffer θ t T) := by
  unfold OnOffer; infer_instance

instance (θ : ℚ) (t : ℕ) : Decidable (C.DeclineStands θ t) := by
  unfold DeclineStands; infer_instance

instance (θ : ℚ) (t : ℕ) : Decidable (C.F1 θ t) := by
  unfold F1; infer_instance

instance [Fintype X] [Fintype O] (η : ℚ) (Y Y' : Finset M) (ω : Ω) (t : ℕ) :
    Decidable (C.HerDiff η Y Y' ω t) := by
  unfold HerDiff; infer_instance

instance (Y : Finset M) (ω : Ω) (t : ℕ) : Decidable (C.Departs Y ω t) := by
  unfold Departs; infer_instance

section Moves

variable [Fintype X] [Fintype O] [Fintype M]

def Contributes (u : ℕ) (η : ℚ) (G : Finset M) : Prop :=
  ∃ t ∈ C.dec, (∃ ω, 0 < C.μ u ω ∧ C.HerDiff η C.c (C.c \ G) ω t) ∨
    C.wt u (fun ω => C.Departs (C.c \ G) ω t) + η < C.wt u (fun ω => C.Departs C.c ω t)

instance (u : ℕ) (η : ℚ) (G : Finset M) : Decidable (C.Contributes u η G) := by
  unfold Contributes; infer_instance

def Bears (u : ℕ) (η : ℚ) (m : M) : Prop :=
  ∃ G ∈ C.c.powerset, m ∈ G ∧ C.Contributes u η G ∧ ¬ C.Contributes u η (G.erase m)

instance (u : ℕ) (η : ℚ) (m : M) : Decidable (C.Bears u η m) := by
  unfold Bears; infer_instance

def Window (m : M) (t : ℕ) : Prop :=
  t ≤ C.finish m ∧ (C.start m ≤ t ∨ ∀ t' ∈ C.dec, t < t' → C.start m ≤ t')

instance (m : M) (t : ℕ) : Decidable (C.Window m t) := by
  unfold Window; infer_instance

def InPlay (η : ℚ) (t : ℕ) (m : M) : Prop := m ∈ C.c ∧ C.Window m t ∧ C.Bears t η m

instance (η : ℚ) (t : ℕ) (m : M) : Decidable (C.InPlay η t m) := by
  unfold InPlay; infer_instance

def Stops (η : ℚ) (t : ℕ) (ω : Ω) (a : O) : Prop :=
  a ∈ C.opts C.c ω t ∧ a ∈ C.herStops t ω ∧ ∀ m ∈ C.goesOn t ω a, ¬ C.InPlay η t m

instance (η : ℚ) (t : ℕ) (ω : Ω) (a : O) : Decidable (C.Stops η t ω a) := by
  unfold Stops; infer_instance

def F2 (η : ℚ) (t : ℕ) : Prop :=
  ∀ ω, 0 < C.μ t ω → (∀ m, C.InPlay η t m → m ∈ C.known t ω) ∧
    ((∃ m, C.InPlay η t m) → ∃ a ∈ C.opts C.c ω t, C.Stops η t ω a)

instance (η : ℚ) (t : ℕ) : Decidable (C.F2 η t) := by
  unfold F2; infer_instance

def LastBefore (G : Finset M) (t₀ : ℕ) : Prop :=
  t₀ ∈ C.dec ∧ (∀ m ∈ G, t₀ < C.start m) ∧
    ∀ t ∈ C.dec, (∀ m ∈ G, t < C.start m) → t ≤ t₀

instance (G : Finset M) (t₀ : ℕ) : Decidable (C.LastBefore G t₀) := by
  unfold LastBefore; infer_instance

def earlier (t₀ t : ℕ) (ω : Ω) : St V M Ω :=
  St.tell (C.told t \ C.told t₀) (St.init C.c ω t₀)

def Against (Y : Finset M) (t₀ t : ℕ) (ω : Ω) : Prop :=
  ∃ b ∈ C.opts Y ω t,
    C.rated (C.earlier t₀ t ω) (C.course Y ω t (C.act Y ω t)) = true ∧
    C.rated (C.earlier t₀ t ω) (C.course Y ω t b) = true ∧
    C.ρ (C.earlier t₀ t ω) (C.course Y ω t (C.act Y ω t)) <
      C.ρ (C.earlier t₀ t ω) (C.course Y ω t b)

instance (Y : Finset M) (t₀ t : ℕ) (ω : Ω) : Decidable (C.Against Y t₀ t ω) := by
  unfold Against; infer_instance

def toldInstead (G : Finset M) : Finset M := (C.c \ G) ∪ G.biUnion C.plain

def F2' (η : ℚ) (t : ℕ) : Prop :=
  ∀ G ∈ C.c.powerset, G.Nonempty → Disjoint G C.asked →
    ∀ t₀ ∈ C.dec, C.LastBefore G t₀ → t₀ ≤ t →
      C.wt t (fun ω => C.Against C.c t₀ t ω) ≤
        C.wt t (fun ω => C.Against (C.toldInstead G) t₀ t ω) + η

instance (η : ℚ) (t : ℕ) : Decidable (C.F2' η t) := by
  unfold F2'; infer_instance

def PrefersStop (η : ℚ) (t : ℕ) (ω : Ω) : Prop :=
  ∃ a ∈ C.opts C.c ω t, C.Stops η t ω a ∧ ∀ b ∈ C.opts C.c ω t, ¬ C.Stops η t ω b →
    C.r (St.init C.c ω t) b < C.r (St.init C.c ω t) a

instance (η : ℚ) (t : ℕ) (ω : Ω) : Decidable (C.PrefersStop η t ω) := by
  unfold PrefersStop; infer_instance

def F3 (η κ : ℚ) (t : ℕ) : Prop :=
  (∃ m, C.InPlay η t m) →
    (1 - κ) * C.wt t (fun ω => C.PrefersStop η t ω) ≤
      C.wt t (fun ω => C.PrefersStop η t ω ∧ C.Stops η t ω (C.act C.c ω t))

instance (η κ : ℚ) (t : ℕ) : Decidable (C.F3 η κ t) := by
  unfold F3; infer_instance

def StartRule (η : ℚ) : Prop :=
  ∀ m ∈ C.c, C.Bears (C.start m) η m → ∃ t ∈ C.dec, t < C.start m ∧ C.InPlay η t m

def Offers (θ : ℚ) : Prop := ∀ t ∈ C.dec, C.OnOffer θ t (C.offered t)

def Declines (θ : ℚ) : Prop := ∀ t ∈ C.dec, C.DeclineStands θ t

def EveryF1 (θ : ℚ) : Prop := ∀ t ∈ C.dec, C.F1 θ t

def EveryF2 (η : ℚ) : Prop := ∀ t ∈ C.dec, C.F2 η t

def EveryF2' (η : ℚ) : Prop := ∀ t ∈ C.dec, C.F2' η t

def EveryF3 (η κ : ℚ) : Prop := ∀ t ∈ C.dec, C.F3 η κ t

instance (η : ℚ) : Decidable (C.StartRule η) := by unfold StartRule; infer_instance
instance (θ : ℚ) : Decidable (C.Offers θ) := by unfold Offers; infer_instance
instance (θ : ℚ) : Decidable (C.Declines θ) := by unfold Declines; infer_instance
instance (θ : ℚ) : Decidable (C.EveryF1 θ) := by unfold EveryF1; infer_instance
instance (η : ℚ) : Decidable (C.EveryF2 η) := by unfold EveryF2; infer_instance
instance (η : ℚ) : Decidable (C.EveryF2' η) := by unfold EveryF2'; infer_instance
instance (η κ : ℚ) : Decidable (C.EveryF3 η κ) := by unfold EveryF3; infer_instance

/-- Which clauses hold, by evaluation. -/
def profile (θ η κ : ℚ) : Profile :=
  ⟨decide (C.StartRule η), decide (C.Offers θ), decide (C.Declines θ), decide (C.EveryF1 θ),
    decide (C.EveryF2 η), decide (C.EveryF2' η), decide (C.EveryF3 η κ)⟩

end Moves

/-! ### The rational clauses are the clauses of `Case.model` -/

theorem model_untold (t : ℕ) : C.model.untold t = C.untold t := rfl

theorem model_μ_pos (t : ℕ) (ω : Ω) : 0 < C.model.μ t ω ↔ 0 < C.μ t ω := by
  show (0 : ℝ) < ((C.μ t ω : ℚ) : ℝ) ↔ _
  norm_cast

theorem model_bearingHolds (θ : ℚ) (t : ℕ) (v : V) :
    C.model.BearingHolds (θ : ℝ) t v ↔ C.BearingHolds θ t v := by
  simp only [Model.BearingHolds, BearingHolds, model_μ_pos]
  simp only [model, mem_powerset]
  norm_cast

theorem model_properOffer (θ : ℚ) (t : ℕ) (T : Finset V) :
    C.model.ProperOffer (θ : ℝ) t T ↔ C.ProperOffer θ t T := by
  unfold Model.ProperOffer ProperOffer
  simp only [model_bearingHolds, model_μ_pos]
  simp only [model]
  norm_cast

theorem model_onOffer (θ : ℚ) (t : ℕ) (T : Finset V) :
    C.model.OnOffer (θ : ℝ) t T ↔ C.OnOffer θ t T := by
  unfold Model.OnOffer OnOffer
  simp only [model_properOffer, mem_powerset]
  rfl

theorem model_declineStands (θ : ℚ) (t : ℕ) :
    C.model.DeclineStands (θ : ℝ) t ↔ C.DeclineStands θ t := by
  unfold Model.DeclineStands DeclineStands
  simp only [model_bearingHolds, model_μ_pos]
  rfl

theorem model_F1 (θ : ℚ) (t : ℕ) : C.model.F1 (θ : ℝ) t ↔ C.F1 θ t := by
  unfold Model.F1 F1
  rw [model_untold]
  simp only [model_μ_pos]
  simp only [model, mem_powerset]
  norm_cast

theorem model_gap (Y : Finset M) (ω : Ω) (t : ℕ) (a : O) :
    C.model.gap Y ω t a = ((C.gap Y ω t a : ℚ) : ℝ) := by
  simp only [Model.gap, gap, model]
  norm_cast

theorem model_departs (Y : Finset M) (ω : Ω) (t : ℕ) :
    C.model.Departs Y ω t ↔ C.Departs Y ω t := by
  simp only [Model.Departs, Departs, model]
  norm_cast

theorem model_wt (u : ℕ) (P : Ω → Prop) (p : Ω → Prop) [DecidablePred p] (h : ∀ ω, P ω ↔ p ω) :
    C.model.wt u P = ((C.wt u p : ℚ) : ℝ) := by
  classical
  unfold Model.wt wt
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hp : p ω
  · rw [if_pos hp, if_pos ((h ω).mpr hp)]; rfl
  · rw [if_neg hp, if_neg (fun hP => hp ((h ω).mp hP))]; simp

theorem model_herDiff [Fintype X] [Fintype O] (η : ℚ) (Y Y' : Finset M) (ω : Ω) (t : ℕ) :
    C.model.HerDiff (η : ℝ) Y Y' ω t ↔ C.HerDiff η Y Y' ω t := by
  unfold Model.HerDiff HerDiff
  simp only [model_gap]
  simp only [model, mem_powerset]
  norm_cast

theorem model_window (m : M) (t : ℕ) : C.model.Window m t ↔ C.Window m t := Iff.rfl

theorem model_lastBefore (G : Finset M) (t₀ : ℕ) : C.model.LastBefore G t₀ ↔ C.LastBefore G t₀ :=
  Iff.rfl

theorem model_against (Y : Finset M) (t₀ t : ℕ) (ω : Ω) :
    C.model.Against Y t₀ t ω ↔ C.Against Y t₀ t ω := by
  simp only [Model.Against, Against, Model.earlier, earlier, model]
  norm_cast

theorem model_offers (θ : ℚ) : C.model.Offers (θ : ℝ) ↔ C.Offers θ := by
  unfold Model.Offers Offers
  simp only [model_onOffer]
  rfl

theorem model_declines (θ : ℚ) : C.model.Declines (θ : ℝ) ↔ C.Declines θ := by
  unfold Model.Declines Declines
  simp only [model_declineStands]
  rfl

theorem model_everyF1 (θ : ℚ) : C.model.EveryF1 (θ : ℝ) ↔ C.EveryF1 θ := by
  unfold Model.EveryF1 EveryF1
  simp only [model_F1]
  rfl

section Moves

variable [Fintype X] [Fintype O]

theorem model_contributes (u : ℕ) (η : ℚ) (G : Finset M) :
    C.model.Contributes u (η : ℝ) G ↔ C.Contributes u η G := by
  unfold Model.Contributes Contributes
  simp only [model_herDiff]
  rw [show C.model.c = C.c from rfl, show C.model.dec = C.dec from rfl]
  refine exists_congr fun t => and_congr Iff.rfl (or_congr ?_ ?_)
  · refine exists_congr fun ω => and_congr ?_ Iff.rfl
    show (0 : ℝ) < (C.μ u ω : ℝ) ↔ 0 < C.μ u ω
    norm_cast
  · rw [C.model_wt u _ (fun ω => C.Departs (C.c \ G) ω t) (fun ω => C.model_departs _ ω t),
      C.model_wt u _ (fun ω => C.Departs C.c ω t) (fun ω => C.model_departs _ ω t)]
    norm_cast

theorem model_bears (u : ℕ) (η : ℚ) (m : M) :
    C.model.Bears u (η : ℝ) m ↔ C.Bears u η m := by
  unfold Model.Bears Bears
  simp only [model_contributes, mem_powerset]
  rfl

theorem model_inPlay (η : ℚ) (t : ℕ) (m : M) : C.model.InPlay (η : ℝ) t m ↔ C.InPlay η t m := by
  unfold Model.InPlay InPlay
  rw [model_bears, model_window]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨a, c, b⟩
  · rintro ⟨a, b, c⟩; exact ⟨a, c, b⟩

theorem model_stops (η : ℚ) (t : ℕ) (ω : Ω) (a : O) :
    C.model.Stops (η : ℝ) t ω a ↔ C.Stops η t ω a := by
  unfold Model.Stops Stops
  simp only [model_inPlay]
  rfl

theorem model_F2 (η : ℚ) (t : ℕ) : C.model.F2 (η : ℝ) t ↔ C.F2 η t := by
  unfold Model.F2 F2
  simp only [model_inPlay, model_stops, model_μ_pos]
  rfl

theorem model_prefersStop (η : ℚ) (t : ℕ) (ω : Ω) :
    C.model.PrefersStop (η : ℝ) t ω ↔ C.PrefersStop η t ω := by
  unfold Model.PrefersStop PrefersStop
  simp only [model_stops]
  simp only [model]
  norm_cast

omit [Fintype X] [Fintype O] in
theorem model_F2' (η : ℚ) (t : ℕ) : C.model.F2' (η : ℝ) t ↔ C.F2' η t := by
  unfold Model.F2' F2'
  have key : ∀ (Y : Finset M) (t₀ : ℕ),
      C.model.wt t (fun ω => C.model.Against Y t₀ t ω) =
        ((C.wt t (fun ω => C.Against Y t₀ t ω) : ℚ) : ℝ) :=
    fun Y t₀ => C.model_wt t _ _ (fun ω => C.model_against Y t₀ t ω)
  have hT : ∀ G, C.model.toldInstead G = C.toldInstead G := fun _ => rfl
  rw [show C.model.c = C.c from rfl, show C.model.asked = C.asked from rfl]
  simp only [hT, key, model_lastBefore, mem_powerset]
  constructor
  · intro h G hG hne ha t₀ _ h0 hle
    have := h G hG hne ha t₀ h0 hle
    exact_mod_cast this
  · intro h G hG hne ha t₀ h0 hle
    have := h G hG hne ha t₀ h0.1 h0 hle
    exact_mod_cast this

theorem model_F3 [Fintype M] (η κ : ℚ) (t : ℕ) : C.model.F3 (η : ℝ) (κ : ℝ) t ↔ C.F3 η κ t := by
  unfold Model.F3 F3
  simp only [model_inPlay]
  rw [C.model_wt t _ (fun ω => C.PrefersStop η t ω) (fun ω => C.model_prefersStop η t ω),
    C.model_wt t (fun ω => C.model.PrefersStop (η : ℝ) t ω ∧
        C.model.Stops (η : ℝ) t ω (C.model.act C.model.c ω t))
      (fun ω => C.PrefersStop η t ω ∧ C.Stops η t ω (C.act C.c ω t))
      (fun ω => and_congr (C.model_prefersStop η t ω) (C.model_stops η t ω _))]
  norm_cast

theorem model_startRule (η : ℚ) : C.model.StartRule (η : ℝ) ↔ C.StartRule η := by
  unfold Model.StartRule StartRule
  simp only [model_bears, model_inPlay]
  rfl

theorem model_everyF2 (η : ℚ) : C.model.EveryF2 (η : ℝ) ↔ C.EveryF2 η := by
  unfold Model.EveryF2 EveryF2
  simp only [model_F2]
  rfl

omit [Fintype X] [Fintype O] in
theorem model_everyF2' (η : ℚ) : C.model.EveryF2' (η : ℝ) ↔ C.EveryF2' η := by
  unfold Model.EveryF2' EveryF2'
  simp only [model_F2']
  rfl

theorem model_everyF3 [Fintype M] (η κ : ℚ) : C.model.EveryF3 (η : ℝ) (κ : ℝ) ↔ C.EveryF3 η κ := by
  unfold Model.EveryF3 EveryF3
  simp only [model_F3]
  rfl

/-- **The bridge.**  The clauses of `Legit` that hold on `C.model`, at the casts of rational
tolerances, are those the evaluation `C.profile` marks. -/
theorem hasProfile [Fintype M] (θ η κ : ℚ) :
    C.model.HasProfile (θ : ℝ) (η : ℝ) (κ : ℝ) (C.profile θ η κ) := by
  unfold Model.HasProfile profile
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [model_startRule, model_offers, model_declines, model_everyF1, model_everyF2,
      model_everyF2', model_everyF3, decide_eq_true_eq]

/-- The bridge at the tolerances of `account/LEGITIMACY_CHECKS.md`: `θ = 1/20`, `η = 1/100`,
`κ = 1/10`. -/
theorem hasProfile_std [Fintype M] {p : Profile} (h : C.profile (1 / 20) (1 / 100) (1 / 10) = p) :
    C.model.HasProfile (1 / 20) (1 / 100) (1 / 10) p := by
  have := C.hasProfile (1 / 20) (1 / 100) (1 / 10)
  rw [h] at this
  have e1 : ((1 / 20 : ℚ) : ℝ) = 1 / 20 := by norm_num
  have e2 : ((1 / 100 : ℚ) : ℝ) = 1 / 100 := by norm_num
  have e3 : ((1 / 10 : ℚ) : ℝ) = 1 / 10 := by norm_num
  rwa [e1, e2, e3] at this

end Moves

end Case

end Workspace.Deference.Contrib.LegitimacyModel

#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.legit_iff
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.HasProfile.legit
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.HasProfile.not_legit
#print axioms Workspace.Deference.Contrib.LegitimacyModel.St.tell_empty
#print axioms Workspace.Deference.Contrib.LegitimacyModel.St.tell_idem
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_untold
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_μ_pos
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_bearingHolds
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_properOffer
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_onOffer
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_declineStands
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_F1
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_gap
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_departs
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_wt
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_herDiff
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_contributes
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_bears
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_window
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_inPlay
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_stops
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_F2
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_lastBefore
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_against
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_F2'
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_prefersStop
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_F3
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_startRule
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_offers
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_declines
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_everyF1
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_everyF2
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_everyF2'
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.model_everyF3
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.hasProfile
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Case.hasProfile_std
