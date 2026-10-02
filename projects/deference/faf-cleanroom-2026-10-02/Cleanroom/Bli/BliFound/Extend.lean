import Cleanroom.Bli.BliFound.Tags
import LogicalInduction.Construction.Conditioning.Presentation
import LogicalInduction.Construction.DeductiveDovetail

/-!
# `bli-found` · Extend: the decided-atom extension and its conservativity (anson-012)

**D2 / T3** of the mandate: the one process combinator every ledger / state / projection package
of the run uses — a *literal schedule* over fresh atoms (`Tags.freshAtom`) adjoined, stage by
stage, to a base FAF `DeductiveProcess` through FAF's own `DeductiveProcess.union` — and the
theorems that make it safe to use:

* `literalProcess_consistent`: a *functional* schedule (never both an atom and its negation)
  has a consistent world at every stage;
* `extendBy_consistentWith` / `extendBy_hworld`: every world consistent with a stage of a base
  process that is *free of the schedule's atoms* extends, by overriding the fresh atoms only, to a
  world consistent with the same stage of the extension — so `hworld` is inherited;
* `extendBy_decides_iff` / `extendBy_decidesTheory_iff` — **conservativity**: for a sentence free
  of the schedule's atoms, the extension decides it (semantically: it holds in every world
  consistent with the stage / with the whole theory) iff the base does. This is anson-012's
  "`PC(Γ⁺)↾𝓛 = PC(Γ)`; `D⁺` decides no new `𝓛`-sentence" in FAF's semantic rendering: FAF's
  `DeductiveProcess` has no closure condition (stages are arbitrary nondecreasing finite sets),
  so "decided" is read as `∀ v, ConsistentWithTheory → Holds`, not as stage membership
  (membership conservativity would be trivially true and useless). A *variant*, not a weakening
  (Known issue 7).
* `extendBy_computable`: computability transports through
  `DeductiveProcessComputation.union_toComputable` and `ComputableDeductiveProcess.ofEncodePrim`,
  given a primitive recursive *list enumeration* of the schedule.

The schedule is a `Finset`-valued monotone family (`LiteralSchedule`), as the mandate asks; its
computability certificate is a primitive recursive list family enumerating each stage (Mathlib
has no `Primcodable (Finset _)`; FAF's own stage encoders reduce to lists the same way through
`encode_stage_prim_of_list`).

Sources: [[anson-inventory]] 012; [[bli-paper-inventory]] 038; mandate D2/T3.
-/

namespace Cleanroom.Bli.BliFound

open LogicalInduction LO.Propositional

/-! ## Literals and schedules -/

/-- The literal named by a schedule entry `(family, payload, polarity)`: the fresh atom when the
polarity is `true`, its negation otherwise.
Source: mandate D2
Kind: D
Fidelity: n/a -/
def literalOf (x : ℕ × ℕ × Bool) : Sentence :=
  cond x.2.2 (freshAtom x.1 x.2.1) (∼freshAtom x.1 x.2.1)

/-- `literalOf_true`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma literalOf_true (f p : ℕ) : literalOf (f, p, true) = freshAtom f p := rfl
/-- `literalOf_false`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma literalOf_false (f p : ℕ) : literalOf (f, p, false) = ∼freshAtom f p := rfl

/-- A **literal schedule**: at stage `s`, the finite set of `(family, payload, polarity)` triples
whose literals are adjoined; monotone in `s` (a `DeductiveProcess` needs `mono`).
Source: mandate D2 (anson-012, bli-paper-038)
Kind: D
Fidelity: n/a -/
structure LiteralSchedule where
  /-- The entries adjoined by stage `s`. -/
  lits : ℕ → Finset (ℕ × ℕ × Bool)
  /-- Entries are never withdrawn. -/
  mono : ∀ s, lits s ⊆ lits (s + 1)

namespace LiteralSchedule

variable (L : LiteralSchedule)

/-- `mono_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mono_le {s t : ℕ} (h : s ≤ t) : L.lits s ⊆ L.lits t := by
  induction t, h using Nat.le_induction with
  | base => exact fun x hx => hx
  | succ t _ ih => exact fun x hx => L.mono t (ih hx)

/-- **Functionality**: no stage carries both an atom and its negation. Without it every stage
can be unsatisfiable, and `isLogicalInductor_of_stage_unsatisfiable` would make every market an
inductor over the extension (mandate T3 trap (i)).
Source: mandate D2
Kind: D
Fidelity: n/a -/
def Functional : Prop :=
  ∀ s f p, ¬ ((f, p, true) ∈ L.lits s ∧ (f, p, false) ∈ L.lits s)

/-- The set of atom indices the schedule ever touches.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def atoms : Set ℕ := {a | ∃ s x, x ∈ L.lits s ∧ a = freshAtomCode x.1 x.2.1}

/-- The families the schedule ever uses.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def families : Set ℕ := {f | ∃ s x, x ∈ L.lits s ∧ x.1 = f}

/-- `freshAtomCode_mem_atoms`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshAtomCode_mem_atoms {s : ℕ} {x : ℕ × ℕ × Bool} (hx : x ∈ L.lits s) :
    freshAtomCode x.1 x.2.1 ∈ L.atoms := ⟨s, x, hx, rfl⟩

/-- Functionality across stages: a positive and a negative entry for the same `(f, p)` cannot
appear at any two stages.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Functional.not_both {L : LiteralSchedule} (hL : L.Functional) {s t f p : ℕ}
    (hpos : (f, p, true) ∈ L.lits s) (hneg : (f, p, false) ∈ L.lits t) : False :=
  hL (max s t) f p ⟨L.mono_le (le_max_left s t) hpos, L.mono_le (le_max_right s t) hneg⟩

end LiteralSchedule

/-! ## The literal process and the extension -/

/-- **The literal process** of a schedule: stage `s` is the set of literals of `L.lits s`.
Source: mandate D2 (anson-012, bli-paper-038)
Kind: D
Fidelity: exact -/
def literalProcess (L : LiteralSchedule) : DeductiveProcess where
  D s := (L.lits s).image literalOf
  mono s := Finset.image_subset_image (L.mono s)

/-- `literalProcess_D`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma literalProcess_D (L : LiteralSchedule) (s : ℕ) :
    (literalProcess L).D s = (L.lits s).image literalOf := rfl

/-- **The decided-atom extension**: the base process with the literal process adjoined, stage by
stage, through FAF's `DeductiveProcess.union`.
Source: mandate D2 (anson-012)
Kind: D
Fidelity: exact -/
def extendBy (DP : DeductiveProcess) (L : LiteralSchedule) : DeductiveProcess :=
  DP.union (literalProcess L)

/-- `extendBy_D`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma extendBy_D (DP : DeductiveProcess) (L : LiteralSchedule) (n : ℕ) :
    (extendBy DP L).D n = DP.D n ∪ (L.lits n).image literalOf := rfl

/-! ## Freeness of the base -/

/-- `φ` mentions no atom the schedule touches.
Source: mandate D2
Kind: D
Fidelity: n/a -/
def FreeOf (L : LiteralSchedule) (φ : Sentence) : Prop :=
  ∀ a ∈ sentenceAtomCodes φ, a ∉ L.atoms

/-- No stage of `DP` mentions an atom the schedule touches.
Source: mandate D2
Kind: D
Fidelity: n/a -/
def ProcessFreeOf (L : LiteralSchedule) (DP : DeductiveProcess) : Prop :=
  ∀ k, ∀ φ ∈ DP.D k, FreeOf L φ

/-- A sentence tag-free for every family the schedule uses is free of the schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma FreeOf.of_tagFree {L : LiteralSchedule} {φ : Sentence}
    (h : ∀ f ∈ L.families, TagFreeSentence (cleanroomBaseTag + f) φ) : FreeOf L φ := by
  rintro a ha ⟨s, x, hx, rfl⟩
  exact h x.1 ⟨s, x, hx, rfl⟩ _ ha (by simp)

/-- A cleanroom-free sentence is free of every schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma FreeOf.of_cleanroomFree {φ : Sentence} (h : CleanroomFreeSentence φ) (L : LiteralSchedule) :
    FreeOf L φ := by
  rintro a ha ⟨s, x, hx, rfl⟩
  have := h _ ha
  simp [cleanroomBaseTag] at this

/-- A cleanroom-free process is free of every schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ProcessFreeOf.of_cleanroomFree {DP : DeductiveProcess} (h : CleanroomFreeProcess DP)
    (L : LiteralSchedule) : ProcessFreeOf L DP :=
  fun k φ hφ => FreeOf.of_cleanroomFree (h k φ hφ) L

/-- A process tag-free for every family the schedule uses is free of the schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ProcessFreeOf.of_tagFree {DP : DeductiveProcess} {L : LiteralSchedule}
    (h : ∀ f ∈ L.families, TagFreeProcess (cleanroomBaseTag + f) DP) : ProcessFreeOf L DP :=
  fun k φ hφ => FreeOf.of_tagFree fun f hf => h f hf k φ hφ

/-! ## The override world -/

open Classical in
/-- The world that assigns every scheduled atom the polarity the schedule gives it (at whatever
stage), and agrees with `v` everywhere else. With a functional schedule the polarity is
well defined; this is the `v'` of the mandate's conservativity (i).
Source: mandate D2
Kind: D
Fidelity: n/a -/
noncomputable def override (L : LiteralSchedule) (v : PCWorld) : PCWorld :=
  fun a =>
    if ∃ s f p, (f, p, true) ∈ L.lits s ∧ a = freshAtomCode f p then True
    else if ∃ s f p, (f, p, false) ∈ L.lits s ∧ a = freshAtomCode f p then False
    else v a

/-- Outside the schedule's atoms, `override` agrees with `v`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma override_agree (L : LiteralSchedule) (v : PCWorld) {a : ℕ} (ha : a ∉ L.atoms) :
    (override L v a ↔ v a) := by
  have h1 : ¬ ∃ s f p, (f, p, true) ∈ L.lits s ∧ a = freshAtomCode f p := by
    rintro ⟨s, f, p, hx, rfl⟩
    exact ha ⟨s, (f, p, true), hx, rfl⟩
  have h2 : ¬ ∃ s f p, (f, p, false) ∈ L.lits s ∧ a = freshAtomCode f p := by
    rintro ⟨s, f, p, hx, rfl⟩
    exact ha ⟨s, (f, p, false), hx, rfl⟩
  simp only [override, h1, h2, if_false]

/-- `override` holds every scheduled literal (functional schedule).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma override_holds_literal {L : LiteralSchedule} (hL : L.Functional) (v : PCWorld) {s : ℕ}
    {x : ℕ × ℕ × Bool} (hx : x ∈ L.lits s) : (override L v).Holds (literalOf x) := by
  obtain ⟨f, p, b⟩ := x
  cases b
  · -- negative literal: the positive branch is ruled out by functionality
    have h1 : ¬ ∃ s' f' p', (f', p', true) ∈ L.lits s' ∧
        freshAtomCode f p = freshAtomCode f' p' := by
      rintro ⟨s', f', p', hx', heq⟩
      obtain ⟨rfl, rfl⟩ := freshAtomCode_inj.mp heq
      exact hL.not_both hx' hx
    have h2 : ∃ s' f' p', (f', p', false) ∈ L.lits s' ∧
        freshAtomCode f p = freshAtomCode f' p' := ⟨s, f, p, hx, rfl⟩
    rw [literalOf_false, PCWorld.holds_neg, freshAtom, PCWorld.holds_atom]
    simp only [override, h1, h2, if_false, if_true, not_false_eq_true]
  · have h1 : ∃ s' f' p', (f', p', true) ∈ L.lits s' ∧
        freshAtomCode f p = freshAtomCode f' p' := ⟨s, f, p, hx, rfl⟩
    rw [literalOf_true, freshAtom, PCWorld.holds_atom]
    simp only [override, h1, if_true]

/-- `override` is consistent with every stage of the literal process (functional schedule).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma override_consistentWith_literalProcess {L : LiteralSchedule} (hL : L.Functional)
    (v : PCWorld) (s : ℕ) : (override L v).ConsistentWith ((literalProcess L).D s) := by
  intro φ hφ
  rw [literalProcess_D, Finset.mem_image] at hφ
  obtain ⟨x, hx, rfl⟩ := hφ
  exact override_holds_literal hL v hx

/-- On a sentence free of the schedule, `override L v` and `v` agree.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma override_holds_iff (L : LiteralSchedule) (v : PCWorld) {φ : Sentence} (hφ : FreeOf L φ) :
    (override L v).Holds φ ↔ v.Holds φ :=
  PCWorld.holds_congr_atomCodes φ fun a ha => override_agree L v (hφ a ha)

/-! ## T3: consistency, `hworld` inheritance, conservativity -/

/-- **`literalProcess_consistent`.** A functional schedule has a consistent world at every stage,
built directly from the literal table (the override of any world).
Source: mandate T3
Kind: P
Fidelity: exact
Hyps: (a) functionality is a hypothesis on the schedule, discharged by every instance -/
theorem literalProcess_consistent {L : LiteralSchedule} (hL : L.Functional) (s : ℕ) :
    ∃ v : PCWorld, v.ConsistentWith ((literalProcess L).D s) :=
  ⟨override L (fun _ => True), override_consistentWith_literalProcess hL _ s⟩

/-- **Conservativity (i), stage form.** Every world consistent with stage `n` of a base process
free of the schedule extends — by overriding the scheduled atoms only, agreeing with `v` on every
other atom — to a world consistent with stage `n` of the extension.
Source: mandate D2/T3 (anson-012)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem extendBy_consistentWith {DP : DeductiveProcess} {L : LiteralSchedule}
    (hL : L.Functional) (hDP : ProcessFreeOf L DP) {v : PCWorld} {n : ℕ}
    (hv : v.ConsistentWith (DP.D n)) :
    (override L v).ConsistentWith ((extendBy DP L).D n) ∧
      ∀ a, a ∉ L.atoms → (override L v a ↔ v a) := by
  refine ⟨?_, fun a ha => override_agree L v ha⟩
  rw [extendBy, PCWorld.consistentWith_union_iff]
  refine ⟨fun φ hφ => ?_, override_consistentWith_literalProcess hL v n⟩
  exact (override_holds_iff L v (hDP n φ hφ)).mpr (hv φ hφ)

/-- **Conservativity (i), theory form.** A world consistent with every stage of the base extends
to one consistent with every stage of the extension.
Source: mandate D2/T3 (anson-012)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem extendBy_consistentWithTheory {DP : DeductiveProcess} {L : LiteralSchedule}
    (hL : L.Functional) (hDP : ProcessFreeOf L DP) {v : PCWorld}
    (hv : v.ConsistentWithTheory DP) :
    (override L v).ConsistentWithTheory (extendBy DP L) :=
  fun n => (extendBy_consistentWith hL hDP (hv n)).1

/-- **Conservativity (iii): `hworld` is inherited.** If every stage of the base has a consistent
world, so does every stage of the extension.
Source: mandate D2/T3 (anson-012)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem extendBy_hworld {DP : DeductiveProcess} {L : LiteralSchedule}
    (hL : L.Functional) (hDP : ProcessFreeOf L DP)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((extendBy DP L).D n) := by
  intro n
  obtain ⟨v, hv⟩ := h n
  exact ⟨override L v, (extendBy_consistentWith hL hDP hv).1⟩

/-- **Conservativity (ii), stage form.** For a sentence free of the schedule's atoms: it holds in
every world consistent with stage `n` of the extension iff it holds in every world consistent
with stage `n` of the base. "Decided" is FAF's semantic reading (`∀ v, ConsistentWith → Holds`),
not stage membership — see the module docstring.
Source: mandate D2/T3 (anson-012, Known issue 7)
Kind: P
Fidelity: variant: semantic "decided" in place of anson-012's Γ-complete-process membership
Hyps: (a) -/
theorem extendBy_decides_iff {DP : DeductiveProcess} {L : LiteralSchedule}
    (hL : L.Functional) (hDP : ProcessFreeOf L DP) {φ : Sentence} (hφ : FreeOf L φ) (n : ℕ) :
    (∀ v : PCWorld, v.ConsistentWith ((extendBy DP L).D n) → v.Holds φ) ↔
      (∀ v : PCWorld, v.ConsistentWith (DP.D n) → v.Holds φ) := by
  constructor
  · intro h v hv
    have := h (override L v) (extendBy_consistentWith hL hDP hv).1
    exact (override_holds_iff L v hφ).mp this
  · intro h v hv
    exact h v ((PCWorld.consistentWith_union_iff v DP (literalProcess L) n).mp hv).1

/-- **Conservativity (ii), theory form**: `D⁺` decides no new `𝓛`-sentence — for `φ` free of the
schedule's atoms, `φ` holds in every completed-theory world of the extension iff it does in every
completed-theory world of the base.
Source: mandate D2/T3 (anson-012, Known issue 7)
Kind: P
Fidelity: variant: semantic "decided" in place of anson-012's Γ-complete-process membership
Hyps: (a) -/
theorem extendBy_decidesTheory_iff {DP : DeductiveProcess} {L : LiteralSchedule}
    (hL : L.Functional) (hDP : ProcessFreeOf L DP) {φ : Sentence} (hφ : FreeOf L φ) :
    (∀ v : PCWorld, v.ConsistentWithTheory (extendBy DP L) → v.Holds φ) ↔
      (∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds φ) := by
  constructor
  · intro h v hv
    have := h (override L v) (extendBy_consistentWithTheory hL hDP hv)
    exact (override_holds_iff L v hφ).mp this
  · intro h v hv
    exact h v (PCWorld.consistentWithTheory_union_left hv)

/-! ## Computability transport -/

/-- `Formula.atom` is primitive recursive on codes (Foundation's `toNat` of an atom is
`Nat.pair 1 c + 1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sentenceAtom_prim : Primrec fun c : ℕ => (Formula.atom c : Sentence) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) Primrec.id)).of_eq
    fun _ => rfl

/-- `freshAtomCode_prim`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshAtomCode_prim : Primrec fun x : ℕ × ℕ × Bool => freshAtomCode x.1 x.2.1 :=
  Primrec₂.natPair.comp (Primrec.nat_add.comp (Primrec.const cleanroomBaseTag) Primrec.fst)
    (Primrec.fst.comp Primrec.snd)

/-- `freshAtom_prim`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshAtom_prim : Primrec fun x : ℕ × ℕ × Bool => freshAtom x.1 x.2.1 :=
  sentenceAtom_prim.comp freshAtomCode_prim

/-- `literalOf_prim`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma literalOf_prim : Primrec literalOf :=
  Primrec.cond (Primrec.snd.comp Primrec.snd) freshAtom_prim (sentenceNeg_prim.comp freshAtom_prim)

/-- A stage of the literal process, given a list enumerating the schedule's entries, is the
`toFinset` of the mapped list.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma literalProcess_D_eq_toFinset (L : LiteralSchedule) (enum : ℕ → List (ℕ × ℕ × Bool))
    (henum : ∀ s, (enum s).toFinset = L.lits s) (s : ℕ) :
    (literalProcess L).D s = ((enum s).map literalOf).toFinset := by
  ext φ
  simp only [literalProcess_D, Finset.mem_image, List.mem_toFinset, List.mem_map, ← henum s]

/-- The literal process is computable given a primitive recursive list enumeration of the
schedule's stages.
Source: mandate D2/T3
Kind: C
Fidelity: exact
Hyps: (a) the enumeration certificate is the dependents' data -/
theorem literalProcess_computable (L : LiteralSchedule) (enum : ℕ → List (ℕ × ℕ × Bool))
    (henum : ∀ s, (enum s).toFinset = L.lits s) (hprim : Primrec enum) :
    ComputableDeductiveProcess (literalProcess L) :=
  ComputableDeductiveProcess.ofEncodePrim
    (encode_stage_prim_of_list (Primrec.list_map hprim (literalOf_prim.comp Primrec.snd).to₂)
      (literalProcess_D_eq_toFinset L enum henum))

/-- **`extendBy_computable`.** The extension of a computable process by a primitively
recursively enumerated schedule is computable (FAF's `union_toComputable`).
Source: mandate D2/T3
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem extendBy_computable {DP : DeductiveProcess} (hDP : ComputableDeductiveProcess DP)
    (L : LiteralSchedule) (enum : ℕ → List (ℕ × ℕ × Bool))
    (henum : ∀ s, (enum s).toFinset = L.lits s) (hprim : Primrec enum) :
    ComputableDeductiveProcess (extendBy DP L) :=
  DeductiveProcessComputation.union_toComputable hDP.nonemptyComputation.some
    (literalProcess_computable L enum henum hprim).nonemptyComputation.some

/-! ## Schedules from list enumerations -/

/-- Build a schedule from a list family that is monotone under membership; its enumeration
certificate is the family itself.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def LiteralSchedule.ofList (enum : ℕ → List (ℕ × ℕ × Bool))
    (hmono : ∀ s, ∀ x ∈ enum s, x ∈ enum (s + 1)) : LiteralSchedule where
  lits s := (enum s).toFinset
  mono s := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact hmono s x hx

/-- `LiteralSchedule.ofList_lits`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma LiteralSchedule.ofList_lits (enum : ℕ → List (ℕ × ℕ × Bool))
    (hmono : ∀ s, ∀ x ∈ enum s, x ∈ enum (s + 1)) (s : ℕ) :
    (LiteralSchedule.ofList enum hmono).lits s = (enum s).toFinset := rfl

/-- `extendBy_ofList_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem extendBy_ofList_computable {DP : DeductiveProcess} (hDP : ComputableDeductiveProcess DP)
    (enum : ℕ → List (ℕ × ℕ × Bool)) (hmono : ∀ s, ∀ x ∈ enum s, x ∈ enum (s + 1))
    (hprim : Primrec enum) :
    ComputableDeductiveProcess (extendBy DP (LiteralSchedule.ofList enum hmono)) :=
  extendBy_computable hDP _ enum (fun _ => rfl) hprim

end Cleanroom.Bli.BliFound
