import Cleanroom.Bli.BliMeasure.Face
import Cleanroom.Bli.BliMeasure.Round
import Cleanroom.Bli.BliTrajectory.Defs

/-!
# `bli-measure` · Measure: the B3 world, the covering horizon, `𝐏_n` (target 0)

**The B3 world** `b3World n h τ v` (`b3Bits` as a `BoolPCWorld`): on a *system* state atom
`⌜𝑸_m = q⌝` (`q` a candidate code of day `m`, `sysState`) it reads the **realized** state for
`m ≤ n` (`q = b3Actual m`), the trajectory's state for `n < m ≤ n + h` (`q = wcode (τ.day m)`),
and `false` beyond the horizon (junk, disclosed); on every other atom it reads the base world `v`.
The base world is a `BoolPCWorld`, not a `FiniteWorld`, so that worlds at different horizons are
comparable without casts.

**The covering horizon.** `Covers n h ψ`: every system state atom of `ψ` has day `≤ n + h` and
every other atom of `ψ` is below `B (n + h)`. Every sentence has one (`exists_covers`, from
`B_unbounded`), `hor n ψ` is the least.

**The mass at a horizon** `b3Mass n h ψ := ∑_τ ∑_u ctrajLaw τ · (τ.last)(φ_u) · [b3World n h τ u ⊨ ψ]`
over the face skeleton started at the rounded table — the weight is the trajectory law times the
last table's world vector, by disintegration (desiderata P4). **Horizon consistency**
(`b3Mass_succ`, `b3Mass_eq_of_covers`): on a covering horizon the mass does not depend on the
horizon — the day-`(n+h+1)` vector restricted to `B (n+h)` atoms averages, under the kernel's
balance on world conjunctions, to the day-`(n+h)` vector. This is exactly what fails for the
table-state design (finding F1).

**`𝐏_n`**: `b3History n ψ := b3Mass n (hor n ψ) ψ`, cast to `ℝ`. `b3StateSystem` is the
`StateSystem` of record (`val m q φ` the marginal of the decoded world vector, on **every**
sentence).
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliFound Cleanroom.Bli.BliTrajectory

variable {DP : DeductiveProcess} (base : CoherentBase DP) (𝓜 : Mesh)

/-! ## States, the realized state, system state atoms -/

/-- **The realized day-`n` state**: the code of the rounded table.
Source: [[bli-measure-mandate]] target 0 (`actual m := code m (roundedTable m)`)
Kind: D
Fidelity: exact -/
noncomputable def b3Actual (n : ℕ) : ℕ := wcode base.𝔅 𝓜 n (roundedTable base 𝓜 n)

/-- The realized state is a candidate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b3Actual_mem (n : ℕ) : b3Actual base 𝓜 n ∈ wstates base.𝔅 𝓜 n :=
  wcode_mem_wstates _ _ (roundedTable_mem_cgrid base 𝓜 n)

/-- Decoding the realized state gives the rounded table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wdecode_b3Actual (n : ℕ) : wdecode base.𝔅 𝓜 n (b3Actual base 𝓜 n) = roundedTable base 𝓜 n :=
  wdecode_wcode _ _ (roundedTable_mem_cgrid base 𝓜 n)

/-- **System state atoms**: the `(day, code)` an atom index reads as, when the code is a candidate
of that day (`bli-trajectory`'s `stateData`, filtered by `wstates`). **Disclosed convention**: a
state-tagged atom whose code is *not* a candidate of its day (e.g. `stateAtom 0 0`, code `90`)
is `none` here, so `b3Bits` reads it from the base world like a propositional atom — `𝐏_n(⌜𝑸_m =
q⌝)` can lie strictly between `0` and `1` for a non-candidate `q`, even for `m ≤ n`. No headline
depends on it (`E5` sums over candidates; `bliDP`'s stage constrains candidates only); the
witness `paper_two_consistent` uses exactly such an atom as its free bit.
Source: none: infrastructure
Kind: D
Fidelity: n/a (convention disclosed) -/
noncomputable def sysState (a : ℕ) : Option (ℕ × ℕ) :=
  match stateData a with
  | some (m, q) => if q ∈ wstates base.𝔅 𝓜 m then some (m, q) else none
  | none => none

/-- The index of a candidate's state atom is a system state atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sysState_of_mem {m q : ℕ} (hq : q ∈ wstates base.𝔅 𝓜 m) :
    sysState base 𝓜 (freshAtomCode stateFamily (Nat.pair m q)) = some (m, q) := by
  unfold sysState
  rw [stateData_freshAtomCode]
  simp [hq]

/-- The index of a non-candidate's state atom is not a system state atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sysState_of_not_mem {m q : ℕ} (hq : q ∉ wstates base.𝔅 𝓜 m) :
    sysState base 𝓜 (freshAtomCode stateFamily (Nat.pair m q)) = none := by
  unfold sysState
  rw [stateData_freshAtomCode]
  simp [hq]

/-- An atom not carrying the state tag is not a system state atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sysState_of_ne_tag {a : ℕ} (h : a.unpair.1 ≠ stateTag) : sysState base 𝓜 a = none := by
  unfold sysState stateData
  rw [if_neg h]

/-- A system state atom reads back a candidate of its day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_wstates_of_sysState {a m q : ℕ} (h : sysState base 𝓜 a = some (m, q)) :
    q ∈ wstates base.𝔅 𝓜 m := by
  unfold sysState at h
  revert h
  cases hs : stateData a with
  | none => intro h; cases h
  | some p =>
      obtain ⟨m', q'⟩ := p
      intro h
      dsimp only at h
      by_cases hq : q' ∈ wstates base.𝔅 𝓜 m'
      · rw [if_pos hq] at h
        have h' := Option.some.inj h
        rw [Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        exact hq
      · rw [if_neg hq] at h; cases h

/-- A system state atom is the state atom of its data.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atom_eq_stateAtom_of_sysState {a m q : ℕ} (h : sysState base 𝓜 a = some (m, q)) :
    Formula.atom a = stateAtom m q := by
  unfold sysState at h
  revert h
  cases hs : stateData a with
  | none => intro h; cases h
  | some p =>
      obtain ⟨m', q'⟩ := p
      intro h
      dsimp only at h
      by_cases hq : q' ∈ wstates base.𝔅 𝓜 m'
      · rw [if_pos hq] at h
        have h' := Option.some.inj h
        rw [Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        exact atom_eq_stateAtom_of_stateData hs
      · rw [if_neg hq] at h; cases h

/-! ## The B3 world -/

/-- **The B3 world's bits**: the realized state on system state atoms of days `≤ n`, the
trajectory's state on days `n < m ≤ n + h`, `false` beyond (junk, disclosed), the base world `v`
on every other atom — including state-tagged atoms whose code is not a candidate of their day
(`sysState` is `none` there; convention disclosed at `sysState`).
Source: [[bli-measure-mandate]] target 0 (`b3World`)
Kind: D
Fidelity: exact (junk `false` beyond the horizon, disclosed; the base part is a `BoolPCWorld`) -/
noncomputable def b3Bits (n h : ℕ) (τ : Traj (wIndex base.𝔅.B) n h) (v : BoolPCWorld) :
    BoolPCWorld := fun a =>
  match sysState base 𝓜 a with
  | some (m, q) =>
      if hmn : m ≤ n then decide (q = b3Actual base 𝓜 m)
      else if hm : m ≤ n + h then
        decide (q = wcode base.𝔅 𝓜 m (τ.day m (not_le.mp hmn) hm))
      else false
  | none => v a

/-- **The B3 world**, as a `PCWorld`.
Source: [[bli-measure-mandate]] target 0 (`b3World`)
Kind: D
Fidelity: exact -/
noncomputable def b3World (n h : ℕ) (τ : Traj (wIndex base.𝔅.B) n h) (v : BoolPCWorld) : PCWorld :=
  toPCWorld (b3Bits base 𝓜 n h τ v)

/-- A non-system atom reads the base world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b3Bits_of_none {n h : ℕ} {τ : Traj (wIndex base.𝔅.B) n h} {v : BoolPCWorld} {a : ℕ}
    (hs : sysState base 𝓜 a = none) : b3Bits base 𝓜 n h τ v a = v a := by
  unfold b3Bits; rw [hs]

/-- A past system state atom reads the realized state.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b3Bits_past {n h : ℕ} {τ : Traj (wIndex base.𝔅.B) n h} {v : BoolPCWorld} {a m q : ℕ}
    (hs : sysState base 𝓜 a = some (m, q)) (hm : m ≤ n) :
    b3Bits base 𝓜 n h τ v a = decide (q = b3Actual base 𝓜 m) := by
  unfold b3Bits; rw [hs]; simp only [dif_pos hm]

/-- A future system state atom within the horizon reads the trajectory's state.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b3Bits_future {n h : ℕ} {τ : Traj (wIndex base.𝔅.B) n h} {v : BoolPCWorld} {a m q : ℕ}
    (hs : sysState base 𝓜 a = some (m, q)) (hm1 : n < m) (hm2 : m ≤ n + h) :
    b3Bits base 𝓜 n h τ v a = decide (q = wcode base.𝔅 𝓜 m (τ.day m hm1 hm2)) := by
  unfold b3Bits; rw [hs]
  simp only [dif_neg (not_le.mpr hm1), dif_pos hm2]

/-- A system state atom beyond the horizon reads `false` (junk).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b3Bits_beyond {n h : ℕ} {τ : Traj (wIndex base.𝔅.B) n h} {v : BoolPCWorld} {a m q : ℕ}
    (hs : sysState base 𝓜 a = some (m, q)) (hm : n + h < m) :
    b3Bits base 𝓜 n h τ v a = false := by
  unfold b3Bits; rw [hs]
  simp only [dif_neg (by omega : ¬ m ≤ n), dif_neg (not_le.mpr hm)]

/-- Two Boolean worlds agreeing on the atoms of `ψ` evaluate `ψ` alike.
Source: FAF `PCWorld.holds_congr_atomCodes`, Boolean form
Kind: L
Fidelity: n/a -/
lemma eval_congr_atomCodes {v v' : BoolPCWorld} (ψ : Sentence)
    (h : ∀ a ∈ sentenceAtomCodes ψ, v a = v' a) : eval v ψ = eval v' ψ := by
  have hh := PCWorld.holds_congr_atomCodes (v := toPCWorld v) (v' := toPCWorld v') ψ
    (fun a ha => by show v a = true ↔ v' a = true; rw [h a ha])
  rw [← eval_eq_true_iff_holds, ← eval_eq_true_iff_holds] at hh
  cases hv : eval v ψ <;> cases hv' : eval v' ψ <;> simp_all

/-- On a state-tag-free sentence the B3 world is the base world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eval_b3Bits_of_tagFree {n h : ℕ} (τ : Traj (wIndex base.𝔅.B) n h) (v : BoolPCWorld)
    {φ : Sentence} (hφ : TagFreeSentence stateTag φ) :
    eval (b3Bits base 𝓜 n h τ v) φ = eval v φ :=
  eval_congr_atomCodes φ fun a ha => b3Bits_of_none base 𝓜 (sysState_of_ne_tag base 𝓜 (hφ a ha))

/-- The B3 world's verdict on a candidate's state atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eval_b3Bits_stateAtom {n h : ℕ} (τ : Traj (wIndex base.𝔅.B) n h) (v : BoolPCWorld)
    (m q : ℕ) :
    eval (b3Bits base 𝓜 n h τ v) (stateAtom m q) =
      b3Bits base 𝓜 n h τ v (freshAtomCode stateFamily (Nat.pair m q)) := rfl

/-! ## Covering horizons -/

/-- **`Covers n h ψ`**: every system state atom of `ψ` has day `≤ n + h`, and every other atom of
`ψ` is below `B (n + h)` — the horizon `h` exposes everything `ψ` talks about.
Source: [[bli-measure-mandate]] target 0 (`hor`: "the least horizon covering every state-atom day
mentioned by `ψ`", plus the base-atom clause the world measure needs)
Kind: D
Fidelity: variant: also covers the base atoms (needed; finding F1) -/
def Covers (n h : ℕ) (ψ : Sentence) : Prop :=
  ∀ a ∈ sentenceAtomCodes ψ,
    (∀ m q, sysState base 𝓜 a = some (m, q) → m ≤ n + h) ∧
    (sysState base 𝓜 a = none → a < base.𝔅.B (n + h))

/-- Covering is monotone in the horizon.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma covers_mono {n h h' : ℕ} {ψ : Sentence} (hc : Covers base 𝓜 n h ψ) (hh : h ≤ h') :
    Covers base 𝓜 n h' ψ := by
  intro a ha
  obtain ⟨h1, h2⟩ := hc a ha
  refine ⟨fun m q hs => (h1 m q hs).trans (by omega), fun hs => ?_⟩
  exact lt_of_lt_of_le (h2 hs) (base.𝔅.B_le (by omega))

/-- A horizon covering an atom.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def coverFor (a : ℕ) : ℕ :=
  match sysState base 𝓜 a with
  | some (m, _) => m
  | none => Classical.choose (base.𝔅.B_unbounded a)

/-- Every sentence has a covering horizon.
Source: none: infrastructure (from `B_unbounded`)
Kind: L
Fidelity: n/a -/
lemma exists_covers (n : ℕ) (ψ : Sentence) : ∃ h, Covers base 𝓜 n h ψ := by
  refine ⟨(sentenceAtomCodes ψ).sup (coverFor base 𝓜), ?_⟩
  intro a ha
  have hle : coverFor base 𝓜 a ≤ (sentenceAtomCodes ψ).sup (coverFor base 𝓜) :=
    Finset.le_sup ha
  constructor
  · intro m q hs
    have : coverFor base 𝓜 a = m := by unfold coverFor; rw [hs]
    omega
  · intro hs
    have hc : coverFor base 𝓜 a = Classical.choose (base.𝔅.B_unbounded a) := by
      unfold coverFor; rw [hs]
    have hspec := Classical.choose_spec (base.𝔅.B_unbounded a)
    rw [← hc] at hspec
    exact lt_of_lt_of_le hspec (base.𝔅.B_le (by omega))

open Classical in
/-- **The horizon of record**: the least horizon covering `ψ` from day `n`.
Source: [[bli-measure-mandate]] target 0 (`hor`)
Kind: D
Fidelity: variant: covers base atoms too (see `Covers`) -/
noncomputable def hor (n : ℕ) (ψ : Sentence) : ℕ := Nat.find (exists_covers base 𝓜 n ψ)

/-- The horizon of record covers.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma covers_hor (n : ℕ) (ψ : Sentence) : Covers base 𝓜 n (hor base 𝓜 n ψ) ψ := by
  classical
  exact Nat.find_spec (exists_covers base 𝓜 n ψ)

/-- The horizon of record is least.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hor_le {n h : ℕ} {ψ : Sentence} (hc : Covers base 𝓜 n h ψ) : hor base 𝓜 n ψ ≤ h := by
  classical
  exact Nat.find_min' (exists_covers base 𝓜 n ψ) hc

/-! ## The mass at a horizon -/

/-- **The B3 weight** of a trajectory and a last-day world: the trajectory law from the rounded
table times the last table's world vector at `u` — the definition by disintegration.
Source: [[bli-measure-mandate]] target 0 (`b3Weight`); [[bli-program-desiderata]] P4
Kind: D
Fidelity: exact -/
noncomputable def b3Weight (n h : ℕ) (τ : Traj (wIndex base.𝔅.B) n h)
    (u : FiniteWorld (base.𝔅.B (n + h))) : ℚ :=
  ctrajLaw (faceSkeleton base.𝔅 𝓜) n h (roundedTable base 𝓜 n) τ *
    (τ.last (roundedTable base 𝓜 n)) (wcSelf (n + h) u)

/-- **The mass of `ψ` at horizon `h`**: the B3 weights of the worlds holding `ψ`.
Source: [[bli-measure-mandate]] target 0 (`b3History` at a horizon)
Kind: D
Fidelity: exact -/
noncomputable def b3Mass (n h : ℕ) (ψ : Sentence) : ℚ :=
  ∑ τ ∈ ctrajGrid (cgrid base.𝔅 𝓜) n h, ∑ u : FiniteWorld (base.𝔅.B (n + h)),
    b3Weight base 𝓜 n h τ u * (if eval (b3Bits base 𝓜 n h τ u.toBoolPCWorld) ψ then 1 else 0)

/-- The B3 weight is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b3Weight_nonneg {n h : ℕ} {τ : Traj (wIndex base.𝔅.B) n h}
    (hτ : τ ∈ ctrajGrid (cgrid base.𝔅 𝓜) n h) (u : FiniteWorld (base.𝔅.B (n + h))) :
    0 ≤ b3Weight base 𝓜 n h τ u :=
  mul_nonneg (ctrajLaw_nonneg _ _ _)
    (vecOf_nonneg base.𝔅 𝓜 (Traj.last_mem (roundedTable_mem_cgrid base 𝓜 n) hτ) u)

/-- The B3 weights sum to one.
Source: [[bli-measure-mandate]] target 1(a) (`𝐏_n ⊤ = 1`)
Kind: L
Fidelity: exact -/
lemma b3Weight_sum (n h : ℕ) :
    ∑ τ ∈ ctrajGrid (cgrid base.𝔅 𝓜) n h, ∑ u : FiniteWorld (base.𝔅.B (n + h)),
      b3Weight base 𝓜 n h τ u = 1 := by
  have hrt := roundedTable_mem_cgrid base 𝓜 n
  calc ∑ τ ∈ ctrajGrid (cgrid base.𝔅 𝓜) n h, ∑ u : FiniteWorld (base.𝔅.B (n + h)),
        b3Weight base 𝓜 n h τ u
      = ∑ τ ∈ ctrajGrid (cgrid base.𝔅 𝓜) n h,
          ctrajLaw (faceSkeleton base.𝔅 𝓜) n h (roundedTable base 𝓜 n) τ := by
        apply Finset.sum_congr rfl
        intro τ hτ
        unfold b3Weight
        rw [← Finset.mul_sum]
        have : ∑ u : FiniteWorld (base.𝔅.B (n + h)),
            (τ.last (roundedTable base 𝓜 n)) (wcSelf (n + h) u) = 1 :=
          vecOf_sum base.𝔅 𝓜 (Traj.last_mem hrt hτ)
        rw [this, mul_one]
    _ = 1 := ctrajLaw_sum_one _ hrt

/-- The mass is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b3Mass_nonneg (n h : ℕ) (ψ : Sentence) : 0 ≤ b3Mass base 𝓜 n h ψ := by
  unfold b3Mass
  apply Finset.sum_nonneg; intro τ hτ
  apply Finset.sum_nonneg; intro u _
  apply mul_nonneg (b3Weight_nonneg base 𝓜 hτ u)
  split_ifs <;> norm_num

/-- The mass is at most one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b3Mass_le_one (n h : ℕ) (ψ : Sentence) : b3Mass base 𝓜 n h ψ ≤ 1 := by
  unfold b3Mass
  calc ∑ τ ∈ ctrajGrid (cgrid base.𝔅 𝓜) n h, ∑ u : FiniteWorld (base.𝔅.B (n + h)),
        b3Weight base 𝓜 n h τ u * (if eval (b3Bits base 𝓜 n h τ u.toBoolPCWorld) ψ then 1 else 0)
      ≤ ∑ τ ∈ ctrajGrid (cgrid base.𝔅 𝓜) n h, ∑ u : FiniteWorld (base.𝔅.B (n + h)),
          b3Weight base 𝓜 n h τ u := by
        apply Finset.sum_le_sum; intro τ hτ
        apply Finset.sum_le_sum; intro u _
        apply mul_le_of_le_one_right (b3Weight_nonneg base 𝓜 hτ u)
        split_ifs <;> norm_num
    _ = 1 := b3Weight_sum base 𝓜 n h

/-- The mass of `⊤` is one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b3Mass_top (n h : ℕ) : b3Mass base 𝓜 n h ⊤ = 1 := by
  unfold b3Mass
  calc ∑ τ ∈ ctrajGrid (cgrid base.𝔅 𝓜) n h, ∑ u : FiniteWorld (base.𝔅.B (n + h)),
        b3Weight base 𝓜 n h τ u * (if eval (b3Bits base 𝓜 n h τ u.toBoolPCWorld) ⊤ then 1 else 0)
      = ∑ τ ∈ ctrajGrid (cgrid base.𝔅 𝓜) n h, ∑ u : FiniteWorld (base.𝔅.B (n + h)),
          b3Weight base 𝓜 n h τ u := by
        apply Finset.sum_congr rfl; intro τ _
        apply Finset.sum_congr rfl; intro u _
        have : eval (b3Bits base 𝓜 n h τ u.toBoolPCWorld) ⊤ = true :=
          (eval_eq_true_iff_holds _ _).mpr (PCWorld.holds_top _)
        rw [this, if_pos rfl, mul_one]
    _ = 1 := b3Weight_sum base 𝓜 n h

/-- The mass at horizon `0`: the rounded measure's mass on the worlds holding `ψ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b3Mass_zero (n : ℕ) (ψ : Sentence) :
    b3Mass base 𝓜 n 0 ψ = ∑ u : FiniteWorld (base.𝔅.B n), measureRound base 𝓜 n u *
      (if eval (b3Bits base 𝓜 n 0 PUnit.unit u.toBoolPCWorld) ψ then 1 else 0) := by
  unfold b3Mass
  rw [sum_ctrajGrid_zero]
  apply Finset.sum_congr rfl; intro u _
  unfold b3Weight
  rw [ctrajLaw_zero, one_mul]
  show (roundedTable base 𝓜 n) (wcSelf n u) * _ = _
  rw [← vecOf_roundedTable base 𝓜 n]
  rfl

/-! ## Horizon consistency -/

/-- The bits at horizon `h+1` and at horizon `h` agree on the atoms of a sentence covered at
horizon `h` (the last-day base world restricted).
Source: none: infrastructure (horizon consistency)
Kind: L
Fidelity: n/a -/
lemma b3Bits_succ_agree {n h : ℕ} {ψ : Sentence} (hc : Covers base 𝓜 n h ψ)
    (τ : Traj (wIndex base.𝔅.B) n h) (Q : Table (wIndex base.𝔅.B) (n + h + 1))
    (u' : FiniteWorld (base.𝔅.B (n + h + 1))) :
    ∀ a ∈ sentenceAtomCodes ψ,
      b3Bits base 𝓜 n (h + 1) (show Traj (wIndex base.𝔅.B) n (h + 1) from (τ, Q))
          u'.toBoolPCWorld a =
        b3Bits base 𝓜 n h τ (restrFW (base.𝔅.B_mono (n + h)) u').toBoolPCWorld a := by
  intro a ha
  obtain ⟨h1, h2⟩ := hc a ha
  cases hs : sysState base 𝓜 a with
  | none =>
      rw [b3Bits_of_none base 𝓜 hs, b3Bits_of_none base 𝓜 hs]
      exact (toBoolPCWorld_restrFW_of_lt _ u' (h2 hs)).symm
  | some p =>
      obtain ⟨m, q⟩ := p
      have hm := h1 m q hs
      by_cases hmn : m ≤ n
      · rw [b3Bits_past base 𝓜 hs hmn, b3Bits_past base 𝓜 hs hmn]
      · have hm1 : n < m := not_le.mp hmn
        rw [b3Bits_future base 𝓜 hs hm1 (by omega), b3Bits_future base 𝓜 hs hm1 hm]
        rw [Traj.day_of_ne τ Q hm1 (by omega) (by omega)]

/-- **Horizon consistency, one step**: on a covering horizon, extending the horizon by one day
does not change the mass. The day-`(n+h+1)` world vectors, averaged under the face kernel
(balanced on the world conjunctions of day `n+h`), restrict to the day-`(n+h)` vector.
Source: [[bli-measure-mandate]] target 0 (horizon consistency); [[bli-program-desiderata]] P4
Kind: P
Fidelity: exact
Hyps: (a) `hc` (the horizon covers `ψ`) -/
theorem b3Mass_succ {n h : ℕ} {ψ : Sentence} (hc : Covers base 𝓜 n h ψ) :
    b3Mass base 𝓜 n (h + 1) ψ = b3Mass base 𝓜 n h ψ := by
  have hrt := roundedTable_mem_cgrid base 𝓜 n
  unfold b3Mass
  rw [sum_ctrajGrid_succ]
  apply Finset.sum_congr rfl
  intro τ hτ
  have hlast : τ.last (roundedTable base 𝓜 n) ∈ cgrid base.𝔅 𝓜 (n + h) := Traj.last_mem hrt hτ
  set rt := roundedTable base 𝓜 n
  set L := ctrajLaw (faceSkeleton base.𝔅 𝓜) n h rt τ
  set κ := (faceSkeleton base.𝔅 𝓜).κ (n + h)
  set f : FiniteWorld (base.𝔅.B (n + h)) → ℚ := fun u =>
    if eval (b3Bits base 𝓜 n h τ u.toBoolPCWorld) ψ then 1 else 0
  -- Step A: rewrite the horizon-(h+1) indicator through the restriction
  have hA : ∀ (Q : Table (wIndex base.𝔅.B) (n + h + 1)) (u' : FiniteWorld (base.𝔅.B (n + h + 1))),
      b3Weight base 𝓜 n (h + 1) (show Traj (wIndex base.𝔅.B) n (h + 1) from (τ, Q)) u' *
        (if eval (b3Bits base 𝓜 n (h + 1) (show Traj (wIndex base.𝔅.B) n (h + 1) from (τ, Q))
            u'.toBoolPCWorld) ψ then 1 else 0) =
      L * κ.law (τ.last rt) Q * (Q (wcSelf (n + h + 1) u') * f (restrFW (base.𝔅.B_mono (n + h)) u')) := by
    intro Q u'
    unfold b3Weight
    rw [eval_congr_atomCodes ψ (b3Bits_succ_agree base 𝓜 hc τ Q u')]
    show L * κ.law (τ.last rt) Q * Q (wcSelf (n + h + 1) u') * _ = _
    ring
  simp only [hA]
  -- Step B: fiberwise over the restriction
  have hB : ∀ Q ∈ cgrid base.𝔅 𝓜 (n + h + 1),
      ∑ u' : FiniteWorld (base.𝔅.B (n + h + 1)),
          Q (wcSelf (n + h + 1) u') * f (restrFW (base.𝔅.B_mono (n + h)) u') =
        ∑ u : FiniteWorld (base.𝔅.B (n + h)), Q (wcAt (Nat.le_succ (n + h)) u) * f u := by
    intro Q hQ
    rw [← Finset.sum_fiberwise (univ : Finset (FiniteWorld (base.𝔅.B (n + h + 1))))
      (restrFW (base.𝔅.B_mono (n + h)))]
    apply Finset.sum_congr rfl
    intro u _
    rw [cgrid_apply_wcAt base.𝔅 𝓜 hQ (Nat.le_succ (n + h)) u, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u' hu'
    rw [Finset.mem_filter] at hu'
    rw [hu'.2]
    rfl
  -- Step C: balance on the world conjunctions
  have hC : ∀ u : FiniteWorld (base.𝔅.B (n + h)),
      ∑ Q ∈ cgrid base.𝔅 𝓜 (n + h + 1), κ.law (τ.last rt) Q * Q (wcAt (Nat.le_succ (n + h)) u) =
        (τ.last rt) (wcSelf (n + h) u) :=
    fun u => κ.sum_law_mul hlast (wcSelf (n + h) u)
  calc ∑ Q ∈ cgrid base.𝔅 𝓜 (n + h + 1), ∑ u' : FiniteWorld (base.𝔅.B (n + h + 1)),
        L * κ.law (τ.last rt) Q * (Q (wcSelf (n + h + 1) u') * f (restrFW (base.𝔅.B_mono (n + h)) u'))
      = ∑ Q ∈ cgrid base.𝔅 𝓜 (n + h + 1), L * κ.law (τ.last rt) Q *
          ∑ u : FiniteWorld (base.𝔅.B (n + h)), Q (wcAt (Nat.le_succ (n + h)) u) * f u := by
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [← Finset.mul_sum, hB Q hQ]
    _ = ∑ u : FiniteWorld (base.𝔅.B (n + h)), L *
          (∑ Q ∈ cgrid base.𝔅 𝓜 (n + h + 1), κ.law (τ.last rt) Q * Q (wcAt (Nat.le_succ (n + h)) u))
            * f u := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro Q _
        apply Finset.sum_congr rfl; intro u _
        ring
    _ = ∑ u : FiniteWorld (base.𝔅.B (n + h)), b3Weight base 𝓜 n h τ u * f u := by
        apply Finset.sum_congr rfl; intro u _
        rw [hC u]
        rfl

/-- **Horizon consistency**: on any horizon covering `ψ`, the mass is the mass at the covering
horizon.
Source: [[bli-measure-mandate]] target 0 (horizon consistency)
Kind: C
Fidelity: exact
Hyps: (a) `hc` -/
theorem b3Mass_eq_of_covers {n h : ℕ} {ψ : Sentence} (hc : Covers base 𝓜 n h ψ) :
    ∀ h', h ≤ h' → b3Mass base 𝓜 n h' ψ = b3Mass base 𝓜 n h ψ := by
  intro h' hh'
  induction h', hh' using Nat.le_induction with
  | base => rfl
  | succ h'' hh'' ih => rw [b3Mass_succ base 𝓜 (covers_mono base 𝓜 hc hh''), ih]

/-! ## `𝐏_n` and the state system of record -/

/-- **`𝐏_n` of record**: the mass at the horizon of record, as a real.
Source: [[bli-measure-mandate]] target 0 (`b3History`); [[bli-program-construction]] §1.1 (B3)
Kind: D
Fidelity: exact -/
noncomputable def b3History : History := fun n ψ => (b3Mass base 𝓜 n (hor base 𝓜 n ψ) ψ : ℝ)

/-- **`𝐏_n` at any covering horizon.**
Source: [[bli-measure-mandate]] target 0 (horizon consistency, the form every target uses)
Kind: C
Fidelity: exact
Hyps: (a) `hc` -/
theorem b3History_eq {n h : ℕ} {ψ : Sentence} (hc : Covers base 𝓜 n h ψ) :
    b3History base 𝓜 n ψ = (b3Mass base 𝓜 n h ψ : ℝ) := by
  unfold b3History
  rw [b3Mass_eq_of_covers base 𝓜 (covers_hor base 𝓜 n ψ) h (hor_le base 𝓜 hc)]

/-- `𝐏_n` is in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b3History_range (n : ℕ) (ψ : Sentence) : 0 ≤ b3History base 𝓜 n ψ ∧ b3History base 𝓜 n ψ ≤ 1 := by
  unfold b3History
  constructor
  · exact_mod_cast b3Mass_nonneg base 𝓜 n _ ψ
  · exact_mod_cast b3Mass_le_one base 𝓜 n _ ψ

/-- **The state system of record**: candidates are the codes of the day's grid, `val m q φ` is the
marginal of the decoded world vector on **every** sentence (a disclosed `variant` of Appendix B's
`Q̂[φ]`, defined only on small `φ`), and the realized state is the code of the rounded table.
**Junk beyond the bound**: `val m q φ` is a price of `φ` for `atomBound φ ≤ B m`; beyond it the
vector's worlds read the atoms `≥ B m` as `false` (`FiniteWorld.toBoolPCWorld`), so the number is
not a price of `φ`. Every headline using `val` carries `atomBound φ ≤ B m` or `φ ∈ smallSet m`.
Source: [[bli-measure-mandate]] target 0 (`coherentStateSystem`); [[bli-program]] §2.3
Kind: D
Fidelity: variant: `val` on every sentence within the bound (the world vector prices everything
there; junk `false`-reading beyond, disclosed); states are world vectors (finding F1) -/
noncomputable def b3StateSystem : StateSystem where
  states := wstates base.𝔅 𝓜
  val m q φ := (wMarginal (vecOf (wdecode base.𝔅 𝓜 m q)) φ : ℝ)
  actual := b3Actual base 𝓜
  actual_mem := b3Actual_mem base 𝓜

/-- Unfolding `val`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma b3StateSystem_val (m q : ℕ) (φ : Sentence) :
    (b3StateSystem base 𝓜).val m q φ = (wMarginal (vecOf (wdecode base.𝔅 𝓜 m q)) φ : ℝ) := rfl

/-- Unfolding `states`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma b3StateSystem_states (m : ℕ) : (b3StateSystem base 𝓜).states m = wstates base.𝔅 𝓜 m := rfl

/-- Unfolding `actual`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma b3StateSystem_actual (m : ℕ) : (b3StateSystem base 𝓜).actual m = b3Actual base 𝓜 m := rfl

/-- The realized state's value is the rounded measure's marginal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b3StateSystem_val_actual (m : ℕ) (φ : Sentence) :
    (b3StateSystem base 𝓜).val m (b3Actual base 𝓜 m) φ = (wMarginal (measureRound base 𝓜 m) φ : ℝ) := by
  rw [b3StateSystem_val, wdecode_b3Actual, vecOf_roundedTable]

end Cleanroom.Bli.BliMeasure
