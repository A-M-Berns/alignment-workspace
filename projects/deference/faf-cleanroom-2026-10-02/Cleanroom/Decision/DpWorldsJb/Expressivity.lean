import Cleanroom.Decision.DpWorldsJb.Defs
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The expressivity lemma (T3): probability-only `cf` plus rigidity vs pair-valued `cf`

**Reading A** (ATTRIBUTION-UNVETTED; the drafting chat's lemma is informal): a finite fine
outcome type `W` with utility `u : W → ℝ`, a coarsening `π : W → Ω` onto the atoms of the
agent's algebra (`Finset Ω`), an actual belief `μ : Dist W` and a supposed belief `μᵃ : Dist W`.
Induced coarse data: `P_s := π_* μ`, `V_s X := E_μ[u | π⁻¹ X]` (`coarseV π μ u`),
`P^a := π_* μᵃ`, the **true** supposed desirability `V^a_true X := E_{μᵃ}[u | π⁻¹ X]`, and the
**rigid** one derived from probability-only data, `V^a_rig X := E_{P^a}[V_s{·} | X]`
(`rigidV π μ μᵃ u`).

* `Dist.toJBPair` (i): any (distribution, atom values) pair is a JB pair with `V = E[· | X]`;
  `rigidPair`: probability-only `cf` plus rigidity embeds into pair-valued `cf`.
* `rigid_eq_true_iff` (ii): rigid = true on every charged event iff no within-atom
  revaluation on any `P^a`-charged atom — an exact identity, but its plain-words reading needs
  the chat's `≪` side condition (every `P^a`-charged atom is `P_s`-charged): at a `μ`-null,
  `μᵃ`-charged atom both sides read the junk value `V_s{ω} = 0/0 = 0`
  (`rigid_eq_true_junk_off_ac`).
* `rigid_faithful_iff_fibres_settle` (iii, the extension): for fixed `(W, u, π)`, rigidity is
  faithful for all pairs `(μ, μᵃ)` (with the chat's `≪` side condition) iff `u` is constant on
  every fibre of `π` — "the algebra is rich enough that atoms settle every value-relevant fact".
* `coarse_smoking_lesion` (iv, N+): on the two-atom algebra `{smoke, ¬smoke}`, `P^a = δ_smoke`
  is forced by success, `V_s(smoke) = -36/5`, `V^a_true(smoke) = -4`, and rigidity returns
  `-36/5` — the EDT news value; the gap is exhibited.

**Reading B** (the purely internal statement, `rigidity_not_surjective`): the rigidity map is not
onto pair-valued `cf` on any algebra with a charged atom — true and trivial (`T`), and not what
the chat means.

All conditional expectations are Lean-total (`x / 0 = 0`). In (i), (iii) and (iv) every
headline hypothesis puts the relevant masses strictly positive, so no junk value is
load-bearing; (ii) is stated without the `≪` side condition and is then true as an identity
because both sides read the same junk value at a `μ`-null atom — it is *meaningful* only under
`≪`, which (iii) carries as a hypothesis (audit r1, N1).
-/

namespace Cleanroom.Decision.DpWorldsJb

noncomputable section

open Classical Finset

section General

variable {α : Type*} [DecidableEq α]

/-- The mass of a weight function on a finset.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def mass (p : α → ℝ) (X : Finset α) : ℝ := ∑ w ∈ X, p w

/-- The conditional expectation `E_p[v | X] = (∑_{w ∈ X} p w · v w) / mass p X` (Lean-total:
`0` when `mass p X = 0`).
Source: [[decision-problems-v2]] §1 Definition 2 (desirability as conditional expectation)
Kind: D
Fidelity: exact where `0 < mass p X`
Hyps: n/a -/
def condExp (p v : α → ℝ) (X : Finset α) : ℝ := (∑ w ∈ X, p w * v w) / mass p X

theorem mass_union (p : α → ℝ) {X Y : Finset α} (h : Disjoint X Y) :
    mass p (X ∪ Y) = mass p X + mass p Y := sum_union h

theorem mass_nonneg {p : α → ℝ} (hp : ∀ w, 0 ≤ p w) (X : Finset α) : 0 ≤ mass p X :=
  sum_nonneg fun w _ => hp w

theorem mass_singleton (p : α → ℝ) (w : α) : mass p {w} = p w := sum_singleton _ _

theorem mass_eq_zero_iff {p : α → ℝ} (hp : ∀ w, 0 ≤ p w) (X : Finset α) :
    mass p X = 0 ↔ ∀ w ∈ X, p w = 0 :=
  sum_eq_zero_iff_of_nonneg fun w _ => hp w

theorem condExp_mul {p v : α → ℝ} {X : Finset α} (hX : 0 < mass p X) :
    mass p X * condExp p v X = ∑ w ∈ X, p w * v w := by
  unfold condExp
  field_simp

theorem sum_mul_eq_zero_of_mass_zero {p : α → ℝ} (hp : ∀ w, 0 ≤ p w) (v : α → ℝ) {X : Finset α}
    (h : mass p X = 0) : ∑ w ∈ X, p w * v w = 0 := by
  apply sum_eq_zero
  intro w hw
  rw [(mass_eq_zero_iff hp X).1 h w hw, zero_mul]

theorem condExp_singleton {p v : α → ℝ} {w : α} (h : 0 < p w) : condExp p v {w} = v w := by
  unfold condExp
  rw [sum_singleton, mass_singleton]
  field_simp

theorem condExp_of_const {p v : α → ℝ} {X : Finset α} {c : ℝ} (hv : ∀ w ∈ X, v w = c)
    (hX : 0 < mass p X) : condExp p v X = c := by
  unfold condExp
  rw [sum_congr rfl fun w hw => by rw [hv w hw], ← sum_mul]
  show mass p X * c / mass p X = c
  field_simp

variable [Fintype α]

/-- A distribution on a finite type: nonnegative weights summing to `1`.
Source: none: infrastructure (finite atomic carrier)
Kind: D
Fidelity: n/a
Hyps: n/a -/
structure Dist (α : Type*) [Fintype α] where
  /-- The weights. -/
  p : α → ℝ
  /-- Nonnegativity. -/
  nonneg : ∀ w, 0 ≤ p w
  /-- Normalization. -/
  sum_one : ∑ w, p w = 1

/-- The probability on `Finset α` of a distribution (`J = ∅`; on a finite algebra designation
is moot).
Source: [[decision-problems-v2]] §1 (finite atomic case)
Kind: D
Fidelity: variant: finite atomic carrier
Hyps: n/a -/
def Dist.toProb (μ : Dist α) : Prob (∅ : Designation (Finset α)) where
  P := mass μ.p
  nonneg X := mass_nonneg μ.nonneg X
  top := μ.sum_one
  add _ _ h := mass_union μ.p h
  cont _ hD := hD.elim

theorem Dist.toProb_apply (μ : Dist α) (X : Finset α) : μ.toProb.P X = mass μ.p X := rfl

/-- **T3(i), general form.** A distribution and a utility on atoms give a JB pair with
`V X := E_μ[v | X]`: the averaging axiom is additivity of `∑_{w ∈ X} p w · v w`.
Source: drafting chat line 2389 (`V^a(X) = E_{cf_s(a)}[V_s(·) | X]`) | dp-core-2-049
Kind: P
Fidelity: variant: finite atomic carrier
Hyps: (a) -/
def Dist.toJBPair (μ : Dist α) (v : α → ℝ) : JBPair (∅ : Designation (Finset α)) where
  P := μ.toProb
  V X := condExp μ.p v X.1
  avg X Y hX hY h := by
    have hX' : 0 < mass μ.p X := hX
    have hY' : 0 < mass μ.p Y := hY
    have hXY : 0 < mass μ.p (X ∪ Y) := by
      rw [mass_union μ.p h]
      linarith
    show mass μ.p (X ∪ Y) * condExp μ.p v (X ∪ Y) =
      mass μ.p X * condExp μ.p v X + mass μ.p Y * condExp μ.p v Y
    rw [condExp_mul hXY, condExp_mul hX', condExp_mul hY', sum_union h]

theorem Dist.toJBPair_V (μ : Dist α) (v : α → ℝ) (X : Finset α) (h : 0 < μ.toProb.P X) :
    (μ.toJBPair v).V ⟨X, h⟩ = condExp μ.p v X := rfl

end General

section Coarsening

variable {W Ω : Type*} [Fintype W] [Fintype Ω] [DecidableEq W] [DecidableEq Ω]

/-- The fibre `π⁻¹ X` of a coarse event.
Source: drafting chat line 2389 ("working finite and atomic") | dp-core-2-049
Kind: D
Fidelity: exact
Hyps: n/a -/
def fibre (π : W → Ω) (X : Finset Ω) : Finset W := univ.filter (fun w => π w ∈ X)

theorem mem_fibre (π : W → Ω) (X : Finset Ω) (w : W) : w ∈ fibre π X ↔ π w ∈ X := by
  simp [fibre]

/-- The pushforward of weights along the coarsening: `(π_* μ) ω = ∑_{π w = ω} μ w`.
Source: drafting chat line 2389
Kind: D
Fidelity: exact
Hyps: n/a -/
def push (π : W → Ω) (μ : W → ℝ) : Ω → ℝ := fun ω => ∑ w ∈ fibre π {ω}, μ w

theorem sum_fibre_eq (π : W → Ω) (f : W → ℝ) (X : Finset Ω) :
    ∑ w ∈ fibre π X, f w = ∑ ω ∈ X, ∑ w ∈ fibre π {ω}, f w := by
  rw [← sum_fiberwise_of_maps_to (g := π) (t := X) (fun w hw => (mem_fibre π X w).1 hw)]
  apply sum_congr rfl
  intro ω hω
  apply sum_congr _ (fun _ _ => rfl)
  ext w
  simp only [mem_filter, mem_fibre, mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨h ▸ hω, h⟩

theorem mass_push (π : W → Ω) (μ : W → ℝ) (X : Finset Ω) :
    mass (push π μ) X = mass μ (fibre π X) := by
  unfold mass push
  rw [sum_fibre_eq]

theorem push_nonneg (π : W → Ω) {μ : W → ℝ} (hμ : ∀ w, 0 ≤ μ w) (ω : Ω) : 0 ≤ push π μ ω :=
  sum_nonneg fun w _ => hμ w

/-- The pushforward distribution.
Source: drafting chat line 2389 (`P_s := π_* μ`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def Dist.pushforward (π : W → Ω) (μ : Dist W) : Dist Ω where
  p := push π μ.p
  nonneg := push_nonneg π μ.nonneg
  sum_one := by
    have := mass_push π μ.p univ
    unfold mass at this
    rw [this]
    have hf : fibre π univ = univ := by
      ext w
      simp [mem_fibre]
    rw [hf]
    exact μ.sum_one

/-- The coarse desirability induced by `(μ, u)`: `V X := E_μ[u | π⁻¹ X]`.
Source: drafting chat line 2389 | dp-core-2-049
Kind: D
Fidelity: exact
Hyps: n/a -/
def coarseV (π : W → Ω) (μ u : W → ℝ) (X : Finset Ω) : ℝ := condExp μ u (fibre π X)

/-- The **rigid** supposed desirability from probability-only data `(P_s, V_s, P^a)`:
`V^a_rig X := E_{P^a}[V_s{·} | X]`, with `V_s{ω} := E_μ[u | π⁻¹{ω}]`.
Source: drafting chat line 2389 ("value-rigidity: `V^a(ω) := V_s(ω)` on charged atoms, whence `V^a(X) = E_{cf_s(a)}[V_s(·) | X]`") | dp-core-2-049
Kind: D
Fidelity: exact
Hyps: n/a -/
def rigidV (π : W → Ω) (μ μa u : W → ℝ) (X : Finset Ω) : ℝ :=
  condExp (push π μa) (fun ω => coarseV π μ u {ω}) X

/-- **T3(i).** Probability-only `cf` plus rigidity embeds into pair-valued `cf`: `(P^a, V^a_rig)`
is a JB pair (and succeeds at `a` whenever `P^a a = 1`).
Source: drafting chat line 2389 | dp-core-2-049
Kind: P
Fidelity: variant: finite atomic carrier (Reading A)
Hyps: (a) -/
def rigidPair (π : W → Ω) (μ μa : Dist W) (u : W → ℝ) : JBPair (∅ : Designation (Finset Ω)) :=
  (μa.pushforward π).toJBPair (fun ω => coarseV π μ.p u {ω})

theorem rigidPair_P (π : W → Ω) (μ μa : Dist W) (u : W → ℝ) (X : Finset Ω) :
    (rigidPair π μ μa u).P.P X = mass (push π μa.p) X := rfl

theorem rigidPair_V (π : W → Ω) (μ μa : Dist W) (u : W → ℝ) (X : Finset Ω)
    (h : 0 < (rigidPair π μ μa u).P.P X) :
    (rigidPair π μ μa u).V ⟨X, h⟩ = rigidV π μ.p μa.p u X := rfl

/-- The fibre-wise decomposition of the true supposed numerator:
`∑_{w ∈ π⁻¹ X} μᵃ w · u w = ∑_{ω ∈ X} P^a{ω} · V^a_true{ω}` (a null atom contributes `0` on both
sides).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem sum_fibre_mul_eq (π : W → Ω) {μa : W → ℝ} (hμa : ∀ w, 0 ≤ μa w) (u : W → ℝ)
    (X : Finset Ω) :
    ∑ w ∈ fibre π X, μa w * u w = ∑ ω ∈ X, push π μa ω * coarseV π μa u {ω} := by
  rw [sum_fibre_eq]
  apply sum_congr rfl
  intro ω _
  by_cases h : 0 < push π μa ω
  · have h' : 0 < mass μa (fibre π {ω}) := h
    show ∑ w ∈ fibre π {ω}, μa w * u w = mass μa (fibre π {ω}) * condExp μa u (fibre π {ω})
    rw [condExp_mul h']
  · have h0 : push π μa ω = 0 := le_antisymm (not_lt.1 h) (push_nonneg π hμa ω)
    rw [h0, zero_mul]
    exact sum_mul_eq_zero_of_mass_zero hμa u h0

/-- **T3(ii), the expressivity lemma pointwise.** Rigidity is faithful on every `P^a`-charged
event iff there is no within-atom revaluation on any `P^a`-charged atom:
`E_{μᵃ}[u | π⁻¹{ω}] = E_μ[u | π⁻¹{ω}]`. Meaningful under the chat's `≪` side condition
(`0 < P^a{ω} → 0 < P_s{ω}`); the identity holds regardless, because at a `μ`-null, `μᵃ`-charged
atom both sides read the same Lean-total junk `E_μ[u | π⁻¹{ω}] = 0/0 = 0`
(`rigid_eq_true_junk_off_ac` exhibits it). (iii) quantifies under `≪`.
Source: drafting chat line 2389 ("then within-atom revaluation is impossible"); [[decision-problems-v2]] Remark 1.2 (line 42: the transport "exists only where there are atoms … has nothing to read off exactly where a supposition moves mass onto the subjectively impossible") | dp-core-2-049
Kind: P
Fidelity: variant: finite atomic carrier, Reading A (ATTRIBUTION-UNVETTED); exact as an identity, meaningful under `≪`
Hyps: (a) -/
theorem rigid_eq_true_iff (π : W → Ω) (μ μa : Dist W) (u : W → ℝ) :
    (∀ X : Finset Ω, 0 < mass (push π μa.p) X → rigidV π μ.p μa.p u X = coarseV π μa.p u X) ↔
      ∀ ω, 0 < push π μa.p ω → coarseV π μa.p u {ω} = coarseV π μ.p u {ω} := by
  constructor
  · intro h ω hω
    have hm : 0 < mass (push π μa.p) {ω} := by rw [mass_singleton]; exact hω
    have := h {ω} hm
    unfold rigidV at this
    rw [condExp_singleton hω] at this
    exact this.symm
  · intro h X hX
    unfold rigidV coarseV
    unfold condExp
    rw [← mass_push]
    congr 1
    rw [sum_fibre_mul_eq π μa.nonneg u X]
    apply sum_congr rfl
    intro ω _
    by_cases hω : 0 < push π μa.p ω
    · rw [h ω hω]
      rfl
    · have h0 : push π μa.p ω = 0 := le_antisymm (not_lt.1 hω) (push_nonneg π μa.nonneg ω)
      rw [h0, zero_mul, zero_mul]

/-- The two-point distribution `½ δ_{w₁} + ½ δ_{w₂}` (for `w₁ ≠ w₂`).
Source: none: infrastructure (the necessity witness of T3(iii))
Kind: D
Fidelity: n/a
Hyps: n/a -/
def twoPoint (w₁ w₂ : W) : Dist W where
  p w := (if w = w₁ then (1 / 2 : ℝ) else 0) + (if w = w₂ then (1 / 2 : ℝ) else 0)
  nonneg w := by split_ifs <;> norm_num
  sum_one := by
    rw [sum_add_distrib, sum_ite_eq', sum_ite_eq']
    simp
    norm_num

/-- The Dirac distribution `δ_{w₁}`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def diracDist (w₁ : W) : Dist W where
  p w := if w = w₁ then 1 else 0
  nonneg w := by split_ifs <;> norm_num
  sum_one := by rw [sum_ite_eq']; simp

/-- `push id μ = μ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem push_id (μ : W → ℝ) (ω : W) : push (id : W → W) μ ω = μ ω := by
  unfold push
  have hf : fibre (id : W → W) {ω} = {ω} := by
    ext w
    simp [mem_fibre]
  rw [hf, sum_singleton]

/-- **What (ii) reads off the `≪` side condition (audit r1, N1).** With `W = Ω = Bool`,
`π = id`, `μ = δ_false`, `μᵃ = δ_true`: the atom `true` is `μᵃ`-charged and `μ`-null, the side
condition fails, `V_s{true} = 0/0 = 0` by Lean's convention, rigidity returns `0` whatever `u` is,
and "rigid = true at `{true}`" is the junk condition `u true = 0`, not "no within-atom
revaluation". So `rigid_eq_true_iff` is exact as an identity and meaningful only under `≪`.
Source: none: infrastructure (audit r1 probes)
Kind: N−
Fidelity: n/a
Hyps: (a) -/
theorem rigid_eq_true_junk_off_ac (u : Bool → ℝ) :
    ¬ (∀ ω, 0 < push (id : Bool → Bool) (diracDist true).p ω →
        0 < push (id : Bool → Bool) (diracDist false).p ω) ∧
    coarseV (id : Bool → Bool) (diracDist false).p u {true} = 0 ∧
    ((rigidV (id : Bool → Bool) (diracDist false).p (diracDist true).p u {true} =
        coarseV (id : Bool → Bool) (diracDist true).p u {true}) ↔ u true = 0) := by
  have hμ : (diracDist false).p true = 0 := by simp [diracDist]
  have hμa : (diracDist true).p true = 1 := by simp [diracDist]
  have hf : fibre (id : Bool → Bool) {true} = {true} := by
    ext w
    simp [mem_fibre]
  have hcoarse0 : coarseV (id : Bool → Bool) (diracDist false).p u {true} = 0 := by
    unfold coarseV condExp mass
    rw [hf, sum_singleton, sum_singleton, hμ]
    simp
  have hrigid : rigidV (id : Bool → Bool) (diracDist false).p (diracDist true).p u {true} = 0 := by
    unfold rigidV
    rw [condExp_singleton (by rw [push_id, hμa]; exact one_pos)]
    exact hcoarse0
  have htrue : coarseV (id : Bool → Bool) (diracDist true).p u {true} = u true := by
    unfold coarseV
    rw [hf]
    exact condExp_singleton (by rw [hμa]; exact one_pos)
  refine ⟨?_, hcoarse0, ?_⟩
  · intro h
    have := h true (by rw [push_id, hμa]; exact one_pos)
    rw [push_id, hμ] at this
    exact lt_irrefl _ this
  · rw [hrigid, htrue]
    exact eq_comm

/-- **T3(iii), the extension of record.** For a fixed fine space `(W, u, π)`, rigidity is
faithful for **all** actual/supposed pairs `(μ, μᵃ)` (with the chat's `≪` side condition: every
`P^a`-charged atom is `P_s`-charged) iff `u` is constant on every fibre of `π` — the atoms of
the coarse algebra settle every value-relevant fact. Necessity: two points of one fibre with
different utilities, `μ` uniform on them and `μᵃ` Dirac on one, exhibit within-atom revaluation.
Source: drafting chat line 2389 ("adequate exactly when the algebra is rich enough that atoms settle every value-relevant fact") | dp-core-2-049; plan §0.4 rule 6
Kind: P
Fidelity: variant: finite atomic carrier, Reading A (ATTRIBUTION-UNVETTED)
Hyps: (a) -/
theorem rigid_faithful_iff_fibres_settle (π : W → Ω) (u : W → ℝ) :
    (∀ μ μa : Dist W, (∀ ω, 0 < push π μa.p ω → 0 < push π μ.p ω) →
        ∀ X : Finset Ω, 0 < mass (push π μa.p) X → rigidV π μ.p μa.p u X = coarseV π μa.p u X) ↔
      ∀ w₁ w₂, π w₁ = π w₂ → u w₁ = u w₂ := by
  constructor
  · intro h w₁ w₂ hπ
    by_contra hne
    have hne' : w₁ ≠ w₂ := fun e => hne (e ▸ rfl)
    let μ := twoPoint w₁ w₂
    let μa := diracDist w₁
    have hpush : ∀ ω, push π μa.p ω = if π w₁ = ω then 1 else 0 := by
      intro ω
      unfold push
      show ∑ w ∈ fibre π {ω}, (if w = w₁ then (1 : ℝ) else 0) = _
      rw [sum_ite_eq']
      simp [mem_fibre]
    have hμ1 : μ.p w₁ = 1 / 2 := by
      show (if w₁ = w₁ then (1 / 2 : ℝ) else 0) + (if w₁ = w₂ then (1 / 2 : ℝ) else 0) = 1 / 2
      simp [hne']
    have hμ2 : μ.p w₂ = 1 / 2 := by
      show (if w₂ = w₁ then (1 / 2 : ℝ) else 0) + (if w₂ = w₂ then (1 / 2 : ℝ) else 0) = 1 / 2
      simp [hne'.symm]
    have hac : ∀ ω, 0 < push π μa.p ω → 0 < push π μ.p ω := by
      intro ω hω
      rw [hpush] at hω
      split_ifs at hω with hω'
      · subst hω'
        unfold push
        have hmem : w₁ ∈ fibre π {π w₁} := (mem_fibre _ _ _).2 (mem_singleton_self _)
        calc (0 : ℝ) < μ.p w₁ := by rw [hμ1]; norm_num
          _ ≤ ∑ w ∈ fibre π {π w₁}, μ.p w :=
            single_le_sum (fun w _ => μ.nonneg w) hmem
      · exact absurd hω (lt_irrefl 0)
    have hX : 0 < mass (push π μa.p) {π w₁} := by
      rw [mass_singleton, hpush]
      simp
    have key := h μ μa hac {π w₁} hX
    unfold rigidV at key
    rw [condExp_singleton (by rw [hpush]; simp)] at key
    -- key : coarseV π μ.p u {π w₁} = coarseV π μa.p u {π w₁}
    have hfib1 : w₁ ∈ fibre π {π w₁} := (mem_fibre _ _ _).2 (mem_singleton_self _)
    have hfib2 : w₂ ∈ fibre π {π w₁} := (mem_fibre _ _ _).2 (by rw [← hπ]; exact mem_singleton_self _)
    have hL : coarseV π μ.p u {π w₁} = (u w₁ + u w₂) / 2 := by
      unfold coarseV condExp mass
      have hnum : ∑ w ∈ fibre π {π w₁}, μ.p w * u w = u w₁ / 2 + u w₂ / 2 := by
        show ∑ w ∈ fibre π {π w₁}, ((if w = w₁ then (1 / 2 : ℝ) else 0) +
          (if w = w₂ then (1 / 2 : ℝ) else 0)) * u w = _
        simp only [add_mul, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq', hfib1, hfib2,
          if_true]
        ring
      have hden : ∑ w ∈ fibre π {π w₁}, μ.p w = 1 := by
        show ∑ w ∈ fibre π {π w₁}, ((if w = w₁ then (1 / 2 : ℝ) else 0) +
          (if w = w₂ then (1 / 2 : ℝ) else 0)) = _
        simp only [sum_add_distrib, sum_ite_eq', hfib1, hfib2, if_true]
        norm_num
      rw [hnum, hden]
      ring
    have hR : coarseV π μa.p u {π w₁} = u w₁ := by
      unfold coarseV condExp mass
      have hnum : ∑ w ∈ fibre π {π w₁}, μa.p w * u w = u w₁ := by
        show ∑ w ∈ fibre π {π w₁}, (if w = w₁ then (1 : ℝ) else 0) * u w = _
        simp only [ite_mul, zero_mul, sum_ite_eq', hfib1, if_true, one_mul]
      have hden : ∑ w ∈ fibre π {π w₁}, μa.p w = 1 := by
        show ∑ w ∈ fibre π {π w₁}, (if w = w₁ then (1 : ℝ) else 0) = _
        simp only [sum_ite_eq', hfib1, if_true]
      rw [hnum, hden, div_one]
    rw [hL, hR] at key
    apply hne
    linarith
  · intro hu μ μa hac
    rw [rigid_eq_true_iff]
    intro ω hω
    -- pick a point of the fibre charged by `μa`
    have hex : ∃ w₀ ∈ fibre π {ω}, 0 < μa.p w₀ := by
      by_contra hcon
      push Not at hcon
      have : push π μa.p ω = 0 :=
        sum_eq_zero fun w hw => le_antisymm (hcon w hw) (μa.nonneg w)
      rw [this] at hω
      exact lt_irrefl 0 hω
    obtain ⟨w₀, hw₀, -⟩ := hex
    have hconst : ∀ w ∈ fibre π {ω}, u w = u w₀ := by
      intro w hw
      rw [mem_fibre, mem_singleton] at hw hw₀
      exact hu w w₀ (hw.trans hw₀.symm)
    unfold coarseV
    rw [condExp_of_const hconst hω, condExp_of_const hconst (hac ω hω)]

/-- **Reading B** (internal, trivial): on an algebra with a charged atom, a probability-only
supposition determines `V^a` at that atom only through rigidity, while pair-valued `cf` may
put any value there — so rigidity is not onto. Stated as: for every `q : Dist Ω` charging an
atom `ω` and every real `c`, there is a JB pair `(q, V)` with `V {ω} = c`.
Source: drafting chat line 2389 (the trivial reading the chat did not mean) | dp-core-2-049
Kind: T
Fidelity: n/a
Hyps: n/a -/
theorem rigidity_not_surjective (q : Dist Ω) (ω : Ω) (hω : 0 < q.p ω) (c : ℝ) :
    ∃ p : JBPair (∅ : Designation (Finset Ω)), p.P = q.toProb ∧
      ∀ hpos : 0 < p.P.P {ω}, p.V ⟨{ω}, hpos⟩ = c :=
  ⟨q.toJBPair (fun _ => c), rfl, fun _ => condExp_singleton hω⟩

end Coarsening

/-! ### T3(iv): the coarse Smoking-Lesion algebra -/

section SmokingLesion

/-- Fine outcomes `(smoke, lesion, cancer)`.
Source: drafting chat line 2389 (the coarse counterexample) | dp-core-2-049
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev SLW : Type := Bool × Bool × Bool

/-- The coarsening onto `{smoke, ¬smoke}` (`Ω = Bool`, `true = smoke`).
Source: drafting chat line 2389
Kind: D
Fidelity: exact
Hyps: n/a -/
def slπ : SLW → Bool := fun w => w.1

/-- Utility: `u(smoke, ·, cancer) = -9`, `u(smoke, ·, ¬cancer) = 1`, `u(¬smoke, ·, cancer) = -10`,
`u(¬smoke, ·, ¬cancer) = 0`.
Source: dp-worlds-jb mandate §3 T3(iv)
Kind: D
Fidelity: exact
Hyps: n/a -/
def slU : SLW → ℝ := fun w =>
  if w.1 then (if w.2.2 then -9 else 1) else (if w.2.2 then -10 else 0)

/-- `P(x | lesion) = 9/10`, `P(x | ¬lesion) = 1/10` for `x ∈ {smoke, cancer}`.
Source: dp-worlds-jb mandate §3 T3(iv)
Kind: D
Fidelity: exact
Hyps: n/a -/
def slCond (l x : Bool) : ℝ := if l = x then 9 / 10 else 1 / 10

/-- The actual belief: lesion w.p. `1/2`, then smoking and cancer independent given the lesion.
Source: dp-worlds-jb mandate §3 T3(iv)
Kind: D
Fidelity: exact
Hyps: n/a -/
def slμ : Dist SLW where
  p w := 1 / 2 * slCond w.2.1 w.1 * slCond w.2.1 w.2.2
  nonneg w := by unfold slCond; split_ifs <;> norm_num
  sum_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, slCond]
    norm_num

/-- The supposed belief for `a = smoke`: same lesion and cancer laws, smoking forced.
Source: dp-worlds-jb mandate §3 T3(iv)
Kind: D
Fidelity: exact
Hyps: n/a -/
def slμa : Dist SLW where
  p w := if w.1 then 1 / 2 * slCond w.2.1 w.2.2 else 0
  nonneg w := by unfold slCond; split_ifs <;> norm_num
  sum_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, slCond]
    norm_num

theorem sl_fibre_true : fibre slπ {true} = univ.filter (fun w : SLW => w.1 = true) := by
  ext w
  simp [mem_fibre, slπ]

/-- `V_s(smoke) = E_μ[u | smoke] = -36/5` (`P_μ(cancer | smoke) = 41/50`).
Source: dp-worlds-jb mandate §3 T3(iv)
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem sl_coarseV_actual : coarseV slπ slμ.p slU {true} = -36 / 5 := by
  unfold coarseV condExp mass
  rw [sl_fibre_true, sum_filter, sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, slμ, slU, slCond]
  norm_num

/-- `V^a_true(smoke) = E_{μᵃ}[u | smoke] = -4` (`P_{μᵃ}(cancer) = 1/2`).
Source: dp-worlds-jb mandate §3 T3(iv)
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem sl_coarseV_supposed : coarseV slπ slμa.p slU {true} = -4 := by
  unfold coarseV condExp mass
  rw [sl_fibre_true, sum_filter, sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, slμa, slU, slCond]
  norm_num

theorem sl_push_true : push slπ slμa.p true = 1 := by
  unfold push
  rw [sl_fibre_true, sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, slμa, slCond]
  norm_num

/-- On a two-atom algebra, success forces `P^a = δ_smoke`: any probability with
`P {smoke} = 1` is the Dirac at `smoke`.
Source: drafting chat line 2389 ("`cf_s(smoke)` is forced to `δ_smoke` — identical to conditioning")
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem forced_dirac_two_atoms (Q : Prob (∅ : Designation (Finset Bool)))
    (h : Q.P {true} = 1) : ∀ s, Q.P s = if true ∈ s then 1 else 0 := by
  have hf : Q.P {false} = 0 := by
    have := Q.compl {true}
    have e : ({true} : Finset Bool)ᶜ = {false} := by decide
    rw [e, h] at this
    linarith
  intro s
  have hsplit : s = (s ∩ {true}) ⊔ (s ∩ {false}) := by
    ext b
    cases b <;> simp
  have hdisj : Disjoint (s ∩ {true}) (s ∩ {false}) :=
    (Finset.disjoint_singleton.2 (by decide)).mono inter_subset_right inter_subset_right
  have hzero : Q.P (s ∩ {false}) = 0 := by
    apply le_antisymm _ (Q.nonneg _)
    have := Q.mono (inter_subset_right (s₁ := s) (s₂ := {false}))
    rw [hf] at this
    exact this
  rw [hsplit, Q.add _ _ hdisj, hzero, add_zero]
  by_cases ht : true ∈ s
  · rw [Finset.inter_singleton_of_mem ht, h, if_pos (by simp [ht])]
  · rw [Finset.inter_singleton_of_notMem ht, ← Finset.bot_eq_empty, Q.bot, if_neg (by simp [ht])]

/-- **T3(iv), N+.** The coarse Smoking-Lesion algebra: `P^a = δ_smoke` is forced (so
probability-only `cf(smoke)` cannot differ from conditioning), `V_s(smoke) = -36/5`,
`V^a_true(smoke) = -4`, and rigidity returns `V^a_rig(smoke) = -36/5 ≠ -4` — EDT's news value.
Within-atom revaluation (cancer is invisible to `Ω`) is exactly what T3(ii)'s condition forbids,
and T3(iii)'s necessity direction is exhibited on the corpus's own example.
Source: drafting chat line 2389 | dp-core-2-049
Kind: N+
Fidelity: exact (numbers verified by `norm_num`)
Hyps: (a) -/
theorem coarse_smoking_lesion :
    (∀ s, (slμa.pushforward slπ).toProb.P s = if true ∈ s then 1 else 0) ∧
    coarseV slπ slμ.p slU {true} = -36 / 5 ∧
    coarseV slπ slμa.p slU {true} = -4 ∧
    rigidV slπ slμ.p slμa.p slU {true} = -36 / 5 ∧
    rigidV slπ slμ.p slμa.p slU {true} ≠ coarseV slπ slμa.p slU {true} ∧
    0 < mass (push slπ slμa.p) {true} := by
  have hpush : push slπ slμa.p true = 1 := sl_push_true
  have hrig : rigidV slπ slμ.p slμa.p slU {true} = -36 / 5 := by
    unfold rigidV
    rw [condExp_singleton (by rw [hpush]; exact one_pos)]
    exact sl_coarseV_actual
  refine ⟨?_, sl_coarseV_actual, sl_coarseV_supposed, hrig, ?_, ?_⟩
  · apply forced_dirac_two_atoms
    show mass (push slπ slμa.p) {true} = 1
    rw [mass_singleton, hpush]
  · rw [hrig, sl_coarseV_supposed]
    norm_num
  · rw [mass_singleton, hpush]
    exact one_pos

end SmokingLesion

end

end Cleanroom.Decision.DpWorldsJb
