import Cleanroom.Corrigibility.LegitNegStatic.SealedBlind

/-!
# Extension: sealing as an exact characterization of `¬L`-blindness

Package `legit-neg-static`, §4 (extension, plan §0.4 rule 6). `NegLBlind R` says: under sealing
with `0 < π(L)`, the R1 argmax of the rule `R` is invariant under every change of the
*void-terminal data* — `u` on terminals with `leg = false`, the void grades `W`, the cross-branch
data `K`. Each positive `(proposal, scoring)` cell is a lemma; each negative cell is a witness
pair (two problems agreeing on all legitimate-terminal data with different argmax). The
necessity direction is the plumbing statement that `NegLBlind` is equivalent to the argmax
factoring through the legitimate-terminal data.

Verdicts (all proved): blind for `{P1, P2} × {S1, S1-blind, S2sel, S3, shift-S3, ordinal S3,
hybrid}`, `P3` at `λ = 0`, `P4b` at `κ' = 0`; not blind for `{P1, P2} × S2`, `P3` at `λ > 0`,
`P4a`, `P4b` at `κ' > 0`, `P5` (through `K`).
-/

namespace Cleanroom.Corrigibility.LegitNegStatic

open Finset Problem

section Defs

variable {S A : Type} [Fintype S] [Fintype A]

/-- Two problems agree on all legitimate-terminal data: same prior, same legitimacy, same `u`
on every legitimate terminal (they may differ on void terminals).
Source: mandate §4
Kind: D
Fidelity: exact -/
def AgreeLegit (P P' : Problem S A) : Prop :=
  P.prior = P'.prior ∧ P.leg = P'.leg ∧ ∀ s a, P.leg s a = true → P.u s a = P'.u s a

/-- A rule: from a problem and the optional data `W`, `K` to a set of chosen options.
Source: mandate §4
Kind: D
Fidelity: exact -/
abbrev Rule (S A : Type) [Fintype S] [Fintype A] :=
  Problem S A → MenuVec S A → MenuVec S A → Finset A

/-- **`NegLBlind R`**: under sealing with `0 < π(L)`, `R`'s choice is invariant under every
change of the void-terminal data (`u` off `L`, `W`, `K`).
Source: mandate §4
Kind: D
Fidelity: exact -/
def NegLBlind (R : Rule S A) : Prop :=
  ∀ (P P' : Problem S A) (Wg Wg' K K' : MenuVec S A) (ℓ : S → Bool),
    P.SealedBy ℓ → 0 < P.mass ℓ → AgreeLegit P P' → R P Wg K = R P' Wg' K'

/-- The legitimate-terminal data of a problem: prior, legitimacy, and `u` where legitimate.
Source: mandate §4 (necessity direction)
Kind: D
Fidelity: exact -/
def legitData (P : Problem S A) : (S → ℚ) × (S → A → Bool) × (S → A → Option ℚ) :=
  (P.prior, P.leg, fun s a => if P.leg s a then some (P.u s a) else none)

/-- `legitData_eq_iff`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma legitData_eq_iff (P P' : Problem S A) : legitData P = legitData P' ↔ AgreeLegit P P' := by
  unfold legitData AgreeLegit
  constructor
  · intro h
    have h1 : P.prior = P'.prior := congrArg Prod.fst h
    have h2 : P.leg = P'.leg := congrArg (fun x => x.2.1) h
    have h3 := congrArg (fun x => x.2.2) h
    refine ⟨h1, h2, fun s a hs => ?_⟩
    have := congrFun (congrFun h3 s) a
    simp only at this
    rw [hs, ← h2, hs] at this
    simpa using this
  · rintro ⟨h1, h2, h3⟩
    refine Prod.ext h1 (Prod.ext h2 ?_)
    funext s a
    simp only
    by_cases hs : P.leg s a = true
    · rw [hs, ← h2, hs, h3 s a hs]
    · simp [Bool.not_eq_true] at hs; rw [← h2]; simp [hs]

/-- **Necessity (plumbing).** A rule is `¬L`-blind on sealed problems iff, on sealed problems
with `0 < π(L)`, its choice factors through the legitimate-terminal data.
Source: mandate §4 ("made precise as: the proposal's score factors through the legitimate-terminal data")
Kind: L
Fidelity: exact (a tautology once `AgreeLegit` is `legitData`-equality) -/
theorem NegLBlind_iff_factors (R : Rule S A) :
    NegLBlind R ↔ ∃ F : (S → ℚ) × (S → A → Bool) × (S → A → Option ℚ) → Finset A,
      ∀ (P : Problem S A) (Wg K : MenuVec S A) (ℓ : S → Bool),
        P.SealedBy ℓ → 0 < P.mass ℓ → R P Wg K = F (legitData P) := by
  classical
  constructor
  · intro hR
    refine ⟨fun d => if h : ∃ (P : Problem S A) (Wg K : MenuVec S A) (ℓ : S → Bool),
        P.SealedBy ℓ ∧ 0 < P.mass ℓ ∧ legitData P = d
      then R h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose else ∅, ?_⟩
    intro P Wg K ℓ hs hpos
    dsimp only
    have hex : ∃ (P₀ : Problem S A) (Wg₀ K₀ : MenuVec S A) (ℓ₀ : S → Bool),
        P₀.SealedBy ℓ₀ ∧ 0 < P₀.mass ℓ₀ ∧ legitData P₀ = legitData P := ⟨P, Wg, K, ℓ, hs, hpos, rfl⟩
    rw [dif_pos hex]
    obtain ⟨hs₀, hpos₀, hd⟩ := hex.choose_spec.choose_spec.choose_spec.choose_spec
    exact hR P hex.choose Wg _ K _ ℓ hs hpos ((legitData_eq_iff _ _).1 hd.symm)
  · rintro ⟨F, hF⟩ P P' Wg Wg' K K' ℓ hs hpos hag
    have hs' : P'.SealedBy ℓ := fun s a => by rw [← hag.2.1]; exact hs s a
    have hm : P'.mass ℓ = P.mass ℓ := by unfold mass; rw [hag.1]
    rw [hF P Wg K ℓ hs hpos, hF P' Wg' K' ℓ hs' (hm ▸ hpos), (legitData_eq_iff P P').2 hag]

end Defs

/-! ### Positive cells -/

namespace Problem

variable {S A : Type} [Fintype S] [Fintype A]

/-- `P1` of two problems agreeing on legitimate data, with vectors agreeing on the legitimate
diagonal, coincide.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P1_eq_of_AgreeLegit {P P' : Problem S A} (h : AgreeLegit P P') {V V' : MenuVec S A}
    (hV : ∀ s a, P.leg s a = true → V s a a = V' s a a) (a : A) : P.P1 V a = P'.P1 V' a := by
  unfold P1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← h.1, ← h.2.1]
  by_cases hs : P.leg s a = true
  · rw [hs, hV s a hs]
  · simp [Bool.not_eq_true] at hs; simp [hs]

/-- `PL_eq_of_AgreeLegit`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma PL_eq_of_AgreeLegit {P P' : Problem S A} (h : AgreeLegit P P') (a : A) : P.PL a = P'.PL a := by
  unfold PL mass; rw [h.1, h.2.1]

/-- `P2_eq_of_AgreeLegit`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P2_eq_of_AgreeLegit {P P' : Problem S A} (h : AgreeLegit P P') {V V' : MenuVec S A}
    (hV : ∀ s a, P.leg s a = true → V s a a = V' s a a) (a : A) : P.P2 V a = P'.P2 V' a := by
  unfold P2; rw [PL_eq_of_AgreeLegit h, P1_eq_of_AgreeLegit h hV]

/-- Under sealing, at a legitimate state every terminal is legitimate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma leg_all_of_SealedBy {P : Problem S A} {ℓ : S → Bool} (h : P.SealedBy ℓ) {s : S} {a : A}
    (hs : P.leg s a = true) (c : A) : P.leg s c = true := by rw [h s c, ← h s a]; exact hs

/-- A scoring family `V : Problem S A → MenuVec S A` is *legit-local* under sealing if its
diagonal at a legitimate terminal depends only on the legitimate-terminal data.
Source: mandate §4
Kind: D
Fidelity: exact -/
def LegitLocal (V : Problem S A → MenuVec S A) : Prop :=
  ∀ (P P' : Problem S A) (ℓ : S → Bool), P.SealedBy ℓ → AgreeLegit P P' →
    ∀ s a, P.leg s a = true → V P s a a = V P' s a a

/-- **Positive cell, P1 × any legit-local scoring.**
Source: mandate §4
Kind: P
Fidelity: exact -/
theorem NegLBlind_P1_of_LegitLocal (V : Problem S A → MenuVec S A) (hV : LegitLocal V) :
    NegLBlind (fun P _ _ => argmax (P.P1 (V P))) := by
  intro P P' _ _ _ _ ℓ hs _ hag
  exact argmax_congr (P1_eq_of_AgreeLegit hag (hV P P' ℓ hs hag))

/-- **Positive cell, P2 × any legit-local scoring.**
Source: mandate §4
Kind: P
Fidelity: exact -/
theorem NegLBlind_P2_of_LegitLocal (V : Problem S A → MenuVec S A) (hV : LegitLocal V) :
    NegLBlind (fun P _ _ => argmaxOpt (P.P2 (V P))) := by
  intro P P' _ _ _ _ ℓ hs _ hag
  have : P.P2 (V P) = P'.P2 (V P') := funext fun a => P2_eq_of_AgreeLegit hag (hV P P' ℓ hs hag) a
  show argmaxOpt (P.P2 (V P)) = argmaxOpt (P'.P2 (V P'))
  rw [this]

/-- `LegitLocal_S1`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem LegitLocal_S1 : LegitLocal (fun P : Problem S A => S1 P.u) :=
  fun _ _ _ _ hag s a hs => by simp [hag.2.2 s a hs]

/-- `LegitLocal_blindImpute`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem LegitLocal_blindImpute [DecidableEq A] (y : ℚ) :
    LegitLocal (fun P : Problem S A => P.blindImpute y) :=
  fun _ _ _ _ hag s a hs => by simp [blindImpute, hag.2.2 s a hs]

/-- `LegitLocal_S2sel`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem LegitLocal_S2sel : LegitLocal (fun P : Problem S A => P.S2sel) := by
  intro P P' ℓ hs hag s a _
  simp only [S2sel, Hcond]
  have hm : P.mass (fun t => P.leg t a) = P'.mass (fun t => P'.leg t a) := PL_eq_of_AgreeLegit hag a
  rw [hm]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← hag.1, ← hag.2.1]
  by_cases ht : P.leg t a = true
  · rw [hag.2.2 t a ht]
  · simp [Bool.not_eq_true] at ht; simp [ht]

/-- `umax_eq_of_AgreeLegit`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem umax_eq_of_AgreeLegit [Nonempty A] {P P' : Problem S A} {ℓ : S → Bool} (hs : P.SealedBy ℓ)
    (hag : AgreeLegit P P') {s : S} {a : A} (hl : P.leg s a = true) : P.umax s = P'.umax s := by
  unfold umax
  exact Finset.sup'_congr _ rfl fun c _ => hag.2.2 s c (leg_all_of_SealedBy hs hl c)

/-- `LegitLocal_S3`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem LegitLocal_S3 [Nonempty A] (D : ℚ) : LegitLocal (fun P : Problem S A => P.S3 D) :=
  fun P P' ℓ hs hag s a hl => by
    simp only [S3]; rw [umax_eq_of_AgreeLegit hs hag hl, hag.2.2 s a hl]

/-- `LegitLocal_shiftS3`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem LegitLocal_shiftS3 (k : S → ℚ) : LegitLocal (fun P : Problem S A => P.shiftS3 k) :=
  fun _ _ _ _ hag s a hs => by simp [shiftS3, hag.2.2 s a hs]

/-- `LegitLocal_ordinalS3`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem LegitLocal_ordinalS3 : LegitLocal (fun P : Problem S A => P.ordinalS3) :=
  fun P P' ℓ hs hag s a hl => by
    simp only [ordinalS3]
    congr 2
    apply propext
    constructor <;> intro h c' <;> have := h c' <;>
      rw [hag.2.2 s c' (leg_all_of_SealedBy hs hl c'), hag.2.2 s a hl] at * <;> assumption

/-- `LegitLocal_penalise`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem LegitLocal_penalise [DecidableEq A] (V : Problem S A → MenuVec S A) (hV : LegitLocal V)
    (where_ : S → A → Bool) (option : A) (p : ℚ) :
    LegitLocal (fun P : Problem S A => Problem.penalise (V P) where_ option p) :=
  fun P P' ℓ hs hag s a hl => by
    simp only [Problem.penalise]
    rw [hV P P' ℓ hs hag s a hl]

/-- `P3` at `λ = 0` is `P1`, hence blind under every legit-local scoring.
Source: mandate §4
Kind: P
Fidelity: exact -/
theorem NegLBlind_P3_zero (V : Problem S A → MenuVec S A) (hV : LegitLocal V) :
    NegLBlind (fun P Wg _ => argmax (P.P3 Wg 0 (V P))) := by
  intro P P' Wg Wg' K K' ℓ hs hpos hag
  have h1 : (fun a => P.P3 Wg 0 (V P) a) = fun a => P.P1 (V P) a := funext fun a => P.P3_zero _ _ a
  have h2 : (fun a => P'.P3 Wg' 0 (V P') a) = fun a => P'.P1 (V P') a :=
    funext fun a => P'.P3_zero _ _ a
  show argmax (fun a => P.P3 Wg 0 (V P) a) = argmax (fun a => P'.P3 Wg' 0 (V P') a)
  rw [h1, h2]
  exact NegLBlind_P1_of_LegitLocal V hV P P' Wg Wg' K K' ℓ hs hpos hag

/-- `P4b_zero_eq`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P4b_zero_eq (P : Problem S A) (Wg : MenuVec S A) (κ : ℚ) (V : MenuVec S A) (a : A) :
    P.P4b Wg κ 0 V a = κ * P.PL a + (1 - κ) * P.P1 V a := by
  unfold P4b P1 PL mass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- `P4b` at `κ' = 0` is cdot plus a constant, hence blind under every legit-local scoring.
Source: mandate §4; [[corr-legit-neg-2-inventory]] item 2-031
Kind: P
Fidelity: exact -/
theorem NegLBlind_P4b_zero (V : Problem S A → MenuVec S A) (hV : LegitLocal V) (κ : ℚ) :
    NegLBlind (fun P Wg _ => argmax (P.P4b Wg κ 0 (V P))) := by
  intro P P' _ _ _ _ ℓ hs _ hag
  show argmax (fun a => P.P4b _ κ 0 (V P) a) = argmax (fun a => P'.P4b _ κ 0 (V P') a)
  refine argmax_congr fun a => ?_
  rw [P4b_zero_eq, P4b_zero_eq, PL_eq_of_AgreeLegit hag, P1_eq_of_AgreeLegit hag (hV P P' ℓ hs hag)]

end Problem

/-! ### Negative cells: witness pairs -/

/-- The two members of the negative-cell witness pair: `incautionInstance (1/2) (1/10) (1/2) harm`
with `harm ∈ {0, 1}` — they agree on all legitimate-terminal data and differ only on the void
state's `u`.
Source: mandate §4
Kind: D
Fidelity: exact -/
def negPair (harm : ℚ) : Problem (Fin 2) (Fin 2) :=
  incautionInstance (1/2) (1/10) (1/2) harm (by norm_num) (by norm_num)

/-- `negPair_AgreeLegit`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem negPair_AgreeLegit (h h' : ℚ) : AgreeLegit (negPair h) (negPair h') := by
  refine ⟨rfl, rfl, fun s a hs => ?_⟩
  fin_cases s
  · fin_cases a <;> rfl
  · simp [negPair, incautionInstance] at hs

/-- **Negative cell, P1 × S2** (A6's escape: S2 reads `H`, which reads `u` on void terminals).
Source: mandate §4
Kind: N+
Fidelity: exact -/
theorem not_NegLBlind_P1_S2 :
    ¬ NegLBlind (fun P : Problem (Fin 2) (Fin 2) => fun _ _ => argmax (P.P1 P.S2)) := by
  intro h
  have := h (negPair 0) (negPair 1) 0 0 0 0 legG (incautionInstance_SealedBy _ _ _ _ _ _)
    (by simp [negPair, incautionInstance, mass, legG]; norm_num) (negPair_AgreeLegit 0 1)
  have h0 : argmax ((negPair 0).P1 (negPair 0).S2) = {1} := by
    rw [argmax_fin2_eq_one_iff]; simp [negPair, incautionInstance, P1, S2, H, W, EU]; norm_num
  have h1 : argmax ((negPair 1).P1 (negPair 1).S2) = {0} := by
    rw [argmax_fin2_eq_zero_iff]; simp [negPair, incautionInstance, P1, S2, H, W, EU]; norm_num
  dsimp only at this
  rw [h0, h1] at this
  exact absurd this (by decide)

/-- **Negative cell, P2 × S2.**
Source: mandate §4
Kind: N+
Fidelity: exact -/
theorem not_NegLBlind_P2_S2 :
    ¬ NegLBlind (fun P : Problem (Fin 2) (Fin 2) => fun _ _ => argmaxOpt (P.P2 P.S2)) := by
  intro h
  have hs := incautionInstance_SealedBy (1/2) (1/10) (1/2) 0 (by norm_num) (by norm_num)
  have hs' := incautionInstance_SealedBy (1/2) (1/10) (1/2) 1 (by norm_num) (by norm_num)
  have hpos : 0 < (negPair 0).mass legG := by simp [negPair, incautionInstance, mass, legG]; norm_num
  have hpos' : 0 < (negPair 1).mass legG := by simp [negPair, incautionInstance, mass, legG]; norm_num
  have := h (negPair 0) (negPair 1) 0 0 0 0 legG hs hpos (negPair_AgreeLegit 0 1)
  dsimp only at this
  rw [(negPair 0).argmaxOpt_P2_eq_argmax_P1_of_SealedBy hs hpos,
    (negPair 1).argmaxOpt_P2_eq_argmax_P1_of_SealedBy hs' hpos'] at this
  have h0 : argmax ((negPair 0).P1 (negPair 0).S2) = {1} := by
    rw [argmax_fin2_eq_one_iff]; simp [negPair, incautionInstance, P1, S2, H, W, EU]; norm_num
  have h1 : argmax ((negPair 1).P1 (negPair 1).S2) = {0} := by
    rw [argmax_fin2_eq_zero_iff]; simp [negPair, incautionInstance, P1, S2, H, W, EU]; norm_num
  rw [h0, h1] at this
  exact absurd this (by decide)

/-- The void grade that favours `safe` on the void state by `M`: `W b safe = M`, `0` elsewhere.
Source: mandate §4
Kind: D
Fidelity: exact -/
def favourSafe (M : ℚ) : MenuVec (Fin 2) (Fin 2) := fun s _ c => if s = 1 ∧ c = 0 then M else 0

/-- **Negative cell, P3 at `λ > 0`** (reads `W`): on `negPair 1` under S1, `W ≡ 0` picks
`risky`, `W = favourSafe (1/λ)` picks `safe`.
Source: mandate §4
Kind: N+
Fidelity: exact -/
theorem not_NegLBlind_P3_pos (lam : ℚ) (hlam : 0 < lam) :
    ¬ NegLBlind (fun P : Problem (Fin 2) (Fin 2) => fun Wg _ => argmax (P.P3 Wg lam (S1 P.u))) := by
  intro h
  have := h (negPair 1) (negPair 1) 0 (favourSafe (1 / lam)) 0 0 legG
    (incautionInstance_SealedBy _ _ _ _ _ _)
    (by simp [negPair, incautionInstance, mass, legG]; norm_num) (negPair_AgreeLegit 1 1)
  have h0 : argmax ((negPair 1).P3 0 lam (S1 (negPair 1).u)) = {1} := by
    rw [argmax_fin2_eq_one_iff]; simp [negPair, incautionInstance, P3]; norm_num
  have h1 : argmax ((negPair 1).P3 (favourSafe (1 / lam)) lam (S1 (negPair 1).u)) = {0} := by
    rw [argmax_fin2_eq_zero_iff]; simp [negPair, incautionInstance, P3, favourSafe]
    field_simp; norm_num
  dsimp only at this
  rw [h0, h1] at this
  exact absurd this (by decide)

/-- Under sealing `PL` is constant, so `P4a`'s lexicographic argmax is the argmax of its
second coordinate `P3 W 1 V` (finding 16).
Source: mandate §4; finding 16
Kind: L
Fidelity: exact -/
theorem argmaxLex_P4a_eq_argmax_P3_of_SealedBy {S A : Type} [Fintype S] [Fintype A]
    (P : Problem S A) {ℓ : S → Bool} (h : P.SealedBy ℓ) (Wg V : MenuVec S A) :
    argmaxLex (P.P4a Wg V) = argmax (P.P3 Wg 1 V) := by
  ext a
  simp only [mem_argmaxLex, mem_argmax, P4a]
  constructor
  · intro ha b
    have := ha b
    rw [P.PL_eq_mass_of_SealedBy h, P.PL_eq_mass_of_SealedBy h] at this
    rw [Prod.Lex.toLex_le_toLex] at this
    rcases this with h1 | ⟨_, h2⟩
    · exact absurd h1 (lt_irrefl _)
    · exact h2
  · intro ha b
    rw [P.PL_eq_mass_of_SealedBy h, P.PL_eq_mass_of_SealedBy h, Prod.Lex.toLex_le_toLex]
    exact Or.inr ⟨rfl, ha b⟩

/-- **Negative cell, P4a** (under sealing it is `P3` at `λ = 1`).
Source: mandate §4
Kind: N+
Fidelity: exact -/
theorem not_NegLBlind_P4a :
    ¬ NegLBlind (fun P : Problem (Fin 2) (Fin 2) => fun Wg _ => argmaxLex (P.P4a Wg (S1 P.u))) := by
  intro h
  apply not_NegLBlind_P3_pos 1 one_pos
  intro P P' Wg Wg' K K' ℓ hs hpos hag
  have := h P P' Wg Wg' K K' ℓ hs hpos hag
  have hs' : P'.SealedBy ℓ := fun s a => by rw [← hag.2.1]; exact hs s a
  dsimp only at this ⊢
  rwa [argmaxLex_P4a_eq_argmax_P3_of_SealedBy P hs, argmaxLex_P4a_eq_argmax_P3_of_SealedBy P' hs'] at this

/-- **Negative cell, P4b at `κ' > 0`** (reads `W`), for `0 < κ' < κ < 1` (at `κ = 1` the
legitimate part is the constant `κ` and P4b reads only `W`: still not blind, but by a tie).
Source: mandate §4
Kind: N+
Fidelity: exact -/
theorem not_NegLBlind_P4b_pos (κ κ' : ℚ) (hκ' : 0 < κ') (hκ : κ' < κ) (hκ1 : κ < 1) :
    ¬ NegLBlind (fun P : Problem (Fin 2) (Fin 2) => fun Wg _ => argmax (P.P4b Wg κ κ' (S1 P.u))) := by
  intro h
  have := h (negPair 1) (negPair 1) 0 (favourSafe (1 / κ')) 0 0 legG
    (incautionInstance_SealedBy _ _ _ _ _ _)
    (by simp [negPair, incautionInstance, mass, legG]; norm_num) (negPair_AgreeLegit 1 1)
  have hκ'ne : κ' ≠ 0 := hκ'.ne'
  have h0 : argmax ((negPair 1).P4b 0 κ κ' (S1 (negPair 1).u)) = {1} := by
    rw [argmax_fin2_eq_one_iff]; simp [negPair, incautionInstance, P4b]; linarith
  have h1 : argmax ((negPair 1).P4b (favourSafe (1 / κ')) κ κ' (S1 (negPair 1).u)) = {0} := by
    rw [argmax_fin2_eq_zero_iff]; simp [negPair, incautionInstance, P4b, favourSafe]
    field_simp; nlinarith [mul_pos hκ' (sub_pos.2 hκ1)]
  dsimp only at this
  rw [h0, h1] at this
  exact absurd this (by decide)

/-- **Negative cell, P4b at `κ = 1`, `κ' > 0`** (the top of the mandate's range `κ' < κ ≤ 1`):
the legitimate part is the constant `κ = 1` and P4b reads only `W`, so under `W ≡ 0` the whole
menu ties (`argmax = univ`) while `favourSafe (1/κ')` picks `safe` — a tie against a singleton is
still non-blindness.
Source: mandate §4
Kind: N+
Fidelity: exact -/
theorem not_NegLBlind_P4b_one (κ' : ℚ) (hκ' : 0 < κ') :
    ¬ NegLBlind (fun P : Problem (Fin 2) (Fin 2) => fun Wg _ => argmax (P.P4b Wg 1 κ' (S1 P.u))) := by
  intro h
  have hne : κ' ≠ 0 := hκ'.ne'
  have := h (negPair 1) (negPair 1) 0 (favourSafe (1 / κ')) 0 0 legG
    (incautionInstance_SealedBy _ _ _ _ _ _)
    (by simp [negPair, incautionInstance, mass, legG]; norm_num) (negPair_AgreeLegit 1 1)
  have h0 : argmax ((negPair 1).P4b 0 1 κ' (S1 (negPair 1).u)) = univ := by
    have hc : ∀ a, (negPair 1).P4b 0 1 κ' (S1 (negPair 1).u) a = 1/2 := by
      intro a; fin_cases a <;> simp [negPair, incautionInstance, P4b] <;> norm_num
    rw [argmax_congr hc, argmax_const]
  have h1 : argmax ((negPair 1).P4b (favourSafe (1 / κ')) 1 κ' (S1 (negPair 1).u)) = {0} := by
    rw [argmax_fin2_eq_zero_iff]; simp [negPair, incautionInstance, P4b, favourSafe]
    field_simp; norm_num
  dsimp only at this
  rw [h0, h1] at this
  exact absurd this (by decide)

/-- **Negative cell, P4b at `κ' > 0`, the whole mandate range `0 < κ' < κ ≤ 1`**: by
`not_NegLBlind_P4b_pos` for `κ < 1` and `not_NegLBlind_P4b_one` at `κ = 1`.
Source: mandate §4
Kind: N+
Fidelity: exact -/
theorem not_NegLBlind_P4b_pos_le_one (κ κ' : ℚ) (hκ' : 0 < κ') (hκ : κ' < κ) (hκ1 : κ ≤ 1) :
    ¬ NegLBlind (fun P : Problem (Fin 2) (Fin 2) => fun Wg _ => argmax (P.P4b Wg κ κ' (S1 P.u))) := by
  rcases hκ1.lt_or_eq with hlt | rfl
  · exact not_NegLBlind_P4b_pos κ κ' hκ' hκ hlt
  · exact not_NegLBlind_P4b_one κ' hκ'

/-- The cross-branch assessment that favours `safe`: `K g safe = M`, `0` elsewhere.
Source: mandate §4
Kind: D
Fidelity: exact -/
def favourSafeK (M : ℚ) : MenuVec (Fin 2) (Fin 2) := fun s _ c => if s = 0 ∧ c = 0 then M else 0

/-- **Negative cell, P5** (reads `K` when `0 < P(L | a) < 1`): `K ≡ 0` picks `risky`,
`K = favourSafeK 1` picks `safe`.
Source: mandate §4
Kind: N+
Fidelity: exact -/
theorem not_NegLBlind_P5 :
    ¬ NegLBlind (fun P : Problem (Fin 2) (Fin 2) => fun _ K => argmaxOpt (P.P5 K (S1 P.u))) := by
  intro h
  have := h (negPair 1) (negPair 1) 0 0 0 (favourSafeK 1) legG
    (incautionInstance_SealedBy _ _ _ _ _ _)
    (by simp [negPair, incautionInstance, mass, legG]; norm_num) (negPair_AgreeLegit 1 1)
  have hPL : ∀ a, (negPair 1).PL a = 1/2 := by
    intro a; simp [negPair, incautionInstance, PL, mass]; norm_num
  have hP5 : ∀ K : MenuVec (Fin 2) (Fin 2), (negPair 1).P5 K (S1 (negPair 1).u)
      = fun a => some ((negPair 1).P1 (S1 (negPair 1).u) a + (1 - 1/2) * (negPair 1).Kbar K a) := by
    intro K; funext a
    rw [(negPair 1).P5_of_ne _ _ a (by rw [hPL]; norm_num), hPL]
  dsimp only at this
  rw [hP5, hP5, argmaxOpt_some, argmaxOpt_some] at this
  have h0 : argmax (fun a => (negPair 1).P1 (S1 (negPair 1).u) a + (1 - 1/2) * (negPair 1).Kbar 0 a) = {1} := by
    rw [argmax_fin2_eq_one_iff]; simp [negPair, incautionInstance, P1, Kbar]; norm_num
  have h1 : argmax (fun a => (negPair 1).P1 (S1 (negPair 1).u) a + (1 - 1/2) * (negPair 1).Kbar (favourSafeK 1) a) = {0} := by
    rw [argmax_fin2_eq_zero_iff]; simp [negPair, incautionInstance, P1, Kbar, PL, mass, favourSafeK]; norm_num
  rw [h0, h1] at this
  exact absurd this (by decide)

end Cleanroom.Corrigibility.LegitNegStatic
