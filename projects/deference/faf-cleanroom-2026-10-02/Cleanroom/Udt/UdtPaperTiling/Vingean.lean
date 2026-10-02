import Cleanroom.Udt.UdtPaperTiling.Rules

/-!
# `udt-paper-tiling` · Vingean: the assumptions of Theorem 3 / Theorem 4 in the
computation-output model, and the two theorems (T4, T5)

**Where this module lives.** Theorems 3 and 4 never apply `eff`: the modification's effect enters
only through Fine-Grained Fairness. So here the prior's `pp` **is the chosen policy** (the trivial
paper layer, `PaperLayer.trivial`), and the paper's `E_p(u | π*(o) = a)` is `udt-bli-core`'s
`EU o a = 𝔼_μ[U | pp · o = a]`. Self-modifying actions are values of `pp` (of positive mass in
the witnesses, `VingeanWitness.lean`). Every docstring below says so.

**The computation-output model (grade (c), disclosed in every headline).** The paper's nested
expressions `π*(o') = argmax_{a'} E_p(u | …⌞a'⌟…)` are self-referential: the argmax is a
computation the agent is uncertain about (`main.tex` 267: "expressions which nest one expectation
inside of another expectation apparently require a probability distribution to reason about
itself"). Here each argmax-term is a **coordinate** of the prior — an impossible-possible-worlds
surrogate for "the output of that computation": `ArgmaxVars` with `αM o'` (the marginal argmax at
`o'`), `αJ A' o o'` (the joint argmax of `main.tex` 222 for `(A', o, o')`), `αC o' a' o`
(Appendix A's conditional argmax at `o` given `π*(o') = a'`). They are constrained *only* by the
assumptions. The extensional reading — every argmax evaluated at the meta level — is the same
predicates at *constant* variables (`Collapse.lean`), not separate definitions.
ATTRIBUTION-UNVETTED that this is what the authors intend (bli-paper-017's own label).

**The model is inert inside Theorem 3's own package** (audit r1, adversarial B1). Action
Coordination at `(A', o, o')` plus Knowledge of Decision Procedure at `o'` pin `αJ` to `pp · o'`
almost surely, so for *any* `V` Faith in Joint Argmax at the triple is equivalent to the
`V`-free `FaithInJointArgmaxPrior` — every positive concrete cell `(a, a')`, `a ∈ A'`, is
dominated by some positive marginal `EU o b`, `b ∈ A'` (`fja_pinned`); and some `V` satisfies the
three together iff the bare prior satisfies that (`exists_vars_iff`). Theorem 3 in this model is
therefore Theorem 3 over the bare prior with hypothesis `FaithInJointArgmaxPrior`
(`thm3_prior`): the (c) is harmless but buys nothing for Theorems 3/4. It still matters for
`Collapse.lean`, whose point is the *constant* case. Under the prior-form hypothesis the best
non-modifying action's row is flat (`row_flat_of_fjaPrior`), and Theorem 4's package forces
`EU o aₘ = EU o (twin aₘ)` (`thm4_forces_equality`).

**Maxima are never `Finset.sup'` over sets with junk cells.** "`x ≤ max_{a ∈ A'} value a`" is
stated as "`∃ b ∈ A'`, the cell of `b` is positive and `x ≤ value b`", and "`max ≥ max`" as
"every positive cell on the right is dominated by some positive cell on the left". Theorem 3's
max ranges over `𝒜^{-m} ∩ 𝒜_o` (`nonModAt o`), the available-action fix of bli-paper-013(ii).

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type} [Fintype Act]
  [DecidableEq Act]

/-! ## Limited Self-Modification -/

/-- **Limited Self-Modification**: every self-modifying action `aₘ` modifies exactly one
policy-point `(ob aₘ, ac aₘ)`, the forced action is non-modifying (`ac aₘ ∉ 𝒜^m`; the text's
`𝒜_m` is a typo for `𝒜^m`, bli-paper-008) and an action cannot modify its own policy-point
(`aₘ ∉ 𝒜_{ob aₘ}`). `ob`/`ac` are data (total functions, read only on `𝒜^m`).
Source: `main.tex` 205–209 (bli-paper-008); bli-slides-045 ("can't modify itself")
Kind: D
Fidelity: exact -/
structure LimitedSelfMod (S : PaperStructure 𝒟 Act) where
  /-- The observation whose point `aₘ` modifies. -/
  ob : Act → ↥𝒟
  /-- The action `aₘ` forces there. -/
  ac : Act → Act
  /-- `mod(aₘ) = {(ob aₘ, ac aₘ)}`. -/
  mod_eq : ∀ a ∈ S.selfMod, ∀ o, S.mod a o = if o = ob a then some (ac a) else none
  /-- `ac aₘ ∉ 𝒜^m`. -/
  ac_nonMod : ∀ a ∈ S.selfMod, ac a ∉ S.selfMod
  /-- `aₘ ∉ 𝒜_{ob aₘ}`. -/
  not_self : ∀ a ∈ S.selfMod, a ∉ S.Aof (ob a)

variable (P : FiniteBLIPrior 𝒮 m 𝒟 Act) (S : PaperStructure 𝒟 Act)

/-! ## Cells -/

/-- **The joint-cell value** `cellEU o o' a a' := 𝔼_μ[U | pp · o = a ∧ pp · o' = a']`, the paper's
`E_p(u | π*(o) = ⌜a⌝ ∧ π*(o') = ⌜a'⌝)` with `pp` the chosen policy. Its mass is `udt-bli-core`'s
`pairMass o o' a a'`; junk `0` at a null cell.
Source: `main.tex` 213, 222 (bli-paper-009, 010)
Kind: D
Fidelity: exact -/
def cellEU (o o' : ↥𝒟) (a a' : Act) : ℚ :=
  condExp P.μ P.U (fun ω => P.pp ω o = a ∧ P.pp ω o' = a')

/-- **Fine-Grained Fairness**: for every available self-modifying action `aₘ` at `o` of positive
mass, its value equals the value of its twin conditioned on the point the modification would
force, `EU o aₘ = cellEU o (ob aₘ) (twin aₘ) (ac aₘ)` — on positive cells (bli-paper-009's
positivity flag; the free `o` of the paper's statement bound by `aₘ ∈ 𝒜_o`). `pp` is the chosen
policy here.
Source: `main.tex` 211–215 (bli-paper-009)
Kind: D
Fidelity: variant: positivity guards on both cells; `o` bound by availability -/
def FineGrainedFairness (L : LimitedSelfMod S) : Prop :=
  ∀ o, ∀ aₘ ∈ S.Aof o, aₘ ∈ S.selfMod → 0 < P.ppMass o aₘ →
    0 < P.pairMass o (L.ob aₘ) (S.twin aₘ) (L.ac aₘ) →
    P.EU o aₘ = cellEU P o (L.ob aₘ) (S.twin aₘ) (L.ac aₘ)

/-! ## The computation-output variables -/

/-- **The argmax computations as coordinates of the prior** (the computation-output model,
grade (c)): `αM o'` is "the output of `argmax_{a'} E_p(u | π*(o') = ⌞a'⌟)`", `αJ A' o o'` the
joint argmax of `main.tex` 222 for `(A', o, o')`, `αC o' a' o` Appendix A's argmax at `o` given
`π*(o') = a'`. Constrained only by the assumptions below; the extensional reading is the
constant case (`Collapse.lean`).
Source: `main.tex` 103–107, 222–235, 267, 365–367 (bli-paper-017(b))
Kind: D
Fidelity: variant: computation-output model (c); ATTRIBUTION-UNVETTED as the authors' intent -/
structure ArgmaxVars (P : FiniteBLIPrior 𝒮 m 𝒟 Act) where
  /-- The marginal argmax at `o'`. -/
  αM : ↥𝒟 → P.Ω → Act
  /-- The joint argmax for `(A', o, o')`. -/
  αJ : Finset Act → ↥𝒟 → ↥𝒟 → P.Ω → Act
  /-- The conditional argmax at `o` given `π*(o') = a'`. -/
  αC : ↥𝒟 → Act → ↥𝒟 → P.Ω → Act

variable {P}

/-- The mass of the cell `pp · o = b ∧ pp · o' = αJ A' o o'` (the event whose second conjunct is
the agent's own joint-argmax computation).
Source: `main.tex` 222
Kind: D
Fidelity: exact -/
def jointMass (V : ArgmaxVars P) (A' : Finset Act) (o o' : ↥𝒟) (b : Act) : ℚ :=
  massOf P.μ (fun ω => P.pp ω o = b ∧ P.pp ω o' = V.αJ A' o o' ω)

/-- The value of the cell `pp · o = b ∧ pp · o' = αJ A' o o'`.
Source: `main.tex` 222
Kind: D
Fidelity: exact -/
def jointEU (V : ArgmaxVars P) (A' : Finset Act) (o o' : ↥𝒟) (b : Act) : ℚ :=
  condExp P.μ P.U (fun ω => P.pp ω o = b ∧ P.pp ω o' = V.αJ A' o o' ω)

/-- **Faith in Joint Argmax at `(A', o, o')`** (the instance Theorem 3 uses): the maximum over
`a ∈ A'` of the value conditioned on the agent's joint-argmax computation at `o'` is at least the
maximum over the concrete cells `(a, a')`, `a ∈ A'` — stated over positive cells: every positive
concrete cell is dominated by some positive `αJ`-cell. The paper's `∀ A' ⊆ 𝒜, ∀ o ≠ o'` form is
`FaithInJointArgmax`.
The positivity of the dominating `αJ`-cell is asserted as a conjunct of the hypothesis — a
strengthening of the paper's display (which has no such clause, and under the junk conventions
would read `0 ≥ max …` at a null `αJ`-cell). Inside Theorem 3's package it is redundant: AC + KDP
make the `αJ`-cell of `b` the point `pp · o = b`, whose positivity is what keeps the conclusion
off junk (`fja_pinned`). The clause is there to keep the predicate off junk when used alone.
Source: `main.tex` 219–225 (bli-paper-010)
Kind: D
Fidelity: variant: positive cells only (no `sup'` over junk), the dominating cell's positivity
asserted (stronger than the paper's display; redundant inside Theorem 3's package);
computation-output model (c) -/
def FaithInJointArgmaxAt (V : ArgmaxVars P) (A' : Finset Act) (o o' : ↥𝒟) : Prop :=
  ∀ a' : Act, ∀ a ∈ A', 0 < P.pairMass o o' a a' →
    ∃ b ∈ A', 0 < jointMass V A' o o' b ∧ cellEU P o o' a a' ≤ jointEU V A' o o' b

/-- **Faith in Joint Argmax**, the paper's quantified form: at every `A'` and every `o ≠ o'`.
Source: `main.tex` 219–225 (bli-paper-010)
Kind: D
Fidelity: variant as `FaithInJointArgmaxAt` -/
def FaithInJointArgmax (V : ArgmaxVars P) : Prop :=
  ∀ (A' : Finset Act) (o o' : ↥𝒟), o ≠ o' → FaithInJointArgmaxAt V A' o o'

/-- **Action Coordination at `(A', o, o')`**: with probability one, the joint-argmax computation
for `(A', o, o')` and the marginal argmax computation at `o'` agree. The paper fixes
`A' = 𝒜^{-m}`; Theorem 3 uses `A' = nonModAt o`.
Source: `main.tex` 227–231 (bli-paper-011)
Kind: D
Fidelity: exact (computation-output model (c)); the extensional form is `Collapse.lean`'s
`actionCoordination_const_iff` -/
def ActionCoordination (V : ArgmaxVars P) (A' : Finset Act) (o o' : ↥𝒟) : Prop :=
  massOf P.μ (fun ω => V.αJ A' o o' ω = V.αM o' ω) = 1

/-- **Knowledge of Decision Procedure at `o`**: with probability one, the chosen point at `o` is
the output of the marginal argmax computation at `o`. (The paper's argmax ranges over `𝒜` where
the rule uses `𝒜_o` — bli-paper-012; the variable `αM o` carries whichever is meant.)
Source: `main.tex` 233–237 (bli-paper-012)
Kind: D
Fidelity: exact (computation-output model (c)); extensional form `kdp_const_null` -/
def KnowledgeOfDecisionProcedure (V : ArgmaxVars P) (o : ↥𝒟) : Prop :=
  massOf P.μ (fun ω => P.pp ω o = V.αM o ω) = 1

/-- **Faith in Argmax (Appendix A) at `(o, o', a')`**: with `φ = (π*(o') = a')`, the value of
`φ ∧ π*(o) = αC o' a' o` (the agent's conditional-argmax computation) is at least every concrete
`φ ∧ π*(o) = a` of positive mass, and that computation's cell is positive. The positivity
conjunct is a strengthening of Appendix A's display (which has none); inside Theorem 4's package
it is redundant — NAC + KDP make the `αC`-cell the twin's point, positive already by the
fairness-cell hypothesis — so `thm4_forces_equality` is not an artifact of the clause; it is
there to keep the predicate off junk when used alone.
Source: `main.tex` 365–370 (bli-paper-014)
Kind: D
Fidelity: variant: positive cells only, the `αC`-cell's positivity asserted (stronger than the
paper's display; redundant inside Theorem 4's package); computation-output model (c) -/
def FaithInArgmax (V : ArgmaxVars P) (o o' : ↥𝒟) (a' : Act) : Prop :=
  ∀ a : Act, 0 < P.pairMass o' o a' a →
    0 < massOf P.μ (fun ω => P.pp ω o' = a' ∧ P.pp ω o = V.αC o' a' o ω) ∧
    cellEU P o' o a' a ≤ condExp P.μ P.U (fun ω => P.pp ω o' = a' ∧ P.pp ω o = V.αC o' a' o ω)

/-- **Naive Action Coordination (Appendix A) at `(o₁, o₂, a₁)`**: for non-modifying `a₁`, with
probability one the conditional argmax at `o₁` given `π*(o₂) = a₁` agrees with the marginal
argmax at `o₁`.
Source: `main.tex` 372–376 (bli-paper-015)
Kind: D
Fidelity: exact (computation-output model (c)) -/
def NaiveActionCoordination (V : ArgmaxVars P) (o₁ o₂ : ↥𝒟) (a₁ : Act) : Prop :=
  a₁ ∉ S.selfMod → massOf P.μ (fun ω => V.αC o₂ a₁ o₁ ω = V.αM o₁ ω) = 1

/-! ## Theorem 3 -/

omit [Fintype Act] in
/-- Under Action Coordination, the `αJ`-cell of `b` has the mass and value of the `αM`-cell.
Source: none: infrastructure (the AC step of Theorem 3's proof, `main.tex` 251–253)
Kind: L
Fidelity: n/a -/
lemma ac_step (V : ArgmaxVars P) {A' : Finset Act} {o o' : ↥𝒟}
    (hAC : ActionCoordination V A' o o') (b : Act) :
    jointMass V A' o o' b = massOf P.μ (fun ω => P.pp ω o = b ∧ P.pp ω o' = V.αM o' ω) ∧
    jointEU V A' o o' b = condExp P.μ P.U (fun ω => P.pp ω o = b ∧ P.pp ω o' = V.αM o' ω) := by
  unfold ActionCoordination at hAC
  rw [massOf_eq_one_iff P.μ P.μ_sum_one, massOf_not_eq_zero_iff P.μ P.μ_nonneg] at hAC
  have hnull : massOf P.μ (fun ω => ¬ ((P.pp ω o = b ∧ P.pp ω o' = V.αJ A' o o' ω) ↔
      (P.pp ω o = b ∧ P.pp ω o' = V.αM o' ω))) = 0 := by
    rw [massOf_not_eq_zero_iff P.μ P.μ_nonneg]
    intro ω hpos
    rw [hAC ω hpos]
  exact ⟨massOf_congr_null P.μ P.μ_nonneg hnull, condExp_congr_null P.μ P.U P.μ_nonneg hnull⟩

omit [Fintype Act] in
/-- Under Knowledge of Decision Procedure at `o'`, the conjunct `pp · o' = αM o'` can be dropped:
the `αM`-cell of `b` has the mass and value of the point `pp · o = b`.
Source: none: infrastructure (the KDP step of Theorem 3's proof, `main.tex` 255–257)
Kind: L
Fidelity: n/a -/
lemma kdp_step (V : ArgmaxVars P) {o' : ↥𝒟} (hK : KnowledgeOfDecisionProcedure V o')
    (o : ↥𝒟) (b : Act) :
    massOf P.μ (fun ω => P.pp ω o = b ∧ P.pp ω o' = V.αM o' ω) = P.ppMass o b ∧
    condExp P.μ P.U (fun ω => P.pp ω o = b ∧ P.pp ω o' = V.αM o' ω) = P.EU o b := by
  unfold KnowledgeOfDecisionProcedure at hK
  rw [massOf_eq_one_iff P.μ P.μ_sum_one] at hK
  exact ⟨massOf_and_eq_of_ae P.μ P.μ_nonneg _ _ hK, condExp_and_eq_of_ae P.μ P.U P.μ_nonneg _ _ hK⟩

/-- **Theorem 3 (the Vingean tiling theorem for UDT 1.0), computation-output model.** Let `pp` be
the chosen policy. Under Limited Self-Modification, Fine-Grained Fairness, Faith in Joint Argmax
at `(𝒜^{-m} ∩ 𝒜_o, o, ob aₘ)`, Action Coordination at that triple and Knowledge of Decision
Procedure at `ob aₘ`: for every available self-modifying action `aₘ` at `o` of positive mass
whose fairness cell is positive, there is an available non-modifying action `a` of positive
mass with `EU o aₘ ≤ EU o a`. The proof is the paper's seven-step chain: FGF; the twin's cell
is one of the concrete cells, so FJA gives a positive `αJ`-cell dominating it; AC replaces `αJ`
by `αM` (`condExp_congr_null`); KDP drops the `αM` conjunct (`condExp_and_eq_of_ae`). Every
intermediate cell is positive, so no step is about the junk value. Inside this package AC + KDP
pin `αJ` to `pp · ob aₘ` a.s., so the FJA hypothesis is `FaithInJointArgmaxPrior` on the prior
(`fja_pinned`, `thm3_prior`); the (c) is inert here. Kind L (regraded from C in repair round 2,
both audits): the body is one application of FGF, one instance of FJA, and two null-event
rewrites — the shape the package grades L for Theorems 1 and 2 and for `thm3_prior`.
Source: `main.tex` 239–261, Theorem 3 (bli-paper-013); bli-slides-028
Kind: L
Fidelity: variant: the FJA instance is the one used (the paper's `∀ A', ∀ o ≠ o'` form implies
it); AC (and that FJA instance) taken at `𝒜^{-m} ∩ 𝒜_o` rather than the paper's `𝒜^{-m}` — the
paper's literal AC instance does not imply this one, and its literal statement would need "`pp`
a.s. well-typed" to make the dominating action available (bli-paper-013(ii)); computation-output
model (c), positive cells only
Hyps: (c) the model (`V` as coordinates; FJA, AC, KDP, FGF about them); (a) the positivities
named -/
theorem thm3_vingean_tiling (L : LimitedSelfMod S) (V : ArgmaxVars P)
    (hFGF : FineGrainedFairness P S L) (o : ↥𝒟) (aₘ : Act) (haₘ : aₘ ∈ S.Aof o)
    (hm : aₘ ∈ S.selfMod) (hpos : 0 < P.ppMass o aₘ)
    (hcell : 0 < P.pairMass o (L.ob aₘ) (S.twin aₘ) (L.ac aₘ))
    (hFJA : FaithInJointArgmaxAt V (S.nonModAt o) o (L.ob aₘ))
    (hAC : ActionCoordination V (S.nonModAt o) o (L.ob aₘ))
    (hKDP : KnowledgeOfDecisionProcedure V (L.ob aₘ)) :
    ∃ a ∈ S.Aof o, a ∉ S.selfMod ∧ 0 < P.ppMass o a ∧ P.EU o aₘ ≤ P.EU o a := by
  -- Step 1: Fine-Grained Fairness.
  have h1 : P.EU o aₘ = cellEU P o (L.ob aₘ) (S.twin aₘ) (L.ac aₘ) := hFGF o aₘ haₘ hm hpos hcell
  -- Step 2: the twin is a non-modifying available action, so FJA dominates its cell.
  have htwin : S.twin aₘ ∈ S.nonModAt o := by
    rw [S.mem_nonModAt]
    exact ⟨S.twin_typed aₘ o haₘ, S.twin_nonMod aₘ⟩
  obtain ⟨b, hb, hbpos, hble⟩ := hFJA (L.ac aₘ) (S.twin aₘ) htwin hcell
  -- Steps 3–4: Action Coordination, then Knowledge of Decision Procedure.
  obtain ⟨hmass₁, hval₁⟩ := ac_step V hAC b
  obtain ⟨hmass₂, hval₂⟩ := kdp_step V hKDP o b
  rw [S.mem_nonModAt] at hb
  refine ⟨b, hb.1, hb.2, ?_, ?_⟩
  · rw [← hmass₂, ← hmass₁]; exact hbpos
  · rw [h1, ← hval₂, ← hval₁]; exact hble

/-! ## The computation-output model is inert inside Theorem 3's package (audit r1) -/

/-- **Faith in Joint Argmax over the bare prior at `(A', o, o')`** — the `V`-free content of
`FaithInJointArgmaxAt` once AC and KDP pin `αJ` to `pp · o'`: every positive concrete cell
`(a, a')` with `a ∈ A'` is dominated by some positive marginal `EU o b`, `b ∈ A'`.
Source: audit r1 adversarial probe `VingeanPinned` (B1); `main.tex` 219–225 read through AC + KDP
Kind: D
Fidelity: variant: the prior-level form Theorem 3's package reduces to -/
def FaithInJointArgmaxPrior (P : FiniteBLIPrior 𝒮 m 𝒟 Act) (A' : Finset Act) (o o' : ↥𝒟) : Prop :=
  ∀ a' : Act, ∀ a ∈ A', 0 < P.pairMass o o' a a' →
    ∃ b ∈ A', 0 < P.ppMass o b ∧ cellEU P o o' a a' ≤ P.EU o b

omit [Fintype Act] in
/-- **AC + KDP pin the model**: under Action Coordination at the triple and Knowledge of Decision
Procedure at `o'`, Faith in Joint Argmax at the triple is `FaithInJointArgmaxPrior` — for any `V`.
Source: audit r1 adversarial probe `VingeanPinned` (B1)
Kind: P
Fidelity: exact
Hyps: (c) the model; (a) AC, KDP about it -/
theorem fja_pinned (V : ArgmaxVars P) {A' : Finset Act} {o o' : ↥𝒟}
    (hAC : ActionCoordination V A' o o') (hK : KnowledgeOfDecisionProcedure V o') :
    FaithInJointArgmaxAt V A' o o' ↔ FaithInJointArgmaxPrior P A' o o' := by
  unfold FaithInJointArgmaxAt FaithInJointArgmaxPrior
  have hm : ∀ b, jointMass V A' o o' b = P.ppMass o b := fun b => by
    rw [(ac_step V hAC b).1, (kdp_step V hK o b).1]
  have hv : ∀ b, jointEU V A' o o' b = P.EU o b := fun b => by
    rw [(ac_step V hAC b).2, (kdp_step V hK o b).2]
  simp only [hm, hv]

/-- The trivial variables: every argmax computation *is* the policy coordinate.
Source: audit r1 adversarial probe `VingeanPinned`
Kind: D
Fidelity: n/a -/
def ppVars (P : FiniteBLIPrior 𝒮 m 𝒟 Act) : ArgmaxVars P where
  αM := fun o ω => P.pp ω o
  αJ := fun _ _ o' ω => P.pp ω o'
  αC := fun _ _ o ω => P.pp ω o

omit [Fintype Act] in
/-- `ppVars` satisfies Action Coordination everywhere (`massOf_true`).
Source: audit r1 adversarial probe. Kind: L. Fidelity: n/a -/
theorem ppVars_ac (A' : Finset Act) (o o' : ↥𝒟) : ActionCoordination (ppVars P) A' o o' := by
  unfold ActionCoordination
  rw [← P.massOf_true]
  exact massOf_congr P.μ (fun ω => by simp [ppVars])

omit [Fintype Act] in
/-- `ppVars` satisfies Knowledge of Decision Procedure everywhere (`massOf_true`).
Source: audit r1 adversarial probe. Kind: L. Fidelity: n/a -/
theorem ppVars_kdp (o : ↥𝒟) : KnowledgeOfDecisionProcedure (ppVars P) o := by
  unfold KnowledgeOfDecisionProcedure
  rw [← P.massOf_true]
  exact massOf_congr P.μ (fun ω => by simp [ppVars])

omit [Fintype Act] in
/-- **The computation-output model is inert inside Theorem 3's package**: some `V` satisfies FJA
at the triple together with AC there and KDP at `o'` iff the bare prior satisfies
`FaithInJointArgmaxPrior`.
Source: audit r1 adversarial probe `VingeanPinned` (B1)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem exists_vars_iff (A' : Finset Act) (o o' : ↥𝒟) :
    (∃ V : ArgmaxVars P, FaithInJointArgmaxAt V A' o o' ∧ ActionCoordination V A' o o' ∧
      KnowledgeOfDecisionProcedure V o') ↔ FaithInJointArgmaxPrior P A' o o' := by
  constructor
  · rintro ⟨V, hF, hAC, hK⟩
    exact (fja_pinned V hAC hK).mp hF
  · intro h
    exact ⟨ppVars P, (fja_pinned (ppVars P) (ppVars_ac A' o o') (ppVars_kdp o')).mpr h,
      ppVars_ac A' o o', ppVars_kdp o'⟩

/-- **Theorem 3 over the bare prior**: Limited Self-Modification, Fine-Grained Fairness and
`FaithInJointArgmaxPrior` at `(𝒜^{-m} ∩ 𝒜_o, o, ob aₘ)` give Theorem 3's conclusion, with no
argmax variables at all. By `exists_vars_iff` this is exactly what `thm3_vingean_tiling` says
once its AC and KDP hypotheses are accounted for; the proof is FGF followed by one instance of
the prior-form hypothesis at the fairness cell.
Source: audit r1 adversarial B1; `main.tex` 239–261 read through AC + KDP
Kind: L
Fidelity: variant: the prior-level form; the max over `𝒜^{-m} ∩ 𝒜_o`; positive cells only
Hyps: (a) FGF, `FaithInJointArgmaxPrior`, the positivities named -/
theorem thm3_prior (L : LimitedSelfMod S) (hFGF : FineGrainedFairness P S L) (o : ↥𝒟) (aₘ : Act)
    (haₘ : aₘ ∈ S.Aof o) (hm : aₘ ∈ S.selfMod) (hpos : 0 < P.ppMass o aₘ)
    (hcell : 0 < P.pairMass o (L.ob aₘ) (S.twin aₘ) (L.ac aₘ))
    (hFJA : FaithInJointArgmaxPrior P (S.nonModAt o) o (L.ob aₘ)) :
    ∃ a ∈ S.Aof o, a ∉ S.selfMod ∧ 0 < P.ppMass o a ∧ P.EU o aₘ ≤ P.EU o a :=
  thm3_vingean_tiling S L (ppVars P) hFGF o aₘ haₘ hm hpos hcell
    ((fja_pinned (ppVars P) (ppVars_ac _ _ _) (ppVars_kdp _)).mpr hFJA) (ppVars_ac _ _ _)
    (ppVars_kdp _)

/-! ## Convex-combination lemmas (audit r1) -/

/-- A convex combination of values each `≤ c` that equals `c` has every positively-weighted value
equal to `c`.
Source: none: infrastructure (audit r1 adversarial probe `Thm4Equality`)
Kind: L
Fidelity: n/a -/
lemma eq_of_convex_le {ι : Type} [Fintype ι] (w f : ι → ℚ) (c : ℚ) (hw : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) (hle : ∀ i, 0 < w i → f i ≤ c) (hsum : ∑ i, w i * f i = c) :
    ∀ i, 0 < w i → f i = c := by
  have hterm : ∀ i, 0 ≤ w i * (c - f i) := by
    intro i
    by_cases hi : 0 < w i
    · exact mul_nonneg (hw i) (sub_nonneg.mpr (hle i hi))
    · have : w i = 0 := le_antisymm (not_lt.mp hi) (hw i)
      rw [this, zero_mul]
  have hzero : ∑ i, w i * (c - f i) = 0 := by
    have : ∑ i, w i * (c - f i) = c * ∑ i, w i - ∑ i, w i * f i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [this, h1, mul_one, hsum, sub_self]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm i)] at hzero
  intro i hi
  have := hzero i (Finset.mem_univ i)
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (ne_of_gt hi)
  · linarith

/-- The marginal value at `o` is the `pairMass`-weighted mixture of the joint cells over the
`o'`-point.
Source: none: infrastructure (audit r1 adversarial probe `Thm4Equality`)
Kind: L
Fidelity: n/a -/
lemma EU_eq_sum_cells (o o' : ↥𝒟) (t : Act) :
    P.EU o t = ∑ b, P.pairMass o o' t b / P.ppMass o t * cellEU P o o' t b := by
  unfold FiniteBLIPrior.EU
  rw [condExp_fiberwise P.μ P.U P.μ_nonneg (fun ω => P.pp ω o = t) (fun ω => P.pp ω o')]
  rfl

/-- The weights of `EU_eq_sum_cells` sum to one when the point is positive.
Source: none: infrastructure (audit r1 adversarial probe `Thm4Equality`)
Kind: L
Fidelity: n/a -/
lemma sum_pair_div (o o' : ↥𝒟) (t : Act) (hpos : 0 < P.ppMass o t) :
    ∑ b, P.pairMass o o' t b / P.ppMass o t = 1 := by
  have hsum : ∑ b, P.pairMass o o' t b = P.ppMass o t := by
    unfold FiniteBLIPrior.ppMass FiniteBLIPrior.pairMass
    exact (massOf_fiberwise P.μ _ (fun ω => P.pp ω o')).symm
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, hsum, mul_inv_cancel₀ (ne_of_gt hpos)]

/-- **Under the prior-form hypothesis, the best non-modifying action's row is flat**: if `b ∈ A'`
is positive and at least as good as every positive `b' ∈ A'`, then every positive cell `(b, a')`
has exactly the value `EU o b` — each cell is `≤` some marginal `≤ EU o b`, and `EU o b` is their
convex combination. The Theorem 3 analogue of `thm4_forces_equality`.
Source: audit r1 adversarial N1 ("the same structure for Theorem 3")
Kind: P
Fidelity: n/a (a consequence of the hypothesis, not a claim of the paper)
Hyps: (a) `FaithInJointArgmaxPrior`, the positivities, maximality of `b` -/
theorem row_flat_of_fjaPrior {A' : Finset Act} {o o' : ↥𝒟} (h : FaithInJointArgmaxPrior P A' o o')
    (b : Act) (hb : b ∈ A') (hbpos : 0 < P.ppMass o b)
    (hbest : ∀ b' ∈ A', 0 < P.ppMass o b' → P.EU o b' ≤ P.EU o b) :
    ∀ a', 0 < P.pairMass o o' b a' → cellEU P o o' b a' = P.EU o b := by
  have hle : ∀ a', 0 < P.pairMass o o' b a' → cellEU P o o' b a' ≤ P.EU o b := by
    intro a' ha'
    obtain ⟨b', hb', hb'pos, hle⟩ := h a' b hb ha'
    exact le_trans hle (hbest b' hb' hb'pos)
  have hmix := EU_eq_sum_cells (P := P) o o' b
  have hw : ∀ a', 0 ≤ P.pairMass o o' b a' / P.ppMass o b :=
    fun a' => div_nonneg (massOf_nonneg _ P.μ_nonneg _) (le_of_lt hbpos)
  have hkey := eq_of_convex_le (fun a' => P.pairMass o o' b a' / P.ppMass o b)
    (fun a' => cellEU P o o' b a') (P.EU o b) hw (sum_pair_div o o' b hbpos)
    (fun a' ha' => hle a' (by
      by_cases hp : 0 < P.pairMass o o' b a'
      · exact hp
      · exfalso
        have hz : P.pairMass o o' b a' = 0 :=
          le_antisymm (not_lt.mp hp) (massOf_nonneg _ P.μ_nonneg _)
        simp [hz] at ha'))
    hmix.symm
  intro a' ha'
  exact hkey a' (div_pos ha' hbpos)

/-! ## Theorem 4 (Appendix A) -/

/-- Under Naive Action Coordination at `(o₁, o₂, a₁)` (with `a₁` non-modifying), the
`αC`-cell has the mass and value of the `αM`-cell.
Source: none: infrastructure (the NAC step of Theorem 4's proof, `main.tex` 393–395)
Kind: L
Fidelity: n/a -/
lemma nac_step (V : ArgmaxVars P) {o₁ o₂ : ↥𝒟} {a₁ : Act} (ha₁ : a₁ ∉ S.selfMod)
    (hN : NaiveActionCoordination S V o₁ o₂ a₁) :
    massOf P.μ (fun ω => P.pp ω o₂ = a₁ ∧ P.pp ω o₁ = V.αC o₂ a₁ o₁ ω) =
      massOf P.μ (fun ω => P.pp ω o₂ = a₁ ∧ P.pp ω o₁ = V.αM o₁ ω) ∧
    condExp P.μ P.U (fun ω => P.pp ω o₂ = a₁ ∧ P.pp ω o₁ = V.αC o₂ a₁ o₁ ω) =
      condExp P.μ P.U (fun ω => P.pp ω o₂ = a₁ ∧ P.pp ω o₁ = V.αM o₁ ω) := by
  have hN' := hN ha₁
  rw [massOf_eq_one_iff P.μ P.μ_sum_one, massOf_not_eq_zero_iff P.μ P.μ_nonneg] at hN'
  have hnull : massOf P.μ (fun ω => ¬ ((P.pp ω o₂ = a₁ ∧ P.pp ω o₁ = V.αC o₂ a₁ o₁ ω) ↔
      (P.pp ω o₂ = a₁ ∧ P.pp ω o₁ = V.αM o₁ ω))) = 0 := by
    rw [massOf_not_eq_zero_iff P.μ P.μ_nonneg]
    intro ω hpos
    rw [hN' ω hpos]
  exact ⟨massOf_congr_null P.μ P.μ_nonneg hnull, condExp_congr_null P.μ P.U P.μ_nonneg hnull⟩

/-- **Theorem 4 (Appendix A's variant), computation-output model.** Let `pp` be the chosen
policy. Under Limited Self-Modification, Fine-Grained Fairness, Faith in Argmax at
`(ob aₘ, o, twin aₘ)`, Naive Action Coordination at `(ob aₘ, o, twin aₘ)` and Knowledge of
Decision Procedure at `ob aₘ`: for every available self-modifying `aₘ` at `o` of positive mass
whose fairness cell is positive, `EU o aₘ ≤ EU o (twin aₘ)` — the sharper conclusion
(bli-paper-016: the self-modification is at most as good as *its own* twin). Chain: FGF; FA
dominates the cell `(twin aₘ, ac aₘ)` by the `αC`-cell; NAC replaces `αC` by `αM`; KDP drops
the conjunct. The twin's point is positive as a consequence. Kind L (regraded from C in repair
round 2, both audits): FGF, one FA instance, and two null-event rewrites — the same shape as
Theorem 3.
Source: `main.tex` 363–404, Theorem 4 (bli-paper-016); bli-slides-045
Kind: L
Fidelity: stronger: the instances actually used; variant: computation-output model (c),
positive cells only; the prose's "at least as great" is `≤` (presentation)
Hyps: (c) the model; (a) the positivities named -/
theorem thm4_appendixA_tiling (L : LimitedSelfMod S) (V : ArgmaxVars P)
    (hFGF : FineGrainedFairness P S L) (o : ↥𝒟) (aₘ : Act) (haₘ : aₘ ∈ S.Aof o)
    (hm : aₘ ∈ S.selfMod) (hpos : 0 < P.ppMass o aₘ)
    (hcell : 0 < P.pairMass o (L.ob aₘ) (S.twin aₘ) (L.ac aₘ))
    (hFA : FaithInArgmax V (L.ob aₘ) o (S.twin aₘ))
    (hNAC : NaiveActionCoordination S V (L.ob aₘ) o (S.twin aₘ))
    (hKDP : KnowledgeOfDecisionProcedure V (L.ob aₘ)) :
    0 < P.ppMass o (S.twin aₘ) ∧ P.EU o aₘ ≤ P.EU o (S.twin aₘ) := by
  have h1 : P.EU o aₘ = cellEU P o (L.ob aₘ) (S.twin aₘ) (L.ac aₘ) := hFGF o aₘ haₘ hm hpos hcell
  obtain ⟨hCpos, hCle⟩ := hFA (L.ac aₘ) hcell
  obtain ⟨hmass₁, hval₁⟩ := nac_step S V (S.twin_nonMod aₘ) hNAC
  obtain ⟨hmass₂, hval₂⟩ := kdp_step V hKDP o (S.twin aₘ)
  refine ⟨?_, ?_⟩
  · rw [← hmass₂, ← hmass₁]; exact hCpos
  · rw [h1, ← hval₂, ← hval₁]; exact hCle

/-- **Theorem 4's hypotheses force equality**: with exactly the hypotheses of
`thm4_appendixA_tiling`, `EU o aₘ = EU o (twin aₘ)`. NAC + KDP pin the `αC`-cell to the point
`pp · o = twin aₘ`, so Faith in Argmax says every positive cell of the twin's row is
`≤ EU o (twin aₘ)`; that marginal is the convex combination of exactly those cells
(`EU_eq_sum_cells`), so every positive cell equals it (`eq_of_convex_le`); the fairness cell is
positive and FGF identifies `EU o aₘ` with it. Appendix A's package therefore forces the twin's
conditional value to be independent of the `ō`-point, and the self-modification to be *exactly*
as good as its twin — the paper's `≤` is weaker than its own hypotheses give (finding F-18).
Source: audit r1 adversarial probe `Thm4Equality` (N1); `main.tex` 363–404
Kind: P
Fidelity: stronger: equality where Theorem 4 concludes `≤`; variant as `thm4_appendixA_tiling`
Hyps: as `thm4_appendixA_tiling` -/
theorem thm4_forces_equality (L : LimitedSelfMod S) (V : ArgmaxVars P)
    (hFGF : FineGrainedFairness P S L) (o : ↥𝒟) (aₘ : Act) (haₘ : aₘ ∈ S.Aof o)
    (hm : aₘ ∈ S.selfMod) (hpos : 0 < P.ppMass o aₘ)
    (hcell : 0 < P.pairMass o (L.ob aₘ) (S.twin aₘ) (L.ac aₘ))
    (hFA : FaithInArgmax V (L.ob aₘ) o (S.twin aₘ))
    (hNAC : NaiveActionCoordination S V (L.ob aₘ) o (S.twin aₘ))
    (hKDP : KnowledgeOfDecisionProcedure V (L.ob aₘ)) :
    P.EU o aₘ = P.EU o (S.twin aₘ) := by
  -- the headline gives `≤` and the twin's positivity
  obtain ⟨htpos, _⟩ := thm4_appendixA_tiling S L V hFGF o aₘ haₘ hm hpos hcell hFA hNAC hKDP
  -- FGF
  have h1 : P.EU o aₘ = cellEU P o (L.ob aₘ) (S.twin aₘ) (L.ac aₘ) := hFGF o aₘ haₘ hm hpos hcell
  -- the `αC`-cell's value is the marginal `EU o (twin aₘ)` (NAC then KDP), as in the headline
  obtain ⟨_, hval₁⟩ := nac_step S V (S.twin_nonMod aₘ) hNAC
  obtain ⟨_, hval₂⟩ := kdp_step V hKDP o (S.twin aₘ)
  -- FA': every positive cell of the twin's row is `≤ EU o (twin aₘ)`
  have hFA' : ∀ b, 0 < P.pairMass o (L.ob aₘ) (S.twin aₘ) b →
      cellEU P o (L.ob aₘ) (S.twin aₘ) b ≤ P.EU o (S.twin aₘ) := by
    intro b hb
    have := (hFA b hb).2
    rwa [hval₁, hval₂] at this
  -- the row's convex combination is the marginal, so every positive cell equals it
  have hmix := EU_eq_sum_cells (P := P) o (L.ob aₘ) (S.twin aₘ)
  have hw : ∀ b, 0 ≤ P.pairMass o (L.ob aₘ) (S.twin aₘ) b / P.ppMass o (S.twin aₘ) :=
    fun b => div_nonneg (massOf_nonneg _ P.μ_nonneg _) (le_of_lt htpos)
  have hkey := eq_of_convex_le (fun b => P.pairMass o (L.ob aₘ) (S.twin aₘ) b / P.ppMass o (S.twin aₘ))
    (fun b => cellEU P o (L.ob aₘ) (S.twin aₘ) b) (P.EU o (S.twin aₘ)) hw
    (sum_pair_div o (L.ob aₘ) (S.twin aₘ) htpos)
    (fun b hb => hFA' b (by
      by_cases h : 0 < P.pairMass o (L.ob aₘ) (S.twin aₘ) b
      · exact h
      · exfalso
        have hz : P.pairMass o (L.ob aₘ) (S.twin aₘ) b = 0 :=
          le_antisymm (not_lt.mp h) (massOf_nonneg _ P.μ_nonneg _)
        simp [hz] at hb))
    hmix.symm
  rw [h1]
  exact hkey (L.ac aₘ) (div_pos hcell htpos)

end Cleanroom.Udt.UdtPaperTiling
