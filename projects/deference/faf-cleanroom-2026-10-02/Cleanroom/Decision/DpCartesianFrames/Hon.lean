import Cleanroom.Decision.DpCartesianFrames.Local
import Mathlib.Data.Set.Prod
import Mathlib.Tactic.FinCases

/-!
# Seeming to observe: the honest companion, the truth test, the image-product criterion

Package `dp-cartesian-frames`, file 6 (T9, headline 5).

* **`Hon C S`** (CF-20's honest companion, over any frame): `Assume^{E_S}(C) & Assume^{E_{¬S}}(C)`
  with `E_S := {e | ∀ a, a ⋆ e ∈ S}` and `E_{¬S} := {e | ∀ a, a ⋆ e ∉ S}` (post 11 §3's
  `Assume_{S_i}`); for column-determined `S` on a frame with a nonempty agent the two column
  sets partition `Env` (`splitCol`). Its agent is a cell-indexed pair of answers, and it
  observes `{S, Sᶜ}` unconditionally (`observable2_hon`).
* **The diagonal** `diagHom : C ⟶ Hon C S` (`a ↦ (a, a)`, identity on columns);
  `C ≅ (Hon C S).commit Δ` in `Chu(W)` (`honCommitIso`), hence `C ◁₊ Hon C S`
  (`addSubagent_hon`): seeming-to-observe is being the diagonal commitment inside the frame that
  could genuinely condition.
* **The truth test** (CF-21 / CFF-24, `observable2_iff_biextEquiv_hon`): for column-determined
  `S` and a nonempty agent, `Observable2 C S ↔ C ≃ᵇ Hon C S`. (⟸) transports `observable2_hon`
  along the equivalence by T9(a); (⟹) is a homotopy equivalence whose backward map sends a pair
  `(a₀, a₁)` to the policy realizing it.
* At a tree: `HonLoc obs d B := Hon (Loc d B) (S_{O_d})` and the instance
  `observable2_loc_iff_biextEquiv_honLoc`.
* **ZO-8's theorem** (`observable2_loc_twoBranch_iff_range_prod`): on the one-point two-branch
  tree `twoBranch β φ` (root coin; a `d`-node in each branch with leaf map `φ i`), with `S`
  containing the tails outcomes and excluding the heads outcomes, `{S, Sᶜ}` is observable at
  `Loc d` iff `range (φ 0 × φ 1) = range (φ 0) ×ˢ range (φ 1)` — the row set is a product; powerless
  outside `S` iff `φ 1` is constant; under the standard coupling `φ 1 = g ∘ φ 0`, observable iff
  powerless. The heads-honest policy-menu mugging (N+) is in `Witnesses.lean`.

Lazy seeding for the tree frames.
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames CategoryTheory
open scoped CartesianFrames.Frame

universe u

section hon

variable {W : Type u}

/-- **The honest companion** `Hon C S := Assume^{E_S}(C) & Assume^{E_{¬S}}(C)`: the frame
whose agent chooses one answer for the `S`-columns and one for the `Sᶜ`-columns — the frame
`C` would be if it could genuinely condition on `{S, Sᶜ}`. Meaningful as a partition of the
columns when `S` is column-determined (then `E_{¬S} = E_Sᶜ`).
Source: cf-correspondence CF-20 (line 104: "`Hon_d := Assume^{E^∀_S}(Loc_d) &
Assume^{E^∀_{¬S}}(Loc_d)`, agent `A_d × A_d`")
Kind: D
Fidelity: exact -/
def Hon (C : CartesianFrames.Frame W) (S : Set W) : CartesianFrames.Frame W :=
  Frame.sum (C.assume (colIn C S)) (C.assume (colIn C Sᶜ))

/-- **The diagonal morphism** `diag : C ⟶ Hon C S`: `g(a) = (a, a)`, `h` the identity on
columns; adjointness holds by construction (cases on the summand).
Source: cf-correspondence CF-20 (line 104: "the diagonal morphism `diag : Loc_d → Hon_d`:
`g(a) = (a, a)`, `h` = identity on columns")
Kind: D
Fidelity: exact -/
def diagHom (C : CartesianFrames.Frame W) (S : Set W) : C ⟶ Hon C S where
  agent a := (a, a)
  env e := Sum.elim Subtype.val Subtype.val e
  adjoint a e := by cases e <;> rfl

/-- **`Hon C S` observes `{S, Sᶜ}`** unconditionally: the pair `(a₀, a₁)` realizes the
conditional policy `(a₀ on S, a₁ off S)` cell by cell.
Source: cf-correspondence CF-21 proof (line 113: "in `Hon_d` the partition is always
observable (`a_f := (f(S)₁, f(¬S)₂)` works cell-by-cell)")
Kind: P
Fidelity: exact
Hyps: none -/
theorem observable2_hon (C : CartesianFrames.Frame W) (S : Set W) : Observable2 (Hon C S) S := by
  intro a₀ a₁
  refine ⟨(a₀.1, a₁.2), ?_⟩
  rintro (⟨e, he⟩ | ⟨e, he⟩)
  · exact ⟨fun _ => rfl, fun h => absurd (he a₀.1) h⟩
  · exact ⟨fun h => absurd h (he a₁.2), fun _ => rfl⟩

/-- For column-determined `S`, a column not entirely in `S` is entirely outside `S`.
Source: none: infrastructure
Kind: L -/
theorem mem_colIn_compl_of_not_mem {C : CartesianFrames.Frame W} {S : Set W}
    (hcd : ColumnDetermined C S) (e : C.Env) (h : e ∉ colIn C S) : e ∈ colIn C Sᶜ := by
  intro a
  by_contra ha
  apply h
  intro a'
  exact (hcd e a a').mp (Classical.not_not.mp ha)

/-- The column split of a column-determined frame: each column to its cell's summand.
Source: cf-correspondence CF-20 (line 104)
Kind: D -/
noncomputable def splitCol {C : CartesianFrames.Frame W} {S : Set W}
    (hcd : ColumnDetermined C S) (e : C.Env) : (Hon C S).Env :=
  open Classical in
  if h : e ∈ colIn C S then Sum.inl ⟨e, h⟩
  else Sum.inr ⟨e, mem_colIn_compl_of_not_mem hcd e h⟩

theorem elim_splitCol {C : CartesianFrames.Frame W} {S : Set W} (hcd : ColumnDetermined C S)
    (e : C.Env) : Sum.elim Subtype.val Subtype.val (splitCol hcd e) = e := by
  unfold splitCol
  split <;> rfl

theorem splitCol_elim {C : CartesianFrames.Frame W} {S : Set W} (hcd : ColumnDetermined C S)
    (hA : Nonempty C.Agent) (y : (Hon C S).Env) :
    splitCol hcd (Sum.elim Subtype.val Subtype.val y) = y := by
  obtain ⟨a⟩ := hA
  rcases y with ⟨e, he⟩ | ⟨e, he⟩
  · show splitCol hcd e = Sum.inl ⟨e, he⟩
    unfold splitCol
    exact dif_pos he
  · show splitCol hcd e = Sum.inr ⟨e, he⟩
    unfold splitCol
    exact dif_neg (fun h => (he a) (h a))

/-- **`C ≅ Commit^Δ(Hon C S)`** in `Chu(W)` for column-determined `S` on a frame with a
nonempty agent: `C` is the diagonal commitment inside its honest companion.
Source: cf-correspondence CF-20 (line 104: "Equivalently `Loc_d ≅ Commit^Δ(Hon_d) ◁₊ Hon_d`")
Kind: P
Fidelity: exact (side conditions made explicit: without column-determinedness a split column
lies in neither summand; without an agent every column lies in both)
Hyps: none -/
noncomputable def honCommitIso {C : CartesianFrames.Frame W} {S : Set W}
    (hcd : ColumnDetermined C S) (hA : Nonempty C.Agent) :
    C ≅ (Hon C S).commit (Set.range fun a : C.Agent => (a, a)) where
  hom :=
    { agent := fun a => ⟨(a, a), ⟨a, rfl⟩⟩
      env := fun y => Sum.elim Subtype.val Subtype.val y
      adjoint := fun a y => by cases y <;> rfl }
  inv :=
    { agent := fun x => x.val.1
      env := fun e => splitCol hcd e
      adjoint := fun x e => by
        obtain ⟨⟨a, b⟩, ⟨a', ha'⟩⟩ := x
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp ha'
        show (Hon C S).outcome (a', a') (splitCol hcd e) = C.outcome a' e
        unfold splitCol
        split <;> rfl }
  hom_inv_id := by
    apply Frame.Hom.ext
    · rfl
    · funext e; exact elim_splitCol hcd e
  inv_hom_id := by
    apply Frame.Hom.ext
    · funext x
      obtain ⟨⟨a, b⟩, ⟨a', ha'⟩⟩ := x
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp ha'
      rfl
    · funext y; exact splitCol_elim hcd hA y

/-- **`C ◁₊ Hon C S`**: through FAF's `commit_addSubagent` and the isomorphism.
Source: cf-correspondence CF-20 (line 104)
Kind: C
Fidelity: exact
Hyps: none -/
theorem addSubagent_hon {C : CartesianFrames.Frame W} {S : Set W} (hcd : ColumnDetermined C S)
    (hA : Nonempty C.Agent) : C ◁₊ Hon C S :=
  (Frame.commit_addSubagent (Hon C S) (Set.range fun a : C.Agent => (a, a))).congr
    (Frame.biextEquiv_of_nonempty_iso ⟨(honCommitIso hcd hA).symm⟩) (Frame.BiextEquiv.refl _)

/-- **The truth test** (CF-21 / CFF-24, headline 5): for column-determined `S` (on any frame —
no nonempty-agent hypothesis), `{S, Sᶜ}` is observable in `C` iff `C ≃ᵇ Hon C S`. (⟹): the homotopy
equivalence `diagHom` forward and, backward, `(a₀, a₁) ↦` the policy realizing that conditional
policy, with the column split; (⟸): `Hon C S` observes `S`, and observability is
biextensionally invariant (T9(a)).
Source: cf-correspondence CF-21 (line 113); cf-frontier CFF-24 (line 108); mandate T9(c)
Kind: P
Fidelity: exact (the sources presuppose column-determinedness; no nonempty-agent side
condition is needed for the test itself, only for the commit isomorphism)
Hyps: none -/
theorem observable2_iff_biextEquiv_hon {C : CartesianFrames.Frame W} {S : Set W}
    (hcd : ColumnDetermined C S) :
    Observable2 C S ↔ (C ≃ᵇ Hon C S) := by
  constructor
  · intro h
    refine Frame.biextEquiv_iff_homotopyEquiv.mpr ⟨diagHom C S, ?_, ?_, ?_⟩
    · exact
        { agent := fun x => Classical.choose (h x.1 x.2)
          env := fun e => splitCol hcd e
          adjoint := fun x e => by
            have hs := Classical.choose_spec (h x.1 x.2) e
            show (Hon C S).outcome x (splitCol hcd e) =
              C.outcome (Classical.choose (h x.1 x.2)) e
            unfold splitCol
            split
            · rename_i he
              exact (hs.1 (he _)).symm
            · rename_i he
              exact (hs.2 (mem_colIn_compl_of_not_mem hcd e he _)).symm }
    · intro a e
      simp only [Frame.id_env, Frame.comp_agent, Function.comp, id]
      have hs := Classical.choose_spec (h a a) e
      show C.outcome a e = C.outcome (Classical.choose (h a a)) e
      by_cases hm : C.outcome (Classical.choose (h a a)) e ∈ S
      · exact (hs.1 hm).symm
      · exact (hs.2 hm).symm
    · rintro x (⟨e, he⟩ | ⟨e, he⟩)
      · simp only [Frame.id_env, Frame.comp_agent, Function.comp, id]
        show C.outcome x.1 e = C.outcome (Classical.choose (h x.1 x.2)) e
        exact ((Classical.choose_spec (h x.1 x.2) e).1 (he _)).symm
      · simp only [Frame.id_env, Frame.comp_agent, Function.comp, id]
        show C.outcome x.2 e = C.outcome (Classical.choose (h x.1 x.2)) e
        exact ((Classical.choose_spec (h x.1 x.2) e).2 (he _)).symm
  · intro h
    exact (observable2_iff_of_biextEquiv h S).mpr (observable2_hon C S)

/-- Ensurability is invisible to `Hon`: `C` cannot ensure `S` iff `Hon C S` cannot (a row of
`Hon` in `S` everywhere gives a row of `C` in `S` on the `S`-columns and, on the `Sᶜ`-columns,
its second component contradicts). Recorded as the sanity check that `Hon` changes the
observability verdict and nothing about control.
Source: none: infrastructure (CF-20's "the gap `Hon_d ∖ Δ` measures the spoof")
Kind: L -/
theorem not_ensurable_hon_of_exists_compl {C : CartesianFrames.Frame W} {S : Set W}
    (hout : ∃ e, e ∈ colIn C Sᶜ) : ¬ Ensurable (Hon C S) S := by
  rintro ⟨⟨a₀, a₁⟩, ha⟩
  obtain ⟨e, he⟩ := hout
  exact (he a₁) (ha (Sum.inr ⟨e, he⟩))

end hon

/-! ### At a tree: `Hon_d` -/

section tree

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [DecidableEq ι]

/-- **`Hon_d(B)`**: the honest companion of the local frame for the claimed observation
`S_{O_d}`.
Source: cf-correspondence CF-20 (line 104)
Kind: D
Fidelity: exact -/
def HonLoc (obs : ι → Finset Ω) (d : ι) (B : Tree Ω ι acts K) : CartesianFrames.Frame (Ω × K) :=
  Hon (Loc d B) (SO obs d)

/-- **The truth test at a point** (CF-21): with `S_{O_d}` column-determined at `Loc d B`, the
pseudo-observation `(Loc d B, S_{O_d})` is a true Observation iff `Loc d B ≃ᵇ Hon_d(B)`.
Source: cf-correspondence CF-21 (line 113); mandate T9(c)
Kind: C
Fidelity: exact
Hyps: none -/
theorem observable2_loc_iff_biextEquiv_honLoc (obs : ι → Finset Ω)
    (d : ι) (B : Tree Ω ι acts K) (hcd : ColumnDetermined (Loc d B) (SO obs d)) :
    Observable2 (Loc d B) (SO obs d) ↔ (Loc d B ≃ᵇ HonLoc obs d B) :=
  observable2_iff_biextEquiv_hon hcd

end tree

/-! ### ZO-8: the one-point two-branch tree and the image-product criterion -/

section twoBranch

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {Ω A K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The one-point two-branch tree**: a root coin `β`; in branch `i` a node of the single
point with leaf map `φ i : A → Ω × K` (branch `0` = tails, `1` = heads).
Source: zoo ZO-8 Theorem (line 90: "a one-point tree with a chance root and a `d`-node in each
branch with edge maps `φ_T, φ_H`")
Kind: D
Fidelity: exact -/
def twoBranch (β : FinDistr K (Fin 2)) (φ : Fin 2 → A → Ω × K) : Tree Ω Unit (fun _ => A) K :=
  .chance 2 β fun i => .decision () fun a => .leaf (φ i a).1 (φ i a).2

/-- The local frame of the two-branch tree reads `φ i a` at a column whose coin is `i`.
Source: none: infrastructure
Kind: L -/
theorem loc_twoBranch_outcome (β : FinDistr K (Fin 2)) (φ : Fin 2 → A → Ω × K) (a : A)
    (p : (Loc () (twoBranch β φ)).Env) :
    (Loc () (twoBranch β φ)).outcome a p = φ p.2.1 a := by
  obtain ⟨p1, ⟨i, εs⟩⟩ := p
  show readout (twoBranch β φ)
    ⟨i, ⟨extend (acts := fun _ => A) () a p1 (), ()⟩⟩ = φ i a
  rw [extend_self]
  rfl

/-- The empty-domain component of a `Loc ()` column on a one-point tree.
Source: none: infrastructure
Kind: L -/
def noOther : (e : {e : Unit // e ≠ ()}) → A := fun e => absurd rfl e.property

/-- **ZO-8, policy form**: on the two-branch tree, with `S` containing every tails outcome and
no heads outcome, `{S, Sᶜ}` is observable at `Loc d` iff every splice of a tails row with a
heads row is a row (CFF-24's second clause).
Source: zoo ZO-8 Theorem (line 90); cf-frontier CFF-24 (line 108: "observable ⟺ every splice
is a row")
Kind: P
Fidelity: exact
Hyps: none -/
theorem observable2_loc_twoBranch_iff (β : FinDistr K (Fin 2)) (φ : Fin 2 → A → Ω × K)
    (S : Set (Ω × K)) (hT : ∀ a, φ 0 a ∈ S) (hH : ∀ a, φ 1 a ∉ S) :
    Observable2 (Loc () (twoBranch β φ)) S ↔
      ∀ a₀ a₁ : A, ∃ a, φ 0 a = φ 0 a₀ ∧ φ 1 a = φ 1 a₁ := by
  constructor
  · intro h a₀ a₁
    obtain ⟨a, ha⟩ := h a₀ a₁
    refine ⟨a, ?_, ?_⟩
    · have h0 := (ha (noOther, (0, fun _ _ => ()))).1
      rw [loc_twoBranch_outcome, loc_twoBranch_outcome] at h0
      exact h0 (hT a)
    · have h1 := (ha (noOther, (1, fun _ _ => ()))).2
      rw [loc_twoBranch_outcome, loc_twoBranch_outcome] at h1
      exact h1 (hH a)
  · intro h a₀ a₁
    obtain ⟨a, h0, h1⟩ := h a₀ a₁
    refine ⟨a, fun p => ?_⟩
    obtain ⟨_, ⟨i, _⟩⟩ := p
    rw [loc_twoBranch_outcome, loc_twoBranch_outcome, loc_twoBranch_outcome]
    dsimp only
    fin_cases i
    · exact ⟨fun _ => h0, fun hn => absurd (hT a) hn⟩
    · exact ⟨fun hs => absurd hs (hH a), fun _ => h1⟩

/-- **ZO-8's theorem, image-product form** (headline 5): on the two-branch tree, `{S, Sᶜ}` is
observable at `Loc d` iff the image of `φ_T × φ_H` is the product of the images.
Source: zoo ZO-8 Theorem (line 90: "observability of `{S_T, S_H}` in `Loc_d` ⟺
`image(φ_T × φ_H) = image φ_T × image φ_H`"); mandate T9(d)
Kind: P
Fidelity: exact
Hyps: none -/
theorem observable2_loc_twoBranch_iff_range_prod (β : FinDistr K (Fin 2))
    (φ : Fin 2 → A → Ω × K) (S : Set (Ω × K)) (hT : ∀ a, φ 0 a ∈ S) (hH : ∀ a, φ 1 a ∉ S) :
    Observable2 (Loc () (twoBranch β φ)) S ↔
      Set.range (fun a => (φ 0 a, φ 1 a)) = Set.range (φ 0) ×ˢ Set.range (φ 1) := by
  rw [observable2_loc_twoBranch_iff β φ S hT hH]
  constructor
  · intro h
    ext ⟨w₀, w₁⟩
    simp only [Set.mem_range, Set.mem_prod, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha₀, ha₁⟩
      exact ⟨⟨a, ha₀⟩, ⟨a, ha₁⟩⟩
    · rintro ⟨⟨a₀, ha₀⟩, ⟨a₁, ha₁⟩⟩
      obtain ⟨a, h0, h1⟩ := h a₀ a₁
      exact ⟨a, h0.trans ha₀, h1.trans ha₁⟩
  · intro h a₀ a₁
    have hmem : (φ 0 a₀, φ 1 a₁) ∈ Set.range (fun a => (φ 0 a, φ 1 a)) := by
      rw [h]
      exact ⟨⟨a₀, rfl⟩, ⟨a₁, rfl⟩⟩
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, congrArg Prod.fst ha, congrArg Prod.snd ha⟩

/-- **ZO-8, powerlessness clause**: `Loc d`'s agent is powerless outside `S` iff the heads leaf
map is constant.
Source: zoo ZO-8 Theorem (line 90: "powerlessness outside `S_T` ⟺ `φ_H` constant")
Kind: P
Fidelity: exact
Hyps: none -/
theorem powerlessOutside_loc_twoBranch_iff (β : FinDistr K (Fin 2)) (φ : Fin 2 → A → Ω × K)
    (S : Set (Ω × K)) (hT : ∀ a, φ 0 a ∈ S) (hH : ∀ a, φ 1 a ∉ S) :
    PowerlessOutside (Loc () (twoBranch β φ)) S ↔ ∀ a a', φ 1 a = φ 1 a' := by
  constructor
  · intro h a a'
    have := h (noOther, (1, fun _ _ => ())) a a'
    rw [loc_twoBranch_outcome, loc_twoBranch_outcome] at this
    exact this (hH a)
  · intro h p a₀ a₁ hout
    obtain ⟨_, ⟨i, _⟩⟩ := p
    rw [loc_twoBranch_outcome] at hout ⊢
    rw [loc_twoBranch_outcome]
    dsimp only at hout ⊢
    fin_cases i
    · exact absurd (hT a₀) hout
    · exact h a₀ a₁

/-- **ZO-8, the standard coupling**: when the heads outcome is a function of the tails outcome
(`φ_H = g ∘ φ_T`), observable ⟺ powerless — the image is a graph, a product only when the
function is constant.
Source: zoo ZO-8 Theorem (line 90: "If the heads outcome is a function of the tails outcome
(the standard coupling) … observable ⟺ powerless")
Kind: P
Fidelity: exact
Hyps: none -/
theorem observable2_iff_powerlessOutside_of_coupled (β : FinDistr K (Fin 2))
    (φ : Fin 2 → A → Ω × K) (S : Set (Ω × K)) (hT : ∀ a, φ 0 a ∈ S) (hH : ∀ a, φ 1 a ∉ S)
    (g : Ω × K → Ω × K) (hg : ∀ a, φ 1 a = g (φ 0 a)) :
    Observable2 (Loc () (twoBranch β φ)) S ↔ PowerlessOutside (Loc () (twoBranch β φ)) S := by
  constructor
  · intro h
    rw [observable2_loc_twoBranch_iff β φ S hT hH] at h
    rw [powerlessOutside_loc_twoBranch_iff β φ S hT hH]
    intro a a'
    obtain ⟨b, hb0, hb1⟩ := h a' a
    rw [← hb1, hg b, hb0, ← hg a']
  · exact PowerlessOutside.observable2

end twoBranch

end Cleanroom.Decision.DpCartesianFrames
