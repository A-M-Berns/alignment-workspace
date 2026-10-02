import Cleanroom.Lit.LitDdbAccuracyMm.MM.Defs

/-!
# MM Theorem 3.4: what is true (Target 15 (i), (iv), (v); item 090)

MM Theorem 3.4 (App. D l. 421): with stochastic choice, clarity, richness and constant acts,
"`π` values `(P, V)` iff for any acts `a, b ∈ A` and every `ω`, if `E_π(u(a) | [ω]) >
E_π(u(b) | [ω])` then `E_ω(V_ω(a)) > E_ω(V_ω(b))`". As printed it is false in both directions
(`MM/Refute.lean`), because MM's `B_ω` may break agent-ties differently at worlds of the same
type. What survives:

* **(i)** `ValuesB.weakAgree`: a valued behaviour, under clarity and richness, gives *weak*
  agreement — MM's first paragraph, with the splice `b⋆ := b` on `[ω]`, `a` off it.
* **(iv)** `typeMeasurable_valuesB_iff_strictAgree`: under clarity and richness, *every*
  type-measurable behaviour is valued iff strict agreement holds. Stochastic choice and constant
  acts are not needed. This is DDB's Value-over-all-recommended-strategies pattern (the cell
  constraint) and the neighbour `corr-legit-general` should import.
* **(v)** `StrictAgree.mass_le`: strict agreement with constant acts and richness makes the
  principal's conditional probabilities on `[ω]` weakly agree with the agent's:
  `P_ω(Y) ≤ P_ω(X) → π(Y | [ω]) ≤ π(X | [ω])` (stronger than the printed `>` ⟹ `≥`).
* **(090)** `strictAgree_affine`: strict agreement is invariant under positive affine changes
  of the agent's utilities — "near-perfect alignment" is not a theorem about `V` itself.
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm.MM

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W] {C : Type} [DecidableEq C]

/-! ## Type cells -/

/-- Membership in a type cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_tcell {G : GFrame W C} {ω ω' : W} :
    ω' ∈ tcell G ω ↔ G.Pag ω' = G.Pag ω ∧ G.V ω' = G.V ω := by
  simp [tcell]

/-- A world is in its own type cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_tcell_self (G : GFrame W C) (ω : W) : ω ∈ tcell G ω := by simp [tcell]

/-- Worlds of the same type have the same type cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tcell_eq_of_mem {G : GFrame W C} {ω ω' : W} (h : ω' ∈ tcell G ω) :
    tcell G ω' = tcell G ω := by
  rw [mem_tcell] at h
  ext w
  simp only [mem_tcell, h.1, h.2]

/-- The agent's expected utility depends on the world only through its type.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem agentEU_of_mem {G : GFrame W C} {ω ω' : W} (h : ω' ∈ tcell G ω) (a : W → C) :
    G.agentEU ω' a = G.agentEU ω a := by
  rw [mem_tcell] at h
  simp [GFrame.agentEU, h.1, h.2]

/-- Under clarity the agent's expected utility of a splice on the agent's own cell is that of
the spliced-in act: `E_ω(V_ω(splice [ω] b a)) = E_ω(V_ω(b))`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. D l. 437
("By clarity, `B_ω(A') = b⋆`")
Kind: L
Fidelity: n/a -/
theorem agentEU_splice_of_clarity {G : GFrame W C} (hcl : Clarity G) (ω : W) (b a : W → C) :
    G.agentEU ω (splice (tcell G ω) b a) = G.agentEU ω b := by
  unfold GFrame.agentEU E
  apply sum_congr rfl
  intro w _
  by_cases hw : w ∈ tcell G ω
  · simp [splice, hw]
  · rw [hcl ω w hw]; simp

/-- The conditional expected utility of the splice `b` on `[ω]`, `a` off it, is that of `b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cellEU_splice (π : W → ℝ) (G : GFrame W C) (ω : W) (b a : W → C) :
    cellEU π G ω (splice (tcell G ω) b a) = cellEU π G ω b := by
  unfold cellEU
  apply sum_congr rfl
  intro w hw
  simp [splice, hw]

/-- The delegated value of a menu splits along a type cell `K`: the part on `K` and the part
off `K`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem delegValue_split (π : W → ℝ) (G : GFrame W C) (B : W → Finset (W → C) → (W → C))
    (𝒜 : Finset (W → C)) (K : Finset W) :
    delegValue π G B 𝒜 = ∑ w ∈ K, π w * G.u (B w 𝒜 w) + ∑ w ∈ univ \ K, π w * G.u (B w 𝒜 w) := by
  unfold delegValue
  rw [add_comm, sum_sdiff (subset_univ K)]

/-- `E_π(u(a))` splits along a type cell `K`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_split (π : W → ℝ) (G : GFrame W C) (a : W → C) (K : Finset W) :
    E π (G.u ∘ a) = ∑ w ∈ K, π w * G.u (a w) + ∑ w ∈ univ \ K, π w * G.u (a w) := by
  unfold E
  rw [add_comm, sum_sdiff (subset_univ K)]
  rfl

/-! ## (i) Weak agreement from a valued behaviour -/

/-- **MM Theorem 3.4, the true part of (⟹).** A valued behaviour under clarity and richness gives
weak conditional preference agreement: if `E_π(u(a) | [ω]) > E_π(u(b) | [ω])` then
`E_ω(V_ω(a)) ≥ E_ω(V_ω(b))`. MM's splice argument with `b⋆ := b` on `[ω]`, `a` off it (the WLOG
`u(a₀, ·) = 0` is unnecessary in product form): were `E_ω(V_ω(a)) < E_ω(V_ω(b))`, by clarity
every world of the cell picks `b⋆` on `{a, b⋆}`, off the cell any choice agrees with `a`
pointwise, and delegation is worth less than `a`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.4 l. 421,
App. D l. 427–443; item 083
Kind: P
Fidelity: weaker: the conclusion is weak agreement — the printed strict conclusion is false
(`MM/Refute.lean`)
Hyps: (a) `IsBehaviour`, `ValuesB`, `Clarity`, `Richness` (the theorem's own hypotheses) -/
theorem ValuesB.weakAgree {π : W → ℝ} {G : GFrame W C}
    {B : W → Finset (W → C) → (W → C)} (hB : IsBehaviour G B) (hval : ValuesB π G B)
    (hcl : Clarity G) (hri : Richness G) : WeakAgree π G := by
  intro a ha b hb ω _ hlt
  by_contra hcon
  rw [not_le] at hcon
  set b' := splice (tcell G ω) b a with hb'
  have hb'A : b' ∈ G.A := hri b hb a ha (tcell G ω)
  have hsub : ({a, b'} : Finset (W → C)) ⊆ G.A := by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact ha
    · rw [mem_singleton] at hx; rw [hx]; exact hb'A
  have hval' := hval {a, b'} hsub (insert_nonempty _ _) a (mem_insert_self _ _)
  -- on the cell every world picks `b'`
  have hpick : ∀ w ∈ tcell G ω, B w {a, b'} = b' := by
    intro w hw
    obtain ⟨hmem, hopt⟩ := hB w {a, b'} hsub (insert_nonempty _ _)
    rcases mem_insert.1 hmem with h1 | h1
    · exfalso
      have h2 := hopt b' (mem_insert_of_mem (mem_singleton_self _))
      rw [h1] at h2
      have e1 : G.agentEU w b' = G.agentEU ω b := by
        rw [hb', ← tcell_eq_of_mem hw, agentEU_splice_of_clarity hcl, agentEU_of_mem hw]
      have e2 : G.agentEU w a = G.agentEU ω a := agentEU_of_mem hw a
      linarith
    · exact mem_singleton.1 h1
  -- off the cell every choice agrees with `a` pointwise
  have hoff : ∀ w, w ∉ tcell G ω → G.u (B w {a, b'} w) = G.u (a w) := by
    intro w hw
    obtain ⟨hmem, _⟩ := hB w {a, b'} hsub (insert_nonempty _ _)
    rcases mem_insert.1 hmem with h1 | h1
    · rw [h1]
    · rw [mem_singleton] at h1
      rw [h1, hb']
      simp [splice, hw]
  rw [delegValue_split π G B _ (tcell G ω), E_split π G a (tcell G ω)] at hval'
  have h1 : ∑ w ∈ tcell G ω, π w * G.u (B w {a, b'} w) = cellEU π G ω b := by
    unfold cellEU
    apply sum_congr rfl
    intro w hw
    rw [hpick w hw, hb']
    simp [splice, hw]
  have h2 : ∑ w ∈ univ \ tcell G ω, π w * G.u (B w {a, b'} w) =
      ∑ w ∈ univ \ tcell G ω, π w * G.u (a w) := by
    apply sum_congr rfl
    intro w hw
    rw [hoff w (mem_sdiff.1 hw).2]
  have h3 : ∑ w ∈ tcell G ω, π w * G.u (a w) = cellEU π G ω a := rfl
  rw [h1, h2, h3] at hval'
  linarith

/-! ## (iv) The repaired theorem -/

/-- A type-measurable optimal choice function: on a nonempty menu, some act maximising
`E_p(v ∘ ·)`, chosen by `Classical.choose` from the pair `(p, v)` only.
Source: none: infrastructure (Target 15 (iv), the witness behaviour)
Kind: D
Fidelity: n/a -/
def optChoice [Nonempty C] (p : W → ℝ) (v : C → ℝ) (𝒜 : Finset (W → C)) : W → C :=
  if h : 𝒜.Nonempty then Classical.choose (𝒜.exists_max_image (fun a => E p (v ∘ a)) h)
  else fun _ => Classical.arbitrary C

/-- The optimal choice is in the menu and maximises.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem optChoice_spec [Nonempty C] (p : W → ℝ) (v : C → ℝ) {𝒜 : Finset (W → C)}
    (h : 𝒜.Nonempty) :
    optChoice p v 𝒜 ∈ 𝒜 ∧ ∀ a ∈ 𝒜, E p (v ∘ a) ≤ E p (v ∘ optChoice p v 𝒜) := by
  unfold optChoice
  rw [dif_pos h]
  exact Classical.choose_spec (𝒜.exists_max_image (fun a => E p (v ∘ a)) h)

/-- **MM Theorem 3.4, repaired (⟹).** Under clarity and richness, if every type-measurable
behaviour is valued then strict agreement holds: a failure at `(a, b, ω)` is refuted by the
type-measurable behaviour that picks `b⋆ := splice [ω] b a` on the menu `{a, b⋆}` throughout the
cell (legitimate: `b⋆` is agent-optimal there) — MM's own splice.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.4 l. 421;
mandate Target 15 (iv)
Kind: P
Fidelity: variant: behaviours quantified over the type-measurable ones (the cell constraint)
Hyps: (a) `Clarity`, `Richness` -/
theorem strictAgree_of_forall_typeMeasurable [Nonempty C] {π : W → ℝ}
    {G : GFrame W C} (hcl : Clarity G) (hri : Richness G)
    (h : ∀ B, TypeMeasurable G B → IsBehaviour G B → ValuesB π G B) : StrictAgree π G := by
  intro a ha b hb ω hmass hlt
  by_contra hcon
  rw [not_lt] at hcon
  set b' := splice (tcell G ω) b a with hb'
  have hb'A : b' ∈ G.A := hri b hb a ha (tcell G ω)
  have hsub : ({a, b'} : Finset (W → C)) ⊆ G.A := by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact ha
    · rw [mem_singleton] at hx; rw [hx]; exact hb'A
  -- the type-measurable behaviour that picks `b'` on `{a, b'}` throughout the cell
  set B : W → Finset (W → C) → (W → C) := fun w 𝒜 =>
    if w ∈ tcell G ω ∧ 𝒜 = {a, b'} then b' else optChoice (G.Pag w) (G.V w) 𝒜 with hBdef
  have hBtm : TypeMeasurable G B := by
    intro w w' 𝒜 hw'
    have hK' : w ∈ tcell G ω ↔ w' ∈ tcell G ω := by
      constructor
      · intro hw
        rw [← tcell_eq_of_mem hw]
        exact hw'
      · intro hw''
        rw [← tcell_eq_of_mem hw'']
        rw [mem_tcell] at hw' ⊢
        exact ⟨hw'.1.symm, hw'.2.symm⟩
    have hp : G.Pag w' = G.Pag w := (mem_tcell.1 hw').1
    have hv : G.V w' = G.V w := (mem_tcell.1 hw').2
    simp only [hBdef, hK', hp, hv]
  have hBbeh : IsBehaviour G B := by
    intro w 𝒜 hsub' hne
    by_cases hc : w ∈ tcell G ω ∧ 𝒜 = {a, b'}
    · simp only [hBdef, if_pos hc]
      rw [hc.2]
      refine ⟨mem_insert_of_mem (mem_singleton_self _), ?_⟩
      intro x hx
      rcases mem_insert.1 hx with rfl | hx
      · have e1 : G.agentEU w b' = G.agentEU ω b := by
          rw [hb', ← tcell_eq_of_mem hc.1, agentEU_splice_of_clarity hcl, agentEU_of_mem hc.1]
        have e2 : G.agentEU w x = G.agentEU ω x := agentEU_of_mem hc.1 x
        rw [e1, e2]; exact hcon
      · rw [mem_singleton] at hx; rw [hx]
    · simp only [hBdef, if_neg hc]
      exact optChoice_spec (G.Pag w) (G.V w) hne
  have hval := h B hBtm hBbeh {a, b'} hsub (insert_nonempty _ _) a (mem_insert_self _ _)
  rw [delegValue_split π G B _ (tcell G ω), E_split π G a (tcell G ω)] at hval
  have h1 : ∑ w ∈ tcell G ω, π w * G.u (B w {a, b'} w) = cellEU π G ω b := by
    unfold cellEU
    apply sum_congr rfl
    intro w hw
    have hc : w ∈ tcell G ω ∧ ({a, b'} : Finset (W → C)) = {a, b'} := ⟨hw, rfl⟩
    have : B w {a, b'} = b' := by simp only [hBdef, if_pos hc]
    rw [this, hb']
    simp [splice, hw]
  have h2 : ∑ w ∈ univ \ tcell G ω, π w * G.u (B w {a, b'} w) =
      ∑ w ∈ univ \ tcell G ω, π w * G.u (a w) := by
    apply sum_congr rfl
    intro w hw
    have hwK := (mem_sdiff.1 hw).2
    obtain ⟨hmem, _⟩ := hBbeh w {a, b'} hsub (insert_nonempty _ _)
    rcases mem_insert.1 hmem with h1 | h1
    · rw [h1]
    · rw [mem_singleton] at h1
      rw [h1, hb']
      simp [splice, hwK]
  have h3 : ∑ w ∈ tcell G ω, π w * G.u (a w) = cellEU π G ω a := rfl
  rw [h1, h2, h3] at hval
  linarith

/-- **MM Theorem 3.4, repaired (⟸) — the unwritten direction.** Under strict agreement every
type-measurable behaviour is valued: on each type cell the behaviour's choice `b_K` is
agent-optimal, so by the contrapositive of strict agreement `∑_K π u(a) ≤ ∑_K π u(b_K)`, and
summing over the cells gives `E_π(u(a)) ≤ E_π(u(B(𝒜)))`. Clarity, richness, stochastic choice and
constant acts are not needed.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.4 l. 421
(the "if" direction, never written out in App. D); item 086; mandate Target 15 (iv)
Kind: P
Fidelity: variant: behaviours quantified over the type-measurable ones (the cell constraint)
Hyps: (a) `hπ`, `StrictAgree` -/
theorem ValuesB_of_strictAgree {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {G : GFrame W C}
    (hsa : StrictAgree π G) {B : W → Finset (W → C) → (W → C)} (hBtm : TypeMeasurable G B)
    (hB : IsBehaviour G B) : ValuesB π G B := by
  classical
  intro 𝒜 hsub hne a ha
  -- the difference as a sum over type cells
  suffices hdiff : 0 ≤ ∑ w, π w * (G.u (B w 𝒜 w) - G.u (a w)) by
    unfold delegValue E
    simp only [mul_sub, sum_sub_distrib] at hdiff
    simp only [Function.comp]
    linarith
  set g : W → (W → ℝ) × (C → ℝ) := fun w => (G.Pag w, G.V w) with hg
  rw [← sum_fiberwise_of_maps_to (t := univ.image g) (g := g)
    (fun w _ => mem_image_of_mem g (mem_univ w))]
  apply sum_nonneg
  intro y hy
  obtain ⟨ω₀, _, rfl⟩ := mem_image.1 hy
  have hfib : univ.filter (fun w => g w = g ω₀) = tcell G ω₀ := by
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_tcell, hg, Prod.mk.injEq]
  rw [hfib]
  set b₀ := B ω₀ 𝒜 with hb₀
  have hconst : ∀ w ∈ tcell G ω₀, B w 𝒜 = b₀ := fun w hw => (hBtm ω₀ w 𝒜 hw).symm
  have hsum : ∑ w ∈ tcell G ω₀, π w * (G.u (B w 𝒜 w) - G.u (a w)) =
      cellEU π G ω₀ b₀ - cellEU π G ω₀ a := by
    unfold cellEU
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro w hw
    rw [hconst w hw]; ring
  rw [hsum]
  obtain ⟨hmem, hopt⟩ := hB ω₀ 𝒜 hsub hne
  rcases (mass_nonneg hπ.1 (tcell G ω₀)).lt_or_eq with hm | hm
  · by_contra hcon
    rw [not_le] at hcon
    have := hsa a (hsub ha) b₀ (hsub hmem) ω₀ hm (by linarith)
    have := hopt a ha
    linarith
  · -- a null cell contributes nothing
    have hz : ∀ f : W → ℝ, ∑ w ∈ tcell G ω₀, π w * f w = 0 := fun f =>
      sum_eq_zero fun w hw => by rw [eq_zero_of_mass_eq_zero hπ.1 hm.symm hw, zero_mul]
    unfold cellEU
    rw [hz, hz]; simp

/-- **MM Theorem 3.4, repaired: the iff.** Under clarity and richness: every type-measurable
behaviour is valued ⟺ strict conditional preference agreement. This is the statement that
survives; the printed one, over MM's world-indexed `B`, fails in both directions
(`MM/Refute.lean`).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.4 l. 97,
l. 421; items 083, 086; mandate Target 15 (iv) (the extension of record)
Kind: P
Fidelity: variant: behaviours quantified over the type-measurable ones (DDB's cell constraint);
stochastic choice and constant acts dropped
Hyps: (a) `hπ`, `Clarity`, `Richness` (for ⟹ only) -/
theorem typeMeasurable_valuesB_iff_strictAgree [Nonempty C] {π : W → ℝ}
    (hπ : π ∈ stdSimplex ℝ W) {G : GFrame W C} (hcl : Clarity G) (hri : Richness G) :
    (∀ B, TypeMeasurable G B → IsBehaviour G B → ValuesB π G B) ↔ StrictAgree π G :=
  ⟨strictAgree_of_forall_typeMeasurable hcl hri,
    fun hsa _ hBtm hB => ValuesB_of_strictAgree hπ hsa hBtm hB⟩

/-! ## (v) The corollary on events -/

/-- The conditional expected utility of `splice X (const c₁) (const c₂)` on the cell of `ω`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cellEU_splice_const (π : W → ℝ) (G : GFrame W C) (ω : W) (X : Finset W) (c₁ c₂ : C) :
    cellEU π G ω (splice X (fun _ => c₁) (fun _ => c₂)) =
      G.u c₁ * mass π (X ∩ tcell G ω) + G.u c₂ * (mass π (tcell G ω) - mass π (X ∩ tcell G ω)) := by
  unfold cellEU
  have h : ∀ w, π w * G.u (splice X (fun _ => c₁) (fun _ => c₂) w) =
      G.u c₁ * (if w ∈ X then π w else 0) + G.u c₂ * (π w - (if w ∈ X then π w else 0)) := by
    intro w
    by_cases hw : w ∈ X <;> simp [splice, hw, mul_comm]
  simp only [h, sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_ite_mem, mass, inter_comm]

/-- The agent's expected utility of `splice X (const c₁) (const c₂)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem agentEU_splice_const (G : GFrame W C) (ω : W) (X : Finset W) (c₁ c₂ : C) :
    G.agentEU ω (splice X (fun _ => c₁) (fun _ => c₂)) =
      G.V ω c₁ * mass (G.Pag ω) X + G.V ω c₂ * (1 - mass (G.Pag ω) X) := by
  unfold GFrame.agentEU E
  have h : ∀ w, G.Pag ω w * (G.V ω ∘ splice X (fun _ => c₁) (fun _ => c₂)) w =
      G.V ω c₁ * (if w ∈ X then G.Pag ω w else 0) +
      G.V ω c₂ * (G.Pag ω w - (if w ∈ X then G.Pag ω w else 0)) := by
    intro w
    by_cases hw : w ∈ X <;> simp [splice, hw, mul_comm]
  simp only [h, sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_ite_mem, univ_inter, mass,
    (G.Pag_mem ω).2]

/-- **MM Theorem 3.4's corollary, strengthened.** Strict agreement with constant acts and richness
makes the principal's conditional probabilities on a positive-mass cell weakly agree with the
agent's: `P_ω(Y) ≤ P_ω(X) → π(Y ∩ [ω]) ≤ π(X ∩ [ω])` (product form; the printed statement has
`P_ω(X) > P_ω(Y) → π(X | [ω]) ≥ π(Y | [ω])`). First the constant acts give `V_ω(c₂) < V_ω(c₁)`,
then the acts `c₁` on `X`/`c₂` off and `c₁` on `Y`/`c₂` off separate the events. MM's printed
proof sets up `E ⊊ [ω]` and then argues for general events; the argument here is for general
events directly.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.4 l. 99,
App. D l. 449; item 086
Kind: C
Fidelity: stronger: `≤` ⟹ `≤` (contrapositive of the strict form), general events
Hyps: (a) `StrictAgree`, `ConstantActs`, `Richness` -/
theorem StrictAgree.mass_le {π : W → ℝ} {G : GFrame W C}
    (hsa : StrictAgree π G) (hca : ConstantActs G) (hri : Richness G) (ω : W)
    (hm : 0 < mass π (tcell G ω)) (X Y : Finset W)
    (hXY : mass (G.Pag ω) Y ≤ mass (G.Pag ω) X) :
    mass π (Y ∩ tcell G ω) ≤ mass π (X ∩ tcell G ω) := by
  obtain ⟨c₁, c₂, hu, hc₁, hc₂⟩ := hca
  -- the agent ranks the consequences as the principal does
  have hV : G.V ω c₂ < G.V ω c₁ := by
    have h := hsa _ hc₁ _ hc₂ ω hm
    have e : ∀ c, cellEU π G ω (fun _ => c) = G.u c * mass π (tcell G ω) := by
      intro c
      simp only [cellEU, mass]
      rw [mul_sum]
      apply sum_congr rfl; intro w _; ring
    rw [e, e] at h
    have h' := h (mul_lt_mul_of_pos_right hu hm)
    have e' : ∀ c, G.agentEU ω (fun _ => c) = G.V ω c := by
      intro c
      simp only [GFrame.agentEU]
      rw [show (G.V ω ∘ fun _ => c) = fun _ => G.V ω c from rfl, E_const (G.Pag_mem ω)]
    rw [e', e'] at h'
    exact h'
  by_contra hcon
  rw [not_le] at hcon
  have hf := hri _ hc₁ _ hc₂ X
  have hg := hri _ hc₁ _ hc₂ Y
  have h := hsa _ hg _ hf ω hm
  rw [cellEU_splice_const, cellEU_splice_const] at h
  have h' := h (by nlinarith)
  rw [agentEU_splice_const, agentEU_splice_const] at h'
  nlinarith

/-! ## Item 090: affine invariance -/

/-- The generalized frame with the agent's utilities rescaled by `α > 0` and shifted by `β`.
Source: none: infrastructure (item 090)
Kind: D
Fidelity: n/a -/
def GFrame.affine (G : GFrame W C) (α β : ℝ) : GFrame W C :=
  { G with V := fun ω c => α * G.V ω c + β }

/-- Type cells are unchanged by a positive affine change of the agent's utilities.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tcell_affine (G : GFrame W C) {α : ℝ} (hα : 0 < α) (β : ℝ) (ω : W) :
    tcell (G.affine α β) ω = tcell G ω := by
  ext w
  rw [mem_tcell, mem_tcell]
  change (G.Pag w = G.Pag ω ∧ (fun c => α * G.V w c + β) = (fun c => α * G.V ω c + β)) ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, funext fun c => ?_⟩
    have h3 : α * G.V w c + β = α * G.V ω c + β := congrFun h2 c
    have : α * (G.V w c - G.V ω c) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hα.ne'
    · linarith
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]⟩

/-- **Item 090.** Strict agreement is invariant under positive affine changes of the agent's
utilities: "near-perfect alignment" of `V` with `u` is not what the theorem measures.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.2 l. 101
("a kind of posterior alignment"); item 090
Kind: L
Fidelity: n/a -/
theorem strictAgree_affine {π : W → ℝ} (G : GFrame W C) {α : ℝ} (hα : 0 < α) (β : ℝ) :
    StrictAgree π (G.affine α β) ↔ StrictAgree π G := by
  have hEU : ∀ ω a, (G.affine α β).agentEU ω a = α * G.agentEU ω a + β := by
    intro ω a
    simp only [GFrame.agentEU, GFrame.affine, E, Function.comp]
    rw [show ∑ w, G.Pag ω w * (α * G.V ω (a w) + β) =
        α * ∑ w, G.Pag ω w * G.V ω (a w) + β * ∑ w, G.Pag ω w by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl; intro w _; ring]
    rw [(G.Pag_mem ω).2]; ring
  have hcell : ∀ ω a, cellEU π (G.affine α β) ω a = cellEU π G ω a := by
    intro ω a
    unfold cellEU
    rw [tcell_affine G hα β]
    rfl
  have hA : (G.affine α β).A = G.A := rfl
  unfold StrictAgree
  simp only [hEU, hcell, tcell_affine G hα β, hA]
  constructor
  · intro h a ha b hb ω hm hlt
    have := h a ha b hb ω hm hlt
    exact lt_of_mul_lt_mul_left (by linarith) hα.le
  · intro h a ha b hb ω hm hlt
    have := h a ha b hb ω hm hlt
    linarith [mul_lt_mul_of_pos_left this hα]

end

end Cleanroom.Lit.LitDdbAccuracyMm.MM
