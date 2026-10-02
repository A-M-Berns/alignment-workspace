import Cleanroom.Bli.UdtBliSist.Sist
import Cleanroom.Bli.UdtBliCore.OfSkeleton

/-!
# `udt-bli-sist` · Skeleton: the mugging verdict over `ofSkeleton` with derived branch beliefs
(T8, U15-finite — the N+ of record for T2)

**Pushforward policy laws** (`pushLaw mk g`): a law on policies given as the image of a finite
parameter type, so that masses of policy events are sums over the parameters
(`massOf_pushLaw`) and nothing is ever summed over the function type `Policy 𝒟 A`. The
**`H_unif` law** `unifLaw 𝒜` is the pushforward of "a common Bernoulli(1/2) value on the class
`𝒜`, independent uniform values elsewhere".

**The skeleton SIST prior** `sistSkel sk n h t coin c V r₀ Qh` is `udt-bli-core`'s
`ofSkeleton sk n h t` with the `H_unif` law on the class `Ask := (· coin = 1)` and the SIST
utility (Ask states read their own point, Rec states `Rec := (· coin = 0)` and residual states
read the observed point `Qh`). It is **parametric in the index, the mesh, the skeleton, the days,
the base table and the coin sentence** so that `bli-witness-lia` instantiates it with the spliced
inductor's segment; nothing in it is specific to the tent.

* `stateMass_sistSkel`: the branch masses **are** `trajLaw` fibers (`stateMass_ofSkeletonWith`),
  and at horizon one the kernel's law `(sk.κ n).law t T` itself (`stateMass_sistSkel_h0`).
* `faith_sistSkel`: faith is `ofSkeleton_faith`, a theorem of the construction (the finite `E2x`).
* `hUnif_sistSkel`: `H_unif` holds by the choice of law.
* `verdict_sistSkel`: `EU Qh give − EU Qh refuse = V·μ(Rec) − c·μ(Ask) + μ(Other)·(r₀ give − r₀ refuse)`
  with the three class masses `classMass` of the prior — `sist_hunif` instantiated.
* `homeEU_sistSkel`, `condEU_rec_sistSkel`: the updateful value at `Qh` is `−c·[give]` and the Rec
  branch's value of the `Qh` point is `V·[give]` — derived, not assumed.

**The tent instance** (`TentSist`): `tentSkeleton witIndex witMesh`, day `0`, horizon `1`, base
`t₀ = (p ↦ 1/2)`, coin `p`, observed table `Qh = (1, 1/2)`. Every grid table has mass `1/9`
(`tentLaw_t₀`), the Ask/Rec/Other classes have mass `1/3` each (by the product-grid coordinate
lemma `sum_piFinset_coord`, not by counting), so the verdict is `30 + (1/3)·(r₀ give − r₀ refuse)`:
the one-step rule pays and the updateful rule refuses for every `|r₀| ≤ 10`; `ClassInert {Qh} Qh`
fails; the base passes the finite §2.6 shadows (`t₀.InUnit`, interior coordinates, balance,
non-degeneracy, `E5`). The mandate's narrow-tent kernel with the source's `49/49/2` proportions is
not built (the tent's `1/3, 1/3, 1/3` is the fallback it names).

Sources: [[bli-program]] §3.9 U5 and U15, §7 items 9/11, bli-slides-034, mandate T8 and §3.7.
-/

namespace Cleanroom.Bli.UdtBliSist

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

/-! ## Pushforward policy laws -/

section Push

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [Fintype A] [DecidableEq A]
variable {K : Type} [Fintype K] (mk : K → Policy 𝒟 A) (g : K → ℚ)

/-- **A pushforward policy law**: the image of the weights `g` on a finite parameter type under
`mk`, `ν π := ∑_{k : mk k = π} g k`.
Source: none: infrastructure (mandate T8: a law under `H_unif` on the Ask class)
Kind: D
Fidelity: n/a -/
def pushLaw : Policy 𝒟 A → ℚ := fun π => ∑ k, if mk k = π then g k else 0

/-- A pushforward of nonnegative weights is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pushLaw_nonneg (hg : ∀ k, 0 ≤ g k) (π : Policy 𝒟 A) : 0 ≤ pushLaw mk g π :=
  Finset.sum_nonneg (fun k _ => by split_ifs; exact hg k; exact le_rfl)

/-- The total mass of a pushforward is the total weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_pushLaw : ∑ π, pushLaw mk g π = ∑ k, g k := by
  unfold pushLaw
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_ite_eq]
  simp

/-- **Masses under a pushforward are sums over the parameters**:
`ν(F) = ∑_{k : F (mk k)} g k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_pushLaw (F : Policy 𝒟 A → Prop) [DecidablePred F] :
    massOf (pushLaw mk g) F = ∑ k, if F (mk k) then g k else 0 := by
  unfold massOf pushLaw
  have e : ∀ π, (if F π then ∑ k, if mk k = π then g k else 0 else 0) =
      ∑ k, if mk k = π ∧ F π then g k else 0 := by
    intro π
    split_ifs with h
    · apply Finset.sum_congr rfl
      intro k _
      simp [h]
    · simp [h]
  simp only [e]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single (mk k)]
  · simp
  · intro π _ hπ
    simp [Ne.symm hπ]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- A policy of positive pushforward mass is the image of a parameter of positive weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exists_of_pushLaw_pos (hg : ∀ k, 0 ≤ g k) {π : Policy 𝒟 A} (h : 0 < pushLaw mk g π) :
    ∃ k, mk k = π ∧ 0 < g k := by
  by_contra hcon
  push_neg at hcon
  have hz : pushLaw mk g π = 0 := by
    unfold pushLaw
    apply Finset.sum_eq_zero
    intro k _
    split_ifs with hk
    · exact le_antisymm (hcon k hk) (hg k)
    · rfl
  rw [hz] at h
  exact lt_irrefl _ h

end Push

/-! ## The `H_unif` law -/

section Unif

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)}
variable (𝒜 : ↥𝒟 → Prop) [DecidablePred 𝒜]

/-- The policy with a common value `k.1` on the class `𝒜` and the values of `k.2` elsewhere.
Source: bli-soto-a-2-013 (`H_unif`); mandate T8
Kind: D
Fidelity: exact -/
def unifMk (k : Bool × Policy 𝒟 Bool) : Policy 𝒟 Bool := fun T => if 𝒜 T then k.1 else k.2 T

/-- The uniform coordinate weights `1/2`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def halfW : ↥𝒟 → Bool → ℚ := fun _ _ => 1 / 2

/-- The weights of the `H_unif` law: `1/2` for the common value, independent uniform elsewhere.
Source: mandate T8
Kind: D
Fidelity: exact -/
def unifG (k : Bool × Policy 𝒟 Bool) : ℚ := 1 / 2 * prodLaw (halfW (𝒟 := 𝒟)) k.2

/-- **The `H_unif` law on the class `𝒜`**: the pushforward of `unifG` under `unifMk`.
Source: bli-soto-a-2-013 (`H_unif`); mandate T8 ("`ν` under `H_unif` on the Ask class")
Kind: D
Fidelity: exact -/
def unifLaw : Policy 𝒟 Bool → ℚ := pushLaw (unifMk 𝒜) unifG

/-- The coordinate weights sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma halfW_sum : ∀ T : ↥𝒟, ∑ a, halfW T a = 1 := by
  intro T; simp [halfW, Fintype.sum_bool]

/-- `unifG ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unifG_nonneg (k : Bool × Policy 𝒟 Bool) : 0 ≤ unifG k :=
  mul_nonneg (by norm_num) (prodLaw_nonneg (fun _ _ => by simp [halfW]) _)

/-- `∑ unifG = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_unifG : ∑ k : Bool × Policy 𝒟 Bool, unifG k = 1 := by
  unfold unifG
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, sum_prodLaw halfW_sum, Fintype.sum_bool]
  norm_num

/-- The `H_unif` law is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unifLaw_nonneg (π : Policy 𝒟 Bool) : 0 ≤ unifLaw 𝒜 π :=
  pushLaw_nonneg _ _ unifG_nonneg π

/-- The `H_unif` law has mass one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_unifLaw : ∑ π, unifLaw 𝒜 π = 1 := by
  unfold unifLaw; rw [sum_pushLaw, sum_unifG]

/-- The inner sum of the `H_unif` law over the independent part, with a condition on the common
value only.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unif_inner_const (q : Prop) [Decidable q] (x : Bool) :
    (∑ f : Policy 𝒟 Bool, if q then unifG (x, f) else 0) = if q then 1 / 2 else 0 := by
  split_ifs with h
  · unfold unifG
    simp only
    rw [← Finset.mul_sum, sum_prodLaw halfW_sum, mul_one]
  · simp

/-- **A point in the class has mass `1/2`.**
Source: mandate T8 (`NDPOL` at `Qh`)
Kind: L
Fidelity: exact -/
lemma massOf_unifLaw_point_in {Q : ↥𝒟} (hQ : 𝒜 Q) (a : Bool) :
    massOf (unifLaw 𝒜) (fun π => π Q = a) = 1 / 2 := by
  unfold unifLaw
  rw [massOf_pushLaw, Fintype.sum_prod_type]
  simp only [unifMk, hQ, if_true]
  simp only [unif_inner_const (𝒟 := 𝒟)]
  rw [Finset.sum_ite_eq']
  simp

/-- **A point off the class has mass `1/2`.**
Source: mandate T8
Kind: L
Fidelity: exact -/
lemma massOf_unifLaw_point_out {T : ↥𝒟} (hT : ¬ 𝒜 T) (b : Bool) :
    massOf (unifLaw 𝒜) (fun π => π T = b) = 1 / 2 := by
  unfold unifLaw
  rw [massOf_pushLaw, Fintype.sum_prod_type]
  simp only [unifMk, hT, if_false]
  have e : ∀ x : Bool, (∑ f : Policy 𝒟 Bool, if f T = b then unifG (x, f) else 0) = 1 / 4 := by
    intro x
    unfold unifG
    simp only
    have : (∑ f : Policy 𝒟 Bool, if f T = b then 1 / 2 * prodLaw (halfW (𝒟 := 𝒟)) f else 0) =
        1 / 2 * massOf (prodLaw (halfW (𝒟 := 𝒟))) (fun f => f T = b) := by
      unfold massOf
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      split_ifs <;> ring
    rw [this, IndepData.massOf_prodLaw_point halfW halfW_sum]
    simp [halfW]; norm_num
  simp only [e, Fintype.sum_bool]
  norm_num

/-- **Two points in the class are a.s. equal**: `ν(π T = b ∧ π Q = a) = [b = a] · 1/2`.
Source: bli-soto-a-2-013 (`H_unif`)
Kind: L
Fidelity: exact -/
lemma massOf_unifLaw_pair_in {T Q : ↥𝒟} (hT : 𝒜 T) (hQ : 𝒜 Q) (b a : Bool) :
    massOf (unifLaw 𝒜) (fun π => π T = b ∧ π Q = a) = if b = a then 1 / 2 else 0 := by
  unfold unifLaw
  rw [massOf_pushLaw, Fintype.sum_prod_type]
  simp only [unifMk, hT, hQ, if_true]
  simp only [unif_inner_const (𝒟 := 𝒟)]
  by_cases hba : b = a
  · subst hba
    simp only [and_self]
    rw [Finset.sum_ite_eq']
    simp
  · have : ∀ x : Bool, (x = b ∧ x = a) ↔ False :=
      fun x => ⟨fun ⟨h1, h2⟩ => hba (h1.symm.trans h2), False.elim⟩
    simp only [this, if_false, Finset.sum_const_zero]
    rw [if_neg hba]

/-- **A point off the class is independent of a point in it**: `ν(π T = b ∧ π Q = a) = 1/4`.
Source: mandate T8
Kind: L
Fidelity: exact -/
lemma massOf_unifLaw_pair_out {T Q : ↥𝒟} (hT : ¬ 𝒜 T) (hQ : 𝒜 Q) (b a : Bool) :
    massOf (unifLaw 𝒜) (fun π => π T = b ∧ π Q = a) = 1 / 4 := by
  unfold unifLaw
  rw [massOf_pushLaw, Fintype.sum_prod_type]
  simp only [unifMk, hT, hQ, if_true, if_false]
  have e : ∀ x : Bool, (∑ f : Policy 𝒟 Bool, if f T = b ∧ x = a then unifG (x, f) else 0) =
      if x = a then 1 / 4 else 0 := by
    intro x
    by_cases hx : x = a
    · simp only [hx, and_true, if_true]
      unfold unifG
      simp only
      have : (∑ f : Policy 𝒟 Bool, if f T = b then 1 / 2 * prodLaw (halfW (𝒟 := 𝒟)) f else 0) =
          1 / 2 * massOf (prodLaw (halfW (𝒟 := 𝒟))) (fun f => f T = b) := by
        unfold massOf
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro f _
        split_ifs <;> ring
      rw [this, IndepData.massOf_prodLaw_point halfW halfW_sum]
      simp [halfW]; norm_num
    · simp [hx]
  simp only [e]
  rw [Finset.sum_ite_eq']
  simp

/-- **`H_unif` holds on any `IndepData` prior whose policy law is `unifLaw 𝒜`**, at any observed
table of the class.
Source: bli-soto-a-2-013 (`H_unif`); mandate T8
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem hUnif_of_unifLaw (D : IndepData 𝒮 m 𝒟 Bool) (hν : D.ν = unifLaw 𝒜) {Q : ↥𝒟}
    (hQ : 𝒜 Q) : HUnif D.toPrior 𝒜 Q := by
  intro ω hμ T hT
  change 0 < D.μ₀ ω.1 * D.ν ω.2 at hμ
  have hν' : 0 < D.ν ω.2 := pos_of_mul_pos_right hμ (D.μ₀_nonneg _)
  rw [hν] at hν'
  obtain ⟨k, hk, _⟩ := exists_of_pushLaw_pos _ _ unifG_nonneg hν'
  change ω.2 T = ω.2 Q
  rw [← hk]
  simp [unifMk, hT, hQ]

end Unif

/-! ## The product-grid coordinate lemma -/

/-- **A coordinate indicator against a product weight on a product grid**: for a product weight
`∏_i f i (x i)` on `piFinset (fun _ => s)`, the mass of `{x i₀ = v}` is
`f i₀ v · ∏_{i ≠ i₀} ∑_{u ∈ s} f i u`. (The class masses of a product kernel, without counting.)
Source: none: infrastructure (mandate T8: branch masses computed from the kernel's law)
Kind: L
Fidelity: n/a -/
lemma sum_piFinset_coord {ι κ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq κ] (s : Finset κ)
    (f : ι → κ → ℚ) (i₀ : ι) (v : κ) (hv : v ∈ s) :
    (∑ x ∈ Fintype.piFinset (fun _ : ι => s), if x i₀ = v then ∏ i, f i (x i) else 0) =
      f i₀ v * ∏ i ∈ univ.erase i₀, ∑ u ∈ s, f i u := by
  set F : ι → κ → ℚ := fun i u => if i = i₀ then (if u = v then f i u else 0) else f i u with hF
  have e : ∀ x : ι → κ, (if x i₀ = v then ∏ i, f i (x i) else 0) = ∏ i, F i (x i) := by
    intro x
    rw [← Finset.mul_prod_erase univ (fun i => F i (x i)) (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase univ (fun i => f i (x i)) (Finset.mem_univ i₀)]
    have hrest : ∏ i ∈ univ.erase i₀, F i (x i) = ∏ i ∈ univ.erase i₀, f i (x i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [hF, Finset.ne_of_mem_erase hi]
    rw [hrest]
    simp only [hF, if_true]
    split_ifs <;> simp
  simp only [e]
  rw [← Finset.prod_univ_sum, ← Finset.mul_prod_erase univ _ (Finset.mem_univ i₀)]
  have h0 : ∑ u ∈ s, F i₀ u = f i₀ v := by
    simp only [hF, if_true]
    rw [Finset.sum_ite_eq' s v, if_pos hv]
  rw [h0]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro u _
  simp [hF, Finset.ne_of_mem_erase hi]

/-! ## The skeleton SIST prior -/

section Skel

variable {𝒮 : SmallIndex} {d : ℕ → ℕ} (sk : Skeleton 𝒮 d) (n h : ℕ) (t : Table 𝒮 n)
variable (coin : ↥(𝒮.S (n + h + 1))) (c V : ℚ) (r₀ : Bool → ℚ) (Qh : ↥(grid 𝒮 d (n + h + 1)))

/-- **The Ask class**: the table prices the coin at `1`.
Source: mandate §3.2
Kind: D
Fidelity: exact -/
def askC (T : ↥(grid 𝒮 d (n + h + 1))) : Prop := T.1 coin = 1

/-- **The Rec class**: the table prices the coin at `0`.
Source: mandate §3.2
Kind: D
Fidelity: exact -/
def recC (T : ↥(grid 𝒮 d (n + h + 1))) : Prop := T.1 coin = 0

/-- `askC` is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance askC.decidable : DecidablePred (askC (d := d) n h coin) :=
  fun T => inferInstanceAs (Decidable (T.1 coin = 1))

/-- `recC` is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance recC.decidable : DecidablePred (recC (d := d) n h coin) :=
  fun T => inferInstanceAs (Decidable (T.1 coin = 0))

/-- The base of `ofSkeleton`: a grid trajectory and a product world.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev SkelBase : Type := ↥(trajGrid 𝒮 d n (h + 1)) × (↥(𝒮.S (n + h + 1)) → Bool)

/-- The reference table of the skeleton SIST utility: an Ask state reads its own table, every
other state reads the observed table (Omega's pick pinned at `Qh`).
Source: mandate §3.5, T8
Kind: D
Fidelity: exact -/
def skelRef (ω : SkelBase (𝒮 := 𝒮) (d := d) n h) : ↥(grid 𝒮 d (n + h + 1)) :=
  if askC n h coin (skelState (d := d) n h ω.1) then skelState (d := d) n h ω.1
  else if recC n h coin (skelState (d := d) n h ω.1) then Qh else Qh

/-- The payoff of the skeleton SIST utility: `−c` for `give` at Ask, `V` for `give` at Rec, `0`
for `refuse`, the residual elsewhere.
Source: bli-slides-034; mandate T8
Kind: D
Fidelity: exact -/
def skelPay (ω : SkelBase (𝒮 := 𝒮) (d := d) n h) (b : Bool) : ℚ :=
  if askC n h coin (skelState (d := d) n h ω.1) then -c * ind b
  else if recC n h coin (skelState (d := d) n h ω.1) then V * ind b else r₀ b

/-- The skeleton SIST utility, as `ofSkeleton` wants it.
Source: mandate T8
Kind: D
Fidelity: exact -/
def skelU (ω : SkelBase (𝒮 := 𝒮) (d := d) n h) (π : Policy (grid 𝒮 d (n + h + 1)) Bool) : ℚ :=
  skelPay n h coin c V r₀ ω (π (skelRef n h coin Qh ω))

/-- The `IndepData` underlying the skeleton SIST prior.
Source: mandate T8
Kind: D
Fidelity: exact -/
def sistSkelData : IndepData 𝒮 (n + h + 1) (grid 𝒮 d (n + h + 1)) Bool :=
  skelData sk n h t (productWorldLaw 𝒮 (n + h + 1)) (unifLaw (askC n h coin))
    (unifLaw_nonneg _) (sum_unifLaw _) (skelU n h coin c V r₀ Qh)

/-- **The skeleton SIST prior** (definition of record, T8): `ofSkeleton` with the `H_unif` law
on the Ask class and the SIST utility. Parametric in the index, the mesh, the skeleton, the days,
the base table, the coin and the observed table.
Source: [[bli-program]] §3.9 U15; mandate T8
Kind: D
Fidelity: variant: finite shadows of the §2.6 predicates (mandate §3.7); the FAF-level
`D_PC`/`D_ND`/`D_NNU` are `bli-found`'s, instantiated in `bli-witness-lia` -/
def sistSkel : FiniteBLIPrior 𝒮 (n + h + 1) (grid 𝒮 d (n + h + 1)) Bool :=
  ofSkeleton sk n h t (unifLaw (askC n h coin)) (unifLaw_nonneg _) (sum_unifLaw _)
    (skelU n h coin c V r₀ Qh)

/-- The prior is the data's `toPrior`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sistSkel_eq : sistSkel sk n h t coin c V r₀ Qh = (sistSkelData sk n h t coin c V r₀ Qh).toPrior :=
  rfl

/-- **The utility has the SIST shape** with `Ask = askC`, `Rec = recC`, Omega's pick pinned at
`Qh`, constant stakes and a base-independent residual.
Source: mandate T8
Kind: L
Fidelity: exact -/
lemma shaped_sistSkel :
    SistShaped (sistSkelData sk n h t coin c V r₀ Qh) (askC n h coin) (recC n h coin) (fun _ => Qh)
      Qh (fun _ => c) (fun _ => V) (fun _ b => r₀ b) :=
  fun _ _ => rfl

/-- **The branch masses are `trajLaw` fibers**:
`stateMass T = ∑_{σ ∈ trajGrid, last σ = T} trajLaw sk n (h+1) t σ` — computed, never asserted.
Source: mandate T8 ("`μ(Ask)`, `μ(Rec)`, `μ(Other)` computed from `trajLaw`")
Kind: L
Fidelity: exact -/
theorem stateMass_sistSkel (T : ↥(grid 𝒮 d (n + h + 1))) :
    (sistSkel sk n h t coin c V r₀ Qh).stateMass T =
      ∑ σ ∈ trajGrid 𝒮 d n (h + 1), if lastOf n h σ = T.1 then trajLaw sk n (h + 1) t σ else 0 :=
  stateMass_ofSkeletonWith sk n h t (productWorldLaw 𝒮 (n + h + 1)) _ _ _ _ T

/-- **Faith is derived** (`ofSkeleton_faith`, the finite `E2x`): within each table's branch the
frequency of every small sentence is the table's price.
Source: mandate T8 ("faith by `ofSkeleton_faith`, never a field you set")
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem faith_sistSkel (T : ↥(grid 𝒮 d (n + h + 1))) (φ : ↥(𝒮.S (n + h + 1))) :
    integralOf (sistSkel sk n h t coin c V r₀ Qh).μ
        (fun ω => ind ((sistSkel sk n h t coin c V r₀ Qh).small ω φ))
        (fun ω => (sistSkel sk n h t coin c V r₀ Qh).state ω = T) =
      T.1 φ * (sistSkel sk n h t coin c V r₀ Qh).stateMass T :=
  ofSkeleton_faith sk n h t _ _ _ _ T φ

/-- **`H_unif` holds** on the skeleton SIST prior at any Ask table.
Source: mandate T8
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem hUnif_sistSkel (hQ : askC n h coin Qh) :
    HUnif (sistSkel sk n h t coin c V r₀ Qh) (askC n h coin) Qh :=
  hUnif_of_unifLaw _ (sistSkelData sk n h t coin c V r₀ Qh) rfl hQ

/-- Every point of the skeleton SIST prior has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppMass_sistSkel (T : ↥(grid 𝒮 d (n + h + 1))) (a : Bool) :
    (sistSkel sk n h t coin c V r₀ Qh).ppMass T a = 1 / 2 := by
  rw [sistSkel_eq, IndepData.ppMass_toPrior]
  change massOf (unifLaw (askC n h coin)) (fun π => π T = a) = 1 / 2
  by_cases hT : askC n h coin T
  · exact massOf_unifLaw_point_in _ hT a
  · exact massOf_unifLaw_point_out _ hT a

/-- **The verdict over the skeleton** (T2's N+ of record, parametric): at an Ask table `Qh`,
`EU Qh give − EU Qh refuse = V·μ(Rec) − c·μ(Ask) + μ(Other)·(r₀ give − r₀ refuse)`, with the three
class masses those of the prior (hence `trajLaw` fibers by `stateMass_sistSkel`).
Source: [[bli-program]] §3.9 U5/U15; bli-slides-034; mandate T8
Kind: C (`sist_hunif` on `sistSkelData`)
Fidelity: exact
Hyps: (a) `askC Qh`; uses faith: no (the verdict is arithmetic in the masses; faith is the
separate theorem `faith_sistSkel`) -/
theorem verdict_sistSkel (hQ : askC n h coin Qh) :
    (sistSkel sk n h t coin c V r₀ Qh).EU Qh true - (sistSkel sk n h t coin c V r₀ Qh).EU Qh false =
      V * classMass (sistSkel sk n h t coin c V r₀ Qh)
          (univ.filter (fun T => ¬ askC n h coin T ∧ recC n h coin T)) -
        c * classMass (sistSkel sk n h t coin c V r₀ Qh) (univ.filter (askC n h coin)) +
        classMass (sistSkel sk n h t coin c V r₀ Qh)
          (univ.filter (fun T => ¬ askC n h coin T ∧ ¬ recC n h coin T)) *
          (r₀ true - r₀ false) := by
  rw [sistSkel_eq]
  rw [sist_hunif (sistSkelData sk n h t coin c V r₀ Qh) (askC n h coin) (recC n h coin) (fun _ => Qh)
    Qh (fun _ b => r₀ b) V c (shaped_sistSkel sk n h t coin c V r₀ Qh)
    (by
      change 0 < massOf (unifLaw (askC n h coin)) (fun π => π Qh = true)
      rw [massOf_unifLaw_point_in _ hQ]; norm_num)
    (by
      change 0 < massOf (unifLaw (askC n h coin)) (fun π => π Qh = false)
      rw [massOf_unifLaw_point_in _ hQ]; norm_num)
    (hUnif_sistSkel sk n h t coin c V r₀ Qh hQ) (fun _ _ => hQ)]
  rw [recMass_eq_classMass, askMass_eq_classMass, resTerm_const]

/-- **The updateful value at `Qh` is `−c·[give]`** whenever `Qh` is an Ask table of positive mass
(`condExp` of the constant `−c·[give]` on the home branch).
Source: [[bli-program]] §3.9 U5; mandate T8 (`IsUpdatefulChoice Qh refuse`)
Kind: C
Fidelity: exact
Hyps: (a) `askC Qh`, `0 < stateMass Qh`; does not use faith -/
theorem homeEU_sistSkel (hQ : askC n h coin Qh)
    (hpos : 0 < (sistSkel sk n h t coin c V r₀ Qh).stateMass Qh) (a : Bool) :
    (sistSkel sk n h t coin c V r₀ Qh).homeEU Qh a = -c * ind a := by
  rw [sistSkel_eq]
  rw [sistSkel_eq, IndepData.stateMass_toPrior] at hpos
  rw [homeEU_ref_self _ _ _ (shaped_sistSkel sk n h t coin c V r₀ Qh) Qh a
    (fun ω hω => by
      unfold sistRef
      change (if askC n h coin (skelState (d := d) n h ω.1) then skelState (d := d) n h ω.1
        else if recC n h coin (skelState (d := d) n h ω.1) then Qh else Qh) = Qh
      change skelState (d := d) n h ω.1 = Qh at hω
      simp [hω])
    (by
      change 0 < massOf (unifLaw (askC n h coin)) (fun π => π Qh = a)
      rw [massOf_unifLaw_point_in _ hQ]; norm_num)]
  unfold condExp
  rw [integralOf_congr_fun _ _ (fun _ => -c * ind a) _ (by
    intro ω hω
    change skelState (d := d) n h ω.1 = Qh at hω
    unfold sistPay
    change (if askC n h coin (skelState (d := d) n h ω.1) then -c * ind a
      else if recC n h coin (skelState (d := d) n h ω.1) then V * ind a else r₀ a) = -c * ind a
    rw [hω, if_pos hQ])]
  rw [integralOf_const, mul_div_assoc, div_self (ne_of_gt hpos), mul_one]

/-- The state coordinate of the skeleton data.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma state₀_sistSkelData (ω : SkelBase (𝒮 := 𝒮) (d := d) n h) :
    (sistSkelData sk n h t coin c V r₀ Qh).state₀ ω = skelState (d := d) n h ω.1 := rfl

/-- **The Rec branch's value of the `Qh` point is `V·[give]`** at any Rec table `R` of positive
mass — derived from the utility and the law, not assumed.
Source: bli-soto-a-077 (the Rec branch's beliefs); mandate T8 ("branch beliefs derived")
Kind: C
Fidelity: exact
Hyps: (a) `askC Qh`, `recC R`, `¬ askC R`, `0 < stateMass R`; does not use faith -/
theorem condEU_rec_sistSkel (hQ : askC n h coin Qh) {R : ↥(grid 𝒮 d (n + h + 1))}
    (hR : recC n h coin R) (hRA : ¬ askC n h coin R)
    (hpos : 0 < (sistSkel sk n h t coin c V r₀ Qh).stateMass R) (a : Bool) :
    (sistSkel sk n h t coin c V r₀ Qh).condEU R Qh a = V * ind a := by
  rw [sistSkel_eq]
  rw [sistSkel_eq, IndepData.stateMass_toPrior] at hpos
  rw [condEU_ref _ _ _ (shaped_sistSkel sk n h t coin c V r₀ Qh) R Qh a]
  have hpp : 0 < (sistSkelData sk n h t coin c V r₀ Qh).toPrior.ppMass Qh a := by
    rw [IndepData.ppMass_toPrior]
    change 0 < massOf (unifLaw (askC n h coin)) (fun π => π Qh = a)
    rw [massOf_unifLaw_point_in _ hQ]; norm_num
  unfold condExp
  rw [integralOf_congr_fun _ _ (fun _ => V * ind a) _ (by
    intro ω hω
    simp only [state₀_sistSkelData] at hω
    unfold sistRef sistPay
    simp only [state₀_sistSkelData, hω, hRA, hR, if_false, if_true,
      condPoint_self _ Qh _ a hpp, Fintype.sum_bool]
    cases a <;> simp)]
  rw [integralOf_const, mul_div_assoc, div_self (ne_of_gt hpos), mul_one]

/-- **`ClassInert {Qh} Qh` fails** on the skeleton SIST prior whenever some Rec table has positive
mass and `V ≠ 0` (the N− of the class-cut with the singleton class, at the skeleton level).
Source: [[bli-program]] §3.9 U5 ("`NoCrossBranch` fails"); mandate T8 (`¬ ClassInert {Q̂} Q̂`)
Kind: N−
Fidelity: exact
Hyps: (a) as stated; does not use faith -/
theorem not_classInert_sistSkel (hQ : askC n h coin Qh) {R : ↥(grid 𝒮 d (n + h + 1))}
    (hR : recC n h coin R) (hRA : ¬ askC n h coin R)
    (hpos : 0 < (sistSkel sk n h t coin c V r₀ Qh).stateMass R) (hV : V ≠ 0) :
    ¬ ClassInert (sistSkel sk n h t coin c V r₀ Qh) {Qh} Qh := by
  intro hI
  have hRQ : R ∉ ({Qh} : Finset ↥(grid 𝒮 d (n + h + 1))) := by
    rw [Finset.mem_singleton]
    intro hRQ; exact hRA (hRQ ▸ hQ)
  have hj : ∀ a, 0 < (sistSkel sk n h t coin c V r₀ Qh).jointMass R Qh a := by
    intro a
    rw [sistSkel_eq, IndepData.jointMass_toPrior]
    apply mul_pos
    · rw [sistSkel_eq, IndepData.stateMass_toPrior] at hpos; exact hpos
    · change 0 < massOf (unifLaw (askC n h coin)) (fun π => π Qh = a)
      rw [massOf_unifLaw_point_in _ hQ]; norm_num
  have := hI R hRQ true false (hj true) (hj false)
  rw [condEU_rec_sistSkel sk n h t coin c V r₀ Qh hQ hR hRA hpos,
    condEU_rec_sistSkel sk n h t coin c V r₀ Qh hQ hR hRA hpos] at this
  simp at this
  exact hV this

/-- **At horizon one the branch masses are the kernel's law**: `stateMass T = (sk.κ n).law t T`.
Source: mandate T8 ("`stateMass_ofSkeletonWith` + the kernel's law")
Kind: L
Fidelity: exact -/
theorem stateMass_sistSkel_h0 (coin : ↥(𝒮.S (n + 0 + 1))) (Qh : ↥(grid 𝒮 d (n + 0 + 1)))
    (T : ↥(grid 𝒮 d (n + 0 + 1))) :
    (sistSkel sk n 0 t coin c V r₀ Qh).stateMass T = (sk.κ n).law t T.1 := by
  rw [stateMass_sistSkel, sum_trajGrid_succ, sum_trajGrid_zero]
  have e : ∀ Q ∈ grid 𝒮 d (n + 0 + 1),
      (if lastOf n 0 (show Traj 𝒮 n 1 from (PUnit.unit, Q)) = T.1 then
        trajLaw sk n 1 t (show Traj 𝒮 n 1 from (PUnit.unit, Q)) else 0) =
      if Q = T.1 then (sk.κ n).law t Q else 0 := by
    intro Q _
    have h1 : lastOf n 0 (show Traj 𝒮 n 1 from (PUnit.unit, Q)) = Q := rfl
    have h2 : trajLaw sk n 1 t (show Traj 𝒮 n 1 from (PUnit.unit, Q)) = (sk.κ n).law t Q := by
      rw [trajLaw_succ, trajLaw_zero, Traj.last_zero, one_mul]
      rfl
    rw [h1, h2]
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq' (grid 𝒮 d (n + 0 + 1)) T.1, if_pos T.2]

end Skel

/-! ## The tent instance -/

namespace TentSist

open Cleanroom.Bli.UdtBliCore.Tent

/-- **The tent SIST prior**: the tent skeleton on `witIndex`, day `0`, horizon `1`, base `t₀`,
coin `p`, observed table `Qh = (1, 1/2)`.
Source: mandate T8 (the fallback instance)
Kind: D
Fidelity: exact -/
abbrev tP (c V : ℚ) (r₀ : Bool → ℚ) : FiniteBLIPrior witIndex 1 (grid witIndex witMesh.d 1) Bool :=
  sistSkel (tentSkeleton witIndex witMesh) 0 0 t₀ pW1 c V r₀ Tone

variable (c V : ℚ) (r₀ : Bool → ℚ)

/-- `(1, 1/2)` is an Ask table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma askC_Tone : askC 0 0 pW1 Tone := by simp [askC, Qone]

/-- `(0, 1/2)` is a Rec table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma recC_Tzero : recC 0 0 pW1 Tzero := by simp [recC, Q₂]

/-- `(0, 1/2)` is not an Ask table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_askC_Tzero : ¬ askC 0 0 pW1 Tzero := by simp [askC, Q₂]

/-- **Every grid table has mass `1/9`** under the tent SIST prior (the kernel's law at `t₀`).
Source: mandate T8; `bli-finite`'s `tentLaw_t₀`
Kind: N+
Fidelity: exact -/
theorem stateMass_eq (T : ↥(grid witIndex witMesh.d 1)) : (tP c V r₀).stateMass T = 1 / 9 := by
  rw [stateMass_sistSkel_h0]
  exact tentLaw_t₀ T.2

/-- **The tent law at `t₀` puts mass `1/3` on each coin value**: for every grid value `v`,
`∑_{Q ∈ grid, Q p = v} tentLaw t₀ Q = tent1 2 (1/2) v = 1/3` — by the product-grid coordinate
lemma on the kernel's law, not by counting.
Source: mandate T8 ("`μ(Ask)`, `μ(Rec)`, `μ(Other)` computed from `trajLaw`")
Kind: C
Fidelity: exact -/
theorem sum_grid_coin_tentLaw (v : ℚ) (hv : v ∈ gridVals 2) :
    (∑ Q ∈ grid witIndex witMesh.d 1, if Q pW1 = v then tentLaw witMesh 0 t₀ Q else 0) = 1 / 3 := by
  change (∑ Q ∈ Fintype.piFinset (fun _ : ↥(witIndex.S 1) => gridVals 2),
    if Q pW1 = v then ∏ φ, tentCoord witMesh 0 t₀ φ (Q φ) else 0) = 1 / 3
  rw [sum_piFinset_coord (gridVals 2) (fun φ u => tentCoord witMesh 0 t₀ φ u) pW1 v hv]
  have hone : ∏ i ∈ univ.erase pW1, ∑ u ∈ gridVals 2, tentCoord witMesh 0 t₀ i u = 1 :=
    Finset.prod_eq_one (fun φ _ => tentCoord_sum_one (𝓜 := witMesh) t₀ φ)
  rw [hone, mul_one]
  unfold tentCoord
  rw [dif_pos pW_mem_S0]
  exact tent1_two_half hv

/-- **The mass of a coin class is `1/3`** under the tent SIST prior.
Source: mandate T8
Kind: C
Fidelity: exact -/
theorem classMass_coin (v : ℚ) (hv : v ∈ gridVals 2) :
    classMass (tP c V r₀) (univ.filter (fun T : ↥(grid witIndex witMesh.d 1) => T.1 pW1 = v)) =
      1 / 3 := by
  unfold classMass
  simp only [stateMass_sistSkel_h0]
  rw [Finset.sum_filter, Finset.sum_coe_sort (grid witIndex witMesh.d 1)
    (fun Q => if Q pW1 = v then ((tentSkeleton witIndex witMesh).κ 0).law t₀ Q else 0)]
  exact sum_grid_coin_tentLaw v hv

/-- `μ(Ask) = 1/3`.
Source: mandate T8
Kind: N+
Fidelity: exact -/
theorem classMass_ask : classMass (tP c V r₀) (univ.filter (askC 0 0 pW1)) = 1 / 3 :=
  classMass_coin c V r₀ 1 (one_mem_gridVals (by norm_num))

/-- `μ(Rec ∖ Ask) = 1/3`.
Source: mandate T8
Kind: N+
Fidelity: exact -/
theorem classMass_rec :
    classMass (tP c V r₀) (univ.filter (fun T => ¬ askC 0 0 pW1 T ∧ recC 0 0 pW1 T)) = 1 / 3 := by
  have e : (univ.filter (fun T : ↥(grid witIndex witMesh.d 1) => ¬ askC 0 0 pW1 T ∧ recC 0 0 pW1 T))
      = univ.filter (fun T => T.1 pW1 = 0) := by
    apply Finset.filter_congr
    intro T _
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h
      refine ⟨?_, h⟩
      unfold askC
      rw [h]; norm_num
  rw [e]
  exact classMass_coin c V r₀ 0 (zero_mem_gridVals 2)

/-- `μ(Other) = 1/3`: the residual class, by `E5` (`sum_stateMass`) minus the two classes.
Source: mandate T8
Kind: N+
Fidelity: exact -/
theorem classMass_other :
    classMass (tP c V r₀) (univ.filter (fun T => ¬ askC 0 0 pW1 T ∧ ¬ recC 0 0 pW1 T)) = 1 / 3 := by
  have h1 := Finset.sum_filter_add_sum_filter_not univ (askC 0 0 pW1) (tP c V r₀).stateMass
  have h2 := Finset.sum_filter_add_sum_filter_not (univ.filter (fun T => ¬ askC 0 0 pW1 T))
    (recC 0 0 pW1) (tP c V r₀).stateMass
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  rw [(tP c V r₀).sum_stateMass] at h1
  have ha := classMass_ask c V r₀
  have hr := classMass_rec c V r₀
  unfold classMass at ha hr ⊢
  linarith

/-- **The verdict over the tent skeleton**:
`EU Qh give − EU Qh refuse = V/3 − c/3 + (1/3)·(r₀ give − r₀ refuse)`; at `(100, 10)` this is
`30 + (r₀ give − r₀ refuse)/3`.
Source: [[bli-program]] §3.9 U5/U15; mandate T8 ("the fallback … verdict `30 > 0`")
Kind: N+ (the N+ of record for T2 (a)/(b)/(c))
Fidelity: exact
Hyps: (a) none; uses faith: no (faith is `faith_tent`, separately) -/
theorem verdict : (tP c V r₀).EU Tone true - (tP c V r₀).EU Tone false =
    V * (1 / 3) - c * (1 / 3) + 1 / 3 * (r₀ true - r₀ false) := by
  rw [verdict_sistSkel _ _ _ _ _ _ _ _ _ (askC_Tone), classMass_ask, classMass_rec, classMass_other]

/-- **One-step UDT pays over the tent skeleton** at `(100, 10)` for every `|r₀| ≤ 10` (strictly);
the exact difference is `30 + (r₀ give − r₀ refuse)/3`.
Source: [[bli-program]] §3.9 U5/U15; bli-slides-034; mandate T8
Kind: N+
Fidelity: exact
Hyps: (a) `|r₀| ≤ 10`; does not use faith -/
theorem isOneStepChoice_pay (hr : ∀ a, |r₀ a| ≤ 10) :
    (tP 10 100 r₀).IsOneStepChoice Tone true ∧
      (tP 10 100 r₀).EU Tone false < (tP 10 100 r₀).EU Tone true := by
  have hd := verdict 10 100 r₀
  have h1 := abs_le.mp (hr true)
  have h2 := abs_le.mp (hr false)
  refine ⟨fun b => ?_, by linarith⟩
  cases b
  · linarith
  · exact le_rfl

/-- **The updateful rule refuses over the tent skeleton**: `homeEU Qh give = −c < 0 = homeEU Qh refuse`.
Source: [[bli-program]] §3.9 U5; mandate T8
Kind: N+
Fidelity: exact
Hyps: (a) `0 < c`; does not use faith -/
theorem isUpdatefulChoice_refuse (hc : 0 < c) :
    (tP c V r₀).IsUpdatefulChoice Tone false ∧ ¬ (tP c V r₀).IsUpdatefulChoice Tone true := by
  have hpos : 0 < (tP c V r₀).stateMass Tone := by rw [stateMass_eq]; norm_num
  have h := homeEU_sistSkel (tentSkeleton witIndex witMesh) 0 0 t₀ pW1 c V r₀ Tone askC_Tone hpos
  constructor
  · intro b
    rw [h, h]
    cases b <;> simp <;> linarith
  · intro hT
    have := hT false
    rw [h, h] at this
    simp at this
    linarith

/-- **`ClassInert {Qh} Qh` fails over the tent skeleton** (the Rec table `(0, 1/2)` has mass `1/9`
and its value of the `Qh` point moves by `V`).
Source: mandate T8 (`¬ ClassInert {Q̂} Q̂`)
Kind: N−
Fidelity: exact
Hyps: (a) `V ≠ 0`; does not use faith -/
theorem not_classInert (hV : V ≠ 0) : ¬ ClassInert (tP c V r₀) {Tone} Tone :=
  not_classInert_sistSkel _ _ _ _ _ _ _ _ _ askC_Tone recC_Tzero not_askC_Tzero
    (by rw [stateMass_eq]; norm_num) hV

/-- **`H_unif` holds over the tent skeleton** at `Qh` (three Ask tables of mass `1/9` each, the
policy a.s. constant on them).
Source: bli-soto-a-2-013; mandate T8
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem hUnif : HUnif (tP c V r₀) (askC 0 0 pW1) Tone :=
  hUnif_sistSkel _ _ _ _ _ _ _ _ _ askC_Tone

/-- **Faith over the tent skeleton is derived** (`ofSkeleton_faith`): the finite `E2x`.
Source: mandate T8
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem faith_tent (T : ↥(grid witIndex witMesh.d 1)) (φ : ↥(witIndex.S 1)) :
    integralOf (tP c V r₀).μ (fun ω => ind ((tP c V r₀).small ω φ))
        (fun ω => (tP c V r₀).state ω = T) = T.1 φ * (tP c V r₀).stateMass T :=
  faith_sistSkel (tentSkeleton witIndex witMesh) 0 0 t₀ pW1 c V r₀ Tone T φ

/-- **Every policy point has mass `1/2`** (`NDPOL`) over the tent skeleton.
Source: mandate T8 (`NDPOL` at `Q̂`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ndpol : (tP c V r₀).NDPOL := fun T a => by rw [ppMass_sistSkel]; norm_num

/-- **The finite §2.6 shadows at the base `t₀`** (mandate §3.7): the base is in the unit cube (on a
one-sentence day-0 index, propositional coherence is exactly `0 ≤ t ≤ 1` — the `D-PC` shadow;
`bli-finite`'s world-marginal `CoherentOn` is not imported here), every coordinate is interior
(`D-ND` shadow), the kernel is balanced at `t₀` (`D-NNU` shadow, exact) and non-degenerate (`FS`),
and the state is a function (`E5`: the branch masses sum to one). The FAF-level predicates are
`bli-found`'s `D_PC`/`D_ND`/`D_NNU`, instantiated in `bli-witness-lia`.
Source: [[bli-program-desiderata]] §2.6; mandate T8 and §3.7
Kind: N+
Fidelity: variant: finite shadows (disclosed)
Hyps: (a) none -/
theorem shadows :
    t₀.InUnit ∧ (∀ φ, 0 < t₀ φ ∧ t₀ φ < 1) ∧ Balanced witMesh.d (tentLaw witMesh 0 t₀) t₀ ∧
      NonDegenerate witMesh.d (tentLaw witMesh 0 t₀) t₀ ∧ ∑ T, (tP c V r₀).stateMass T = 1 :=
  ⟨t₀_inUnit, fun _ => by unfold t₀; norm_num, balanced_t₀, nonDegenerate_t₀,
    (tP c V r₀).sum_stateMass⟩

end TentSist

end Cleanroom.Bli.UdtBliSist
