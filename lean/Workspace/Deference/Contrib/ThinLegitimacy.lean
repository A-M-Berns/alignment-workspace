/-
# Legitimacy at two levels: the thin specification and the thick realization

Round `projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/`
(`prompts/2026-10-01-thin-legitimacy-and-effective-authority/PROMPT.md`), Part A.

**The setting** (§1).  Finite worlds `W` with her prior `π`; a *process* is a kernel from
worlds to later records (`Kernel`: nonnegative rows summing to one; a deterministic
record is the `0/1` case, `detKernel`); her earlier record is a function `E` of the world,
shared by the three processes — her model `M`, the actual `A`, the baseline `B`.  Her
program `F` maps a later record to a credence; it is *coherent* when `F r` is `M`'s
posterior given `r`.  The reference is `B`'s later record beside her earlier one
(`refKernel E B`), used correctly.

**The four thick conditions** (§2): authorship (`Authorship`: the actual verdict map is
`F`), transparency (`Transparent`: `A = M` as kernels; the weakest form that suffices for
the first theorem is `WeakTransparent`: on every record `A` assigns positive mass, the
likelihoods of `A` and `M` are proportional), Integrity's used part (`Integrity`: the
earlier record is a function of the later), openness (`Openness`: `B` is a garbling of
`A`, Blackwell's sense).

**The three thin properties** (§3): *correct* (`Correct`: on `A`'s support her credence is
`A`'s conditional), *sufficient* (`Sufficient`: the reference is a garbling of `A`), and
their product *value* (`Value`: for every finite decision problem, best-responding to her
credence under `A` does at least as well as any rule on the reference).  Names
provisional (P4).

**The theorems** (§4).  `correct_of_coherent_authorship_transparent` (1);
`sufficient_of_integrity_openness` (2 — the composition of a deterministic reduction with
a garbling is a garbling; sufficient is Blackwell's order by definition, and this is the
one-line lemma that puts the earlier record into it); `value_of_correct_sufficient` (3 —
the easy direction of Blackwell's theorem for a fixed rule); the converse of 3 refuted on
its *correct* half (`Witness.value_not_correct`: a wrong credence that happens to be the
reference's loses nothing against the reference) and filed on its *sufficient* half
(Blackwell's converse, `REPORT.md`); reflection as the special case with the trivial
baseline (§5: `sufficient_reflection_of_integrity`, `reflection_value`,
`totalTrust_of_correct`, `reflection_inherited_value` through
`InheritedAlgebra.value_iff_totalTrust`); preservation (§6:
`condReflection_iff_coherent`, `preservation`, `preservation_pair`, with
`MarginalMartingale` too weak: `Witness.marginal_not_correct`).

**The approximate form** (§7): the value loss against the model's Bayes value is at most
`D` times the transparency defect plus `D` times the authorship defect, from
`TransparentChannel.abs_expect_sub_le_width` (`value_loss_le_defects`,
`value_approx`).

**Licensed authorship** (§8): the single-verdict case is the singleton license
(`correct_of_licensed_singleton`); with two licensed credences at one record only one is
correct, so the theorem needs the selection in her model (`Witness.licensed_two_obstruction`).

**Witnesses** (§9): necessity of each thick hypothesis on two worlds, the converse
refutation, the marginal martingale, the trivial inhabitants.

**What this does not establish.**  Blackwell's converse (value for every problem under a
correct credence implies sufficient); anything about the baseline `B`, a parameter here;
the obligation accounting of Integrity, which §3 does not use; the kernel form of the
approximate bound (stated for deterministic records).  Names are provisional
(`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.InheritedAlgebra
import Workspace.Deference.Contrib.TransparentChannel

namespace Workspace.Deference.Contrib.ThinLegitimacy

open Finset

/-! ## 1. The setting -/

section Setting

variable {W Rec : Type*} [Fintype W] [Fintype Rec]

/-- A process from worlds to later records: a stochastic kernel.  A deterministic record is
the `0/1` case. -/
structure Kernel (W Rec : Type*) [Fintype Rec] where
  k : W → Rec → ℝ
  nonneg : ∀ w r, 0 ≤ k w r
  sum_one : ∀ w, ∑ r, k w r = 1

/-- The deterministic kernel of a record function. -/
noncomputable def detKernel [DecidableEq Rec] (a : W → Rec) : Kernel W Rec where
  k w r := if a w = r then 1 else 0
  nonneg _ _ := by split_ifs <;> norm_num
  sum_one w := by simp

/-- The record's mass under the prior. -/
noncomputable def mass (π : W → ℝ) (A : Kernel W Rec) (r : Rec) : ℝ := ∑ w, π w * A.k w r

/-- The posterior over worlds given a later record. -/
noncomputable def post (π : W → ℝ) (A : Kernel W Rec) (r : Rec) (w : W) : ℝ :=
  π w * A.k w r / mass π A r

/-- A credence map: her later credence as a function of her later record. -/
abbrev Credence (W Rec : Type*) := Rec → W → ℝ

theorem mass_nonneg (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (A : Kernel W Rec) (r : Rec) :
    0 ≤ mass π A r :=
  Finset.sum_nonneg fun w _ => mul_nonneg (hπ w) (A.nonneg w r)

/-- A record of zero mass has zero joint weight at every world. -/
theorem joint_eq_zero_of_mass_zero (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (A : Kernel W Rec)
    (r : Rec) (h : mass π A r = 0) (w : W) : π w * A.k w r = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun w _ => mul_nonneg (hπ w) (A.nonneg w r)).mp h w
    (Finset.mem_univ w)

/-- The posterior's expectation, unnormalized: `mass · E_post X = Σ_w π w A w r X w`. -/
theorem mass_mul_post_sum (π : W → ℝ) (A : Kernel W Rec) (r : Rec) (hr : 0 < mass π A r)
    (X : W → ℝ) : mass π A r * ∑ w, post π A r w * X w = ∑ w, π w * A.k w r * X w := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold post
  field_simp

/-- The posterior sums to one on the support. -/
theorem post_sum_one (π : W → ℝ) (A : Kernel W Rec) (r : Rec) (hr : 0 < mass π A r) :
    ∑ w, post π A r w = 1 := by
  unfold post
  rw [← Finset.sum_div, div_eq_one_iff_eq hr.ne']
  rfl

/-- The trivial process: one record, carrying nothing. -/
noncomputable def trivialKernel : Kernel W Unit where
  k _ _ := 1
  nonneg _ _ := zero_le_one
  sum_one _ := by simp

end Setting

/-! ## 2. The four thick conditions -/

section Thick

variable {W Rec Rec₀ RecB : Type*} [Fintype W] [Fintype Rec] [Fintype Rec₀] [Fintype RecB]

/-- **Coherence**: her program is her model's posterior on the model's support.  A
hypothesis about her — what "preserves, not guarantees" comes to. -/
def Coherent (π : W → ℝ) (M : Kernel W Rec) (F : Credence W Rec) : Prop :=
  ∀ r, 0 < mass π M r → F r = post π M r

/-- **Authorship**, the single-verdict case: the actual verdict map is her program. -/
def Authorship (F V : Credence W Rec) : Prop := V = F

/-- **Transparency**: the actual later record is generated as her model says. -/
def Transparent (A M : Kernel W Rec) : Prop := A = M

/-- **The weakest form that suffices for the first theorem**: on every record the actual
process reaches, its likelihood is proportional to the model's. -/
def WeakTransparent (π : W → ℝ) (A M : Kernel W Rec) : Prop :=
  ∀ r, 0 < mass π A r → ∃ c : ℝ, 0 < c ∧ ∀ w, A.k w r = c * M.k w r

theorem weakTransparent_of_transparent (π : W → ℝ) {A M : Kernel W Rec}
    (h : Transparent A M) : WeakTransparent π A M := by
  subst h
  exact fun _ _ => ⟨1, one_pos, fun w => by ring⟩

/-- **Integrity, the part used**: her earlier record is a function of the actual later
record — nothing entered earlier has left. -/
def Integrity (E : W → Rec₀) (A : Kernel W Rec) : Prop :=
  ∃ g : Rec → Rec₀, ∀ w r, 0 < A.k w r → g r = E w

/-- **A garbling** (Blackwell): `B` is `A` followed by a stochastic matrix. -/
def Garbling (A : Kernel W Rec) (B : Kernel W RecB) : Prop :=
  ∃ Γ : Rec → RecB → ℝ, (∀ r r', 0 ≤ Γ r r') ∧ (∀ r, ∑ r', Γ r r' = 1) ∧
    ∀ w r', B.k w r' = ∑ r, A.k w r * Γ r r'

/-- **Openness**: the baseline's later record is a garbling of the actual one — what would
have reached her did reach her, up to garbling.  A deterministic function of `A`'s record
is the `0/1` case. -/
def Openness (A : Kernel W Rec) (B : Kernel W RecB) : Prop := Garbling A B

omit [Fintype W] in
/-- Every process is a garbling of itself. -/
theorem garbling_refl [DecidableEq Rec] (A : Kernel W Rec) : Garbling A A :=
  ⟨fun r r' => if r = r' then 1 else 0, fun _ _ => by dsimp only; split_ifs <;> norm_num,
    fun r => by simp, fun w r' => by simp⟩

omit [Fintype W] in
/-- A deterministic reduction of the record is a garbling. -/
theorem garbling_of_map [DecidableEq RecB] (A : Kernel W Rec) (g : Rec → RecB) :
    Garbling A ⟨fun w r' => ∑ r, A.k w r * (if g r = r' then 1 else 0),
      fun w r' => Finset.sum_nonneg fun r _ => mul_nonneg (A.nonneg w r) (by split_ifs <;> norm_num),
      fun w => by
        rw [Finset.sum_comm]
        simp [A.sum_one]⟩ :=
  ⟨fun r r' => if g r = r' then 1 else 0, fun _ _ => by dsimp only; split_ifs <;> norm_num,
    fun r => by simp, fun _ _ => rfl⟩

omit [Fintype W] in
/-- The trivial process is a garbling of anything. -/
theorem garbling_trivial (A : Kernel W Rec) : Garbling A (trivialKernel (W := W)) :=
  ⟨fun _ _ => 1, fun _ _ => zero_le_one, fun _ => by simp, fun w _ => by
    simp [trivialKernel, A.sum_one]⟩

end Thick

/-! ## 3. The reference and the three thin properties -/

section Thin

variable {W Rec Rec₀ RecB : Type*} [Fintype W] [Fintype Rec] [Fintype Rec₀] [Fintype RecB]
  [DecidableEq Rec₀]

/-- **The reference**: her earlier record beside the baseline's later record. -/
noncomputable def refKernel (E : W → Rec₀) (B : Kernel W RecB) : Kernel W (Rec₀ × RecB) where
  k w p := (if E w = p.1 then 1 else 0) * B.k w p.2
  nonneg w p := mul_nonneg (by split_ifs <;> norm_num) (B.nonneg w p.2)
  sum_one w := by
    rw [Fintype.sum_prod_type]
    simp [B.sum_one]

/-- **Correct**: on the actual process's support, her later credence is the true conditional
distribution of the world given her later record. -/
def Correct (π : W → ℝ) (A : Kernel W Rec) (V : Credence W Rec) : Prop :=
  ∀ r, 0 < mass π A r → V r = post π A r

/-- **Sufficient**: the actual later record is at least as informative as the reference, in
Blackwell's sense — the reference is a garbling of it. -/
def Sufficient (E : W → Rec₀) (A : Kernel W Rec) (B : Kernel W RecB) : Prop :=
  Garbling A (refKernel E B)

/-- The payoff, by her prior, of a decision rule on a process's record. -/
noncomputable def payoff {R Act : Type*} [Fintype R] (π : W → ℝ) (K : Kernel W R)
    (u : Act → W → ℝ) (δ : R → Act) : ℝ :=
  ∑ w, ∑ r, π w * K.k w r * u (δ r) w

/-- A rule best-responds to a credence map on a decision problem. -/
def IsBest {Act : Type*} (V : Credence W Rec) (u : Act → W → ℝ) (δ : Rec → Act) : Prop :=
  ∀ r a, ∑ w, V r w * u a w ≤ ∑ w, V r w * u (δ r) w

/-- **Value**: for every finite decision problem, best-responding to her later credence under
the actual process does at least as well, by her prior, as any rule on the reference —
in particular as the reference's own best response. -/
def Value (π : W → ℝ) (E : W → Rec₀) (A : Kernel W Rec) (V : Credence W Rec)
    (B : Kernel W RecB) : Prop :=
  ∀ (Act : Type) [Fintype Act] (u : Act → W → ℝ) (δA : Rec → Act), IsBest V u δA →
    ∀ δB : Rec₀ × RecB → Act, payoff π (refKernel E B) u δB ≤ payoff π A u δA

end Thin

/-! ## 4. The theorems -/

section Theorems

variable {W Rec Rec₀ RecB : Type*} [Fintype W] [Fintype Rec] [Fintype Rec₀] [Fintype RecB]
  [DecidableEq Rec₀]

/-- Proportional likelihoods give proportional masses. -/
theorem mass_eq_of_prop (π : W → ℝ) (A M : Kernel W Rec) (r : Rec) (c : ℝ)
    (h : ∀ w, A.k w r = c * M.k w r) : mass π A r = c * mass π M r := by
  unfold mass
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by rw [h w]; ring

/-- Proportional likelihoods give the same posterior. -/
theorem post_eq_of_prop (π : W → ℝ) (A M : Kernel W Rec) (r : Rec) (c : ℝ) (hc : 0 < c)
    (h : ∀ w, A.k w r = c * M.k w r) : post π A r = post π M r := by
  funext w
  unfold post
  rw [h w, mass_eq_of_prop π A M r c h]
  rw [show π w * (c * M.k w r) = c * (π w * M.k w r) by ring]
  exact mul_div_mul_left _ _ hc.ne'

/-- **Theorem 1.**  Coherence, authorship and transparency (in its weakest form) give
*correct*. -/
theorem correct_of_coherent_authorship_transparent (π : W → ℝ) (M A : Kernel W Rec)
    (F V : Credence W Rec) (hF : Coherent π M F) (hV : Authorship F V)
    (hT : WeakTransparent π A M) : Correct π A V := by
  intro r hr
  obtain ⟨c, hc, hprop⟩ := hT r hr
  have hM : 0 < mass π M r := by
    have := mass_eq_of_prop π A M r c hprop
    rw [this] at hr
    exact pos_of_mul_pos_right hr hc.le
  rw [hV, hF r hM, post_eq_of_prop π A M r c hc hprop]

omit [Fintype W] in
/-- **Theorem 2.**  Integrity and openness give *sufficient*: a deterministic reduction of
the record beside a garbling of it is a garbling of it.  Sufficient is Blackwell's order
by definition; this is the lemma that places her earlier record inside the reference. -/
theorem sufficient_of_integrity_openness (E : W → Rec₀) (A : Kernel W Rec) (B : Kernel W RecB)
    (hI : Integrity E A) (hO : Openness A B) : Sufficient E A B := by
  obtain ⟨g, hg⟩ := hI
  obtain ⟨Γ, hΓ0, hΓ1, hΓ⟩ := hO
  refine ⟨fun r p => (if g r = p.1 then 1 else 0) * Γ r p.2,
    fun r p => mul_nonneg (by split_ifs <;> norm_num) (hΓ0 r p.2), fun r => ?_, fun w p => ?_⟩
  · rw [Fintype.sum_prod_type]
    simp [hΓ1 r]
  · show (if E w = p.1 then 1 else 0) * B.k w p.2 = _
    rw [hΓ w p.2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    show (if E w = p.1 then 1 else 0) * (A.k w r * Γ r p.2)
      = A.k w r * ((if g r = p.1 then 1 else 0) * Γ r p.2)
    rcases (A.nonneg w r).lt_or_eq with hpos | hzero
    · rw [hg w r hpos]; ring
    · rw [← hzero]; ring

/-- Under *correct*, best-responding to her credence is Bayes-optimal on each record of
positive mass: the unnormalized fiber inequality. -/
theorem fiber_le_of_correct {Act : Type*} (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (A : Kernel W Rec)
    (V : Credence W Rec) (hC : Correct π A V) (u : Act → W → ℝ) (δ : Rec → Act)
    (hδ : IsBest V u δ) (r : Rec) (a : Act) :
    ∑ w, π w * A.k w r * u a w ≤ ∑ w, π w * A.k w r * u (δ r) w := by
  rcases (mass_nonneg π hπ A r).lt_or_eq with hr | hr
  · have h := hδ r a
    rw [hC r hr] at h
    have h' := mul_le_mul_of_nonneg_left h hr.le
    rwa [mass_mul_post_sum π A r hr, mass_mul_post_sum π A r hr] at h'
  · have hz := joint_eq_zero_of_mass_zero π hπ A r hr.symm
    simp [hz]

/-- **Theorem 3.**  *Correct* and *sufficient* give *value*: the easy direction of
Blackwell's theorem, for every rule on the reference. -/
theorem value_of_correct_sufficient (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (E : W → Rec₀)
    (A : Kernel W Rec) (V : Credence W Rec) (B : Kernel W RecB) (hC : Correct π A V)
    (hS : Sufficient E A B) : Value π E A V B := by
  intro Act _ u δA hbest δB
  obtain ⟨Γ, hΓ0, hΓ1, hΓ⟩ := hS
  -- the reference payoff as a Γ-weighted sum of fiber payoffs of `A`
  have h1 : payoff π (refKernel E B) u δB
      = ∑ p, ∑ r, Γ r p * ∑ w, π w * A.k w r * u (δB p) w := by
    unfold payoff
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hw : ∀ w, π w * (refKernel E B).k w p * u (δB p) w
        = ∑ r, Γ r p * (π w * A.k w r * u (δB p) w) := by
      intro w
      rw [hΓ w p, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [Finset.sum_congr rfl (fun w _ => hw w), Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => by rw [Finset.mul_sum]
  have h2 : payoff π A u δA = ∑ r, ∑ w, π w * A.k w r * u (δA r) w := by
    unfold payoff; rw [Finset.sum_comm]
  rw [h1, h2]
  calc ∑ p, ∑ r, Γ r p * ∑ w, π w * A.k w r * u (δB p) w
      ≤ ∑ p, ∑ r, Γ r p * ∑ w, π w * A.k w r * u (δA r) w := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun r _ => ?_
        exact mul_le_mul_of_nonneg_left
          (fiber_le_of_correct π hπ A V hC u δA hbest r (δB p)) (hΓ0 r p)
    _ = ∑ r, (∑ p, Γ r p) * ∑ w, π w * A.k w r * u (δA r) w := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ r, ∑ w, π w * A.k w r * u (δA r) w := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hΓ1 r, one_mul]

/-- **The thick conditions give value**: theorems 1, 2 and 3 composed. -/
theorem value_of_thick (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (E : W → Rec₀) (M A : Kernel W Rec)
    (B : Kernel W RecB) (F V : Credence W Rec) (hF : Coherent π M F) (hV : Authorship F V)
    (hT : WeakTransparent π A M) (hI : Integrity E A) (hO : Openness A B) : Value π E A V B :=
  value_of_correct_sufficient π hπ E A V B
    (correct_of_coherent_authorship_transparent π M A F V hF hV hT)
    (sufficient_of_integrity_openness E A B hI hO)

end Theorems

/-! ## 5. Reflection: the trivial baseline -/

section Reflection

variable {W Rec Rec₀ : Type*} [Fintype W] [Fintype Rec] [Fintype Rec₀] [DecidableEq Rec₀]

omit [Fintype W] in
/-- **Reflection's reference** is her earlier record alone: the trivial baseline. -/
theorem sufficient_reflection_of_integrity (E : W → Rec₀) (A : Kernel W Rec)
    (hI : Integrity E A) : Sufficient E A (trivialKernel (W := W)) :=
  sufficient_of_integrity_openness E A trivialKernel hI (garbling_trivial A)

/-- **Reflection as value**: *correct* and Integrity alone — openness is the trivial
`garbling_trivial` and is not used — give value against her earlier self. -/
theorem reflection_value (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (E : W → Rec₀) (A : Kernel W Rec)
    (V : Credence W Rec) (hC : Correct π A V) (hI : Integrity E A) :
    Value π E A V (trivialKernel (W := W)) :=
  value_of_correct_sufficient π hπ E A V trivialKernel hC
    (sufficient_reflection_of_integrity E A hI)

variable [DecidableEq Rec]

/-- Her later credence read world by world through a deterministic record: the `Pr` of the
inherited algebra. -/
noncomputable def credenceOf (a : W → Rec) (V : Credence W Rec) (w v : W) : ℝ := V (a w) v

/-- The fiber identity for a deterministic record: the unnormalized expectation of `X` on
the fiber of `r` is the mass times the posterior expectation. -/
theorem fiber_sum_det (π : W → ℝ) (a : W → Rec) (r : Rec) (hr : 0 < mass π (detKernel a) r)
    (X : W → ℝ) :
    ∑ w, (if a w = r then π w * X w else 0)
      = mass π (detKernel a) r * ∑ w, post π (detKernel a) r w * X w := by
  rw [mass_mul_post_sum π (detKernel a) r hr X]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [detKernel]
  split_ifs <;> ring

/-- **Total trust from correct.**  Under a correct credence on a deterministic record, for
every variable `X` and threshold `s`, the mass of the worlds where she expects `X ≥ s`,
weighted by `X − s`, is nonnegative — the inherited total-trust condition. -/
theorem totalTrust_of_correct (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (a : W → Rec)
    (V : Credence W Rec) (hC : Correct π (detKernel a) V) (X : W → ℝ) (s : ℝ) :
    0 ≤ ∑ w, (if s ≤ ∑ v, credenceOf a V w v * X v then π w * (X w - s) else 0) := by
  classical
  -- group the worlds by their record
  have hsplit : ∑ w, (if s ≤ ∑ v, credenceOf a V w v * X v then π w * (X w - s) else 0)
      = ∑ r, ∑ w, (if a w = r then
          (if s ≤ ∑ v, credenceOf a V w v * X v then π w * (X w - s) else 0) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp
  rw [hsplit]
  refine Finset.sum_nonneg fun r _ => ?_
  rcases (mass_nonneg π hπ (detKernel a) r).lt_or_eq with hr | hr
  · -- on a fiber of positive mass the indicator is constant
    have hconst : ∀ w, a w = r →
        (s ≤ ∑ v, credenceOf a V w v * X v ↔ s ≤ ∑ v, post π (detKernel a) r v * X v) := by
      intro w hw
      unfold credenceOf
      rw [hw, hC r hr]
    by_cases hs : s ≤ ∑ v, post π (detKernel a) r v * X v
    · have heq : ∑ w, (if a w = r then
          (if s ≤ ∑ v, credenceOf a V w v * X v then π w * (X w - s) else 0) else 0)
          = ∑ w, (if a w = r then π w * (X w - s) else 0) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        by_cases hw : a w = r
        · simp only [hw, if_true, (hconst w hw).mpr hs]
        · simp [hw]
      rw [heq, fiber_sum_det π a r hr (fun w => X w - s)]
      have hpost : ∑ w, post π (detKernel a) r w * (X w - s)
          = (∑ w, post π (detKernel a) r w * X w) - s := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, post_sum_one π _ r hr,
          one_mul]
      rw [hpost]
      exact mul_nonneg hr.le (by linarith)
    · have heq : ∑ w, (if a w = r then
          (if s ≤ ∑ v, credenceOf a V w v * X v then π w * (X w - s) else 0) else 0) = 0 := by
        refine Finset.sum_eq_zero fun w _ => ?_
        by_cases hw : a w = r
        · have := (hconst w hw).not.mpr hs
          simp [hw, this]
        · simp [hw]
      rw [heq]
  · have hz := joint_eq_zero_of_mass_zero π hπ (detKernel a) r hr.symm
    refine le_of_eq (Finset.sum_eq_zero fun w _ => ?_).symm
    by_cases hw : a w = r
    · have h0 : π w = 0 := by
        have := hz w
        simp [detKernel, hw] at this
        exact this
      simp [hw, h0]
    · simp [hw]

/-- **Reflection in the inherited algebra.**  A correct credence on a deterministic record
satisfies the inherited Value statement — the followed strategy beats every constant option
on every witness menu — through `InheritedAlgebra.value_iff_totalTrust`.  The thick
conditions used are authorship and transparency (for *correct*) and Integrity (for the
reference to be her earlier record); openness is not among them. -/
theorem reflection_inherited_value (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (a : W → Rec)
    (V : Credence W Rec) (hC : Correct π (detKernel a) V) :
    ∀ (X : W → ℝ) (s : ℝ),
      s * (∑ w, π w) ≤ ∑ w, π w * (if s ≤ (∑ v, credenceOf a V w v * X v) then X w else s) :=
  fun X s =>
    (InheritedAlgebra.value_witness_iff_totalTrust π (credenceOf a V) X s).mpr
      (totalTrust_of_correct π hπ a V hC X s)

end Reflection

/-! ## 6. Preservation: the conditional form, and why the marginal form is too weak -/

section Preservation

variable {W Rec Rec₀ : Type*} [Fintype W] [Fintype Rec] [Fintype Rec₀] [DecidableEq Rec₀]

/-- **Conditional reflection** of a credence map in a process: on every record the process
reaches, her expectation of every variable is the conditional expectation given the
record. -/
def CondReflection (π : W → ℝ) (K : Kernel W Rec) (V : Credence W Rec) : Prop :=
  ∀ r, 0 < mass π K r → ∀ X : W → ℝ, ∑ w, V r w * X w = ∑ w, post π K r w * X w

/-- Conditional reflection in the model is coherence; in the actual process it is
*correct*. -/
theorem condReflection_iff_coherent [DecidableEq W] (π : W → ℝ) (K : Kernel W Rec)
    (V : Credence W Rec) :
    CondReflection π K V ↔ Coherent π K V := by
  constructor
  · intro h r hr
    funext w
    have := h r hr (fun v => if v = w then 1 else 0)
    simpa using this
  · intro h r hr X
    rw [h r hr]

/-- **Theorem 6, preservation.**  Conditional reflection in her model, authorship and
transparency give conditional reflection in the actual process. -/
theorem preservation [DecidableEq W] (π : W → ℝ) (M A : Kernel W Rec) (F V : Credence W Rec)
    (hM : CondReflection π M F) (hV : Authorship F V) (hT : WeakTransparent π A M) :
    CondReflection π A V :=
  (condReflection_iff_coherent π A V).mpr
    (correct_of_coherent_authorship_transparent π M A F V
      ((condReflection_iff_coherent π M F).mp hM) hV hT)

/-- **The pair form.**  With Integrity, conditioning on her later record is conditioning on
her whole record: the actual later record and the earlier one together carry the same
posterior as the later record alone. -/
theorem preservation_pair (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (E : W → Rec₀) (A : Kernel W Rec)
    (V : Credence W Rec) (hC : Correct π A V) (hI : Integrity E A) (e : Rec₀) (r : Rec)
    (hp : 0 < mass π (refKernel E A) (e, r)) : V r = post π (refKernel E A) (e, r) := by
  obtain ⟨g, hg⟩ := hI
  -- some world of positive joint weight lies in the fiber, so `g r = e`
  have hex : ∃ w, 0 < π w * A.k w r ∧ E w = e := by
    by_contra hno
    have hno' : ∀ w, 0 < π w * A.k w r → E w ≠ e := fun w h he => hno ⟨w, h, he⟩
    have hzero : mass π (refKernel E A) (e, r) = 0 := by
      unfold mass
      refine Finset.sum_eq_zero fun w _ => ?_
      show π w * ((if E w = e then 1 else 0) * A.k w r) = 0
      rcases (mul_nonneg (hπ w) (A.nonneg w r)).lt_or_eq with hpos | hz
      · have := hno' w hpos
        simp [this]
      · rw [show π w * ((if E w = e then 1 else 0) * A.k w r)
            = (if E w = e then 1 else 0) * (π w * A.k w r) by ring, ← hz, mul_zero]
    linarith
  obtain ⟨w₀, hw₀, he⟩ := hex
  have hA₀ : 0 < A.k w₀ r := by
    rcases (A.nonneg w₀ r).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hw₀; exact absurd hw₀ (lt_irrefl 0)
  have hgr : g r = e := (hg w₀ r hA₀).trans he
  -- the two columns agree world by world
  have hcol : ∀ w, (refKernel E A).k w (e, r) = A.k w r := by
    intro w
    show (if E w = e then 1 else 0) * A.k w r = A.k w r
    rcases (A.nonneg w r).lt_or_eq with h | h
    · rw [if_pos ((hg w r h).symm.trans hgr), one_mul]
    · rw [← h, mul_zero]
  have hmass : mass π (refKernel E A) (e, r) = mass π A r := by
    unfold mass
    exact Finset.sum_congr rfl fun w _ => by rw [hcol w]
  have hr : 0 < mass π A r := hmass ▸ hp
  rw [hC r hr]
  funext w
  unfold post
  rw [hcol w, hmass]

/-- **The marginal martingale**: her expected later credence is her prior.  Too weak for
preservation — `Witness.marginal_not_correct`, and the inherited `AntiExpert`. -/
def MarginalMartingale (π : W → ℝ) (A : Kernel W Rec) (V : Credence W Rec) : Prop :=
  ∀ v, ∑ w, ∑ r, π w * A.k w r * V r v = π v

end Preservation

/-! ## 7. The approximate form -/

section Approximate

open Workspace.Deference.Contrib.LICorrigibility (expectR)
open Workspace.Deference.Contrib.TransparentChannel (disagree abs_expect_sub_le_width
  disagree_nonneg)

variable {W Rec Rec₀ RecB : Type*} [Fintype W] [Fintype Rec] [Fintype Rec₀] [Fintype RecB]
  [DecidableEq Rec₀] [DecidableEq Rec] [DecidableEq W]

omit [DecidableEq W] in
/-- The payoff of a rule on a deterministic record is an expectation over worlds. -/
theorem payoff_det {Act : Type*} (π : W → ℝ) (a : W → Rec) (u : Act → W → ℝ) (δ : Rec → Act) :
    payoff π (detKernel a) u δ = expectR π (fun w => u (δ (a w)) w) := by
  unfold payoff expectR
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [detKernel]

/-- **The transparency defect**: the prior mass of the worlds where the actual record is not
the model's. -/
noncomputable def transparencyDefect (π : W → ℝ) (a m : W → Rec) : ℝ :=
  expectR π (fun w => if a w = m w then 0 else 1)

/-- **The authorship defect**: the prior mass of the worlds where the actual verdict is not
her program's, on the actual record. -/
noncomputable def authorshipDefect (π : W → ℝ) (a : W → Rec) (F V : Credence W Rec) : ℝ :=
  expectR π (fun w => if V (a w) = F (a w) then 0 else 1)

/-- **The value loss is at most `D` times the two defects.**  Her payoff under the actual
process, best-responding to her actual verdict, is within `D·(τ + α)` of the payoff she
would get under the model, best-responding to her program — for any decision problem with
values in a band of width `D`, provided her selection depends on the credence alone. -/
theorem value_loss_le_defects {Act : Type*} [DecidableEq Act] (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w)
    (a m : W → Rec) (F V : Credence W Rec) (u : Act → W → ℝ) (D : ℝ)
    (hD₀ : 0 ≤ D) (hu : ∀ x x' w w', |u x w - u x' w'| ≤ D) (δV δF : Rec → Act)
    (hsel : ∀ r, V r = F r → δV r = δF r) :
    |payoff π (detKernel a) u δV - payoff π (detKernel m) u δF|
      ≤ D * (transparencyDefect π a m + authorshipDefect π a F V) := by
  rw [payoff_det, payoff_det]
  have hD : 0 ≤ D := by
    rcases isEmpty_or_nonempty W with hW | hW
    · exact hD₀
    · obtain ⟨w₀⟩ := hW
      have := hu (δV (a w₀)) (δV (a w₀)) w₀ w₀
      simpa using le_trans (abs_nonneg _) this
  have hwidth := abs_expect_sub_le_width π hπ (fun p : Act × W => u p.1 p.2) D
    (fun p p' => hu p.1 p'.1 p.2 p'.2) (fun w => (δV (a w), w)) (fun w => (δF (m w), w))
  simp only at hwidth
  refine le_trans hwidth (mul_le_mul_of_nonneg_left ?_ hD)
  unfold transparencyDefect authorshipDefect expectR
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hπ w)
  unfold disagree
  dsimp only
  by_cases h1 : a w = m w
  · by_cases h2 : V (a w) = F (a w)
    · have h3 : (δV (a w), w) = (δF (m w), w) := by rw [← h1, hsel _ h2]
      rw [if_pos h3, if_pos h1, if_pos h2]; norm_num
    · rw [if_pos h1, if_neg h2]; split_ifs <;> norm_num
  · rw [if_neg h1]; split_ifs <;> norm_num


/-- **The approximate value theorem.**  Against a baseline the *model* is sufficient for,
her actual payoff is within `D·(τ + α)` of the reference's: coherence makes her program
Bayes-optimal under the model, and the two defects bound the passage to the actual
process. -/
theorem value_approx {Act : Type} [DecidableEq Act] [Fintype Act] (π : W → ℝ)
    (hπ : ∀ w, 0 ≤ π w) (E : W → Rec₀) (a m : W → Rec) (B : Kernel W RecB)
    (F V : Credence W Rec) (hF : Coherent π (detKernel m) F)
    (hS : Sufficient E (detKernel m) B) (u : Act → W → ℝ) (D : ℝ) (hD₀ : 0 ≤ D)
    (hu : ∀ x x' w w', |u x w - u x' w'| ≤ D) (δV δF : Rec → Act) (hbest : IsBest F u δF)
    (hsel : ∀ r, V r = F r → δV r = δF r) (δB : Rec₀ × RecB → Act) :
    payoff π (refKernel E B) u δB
      ≤ payoff π (detKernel a) u δV + D * (transparencyDefect π a m + authorshipDefect π a F V) := by
  have h1 : payoff π (refKernel E B) u δB ≤ payoff π (detKernel m) u δF :=
    value_of_correct_sufficient π hπ E (detKernel m) F B hF hS Act u δF hbest δB
  have h2 := value_loss_le_defects π hπ a m F V u D hD₀ hu δV δF hsel
  have h3 := (abs_le.mp h2).1
  linarith

end Approximate

/-! ## 8. Licensed authorship -/

section Licensed

variable {W Rec : Type*} [Fintype W] [Fintype Rec]

/-- **Relational authorship**, the single-verdict case: her actual credence at each record
lies in the set the record licenses. -/
def LicensedAuthorship (Lic : Rec → Set (W → ℝ)) (V : Credence W Rec) : Prop :=
  ∀ r, V r ∈ Lic r

/-- **Theorem 1 for licensed choice, the singleton case.**  Where the license at every
reached record is exactly her program's credence, licensed authorship is authorship and
*correct* follows. -/
theorem correct_of_licensed_singleton (π : W → ℝ) (M A : Kernel W Rec) (F V : Credence W Rec)
    (Lic : Rec → Set (W → ℝ)) (hLic : ∀ r, 0 < mass π A r → Lic r = {F r})
    (hV : LicensedAuthorship Lic V) (hF : Coherent π M F) (hT : WeakTransparent π A M) :
    Correct π A V := by
  intro r hr
  have hVr : V r = F r := by
    have := hV r
    rw [hLic r hr] at this
    exact this
  obtain ⟨c, hc, hprop⟩ := hT r hr
  have hM : 0 < mass π M r := by
    have := mass_eq_of_prop π A M r c hprop
    rw [this] at hr
    exact pos_of_mul_pos_right hr hc.le
  rw [hVr, hF r hM, post_eq_of_prop π A M r c hc hprop]

end Licensed

/-! ## 9. The landed predicates, read into the setting -/

section Landed

open Workspace.Deference.Contrib.TransparentChannel (Realizes)
open Workspace.Deference.Contrib.ReasonMediatedAuthorship (ReasonMediated)

variable {Q Z Ω X Y ℛ 𝒱 : Type*} [Fintype Z] [Fintype Y] [DecidableEq Y]

omit [Fintype Z] in
/-- **Transparency from `Realizes`.**  Reading the exterior as the world, a continuation's
channel as the actual later record and the declared reference on its declared inputs as
the model's, `Realizes` is transparency of the actual process to the model, record by
record. -/
theorem transparent_of_realizes (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y) (κ : X → Z → Y)
    (D : Set Q) (h : Realizes β x f κ D) (q : Q) (hq : q ∈ D) :
    Transparent (detKernel fun z => f (β q z)) (detKernel fun z => κ (x (β q z)) z) := by
  unfold Transparent
  congr 1
  funext z
  exact h q hq z

/-- Under `Realizes` the posteriors of the actual and the reference process agree on every
record: the kernel-level reading of `TransparentChannel.posterior_weight_eq`. -/
theorem post_eq_of_realizes (π : Z → ℝ) (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y)
    (κ : X → Z → Y) (D : Set Q) (h : Realizes β x f κ D) (q : Q) (hq : q ∈ D) (r : Y) :
    post π (detKernel fun z => f (β q z)) r = post π (detKernel fun z => κ (x (β q z)) z) r := by
  rw [transparent_of_realizes β x f κ D h q hq]

omit [Fintype Z] [Fintype Y] [DecidableEq Y] in
/-- **Authorship from `ReasonMediated`.**  At a fixed exterior, two audited continuations
with the same reason trace carry the same verdict — so where the actual record equals the
model's, the actual verdict is the model's verdict of that record: authorship pointwise,
on the records transparency delivers. -/
theorem authorship_of_mediated (β : Q → Z → Ω) (R : Ω → ℛ) (V : Ω → 𝒱) (D : Set Q) (z : Z)
    (h : ReasonMediated β R V D z) (qA qM : Q) (hA : qA ∈ D) (hM : qM ∈ D)
    (hrec : R (β qA z) = R (β qM z)) : V (β qA z) = V (β qM z) :=
  h qA hA qM hM hrec

end Landed

/-! ## 10. Witnesses -/

namespace Witness

/-- Two worlds, the uniform prior. -/
noncomputable def π₂ : Fin 2 → ℝ := fun _ => 1 / 2

theorem π₂_nonneg : ∀ w, 0 ≤ π₂ w := fun _ => by norm_num [π₂]

/-- The revealing record. -/
noncomputable def reveal : Kernel (Fin 2) (Fin 2) := detKernel id

/-- The uninformative record on two record values. -/
noncomputable def uninformative : Kernel (Fin 2) (Fin 2) where
  k _ _ := 1 / 2
  nonneg _ _ := by norm_num
  sum_one _ := by norm_num [Fin.sum_univ_two]

/-- The blank record. -/
noncomputable def blank : Kernel (Fin 2) Unit := trivialKernel

/-- The point-mass credence: the correct credence on the revealing record. -/
noncomputable def pointMass : Credence (Fin 2) (Fin 2) := fun r w => if w = r then 1 else 0

/-- The prior as a credence map. -/
noncomputable def priorCredence : Credence (Fin 2) (Fin 2) := fun _ _ => 1 / 2

theorem mass_reveal (r : Fin 2) : mass π₂ reveal r = 1 / 2 := by
  fin_cases r <;> norm_num [mass, reveal, detKernel, π₂, Fin.sum_univ_two]

theorem post_reveal (r : Fin 2) : post π₂ reveal r = pointMass r := by
  funext w
  fin_cases r <;> fin_cases w <;> norm_num [post, mass, reveal, detKernel, π₂, pointMass,
    Fin.sum_univ_two]

theorem mass_uninformative (r : Fin 2) : mass π₂ uninformative r = 1 / 2 := by
  norm_num [mass, uninformative, π₂, Fin.sum_univ_two]

theorem post_uninformative (r : Fin 2) : post π₂ uninformative r = priorCredence r := by
  funext w
  unfold post
  rw [mass_uninformative]
  norm_num [uninformative, π₂, priorCredence]

/-- **The thick package is inhabited**: the revealing process is its own model, her program
the point mass, her earlier record blank, the baseline blank. -/
theorem thick_inhabited :
    Coherent π₂ reveal pointMass ∧ Authorship pointMass pointMass ∧ Transparent reveal reveal ∧
      Integrity (fun _ : Fin 2 => ()) reveal ∧ Openness reveal blank :=
  ⟨fun r _ => (post_reveal r).symm, rfl, rfl, ⟨fun _ => (), fun _ _ _ => rfl⟩,
    garbling_trivial reveal⟩

/-- The thin properties hold on the witness, by the theorems. -/
theorem thin_inhabited :
    Correct π₂ reveal pointMass ∧ Sufficient (fun _ : Fin 2 => ()) reveal blank ∧
      Value π₂ (fun _ : Fin 2 => ()) reveal pointMass blank :=
  ⟨correct_of_coherent_authorship_transparent π₂ reveal reveal pointMass pointMass
      thick_inhabited.1 thick_inhabited.2.1 (weakTransparent_of_transparent π₂ thick_inhabited.2.2.1),
    sufficient_of_integrity_openness _ reveal blank thick_inhabited.2.2.2.1 thick_inhabited.2.2.2.2,
    value_of_thick π₂ π₂_nonneg _ reveal reveal blank pointMass pointMass thick_inhabited.1
      thick_inhabited.2.1 (weakTransparent_of_transparent π₂ thick_inhabited.2.2.1)
      thick_inhabited.2.2.2.1 thick_inhabited.2.2.2.2⟩

/-- **Transparency is necessary for theorem 1**: her model uninformative, the actual process
revealing, her program coherent and authored — her credence is the prior, the truth is the
point mass. -/
theorem transparency_necessary :
    Coherent π₂ uninformative priorCredence ∧ Authorship priorCredence priorCredence ∧
      ¬ Transparent reveal uninformative ∧ ¬ Correct π₂ reveal priorCredence := by
  refine ⟨fun r _ => (post_uninformative r).symm, rfl, fun h => ?_, fun h => ?_⟩
  · have := congrArg (fun K : Kernel (Fin 2) (Fin 2) => K.k 0 0) h
    norm_num [reveal, detKernel, uninformative] at this
  · have := congrFun (h 0 (by rw [mass_reveal]; norm_num)) 0
    rw [post_reveal] at this
    norm_num [priorCredence, pointMass] at this

/-- The altered program: her credence at each record is the point mass on the *other*
world. -/
noncomputable def swapped : Credence (Fin 2) (Fin 2) := fun r w => if w = r then 0 else 1

/-- **Authorship is necessary for theorem 1**: the record transparent, her program coherent,
the verdict map altered off the record — incorrect at every record. -/
theorem authorship_necessary :
    Coherent π₂ reveal pointMass ∧ Transparent reveal reveal ∧ ¬ Authorship pointMass swapped ∧
      ¬ Correct π₂ reveal swapped := by
  refine ⟨fun r _ => (post_reveal r).symm, rfl, fun h => ?_, fun h => ?_⟩
  · have := congrFun (congrFun h 0) 0
    norm_num [pointMass, swapped] at this
  · have := congrFun (h 0 (by rw [mass_reveal]; norm_num)) 0
    rw [post_reveal] at this
    norm_num [swapped, pointMass] at this

/-- **The marginal martingale is too weak**: the altered program's expected credence is the
prior, and it is correct nowhere. -/
theorem marginal_not_correct :
    MarginalMartingale π₂ reveal swapped ∧ ¬ Correct π₂ reveal swapped := by
  refine ⟨fun v => ?_, authorship_necessary.2.2.2⟩
  fin_cases v <;> norm_num [reveal, detKernel, swapped, π₂, Fin.sum_univ_two]

/-- A garbling of the uninformative process is uninformative. -/
theorem garbling_uninformative_const {RecB : Type*} [Fintype RecB] (B : Kernel (Fin 2) RecB)
    (h : Garbling uninformative B) (r' : RecB) : B.k 0 r' = B.k 1 r' := by
  obtain ⟨Γ, -, -, hΓ⟩ := h
  rw [hΓ 0 r', hΓ 1 r']
  rfl

/-- **Integrity is necessary for theorem 2**: the earlier record reveals the world, the
later record is uninformative, the baseline blank — the reference is not a garbling of the
later record. -/
theorem integrity_necessary :
    Openness uninformative blank ∧ ¬ Integrity (fun w : Fin 2 => w) uninformative ∧
      ¬ Sufficient (fun w : Fin 2 => w) uninformative blank := by
  refine ⟨garbling_trivial uninformative, fun ⟨g, hg⟩ => ?_, fun h => ?_⟩
  · have h0 := hg 0 0 (by norm_num [uninformative])
    have h1 := hg 1 0 (by norm_num [uninformative])
    rw [h0] at h1
    exact absurd h1 (by decide)
  · have := garbling_uninformative_const _ h (0, ())
    norm_num [refKernel, blank, trivialKernel] at this

/-- **Openness is necessary for theorem 2**: the earlier record blank, the later record
uninformative, the baseline revealing. -/
theorem openness_necessary :
    Integrity (fun _ : Fin 2 => ()) uninformative ∧ ¬ Openness uninformative reveal ∧
      ¬ Sufficient (fun _ : Fin 2 => ()) uninformative reveal := by
  refine ⟨⟨fun _ => (), fun _ _ _ => rfl⟩, fun h => ?_, fun h => ?_⟩
  · have := garbling_uninformative_const _ h 0
    norm_num [reveal, detKernel] at this
  · have := garbling_uninformative_const _ h ((), 0)
    norm_num [refKernel, reveal, detKernel] at this

/-- A wrong credence that happens to be the reference's: the point mass at record `0`, the
prior at record `1`. -/
noncomputable def halfWrong : Credence (Fin 2) (Fin 2) :=
  fun r w => if r = 0 then (if w = 0 then 1 else 0) else 1 / 2

/-- **The converse of theorem 3 fails on its *correct* half.**  The revealing process with
the half-wrong credence has *value* against the blank reference for every decision problem
— on record `1` she acts as the reference would — and is not *correct*. -/
theorem value_not_correct :
    Value π₂ (fun _ : Fin 2 => ()) reveal halfWrong blank ∧ ¬ Correct π₂ reveal halfWrong := by
  constructor
  · intro Act _ u δA hbest δB
    have h0 := hbest 0 (δB ((), ()))
    have h1 := hbest 1 (δB ((), ()))
    have h01 := hbest 0 (δA 1)
    simp only [halfWrong, Fin.sum_univ_two] at h0 h1 h01
    norm_num at h0 h1 h01
    unfold payoff
    simp only [refKernel, blank, trivialKernel, reveal, detKernel, π₂, Fin.sum_univ_two,
      Fintype.sum_prod_type, Fintype.sum_unique]
    norm_num
    linarith
  · intro h
    have := congrFun (h 1 (by rw [mass_reveal]; norm_num)) 1
    rw [post_reveal] at this
    norm_num [halfWrong, pointMass] at this

/-- **Licensed choice with two licensed credences**: both the point mass and the prior are
licensed at record `0`; only the point mass is correct.  Which she takes is a selection,
and the theorem needs the selection in her model. -/
theorem licensed_two_obstruction :
    LicensedAuthorship (fun _ : Fin 2 => {pointMass 0, priorCredence 0}) (fun _ => priorCredence 0) ∧
      LicensedAuthorship (fun _ : Fin 2 => {pointMass 0, priorCredence 0}) (fun _ => pointMass 0) ∧
      ¬ Correct π₂ reveal (fun _ => priorCredence 0) := by
  refine ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun h => ?_⟩
  have := congrFun (h 0 (by rw [mass_reveal]; norm_num)) 0
  rw [post_reveal] at this
  norm_num [priorCredence, pointMass] at this

end Witness

/-! ## 11. Covert blocking: when silence is informative

A process that always reads silence is *correct* at silence exactly when her model's
likelihood of silence is the same across the prior's support.  The eight-world fixture had
silence at probability one half in every world; with a challenge likelier in one world
than another, silence is informative and covert blocking breaks both the weakest form of
transparency and *correct*. -/

section Silence

variable {W Rec : Type*} [Fintype W] [Fintype Rec] [DecidableEq Rec]

/-- The process that always reads one record. -/
noncomputable def constKernel (r₀ : Rec) : Kernel W Rec := detKernel fun _ => r₀

theorem mass_const (π : W → ℝ) (r₀ : Rec) : mass π (constKernel r₀) r₀ = ∑ w, π w := by
  unfold mass constKernel detKernel
  simp

/-- **The silence characterization.**  Her coherent credence at silence is the actual
conditional given silence iff her model's likelihood of silence is the same at every world
of positive prior. -/
theorem correct_silence_iff (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (M : Kernel W Rec) (r₀ : Rec)
    (hM : 0 < mass π M r₀) (hsum : 0 < ∑ w, π w) :
    post π M r₀ = post π (constKernel r₀) r₀ ↔
      ∀ w w', 0 < π w → 0 < π w' → M.k w r₀ = M.k w' r₀ := by
  have hconst : ∀ w, post π (constKernel r₀) r₀ w = π w / ∑ v, π v := by
    intro w
    unfold post
    rw [mass_const]
    simp [constKernel, detKernel]
  constructor
  · intro h w w' hw hw'
    have e := congrFun h w
    have e' := congrFun h w'
    rw [hconst] at e e'
    unfold post at e e'
    have hw1 : M.k w r₀ = mass π M r₀ / ∑ v, π v := by
      field_simp at e ⊢
      nlinarith [e]
    have hw2 : M.k w' r₀ = mass π M r₀ / ∑ v, π v := by
      field_simp at e' ⊢
      nlinarith [e']
    rw [hw1, hw2]
  · intro h
    funext w
    rw [hconst]
    unfold post
    rcases (hπ w).lt_or_eq with hw | hw
    · -- every world of positive prior shares the likelihood `s`; the mass is `s · Σπ`
      have hmass : mass π M r₀ = M.k w r₀ * ∑ v, π v := by
        unfold mass
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rcases (hπ v).lt_or_eq with hv | hv
        · rw [h v w hv hw]; ring
        · rw [← hv]; ring
      have hs : 0 < M.k w r₀ := by
        rw [hmass] at hM
        exact pos_of_mul_pos_left hM hsum.le
      rw [hmass]
      field_simp
    · rw [← hw]; simp

/-- **Covert blocking breaks *correct* iff silence is informative**: with authorship and
coherence, the actual process always reading silence, her credence at silence is the truth
iff the model's silence likelihood is constant on the support. -/
theorem covert_blocking_correct_iff (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (M : Kernel W Rec) (r₀ : Rec)
    (F V : Credence W Rec) (hF : Coherent π M F) (hV : Authorship F V)
    (hM : 0 < mass π M r₀) (hsum : 0 < ∑ w, π w) :
    Correct π (constKernel r₀) V ↔ ∀ w w', 0 < π w → 0 < π w' → M.k w r₀ = M.k w' r₀ := by
  rw [← correct_silence_iff π hπ M r₀ hM hsum]
  constructor
  · intro h
    have := h r₀ (by rw [mass_const]; exact hsum)
    rw [hV, hF r₀ hM] at this
    exact this
  · intro h r hr
    have hr0 : r = r₀ := by
      by_contra hne
      have : mass π (constKernel r₀) r = 0 := by
        unfold mass constKernel detKernel
        simp [Ne.symm hne]
      linarith
    subst hr0
    rw [hV, hF r hM, h]

namespace Witness

/-- **Informative silence.**  Two worlds, uniform prior; under her model the challenge is
blocked (silence) with probability `1/2` in world `0` and `1/4` in world `1`, so silence is
evidence for world `0`; the agent blocks every challenge.  Her coherent credence at silence
is not the truth, and the weak form of transparency fails. -/
noncomputable def silentModel : Kernel (Fin 2) (Fin 3) where
  k := ![![1 / 4, 1 / 4, 1 / 2], ![1 / 4, 1 / 2, 1 / 4]]
  nonneg w r := by fin_cases w <;> fin_cases r <;> norm_num
  sum_one w := by fin_cases w <;> norm_num [Fin.sum_univ_three]

noncomputable def alwaysSilent : Kernel (Fin 2) (Fin 3) := constKernel 2

theorem informative_silence_not_correct :
    ¬ Correct π₂ alwaysSilent (fun r => post π₂ silentModel r) ∧
      ¬ WeakTransparent π₂ alwaysSilent silentModel := by
  constructor
  · intro h
    have hm : 0 < mass π₂ alwaysSilent 2 := by
      norm_num [mass, alwaysSilent, constKernel, detKernel, π₂, Fin.sum_univ_two]
    have := congrFun (h 2 hm) 0
    norm_num [post, mass, alwaysSilent, constKernel, detKernel, silentModel, π₂,
      Fin.sum_univ_two] at this
  · intro h
    obtain ⟨c, -, hc⟩ := h 2 (by
      norm_num [mass, alwaysSilent, constKernel, detKernel, π₂, Fin.sum_univ_two])
    have h0 := hc 0
    have h1 := hc 1
    norm_num [alwaysSilent, constKernel, detKernel, silentModel] at h0 h1
    linarith

end Witness

end Silence

end Workspace.Deference.Contrib.ThinLegitimacy

#print axioms Workspace.Deference.Contrib.ThinLegitimacy.correct_silence_iff
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.covert_blocking_correct_iff
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.Witness.informative_silence_not_correct

#print axioms Workspace.Deference.Contrib.ThinLegitimacy.correct_of_coherent_authorship_transparent
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.sufficient_of_integrity_openness
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.fiber_le_of_correct
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.value_of_correct_sufficient
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.value_of_thick
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.sufficient_reflection_of_integrity
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.reflection_value
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.totalTrust_of_correct
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.reflection_inherited_value
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.condReflection_iff_coherent
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.preservation
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.preservation_pair
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.value_loss_le_defects
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.value_approx
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.correct_of_licensed_singleton
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.transparent_of_realizes
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.post_eq_of_realizes
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.authorship_of_mediated
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.Witness.thick_inhabited
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.Witness.thin_inhabited
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.Witness.transparency_necessary
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.Witness.authorship_necessary
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.Witness.marginal_not_correct
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.Witness.integrity_necessary
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.Witness.openness_necessary
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.Witness.value_not_correct
#print axioms Workspace.Deference.Contrib.ThinLegitimacy.Witness.licensed_two_obstruction
