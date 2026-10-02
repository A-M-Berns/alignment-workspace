import Cleanroom.Udt.UdtPolicyCalc.LocalGlobal

/-!
# T7: EDT node value, the `κ`-collapse lemma, and the coupled mugging
# T5: "updatelessness boosts endorsed agency" · T10: Geometric UDT as separable/coupled

Sources: `run2/work/edt-node-value.md` §1–§4 (trust-lab-028/029/030, 2-019), the red-team
`redteam/updateless-deference-redteam.md` §A–§E; [[meaning-and-agency-reference]] §Updatelessness
and Q6 (udt-rep-2-016); [[updateless-deference-ideate]] §3 Idea C (trust-lab-2-015, 027) and
`AGENDA.md` line 90 (Abram's Geometric-UDT sentence).

**Definitions of record.** Over `udt-policy-calc`'s `Policy S A` and coupled utilities
`U : Policy S A → ℝ`: a self-prediction kernel `κ : S → A → Policy S A` ("conditioned on reaching
`s` and playing `a`, which whole policy do I expect to be running?"), the EDT node value
`vNode U κ s a := U (κ s a)` (the kernel is inside the definition, not a relabel), the decoupled
kernels `Decoupled κ base` (`κ s a = update (base s) s a`: a fixed off-`s` prediction independent of
`a`), the EDT-argmax assemblies (`EdtAssembly U κ π`), and the round-1 relation `UDefers U v`
quantified over *every* argmax selection (the tie fix of trust-lab-2-019(1)) with its
`∃`-selection variant `UDefersSome`.

* `vNode_decoupled_eq` (P): under weighted separability and decoupling,
  `vNode U κ s a = p s · u s a + ∑_{t ≠ s} p t · u t (base s t)`.
* `edt_decoupled_globally_optimal` (P): under the same hypotheses every EDT-argmax assembly is
  globally optimal; the local `u`-argmax is *derived* from the EDT ranking, not assumed.
* The mugging (`mugU`, N+): non-separable, the severing `κsev` makes refusing the EDT argmax,
  every EDT assembly scores `0` while `(pay, pay)` scores `9900` (`mugging_edt_misses`), the
  severed amount is `10000` (`gap_is_acausal_payoff`), the correlated `κcorr` restores agreement;
  `separability_load_bearing`: without `Separable`, the conclusion of the collapse theorem is false.
* `udefers_of_separable` (T): the round-1 relation is a wrapper around argmax;
  `udefers_tie_witness` (N+): ties make `UDefersSome` and `UDefers` differ.
* T5: the decoupled kernel's **base is a free parameter and decides the question by itself**
  (repair round 1, audit r1 B2): an EDT assembly through the kernel decoupled at the policy
  itself (`selfKernel π`) is, definitionally, `udt-policy-calc`'s `IsLocalOptimum`
  (`edtAssembly_selfKernel_iff`), so every optimum of every `U` is an endorsed updateful assembly
  (`edtAssembly_selfKernel_of_optimal`) and every non-global local optimum of every `U` is an
  unendorsed one. The mugging and Coordinated Buttons each exhibit *both* behaviours
  (`mugging_pay_base`, `coordButtons_refuse_base`; `κsev = selfKernel (0,0)`,
  `κcb = selfKernel (1,1)`). `coordButtons_assembly_optimal` is kept as the base-`(1,1)` instance
  and graded N−: its certificate is generic in the base and says nothing about Coordinated
  Buttons in particular. Under the kernel reading, "updateful ⟹ not endorsed" is therefore not a
  property of `U` at all until the base is fixed, and udt-rep-2-016's "exactly under
  cross-situation dependence" is ill-posed rather than refuted.
* T10: `geometric_udt_identity` (T) and the values-coin reading of the mugging (`values_coin`).
-/

namespace Cleanroom.Udt.UdtEndorsePolicy

open Cleanroom.Udt.UdtPolicyCalc Finset

noncomputable section

section General

variable {S A : Type} [Fintype S] [DecidableEq S]

/-- **Weighted separability** (the lab's `Separable U p u`): `U π = ∑ s, p s · u s (π s)`.
Equivalent to `udt-policy-calc`'s `Separable` with the weight absorbed (`separable_iff_weighted`).
Source: `run2/work/edt-node-value.md` §2; [[updateless-deference-model]] §1.1
Kind: D
Fidelity: exact (the lab's definition)
Hyps: n/a -/
def SeparableW (U : Policy S A → ℝ) (p : S → ℝ) (u : S → A → ℝ) : Prop :=
  ∀ π, U π = ∑ s, p s * u s (π s)

omit [DecidableEq S] in
/-- **The lab's weighted separability is the run's `Separable`** (plan §0.4 rule 10): absorb `p`
into `u`, or take `p ≡ 1`.
Source: `run2/work/edt-node-value.md` §2 versus `udt-policy-calc` (`Separable`)
Kind: L
Fidelity: exact
Hyps: none -/
theorem separable_iff_weighted (U : Policy S A → ℝ) :
    Separable U ↔ ∃ (p : S → ℝ) (u : S → A → ℝ), SeparableW U p u := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨fun _ => 1, u, fun π => by simp [hu π]⟩
  · rintro ⟨p, u, h⟩
    exact separable_of_weighted p u h

/-- **The EDT node value through a self-prediction kernel**: `vNode U κ s a := U (κ s a)` — the
utility of the whole policy the agent expects to be running given "reach `s`, play `a`".
Source: `run2/work/edt-node-value.md` §1 (trust-lab-029); red-team §E1
Kind: D
Fidelity: exact
Hyps: n/a -/
def vNode (U : Policy S A → ℝ) (κ : S → A → Policy S A) (s : S) (a : A) : ℝ := U (κ s a)

/-- **Decoupled kernels**: `κ s a = update (base s) s a` — a fixed off-`s` prediction `base s`,
independent of the local action ("reach `s` and the local action do not couple to actions
elsewhere").
Source: `run2/work/edt-node-value.md` §2 (trust-lab-029)
Kind: D
Fidelity: exact
Hyps: n/a -/
def Decoupled (κ : S → A → Policy S A) (base : S → Policy S A) : Prop :=
  ∀ s a, κ s a = Function.update (base s) s a

/-- **An EDT-argmax assembly**: a policy that at every node plays an argmax of the EDT node value
(the diagonal assembly of the informed self's local choices; ties allowed).
Source: `run2/work/edt-node-value.md` §2 (`hEDT`); [[updateless-deference-model]] §1.2
Kind: D
Fidelity: exact (set-valued argmax)
Hyps: n/a -/
def EdtAssembly (U : Policy S A → ℝ) (κ : S → A → Policy S A) (π : Policy S A) : Prop :=
  ∀ s, IsArgmax (vNode U κ s) (π s)

/-- **The kernel decoupled at the policy itself**: at each node the EDT self predicts `π`
elsewhere (`selfKernel π s a = update π s a`). Every decoupled kernel with base `fun _ => π` is
this one; the mugging's `κsev` and Coordinated Buttons' `κcb` are its instances at `(0,0)` and
`(1,1)`.
Source: audit r1 B2 (the base is a free parameter)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def selfKernel (π : Policy S A) : S → A → Policy S A := fun s a => Function.update π s a

omit [Fintype S] in
/-- Supporting lemma: the self-kernel is decoupled with constant base `π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem selfKernel_decoupled (π : Policy S A) : Decoupled (selfKernel π) (fun _ => π) :=
  fun _ _ => rfl

omit [Fintype S] in
/-- **An EDT assembly through one's own decoupled kernel is a local optimum, definitionally**:
`EdtAssembly U (selfKernel π) π ↔ IsLocalOptimum U π` (`udt-policy-calc`'s local optimum: no
one-node change improves `U`). So T5's "updateful through a decoupled kernel" at base `π` is
T7's local-versus-global question in different words.
Source: audit r1 B2 | [[udt-policy-calc]] `IsLocalOptimum`
Kind: L
Fidelity: exact
Hyps: none -/
theorem edtAssembly_selfKernel_iff (U : Policy S A → ℝ) (π : Policy S A) :
    EdtAssembly U (selfKernel π) π ↔ IsLocalOptimum U π :=
  ⟨fun h s a => h s a, fun h s a => h s a⟩

omit [Fintype S] in
/-- **Every optimum of every `U` is an EDT assembly through its own decoupled kernel**: so for
*every* utility, coupled or not, there is a decoupled kernel whose updateful assembly is endorsed
(`IsOptimal`). "Updateful ⟹ not endorsed" is therefore false for every `U` with an optimum once
the kernel may be chosen; it can only be asked relative to a fixed base.
Source: audit r1 B2 (T5)
Kind: P
Fidelity: n/a (a structural fact about the kernel reading)
Hyps: (a) all -/
theorem edtAssembly_selfKernel_of_optimal (U : Policy S A → ℝ) {π : Policy S A}
    (h : IsOptimal U π) : EdtAssembly U (selfKernel π) π := by
  intro s a
  show U (Function.update π s a) ≤ U (Function.update π s (π s))
  rw [Function.update_eq_self]
  exact h _

/-- **T7(a), the `κ`-collapse lemma**: under weighted separability and decoupling,
`vNode U κ s a = p s · u s a + ∑_{t ≠ s} p t · u t (base s t)` — the `a`-dependence is carried
exactly by the local term and the off-`s` mass is the kernel's prediction, an `a`-constant.
Source: `run2/work/edt-node-value.md` §2 `vNode_decoupled_eq` (trust-lab-029)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem vNode_decoupled_eq {U : Policy S A → ℝ} {p : S → ℝ} {u : S → A → ℝ}
    (hU : SeparableW U p u) {κ : S → A → Policy S A} {base : S → Policy S A}
    (hκ : Decoupled κ base) (s : S) (a : A) :
    vNode U κ s a = p s * u s a + ∑ t ∈ univ.erase s, p t * u t (base s t) := by
  unfold vNode
  rw [hU, hκ, ← Finset.add_sum_erase _ _ (mem_univ s), Function.update_self]
  congr 1
  exact Finset.sum_congr rfl fun t ht => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]

/-- **T7(b): EDT assemblies are globally optimal in the decoupled separable regime** — any
policy that at each node plays an EDT-argmax through a decoupled kernel is `IsOptimal`. The local
`u`-argmax is derived from the EDT ranking via `vNode_decoupled_eq` (the common off-`s` mass
cancels), then the separable sum is dominated termwise. No sign condition on `p` is needed: the
EDT ranking transfers to `p s · u s` directly.
Source: `run2/work/edt-node-value.md` §2 `edt_decoupled_globally_optimal` (trust-lab-029/030)
Kind: P
Fidelity: exact (marginally stronger: `p ≥ 0` dropped, as the source's honest note anticipates)
Hyps: (a) all -/
theorem edt_decoupled_globally_optimal {U : Policy S A → ℝ} {p : S → ℝ} {u : S → A → ℝ}
    (hU : SeparableW U p u) {κ : S → A → Policy S A} {base : S → Policy S A}
    (hκ : Decoupled κ base) {πs : Policy S A} (hEDT : EdtAssembly U κ πs) : IsOptimal U πs := by
  intro π
  rw [hU π, hU πs]
  refine Finset.sum_le_sum fun s _ => ?_
  have h := hEDT s (π s)
  rw [vNode_decoupled_eq hU hκ, vNode_decoupled_eq hU hκ] at h
  linarith

/-- **The round-1 relation** `UDefers U v`: every assembly of per-node argmaxes of the local
valuation `v` is globally optimal for `U` (quantified over *every* argmax selection — the tie fix of
trust-lab-2-019(1)).
Source: trust-lab-028 (round 1, `UpdatelessDeference.lean`, not read); red-team §A–§B; 2-019(1)
Kind: D
Fidelity: variant: universal over argmax selections (the source's tie-break is unspecified)
Hyps: n/a -/
def UDefers (U : Policy S A → ℝ) (v : S → A → ℝ) : Prop :=
  ∀ choice : Policy S A, (∀ s, IsArgmax (v s) (choice s)) → IsOptimal U choice

/-- **The `∃`-selection variant**: *some* assembly of per-node argmaxes is globally optimal.
Source: trust-lab-2-019(1)
Kind: D
Fidelity: variant: existential over argmax selections
Hyps: n/a -/
def UDefersSome (U : Policy S A → ℝ) (v : S → A → ℝ) : Prop :=
  ∃ choice : Policy S A, (∀ s, IsArgmax (v s) (choice s)) ∧ IsOptimal U choice

omit [DecidableEq S] in
/-- **T7(d): the round-1 relation is a wrapper around argmax** — for separable `U` with
per-node rewards `u`, `UDefers U u` holds outright: an argmax of `u s` at each `s` dominates the
separable sum termwise. There is no second belief object in the statement (red-team §B).
Source: trust-lab-028; red-team §B ("Theorem R is a true tautology about argmax")
Kind: T
Fidelity: exact
Hyps: (a) none beyond the presentation `hU` -/
theorem udefers_of_separable {U : Policy S A → ℝ} {u : S → A → ℝ}
    (hU : ∀ π, U π = ∑ s, u s (π s)) : UDefers U u := by
  intro choice hc π
  rw [hU π, hU choice]
  exact Finset.sum_le_sum fun s _ => hc s (π s)

omit [Fintype S] [DecidableEq S] in
/-- Supporting lemma: `UDefers` implies `UDefersSome` when some argmax selection exists.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem udefersSome_of_udefers {U : Policy S A → ℝ} {v : S → A → ℝ} (h : UDefers U v)
    {choice : Policy S A} (hc : ∀ s, IsArgmax (v s) (choice s)) : UDefersSome U v :=
  ⟨choice, hc, h choice hc⟩

end General

/-! ### The coupled mugging (T7(c), T5(b), T10(b)) -/

section Mugging

/-- **The coupled mugging utility** on two nodes (`0` = self, `1` = the predicted copy; action
`1` = pay, `0` = refuse): `U π = (−100 if π 0 = pay) + (10000 if π 0 = pay ∧ π 1 = pay)`. The
`10000` fires only on the matched-pay diagonal (the acausal correlation). Values:
`(0,0) ↦ 0, (0,1) ↦ 0, (1,0) ↦ −100, (1,1) ↦ 9900`. Monetary framing throughout.
Source: `run2/work/edt-node-value.md` §4 (trust-lab-030)
Kind: D
Fidelity: exact
Hyps: n/a -/
def mugU : Policy (Fin 2) (Fin 2) → ℝ := tbl 0 0 (-100) 9900

/-- Supporting lemma: `mugU` in the source's `if`-form.
Source: `run2/work/edt-node-value.md` §4
Kind: L
Fidelity: exact
Hyps: none -/
theorem mugU_eq (π : Policy (Fin 2) (Fin 2)) :
    mugU π = (if π 0 = 1 then -100 else 0) + (if π 0 = 1 ∧ π 1 = 1 then 10000 else 0) := by
  revert π
  rw [forall_policy2]
  simp [mugU]
  norm_num

/-- **The mugging is not separable** (`CrossSituationDependence`): separability would force the
exchange identity `U(0,0) + U(1,1) = U(0,1) + U(1,0)`, i.e. `9900 = −100`.
Source: `run2/work/edt-node-value.md` §4 `not_separable`
Kind: N+ (component)
Fidelity: exact
Hyps: none -/
theorem mugU_not_separable : CrossSituationDependence mugU := by
  intro h
  have := h.exchange ![0, 0] ![1, 1]
  simp only [update_vec2_one, Matrix.cons_val_one, Matrix.cons_val_zero, mugU,
    tbl_00, tbl_11, tbl_01, tbl_10, Fin.isValue] at this
  norm_num at this

/-- **The severing kernel**: at each node the EDT self predicts the other node frozen at refuse.
Source: `run2/work/edt-node-value.md` §4
Kind: D
Fidelity: exact
Hyps: n/a -/
def κsev : Fin 2 → Fin 2 → Policy (Fin 2) (Fin 2) := fun s a => Function.update (fun _ => 0) s a

/-- Supporting lemma: `κsev` is decoupled at the all-refuse base.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem κsev_decoupled : Decoupled κsev fun _ _ => 0 := fun _ _ => rfl

/-- **The severing kernel is the self-kernel of refusal**: `κsev = selfKernel (0, 0)`.
Source: audit r1 B2
Kind: L
Fidelity: exact
Hyps: none -/
theorem κsev_eq_selfKernel : κsev = selfKernel ![0, 0] := by
  have h : (fun _ : Fin 2 => (0 : Fin 2)) = ![0, 0] := by
    funext i; fin_cases i <;> rfl
  funext s a
  show Function.update (fun _ => 0) s a = Function.update ![0, 0] s a
  rw [h]

/-- **The kernel is inside the value** (`rfl`): `vNode mugU κsev 0 1 = mugU (update (const 0) 0 1)`.
Source: `run2/work/edt-node-value.md` §3 `vNode_via_kappa`
Kind: T
Fidelity: exact
Hyps: none -/
theorem vNode_via_kappa : vNode mugU κsev 0 1 = mugU (Function.update (fun _ => 0) 0 1) := rfl

/-- Supporting lemma: the four node values through `κsev`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem vNode_κsev_values :
    vNode mugU κsev 0 0 = 0 ∧ vNode mugU κsev 0 1 = -100 ∧
      vNode mugU κsev 1 0 = 0 ∧ vNode mugU κsev 1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · show mugU (Function.update (fun _ => (0 : Fin 2)) _ _) = _
    rw [policy2_eq (fun _ => (0 : Fin 2))]
    simp [mugU]

/-- **Refusing is the EDT argmax at both nodes under the severing kernel** (strictly at node `0`,
tied at node `1`).
Source: `run2/work/edt-node-value.md` §4 `edt_argmax_is_refuse_s0/s1`
Kind: N+ (component)
Fidelity: exact
Hyps: none -/
theorem mug_edt_argmax_refuse : EdtAssembly mugU κsev ![0, 0] := by
  obtain ⟨h00, h01, h10, h11⟩ := vNode_κsev_values
  simp only [EdtAssembly, IsArgmax, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    h00, h01, h10, h11]
  norm_num

/-- **Every EDT assembly through `κsev` refuses at node `0`** (the strict node), hence scores `0`.
Source: `run2/work/edt-node-value.md` §4 (`edtPolicy_is_edt_argmax`, generalized to all assemblies)
Kind: P
Fidelity: stronger: over every argmax selection, not the source's fixed `edtPolicy`
Hyps: (a) all -/
theorem mug_edt_assembly_value {π : Policy (Fin 2) (Fin 2)} (h : EdtAssembly mugU κsev π) :
    mugU π = 0 := by
  obtain ⟨h00, h01, _, _⟩ := vNode_κsev_values
  have h0 : π 0 = 0 := by
    by_contra hne
    have h1 : π 0 = 1 := by omega
    have := h 0 0
    rw [h1, h00, h01] at this
    norm_num at this
  rw [mugU_eq, h0]
  simp

/-- **`(pay, pay)` is the unrestricted optimum**: `9900` beats `0, 0, −100`.
Source: `run2/work/edt-node-value.md` §4 `global_opt_dominates_all`
Kind: N+ (component)
Fidelity: exact
Hyps: none -/
theorem mug_optimal : IsOptimal mugU ![1, 1] := by
  rw [IsOptimal, forall_policy2]
  simp only [mugU, tbl_00, tbl_01, tbl_10, tbl_11]
  norm_num

/-- **T7(c), the mugging near-miss**: every EDT assembly through the severing kernel scores `0`,
strictly below the unrestricted optimum `9900`; the gap is `9900` and the severed matched-pay
reward is `10000` (`U(pay,pay) − vNode 0 pay`).
Source: `run2/work/edt-node-value.md` §4 `mugging_edt_misses`, `gap_is_acausal_payoff` (trust-lab-030)
Kind: N+
Fidelity: exact (non-separable `U`, decoupled non-inert `κ`, all argmax selections)
Hyps: none -/
theorem mugging_edt_misses :
    CrossSituationDependence mugU ∧ EdtAssembly mugU κsev ![0, 0] ∧ IsOptimal mugU ![1, 1] ∧
      (∀ π, EdtAssembly mugU κsev π → mugU π < mugU ![1, 1] ∧ mugU ![1, 1] - mugU π = 9900) ∧
      mugU ![1, 1] - vNode mugU κsev 0 1 = 10000 := by
  refine ⟨mugU_not_separable, mug_edt_argmax_refuse, mug_optimal, fun π h => ?_, ?_⟩
  · rw [mug_edt_assembly_value h]
    simp [mugU]
  · rw [vNode_κsev_values.2.1]
    simp [mugU]
    norm_num

/-- **The correlated kernel**: the copy does what I do (`κcorr s a = const a`).
Source: `run2/work/edt-node-value.md` §4
Kind: D
Fidelity: exact
Hyps: n/a -/
def κcorr : Fin 2 → Fin 2 → Policy (Fin 2) (Fin 2) := fun _ a _ => a

/-- **With the correlated kernel, paying is the strict EDT argmax at both nodes and the EDT
assembly is the optimum**: the divergence is caused precisely by `κsev`'s severance — `κ` is
load-bearing, not inert (two kernels, two answers, same `U`).
Source: `run2/work/edt-node-value.md` §4 `correlated_kappa_agrees`
Kind: N+ (component)
Fidelity: exact
Hyps: none -/
theorem correlated_kappa_agrees :
    (∀ s, IsStrictArgmax (vNode mugU κcorr s) 1) ∧ EdtAssembly mugU κcorr ![1, 1] := by
  have hv : ∀ s a, vNode mugU κcorr s a = mugU ![a, a] := fun s a => by
    show mugU (fun _ => a) = _
    rw [policy2_eq (fun _ => a)]
  constructor
  · intro s a ha
    have h1 : a = 0 := by omega
    subst h1
    rw [hv, hv]
    norm_num [mugU]
  · simp only [EdtAssembly, IsArgmax, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      hv]
    norm_num [mugU]

/-- **Separability is load-bearing in T7(b)**: dropping `SeparableW`, the conclusion is false —
the mugging with the decoupled `κsev` has the EDT assembly `(refuse, refuse)` that is not optimal.
Source: `run2/work/edt-node-value.md` §4 `separability_load_bearing` (trust-lab-030)
Kind: N+
Fidelity: exact (the "weaker hypothesis ⇒ FALSE" form)
Hyps: none -/
theorem separability_load_bearing :
    ¬ ∀ (U : Policy (Fin 2) (Fin 2) → ℝ) (κ : Fin 2 → Fin 2 → Policy (Fin 2) (Fin 2))
        (base : Fin 2 → Policy (Fin 2) (Fin 2)), Decoupled κ base →
        ∀ πs, EdtAssembly U κ πs → IsOptimal U πs := by
  intro h
  have := h mugU κsev (fun _ _ => 0) κsev_decoupled ![0, 0] mug_edt_argmax_refuse ![1, 1]
  simp only [mugU, tbl_00, tbl_11] at this
  norm_num at this

/-! #### T7(d): ties make the round-1 relation selection-dependent -/

/-- A local valuation with a tie at node `0` and a strict preference for `1` at node `1`.
Source: trust-lab-2-019(1) (the tie witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def vTie : Fin 2 → Fin 2 → ℝ := ![![0, 0], ![0, 1]]

/-- **T7(d), the tie witness (N+)**: for Coordinated Buttons and `vTie`, some argmax assembly
(`(1, 1)`) is optimal while another (`(0, 1)`) is not — `UDefersSome` holds and `UDefers` fails.
The round-1 relation is order-dependent unless the quantifier over selections is fixed.
Source: trust-lab-2-019(1); red-team §E3
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem udefers_tie_witness : UDefersSome coordButtons vTie ∧ ¬ UDefers coordButtons vTie := by
  have hargmax : ∀ b : Fin 2, ∀ s, IsArgmax (vTie s) (![b, 1] s) := by
    intro b s a
    fin_cases s <;> fin_cases a <;> fin_cases b <;> simp [vTie]
  constructor
  · refine ⟨![1, 1], hargmax 1, ?_⟩
    rw [IsOptimal, forall_policy2]
    simp only [coordButtons, tbl_00, tbl_01, tbl_10, tbl_11]
    norm_num
  · intro h
    have := h ![0, 1] (hargmax 0) ![1, 1]
    simp only [coordButtons, tbl_01, tbl_11] at this
    norm_num at this

/-- **The mugging with base `(pay, pay)` gives the endorsed certificate** (N+ component for
T5): coupled `U`, decoupled kernel (`selfKernel (1,1)`), strict EDT argmax `pay` at both nodes,
and the assembly `(pay, pay)` optimal — the same four-part certificate as
`coordButtons_assembly_optimal`, on the utility whose base-`(0,0)` kernel `κsev` makes the EDT
assembly *miss* (`mugging_edt_misses`). One coupled `U`, two bases, both behaviours.
Source: audit r1 B2 (T5)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem mugging_pay_base :
    CrossSituationDependence mugU ∧ Decoupled (selfKernel ![1, 1]) (fun _ => ![1, 1]) ∧
      (∀ s, IsStrictArgmax (vNode mugU (selfKernel ![1, 1]) s) 1) ∧ IsOptimal mugU ![1, 1] := by
  refine ⟨mugU_not_separable, selfKernel_decoupled _, fun s a ha => ?_, mug_optimal⟩
  have h1 : a = 0 := by omega
  subst h1
  fin_cases s <;>
  · show mugU (Function.update ![1, 1] _ 0) < mugU (Function.update ![1, 1] _ 1)
    simp [mugU] <;> norm_num

end Mugging

/-! ### T5: "updatelessness boosts endorsed agency" — the "exactly" is false -/

section CoordButtons

/-- **Coordinated Buttons is optimal at `(1, 1)`** (`10` beats `5, 0, 0`).
Source: [[udt-policy-calc]] `coordButtons` (mandate T5(c))
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem coordButtons_optimal_one : IsOptimal coordButtons ![1, 1] := by
  rw [IsOptimal, forall_policy2]
  simp only [coordButtons, tbl_00, tbl_01, tbl_10, tbl_11]
  norm_num

/-- The kernel decoupled at the base `(1, 1)`: each copy predicts the other presses `1`.
Source: mandate T5(c)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def κcb : Fin 2 → Fin 2 → Policy (Fin 2) (Fin 2) := fun s a => Function.update ![1, 1] s a

/-- Supporting lemma: `κcb` is decoupled.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem κcb_decoupled : Decoupled κcb fun _ => ![1, 1] := fun _ _ => rfl

/-- **`κcb` is the self-kernel of `(1, 1)`.**
Source: audit r1 B2
Kind: L
Fidelity: exact
Hyps: none -/
theorem κcb_eq_selfKernel : κcb = selfKernel ![1, 1] := rfl

/-- **Coordinated Buttons with base `(0, 0)` gives the unendorsed certificate** (N+ component
for T5): decoupled kernel (`selfKernel (0,0)`), the EDT assembly `(0, 0)` (a local optimum,
`coordButtons_localOptimum`), not optimal (`5 < 10`) — the mugging's failure certificate on the
utility of `coordButtons_assembly_optimal`.
Source: audit r1 B2 (T5)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem coordButtons_refuse_base :
    Decoupled (selfKernel ![0, 0]) (fun _ => ![0, 0]) ∧
      EdtAssembly coordButtons (selfKernel ![0, 0]) ![0, 0] ∧ ¬ IsOptimal coordButtons ![0, 0] :=
  ⟨selfKernel_decoupled _, (edtAssembly_selfKernel_iff _ _).2 coordButtons_localOptimum,
    coordButtons_not_optimal⟩

/-- **T5(c): Coordinated Buttons at base `(1, 1)`** — a non-separable `U` with a decoupled kernel
through which the per-node EDT assembly is strictly ranked and optimal. **Graded N−** (repair
round 1, audit r1 B2): the certificate is generic in the base and independent of `U` — `κcb` is
`selfKernel (1,1)`, and every optimum of every utility is an EDT assembly through its own
self-kernel (`edtAssembly_selfKernel_of_optimal`); the mugging gives the identical certificate at
base `(pay, pay)` (`mugging_pay_base`), and Coordinated Buttons gives the mugging's failure
certificate at base `(0, 0)` (`coordButtons_refuse_base`). So this instance does not exercise
anything about Coordinated Buttons; it exhibits the base-dependence. What survives of T5 under
the kernel reading ("updateful" = an EDT assembly through a decoupled kernel, "endorsed" =
`IsOptimal`): separable ⟹ every assembly through every decoupled kernel is endorsed
(`edt_decoupled_globally_optimal`); for a coupled `U` the answer depends on the base, and
udt-rep-2-016's "true exactly under cross-situation dependence" (the surveyor's reading,
ATTRIBUTION-UNVETTED) is ill-posed until the base is fixed — with base = an optimum it fails for
every `U`, with base = a non-global local optimum it holds for every `U` that has one.
Source: [[meaning-and-agency-reference]] §Updatelessness | udt-rep-2-016 (mandate T5(c))
Kind: N−
Fidelity: n/a (non-separable `U`, strict EDT ranking at both nodes — but generic in the base, see above)
Hyps: none -/
theorem coordButtons_assembly_optimal :
    CrossSituationDependence coordButtons ∧ Decoupled κcb (fun _ => ![1, 1]) ∧
      (∀ s, IsStrictArgmax (vNode coordButtons κcb s) 1) ∧ IsOptimal coordButtons ![1, 1] := by
  refine ⟨coordButtons_not_separable, κcb_decoupled, fun s a ha => ?_, coordButtons_optimal_one⟩
  have h1 : a = 0 := by omega
  subst h1
  fin_cases s <;>
  · show coordButtons (Function.update ![1, 1] _ 0) < coordButtons (Function.update ![1, 1] _ 1)
    simp [coordButtons]

end CoordButtons

/-! ### T10: Geometric UDT as the separable/coupled decomposition -/

section Geometric

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]

/-- **T10(a), the Geometric-UDT identity on a separable coordinate**:
`max_π ∑_s p s · u s (π s) = ∑_s max_a (p s · u s a)` — `udt-policy-calc`'s
`sup'_eq_sum_sup'_of_separable` with the weight absorbed (Idea C's "PROVED" boundary half; the
source's own red-team calls it trivial). With `p s ≥ 0` the factor `p s` pulls out of the inner
max, which is the displayed form.
Source: [[updateless-deference-ideate]] §3 Idea C (trust-lab-2-015); `AGENDA.md` line 90
Kind: T
Fidelity: exact (weights absorbed)
Hyps: (a) none beyond the presentation -/
theorem geometric_udt_identity {U : Policy S A → ℝ} {p : S → ℝ} {u : S → A → ℝ}
    (hU : SeparableW U p u) :
    univ.sup' univ_nonempty U = ∑ s, univ.sup' univ_nonempty (fun a => p s * u s a) :=
  sup'_eq_sum_sup'_of_separable (fun s a => p s * u s a) U hU

end Geometric

/-- **T10(b), the values-coin witness**: the same mugging instance read with the branch index as a
*values* fact — node `0` is the copy that learns "aggregation rule `0` is correct", node `1` the copy
that learns "rule `1` is correct", and the payoff `10000` is available only if both copies act
alike (a population-ethics-style coupling across the copies' value verdicts). The values-updateful
policy (each copy acting on its own verdict through the severing kernel) is the EDT assembly and
loses `9900`. So "values are separable" is not a property of subject matter: a values fact can
couple copies exactly as an empirical one can, and whether a coordinate is flat is the coupling
graph's question (T9), not the coordinate's label.
Source: [[updateless-deference-ideate]] §3 Idea C; trust-lab-027 (`𝒳_val`/`𝒳_fact`); `AGENDA.md` line 90 (mandate T10(b))
Kind: N+
Fidelity: n/a (the same Lean instance as `mugging_edt_misses`, under the values reading; ATTRIBUTION-UNVETTED that this is the coupling Abram's sentence excludes)
Hyps: none -/
theorem values_coin :
    CrossSituationDependence mugU ∧ (∀ π, EdtAssembly mugU κsev π → mugU ![1, 1] - mugU π = 9900) :=
  ⟨mugging_edt_misses.1, fun π h => (mugging_edt_misses.2.2.2.1 π h).2⟩

end

end Cleanroom.Udt.UdtEndorsePolicy
