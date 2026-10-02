import Cleanroom.Decision.DpCausalConsist.Collapse

/-!
# `dp-causal-consist`: `CDT_π`, `T_OCC`, the restated corollary (T5) and the evidential half of T6

* `edt_nonResponsive_preQuery` (T6(b)): at a recorded point under clause 1, the act-conditional
  `P_{s_d}(· | a)` agrees with `P_{s_d}` on every pre-query event — Lemma 3′ read as
  non-responsiveness of conditioning on `⟨V₀⟩`. With Pearl's invariance (`Truncate.lean`) the
  property is *shared* on `𝓔₀^G ∩ ⟨V₀⟩` and separates nothing there; its content is the choice of
  the fixed algebra (a docstring sentence, not a theorem).
* `CDTpi` (Definition 26): the causal argmax over all of `A_d` of the Jeffrey mixture of the
  interventional suppositions `cf^{Γ_i}(a)` under a finite prior `π` — a plain `def`, as
  `dp-referents-cdt` needs.
* `TOCCAt` (Definition 25): the counterfactual component *is* such a mixture, over structures for
  `P_{s_d}`; an epistemology (it reads only the state, never `ν`).
* `mixState_cfG_V_eq_V`: under Theorem 3(ii)'s hypotheses for every `Γ_i` ("temporal `π`"), the
  mixed supposed value of every positive act is its evidential value.
* `cdtpi_inter_aPlus_subset_argmaxPlus`, `cdtpi_inter_aPlus_eq_argmaxPlus`, `tcdt_mix_iff_tedt`: the
  **restated corollary** — `CDT_π ∩ A_d^+ ⊆ argmax_{A_d^+}`, with equality (and `T_CDT ↔ T_EDT`)
  exactly under the proviso that the causal argmax meets `A_d^+`; the `⊇` direction can fail at
  null acts (`tcdt_not_tedt_of_null_argmax`).
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Decision.DpCalibration
  FactoredSpaces Finset

section edt

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
  [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  {C : Proc ι acts ℚ} {B : Tree Ω ι acts ℚ} {d : ι}

/-- **Conditioning on the act is non-responsive on the pre-query algebra at a recorded point**:
`P_{s_d}(X | a) = P_{s_d}(X)` for every pre-query `X` and every `a ∈ A_d^+`.
Source: [[learning-cdt-renderings]] "Non-responsiveness: form, not content" ("so is the
evidential conditional on the pre-query algebra at every recorded point — that is Lemma 3′");
mandate T6(b) (`edt_nonResponsive_preQuery`)
Kind: C
Fidelity: exact
Hyps: (a) recording; (a) `0 < ν(O_d)`; (a) clause 1; (a) `X` pre-query; (a) `0 < P_{s_d}(a)` -/
theorem edt_nonResponsive_preQuery (s : ι → State Ω ℚ) (hrec : RecordsFor obs actEv C B d)
    (hO : 0 < nu C B (obs d)) (h1 : StrictClause1At s obs C B d) {X : Finset Ω}
    (hX : PreQuery obs C B d X) (a : acts d) (ha : 0 < (s d).pr (actEv d a)) :
    (jeffreyCond (s d) (actEv d a) ha).pr X = (s d).pr X := by
  rw [jeffreyCond_pr, pr_inter_eq_mul_of_recordsFor obs actEv s hrec hO h1 hX a, mul_div_assoc,
    div_self ha.ne', mul_one]

end edt

section cdtpi

variable {V : Type} [Fintype V] [DecidableEq V] {Val : V → Type} [∀ v, Fintype (Val v)]
  [∀ v, DecidableEq (Val v)] [∀ v, Nonempty (Val v)]

/-- **`CDT_π` (Definition 26)**: the acts maximising the Jeffrey mixture, under the finite prior
`π`, of the interventional suppositions `cf^{Γ_i}(a)` — the argmax over **all** of `A_d`.
Source: [[learning-cdt-renderings]] Definition 26 ("`CDT_π(d) := argmax_a V^{π,a}_{s_d}(a)`");
mandate T5 (`CDTpi`, "a plain `def` on a state and a mixture")
Kind: D
Fidelity: variant: finite support of `π` (mandate §3.5) -/
noncomputable def CDTpi {A : Type} [Fintype A] [DecidableEq A] {n : ℕ} (π : FinDistr ℝ (Fin n))
    (Γ : Fin n → CausalStructure Val) (m : V) (u : Pt Val → ℝ) (e : A → Val m)
    (actEv : A → Finset (Pt Val)) : Finset A :=
  argmaxAll fun a => (mixState π fun i => cfG (Γ i) m u (e a)).V (actEv a)

/-- **Observational causal consistency at a point (Definition 25)**: the counterfactual component
is a finite mixture of interventional suppositions of structures for `P_{s}` — reading only the
state, never `ν` (an epistemology, Definition 19).
Source: [[learning-cdt-renderings]] Definition 25 ("there is a probability `π_d` over causal
structures for `s_d` with `cf_{s_d} = ∫ cf^G_{s_d} dπ_d(G)`"); mandate T5 (`TOCCAt`)
Kind: D
Fidelity: variant: finite support; latent-free structures (mandate §3.5); the payoff `u` is a
parameter of the definition (it reads no `ν`) — under strict clause 2 with a supervenient payoff
`u(x) = V_{s_d}{x}` on `supp P_{s_d}` (`V_eq_condExp_of_strict` at singletons), so `u` is
state-determined on the support and an external input only at `P_{s_d}`-null worlds (audit r1 N6) -/
def TOCCAt {A : Type} (t : CfState (Pt Val) ℝ) (m : V) (u : Pt Val → ℝ) (e : A → Val m)
    (actEv : A → Finset (Pt Val)) : Prop :=
  ∃ (n : ℕ) (π : FinDistr ℝ (Fin n)) (Γ : Fin n → CausalStructure Val),
    (∀ i, (Γ i).IsFor (State.toDistr t.s)) ∧
    ∀ a (h : (actEv a).Nonempty), t.cf (actEv a) h = mixState π fun i => cfG (Γ i) m u (e a)

variable {ι : Type} [DecidableEq ι] {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  (obs : ι → Finset (Pt Val)) (actEv : (d : ι) → acts d → Finset (Pt Val))
  {C : Proc ι acts ℚ} {B : Tree (Pt Val) ι acts ℚ} {d : ι}

/-- **The mixed supposed value of a positive act is its evidential value** under Theorem 3(ii)'s
hypotheses for every structure in the support of `π` (a temporal prior).
Source: [[learning-cdt-renderings]] "Corollary 3.1 restated" ("for every temporal `π`");
mandate T5 (restated corollary)
Kind: C
Hyps: as `thm3_ii` for every `Γ i`; (a) `r = u ∘ λ`; (a) `a ∈ A_d^+` -/
theorem mixState_cfG_V_eq_V (s : ι → State (Pt Val) ℚ) (hrec : RecordsFor obs actEv C B d)
    (hO : 0 < nu C B (obs d)) (hs : StrictClausesAt s obs C B d) (m : V) (e : acts d → Val m)
    (hact : ∀ a, actEv d a = actEvCoord m (e a)) {n : ℕ} (π : FinDistr ℝ (Fin n))
    (Γ : Fin n → CausalStructure Val)
    (hΓ : ∀ i, (Γ i).IsFor (State.toDistr (State.castℝ (s d))))
    (hpa : ∀ i c, PreQuery obs C B d (parentCell (Γ i) m c)) (u : Pt Val → ℚ)
    (hu : ∀ ℓ, payoff B ℓ = u (world B ℓ)) (a : acts d) (ha : a ∈ APlus s actEv d) :
    (mixState π fun i => cfG (Γ i) m (fun x => (u x : ℝ)) (e a)).V (actEv d a)
      = ((s d).V (actEv d a) : ℝ) := by
  rw [mixState_V_of_suppRegular π (fun i => cfG (Γ i) m (fun x => (u x : ℝ)) (e a))
    (fun i => by unfold cfG; exact expState_suppRegular _ _)]
  have hpr : ∀ i, (cfG (Γ i) m (fun x => (u x : ℝ)) (e a)).pr (actEv d a) = 1 := by
    intro i; rw [hact a]; exact cfG_success _ _ _ _
  have hV : ∀ i, (cfG (Γ i) m (fun x => (u x : ℝ)) (e a)).V (actEv d a) = ((s d).V (actEv d a) : ℝ) :=
    fun i => cfG_V_eq_V_of_recordsFor obs actEv s hrec hO hs m e hact (Γ i) (hΓ i) (hpa i) u hu a ha
  simp_rw [hpr, hV, mul_one]
  rw [← Finset.sum_mul, π.sum_one, one_mul, div_one]

/-- The general argmax transfer: if a value `v` agrees with `V_{s_d}` on `A_d^+`, then on `A_d^+`
membership in `argmax_{A_d} v` implies membership in `argmax_{A_d^+} V_{s_d}`, and the converse
holds whenever some element of `A_d^+` is in `argmax_{A_d} v`.
Source: [[learning-cdt-renderings]] Theorem 3(iv), "Corollary 3.1 restated"
Kind: L -/
theorem argmax_transfer (s : ι → State (Pt Val) ℚ) (v : acts d → ℝ)
    (hagree : ∀ a ∈ APlus s actEv d, v a = ((s d).V (actEv d a) : ℝ)) :
    (∀ a ∈ APlus s actEv d, a ∈ argmaxAll v → a ∈ argmaxPlus s actEv d) ∧
    ((argmaxAll v ∩ APlus s actEv d).Nonempty →
      ∀ a ∈ APlus s actEv d, a ∈ argmaxPlus s actEv d → a ∈ argmaxAll v) := by
  constructor
  · intro a ha h
    rw [mem_argmaxAll] at h
    rw [mem_argmaxPlus]
    refine ⟨ha, fun b hb => ?_⟩
    have := h b
    rw [hagree a ha, hagree b hb] at this
    exact_mod_cast this
  · rintro ⟨a₀, ha₀⟩ a ha h
    rw [Finset.mem_inter, mem_argmaxAll] at ha₀
    rw [mem_argmaxPlus] at h
    rw [mem_argmaxAll]
    intro b
    have h1 : v a₀ ≤ v a := by
      rw [hagree a ha, hagree a₀ ha₀.2]
      exact_mod_cast h.2 a₀ ha₀.2
    exact (ha₀.1 b).trans h1

/-- **The restated corollary, one direction**: `CDT_π ∩ A_d^+ ⊆ argmax_{A_d^+} V_{s_d}` for a temporal
prior at a recorded point under strict calibration.
Source: [[learning-cdt-renderings]] "Corollary 3.1 restated" ("`CDT_π` and EDT approve the same
labels on positive-probability acts … for every temporal `π`"); mandate T5
Kind: C
Hyps: as `mixState_cfG_V_eq_V` -/
theorem cdtpi_inter_aPlus_subset_argmaxPlus (s : ι → State (Pt Val) ℚ)
    (hrec : RecordsFor obs actEv C B d) (hO : 0 < nu C B (obs d))
    (hs : StrictClausesAt s obs C B d) (m : V) (e : acts d → Val m)
    (hact : ∀ a, actEv d a = actEvCoord m (e a)) {n : ℕ} (π : FinDistr ℝ (Fin n))
    (Γ : Fin n → CausalStructure Val)
    (hΓ : ∀ i, (Γ i).IsFor (State.toDistr (State.castℝ (s d))))
    (hpa : ∀ i c, PreQuery obs C B d (parentCell (Γ i) m c)) (u : Pt Val → ℚ)
    (hu : ∀ ℓ, payoff B ℓ = u (world B ℓ)) :
    CDTpi π Γ m (fun x => (u x : ℝ)) e (actEv d) ∩ APlus s actEv d ⊆ argmaxPlus s actEv d := by
  intro a ha
  rw [Finset.mem_inter] at ha
  exact (argmax_transfer actEv s _ (fun a ha =>
    mixState_cfG_V_eq_V obs actEv s hrec hO hs m e hact π Γ hΓ hpa u hu a ha)).1 a ha.2 ha.1

/-- **The restated corollary under the proviso**: if `CDT_π` meets `A_d^+`, then
`CDT_π ∩ A_d^+ = argmax_{A_d^+} V_{s_d}` — CDT`_π` and EDT approve the same positive acts.
Source: [[learning-cdt-renderings]] "Corollary 3.1 restated"; Theorem 3(iv)'s proviso; mandate T5
Kind: C
Hyps: as `mixState_cfG_V_eq_V`; (a) the proviso -/
theorem cdtpi_inter_aPlus_eq_argmaxPlus (s : ι → State (Pt Val) ℚ)
    (hrec : RecordsFor obs actEv C B d) (hO : 0 < nu C B (obs d))
    (hs : StrictClausesAt s obs C B d) (m : V) (e : acts d → Val m)
    (hact : ∀ a, actEv d a = actEvCoord m (e a)) {n : ℕ} (π : FinDistr ℝ (Fin n))
    (Γ : Fin n → CausalStructure Val)
    (hΓ : ∀ i, (Γ i).IsFor (State.toDistr (State.castℝ (s d))))
    (hpa : ∀ i c, PreQuery obs C B d (parentCell (Γ i) m c)) (u : Pt Val → ℚ)
    (hu : ∀ ℓ, payoff B ℓ = u (world B ℓ))
    (hprov : (CDTpi π Γ m (fun x => (u x : ℝ)) e (actEv d) ∩ APlus s actEv d).Nonempty) :
    CDTpi π Γ m (fun x => (u x : ℝ)) e (actEv d) ∩ APlus s actEv d = argmaxPlus s actEv d := by
  have ht := argmax_transfer actEv s
    (fun a => (mixState π fun i => cfG (Γ i) m (fun x => (u x : ℝ)) (e a)).V (actEv d a))
    (fun a ha => mixState_cfG_V_eq_V obs actEv s hrec hO hs m e hact π Γ hΓ hpa u hu a ha)
  ext a
  constructor
  · intro ha
    rw [Finset.mem_inter] at ha
    exact ht.1 a ha.2 ha.1
  · intro ha
    have haP : a ∈ APlus s actEv d := (mem_argmaxPlus s actEv d a).mp ha |>.1
    exact Finset.mem_inter.mpr ⟨ht.2 hprov a haP ha, haP⟩

/-- **`T_CDT` for the mixture `↔ T_EDT`** under the proviso.
Source: [[learning-cdt-renderings]] "Corollary 3.1 restated" ("hence `TCdtAt`-for-the-mixture
`↔ TEdtAt` under T2(iv)'s proviso"); mandate T5
Kind: C
Hyps: as `cdtpi_inter_aPlus_eq_argmaxPlus` -/
theorem tcdt_mix_iff_tedt (s : ι → State (Pt Val) ℚ) (hrec : RecordsFor obs actEv C B d)
    (hO : 0 < nu C B (obs d)) (hs : StrictClausesAt s obs C B d) (m : V) (e : acts d → Val m)
    (hact : ∀ a, actEv d a = actEvCoord m (e a)) {n : ℕ} (π : FinDistr ℝ (Fin n))
    (Γ : Fin n → CausalStructure Val)
    (hΓ : ∀ i, (Γ i).IsFor (State.toDistr (State.castℝ (s d))))
    (hpa : ∀ i c, PreQuery obs C B d (parentCell (Γ i) m c)) (u : Pt Val → ℚ)
    (hu : ∀ ℓ, payoff B ℓ = u (world B ℓ))
    (hprov : (CDTpi π Γ m (fun x => (u x : ℝ)) e (actEv d) ∩ APlus s actEv d).Nonempty) :
    TCdtAt s actEv C d (fun a => mixState π fun i => cfG (Γ i) m (fun x => (u x : ℝ)) (e a))
      ↔ TEdtAt s actEv C d := by
  have heq := cdtpi_inter_aPlus_eq_argmaxPlus obs actEv s hrec hO hs m e hact π Γ hΓ hpa u hu hprov
  have hst : SelfTransparent s actEv C d :=
    selfTransparent_of_recordsFor_strict obs actEv C B s hrec hO (fun _ => hs)
  have hplay : ∀ a, 0 < (C d).w a → a ∈ APlus s actEv d := by
    intro a ha
    rw [APlus, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hst a]; exact ha⟩
  unfold TCdtAt TEdtAt
  constructor
  · intro h hne a ha
    have := h hne a ha
    rw [← heq, Finset.mem_inter]
    exact ⟨this, hplay a ha⟩
  · intro h hne a ha
    have := h hne a ha
    rw [← heq, Finset.mem_inter] at this
    exact this.1

end cdtpi

end Cleanroom.Decision.DpCausalConsist
