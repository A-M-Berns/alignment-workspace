import Cleanroom.Udt.UdtCommTrust.Structure

/-!
# `Cleanroom.Udt.UdtCommTrust.Determination`: decision-determination and its consequences

Work package `udt-comm-trust`, targets T5(a)–(c) (the definition of record, the deterministic
reading, `DynamicsCI`), T6 (DD ⟹ the expected utility factors through the external policy) and
T7 (the decomposition over external policies needs `Π* ⊑ D_{I,B}`). Sources:
[[communication-trust-translated]] lines 381–392 and 463–466; [[topics/decision-determination]]
lines 7–19; [[ibe-connection]] lines 80–81.
-/

namespace Cleanroom.Udt.UdtCommTrust

namespace AbstractDS

open Cleanroom.Udt.UdtPolicyCalc Finset

variable {Ω OI OE AI AE DI DE DB OH OC : Type}
variable [Fintype Ω] [DecidableEq Ω] [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE]
  [Fintype DE] [DecidableEq DE] [Fintype DI] [DecidableEq DI] [Fintype DB] [DecidableEq DB]
variable (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)

/-! ### Events of record -/

/-- The event `{E = e}`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def evE (e : AE × DE) : Finset Ω := event fun ω => S.E ω = e

/-- The event `{D_{I,B} = d}`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def evDIB (d : DI × DB) : Finset Ω := event fun ω => S.DIB ω = d

/-- The event `{Π̈ = π̈}`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def evPolE (π : OE → AE) : Finset Ω := event fun ω => S.polE ω = π

/-- Supporting lemma `mem_evDIB`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mem_evDIB {d : DI × DB} {ω : Ω} : ω ∈ S.evDIB d ↔ S.DIB ω = d := by simp [evDIB]

/-- Supporting lemma `mem_evPolE`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mem_evPolE {π : OE → AE} {ω : Ω} : ω ∈ S.evPolE π ↔ S.polE ω = π := by
  simp [evPolE]

/-- Supporting lemma `mem_evE`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mem_evE {e : AE × DE} {ω : Ω} : ω ∈ S.evE e ↔ S.E ω = e := by simp [evE]

/-- Supporting lemma `evDIB_subset_evPolE`: the `D_{I,B}`-atom of `d` lies in `{Π̈ = [[d]]_Π̈}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evDIB_subset_evPolE (d : DI × DB) : S.evDIB d ⊆ S.evPolE (S.polOf d) := by
  intro ω hω
  rw [mem_evDIB] at hω
  rw [mem_evPolE, polE_eq, hω]

/-- Supporting lemma `mass_eq_sum_fiber`: the mass of an event is the sum of the masses of its
fibres under `Z`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_eq_sum_fiber {K : Type} [Fintype K] [DecidableEq K] (w : Ω → ℝ) (P : Ω → Prop)
    [DecidablePred P] (Z : Ω → K) :
    mass w (event P) = ∑ z, mass w (event fun ω => P ω ∧ Z ω = z) := by
  rw [mass, ← Finset.sum_fiberwise (event P) Z]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [mass]
  congr 1
  ext ω
  simp

/-! ### T5(a): the definition of record -/

/-- **Decision-determination** (the C&T definition of record): (1) `U` is a function of `E`;
(2) `E` is conditionally independent of `D_{I,B}` given `Π̈`, in division-free form on the
support: `P(E = e, D_{I,B} = d) · P(Π̈ = [[d]]_Π̈) = P(E = e, Π̈ = [[d]]_Π̈) · P(D_{I,B} = d)` for all
`e`, `d`. `decisionDetermined_ratio` is the paper's displayed ratio form on positive-mass atoms.
Source: [[communication-trust-translated]] lines 381–390; [[topics/decision-determination]] lines 7–19 (udt-rep-014, 2-003, 2-032)
Kind: D
Fidelity: exact on the support (division-free form)
Hyps: n/a -/
def DecisionDetermined : Prop :=
  IsSubvariable S.E S.U ∧ ∀ (e : AE × DE) (d : DI × DB),
    mass S.μ.w (event fun ω => S.E ω = e ∧ S.DIB ω = d) * mass S.μ.w (S.evPolE (S.polOf d)) =
      mass S.μ.w (event fun ω => S.E ω = e ∧ S.polE ω = S.polOf d) * mass S.μ.w (S.evDIB d)

/-- **The paper's displayed ratio form**: on a positive-mass atom `d`,
`P(E = e ∣ D_{I,B} = d) = P(E = e ∣ Π̈ = [[d]]_Π̈)`.
Source: [[communication-trust-translated]] lines 386–389
Kind: L
Fidelity: exact
Hyps: none -/
theorem decisionDetermined_ratio (h : S.DecisionDetermined) (e : AE × DE) {d : DI × DB}
    (hd : (S.evDIB d).Nonempty) :
    condProbJunk S.μ.w (S.evE e) (S.evDIB d) 0 =
      condProbJunk S.μ.w (S.evE e) (S.evPolE (S.polOf d)) 0 := by
  have hπ : (S.evPolE (S.polOf d)).Nonempty := hd.mono (S.evDIB_subset_evPolE d)
  rw [condProbJunk_of_nonempty S.pos hd, condProbJunk_of_nonempty S.pos hπ,
    div_eq_div_iff (mass_pos_of_nonempty S.pos hd).ne' (mass_pos_of_nonempty S.pos hπ).ne']
  have h1 : S.evE e ∩ S.evDIB d = event fun ω => S.E ω = e ∧ S.DIB ω = d := by
    ext ω; simp
  have h2 : S.evE e ∩ S.evPolE (S.polOf d) = event fun ω => S.E ω = e ∧ S.polE ω = S.polOf d := by
    ext ω; simp
  rw [h1, h2]
  exact h.2 e d

/-! ### T5(b): the deterministic reading -/

/-- **The deterministic reading of decision-determination** ([[ibe-connection]] lines 80–81:
"Decision-determined: `E = f(Π̈, D_E)` for some `f`").
Source: [[ibe-connection]] lines 80–81 (udt-rep-2-003(i))
Kind: D
Fidelity: exact
Hyps: n/a -/
def DetDD : Prop := ∃ f : (OE → AE) → DE → AE × DE, ∀ ω, S.E ω = f (S.polE ω) (S.dE ω)

/-- **`E` solves the fixed-point equation** `x = ε_{D_E}(Π̈(x's observation))`: in every
structure, `E(ω) = (Π̈(ω)([[E(ω)]]_Ö), D_E(ω))` (`ε_{d_E}(ä) = (ä, d_E)` is definitional).
Source: mandate T5(b)
Kind: L
Fidelity: exact
Hyps: none -/
theorem E_fixed_point (ω : Ω) : S.E ω = (S.polE ω (S.projOE (S.E ω)), S.dE ω) := by
  rw [projOE_E, polE_apply_oE]
  rfl

/-- **Uniqueness of the environment fixed point**: for each external policy and environment
dynamic, the equation `x = (π̈([[x]]_Ö), d_E)` has at most one solution.
Source: mandate T5(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def UniqueFix : Prop :=
  ∀ (π : OE → AE) (d : DE) (x x' : AE × DE),
    x = (π (S.projOE x), d) → x' = (π (S.projOE x'), d) → x = x'

/-- **D1 is automatic under uniqueness** (udt-rep-2-003(i)): if the environment fixed-point
equation has at most one solution, the deterministic reading `E = f(Π̈, D_E)` holds. Without
uniqueness it can fail: `not_detDD_of_two_worlds` gives the criterion, and `Witness.lean` a
structure meeting it (two environment states with the same `(Π̈, D_E)` and different observations).
Source: [[ibe-connection]] lines 80–81; mandate T5(b)
Kind: P
Fidelity: exact
Hyps: (a); §3 (c) -/
theorem detDD_of_uniqueFix (h : S.UniqueFix) : S.DetDD := by
  classical
  refine ⟨fun π d => if hx : ∃ x : AE × DE, x = (π (S.projOE x), d) then hx.choose
    else (S.aE S.w₀, d), fun ω => ?_⟩
  have hx : ∃ x : AE × DE, x = (S.polE ω (S.projOE x), S.dE ω) := ⟨S.E ω, S.E_fixed_point ω⟩
  simp only [hx, ↓reduceDIte]
  exact h (S.polE ω) (S.dE ω) (S.E ω) hx.choose (S.E_fixed_point ω) hx.choose_spec

/-- **Criterion for the failure of the deterministic reading**: two worlds with the same external
policy and environment dynamic but different environments refute `DetDD`.
Source: mandate T5(b)
Kind: L
Fidelity: exact
Hyps: none -/
theorem not_detDD_of_two_worlds {ω ω' : Ω} (h1 : S.polE ω = S.polE ω') (h2 : S.dE ω = S.dE ω')
    (h3 : S.E ω ≠ S.E ω') : ¬ S.DetDD := by
  rintro ⟨f, hf⟩
  exact h3 (by rw [hf ω, hf ω', h1, h2])

/-! ### T5(c): `D_E ⊥ D_{I,B} ∣ Π̈` -/

/-- **`DynamicsCI`**: `D_E` is conditionally independent of `D_{I,B}` given `Π̈` (division-free,
same shape as `DecisionDetermined` clause (2)).
Source: mandate T5(c) (udt-rep-2-003(ii),(iii))
Kind: D
Fidelity: n/a
Hyps: n/a -/
def DynamicsCI : Prop :=
  ∀ (x : DE) (d : DI × DB),
    mass S.μ.w (event fun ω => S.dE ω = x ∧ S.DIB ω = d) * mass S.μ.w (S.evPolE (S.polOf d)) =
      mass S.μ.w (event fun ω => S.dE ω = x ∧ S.polE ω = S.polOf d) * mass S.μ.w (S.evDIB d)

/-- **Decision-determination implies `DynamicsCI`**: because `E` factors as `(Ä, D_E)`, `D_E` is
a subvariable of `E`, and conditional independence of `E` from `D_{I,B}` given `Π̈` passes to the
subvariable. This *reverses* the expected strictness (udt-rep-2-003(iii) / mandate T5(c) asked
for a witness of `DecisionDetermined ∧ ¬ DynamicsCI` "where `D_E` is correlated with `D_B` on a
coordinate `ε` ignores"): under the paper's environment-dynamic assumption `ε` cannot ignore a
coordinate of `D_E`, so no such witness exists. Recorded in the findings.
Source: mandate T5(c); udt-rep-2-003(iii)
Kind: P
Fidelity: n/a (a finding about the corpus's expectation)
Hyps: (a); §3 (c) -/
theorem dynamicsCI_of_decisionDetermined (h : S.DecisionDetermined) : S.DynamicsCI := by
  intro x d
  have hL : mass S.μ.w (event fun ω => S.dE ω = x ∧ S.DIB ω = d) =
      ∑ a, mass S.μ.w (event fun ω => S.E ω = (a, x) ∧ S.DIB ω = d) := by
    rw [mass_eq_sum_fiber S.μ.w _ S.aE]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    ext ω
    simp only [mem_event, E, Prod.mk.injEq]
    tauto
  have hR : mass S.μ.w (event fun ω => S.dE ω = x ∧ S.polE ω = S.polOf d) =
      ∑ a, mass S.μ.w (event fun ω => S.E ω = (a, x) ∧ S.polE ω = S.polOf d) := by
    rw [mass_eq_sum_fiber S.μ.w _ S.aE]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    ext ω
    simp only [mem_event, E, Prod.mk.injEq]
    tauto
  rw [hL, hR, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => h.2 (a, x) d

/-- **`DynamicsCI` implies clause (2) of decision-determination under the deterministic reading**
(udt-rep-2-003(ii)): if `E = f(Π̈, D_E)` and `D_E ⊥ D_{I,B} ∣ Π̈`, then `E ⊥ D_{I,B} ∣ Π̈`. With
`dynamicsCI_of_decisionDetermined`, under `DetDD` the two conditions are equivalent.
Source: mandate T5(c); udt-rep-2-003(ii)
Kind: P
Fidelity: exact
Hyps: (a); §3 (c) -/
theorem dd2_of_dynamicsCI (hdet : S.DetDD) (hci : S.DynamicsCI) (e : AE × DE) (d : DI × DB) :
    mass S.μ.w (event fun ω => S.E ω = e ∧ S.DIB ω = d) * mass S.μ.w (S.evPolE (S.polOf d)) =
      mass S.μ.w (event fun ω => S.E ω = e ∧ S.polE ω = S.polOf d) * mass S.μ.w (S.evDIB d) := by
  classical
  obtain ⟨f, hf⟩ := hdet
  have hL : mass S.μ.w (event fun ω => S.E ω = e ∧ S.DIB ω = d) =
      ∑ x, if f (S.polOf d) x = e then mass S.μ.w (event fun ω => S.dE ω = x ∧ S.DIB ω = d)
        else 0 := by
    rw [mass_eq_sum_fiber S.μ.w _ S.dE]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hfx
    · congr 1
      ext ω
      simp only [mem_event]
      constructor
      · rintro ⟨⟨-, hd⟩, hx⟩; exact ⟨hx, hd⟩
      · rintro ⟨hx, hd⟩
        refine ⟨⟨?_, hd⟩, hx⟩
        rw [hf ω, polE_eq, hd, hx, hfx]
    · refine mass_eq_zero_of_forall fun ω hω => ?_
      rw [mem_event] at hω
      obtain ⟨⟨he, hd⟩, hx⟩ := hω
      exact absurd (by rw [← he, hf ω, polE_eq, hd, hx]) hfx
  have hR : mass S.μ.w (event fun ω => S.E ω = e ∧ S.polE ω = S.polOf d) =
      ∑ x, if f (S.polOf d) x = e then
        mass S.μ.w (event fun ω => S.dE ω = x ∧ S.polE ω = S.polOf d) else 0 := by
    rw [mass_eq_sum_fiber S.μ.w _ S.dE]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hfx
    · congr 1
      ext ω
      simp only [mem_event]
      constructor
      · rintro ⟨⟨-, hp⟩, hx⟩; exact ⟨hx, hp⟩
      · rintro ⟨hx, hp⟩
        refine ⟨⟨?_, hp⟩, hx⟩
        rw [hf ω, hp, hx, hfx]
    · refine mass_eq_zero_of_forall fun ω hω => ?_
      rw [mem_event] at hω
      obtain ⟨⟨he, hp⟩, hx⟩ := hω
      exact absurd (by rw [← he, hf ω, hp, hx]) hfx
  rw [hL, hR, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · exact hci x d
  · simp

/-! ### T6: DD ⟹ the expected utility factors through the external policy -/

/-- **The policy utility** `E[U ∣ Π̈ = π̈]` (junk `−1` on an unrealized policy).
Source: [[communication-trust-translated]] line 464 (the `E(U ∣ Π̈ = π̈)` of the decomposition; udt-rep-015)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def policyUtility (π : OE → AE) : ℝ := condExpJunk S.μ.w S.U (S.evPolE π) (-1)

/-- **DD ⟹ the conditional expected utility given the dynamics is the policy utility of the
external policy they encode**: for every realized `d` (a positive-mass atom on the support),
`E[U ∣ D_{I,B} = d] = E[U ∣ Π̈ = [[d]]_Π̈]`. Derived, not assumed: clause (1) gives `U = u ∘ E`, and
the atom identity of clause (2) summed over `e` with weight `u(e)` gives the claim. Quantified over
realized `d` only: for `d` outside the range the left side is the junk `−1` while `{Π̈ = [[d]]_Π̈}`
may be non-empty, so the identity is false there. `udt-policy-calc`'s `exists_policyUtility` is
the deterministic `(c)` shadow of this theorem.
Source: [[communication-trust-translated]] lines 381–392, 463–464 (udt-rep-015)
Kind: P
Fidelity: exact (over realized `d`)
Hyps: (a); §3 (c) -/
theorem condExp_DIB_eq_policyUtility (h : S.DecisionDetermined) {d : DI × DB}
    (hd : (S.evDIB d).Nonempty) :
    condExpJunk S.μ.w S.U (S.evDIB d) (-1) = S.policyUtility (S.polOf d) := by
  obtain ⟨u, hu⟩ := (isSubvariable_iff_exists S.E S.U).1 h.1
  have hπ : (S.evPolE (S.polOf d)).Nonempty := hd.mono (S.evDIB_subset_evPolE d)
  have hd' := mass_pos_of_nonempty S.pos hd
  have hπ' := mass_pos_of_nonempty S.pos hπ
  unfold policyUtility
  rw [condExpJunk_of_pos hd', condExpJunk_of_pos hπ', div_eq_div_iff hd'.ne' hπ'.ne']
  have hsum : ∀ F : Finset Ω, ∑ ω ∈ F, S.μ.w ω * S.U ω =
      ∑ e, u e * mass S.μ.w (F.filter fun ω => S.E ω = e) := by
    intro F
    rw [← sum_mul_comp_eq]
    exact Finset.sum_congr rfl fun ω _ => by rw [hu ω]
  rw [hsum, hsum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h1 : (S.evDIB d).filter (fun ω => S.E ω = e) = event fun ω => S.E ω = e ∧ S.DIB ω = d := by
    ext ω; simp [and_comm]
  have h2 : (S.evPolE (S.polOf d)).filter (fun ω => S.E ω = e) =
      event fun ω => S.E ω = e ∧ S.polE ω = S.polOf d := by
    ext ω; simp [and_comm]
  rw [h1, h2, mul_assoc, mul_assoc, h.2 e d]

/-- **Corollary**: at every world, `E[U ∣ D_{I,B} = D_{I,B}(ω)] = policyUtility(Π̈(ω))`.
Source: [[communication-trust-translated]] lines 463–464 (udt-rep-015)
Kind: C
Fidelity: exact
Hyps: (a); §3 (c) -/
theorem condExp_DIB_eq_policyUtility_polE (h : S.DecisionDetermined) (ω : Ω) :
    condExpJunk S.μ.w S.U (S.evDIB (S.DIB ω)) (-1) = S.policyUtility (S.polE ω) :=
  S.condExp_DIB_eq_policyUtility h ⟨ω, by simp⟩

/-! ### T7: the decomposition over external policies -/

/-- **On a `D_{I,B}`-measurable non-empty event, the conditional expected utility is the average
of the policy utilities**: under DD, `E[U ∣ G] = E[policyUtility(Π̈) ∣ G]` for every non-empty `G`
that is a union of `D_{I,B}`-atoms. This is the engine of every C&T proof; T7 and T10 are
instances.
Source: [[communication-trust-translated]] lines 463–466 (udt-rep-016)
Kind: P
Fidelity: n/a (infrastructure for T7/T10)
Hyps: (a); §3 (c) -/
theorem condExp_eq_policyUtility_of_measurable (h : S.DecisionDetermined) {G : Finset Ω}
    (hG : G.Nonempty) (hmeas : ∀ ω ∈ G, ∀ ω', S.DIB ω' = S.DIB ω → ω' ∈ G) (π : OE → AE)
    (hπ : ∀ ω ∈ G, S.polE ω = π) : condExpJunk S.μ.w S.U G (-1) = S.policyUtility π := by
  refine condExpJunk_of_atoms S.pos S.U S.DIB hG hmeas fun ω hω => ?_
  rw [← hπ ω hω]
  exact S.condExp_DIB_eq_policyUtility_polE h ω

/-- **The decomposition over external policies (T7)**: under DD and `Π* ⊑ D_{I,B}`, for a
non-empty event `{Π*(ȯ, ö) = a}`,
`E[U ∣ Π*(ȯ,ö) = a] = ∑_{π̈ ∈ range Π̈} E[U ∣ Π̈ = π̈] · P(Π̈ = π̈ ∣ Π*(ȯ,ö) = a)`.
The paper's "By decision-determination" (translation line 463) uses `Π* ⊑ D_{I,B}` silently; the
original's "I assume that a subvariable representing the chosen policy exists" (line ~345) is where
it is taken. `Witness.lean` shows the identity fails when `Π*` is not a function of `D_{I,B}`.
Source: [[communication-trust-translated]] lines 463–466 (udt-rep-016)
Kind: P
Fidelity: exact
Hyps: (a); §3 (c) -/
theorem decomposition (h : S.DecisionDetermined) (hsub : IsSubvariable S.DIB S.polS)
    [DecidableEq AI] {o : OI} {e : OE} {a : AI × AE} (hne : (S.evS o e a).Nonempty) :
    S.score o e a = ∑ π ∈ Finset.univ.image S.polE,
      S.policyUtility π * condProbJunk S.μ.w (S.evPolE π) (S.evS o e a) 0 := by
  unfold score
  rw [condExpJunk_total S.pos S.U S.polE hne]
  have hzero : ∀ π ∈ (Finset.univ : Finset (OE → AE)), π ∉ Finset.univ.image S.polE →
      S.policyUtility π * condProbJunk S.μ.w (S.evPolE π) (S.evS o e a) 0 = 0 := by
    intro π _ hπ
    have : S.evPolE π = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ω hω
      rw [mem_evPolE] at hω
      exact hπ (Finset.mem_image.2 ⟨ω, Finset.mem_univ _, hω⟩)
    rw [condProbJunk_of_nonempty S.pos hne, this, Finset.empty_inter]
    simp [mass]
  symm
  rw [Finset.sum_subset (Finset.subset_univ _) hzero]
  · refine Finset.sum_congr rfl fun π _ => ?_
    by_cases hG : ((S.evS o e a).filter fun ω => S.polE ω = π).Nonempty
    · congr 1
      refine (S.condExp_eq_policyUtility_of_measurable h hG ?_ π ?_).symm
      · intro ω hω ω' hω'
        rw [Finset.mem_filter, mem_evS] at hω ⊢
        refine ⟨?_, ?_⟩
        · rw [← hω.1]
          exact congrFun (hsub ω' ω hω') (o, e)
        · rw [← hω.2]
          exact S.polE_sub ω' ω hω'
      · intro ω hω
        exact (Finset.mem_filter.1 hω).2
    · rw [Finset.not_nonempty_iff_eq_empty] at hG
      have : condProbJunk S.μ.w (S.evPolE π) (S.evS o e a) 0 = 0 := by
        rw [condProbJunk_of_nonempty S.pos hne]
        unfold evPolE
        rw [event_inter_eq_filter, hG]
        simp [mass]
      have this' : condProbJunk S.μ.w (event fun ω => S.polE ω = π) (S.evS o e a) 0 = 0 := this
      rw [hG, this', this, mul_zero, mul_zero]

end AbstractDS

end Cleanroom.Udt.UdtCommTrust
