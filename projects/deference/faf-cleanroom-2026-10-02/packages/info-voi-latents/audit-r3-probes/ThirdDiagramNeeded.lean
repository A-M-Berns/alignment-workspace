import Cleanroom.Info.InfoVoiLatents.NaturalLatentsWitnessFour
import Cleanroom.Info.InfoVoiLatents.NaturalLatentsStochastic

/-!
# info-voi-latents — audit round 3 (adversarial) probe: the third diagram is load-bearing

Probe file, not imported by the library. Elaborated with `scripts/lean-check`.

`NaturalLatentsStochastic.natural_latents_stochastic` takes four hypotheses (mediation, the two
stochastic-redundancy diagrams, the third diagram `Λ ⊥ Λ' | X`). The deterministic special case
makes the third diagram automatic (`thirdDiagram_of_detRedundant`), and the package's only
witness inhabits the stochastic theorem through that reduction — so nothing in the package shows
that the third diagram is a *real* hypothesis of the stochastic theorem, i.e. that the theorem is
not provable from the other three. This probe shows it is real: on the package's own four uniform
bits `((b, d), (n₁, n₂))` take `X₁ = n₁`, `X₂ = n₂`, `Λ = d`, `Λ' = d ⊕ n₁` (`b` unused). Then

* mediation `I[n₁ : n₂ | d] = 0` and both redundancies `I[Λ' : n₁ | n₂] = I[Λ' : n₂ | n₁] = 0`
  hold (`d ⊕ n₁` is a fair coin independent of `n₁` given `n₂`, and a function of `d` given `n₁`),
* the third diagram fails, `I[d : Λ' | (n₁, n₂)] = log 2`,
* and the conclusion fails, `I[Λ' : (n₁, n₂) | d] = log 2` — so `¬ CondIndepFun Λ' ⟨X₁, X₂⟩ Λ`.

Bonus for `Open.natural_latents_approx` (coefficient `1` on `ε₃`): at this instance
`ε₁ = ε₂ = ε₂' = 0`, `ε₃ = log 2` and `I[Λ' : X | Λ] = log 2 = ε₃`, so the conjectured constant is
*attained* here (not refuted); the proved `2ε₃` bound is slack by `log 2` at this instance.
-/

namespace AuditR3

open MeasureTheory ProbabilityTheory ShannonInformation Finset
open Cleanroom.Info.InfoVoiLatents.Shannon
open Cleanroom.Info.InfoVoiLatents.NaturalLatents

noncomputable section

/-- `n₁`. -/
def N₁x : Ω4 → Bool := fun ω => ω.2.1
/-- `n₂`. -/
def N₂x : Ω4 → Bool := fun ω => ω.2.2
/-- `d`. -/
def Dx : Ω4 → Bool := fun ω => ω.1.2
/-- `d ⊕ n₁`. -/
def Lx : Ω4 → Bool := fun ω => Bool.xor ω.1.2 ω.2.1
/-- `(n₁, n₂)`. -/
def Nx : Ω4 → Bool × Bool := fun ω => (ω.2.1, ω.2.2)

theorem measurable_N₁x : Measurable N₁x := measurable_of_countable _
theorem measurable_N₂x : Measurable N₂x := measurable_of_countable _
theorem measurable_Dx : Measurable Dx := measurable_of_countable _
theorem measurable_Lx : Measurable Lx := measurable_of_countable _
theorem measurable_Nx : Measurable Nx := measurable_of_countable _

/-! ### Entropies (equal fibres on the 16-point space, or injective images) -/

theorem entropy_Dx : H[Dx ; μ4] = Real.log 2 := by
  rw [entropy_of_fibre measurable_Dx 8 (by decide), Fintype.card_bool]; norm_num

theorem entropy_N₁x : H[N₁x ; μ4] = Real.log 2 := by
  rw [entropy_of_fibre measurable_N₁x 8 (by decide), Fintype.card_bool]; norm_num

theorem entropy_N₂x : H[N₂x ; μ4] = Real.log 2 := by
  rw [entropy_of_fibre measurable_N₂x 8 (by decide), Fintype.card_bool]; norm_num

theorem entropy_Nx : H[Nx ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre measurable_Nx 4 (by decide), Fintype.card_prod, Fintype.card_bool]; norm_num

theorem entropy_N₁D : H[(⟨N₁x, Dx⟩ : Ω4 → Bool × Bool) ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre (measurable_N₁x.prodMk measurable_Dx) 4 (by decide), Fintype.card_prod,
    Fintype.card_bool]; norm_num

theorem entropy_N₂D : H[(⟨N₂x, Dx⟩ : Ω4 → Bool × Bool) ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre (measurable_N₂x.prodMk measurable_Dx) 4 (by decide), Fintype.card_prod,
    Fintype.card_bool]; norm_num

theorem entropy_N₁N₂D : H[(⟨N₁x, ⟨N₂x, Dx⟩⟩ : Ω4 → Bool × (Bool × Bool)) ; μ4] = Real.log 8 := by
  rw [entropy_of_fibre (measurable_N₁x.prodMk (measurable_N₂x.prodMk measurable_Dx)) 2 (by decide),
    Fintype.card_prod, Fintype.card_prod, Fintype.card_bool]; norm_num

theorem entropy_LN₂ : H[(⟨Lx, N₂x⟩ : Ω4 → Bool × Bool) ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre (measurable_Lx.prodMk measurable_N₂x) 4 (by decide), Fintype.card_prod,
    Fintype.card_bool]; norm_num

theorem entropy_LN₁ : H[(⟨Lx, N₁x⟩ : Ω4 → Bool × Bool) ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre (measurable_Lx.prodMk measurable_N₁x) 4 (by decide), Fintype.card_prod,
    Fintype.card_bool]; norm_num

theorem entropy_LD : H[(⟨Lx, Dx⟩ : Ω4 → Bool × Bool) ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre (measurable_Lx.prodMk measurable_Dx) 4 (by decide), Fintype.card_prod,
    Fintype.card_bool]; norm_num

theorem entropy_N₁N₂ : H[(⟨N₁x, N₂x⟩ : Ω4 → Bool × Bool) ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre (measurable_N₁x.prodMk measurable_N₂x) 4 (by decide), Fintype.card_prod,
    Fintype.card_bool]; norm_num

theorem entropy_N₂N₁ : H[(⟨N₂x, N₁x⟩ : Ω4 → Bool × Bool) ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre (measurable_N₂x.prodMk measurable_N₁x) 4 (by decide), Fintype.card_prod,
    Fintype.card_bool]; norm_num

theorem entropy_LN₁N₂ : H[(⟨Lx, ⟨N₁x, N₂x⟩⟩ : Ω4 → Bool × (Bool × Bool)) ; μ4] = Real.log 8 := by
  rw [entropy_of_fibre (measurable_Lx.prodMk (measurable_N₁x.prodMk measurable_N₂x)) 2 (by decide),
    Fintype.card_prod, Fintype.card_prod, Fintype.card_bool]; norm_num

theorem entropy_LN₂N₁ : H[(⟨Lx, ⟨N₂x, N₁x⟩⟩ : Ω4 → Bool × (Bool × Bool)) ; μ4] = Real.log 8 := by
  rw [entropy_of_fibre (measurable_Lx.prodMk (measurable_N₂x.prodMk measurable_N₁x)) 2 (by decide),
    Fintype.card_prod, Fintype.card_prod, Fintype.card_bool]; norm_num

theorem entropy_LNx : H[(⟨Lx, Nx⟩ : Ω4 → Bool × (Bool × Bool)) ; μ4] = Real.log 8 := by
  rw [entropy_of_fibre (measurable_Lx.prodMk measurable_Nx) 2 (by decide),
    Fintype.card_prod, Fintype.card_prod, Fintype.card_bool]; norm_num

theorem entropy_DNx : H[(⟨Dx, Nx⟩ : Ω4 → Bool × (Bool × Bool)) ; μ4] = Real.log 8 := by
  rw [entropy_of_fibre (measurable_Dx.prodMk measurable_Nx) 2 (by decide),
    Fintype.card_prod, Fintype.card_prod, Fintype.card_bool]; norm_num

theorem entropy_NxD : H[(⟨Nx, Dx⟩ : Ω4 → (Bool × Bool) × Bool) ; μ4] = Real.log 8 := by
  rw [entropy_of_fibre (measurable_Nx.prodMk measurable_Dx) 2 (by decide),
    Fintype.card_prod, Fintype.card_prod, Fintype.card_bool]; norm_num

/-- `(Λ', (N, d))` is an injective image of `(N, d)` (`Λ' = d ⊕ n₁`). -/
theorem entropy_LNxD : H[(⟨Lx, ⟨Nx, Dx⟩⟩ : Ω4 → Bool × ((Bool × Bool) × Bool)) ; μ4]
    = Real.log 8 := by
  rw [entropy_comp_eq (measurable_Nx.prodMk measurable_Dx)
    (⟨Lx, ⟨Nx, Dx⟩⟩ : Ω4 → Bool × ((Bool × Bool) × Bool))
    (fun p : (Bool × Bool) × Bool => (Bool.xor p.2 p.1.1, p)) (by decide) (fun _ => rfl),
    entropy_NxD]

/-- `(d, (Λ', N))` is an injective image of `(d, N)`. -/
theorem entropy_DLNx : H[(⟨Dx, ⟨Lx, Nx⟩⟩ : Ω4 → Bool × (Bool × (Bool × Bool))) ; μ4]
    = Real.log 8 := by
  rw [entropy_comp_eq (measurable_Dx.prodMk measurable_Nx)
    (⟨Dx, ⟨Lx, Nx⟩⟩ : Ω4 → Bool × (Bool × (Bool × Bool)))
    (fun p : Bool × (Bool × Bool) => (p.1, (Bool.xor p.1 p.2.1, p.2))) (by decide) (fun _ => rfl),
    entropy_DNx]

/-! ### The four diagrams and the conclusion, computed -/

/-- Mediation holds: `I[n₁ : n₂ | d] = 0`. -/
theorem cmi_mediation : I[N₁x : N₂x | Dx ; μ4] = 0 := by
  haveI : FiniteEntropyOf (⟨N₂x, Dx⟩ : Ω4 → Bool × Bool) μ4 :=
    finiteEntropyOf_pair measurable_N₂x measurable_Dx
  rw [ShannonInformation.condMutualInfo_eq' measurable_N₁x measurable_N₂x measurable_Dx μ4,
    ShannonInformation.chain_rule'' μ4 measurable_N₁x measurable_Dx,
    ShannonInformation.chain_rule'' μ4 measurable_N₁x (measurable_N₂x.prodMk measurable_Dx),
    entropy_N₁D, entropy_Dx, entropy_N₁N₂D, entropy_N₂D]
  obtain ⟨h4, h8, -⟩ := log_pow_two_facts
  rw [h4, h8]; ring

/-- Redundancy in the first direction: `I[Λ' : n₁ | n₂] = 0`. -/
theorem cmi_red₁ : I[Lx : N₁x | N₂x ; μ4] = 0 := by
  haveI : FiniteEntropyOf (⟨N₁x, N₂x⟩ : Ω4 → Bool × Bool) μ4 :=
    finiteEntropyOf_pair measurable_N₁x measurable_N₂x
  rw [ShannonInformation.condMutualInfo_eq' measurable_Lx measurable_N₁x measurable_N₂x μ4,
    ShannonInformation.chain_rule'' μ4 measurable_Lx measurable_N₂x,
    ShannonInformation.chain_rule'' μ4 measurable_Lx (measurable_N₁x.prodMk measurable_N₂x),
    entropy_LN₂, entropy_N₂x, entropy_LN₁N₂, entropy_N₁N₂]
  obtain ⟨h4, h8, -⟩ := log_pow_two_facts
  rw [h4, h8]; ring

/-- Redundancy in the second direction: `I[Λ' : n₂ | n₁] = 0`. -/
theorem cmi_red₂ : I[Lx : N₂x | N₁x ; μ4] = 0 := by
  haveI : FiniteEntropyOf (⟨N₂x, N₁x⟩ : Ω4 → Bool × Bool) μ4 :=
    finiteEntropyOf_pair measurable_N₂x measurable_N₁x
  rw [ShannonInformation.condMutualInfo_eq' measurable_Lx measurable_N₂x measurable_N₁x μ4,
    ShannonInformation.chain_rule'' μ4 measurable_Lx measurable_N₁x,
    ShannonInformation.chain_rule'' μ4 measurable_Lx (measurable_N₂x.prodMk measurable_N₁x),
    entropy_LN₁, entropy_N₁x, entropy_LN₂N₁, entropy_N₂N₁]
  obtain ⟨h4, h8, -⟩ := log_pow_two_facts
  rw [h4, h8]; ring

/-- The third diagram fails: `I[d : Λ' | (n₁, n₂)] = log 2`. -/
theorem cmi_third : I[Dx : Lx | Nx ; μ4] = Real.log 2 := by
  haveI : FiniteEntropyOf (⟨Lx, Nx⟩ : Ω4 → Bool × (Bool × Bool)) μ4 :=
    finiteEntropyOf_pair measurable_Lx measurable_Nx
  rw [ShannonInformation.condMutualInfo_eq' measurable_Dx measurable_Lx measurable_Nx μ4,
    ShannonInformation.chain_rule'' μ4 measurable_Dx measurable_Nx,
    ShannonInformation.chain_rule'' μ4 measurable_Dx (measurable_Lx.prodMk measurable_Nx),
    entropy_DNx, entropy_Nx, entropy_DLNx, entropy_LNx]
  obtain ⟨h4, h8, -⟩ := log_pow_two_facts
  rw [h4, h8]; ring

/-- The conclusion fails: `I[Λ' : (n₁, n₂) | d] = log 2`. -/
theorem cmi_conclusion : I[Lx : Nx | Dx ; μ4] = Real.log 2 := by
  haveI : FiniteEntropyOf (⟨Nx, Dx⟩ : Ω4 → (Bool × Bool) × Bool) μ4 :=
    finiteEntropyOf_pair measurable_Nx measurable_Dx
  rw [ShannonInformation.condMutualInfo_eq' measurable_Lx measurable_Nx measurable_Dx μ4,
    ShannonInformation.chain_rule'' μ4 measurable_Lx measurable_Dx,
    ShannonInformation.chain_rule'' μ4 measurable_Lx (measurable_Nx.prodMk measurable_Dx),
    entropy_LD, entropy_Dx, entropy_LNxD, entropy_NxD]
  obtain ⟨h4, h8, -⟩ := log_pow_two_facts
  rw [h4, h8]; ring

/-- `Nx` is definitionally the pair `⟨N₁x, N₂x⟩`. -/
theorem Nx_eq : Nx = (⟨N₁x, N₂x⟩ : Ω4 → Bool × Bool) := rfl

/-- **The third diagram is load-bearing**: mediation and both stochastic redundancies hold, the
third diagram fails, and the conclusion of `natural_latents_stochastic` fails. -/
theorem third_diagram_load_bearing :
    Mediates Dx N₁x N₂x μ4 ∧ StochRedundant N₁x N₂x Lx μ4 ∧
    ¬ ThirdDiagram N₁x N₂x Dx Lx μ4 ∧
    ¬ CondIndepFun Lx (⟨N₁x, N₂x⟩ : Ω4 → Bool × Bool) Dx μ4 := by
  haveI : FiniteEntropyOf (⟨N₁x, N₂x⟩ : Ω4 → Bool × Bool) μ4 :=
    finiteEntropyOf_pair measurable_N₁x measurable_N₂x
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (ShannonInformation.condMutualInfo_eq_zero measurable_N₁x measurable_N₂x
      measurable_Dx).1 cmi_mediation
  · exact (ShannonInformation.condMutualInfo_eq_zero measurable_Lx measurable_N₁x
      measurable_N₂x).1 cmi_red₁
  · exact (ShannonInformation.condMutualInfo_eq_zero measurable_Lx measurable_N₂x
      measurable_N₁x).1 cmi_red₂
  · intro h
    have := (ShannonInformation.condMutualInfo_eq_zero measurable_Dx measurable_Lx
      (measurable_N₁x.prodMk measurable_N₂x)).2 h
    change I[Dx : Lx | Nx ; μ4] = 0 at this
    rw [cmi_third] at this
    exact hlog this
  · intro h
    have := (ShannonInformation.condMutualInfo_eq_zero measurable_Lx
      (measurable_N₁x.prodMk measurable_N₂x) measurable_Dx).2 h
    change I[Lx : Nx | Dx ; μ4] = 0 at this
    rw [cmi_conclusion] at this
    exact hlog this

/-- **Coefficient `1` is attained here**: `I[Λ' : X | Λ] = ε₃` with `ε₁ = ε₂ = ε₂' = 0`, so
`Open.natural_latents_approx` (constant `ε₁ + ε₂ + ε₂' + ε₃`) is tight, not refuted, at this
instance; the proved `2ε₃` bound is slack by `log 2`. -/
theorem coefficient_one_attained :
    I[Lx : (⟨N₁x, N₂x⟩ : Ω4 → Bool × Bool) | Dx ; μ4]
      = I[N₁x : N₂x | Dx ; μ4] + I[Lx : N₁x | N₂x ; μ4] + I[Lx : N₂x | N₁x ; μ4]
        + I[Dx : Lx | (⟨N₁x, N₂x⟩ : Ω4 → Bool × Bool) ; μ4] := by
  change I[Lx : Nx | Dx ; μ4] = I[N₁x : N₂x | Dx ; μ4] + I[Lx : N₁x | N₂x ; μ4]
    + I[Lx : N₂x | N₁x ; μ4] + I[Dx : Lx | Nx ; μ4]
  rw [cmi_conclusion, cmi_mediation, cmi_red₁, cmi_red₂, cmi_third]; ring

end

end AuditR3
