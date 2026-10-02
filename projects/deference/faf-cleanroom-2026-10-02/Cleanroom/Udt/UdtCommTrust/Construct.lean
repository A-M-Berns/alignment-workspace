import Cleanroom.Udt.UdtCommTrust.Concrete

/-!
# `Cleanroom.Udt.UdtCommTrust.Construct`: a defensible `Π*` from `D_B` and a neutral side channel

Work package `udt-comm-trust`, target T4(b) (udt-rep-2-009), written in repair round 1. Sources:
the original `references/communication&trust.md` lines ~343–347 ("I assume that a subvariable
representing the chosen policy exists"), ~333 (`Ô`, `Ǒ` need not split `Ȯ`); mandate T4(b).

The paper assumes `Π*` exists. Given a **neutral side-channel value** `ǒ₀` (forcing nothing at any
instance) that is **compatible** with every realized semantic observation, and given that `Ȯ` is
determined by `(Ô, Ǒ)`, the chosen policy can be *defined* as the effective policy with the side
channel neutralized:

`Π*_c(ω)(ȯ, ö) := [[β_{D_B(ω)}(ȯ⟨Ǒ := ǒ₀⟩, ö)]]_A`.

What is and is not a theorem here (the mandate's (i)–(iii)):

* (i) `Π*_c ⊑ D_B` — by construction (`polSC_sub`).
* (ii) `Π† = Π*_c` at the realized observation. **At worlds whose side channel is at the neutral
  value** this is by construction (`polD_eq_polSC_of_oC`). **On the whole unforced event**
  `{P(ω)(Ö(ω)) = ⊥}` it is *not* a theorem of the abstract structure: it is exactly the assumption
  that the boundary dynamics respond to the side channel only through forcing
  (`SideChannelInert`), and `polD_eq_polSC_iff_inert` records the equivalence rather than
  pretending to prove it. This is `hlink` of "`Π̈ = R` in fact", for the constructed policy.
* (iii) `m{Π*_c = π} = 0 → Π† = Π*_c` on that event — under inertness, from the junk-`0` reading of
  `m` (`polD_eq_polSC_of_modProb_zero`; the general form is for any event of modification
  probability zero).

When `Ȯ` is not determined by `(Ô, Ǒ)` the neutralized observation is junk and the construction is
unavailable: `Π*` stays a field (the paper's assumption). The mandate's precondition
`FactorsAs Ô Ǒ` is stronger than needed: only compatibility of the *neutral* value with every
realized semantic observation is used (`neutralCompatible_of_factorsAs`); `W2m` satisfies the
weaker condition and not the stronger one (`WitnessDet.lean`).
-/

namespace Cleanroom.Udt.UdtCommTrust

namespace ConcreteDS

open Cleanroom.Udt.UdtPolicyCalc Finset

variable {Ω OI OE AI AE DI DE DB OH OC : Type}
variable [Fintype Ω] [DecidableEq Ω]
variable (S : ConcreteDS Ω OI OE AI AE DI DE DB OH OC)

/-! ### Preconditions -/

/-- **`Ȯ` is determined by `(Ô, Ǒ)`**: the internal observation splits into its semantic and
side-channel parts. The abstract structure only gives `Ô ⊑ Ȯ` and `Ǒ ⊑ Ȯ`; the original (line ~333)
allows `Ȯ` to carry more. Without this the construction is unavailable.
Source: original line ~333; mandate T4(b) ("`FactorsAs Ô Ǒ` at each instance")
Kind: D
Fidelity: n/a (precondition)
Hyps: n/a -/
def SemChanSplit : Prop := IsSubvariable (fun ω => (S.oH ω, S.oC ω)) S.oI

/-- **A neutral side-channel value**: `p_ö(ǒ₀) = ⊥` at every instance.
Source: mandate T4(b)
Kind: D
Fidelity: exact
Hyps: n/a -/
def Neutral (c₀ : OC) : Prop := ∀ e, S.p e c₀ = none

/-- **The neutral value is compatible with every realized semantic observation**: for every world
there is a world with the same `Ô` and side channel `ǒ₀`. This is what the construction uses;
`FactorsAs Ô Ǒ` (the mandate's precondition) with `ǒ₀` realized implies it.
Source: mandate T4(b) (weakened precondition)
Kind: D
Fidelity: weaker than `FactorsAs Ô Ǒ`: only the neutral value must combine with every `Ô`
Hyps: n/a -/
def NeutralCompatible (c₀ : OC) : Prop := ∀ ω, ∃ ω', S.oH ω' = S.oH ω ∧ S.oC ω' = c₀

/-- **`FactorsAs Ô Ǒ` with `ǒ₀` realized gives compatibility.**
Source: mandate T4(b)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem neutralCompatible_of_factorsAs (hfac : FactorsAs S.oH S.oC) {c₀ : OC}
    (hc : c₀ ∈ Set.range S.oC) : S.NeutralCompatible c₀ :=
  fun ω => hfac (S.oH ω) ⟨ω, rfl⟩ c₀ hc

/-! ### The neutralized observation and the constructed policy -/

/-- **`ȯ⟨Ǒ := ǒ₀⟩`**: the internal observation with semantic part `[[ȯ]]_Ô` and side channel
`ǒ₀`, as the projection of `Ȯ` along `(Ô, Ǒ)`. Junk `Ȯ(w₀)` when `([[ȯ]]_Ô, ǒ₀)` is unrealized or
`Ȯ` is not determined by `(Ô, Ǒ)` (`neutralize_eq` is the spec).
Source: mandate T4(b) ("`ȯ` with `Ǒ`-coordinate `ǒ₀`")
Kind: D
Fidelity: exact on realized `ȯ` under `SemChanSplit` and `NeutralCompatible`; junk otherwise
Hyps: n/a -/
noncomputable def neutralize (c₀ : OC) (o : OI) : OI :=
  projOf (fun ω => (S.oH ω, S.oC ω)) S.oI S.w₀ (S.projOH o, c₀)

/-- Supporting lemma `neutralize_spec`: at a world whose side channel is already `ǒ₀`,
neutralizing its observation changes nothing.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem neutralize_spec (hsplit : S.SemChanSplit) {c₀ : OC} (ω : Ω) (hc : S.oC ω = c₀) :
    S.neutralize c₀ (S.oI ω) = S.oI ω := by
  unfold neutralize
  rw [S.projOH_oI, ← hc]
  exact projOf_spec hsplit S.w₀ ω

/-- Supporting lemma `neutralize_eq`: under the preconditions, the neutralized observation of a
realized `ȯ` is the observation of a world with the same `Ô` and side channel `ǒ₀`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem neutralize_eq (hsplit : S.SemChanSplit) {c₀ : OC} (hcomp : S.NeutralCompatible c₀)
    (ω : Ω) : ∃ ω', S.oH ω' = S.oH ω ∧ S.oC ω' = c₀ ∧ S.neutralize c₀ (S.oI ω) = S.oI ω' := by
  obtain ⟨ω', h1, h2⟩ := hcomp ω
  refine ⟨ω', h1, h2, ?_⟩
  unfold neutralize
  rw [S.projOH_oI, ← h1, ← h2]
  exact projOf_spec hsplit S.w₀ ω'

/-- **The constructed chosen policy `Π*_c`**: `Π*_c(ω)(ȯ, ö) := [[((ȯ⟨Ǒ := ǒ₀⟩, ö), D_B(ω))]]_A`,
the effective policy `Π†(ω)` evaluated at the observation with the side channel neutralized. The
paper assumes `Π*` exists (original line ~345); this discharges the assumption under the stated
preconditions. When `Ô, Ǒ` do not determine `Ȯ` the construction is unavailable and `Π*` stays a
field.
Source: original lines ~343–347; mandate T4(b) (udt-rep-2-009)
Kind: D
Fidelity: variant: the mandate's recipe with `FactorsAs Ô Ǒ` weakened to `NeutralCompatible`
Hyps: n/a -/
noncomputable def polSC (c₀ : OC) (ω : Ω) : Policy (OI × OE) (AI × AE) :=
  fun oe => S.projA ((S.neutralize c₀ oe.1, oe.2), S.dB ω)

/-- `Π*_c(ω)(ȯ, ö) = Π†(ω)(ȯ⟨Ǒ := ǒ₀⟩, ö)`, by definition.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polSC_eq_polD (c₀ : OC) (ω : Ω) (oe : OI × OE) :
    S.polSC c₀ ω oe = S.polD ω (S.neutralize c₀ oe.1, oe.2) := rfl

/-- **(i) `Π*_c ⊑ D_B`** — by construction.
Source: mandate T4(b)(i)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem polSC_sub (c₀ : OC) : IsSubvariable S.dB (S.polSC c₀) :=
  IsSubvariable.of_comp S.dB fun d => fun (oe : OI × OE) => S.projA ((S.neutralize c₀ oe.1, oe.2), d)

/-- **`Π*_c ⊑ D_{I,B}`**: the hypothesis of T7, T10 and T11 (the decomposition over external
policies), discharged for the constructed policy.
Source: mandate T4(b), T7 ("that is the point of T4(b)")
Kind: L
Fidelity: exact
Hyps: none -/
theorem polSC_sub_DIB (c₀ : OC) : IsSubvariable S.DIB (S.polSC c₀) :=
  fun ω ω' h => S.polSC_sub c₀ ω ω' (congrArg Prod.snd h)

/-! ### (ii): `Π† = Π*_c` at the realized observation -/

/-- **(ii), exact form: at a world whose side channel is at the neutral value, the effective and
constructed policies agree at the realized observation.** By construction (`neutralize_spec`).
Source: mandate T4(b)(ii), restricted to `{Ǒ = ǒ₀}`
Kind: P
Fidelity: weaker: on `{Ǒ(ω) = ǒ₀}` rather than the mandate's unforced event `{P(ω)(Ö(ω)) = ⊥}` (for which see `polD_eq_polSC_iff_inert`)
Hyps: (a); `SemChanSplit` is the precondition -/
theorem polD_eq_polSC_of_oC (hsplit : S.SemChanSplit) {c₀ : OC} {ω : Ω} (hc : S.oC ω = c₀) :
    S.polD ω (S.O ω) = S.polSC c₀ ω (S.O ω) := by
  show S.polD ω (S.O ω) = S.polD ω (S.neutralize c₀ (S.oI ω), S.oE ω)
  rw [S.neutralize_spec hsplit ω hc]
  rfl

/-- **Side-channel inertness**: at every unforced world, the effective policy gives the same action
at the neutralized observation as at the realized one — the boundary dynamics respond to the
side channel only through forcing. This is the *content* of the paper's prose meaning of `Π*`
("what would run if unmodified"); it is not derivable from the abstract structure.
Source: original lines ~343–347 (the prose meaning of `Π*`); mandate T4(b)(ii)
Kind: D
Fidelity: n/a (the assumption (ii) needs beyond `{Ǒ = ǒ₀}`)
Hyps: n/a -/
def SideChannelInert (c₀ : OC) : Prop :=
  ∀ ω, S.P ω (S.oE ω) = none →
    S.polD ω (S.neutralize c₀ (S.oI ω), S.oE ω) = S.polD ω (S.O ω)

/-- **(ii) on the unforced event is equivalent to inertness** — not a theorem about the structure
but a restatement: `Π*_c(ω)(O(ω))` *is* `Π†(ω)(ȯ⟨Ǒ := ǒ₀⟩, ö)` by definition. Recorded as `L` so
that nobody reads (ii) as proved.
Source: mandate T4(b)(ii)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polD_eq_polSC_iff_inert (c₀ : OC) :
    (∀ ω, S.P ω (S.oE ω) = none → S.polD ω (S.O ω) = S.polSC c₀ ω (S.O ω)) ↔
      S.SideChannelInert c₀ :=
  ⟨fun h ω hω => (h ω hω).symm, fun h ω hω => (h ω hω).symm⟩

variable [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE]

/-- **(iii): on any event of modification probability zero, `Π† = Π*_c` at the realized
observation** (under inertness). With junk `0`, `m(G) = 0` on a non-empty `G` means no world of `G`
is modified, so every world of `G` is unforced at its instance. The mandate's form is the instance
`G = {Π*_c = π}`.
Source: mandate T4(b)(iii)
Kind: C
Fidelity: exact (for any event; the mandate's is the instance `{Π*_c = π}`)
Hyps: (a); `SideChannelInert` as in (ii); §3 (c) junk `0` -/
theorem polD_eq_polSC_of_modProb_zero {c₀ : OC} (hin : S.SideChannelInert c₀) {G : Finset Ω}
    (hG : S.modProb G = 0) : ∀ ω ∈ G, S.polD ω (S.O ω) = S.polSC c₀ ω (S.O ω) := by
  intro ω hω
  have hGne : G.Nonempty := ⟨ω, hω⟩
  unfold modProb at hG
  rw [condProbJunk_of_nonempty S.pos hGne, div_eq_zero_iff] at hG
  rcases hG with hG | hG
  · rw [mass_eq_zero_iff S.pos] at hG
    have hnot : ω ∉ S.evMod := fun h => by
      have : ω ∈ S.evMod ∩ G := Finset.mem_inter.2 ⟨h, hω⟩
      rw [hG] at this
      exact Finset.notMem_empty _ this
    have hunmod : ¬ S.IsModified ω := by simpa [evMod] using hnot
    have hnone : S.P ω (S.oE ω) = none := by
      cases h : S.P ω (S.oE ω) with
      | none => rfl
      | some a => exact absurd ⟨S.oE ω, by rw [h]; rfl⟩ hunmod
    exact (hin ω hnone).symm
  · exact absurd hG (mass_pos_of_nonempty S.pos hGne).ne'

/-! ### The structure with the constructed policy -/

/-- **The concrete structure with `Π* := Π*_c`**: every other field unchanged (`Π†`, `Π̈`, `R`,
`P` do not depend on `Π*`).
Source: mandate T4(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def withPolSC (c₀ : OC) : ConcreteDS Ω OI OE AI AE DI DE DB OH OC :=
  { S with polS := S.polSC c₀ }

/-- Supporting lemma: the derived policies of `withPolSC` are those of `S`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem withPolSC_polD (c₀ : OC) : (S.withPolSC c₀).polD = S.polD := rfl

/-- **Under inertness, the constructed policy satisfies `hlink`** — the hypothesis (iii) of
"`Π̈ = R` in fact" (`aE_follows_R_of_udtRuleAt`, `polE_follows_R`) is discharged for `withPolSC`.
Source: mandate T4(b)(ii), T13(c)
Kind: L
Fidelity: exact
Hyps: none -/
theorem withPolSC_hlink {c₀ : OC} (hin : S.SideChannelInert c₀) :
    ∀ ω, (S.withPolSC c₀).P ω ((S.withPolSC c₀).oE ω) = none →
      (S.withPolSC c₀).polD ω ((S.withPolSC c₀).O ω) =
        (S.withPolSC c₀).polS ω ((S.withPolSC c₀).O ω) :=
  fun ω h => (hin ω h).symm

/-- **`Π* ⊑ D_{I,B}` on `withPolSC`.**
Source: mandate T4(b), T7
Kind: L
Fidelity: exact
Hyps: none -/
theorem withPolSC_polS_sub (c₀ : OC) :
    IsSubvariable (S.withPolSC c₀).DIB (S.withPolSC c₀).polS := S.polSC_sub_DIB c₀

end ConcreteDS

end Cleanroom.Udt.UdtCommTrust
