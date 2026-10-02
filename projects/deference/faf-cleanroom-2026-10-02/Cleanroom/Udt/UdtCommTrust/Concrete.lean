import Cleanroom.Udt.UdtCommTrust.Determination

/-!
# `Cleanroom.Udt.UdtCommTrust.Concrete`: the concrete decision structure, modification,
minimally modifying actions, communicative alternatives, stability, internal drive

Work package `udt-comm-trust`, targets T8 (the concrete structure), T9 (minimally modifying
actions and communicative alternatives) and T12 (stability, internally-driven recommendations).
Sources: [[communication-trust-translated]] lines 396–456 and 490–499; the original
`references/communication&trust.md` lines 456–470 (`Π̈ ≡ R`) and 507–516 (the Stability remark
distinguishing "this particular recommendation is followed" from "whatever the recommendation is, it
is followed").

## Representation (mandate §3, with two departures recorded in the findings)

* The instance index is the value type `OE` of `Ö` (the paper's `range Ö`). Caveat (audit r1): an
  instance `ö` whose observation is never realized is *not* inert everywhere — `Π̈(ω)(ö)` is then the
  junk `Ä(w₀)` (through `rho`'s off-range branch), so `Follows`/`{Π̈ = R}` compare a recommendation
  at such an `ö` with junk, and `Stable`/`StableR`/`InternallyDriven`/`HasCA` quantify over
  unrealized `(ȯ, ö)` too. Every witness realizes every value of `OI` and `OE`, so nothing here
  is exercised off-range; the theorems whose hypotheses mention `{Π̈ = R}` (T10(ii), T11(b),
  T13(b)) are, on a structure with an unrealized recommended instance, `Classical.choice`-sensitive
  in that hypothesis.
* **Message semantics** `s : OE → OH → Option AE` and **side-channel impact** `p : OE → OC → Option AE`
  read the *whole* semantic observation / side channel and choose their instance by the first
  argument; the paper's `s_ö : range Ô_ö ⇀ range Ä` is recovered when `OH` is a product over
  instances and `s ö` reads its `ö`-coordinate. `none` is the paper's `⊥` (silence / no forcing).
* The **recommendation** `R ω : OE → Option AE` and the **forced policy** `P ω : OE → Option AE`
  are derived from `Ô` and `Ǒ`; both are subvariables of `Ȯ` by construction.
* The **instance factorizations** ("`Π*` factors as `(Π*_ö)_ö`", …) are bundled in the predicate
  `InstanceFactored` rather than taken as fields: no theorem of the paper uses them, so the
  theorems below are stated without them (stronger), and a witness that satisfies the predicate is
  supplied in `Witness.lean`. The paper's family factorizations of `B, Ȧ, Ä, A, Ȯ` are not
  representable on the realized-instance reading of the abstract structure (`Ä = Π̈(Ö)` is one
  action, not a tuple); see the findings, item T8.
-/

namespace Cleanroom.Udt.UdtCommTrust

open Cleanroom.Udt.UdtPolicyCalc Finset

variable (Ω : Type) (OI OE AI AE DI DE DB OH OC : Type)

/-- **The concrete decision structure**: an abstract decision structure with message semantics
`s` (each instance's semantic observation either recommends an external action or is silent)
and side-channel impact `p` (each instance's side channel either forces an external action or does
nothing). Zero cases: `none` is silence / no forcing.
Source: [[communication-trust-translated]] lines 396–436 (udt-rep-017); original lines 400–440
Kind: D
Fidelity: variant: `s ö`, `p ö` read the whole `Ô` / `Ǒ` (instance selection by `ö`); instance factorizations in `InstanceFactored`, not fields; §3 (c)
Hyps: n/a -/
structure ConcreteDS [Fintype Ω] extends AbstractDS Ω OI OE AI AE DI DE DB OH OC where
  /-- Message semantics `s_ö : Ô ⇀ Ä`. -/
  s : OE → OH → Option AE
  /-- Side-channel impact `p_ö : Ǒ ⇀ Ä`. -/
  p : OE → OC → Option AE

namespace ConcreteDS

variable {Ω OI OE AI AE DI DE DB OH OC}
variable [Fintype Ω] [DecidableEq Ω]
variable (S : ConcreteDS Ω OI OE AI AE DI DE DB OH OC)

/-- `[[·]]_Ô` from `Ȯ` (junk `Ô(w₀)` off the range).
Source: [[communication-trust-translated]] line 420 (`[[Ȯ]]_{Ô_ö}`)
Kind: D
Fidelity: exact on the range
Hyps: n/a -/
noncomputable def projOH : OI → OH := projOf S.oI S.oH S.w₀

/-- `[[·]]_Ǒ` from `Ȯ`.
Source: [[communication-trust-translated]] line 428
Kind: D
Fidelity: exact on the range
Hyps: n/a -/
noncomputable def projOC : OI → OC := projOf S.oI S.oC S.w₀

/-- Supporting lemma `projOH_oI`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem projOH_oI (ω : Ω) : S.projOH (S.oI ω) = S.oH ω := projOf_spec S.oH_oI _ _

/-- Supporting lemma `projOC_oI`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem projOC_oI (ω : Ω) : S.projOC (S.oI ω) = S.oC ω := projOf_spec S.oC_oI _ _

/-- **The recommendation `R`**: `R(ω)(ö) = s_ö([[Ȯ(ω)]]_Ô)`, a partial external policy (a value
of one random variable). Zero case: `none` where the semantics are silent.
Source: [[communication-trust-translated]] lines 418–422 (udt-rep-017)
Kind: D
Fidelity: exact
Hyps: n/a -/
def R (ω : Ω) : OE → Option AE := fun e => S.s e (S.oH ω)

/-- **The forced policy `P`**: `P(ω)(ö) = p_ö([[Ȯ(ω)]]_Ǒ)`.
Source: [[communication-trust-translated]] lines 426–430 (udt-rep-017)
Kind: D
Fidelity: exact
Hyps: n/a -/
def P (ω : Ω) : OE → Option AE := fun e => S.p e (S.oC ω)

/-- `R` written through the projection `[[·]]_Ô`, as the paper does.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem R_eq_projOH (ω : Ω) : S.R ω = fun e => S.s e (S.projOH (S.oI ω)) := by
  funext e; simp [R, projOH_oI]

/-- **`R` is a subvariable of `Ȯ`.**
Source: [[communication-trust-translated]] line 422
Kind: L
Fidelity: exact
Hyps: none -/
theorem R_sub : IsSubvariable S.oI S.R := S.oH_oI.comp fun h => fun e => S.s e h

/-- **`P` is a subvariable of `Ȯ`.**
Source: [[communication-trust-translated]] line 430
Kind: L
Fidelity: exact
Hyps: none -/
theorem P_sub : IsSubvariable S.oI S.P := S.oC_oI.comp fun c => fun e => S.p e c

/-! ### "`Π̈ = R`" and modification -/

/-- **An external policy follows a partial recommendation**: `π ö = a` wherever `r ö = some a`
(udt-rep-017's reading of the paper's "for all `ö ∈ dom r`, `π̈(ö) = r(ö)`"; the original writes
`Π̈ ≡ R`).
Source: [[communication-trust-translated]] line 424; original line 460
Kind: D
Fidelity: exact
Hyps: n/a -/
def Follows (π : OE → AE) (r : OE → Option AE) : Prop := ∀ e a, r e = some a → π e = a

instance [Fintype OE] [Fintype AE] [DecidableEq AE] (π : OE → AE) (r : OE → Option AE) :
    Decidable (Follows π r) := by unfold Follows; infer_instance

variable [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE]

/-- **The event `{Π̈ = R}`**: the worlds whose external policy follows their recommendation.
Source: [[communication-trust-translated]] line 424 (udt-rep-017 flag: `Π̈ = R` is one event over `Ω`, not a statement about all `ô`)
Kind: D
Fidelity: exact (udt-rep-017's reading)
Hyps: n/a -/
noncomputable def evFollowsR : Finset Ω := event fun ω => Follows (S.polE ω) (S.R ω)

/-- Supporting lemma `mem_evFollowsR`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mem_evFollowsR {ω : Ω} : ω ∈ S.evFollowsR ↔ Follows (S.polE ω) (S.R ω) := by
  simp [evFollowsR]

/-- **`P(Π̈ = R) = 1` means `{Π̈ = R} = Ω`** on the support.
Source: mandate T10(ii)
Kind: L
Fidelity: exact
Hyps: none -/
theorem evFollowsR_eq_univ_iff : mass S.μ.w S.evFollowsR = 1 ↔ S.evFollowsR = univ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ S.evFollowsR := by
      by_contra hall
      push_neg at hall
      exact hne (Finset.eq_univ_iff_forall.2 hall)
    have h1 : mass S.μ.w S.evFollowsR + mass S.μ.w (univ \ S.evFollowsR) = 1 := by
      rw [mass, mass, ← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset
        (Finset.subset_univ _)]
      exact S.μ.sum_one
    have h2 : 0 < mass S.μ.w (univ \ S.evFollowsR) :=
      mass_pos_of_nonempty S.pos ⟨ω, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hω⟩⟩
    linarith
  · intro h
    rw [h]
    exact mass_univ S.μ

/-- **Modification** occurs in `ω` when some instance's side channel forces an action
(`dom P(ω) ≠ ∅`).
Source: [[communication-trust-translated]] lines 432–434 (udt-rep-017)
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsModified (ω : Ω) : Prop := ∃ e, (S.P ω e).isSome

instance (ω : Ω) : Decidable (S.IsModified ω) := by
  unfold IsModified; infer_instance

/-- The modification event.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def evMod : Finset Ω := event S.IsModified

/-- **The modification probability `m(e) = P(dom P ≠ ∅ ∣ e)`**, with junk `0` on an empty `e` —
this package's convention; the paper states none for conditional probabilities (udt-rep-018 flag).
Source: [[communication-trust-translated]] line 434 (udt-rep-017)
Kind: D
Fidelity: variant: junk `0` on the empty event
Hyps: n/a -/
noncomputable def modProb (e : Finset Ω) : ℝ := condProbJunk S.μ.w S.evMod e 0

variable [DecidableEq AI]

/-- `m(Π*(ȯ, ö) = a)`.
Source: [[communication-trust-translated]] line 446
Kind: D
Fidelity: exact (junk `0` when the event is empty)
Hyps: n/a -/
noncomputable def modS (o : OI) (e : OE) (a : AI × AE) : ℝ := S.modProb (S.evS o e a)

/-! ### T9: minimally modifying actions and communicative alternatives -/

/-- **`a` is minimally modifying at `(ȯ, ö)`**: `m(Π*(ȯ,ö) = a) ≤ m(Π*(ȯ,ö) = a')` for every
action `a'` attained by some chosen policy at `(ȯ, ö)` (the paper's `min_{a' ∈ range A_ö}`;
restricting to attained `a'` matters because an unattained `a'` has the junk value `0`). "Attained
at `(ȯ,ö)` by some chosen policy" is this package's reading of the paper's `range A_ö` (a choice,
sensible under junk `0`). `a` itself is *not* required to be attained: an unattained `a` has
`m = 0` and is vacuously minimally modifying (audit r1); every consumer of `MinMod` in this package
produces an attained `a` (`evS_nonempty_of_isArgmax`, `isCA_nonempty`).
Source: [[communication-trust-translated]] lines 444–447 (udt-rep-018)
Kind: D
Fidelity: exact over attained `a'`; junk `0` disclosed; `a` unrestricted (vacuous when unattained)
Hyps: n/a -/
def MinMod (o : OI) (e : OE) (a : AI × AE) : Prop :=
  ∀ a', (S.evS o e a').Nonempty → S.modS o e a ≤ S.modS o e a'

/-- **`c` is a communicative alternative to `a` at `(ȯ, ö)`**: `c` is minimally modifying and, for
every external policy `π̈`, `P(Π̈ = π̈ ∣ Π*(ȯ,ö) = a) = P(Π̈ = π̈ ∣ Π*(ȯ,ö) = c, Π̈ = R)`, both with
junk `0` on an empty conditioning event.
Source: [[communication-trust-translated]] lines 449–456 (udt-rep-018); original lines 458–466
Kind: D
Fidelity: exact (junk `0` disclosed; `isCA_nonempty` is its consequence)
Hyps: n/a -/
def IsCA (o : OI) (e : OE) (a c : AI × AE) : Prop :=
  S.MinMod o e c ∧ ∀ π : OE → AE,
    condProbJunk S.μ.w (S.evPolE π) (S.evS o e a) 0 =
      condProbJunk S.μ.w (S.evPolE π) (S.evS o e c ∩ S.evFollowsR) 0

/-- **The structure has communicative alternatives**: every attained action at every input has one.
Source: [[communication-trust-translated]] line 458 ("has communicative alternatives"; udt-rep-018)
Kind: D
Fidelity: exact (over attained actions)
Hyps: n/a -/
def HasCA : Prop := ∀ o e a, (S.evS o e a).Nonempty → ∃ c, S.IsCA o e a c

/-- **With junk `0`, a communicative alternative of an attained action is attained together with
`Π̈ = R`**: summing the CA identity over `π̈` gives `1` on the left and `0` on the right unless
`{Π*(ȯ,ö) = c} ∩ {Π̈ = R}` is non-empty (T9(i)).
Source: mandate T9(i) (a consequence of the junk convention; udt-rep-018 flag)
Kind: L
Fidelity: exact
Hyps: none -/
theorem isCA_nonempty {o : OI} {e : OE} {a c : AI × AE} (h : S.IsCA o e a c)
    (ha : (S.evS o e a).Nonempty) : (S.evS o e c ∩ S.evFollowsR).Nonempty := by
  have hsum := sum_condProbJunk S.pos S.polE (S.evS o e a)
  have hsum' := sum_condProbJunk S.pos S.polE (S.evS o e c ∩ S.evFollowsR)
  rw [if_pos ha] at hsum
  have heq : ∑ π, condProbJunk S.μ.w (event fun ω => S.polE ω = π) (S.evS o e a) 0 =
      ∑ π, condProbJunk S.μ.w (event fun ω => S.polE ω = π) (S.evS o e c ∩ S.evFollowsR) 0 :=
    Finset.sum_congr rfl fun π _ => h.2 π
  rw [heq] at hsum
  rw [hsum] at hsum'
  by_contra hne
  rw [if_neg hne] at hsum'
  exact one_ne_zero hsum'

/-- **Under `P(Π̈ = R) = 1`, every minimally modifying action is its own communicative alternative**
(T9(ii)): the intersection with `{Π̈ = R} = Ω` is void.
Source: mandate T9(ii)
Kind: L
Fidelity: exact
Hyps: none -/
theorem isCA_self_of_minMod (h1 : mass S.μ.w S.evFollowsR = 1) {o : OI} {e : OE} {c : AI × AE}
    (hc : S.MinMod o e c) : S.IsCA o e c c := by
  refine ⟨hc, fun π => ?_⟩
  rw [(S.evFollowsR_eq_univ_iff).1 h1, Finset.inter_univ]

/-! ### T12: stability and internally-driven recommendations -/

/-- **`[Π̈ = r]_{−ö}`**: the other instances' external actions follow the particular partial
recommendation `r` (the original's `[Π̈ = r_ô]_{−ö}`, "this particular recommendation is followed").
Source: [[communication-trust-translated]] lines 493–495; original lines 507–509 (udt-rep-022, 2-008(d))
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def evFollowsMinus (r : OE → Option AE) (e : OE) : Finset Ω :=
  event fun ω => ∀ e' ≠ e, ∀ a, r e' = some a → S.polE ω e' = a

/-- **`{R_{−ö} = r_{−ö}}`**: the other instances were *told* `r` (the original's second reading,
"whatever the recommendation is, it is followed" contrasts with this; the translation drops it).
Source: original line 508 (udt-rep-2-008(d)); mandate T12
Kind: D
Fidelity: exact
Hyps: n/a -/
def evToldMinus (r : OE → Option AE) (e : OE) : Finset Ω :=
  event fun ω => ∀ e' ≠ e, S.R ω e' = r e'

/-- The event `{R = r}`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def evR (r : OE → Option AE) : Finset Ω := event fun ω => S.R ω = r

/-- Supporting lemma `mem_evR`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mem_evR {r : OE → Option AE} {ω : Ω} : ω ∈ S.evR r ↔ S.R ω = r := by simp [evR]

/-- **Stability of `r` (Π-form, as printed)**: for every instance `ö` that `r` addresses, every
internal observation `ȯ` at which the semantics produce `r ö`, every internal action `ȧ` and every
`ä' ≠ r ö`, `E[U ∣ Π*(ȯ,ö) = (ȧ, r ö), [Π̈ = r]_{−ö}] > E[U ∣ Π*(ȯ,ö) = (ȧ, ä'), [Π̈ = r]_{−ö}]`
(junk `−1`). The paper leaves `ȯ_ö` free; it is quantified over the internal observations that
produce `r ö`, which is what the Advice-Following proof uses (mandate T12). Two caveats (audit r1):
the quantifier runs over the value type `OI`, so at an unrealized `ȯ` the guard
`s ö [[ȯ]]_Ô = some a₀` reads the junk projection `Ô(w₀)`; and junk `−1` makes the inequality
demand, for *every* `ȧ : AI`, that `{Π*(ȯ,ö) = (ȧ, r ö)} ∩ [Π̈ = r]_{−ö}` be non-empty
(`stable_nonempty`) — with `|AI| ≥ 2` this is stronger than a reading over attained `ȧ`. Every
witness realizes every `ȯ` and has `AI = Fin 1`, so neither caveat is exercised.
Source: [[communication-trust-translated]] lines 491–495 (udt-rep-022); original lines 507–512
Kind: D
Fidelity: variant: junk `−1` (forces attainment of `(ȧ, r ö)` for every `ȧ`); `ȯ_ö` over the value type
Hyps: n/a -/
def Stable (r : OE → Option AE) : Prop :=
  ∀ e a₀, r e = some a₀ → ∀ o, S.s e (S.projOH o) = some a₀ → ∀ (ai : AI) (a' : AE), a' ≠ a₀ →
    condExpJunk S.μ.w S.U (S.evS o e (ai, a₀) ∩ S.evFollowsMinus r e) (-1) >
      condExpJunk S.μ.w S.U (S.evS o e (ai, a') ∩ S.evFollowsMinus r e) (-1)

/-- **Stability of `r` (R-form)**: as `Stable`, conditioning on `{R_{−ö} = r_{−ö}}` (the other
instances were told `r`) instead of `[Π̈ = r]_{−ö}` (they follow `r`). Attribution (corrected in
audit r1): the original's Stability remark (line ~508) contrasts two events about `Π̈`
(`[Π̈ = r_ô]_{−ö}` versus `[Π̈ = R]_{−ö}`), neither of which is this one; the told event is the one
the original's *proof* decomposes over before its "By (1)" step (line ~536, `r_{ô'} − ö`). The
remark motivates this definition; it does not state it. Same junk caveats as `Stable`
(`stableR_nonempty`).
Source: original line ~536 (the proof's decomposition over `R_{−ö}`; udt-rep-2-008(d)); mandate T12
Kind: D
Fidelity: variant: the told form, which is what the paper's proof supports; junk `−1` as in `Stable`
Hyps: n/a -/
def StableR (r : OE → Option AE) : Prop :=
  ∀ e a₀, r e = some a₀ → ∀ o, S.s e (S.projOH o) = some a₀ → ∀ (ai : AI) (a' : AE), a' ≠ a₀ →
    condExpJunk S.μ.w S.U (S.evS o e (ai, a₀) ∩ S.evToldMinus r e) (-1) >
      condExpJunk S.μ.w S.U (S.evS o e (ai, a') ∩ S.evToldMinus r e) (-1)

/-- **Internally-driven recommendations** (definition of record, guarded): `P(R = r ∣ Π*(ȯ,ö) =
(ȧ, ä))` does not depend on `ä`, *among the external actions `ä` attained at `(ȯ,ö)` with `ȧ`* —
i.e. wherever both conditional probabilities are defined. This is the paper's identity read with
conditional probabilities defined on positive-mass events only. The unguarded junk-`0` form is
`InternallyDrivenJunk`; audit r1 found that the unguarded form, together with the pointwise UDT
rule and told-form stability, is contradictory on every structure with two external actions
(`udtRule_internallyDrivenJunk_stableR_inconsistent`), so the theorems take this form.
Source: [[communication-trust-translated]] lines 497–499 (udt-rep-022); original lines 514–516
Kind: D
Fidelity: exact (the identity where both sides are defined); quantifier over the value types `OI`, `OE`
Hyps: n/a -/
def InternallyDriven : Prop :=
  ∀ (o : OI) (e : OE) (ai : AI) (a a' : AE) (r : OE → Option AE),
    (S.evS o e (ai, a)).Nonempty → (S.evS o e (ai, a')).Nonempty →
    condProbJunk S.μ.w (S.evR r) (S.evS o e (ai, a)) 0 =
      condProbJunk S.μ.w (S.evR r) (S.evS o e (ai, a')) 0

/-- **Internally-driven recommendations, unguarded (junk `0`)**: the identity for *all* `ä, ä'`,
with junk `0` on an empty conditioning event. Stronger than `InternallyDriven`: summed over `r` it
forces the events `{Π*(ȯ,ö) = (ȧ, ä)}` to be all empty or all non-empty as `ä` varies
(`internallyDrivenJunk_nonempty`), which is what makes it inconsistent with the pointwise UDT
rule under stability (audit r1, B1). Kept as the record of the package's first reading and as the
hypothesis of the inconsistency theorem; the witnesses prove it, and it implies the guarded form.
Source: [[communication-trust-translated]] lines 497–499 (udt-rep-022), read with junk `0`
Kind: D
Fidelity: stronger: junk `0` on empty events turns the identity into an attainment constraint
Hyps: n/a -/
def InternallyDrivenJunk : Prop :=
  ∀ (o : OI) (e : OE) (ai : AI) (a a' : AE) (r : OE → Option AE),
    condProbJunk S.μ.w (S.evR r) (S.evS o e (ai, a)) 0 =
      condProbJunk S.μ.w (S.evR r) (S.evS o e (ai, a')) 0

/-- **The unguarded form implies the guarded one.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem InternallyDrivenJunk.toInternallyDriven (h : S.InternallyDrivenJunk) :
    S.InternallyDriven := fun o e ai a a' r _ _ => h o e ai a a' r

/-- **With junk `0`, unguarded internal drive forces the events `{Π*(ȯ,ö) = (ȧ, ä)}` to be all
empty or all non-empty as `ä` varies** (sum the identity over `r`). This is the hinge of the audit
r1 inconsistency: it makes every `(ȧ, ä)` attained once one is.
Source: mandate T12 (udt-rep-022 flag, quantified)
Kind: L
Fidelity: exact
Hyps: none -/
theorem internallyDrivenJunk_nonempty (h : S.InternallyDrivenJunk) {o : OI} {e : OE} {ai : AI}
    {a a' : AE} (ha : (S.evS o e (ai, a)).Nonempty) : (S.evS o e (ai, a')).Nonempty := by
  have h1 := sum_condProbJunk S.pos S.R (S.evS o e (ai, a))
  have h2 := sum_condProbJunk S.pos S.R (S.evS o e (ai, a'))
  rw [if_pos ha] at h1
  have heq : ∑ r, condProbJunk S.μ.w (event fun ω => S.R ω = r) (S.evS o e (ai, a)) 0 =
      ∑ r, condProbJunk S.μ.w (event fun ω => S.R ω = r) (S.evS o e (ai, a')) 0 :=
    Finset.sum_congr rfl fun r _ => h o e ai a a' r
  rw [heq] at h1
  rw [h1] at h2
  by_contra hne
  rw [if_neg hne] at h2
  exact one_ne_zero h2

/-- **With junk `−1`, stability forces the `(ȧ, r ö)`-events to be non-empty**: an empty left
event scores `−1`, which is never `>` anything the right side can score.
Source: mandate T12 (udt-rep-022's "the `−1` junk value makes stable depend on the convention", quantified)
Kind: L
Fidelity: exact
Hyps: none -/
theorem stable_nonempty {r : OE → Option AE} (h : S.Stable r) {e : OE} {a₀ : AE}
    (hr : r e = some a₀) {o : OI} (ho : S.s e (S.projOH o) = some a₀) (ai : AI) (a' : AE)
    (ha' : a' ≠ a₀) : (S.evS o e (ai, a₀) ∩ S.evFollowsMinus r e).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have := h e a₀ hr o ho ai a' ha'
  rw [hne, condExpJunk_of_empty] at this
  by_cases hne' : (S.evS o e (ai, a') ∩ S.evFollowsMinus r e).Nonempty
  · exact absurd this (not_lt.2 (junk_lt_of_nonempty S.pos S.U_nonneg hne').le)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne'
    rw [hne', condExpJunk_of_empty] at this
    exact lt_irrefl _ this

/-- **With junk `−1`, told-form stability forces the `(ȧ, r ö)`-events (with the told event) to be
non-empty**, for every `ȧ`: the mirror of `stable_nonempty` for `StableR`. Used by "`Π̈ = R` in
fact": it is what makes the recommended action attained alongside any chosen internal action.
Source: mandate T12 (udt-rep-022's junk flag), for the told form
Kind: L
Fidelity: exact
Hyps: none -/
theorem stableR_nonempty {r : OE → Option AE} (h : S.StableR r) {e : OE} {a₀ : AE}
    (hr : r e = some a₀) {o : OI} (ho : S.s e (S.projOH o) = some a₀) (ai : AI) (a' : AE)
    (ha' : a' ≠ a₀) : (S.evS o e (ai, a₀) ∩ S.evToldMinus r e).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have := h e a₀ hr o ho ai a' ha'
  rw [hne, condExpJunk_of_empty] at this
  by_cases hne' : (S.evS o e (ai, a') ∩ S.evToldMinus r e).Nonempty
  · exact absurd this (not_lt.2 (junk_lt_of_nonempty S.pos S.U_nonneg hne').le)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne'
    rw [hne', condExpJunk_of_empty] at this
    exact lt_irrefl _ this

/-! ### Instance factorizations (definition of record, not used by any theorem) -/

/-- **The instance factorizations** of the paper's Instance Structure definition, for the objects
that exist on this representation: `Π*` factors as `(Π*_ö)_ö` and `Π†` factors as `(Π†_ö)_ö`
(every combination of realized instance policies is realized), and `Ô`, `Ǒ` are subvariables of
`Ȯ` (fields of the abstract structure). Not a hypothesis of any theorem below.
Source: [[communication-trust-translated]] lines 399–413 (udt-rep-017)
Kind: D
Fidelity: weaker: `B, Ȧ, Ä, A, Ȯ` are not families on the realized-instance reading (findings, T8)
Hyps: n/a -/
def InstanceFactored : Prop :=
  FactorsAsFam (fun ω e => fun o => S.polS ω (o, e)) ∧
    FactorsAsFam (fun ω e => fun o => S.polD ω (o, e))

end ConcreteDS

end Cleanroom.Udt.UdtCommTrust
