import Cleanroom.Udt.UdtCommTrust.SelfTrust

/-!
# `Cleanroom.Udt.UdtCommTrust.Advice`: Advice-Following, termwise

Work package `udt-comm-trust`, target T13 (load-bearing 2). Sources:
[[communication-trust-translated]] lines 501–521; the original `references/communication&trust.md`
lines 524–549 (theorem and proof); udt-rep-023, 2-010, bli-paper-089.

Three theorems and a corollary:

* `adviceFollowing_R` (**AF-R**): the theorem the paper's proof supports, for each internal action
  separately, with stability in the *told* form (`StableR`). No `max`/`argmax` interchange and no
  use of `P(Π̈ = R) = 1`. Its one hypothesis beyond the paper's list is `FactorsAsFam S.R`, the
  instance factorization of the recommendation (a clause of the paper's Instance Structure that the
  proof uses silently: it makes "the recommendation `a₀` here together with the others' realized
  recommendations" a realized recommendation, so that stability applies to it).
* `adviceFollowing_Pi` (**AF-Π**): the paper's form, with stability in the printed *followed* form
  (`Stable`), `P(Π̈ = R) = 1`, and the identification hypothesis `Faithful` — the paper's step
  "By (1)" is valid exactly when `[Π̈ = r]_{−ö}` and `{R_{−ö} = r_{−ö}}` coincide.
* `faithful_of_nonsilent`: `Faithful` holds under `P(Π̈ = R) = 1` whenever no realized
  recommendation is silent at any instance.
* `aE_follows_R_of_udtRuleAt` (**"`Π̈ = R` in fact", per world**): if the chosen policy at `ω` is
  a UDT argmax at `ω`'s own realized input, no instance receives a recommendation and a modification
  at once, `Π*` means what the paper says (what runs when unmodified), and AF-R's hypotheses hold,
  then `ω`'s external action is its recommendation. `polE_follows_R` (**the corollary as printed**)
  is this at every world with the pointwise rule and `R ⊑ D_{I,B}`. The paper's `argmax_ä max_ȧ`
  belongs here, where it is valid.
* `udtRule_internallyDrivenJunk_stableR_inconsistent` (audit r1 finding): with the *unguarded*
  junk-`0` internal drive, the pointwise rule and told-form stability are contradictory as soon as
  a recommendation is non-silent and there are two external actions. The theorems above take the
  guarded `InternallyDriven` for this reason.
* `AbstractDS.udtRule_of_const` (T14(b)): a constant chosen policy satisfies the pointwise rule on
  every structure.
-/

namespace Cleanroom.Udt.UdtCommTrust

namespace ConcreteDS

open Cleanroom.Udt.UdtPolicyCalc Finset

variable {Ω OI OE AI AE DI DE DB OH OC : Type}
variable [Fintype Ω] [DecidableEq Ω] [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE]
  [DecidableEq AI]
variable (S : ConcreteDS Ω OI OE AI AE DI DE DB OH OC)

/-! ### `r_{−ö}` and `R_{−ö}` -/

/-- `r_{−ö}`: the partial recommendation `r` with instance `ö` blanked.
Source: original line 536 (`r_ô − ö`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def minus (e : OE) (r : OE → Option AE) : OE → Option AE := fun e' => if e' = e then none else r e'

/-- `R_{−ö}` as a random variable.
Source: original line 536
Kind: D
Fidelity: exact
Hyps: n/a -/
def Rminus (e : OE) (ω : Ω) : OE → Option AE := minus e (S.R ω)

/-- Supporting lemma `minus_eq_iff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem minus_eq_iff (e : OE) (r r' : OE → Option AE) :
    minus e r = minus e r' ↔ ∀ e' ≠ e, r e' = r' e' := by
  constructor
  · intro h e' he'
    have := congrFun h e'
    simpa [minus, he'] using this
  · intro h
    funext e'
    by_cases he' : e' = e
    · simp [minus, he']
    · simp [minus, he', h e' he']

/-- Supporting lemma `mem_evToldMinus_iff`: `{R_{−ö} = r_{−ö}}` is the fibre of `R_{−ö}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_evToldMinus_iff {r : OE → Option AE} {e : OE} {ω : Ω} :
    ω ∈ S.evToldMinus r e ↔ S.Rminus e ω = minus e r := by
  simp only [evToldMinus, mem_event, Rminus, minus_eq_iff]

/-- Supporting lemma `condProbJunk_nonneg`: with junk `0`, a junk conditional probability is
non-negative.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condProbJunk_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 < w ω) (E F : Finset Ω) :
    0 ≤ condProbJunk w E F 0 := by
  by_cases hF : F.Nonempty
  · rw [condProbJunk_of_nonempty hw hF]
    exact div_nonneg (mass_nonneg (fun ω => (hw ω).le) _) (mass_nonneg (fun ω => (hw ω).le) _)
  · rw [Finset.not_nonempty_iff_eq_empty] at hF
    subst hF
    exact le_of_eq (condProbJunk_of_empty _ _).symm

/-- **The law of `R_{−ö}` given an event is the sum of the laws of `R` over the compatible `r`**
(with junk `0` on both sides for an empty event).
Source: none: infrastructure (the "decompose over `r_{−ö}`" step of the Advice-Following proof)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condProb_Rminus_eq_sum (e : OE) (z : OE → Option AE) (F : Finset Ω) :
    condProbJunk S.μ.w (event fun ω => S.Rminus e ω = z) F 0 =
      ∑ r, if minus e r = z then condProbJunk S.μ.w (S.evR r) F 0 else 0 := by
  by_cases hF : F.Nonempty
  · rw [condProbJunk_of_nonempty S.pos hF]
    have h1 : (event fun ω => S.Rminus e ω = z) ∩ F = event fun ω => S.Rminus e ω = z ∧ ω ∈ F := by
      ext ω; simp
    rw [h1, AbstractDS.mass_eq_sum_fiber S.μ.w _ S.R, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs with hr
    · rw [condProbJunk_of_nonempty S.pos hF, div_eq_mul_inv]
      congr 2
      ext ω
      simp only [mem_event, Finset.mem_inter, mem_evR]
      constructor
      · rintro ⟨⟨-, hω⟩, hr'⟩
        exact ⟨hr', hω⟩
      · rintro ⟨hr', hω⟩
        exact ⟨⟨by rw [Rminus, hr', hr], hω⟩, hr'⟩
    · have hempty : (event fun ω => (S.Rminus e ω = z ∧ ω ∈ F) ∧ S.R ω = r) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro ω hω
        rw [mem_event] at hω
        exact hr (by rw [← hω.2]; exact hω.1.1)
      rw [hempty]
      simp [mass]
  · rw [Finset.not_nonempty_iff_eq_empty] at hF
    subst hF
    simp [condProbJunk_of_empty]

/-- Supporting lemma `Rminus_eq_iff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem Rminus_eq_iff {e : OE} {ω ω' : Ω} :
    S.Rminus e ω = S.Rminus e ω' ↔ ∀ e' ≠ e, S.R ω e' = S.R ω' e' := minus_eq_iff e _ _

/-- Supporting lemma `filter_Rminus_eq`: the `R_{−ö}`-fibre of `ω₁` inside `F` is
`F ∩ {R_{−ö} = R(ω₁)_{−ö}}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem filter_Rminus_eq (F : Finset Ω) (e : OE) (ω₁ : Ω) :
    (F.filter fun ω => S.Rminus e ω = S.Rminus e ω₁) = F ∩ S.evToldMinus (S.R ω₁) e := by
  ext ω
  simp only [Finset.mem_filter, Finset.mem_inter, evToldMinus, mem_event, Rminus_eq_iff,
    Finset.mem_univ, true_and]

/-- Supporting lemma `evToldMinus_congr`: `{R_{−ö} = r_{−ö}}` depends on `r` only off `ö`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evToldMinus_congr {r r' : OE → Option AE} {e : OE} (h : ∀ e' ≠ e, r e' = r' e') :
    S.evToldMinus r e = S.evToldMinus r' e := by
  ext ω
  simp only [evToldMinus, mem_event]
  exact ⟨fun hω e' he' => (hω e' he').trans (h e' he'),
    fun hω e' he' => (hω e' he').trans (h e' he').symm⟩

/-! ### T13(a): Advice-Following in the told form, termwise -/

/-- **Advice-Following, R-form (AF-R)** — the theorem the paper's proof supports, for each internal
action `ȧ` separately: if recommendations are internally driven, every realized recommendation is
stable in the told form (`StableR`), and the recommendation tuple factors by instance
(`FactorsAsFam S.R`), then at every realized internal observation `ȯ` whose semantics at `ö`
recommend `ä₀`, and every `ȧ` with `{Π*(ȯ,ö) = (ȧ, ä₀)}` attained,
`E[U ∣ Π*(ȯ,ö) = (ȧ, ä)] < E[U ∣ Π*(ȯ,ö) = (ȧ, ä₀)]` for every `ä ≠ ä₀`. Proof: if `(ȧ, ä)` is
unattained it scores the junk `−1`, strictly below the attained `(ȧ, ä₀)`; otherwise both sides
decompose over `R_{−ö}` (law of total expectation); the weights agree because internal drive makes
`P(R = r ∣ Π*(ȯ,ö) = (ȧ, ·))` independent of the external action among attained actions; on each
positive-weight fibre the combined recommendation (`ä₀` at `ö`, the fibre's values elsewhere) is
realized by the instance factorization, so `StableR` at that recommendation, *at the same `ȧ`*,
gives the strict termwise inequality; a positive-weight average of strict inequalities is strict.
**No `max`/`argmax` interchange and no use of `P(Π̈ = R) = 1`** (udt-rep-2-010). Squeeze caveat:
when `R_{−ö}` takes a single value on `{Π*(ȯ,ö) = (ȧ, ·)}` (one instance, or a constant
recommendation) the told event is `Ω` and `StableR` *is* the conclusion; the content is the
averaging over several told-fibres (`W2` has two).
Source: [[communication-trust-translated]] lines 501–512; original lines 524–541 (udt-rep-023, 2-010, bli-paper-089)
Kind: P
Fidelity: variant: stability in the told form (`StableR`, what the proof supports) and no `P(Π̈ = R) = 1`; conclusion exact
Hyps: (a) throughout: internal drive (guarded form) and stability are the theorem's conditions (2),(3); `FactorsAsFam S.R` is the paper's instance factorization of `Ȯ` used silently by the proof; `ȯ ∈ range Ȯ` is the paper's `ȯ_ö ∈ range Ȯ_ö`; attainment of `(ȧ, ä₀)` replaces a positivity side-condition; §3 (c) -/
theorem adviceFollowing_R (hID : S.InternallyDriven) (hStab : ∀ r ∈ Set.range S.R, S.StableR r)
    (hRfac : FactorsAsFam S.R) {o : OI} (ho : o ∈ Set.range S.oI) {e : OE} {a₀ : AE}
    (hs : S.s e (S.projOH o) = some a₀) (ai : AI) (hne : (S.evS o e (ai, a₀)).Nonempty)
    {a : AE} (ha : a ≠ a₀) : S.score o e (ai, a) < S.score o e (ai, a₀) := by
  by_cases hne' : (S.evS o e (ai, a)).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hne'
    exact S.score_lt_of_empty hne' hne
  simp only [AbstractDS.score]
  rw [condExpJunk_total S.pos S.U (S.Rminus e) hne' (-1),
    condExpJunk_total S.pos S.U (S.Rminus e) hne (-1)]
  have hw : ∀ z, condProbJunk S.μ.w (event fun ω => S.Rminus e ω = z) (S.evS o e (ai, a)) 0 =
      condProbJunk S.μ.w (event fun ω => S.Rminus e ω = z) (S.evS o e (ai, a₀)) 0 := by
    intro z
    rw [S.condProb_Rminus_eq_sum, S.condProb_Rminus_eq_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs
    · exact hID o e ai a a₀ r hne' hne
    · rfl
  simp_rw [hw]
  refine sum_mul_lt_sum_mul
    (fun z => condExpJunk S.μ.w S.U ((S.evS o e (ai, a)).filter fun ω => S.Rminus e ω = z) (-1))
    (fun z => condExpJunk S.μ.w S.U ((S.evS o e (ai, a₀)).filter fun ω => S.Rminus e ω = z) (-1))
    (fun z => condProbJunk S.μ.w (event fun ω => S.Rminus e ω = z) (S.evS o e (ai, a₀)) 0)
    (fun z => condProbJunk_nonneg S.pos _ _) ?_ (fun z hz => ?_)
  · have := sum_condProbJunk S.pos (S.Rminus e) (S.evS o e (ai, a₀))
    rw [if_pos hne] at this
    exact this
  · have hfib : ((S.evS o e (ai, a₀)).filter fun ω => S.Rminus e ω = z).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      rw [condProbJunk_of_nonempty S.pos hne, event_inter_eq_filter, hcon] at hz
      simp [mass] at hz
    obtain ⟨ω₁, hω₁⟩ := hfib
    rw [Finset.mem_filter] at hω₁
    obtain ⟨ω₂, rfl⟩ := ho
    obtain ⟨c, hc⟩ : ∃ c : OE → Option AE,
        c = fun e' => if e' = e then S.R ω₂ e' else S.R ω₁ e' := ⟨_, rfl⟩
    have hcreal : c ∈ Set.range S.R := by
      obtain ⟨ω₃, hω₃⟩ := hRfac c fun e' => by
        by_cases he' : e' = e
        · exact ⟨ω₂, by simp [hc, he']⟩
        · exact ⟨ω₁, by simp [hc, he']⟩
      exact ⟨ω₃, hω₃⟩
    have hce : c e = some a₀ := by
      have : c e = S.R ω₂ e := by simp [hc]
      rw [this]
      show S.s e (S.oH ω₂) = some a₀
      rw [← S.projOH_oI]
      exact hs
    have hmin : ∀ e' ≠ e, c e' = S.R ω₁ e' := fun e' he' => by simp [hc, he']
    have hE : ∀ b, ((S.evS (S.oI ω₂) e (ai, b)).filter fun ω => S.Rminus e ω = z) =
        S.evS (S.oI ω₂) e (ai, b) ∩ S.evToldMinus c e := by
      intro b
      rw [← hω₁.2, S.filter_Rminus_eq, S.evToldMinus_congr hmin]
    rw [hE, hE]
    exact hStab c hcreal e a₀ hce (S.oI ω₂) hs ai a ha

/-! ### T13(b): the paper's form, under `Faithful` -/

/-- **`Faithful`**: for every realized recommendation `r` and instance `ö`, the other instances
follow `r` only when they were told `r`: `[Π̈ = r]_{−ö} ⊆ {R_{−ö} = r_{−ö}}`. This is the
hypothesis under which the paper's step "By (1)" (replacing "told `r`" by "follow `r`", original
line 539) is valid; bli-paper-089's "the events must differ by a null set given the conditioning".
Source: original line 539; bli-paper-089 flag; mandate T13(b)
Kind: D
Fidelity: n/a (the proof's unstated hypothesis, named)
Hyps: n/a -/
def Faithful : Prop :=
  ∀ r ∈ Set.range S.R, ∀ e, ∀ ω ∈ S.evFollowsMinus r e, ω ∈ S.evToldMinus r e

/-- **Under `P(Π̈ = R) = 1`, being told `r` at the other instances implies following `r` there.**
Source: original line 539 (the direction "By (1)" does give)
Kind: L
Fidelity: exact
Hyps: none -/
theorem evToldMinus_subset_evFollowsMinus (h1 : mass S.μ.w S.evFollowsR = 1)
    (r : OE → Option AE) (e : OE) : S.evToldMinus r e ⊆ S.evFollowsMinus r e := by
  intro ω hω
  have hall := (S.evFollowsR_eq_univ_iff).1 h1
  have hfol : Follows (S.polE ω) (S.R ω) := by
    have : ω ∈ S.evFollowsR := by rw [hall]; exact Finset.mem_univ _
    simpa using this
  simp only [evToldMinus, mem_event] at hω
  simp only [evFollowsMinus, mem_event]
  intro e' he' a hra
  exact hfol e' a (by rw [hω e' he']; exact hra)

/-- **Under `P(Π̈ = R) = 1` and `Faithful`, the two conditioning events coincide**, so the printed
(followed-form) stability implies the told-form stability.
Source: original lines 507–509 (the Stability remark); mandate T13(b)
Kind: L
Fidelity: exact
Hyps: none -/
theorem stableR_of_stable (h1 : mass S.μ.w S.evFollowsR = 1) (hF : S.Faithful)
    {r : OE → Option AE} (hr : r ∈ Set.range S.R) (hs : S.Stable r) : S.StableR r := by
  intro e a₀ hra o ho ai a' ha'
  have heq : S.evToldMinus r e = S.evFollowsMinus r e :=
    Finset.Subset.antisymm (S.evToldMinus_subset_evFollowsMinus h1 r e) (hF r hr e)
  rw [heq]
  exact hs e a₀ hra o ho ai a' ha'

/-- **Advice-Following, Π-form (AF-Π)** — the paper's statement: with `P(Π̈ = R) = 1`, internally
driven recommendations, every realized recommendation stable in the printed (followed) form, and
`Faithful`, the recommended external action is strictly preferred at every `ȧ`. Derived from AF-R
via `stableR_of_stable`.
Source: [[communication-trust-translated]] lines 501–512; original lines 524–541 (udt-rep-023)
Kind: C
Fidelity: exact (the paper's hypotheses (1)–(4)) plus `Faithful`, the hypothesis the paper's proof uses without stating
Hyps: (a) throughout; `Faithful` is the proof's silent hypothesis; the rest as `adviceFollowing_R`; §3 (c) -/
theorem adviceFollowing_Pi (h1 : mass S.μ.w S.evFollowsR = 1) (hID : S.InternallyDriven)
    (hStab : ∀ r ∈ Set.range S.R, S.Stable r) (hF : S.Faithful) (hRfac : FactorsAsFam S.R)
    {o : OI} (ho : o ∈ Set.range S.oI) {e : OE} {a₀ : AE} (hs : S.s e (S.projOH o) = some a₀)
    (ai : AI) (hne : (S.evS o e (ai, a₀)).Nonempty) {a : AE} (ha : a ≠ a₀) :
    S.score o e (ai, a) < S.score o e (ai, a₀) :=
  S.adviceFollowing_R hID (fun r hr => S.stableR_of_stable h1 hF hr (hStab r hr)) hRfac ho hs ai
    hne ha

/-- **`Faithful` holds under `P(Π̈ = R) = 1` when no realized recommendation is silent at any
instance**: following `r` at `ö'` and following the (non-silent) actual recommendation there
forces the two to agree.
Source: mandate T13(b); bli-paper-089 flag
Kind: P
Fidelity: n/a
Hyps: (a); §3 (c) -/
theorem faithful_of_nonsilent (h1 : mass S.μ.w S.evFollowsR = 1)
    (hns : ∀ r ∈ Set.range S.R, ∀ e', (r e').isSome) : S.Faithful := by
  intro r hr e ω hω
  have hall := (S.evFollowsR_eq_univ_iff).1 h1
  have hfol : Follows (S.polE ω) (S.R ω) := by
    have : ω ∈ S.evFollowsR := by rw [hall]; exact Finset.mem_univ _
    simpa using this
  simp only [evFollowsMinus, mem_event] at hω
  simp only [evToldMinus, mem_event]
  intro e' he'
  obtain ⟨a, hra⟩ := Option.isSome_iff_exists.1 (hns r hr e')
  obtain ⟨b, hRb⟩ := Option.isSome_iff_exists.1 (hns (S.R ω) ⟨ω, rfl⟩ e')
  have h1' := hω e' he' a hra
  have h2' := hfol e' b hRb
  rw [hRb, hra, ← h2', h1']

/-! ### T13(c): "`Π̈ = R` in fact" -/

/-- **"`Π̈ = R` in fact", per world** — the fact at one world, with its hypotheses visible: if
(i) the chosen policy at `ω` is a UDT argmax *at `ω`'s own realized input* (`UdtRuleAt ω Ȯ(ω) Ö(ω)`),
(ii) no instance receives a recommendation and a modification at once, (iii) `Π*` means what the
paper says (the effective action equals the chosen action wherever the realized instance is
unforced: `Π†(ω)(O(ω)) = Π*(ω)(O(ω))` when `P(ω)(Ö(ω)) = none`), and (iv) AF-R's hypotheses hold,
then `ω`'s external action is its recommendation at its instance: `R(ω)(Ö(ω)) = some a → Ä(ω) = a`.
Proof: the chosen pair is `(ȧ*, ä*)`; told-form stability at `ω`'s own (realized) recommendation
forces `(ȧ*, a)` to be attained (`stableR_nonempty`); AF-R at `ȧ*` then scores `(ȧ*, a)` strictly
above `(ȧ*, ä*)` unless `ä* = a`, contradicting (i) — this is where the paper's `argmax_ä max_ȧ`
belongs, and it is valid here; (ii),(iii) turn the chosen action into the effective one, and
`Π̈(ω)(Ö(ω)) = Ä(ω)`. Uses no `P(Π̈ = R) = 1` and no all-or-nothing attainment: the guarded
`InternallyDriven` suffices. Audit r1 (B1) showed that the pointwise rule over the whole support
is inconsistent with unguarded internal drive whenever advice-following has bite; this per-world
form is what a nondegenerate prior can satisfy (`W2` at its following worlds, N+).
Source: original lines 543–549; [[communication-trust-translated]] lines 513–516 (udt-rep-2-010, bli-paper-089)
Kind: P
Fidelity: weaker: the rule is assumed at the one world and its realized input; the conclusion is at that world only (the printed clause is `polE_follows_R`)
Hyps: (a) throughout; (iii) is the paper's prose definition of `Π*` taken as a hypothesis because `Π*` is a field; §3 (c) -/
theorem aE_follows_R_of_udtRuleAt (ω : Ω) (hUdt : S.UdtRuleAt ω (S.oI ω) (S.oE ω))
    (hnosim : ∀ e o, (S.s e (S.projOH o)).isSome → S.p e (S.projOC o) = none)
    (hlink : ∀ ω, S.P ω (S.oE ω) = none → S.polD ω (S.O ω) = S.polS ω (S.O ω))
    (hID : S.InternallyDriven) (hStab : ∀ r ∈ Set.range S.R, S.StableR r)
    (hRfac : FactorsAsFam S.R) {a : AE} (hRa : S.R ω (S.oE ω) = some a) : S.aE ω = a := by
  have hs : S.s (S.oE ω) (S.projOH (S.oI ω)) = some a := by rw [S.projOH_oI]; exact hRa
  have hnoforce : S.P ω (S.oE ω) = none := by
    show S.p (S.oE ω) (S.oC ω) = none
    rw [← S.projOC_oI]
    exact hnosim (S.oE ω) (S.oI ω) (by rw [hs]; rfl)
  have hact : S.aE ω = (S.polS ω (S.oI ω, S.oE ω)).2 := by
    have h1 := S.polD_apply_O ω
    rw [hlink ω hnoforce] at h1
    have h2 : S.aE ω = (S.polS ω (S.O ω)).2 := by rw [h1]; rfl
    exact h2
  rw [hact]
  by_contra hne
  have hatt : (S.evS (S.oI ω) (S.oE ω) ((S.polS ω (S.oI ω, S.oE ω)).1, a)).Nonempty := by
    obtain ⟨ω'', hω''⟩ := S.stableR_nonempty (hStab (S.R ω) ⟨ω, rfl⟩) hRa hs
      (S.polS ω (S.oI ω, S.oE ω)).1 _ hne
    exact ⟨ω'', (Finset.mem_inter.1 hω'').1⟩
  have hlt := S.adviceFollowing_R hID hStab hRfac ⟨ω, rfl⟩ hs (S.polS ω (S.oI ω, S.oE ω)).1 hatt
    hne
  exact absurd (hUdt ((S.polS ω (S.oI ω, S.oE ω)).1, a)) (not_le.2 hlt)

/-- **"`Π̈ = R` in fact"** — the printed clause, with its hypotheses visible: if (i) the pointwise
UDT rule holds, (ii) no instance receives a recommendation and a modification at once, (iii) `Π*`
means what the paper says (as in `aE_follows_R_of_udtRuleAt`), (iv) `R ⊑ D_{I,B}`, and (v) AF-R's
hypotheses hold, then every realized instance's external action is its recommendation:
`R(ω)(ö) = some a → Π̈(ω)(ö) = a` for `ö ∈ range Ö`. Proof: the world `ω'` with `ω`'s dynamics
observing `ö` (agent-dynamic factorization) has `Π̈(ω)(ö) = Ä(ω')` and the same recommendation
(iv); apply the per-world theorem at `ω'`. The paper's "then `Π̈ = R` in fact" (original line 545)
conflates subjective probability one with fact (bli-paper-089); this corollary uses no
`P(Π̈ = R) = 1`. Its full package is satisfiable (the deterministic `Det` witness, N−: a constant
following `Π*`); on a nondegenerate prior the pointwise rule (i) fails wherever advice-following
has bite (`W2.not_udtRule`), which is why the per-world form carries the N+ witness.
Source: original lines 543–549; [[communication-trust-translated]] lines 513–516 (udt-rep-2-010, bli-paper-089)
Kind: C
Fidelity: exact for the clause, with the three hypotheses 2-010 names ((i),(ii),(iii)) plus (iv),(v); internal drive in the guarded form
Hyps: (a) throughout; (iii) is the paper's prose definition of `Π*` taken as a hypothesis because `Π*` is a field; §3 (c) -/
theorem polE_follows_R (hUdt : S.UdtRule)
    (hnosim : ∀ e o, (S.s e (S.projOH o)).isSome → S.p e (S.projOC o) = none)
    (hlink : ∀ ω, S.P ω (S.oE ω) = none → S.polD ω (S.O ω) = S.polS ω (S.O ω))
    (hR : IsSubvariable S.DIB S.R) (hID : S.InternallyDriven)
    (hStab : ∀ r ∈ Set.range S.R, S.StableR r) (hRfac : FactorsAsFam S.R) :
    ∀ ω, ∀ e ∈ Set.range S.oE, ∀ a, S.R ω e = some a → S.polE ω e = a := by
  intro ω e he a hRa
  obtain ⟨ω', hoe, hD⟩ := S.IB_fac e he (S.DIB ω) ⟨ω, rfl⟩
  have hR' : S.R ω' = S.R ω := hR ω' ω hD
  have hRa' : S.R ω' (S.oE ω') = some a := by rw [hoe, hR']; exact hRa
  rw [← hoe, S.polE_apply_of_DIB_eq hD.symm]
  exact S.aE_follows_R_of_udtRuleAt ω' (hUdt ω' _ _) hnosim hlink hID hStab hRfac hRa'

/-! ### Audit r1 finding: the unguarded internal drive is inconsistent with the pointwise rule -/

/-- **Under the pointwise UDT rule and unguarded internal drive, all attained actions with the same
internal component tie**: once `(ȧ, ä)` is attained, every `(ȧ, b)` is attained
(`internallyDrivenJunk_nonempty`), and the rule at a world choosing `(ȧ, b)` bounds `(ȧ, ä)`'s
score by it.
Source: audit r1 (B1), probe `VacuityPolEFollowsR.lean`
Kind: L
Fidelity: n/a
Hyps: none -/
theorem tie_of_udtRule_internallyDrivenJunk (hUdt : S.UdtRule) (hID : S.InternallyDrivenJunk)
    {o : OI} {e : OE} {ai : AI} {a : AE} (ha : (S.evS o e (ai, a)).Nonempty) (b : AE) :
    S.score o e (ai, a) ≤ S.score o e (ai, b) := by
  obtain ⟨ω, hω⟩ := S.internallyDrivenJunk_nonempty hID (a' := b) ha
  rw [AbstractDS.mem_evS] at hω
  have hArg : IsArgmax (S.score o e) (S.polS ω (o, e)) := hUdt ω o e
  rw [hω] at hArg
  exact hArg (ai, a)

/-- **Finding (audit r1, B1): the pointwise UDT rule, unguarded (junk-`0`) internal drive,
told-form stability of every realized recommendation and `FactorsAsFam R` are jointly
contradictory** on any structure where some world's recommendation at some instance is non-silent
and the external action type has two distinct elements. So the first version of "`Π̈ = R` in fact",
stated with `InternallyDrivenJunk`, had a hypothesis package with no model beyond the trivial
ones; the theorems above take the guarded `InternallyDriven` instead. This is a finding about the
junk-`0` convention for conditional probabilities, which the paper does not fix (udt-rep-022 flag),
not about the paper's clause.
Source: audit r1 (B1); the package's own conventions (mandate §3, junk `0`)
Kind: P
Fidelity: n/a (finding)
Hyps: (a); §3 (c) -/
theorem udtRule_internallyDrivenJunk_stableR_inconsistent (hUdt : S.UdtRule)
    (hID : S.InternallyDrivenJunk) (hStab : ∀ r ∈ Set.range S.R, S.StableR r)
    (hRfac : FactorsAsFam S.R) {ω : Ω} {e : OE} {a : AE} (hRa : S.R ω e = some a) {b : AE}
    (hb : b ≠ a) : False := by
  have hs : S.s e (S.projOH (S.oI ω)) = some a := by rw [S.projOH_oI]; exact hRa
  have hatt : (S.evS (S.oI ω) e ((S.polS ω (S.oI ω, e)).1, a)).Nonempty :=
    S.internallyDrivenJunk_nonempty hID (S.evS_self_nonempty ω (S.oI ω) e)
  have hlt := S.adviceFollowing_R hID.toInternallyDriven hStab hRfac ⟨ω, rfl⟩ hs
    (S.polS ω (S.oI ω, e)).1 hatt hb
  exact absurd (S.tie_of_udtRule_internallyDrivenJunk hUdt hID hatt b) (not_le.2 hlt)

end ConcreteDS

namespace AbstractDS

open Cleanroom.Udt.UdtPolicyCalc Finset

variable {Ω OI OE AI AE DI DE DB OH OC : Type}
variable [Fintype Ω] [DecidableEq Ω] [DecidableEq AI] [DecidableEq AE]
variable (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)

/-- **A constant chosen policy satisfies the pointwise UDT rule on every structure** (T14(b)): the
chosen action's event at every input is `Ω`, every other action's event is empty and scores the
junk `−1`. So "no `Π*` satisfies the rule" is false as long as `Π*` is a free field; the
self-referential difficulty (udt-rep-090) is confined to nondegenerate priors over chosen policies
(`W2.not_udtRule`) and to `Π*` tied to the dynamics (`hlink` in "`Π̈ = R` in fact").
Source: mandate T14(b) (udt-rep-2-005(b))
Kind: P
Fidelity: n/a (existence of a fixed point, on the pointwise reading)
Hyps: (a); §3 (c) -/
theorem udtRule_of_const (π : Policy (OI × OE) (AI × AE)) (h : ∀ ω, S.polS ω = π) :
    S.UdtRule := by
  intro ω o e x
  show S.score o e x ≤ S.score o e (S.polS ω (o, e))
  rw [h ω]
  by_cases hx : x = π (o, e)
  · rw [hx]
  · have hempty : S.evS o e x = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ω' hω'
      rw [AbstractDS.mem_evS, h ω'] at hω'
      exact hx hω'.symm
    have hne : (S.evS o e (π (o, e))).Nonempty := ⟨ω, by rw [AbstractDS.mem_evS, h ω]⟩
    exact (S.score_lt_of_empty hempty hne).le

end AbstractDS

end Cleanroom.Udt.UdtCommTrust
