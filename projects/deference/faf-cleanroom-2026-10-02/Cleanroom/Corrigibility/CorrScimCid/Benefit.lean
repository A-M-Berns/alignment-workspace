import Cleanroom.Corrigibility.CorrScimCid.Shutdown

/-!
# Props 6, 8, 9, the alignment identity, Theorem 10 and its vacuity (T5, T6)

The spine of Carey–Everitt §5.1–5.2 is one consistency step: at a human context where the agent
shuts down surely, `U = U_{S=0}` pointwise on the support (`US0val_eq_of_shut`, Pearl consistency
= `Scm.eval_doAt_of_eq`), so the two conditional expectations coincide and *need cannot be
realised there*. From it:

* **T5(a), the alignment identity** (`aligned_iff_forall_condEUS0_le`): shutdown alignment (Def. 7)
  is equivalent to "at no positive-probability human context is shutdown strictly better". The
  paper never says so; its Thm 10 proof handles the vigilance half through hypothesis (c)
  unnecessarily (`ensuresVigilance_of_aligned`).
* **Prop 9** (`aligned_of_instructable`), **Prop 8** (`beneficial_of_cautious_of_aligned`), **Prop 6**
  (`beneficial_of_instructable`), all through the key lemma
  `aligned_of_obedient_of_ensuresVigilance` (obedience + vigilance ⇒ alignment, no caution). The
  mandate's "conditioning on all parents = intervention" (T1 iii) is *not* needed: obedience is a
  statement under `do(H = 0)` holding at every support point, and consistency transports it to
  the event `{H = 0}`.
* **T6, Theorem 10 as printed** (`thm10_as_printed`) in both readings of its hypothesis (c), and the
  **vacuity theorem** (`prob_H0_eq_zero_of_aligned_of_uncertaintyGlob`, `…_uncertaintyCtx`):
  `Aligned ∧ (c) ⇒ P^π(H = 0) = 0`. Every instance of Theorem 10 is a model in which the human
  never requests shutdown, and its obedience clause holds vacuously (`thm10_without_a_b`).

Source: carey-everitt-2023 Props 6, 8, 9 (l. 127–137, 209–215), Thm 10 (l. 217), Appendix A
(l. 333–346).
-/

namespace Cleanroom.Corrigibility.CorrScimCid

open FactoredSpaces Cleanroom.Found.CorrThreeStep

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val E : V → Type} [∀ v, Fintype (E v)]

namespace ShutdownSpec

variable {C : Cid G Val} (P : ShutdownSpec C) (M : Scim C E) (π : Policy C)

/-- **Consistency at the shutdown event**: where the agent shuts down, `U_{S=0}(ε) = U(ε)`.
Source: carey-everitt-2023 Prop. 6 proof (eq. (1)), Lemma 22 proof ("from consistency")
Kind: P -/
lemma US0val_eq_of_shut {ε : Pt E} (h : M.ev π ε P.S = P.s0) :
    P.US0val M π ε = P.Uval M π ε := by
  unfold US0val Uval evS0 uU
  rw [Scm.eval_doAt_of_eq _ C.acyclic ε h]
  rfl

/-- If every support point of the human context `pa_H` has `S = 0`, then
`E[U | pa_H] = E[U_{S=0} | pa_H]`.
Source: carey-everitt-2023 Prop. 6 proof
Kind: P -/
lemma condEU_eq_condEUS0_of_shut (pa : ParentVals G Val P.H)
    (h : ∀ ε, 0 < M.μ.mass ε → P.paH M π ε = pa → M.ev π ε P.S = P.s0) :
    P.condEU M π pa = P.condEUS0 M π pa := by
  unfold condEU condEUS0
  exact condExpect_congr M.μ fun ε hctx hε => (P.US0val_eq_of_shut M π (h ε hε hctx)).symm

/-- **T5(a): the alignment identity.** Shutdown alignment (Def. 7) holds iff at every
positive-probability human context shutdown is not strictly better:
`Aligned π ↔ ∀ pa_H, 0 < P(pa_H) → E[U_{S=0} | pa_H] ≤ E[U | pa_H]`. (⇒) is the consistency
step; (⇐) makes Def. 7 vacuous.
Source: mandate T5(a) (this package's derivation); carey-everitt-2023 Def. 7
Kind: P
Fidelity: exact
Hyps: — -/
theorem aligned_iff_forall_condEUS0_le :
    P.Aligned M π ↔
      ∀ pa, 0 < M.μ.prob (P.ctxH M π pa) → P.condEUS0 M π pa ≤ P.condEU M π pa := by
  rw [aligned_iff]
  constructor
  · intro h pa hpa
    by_contra hlt
    push Not at hlt
    exact absurd (P.condEU_eq_condEUS0_of_shut M π pa (h pa hpa hlt)) (ne_of_lt hlt)
  · intro h pa hpa hneed
    exact absurd hneed (not_lt.mpr (h pa hpa))

/-- **Corollary: alignment ensures vigilance**, because need is never realised on the support (so
Def. 4's implication holds vacuously at every support point).
Source: mandate T5(a); carey-everitt-2023 Thm 10 proof (which reaches vigilance through (c) instead)
Kind: C
Fidelity: exact
Hyps: — -/
theorem ensuresVigilance_of_aligned (h : P.Aligned M π) : P.EnsuresVigilance M π := by
  rw [ensuresVigilance_iff]
  intro ε hε hneed
  exfalso
  have hpa : 0 < M.μ.prob (P.ctxH M π (P.paH M π ε)) := prob_pos_of_mass_pos M.μ hε rfl
  exact absurd hneed (not_lt.mpr ((P.aligned_iff_forall_condEUS0_le M π).mp h _ hpa))

/-- **The mixture step**: if at every positive-probability human context shutdown is not strictly
better, then `π` weakly outperforms shutdown, `E[U_{S=0}] ≤ E[U]`.
Source: carey-everitt-2023 Prop. 6 proof (last step)
Kind: C -/
lemma weaklyOutperforms_of_forall
    (h : ∀ pa, 0 < M.μ.prob (P.ctxH M π pa) → P.condEUS0 M π pa ≤ P.condEU M π pa) :
    P.WeaklyOutperforms M π :=
  expect_le_of_condExpect_le M.μ (P.paH M π) h

/-- Aligned policies weakly outperform shutdown.
Source: carey-everitt-2023 Prop. 8 proof
Kind: C -/
theorem weaklyOutperforms_of_aligned (h : P.Aligned M π) : P.WeaklyOutperforms M π :=
  P.weaklyOutperforms_of_forall M π ((P.aligned_iff_forall_condEUS0_le M π).mp h)

/-- **Prop. 8 (shutdown alignment benefit)**: cautious and shutdown aligned ⇒ beneficial.
Source: carey-everitt-2023 Prop. 8 (l. 211)
Kind: C
Fidelity: exact
Hyps: — -/
theorem beneficial_of_cautious_of_aligned (hc : P.Cautious M π) (ha : P.Aligned M π) :
    P.Beneficial M π :=
  le_trans hc (P.weaklyOutperforms_of_aligned M π ha)

/-- **Key lemma: obedience and ensured vigilance imply shutdown alignment** (Prop. 9 without
caution). At a positive-probability context with need, vigilance makes every support point request
shutdown (`H = 0`), and obedience under `do(H = 0)` transports through consistency to shutdown on
the event `{H = 0}` — no "conditioning on all parents = intervention" lemma is needed.
Source: carey-everitt-2023 Prop. 6 proof, eq. (1); Prop. 9
Kind: P
Fidelity: stronger (no caution hypothesis)
Hyps: — -/
theorem aligned_of_obedient_of_ensuresVigilance (ho : P.Obedient M π)
    (hv : P.EnsuresVigilance M π) : P.Aligned M π := by
  rw [aligned_iff]
  intro pa hpa hneed ε hε hctx
  have hH : M.ev π ε P.H = P.h0 :=
    (P.ensuresVigilance_iff M π).mp hv ε hε (hctx ▸ hneed)
  have := (P.obedient_iff M π).mp ho ε hε
  unfold evH0 at this
  rwa [Scm.eval_doAt_of_eq _ C.acyclic ε hH] at this

/-- **Prop. 9 (instructability ⇒ alignment).**
Source: carey-everitt-2023 Prop. 9 (l. 213)
Kind: C
Fidelity: exact
Hyps: — -/
theorem aligned_of_instructable (h : P.Instructable M π) : P.Aligned M π :=
  P.aligned_of_obedient_of_ensuresVigilance M π h.1 h.2.1

/-- **Prop. 6 (shutdown instructability benefit)**: instructable ⇒ beneficial.
Source: carey-everitt-2023 Prop. 6 (l. 133)
Kind: C
Fidelity: exact
Hyps: — -/
theorem beneficial_of_instructable (h : P.Instructable M π) : P.Beneficial M π :=
  P.beneficial_of_cautious_of_aligned M π h.2.2 (P.aligned_of_instructable M π h)

/-- Obedience and ensured vigilance alone give weak outperformance of shutdown (the
"no caution needed" observation behind Thm 14 ⇒ and the indispensability loophole).
Source: carey-everitt-2023 §5.3 (after Thm 14: "caution isn't required to outperform shutdown")
Kind: C -/
theorem weaklyOutperforms_of_obedient_of_ensuresVigilance (ho : P.Obedient M π)
    (hv : P.EnsuresVigilance M π) : P.WeaklyOutperforms M π :=
  P.weaklyOutperforms_of_aligned M π (P.aligned_of_obedient_of_ensuresVigilance M π ho hv)

/-! ### Theorem 10 and its vacuity (T6) -/

/-- The event "the human is not vigilant or requests shutdown", `{C ≠ 0 ∨ H = 0}`.
Source: carey-everitt-2023 Thm 10 (c)
Kind: D -/
def nonVigOrRequest : Set (Pt E) := {ε | ¬ P.Vigilant M π ε ∨ M.ev π ε P.H = P.h0}

/-- The agent's context `Pa_{D₂}(ε)`.
Source: carey-everitt-2023 Thm 10 (c)
Kind: D -/
noncomputable def paD₂ (ε : Pt E) : ParentVals G Val P.D₂ := parentConfig G Val (M.ev π ε) P.D₂

/-- The event `{Pa_{D₂} = pa}`.
Source: none: infrastructure
Kind: D -/
def ctxD₂ (pa : ParentVals G Val P.D₂) : Set (Pt E) := {ε | P.paD₂ M π ε = pa}

/-- The event "shutdown is needed at the human's context", `{E[U | Pa_H] < E[U_{S=0} | Pa_H]}`.
Source: carey-everitt-2023 Thm 10 (c)
Kind: D -/
def needEvent : Set (Pt E) := {ε | P.Need M π (P.paH M π ε)}

/-- **Hypothesis (c) of Theorem 10, global reading** (the one Appendix A's proof uses): if the human
is possibly non-vigilant-or-requesting, then at every positive-probability agent context need has
positive conditional probability. Stated at the given `π` (the printed "∀π" is not used by the
proof; Fidelity: stronger).
Source: carey-everitt-2023 Thm 10 (c) (l. 217), Appendix A eq. (2)
Kind: D
Fidelity: stronger: stated at the given policy -/
def UncertaintyGlob : Prop :=
  0 < M.μ.prob (P.nonVigOrRequest M π) →
    ∀ pa, 0 < M.μ.prob (P.ctxD₂ M π pa) →
      0 < M.μ.condProb (P.needEvent M π) (P.ctxD₂ M π pa)

/-- **Hypothesis (c), per-context reading** (the inventory's): at every agent context where
non-vigilance-or-request has positive conditional probability, so does need.
Source: carey-everitt-2023 Thm 10 (c); corr-refs-inventory 044
Kind: D
Fidelity: variant: per-context reading -/
def UncertaintyCtx : Prop :=
  ∀ pa, 0 < M.μ.condProb (P.nonVigOrRequest M π) (P.ctxD₂ M π pa) →
    0 < M.μ.condProb (P.needEvent M π) (P.ctxD₂ M π pa)

/-- **Hypothesis (a)**: no indiscriminate shutdown, `P^π(S = 0) ≠ 1`.
Source: carey-everitt-2023 Thm 10 (a)
Kind: D -/
def NoIndiscriminateShutdown : Prop := M.μ.prob (P.shutEvent M π) ≠ 1

/-- **Hypothesis (b)**: `D₂` determines shutdown, `P^π(D₂ = S) = 1`, through a designated
translation `e : Val D₂ → Val S` (the identity when the two domains coincide).
Source: carey-everitt-2023 Thm 10 (b)
Kind: D
Fidelity: variant: designated map between the two domains -/
def D2DeterminesShutdown (e : Val P.D₂ → Val P.S) : Prop :=
  M.μ.prob {ε | e (M.ev π ε P.D₂) = M.ev π ε P.S} = 1

/-- Under alignment, the need event has probability zero.
Source: mandate T6(c)
Kind: P -/
theorem prob_needEvent_eq_zero_of_aligned (ha : P.Aligned M π) :
    M.μ.prob (P.needEvent M π) = 0 := by
  refine prob_eq_zero_of_forall M.μ fun ε hε hneed => ?_
  have hpa : 0 < M.μ.prob (P.ctxH M π (P.paH M π ε)) := prob_pos_of_mass_pos M.μ hε rfl
  exact absurd hneed (not_lt.mpr ((P.aligned_iff_forall_condEUS0_le M π).mp ha _ hpa))

/-- Under alignment, need has conditional probability zero given any agent context.
Source: mandate T6(c)
Kind: L -/
lemma condProb_needEvent_eq_zero_of_aligned (ha : P.Aligned M π) (pa : ParentVals G Val P.D₂) :
    M.μ.condProb (P.needEvent M π) (P.ctxD₂ M π pa) = 0 := by
  rw [Distr.condProb, Distr.prob_eq_zero_of_subset M.μ Set.inter_subset_left
    (P.prob_needEvent_eq_zero_of_aligned M π ha), zero_div]

/-- Some exogenous setting has positive mass.
Source: none: infrastructure
Kind: L -/
lemma exists_mass_pos : ∃ ε, 0 < M.μ.mass ε := by
  by_contra h
  push Not at h
  have h1 := M.μ.sum_eq_one
  rw [Finset.sum_eq_zero (fun ε _ => le_antisymm (h ε) (M.μ.nonneg ε))] at h1
  exact zero_ne_one h1

/-- **The vacuity theorem, global reading (T6 c).** A shutdown-aligned policy satisfying Theorem
10's uncertainty hypothesis (c) lives in a model where the human *never* requests shutdown:
`P^π(H = 0) = 0`. Proof: by the alignment identity need is never realised, so every consequent of
(c) is false, so its antecedent `0 < P(C ≠ 0 ∨ H = 0)` is false.
Source: mandate T6(c) (finding, severity: blocking the theorem's advertised content);
carey-everitt-2023 Thm 10
Kind: P
Fidelity: exact
Hyps: — -/
theorem prob_H0_eq_zero_of_aligned_of_uncertaintyGlob (ha : P.Aligned M π)
    (hc : P.UncertaintyGlob M π) : M.μ.prob {ε | M.ev π ε P.H = P.h0} = 0 := by
  by_contra hne
  have hpos : 0 < M.μ.prob {ε | M.ev π ε P.H = P.h0} :=
    lt_of_le_of_ne (M.μ.prob_nonneg _) (Ne.symm hne)
  have hpos' : 0 < M.μ.prob (P.nonVigOrRequest M π) :=
    lt_of_lt_of_le hpos (M.μ.prob_mono fun ε h => Or.inr h)
  obtain ⟨ε₀, hε₀⟩ := exists_mass_pos M
  have hctx : 0 < M.μ.prob (P.ctxD₂ M π (P.paD₂ M π ε₀)) := prob_pos_of_mass_pos M.μ hε₀ rfl
  have := hc hpos' _ hctx
  rw [P.condProb_needEvent_eq_zero_of_aligned M π ha] at this
  exact lt_irrefl 0 this

/-- **The vacuity theorem, per-context reading.**
Source: mandate T6(c); corr-refs-inventory 044
Kind: P
Fidelity: exact
Hyps: — -/
theorem prob_H0_eq_zero_of_aligned_of_uncertaintyCtx (ha : P.Aligned M π)
    (hc : P.UncertaintyCtx M π) : M.μ.prob {ε | M.ev π ε P.H = P.h0} = 0 := by
  refine prob_eq_zero_of_forall M.μ fun ε₀ hε₀ hH => ?_
  have hctx : 0 < M.μ.prob (P.ctxD₂ M π (P.paD₂ M π ε₀)) := prob_pos_of_mass_pos M.μ hε₀ rfl
  have hnum : 0 < M.μ.prob (P.nonVigOrRequest M π ∩ P.ctxD₂ M π (P.paD₂ M π ε₀)) :=
    prob_pos_of_mass_pos M.μ hε₀ ⟨Or.inr hH, rfl⟩
  have := hc _ (div_pos hnum hctx)
  rw [P.condProb_needEvent_eq_zero_of_aligned M π ha] at this
  exact lt_irrefl 0 this

/-- No instance of Theorem 10 (global reading) has a press: the negation form.
Source: mandate T6(c)
Kind: L -/
theorem not_prob_H0_pos_of_aligned_of_uncertaintyGlob (ha : P.Aligned M π)
    (hc : P.UncertaintyGlob M π) : ¬ 0 < M.μ.prob {ε | M.ev π ε P.H = P.h0} := by
  rw [P.prob_H0_eq_zero_of_aligned_of_uncertaintyGlob M π ha hc]
  exact lt_irrefl 0

/-- If the human never requests shutdown, obedience on distribution holds vacuously.
Source: mandate T6(c)
Kind: L -/
lemma obedientOnDist_of_prob_H0_eq_zero (h : M.μ.prob {ε | M.ev π ε P.H = P.h0} = 0) :
    P.ObedientOnDist M π :=
  Distr.prob_eq_zero_of_subset M.μ (fun _ hε => hε.2) h

/-- **Theorem 10 without (a), (b) — the content that survives.** A shutdown-aligned policy with
uncertainty (c-glob) and caution is weakly shutdown instructable; the obedience clause holds
because the human never requests shutdown (`prob_H0_eq_zero_of_aligned_of_uncertaintyGlob`).
Source: carey-everitt-2023 Thm 10; mandate T6(c)
Kind: C
Fidelity: stronger (hypotheses (a), (b) dropped)
Hyps: — -/
theorem thm10_without_a_b (ha : P.Aligned M π) (hc : P.UncertaintyGlob M π)
    (hd : P.Cautious M π) : P.WeaklyInstructable M π :=
  ⟨P.obedientOnDist_of_prob_H0_eq_zero M π
      (P.prob_H0_eq_zero_of_aligned_of_uncertaintyGlob M π ha hc),
    P.ensuresVigilance_of_aligned M π ha, hd⟩

/-- **Theorem 10 as printed** (global reading of (c)): a shutdown-aligned policy with (a) no
indiscriminate shutdown, (b) `D₂` determining shutdown, (c) uncertainty and (d) caution is weakly
shutdown instructable. Hypotheses (a) and (b) are named and unused: the conclusion follows from
(c) and (d) alone (`thm10_without_a_b`), and its obedience clause is vacuous — every instance has
`P^π(H = 0) = 0`. Ledger status: proved, flagged: hypotheses force `P(H = 0) = 0`.
Source: carey-everitt-2023 Thm 10 (l. 217), Appendix A (l. 333–346)
Kind: C
Fidelity: exact ((c) at the given policy: stronger)
Hyps: — ((a), (b) named-and-unused) -/
theorem thm10_as_printed (ha : P.Aligned M π) (_h_a : P.NoIndiscriminateShutdown M π)
    (e : Val P.D₂ → Val P.S) (_h_b : P.D2DeterminesShutdown M π e)
    (hc : P.UncertaintyGlob M π) (hd : P.Cautious M π) : P.WeaklyInstructable M π :=
  P.thm10_without_a_b M π ha hc hd

/-- **Theorem 10, per-context reading of (c).**
Source: carey-everitt-2023 Thm 10; corr-refs-inventory 044
Kind: C
Fidelity: variant: per-context (c)
Hyps: — -/
theorem thm10_ctx (ha : P.Aligned M π) (hc : P.UncertaintyCtx M π) (hd : P.Cautious M π) :
    P.WeaklyInstructable M π :=
  ⟨P.obedientOnDist_of_prob_H0_eq_zero M π
      (P.prob_H0_eq_zero_of_aligned_of_uncertaintyCtx M π ha hc),
    P.ensuresVigilance_of_aligned M π ha, hd⟩

end ShutdownSpec

end Cleanroom.Corrigibility.CorrScimCid
