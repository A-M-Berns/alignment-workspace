import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Properties.NonDogmatism
import LogicalInduction.Construction.Quotation.DeferralFibre

/-!
# `legit-li-register` · PiOne: legitimacy is Π₁ — instance checks (Target 5)

trust-lab-071 / scout-fresh-eyes Q5: for a day-indexed family of legitimacy sentences `L_n`
("the feedback on day `n` is uncorrupted"), (i) each bounded instance is learned, in a timely
manner, by provability induction; (ii) the global sentence `∀ n, L_n` — Π₁ *in meaning* — is pinned
in `[ε, 1 − ε']` forever by non-dogmatism and its dual whenever both polarities stay consistent
with every stage; (iii) hence (INTERPRETATION, findings) gates must be day-indexed.

**Fidelity: variant.** FAF's sentences are propositional over `ℕ` atoms; "Π₁" is the *meaning*
of the atom `σ`, not a syntactic class in the formalization. What is proved is exactly: (i) is
`lic_provind_true` (a named instance, Kind L), its deferred-day form by the reindexing idiom;
(ii) is the composition of `lic_nonDogmatism` and `lic_nonDogmatism_dual` at a sentence both of
whose polarities are consistent with every stage (Kind C, two instances composed). The content is
the composition and the reading, not new mathematics — the scout's own framing ("instances of
known LI theorems whose composition and consequence for the gate design are the new content").

Witnesses (`Witness.lean`): N+ for (i) the ledger-threshold monitors on the even days of
`onGSystem` (a real "the published record passed its day-`n` check" family); N− for (ii) an
atom no stage mentions (both polarities consistent because nothing constrains it); the N+ for
(ii) — a genuinely independent Π₁ sentence of `𝗜𝚺₁` through FAF's `paperDP` — was not attempted
(report, "Not done").
-/

namespace Cleanroom.Trust.LegitLiRegister

open LogicalInduction LO.Propositional
open Filter Topology

/-- **Bounded legitimacy is learned** (i): an e.c. family of legitimacy monitors each of which is
a theorem of the process has price `→ 1`. This *is* FAF's `lic_provind_true`, named for the
instance; the hypothesis `hthm` is "no corruption ever occurs" (every monitor true in every
completed-theory world), which is what the scout's (i) assumes.
Source: trust-lab-071 (i); scout-fresh-eyes Q5 (i); FAF `thm:provind` (`lic_provind_true`)
Kind: L (a named instance)
Fidelity: variant: "legitimacy sentence" is any e.c. sentence family; Π₁ is the meaning, not a syntactic class
Hyps: (a) none (`hthm` is the instance's premise: the monitors are theorems; `hworld` the stages are satisfiable) -/
theorem boundedLegit_learned (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (L : ℕ → Sentence) (hL : MachineSentenceCodes L)
    (hthm : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (L n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (L n)) ≈ₙ (fun _ => 1) :=
  lic_provind_true P DP L hL hthm hworld

/-- **Bounded legitimacy is learned, deferred-day form** ("timely"): the day-`f n` price of the
day-`n` monitor tends to `1`, for any injective deferral `f` — provability induction on the
reindexed family `m ↦ L (f⁻¹ m)`, read back at `m = f n`. What "timely" buys over "eventual" here
is only the clock on which the convergence is read (the reader's day `f n`, not `n → ∞` at a fixed
monitor); the statement is still asymptotic in `n`.
Source: trust-lab-071 (i) ("in a timely manner"); scout-fresh-eyes Q5 (i); FAF `thm:provind`; `def-self-trust` `deferred_price_taut_eventually` (the idiom)
Kind: L
Fidelity: variant: as `boundedLegit_learned`; `hinj` as a hypothesis (FAF's `DeferralFunction` is not injective by type)
Hyps: (a) none -/
theorem boundedLegit_learned_deferred (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (L : ℕ → Sentence) (hL : MachineSentenceCodes L)
    (hthm : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (L n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) (hinj : Function.Injective f.f) :
    Tendsto (fun n => P (f n) (L n)) atTop (𝓝 1) := by
  have h := lic_provind_true P DP (fun m => L (deferralPreimage f m))
    (hL.comp (unaryRuler_deferralPreimage f)) (fun m v hv => hthm _ v hv) hworld
  have h' : Tendsto (fun m => P m (L (deferralPreimage f m)) - 1) atTop (𝓝 0) := h
  have h2 := h'.comp f.tendsto_atTop
  have h3 : Tendsto (fun n => P (f n) (L n) - 1) atTop (𝓝 0) := by
    refine h2.congr (fun n => ?_)
    simp only [Function.comp, deferralPreimage_at f hinj]
  exact tendsto_sub_nhds_zero_iff.1 h3

/-- **Global legitimacy is pinned in `(0,1)` forever** (ii): at a sentence `σ` both of whose
polarities are consistent with every stage, the price is eventually bounded below by some
`ε > 0` and above by some `ε' < 1` — non-dogmatism and its dual, composed. The assumption "no
corruption ever occurs" is retainable (`ε ≤ P n σ`) but never certifiable (`P n σ ≤ ε' < 1`),
*whatever clean history the inductor sees*: the hypotheses say nothing about the stages beyond
the two consistencies. The Π₁ reading is the interpretation of `σ` as "∀ n, L n"; nothing in the
formalization relates `σ` to the monitors `L` — the relation is the meaning of the atom.
Source: trust-lab-071 (ii); scout-fresh-eyes Q5 (ii); FAF `thm:nd` (`lic_nonDogmatism`, `lic_nonDogmatism_dual`)
Kind: L (two named FAF instances conjoined by `filter_upwards`; regraded from C after audit round 1)
Fidelity: variant: Π₁ is the meaning of `σ`, not a syntactic class; the bounds are FAF's (eventual, with unnamed constants)
Hyps: (a) none (`h₁`, `h₀` are the instance's premise: both polarities of `σ` consistent with every stage) -/
theorem globalLegit_pinned (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (σ : Sentence)
    (h₁ : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds σ)
    (h₀ : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds σ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ε' : ℝ, ε' < 1 ∧ ∀ᶠ n in atTop, ε ≤ P n σ ∧ P n σ ≤ ε' := by
  obtain ⟨ε, hε, h1⟩ := lic_nonDogmatism P DP σ h₁
  obtain ⟨ε', hε', h0⟩ := lic_nonDogmatism_dual P DP σ h₀
  refine ⟨ε, hε, 1 - ε', by linarith, ?_⟩
  filter_upwards [h1, h0] with n hn1 hn0
  exact ⟨hn1, hn0⟩

end Cleanroom.Trust.LegitLiRegister
