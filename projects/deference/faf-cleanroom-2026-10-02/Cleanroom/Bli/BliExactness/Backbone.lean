import Cleanroom.Bli.BliExactness.Defs
import LogicalInduction.Construction.Paper.Market
import LogicalInduction.Properties.TimelyLearning
import LogicalInduction.Framework.Machine.Witnesses
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# `bli-exactness` — X6: the LI-side asymptotic backbone

Everything a logical inductor has *asymptotically* that BLI imposes *exactly*, over FAF's
constructed market `liaHistory (paperDP T)` in closed form (no quote hypotheses) — the rows the
program's §4–§5 cite whenever they say "the base approximately satisfies D-NNU / D-ST":

* **(i)** `nnu_asymptotic` = `thm:ceu` (`lic_no_expected_net_update_closed`): the asymptotic
  constraint 4 of `𝑸` itself — `𝑸_n(φ_n) ≈ₙ 𝔼_n(⌜𝑸_{f(n)}(φ_n)⌝)`; instantiated at the atom family
  and `succDeferral` so no binder is unwitnessed.
* **(ii)** `self_trust_smoothed_const` = `thm:st` (`lic_self_trust_closed`) at `δ ≡ ¼`, `p ≡ ½`:
  the asymptotic `E2i`, slide 40's displayed inequality with `ctsInd`'s `(p, p+δ]` ramp, in
  product form.
* **(iii)** `no_predictable_push` / `no_predictable_drop` (bli-soto-b-057's honest first target,
  **without** an exogenous trader): for every e.c. sentence family and every `c > 0`, an inductor's
  price cannot be eventually pushed up (or down) by `c` from one day to the next — from `thm:tbo`
  (`lic_preemptive_learning`): the liminf of `P_n(φ_n)` equals the liminf of the future suprema,
  which dominate `P_{n+1}(φ_n)`. Kind C (a) for any `[IsLogicalInductor P DP]` with `hworld`;
  instantiated at the LIA. The version with a human pusher `H` inside the market needs
  bli-soto-b-056's market and is not claimed.
* **(iv)** `lic_introspection_closed` at constant bounds is X2 (iii)'s surviving form; cited in the
  report, not re-instantiated (its `GeneratedRatFeature` binders need a feature presentation of
  the constant bounds that this package has no reason to build).
* **(v)** exact ⟹ smoothed is `Smoothed.lean`.
-/

namespace Cleanroom.Bli.BliExactness

open LogicalInduction LO.Propositional Filter Topology

/-! ## (iii) Front-running without an exogenous trader -/

/-- Prices of a logical inductor lie in `[0, 1]` (the criterion carries `def:market`'s range).
Source: FAF `IsLogicalInductor.marketComputable`, `ComputableMarket.price_mem_Icc`
Kind: L
Fidelity: n/a -/
lemma li_price_mem (P : History) (DP : DeductiveProcess) [hLI : IsLogicalInductor P DP] (n : ℕ)
    (ψ : Sentence) : 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
  hLI.marketComputable.price_mem_Icc n ψ

section Push

variable (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]

/-- **No persistent predictable one-day drift** (bli-soto-b-057, the no-persistent-gap half): for
an e.c. sentence family and `c > 0`, it is not the case that eventually
`P_{n+1}(φ_n) ≥ P_n(φ_n) + c`. From `thm:tbo`:
`liminf P_n(φ_n) = liminf sup_j P_{n+j}(φ_n) ≥ liminf (P_n(φ_n) + c) = liminf P_n(φ_n) + c`.
**Scope** (audit r1 N4/N8): this is the negative half of the thread's Consequence 2 ("prices move
toward a predicted push before it") — no e.c. family has a fixed next-day gap on cofinitely many
days; a push predictable on infinitely many but not cofinitely many days is not excluded, and for
a *constant* family the statement follows from boundedness alone (the content is for varying
families, e.g. `no_predictable_push_lia_atoms`). The thread's sentence "a corrigible agent already
believes what it expects to be legitimately taught" is the thread's claim, not what is proved
here.
Source: corrigibility thread 2026-09-14 l.77 "Consequence 2" ([[bli-soto-b-inventory]] 057);
FAF `lic_preemptive_learning` (`Properties/TimelyLearning.lean:394`, `thm:tbo`); mandate X6 (iii),
judged item 3
Kind: C
Fidelity: variant: fixed margin `c`, next day (`n+1`), eventually-always quantifier; the e.c.
family is the paper's `def:ec`; the thread's "toward the push, before it" is not rendered
Hyps: (a) `hworld` (the paper's standing plausible-world assumption, discharged at the LIA by
`paperDP_hworld`) -/
theorem no_predictable_push (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) {c : ℝ} (hc : 0 < c) :
    ¬ (∀ᶠ n in atTop, P n (φ n) + c ≤ P (n + 1) (φ n)) := by
  intro h
  obtain ⟨hinf, -⟩ := lic_preemptive_learning P DP φ hφ hworld
  have hs_ge : ∀ n, P (n + 1) (φ n) ≤ sSup (Set.range fun j => P (n + j) (φ n)) := fun n =>
    le_csSup ⟨1, by rintro x ⟨j, rfl⟩; exact (li_price_mem P DP _ _).2⟩ ⟨1, rfl⟩
  have hs_le : ∀ n, sSup (Set.range fun j => P (n + j) (φ n)) ≤ 1 := fun n =>
    csSup_le ⟨_, ⟨0, rfl⟩⟩ (by rintro x ⟨j, rfl⟩; exact (li_price_mem P DP _ _).2)
  have hev : ∀ᶠ n in atTop, P n (φ n) + c ≤ sSup (Set.range fun j => P (n + j) (φ n)) :=
    h.mono fun n hn => le_trans hn (hs_ge n)
  have hu_bdd : IsBoundedUnder (· ≥ ·) atTop fun n => P n (φ n) + c :=
    isBoundedUnder_of ⟨c, fun n => by linarith [(li_price_mem P DP n (φ n)).1]⟩
  have hs_cobdd : IsCoboundedUnder (· ≥ ·) atTop fun n =>
      sSup (Set.range fun j => P (n + j) (φ n)) :=
    (isBoundedUnder_of ⟨1, fun n => hs_le n⟩ :
      IsBoundedUnder (· ≤ ·) atTop fun n => sSup (Set.range fun j => P (n + j) (φ n))
      ).isCoboundedUnder_flip
  have h1 := liminf_le_liminf hev hu_bdd hs_cobdd
  have hu_cobdd : IsCoboundedUnder (· ≥ ·) atTop fun n => P n (φ n) :=
    (isBoundedUnder_of ⟨1, fun n => (li_price_mem P DP n (φ n)).2⟩ :
      IsBoundedUnder (· ≤ ·) atTop fun n => P n (φ n)).isCoboundedUnder_flip
  have hu_bdd' : IsBoundedUnder (· ≥ ·) atTop fun n => P n (φ n) :=
    isBoundedUnder_of ⟨0, fun n => (li_price_mem P DP n (φ n)).1⟩
  have h2 := liminf_add_const atTop (fun n => P n (φ n)) c hu_cobdd hu_bdd'
  rw [h2, ← hinf] at h1
  linarith

/-- **No predictable downward push**: the twin, from the limsup half of `thm:tbo`.
Source: as `no_predictable_push`
Kind: C
Fidelity: variant: as `no_predictable_push`
Hyps: (a) `hworld` -/
theorem no_predictable_drop (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) {c : ℝ} (hc : 0 < c) :
    ¬ (∀ᶠ n in atTop, P (n + 1) (φ n) + c ≤ P n (φ n)) := by
  intro h
  obtain ⟨-, hsup⟩ := lic_preemptive_learning P DP φ hφ hworld
  have ht_le : ∀ n, sInf (Set.range fun j => P (n + j) (φ n)) ≤ P (n + 1) (φ n) := fun n =>
    csInf_le ⟨0, by rintro x ⟨j, rfl⟩; exact (li_price_mem P DP _ _).1⟩ ⟨1, rfl⟩
  have ht_ge : ∀ n, 0 ≤ sInf (Set.range fun j => P (n + j) (φ n)) := fun n =>
    le_csInf ⟨_, ⟨0, rfl⟩⟩ (by rintro x ⟨j, rfl⟩; exact (li_price_mem P DP _ _).1)
  have hev : ∀ᶠ n in atTop, sInf (Set.range fun j => P (n + j) (φ n)) ≤ P n (φ n) - c :=
    h.mono fun n hn => by linarith [ht_le n]
  have ht_cobdd : IsCoboundedUnder (· ≤ ·) atTop fun n =>
      sInf (Set.range fun j => P (n + j) (φ n)) :=
    (isBoundedUnder_of ⟨0, fun n => ht_ge n⟩ :
      IsBoundedUnder (· ≥ ·) atTop fun n => sInf (Set.range fun j => P (n + j) (φ n))
      ).isCoboundedUnder_flip
  have hu_bdd : IsBoundedUnder (· ≤ ·) atTop fun n => P n (φ n) - c :=
    isBoundedUnder_of ⟨1 - c, fun n => by linarith [(li_price_mem P DP n (φ n)).2]⟩
  have h1 := limsup_le_limsup hev ht_cobdd hu_bdd
  have hu_bdd' : IsBoundedUnder (· ≤ ·) atTop fun n => P n (φ n) :=
    isBoundedUnder_of ⟨1, fun n => (li_price_mem P DP n (φ n)).2⟩
  have hu_cobdd : IsCoboundedUnder (· ≤ ·) atTop fun n => P n (φ n) :=
    (isBoundedUnder_of ⟨0, fun n => (li_price_mem P DP n (φ n)).1⟩ :
      IsBoundedUnder (· ≥ ·) atTop fun n => P n (φ n)).isCoboundedUnder_flip
  have h2 := limsup_sub_const atTop (fun n => P n (φ n)) c hu_bdd' hu_cobdd
  rw [h2, ← hsup] at h1
  linarith

end Push

section Lia

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [LO.Entailment.Consistent T]

/-- **(i) Asymptotic constraint 4 for `𝑸` itself** (`thm:ceu`, closed form): the LIA's day-`n`
price of `φ_n` is asymptotically its day-`n` expectation of its own day-`f(n)` price of `φ_n`.
This is the row every "the base approximately satisfies D-NNU" sentence of the program cites;
BLI's constraint 4 is its exact, day-by-day form.
Source: bli-paper-2-008 (a) (b.270: "if the expected posterior doesn't match current probabilities,
we're dutch-bookable"); FAF `lic_no_expected_net_update_closed` (`Construction/Paper/Market.lean:285`);
mandate X6 (i), judged item 3
Kind: L (verbatim alias of FAF `lic_no_expected_net_update_closed`; regraded from C in repair r1 — STANDARDS §6's C means multi-step chaining)
Fidelity: exact (FAF's `thm:ceu` restated under the BLI name)
Hyps: (a) -/
theorem nnu_asymptotic (f : DeferralFunction) (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) :
    (fun n ↦ liaHistory (paperDP T) n (φ n)) ≈ₙ
      fun n ↦ ((paperFutureQuoteCode T f φ hφ).luv n).expect (liaHistory (paperDP T)) n :=
  lic_no_expected_net_update_closed T f φ hφ

/-- (i) at the atom family and the successor deferral: no binder unwitnessed.
Source: mandate X6 (i); FAF `machineSentenceCodes_atom`, `succDeferral`
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem nnu_asymptotic_atoms_succ :
    (fun n ↦ liaHistory (paperDP T) n (Formula.atom n)) ≈ₙ
      fun n ↦ ((paperFutureQuoteCode T succDeferral (fun n => (Formula.atom n : Sentence))
        machineSentenceCodes_atom).luv n).expect (liaHistory (paperDP T)) n :=
  nnu_asymptotic T succDeferral _ machineSentenceCodes_atom

/-- **(ii) Smoothed self-trust in product form at constant threshold data** (`thm:st`, closed form,
`δ ≡ ¼`, `p ≡ ½`): slide 40's displayed inequality
`𝔼_n(𝟙(φ_n)·Ind_δ(𝑸_{f(n)}(φ_n) > ½)) ≳ₙ ½·𝔼_n(Ind_δ(𝑸_{f(n)}(φ_n) > ½))` with FAF's `ctsInd`
ramp — the asymptotic `E2i`. The constant threshold data are machine-metered by
`MachineRatCodes.const`, and `p` is `ℙ`-generable by `PGenerableRat.ofMachineRatCodes`.
Source: slide 40 bullet 3 ([[bli-slides-inventory]] 042); bli-paper-2-008 (b); FAF
`lic_self_trust_closed` (`Construction/Paper/Market.lean:500`); mandate X6 (ii)
Kind: L (instantiation of FAF `lic_self_trust_closed` at two constants; regraded from C in repair r1)
Fidelity: exact (FAF's `thm:st` at constant `δ`, `p`)
Hyps: (a) -/
theorem self_trust_smoothed_const (f : DeferralFunction) (φ : ℕ → Sentence)
    (hφ : MachineSentenceCodes φ) :
    (fun n ↦ (indicatorProductLUV
          (paperConfidenceQuoteCode T f φ hφ (fun _ => 1 / 4) (fun _ => 1 / 2)
              (MachineRatCodes.const (1 / 4)).computable
              (PGenerableRat.ofMachineRatCodes (MachineRatCodes.const (1 / 2))
                (liaHistory (paperDP T)))) φ n).expect
        (liaHistory (paperDP T)) n) ≳ₙ
      fun n ↦ ((1 / 2 : ℚ) : ℝ) *
        ((paperConfidenceQuoteCode T f φ hφ (fun _ => 1 / 4) (fun _ => 1 / 2)
            (MachineRatCodes.const (1 / 4)).computable
            (PGenerableRat.ofMachineRatCodes (MachineRatCodes.const (1 / 2))
              (liaHistory (paperDP T)))).luv n).expect
          (liaHistory (paperDP T)) n :=
  lic_self_trust_closed T f φ (fun _ => 1 / 4) (fun _ => 1 / 2) (fun _ => by norm_num)
    (fun _ => by norm_num) hφ (MachineRatCodes.const (1 / 4))
    (PGenerableRat.ofMachineRatCodes (MachineRatCodes.const (1 / 2)) (liaHistory (paperDP T)))

/-- **(iii) at the LIA**: the constructed inductor's price of an e.c. family is never predictably
pushed by a fixed margin, up or down.
Source: mandate X6 (iii); FAF `paperLIA`, `paperDP_hworld`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem no_predictable_push_lia (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) {c : ℝ}
    (hc : 0 < c) :
    ¬ (∀ᶠ n in atTop, liaHistory (paperDP T) n (φ n) + c ≤ liaHistory (paperDP T) (n + 1) (φ n)) ∧
    ¬ (∀ᶠ n in atTop, liaHistory (paperDP T) (n + 1) (φ n) + c ≤ liaHistory (paperDP T) n (φ n)) :=
  haveI := paperLIA T
  ⟨no_predictable_push (liaHistory (paperDP T)) (paperDP T) φ hφ (paperDP_hworld T) hc,
   no_predictable_drop (liaHistory (paperDP T)) (paperDP T) φ hφ (paperDP_hworld T) hc⟩

/-- (iii) at the atom family: no binder unwitnessed.
Source: mandate X6 (iii)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem no_predictable_push_lia_atoms {c : ℝ} (hc : 0 < c) :
    ¬ (∀ᶠ n in atTop, liaHistory (paperDP T) n (Formula.atom n) + c ≤
        liaHistory (paperDP T) (n + 1) (Formula.atom n)) :=
  (no_predictable_push_lia T (fun n => (Formula.atom n : Sentence)) machineSentenceCodes_atom hc).1

end Lia

end Cleanroom.Bli.BliExactness
