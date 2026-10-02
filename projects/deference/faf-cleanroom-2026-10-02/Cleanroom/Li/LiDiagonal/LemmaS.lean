import LogicalInduction.Properties.TimelyLearning
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Framework.Machine.SentenceMachine
import Mathlib.Order.Filter.IsBounded

/-!
# `li-diagonal` · Lemma S: a revisiting enumeration has liminf `0` and limsup `1` (T6c)

vq-wiki-060(b): with a revisiting enumeration `κ` and decided sentences `π_k` of both truth
values, `liminf_j P_j(π_{κ j}) = 0` and `limsup = 1`. The source proves it through Preemptive
Learning (`thm:tbo`) on the future suprema/infima; **over FAF the statement as boxed needs neither
`thm:tbo` nor an e.c. certificate of the enumeration** (audit r1, adversarial N1, probe
`LemmaSNoCert.lean`): on the days `j` with `κ j = k₁` the diagonal price *is* `P_j(π_{k₁})`, which
`→ 0` by provability induction on the constant family (`price_tendsto_zero_of_neg_mem`), so
`liminf ≤ ε` for every `ε`; dually for `k₀`. The first version of this file routed through
`lic_preemptive_learning` and carried `hψ : MachineSentenceCodes (fun j => π (κ j))`; both were
superfluous for this statement and are dropped (finding F-11: the source's "revisiting is
necessary" is argued for the sup-form `liminf_j sup_{m ≥ j} P_m(ψ_j) = 0`, which is not what the
boxed statement says). The source's (NH-1) caveat is rendered as the hypotheses: `κ` revisits both
`k₀` and `k₁` infinitely often, `π_{k₀}` lies in some stage of the process and `∼π_{k₁}` lies in
some stage.

Scope: single-market.
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO.Propositional
open Filter Topology

/-- A sentence lying in some stage of the process has price `→ 1` (`lic_provind_true` on the
constant family).
Scope: single-market.
Source: LI paper `thm:provind`; FAF `lic_provind_true`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem price_tendsto_one_of_mem (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : Sentence) (h : ∃ k, φ ∈ DP.D k)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n => P n φ) atTop (𝓝 1) := by
  have := lic_provind_true P DP (fun _ => φ) (MachineSentenceCodes.const φ)
    (fun _ v hv => hv.holds_of_mem_stage h) hworld
  unfold AsympEq at this
  simpa using this.add_const (1 : ℝ)

/-- A sentence whose negation lies in some stage of the process has price `→ 0`
(`lic_provind_false` on the constant family).
Scope: single-market.
Source: LI paper `thm:provind`; FAF `lic_provind_false`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem price_tendsto_zero_of_neg_mem (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : Sentence) (h : ∃ k, ∼ φ ∈ DP.D k)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n => P n φ) atTop (𝓝 0) := by
  have := lic_provind_false P DP (fun _ => φ) (MachineSentenceCodes.const φ)
    (fun _ v hv => hv.holds_of_mem_stage h) hworld
  unfold AsympEq at this
  simpa using this

/-- **Lemma S (T6c).** For a revisiting enumeration `ψ_j := π_{κ j}` that revisits a proved index
`k₀` and a refuted index `k₁` infinitely often, the diagonal prices have `liminf = 0` and
`limsup = 1`. No e.c. certificate of the enumeration is needed (the statement is about the prices
of the two constant families on the revisiting days): `thm:provind` on `π_{k₀}` and `π_{k₁}`.
Scope: single-market.
Source: [[vq-wiki-inventory]] 060(b) (Lemma S, "proved modulo (NH-1)"); [[route-negative-introspective]] §5.2
Kind: L
Fidelity: exact (the (NH-1) caveat is the hypothesis package: revisiting of both indices, decidedness in the process; no cheapness of `κ` required — see F-11)
Hyps: (a) `hrev₀`, `hrev₁`, `hproved`, `hrefuted` -/
theorem lemmaS (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (π : ℕ → Sentence) (κ : ℕ → ℕ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (k₀ k₁ : ℕ) (hrev₀ : ∃ᶠ j in atTop, κ j = k₀) (hrev₁ : ∃ᶠ j in atTop, κ j = k₁)
    (hproved : ∃ m, π k₀ ∈ DP.D m) (hrefuted : ∃ m, ∼ π k₁ ∈ DP.D m) :
    liminf (fun j => P j (π (κ j))) atTop = 0 ∧ limsup (fun j => P j (π (κ j))) atTop = 1 := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 := fun n φ =>
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  set u : ℕ → ℝ := fun j => P j (π (κ j)) with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => (hP n _).1
  have hu1 : ∀ n, u n ≤ 1 := fun n => (hP n _).2
  have hubddAbove : IsBoundedUnder (· ≤ ·) atTop u := isBoundedUnder_of ⟨1, hu1⟩
  have hubddBelow : IsBoundedUnder (· ≥ ·) atTop u := isBoundedUnder_of ⟨0, hu0⟩
  have hzero := price_tendsto_zero_of_neg_mem P DP (π k₁) hrefuted hworld
  have hone := price_tendsto_one_of_mem P DP (π k₀) hproved hworld
  constructor
  · refine le_antisymm ?_ (le_liminf_of_le hubddAbove.isCoboundedUnder_ge
      (Eventually.of_forall hu0))
    have hle : ∀ ε > (0 : ℝ), liminf u atTop ≤ ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hzero.eventually (gt_mem_nhds hε))
      have hfreq : ∃ᶠ j in atTop, u j ≤ ε := by
        refine (hrev₁.and_eventually (eventually_ge_atTop N)).mono ?_
        rintro j ⟨hj, hjN⟩
        simp only [hu, hj]
        exact (hN j hjN).le
      exact liminf_le_of_frequently_le hfreq hubddBelow
    by_contra hpos
    rw [not_le] at hpos
    have := hle (liminf u atTop / 2) (by linarith)
    linarith
  · refine le_antisymm (limsup_le_of_le hubddBelow.isCoboundedUnder_le
      (Eventually.of_forall hu1)) ?_
    have hge : ∀ ε > (0 : ℝ), 1 - ε ≤ limsup u atTop := by
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hone.eventually (lt_mem_nhds (by linarith : 1 - ε < 1)))
      have hfreq : ∃ᶠ j in atTop, 1 - ε ≤ u j := by
        refine (hrev₀.and_eventually (eventually_ge_atTop N)).mono ?_
        rintro j ⟨hj, hjN⟩
        simp only [hu, hj]
        exact (hN j hjN).le
      exact le_limsup_of_frequently_le hfreq hubddAbove
    by_contra hlt
    rw [not_le] at hlt
    have := hge ((1 - limsup u atTop) / 2) (by linarith)
    linarith

/-- **Lemma S, N+ instance**: the alternating enumeration `κ j := j mod 2` of a sentence lying in
the process and one whose negation lies in the process.
Scope: single-market.
Source: [[vq-wiki-inventory]] 060(b); [[li-diagonal-handoff]] item 1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem lemmaS_alternating (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ₀ φ₁ : Sentence) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hproved : ∃ m, φ₀ ∈ DP.D m) (hrefuted : ∃ m, ∼ φ₁ ∈ DP.D m) :
    liminf (fun j => P j (if j % 2 = 0 then φ₀ else φ₁)) atTop = 0 ∧
    limsup (fun j => P j (if j % 2 = 0 then φ₀ else φ₁)) atTop = 1 := by
  have h := lemmaS P DP (fun k => if k = 0 then φ₀ else φ₁) (fun j => j % 2) hworld 0 1
    (Filter.frequently_atTop.2 fun a => ⟨2 * a, by omega, by omega⟩)
    (Filter.frequently_atTop.2 fun a => ⟨2 * a + 1, by omega, by omega⟩)
    (by simpa using hproved) (by simpa using hrefuted)
  have heq : (fun j => P j (if (j % 2) = 0 then φ₀ else φ₁)) =
      fun j => P j (if j % 2 = 0 then φ₀ else φ₁) := rfl
  simpa [heq] using h

/-! ## The sup-form (repair round 2) -/

/-- **Lemma S, sup-form (repair round 2; audit r2 fidelity B1, adversarial N10).** The form the
source's proof establishes first and its "revisiting is necessary" paragraph is argued for:
`liminf_j sup_{m ≥ j} P_m(ψ_j) = 0` and `limsup_j inf_{m ≥ j} P_m(ψ_j) = 1`. Over FAF it follows
from `thm:provind` on the two constant families exactly as the boxed form does: on a day
`j ≥ N_ε` with `κ j = k₁` every `m ≥ j` has `P_m(ψ_j) = P_m(π_{k₁}) < ε`, so the future supremum
is `≤ ε` on a frequent set; dually for `k₀`. No `thm:tbo`, no e.c. certificate of `κ`. What
`thm:tbo` does in the source is the passage *between* the two forms; with the sentences decided in
the process both are provind corollaries (F-11, corrected). Suprema and infima are over the
image of `Set.Ici j`, bounded in `[0, 1]` by `price_mem_Icc`.
Scope: single-market.
Source: [[route-negative-introspective]] §5.2 (the proof's first display and the "revisiting is necessary" paragraph); [[vq-wiki-inventory]] 060(b)
Kind: L
Fidelity: exact (the sup/inf-form of the source's proof; same hypothesis package as `lemmaS`)
Hyps: (a) `hrev₀`, `hrev₁`, `hproved`, `hrefuted` -/
theorem lemmaS_supForm (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (π : ℕ → Sentence) (κ : ℕ → ℕ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (k₀ k₁ : ℕ) (hrev₀ : ∃ᶠ j in atTop, κ j = k₀) (hrev₁ : ∃ᶠ j in atTop, κ j = k₁)
    (hproved : ∃ m, π k₀ ∈ DP.D m) (hrefuted : ∃ m, ∼ π k₁ ∈ DP.D m) :
    liminf (fun j => sSup ((fun m => P m (π (κ j))) '' Set.Ici j)) atTop = 0 ∧
    limsup (fun j => sInf ((fun m => P m (π (κ j))) '' Set.Ici j)) atTop = 1 := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 := fun n φ =>
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  have hne : ∀ j, ((fun m => P m (π (κ j))) '' Set.Ici j).Nonempty :=
    fun j => ⟨_, j, Set.mem_Ici.2 le_rfl, rfl⟩
  have hbddA : ∀ j, BddAbove ((fun m => P m (π (κ j))) '' Set.Ici j) := fun j =>
    ⟨1, by rintro _ ⟨m, -, rfl⟩; exact (hP m _).2⟩
  have hbddB : ∀ j, BddBelow ((fun m => P m (π (κ j))) '' Set.Ici j) := fun j =>
    ⟨0, by rintro _ ⟨m, -, rfl⟩; exact (hP m _).1⟩
  have hzero := price_tendsto_zero_of_neg_mem P DP (π k₁) hrefuted hworld
  have hone := price_tendsto_one_of_mem P DP (π k₀) hproved hworld
  constructor
  · set S : ℕ → ℝ := fun j => sSup ((fun m => P m (π (κ j))) '' Set.Ici j) with hS
    have hS0 : ∀ j, 0 ≤ S j := fun j =>
      le_csSup_of_le (hbddA j) ⟨j, Set.mem_Ici.2 le_rfl, rfl⟩ (hP j _).1
    have hS1 : ∀ j, S j ≤ 1 := fun j =>
      csSup_le (hne j) (by rintro _ ⟨m, -, rfl⟩; exact (hP m _).2)
    have hbelow : IsBoundedUnder (· ≥ ·) atTop S := isBoundedUnder_of ⟨0, hS0⟩
    have habove : IsBoundedUnder (· ≤ ·) atTop S := isBoundedUnder_of ⟨1, hS1⟩
    refine le_antisymm ?_
      (le_liminf_of_le habove.isCoboundedUnder_ge (Eventually.of_forall hS0))
    have hle : ∀ ε > (0 : ℝ), liminf S atTop ≤ ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hzero.eventually (gt_mem_nhds hε))
      have hfreq : ∃ᶠ j in atTop, S j ≤ ε := by
        refine (hrev₁.and_eventually (eventually_ge_atTop N)).mono ?_
        rintro j ⟨hj, hjN⟩
        refine csSup_le (hne j) ?_
        rintro _ ⟨m, hm, rfl⟩
        show P m (π (κ j)) ≤ ε
        rw [hj]
        exact (hN m (le_trans hjN hm)).le
      exact liminf_le_of_frequently_le hfreq hbelow
    by_contra hpos
    rw [not_le] at hpos
    have := hle (liminf S atTop / 2) (by linarith)
    linarith
  · set I : ℕ → ℝ := fun j => sInf ((fun m => P m (π (κ j))) '' Set.Ici j) with hI
    have hI0 : ∀ j, 0 ≤ I j := fun j =>
      le_csInf (hne j) (by rintro _ ⟨m, -, rfl⟩; exact (hP m _).1)
    have hI1 : ∀ j, I j ≤ 1 := fun j =>
      csInf_le_of_le (hbddB j) ⟨j, Set.mem_Ici.2 le_rfl, rfl⟩ (hP j _).2
    have hbelow : IsBoundedUnder (· ≥ ·) atTop I := isBoundedUnder_of ⟨0, hI0⟩
    have habove : IsBoundedUnder (· ≤ ·) atTop I := isBoundedUnder_of ⟨1, hI1⟩
    refine le_antisymm
      (limsup_le_of_le hbelow.isCoboundedUnder_le (Eventually.of_forall hI1)) ?_
    have hge : ∀ ε > (0 : ℝ), 1 - ε ≤ limsup I atTop := by
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.1
        (hone.eventually (lt_mem_nhds (by linarith : 1 - ε < 1)))
      have hfreq : ∃ᶠ j in atTop, 1 - ε ≤ I j := by
        refine (hrev₀.and_eventually (eventually_ge_atTop N)).mono ?_
        rintro j ⟨hj, hjN⟩
        refine le_csInf (hne j) ?_
        rintro _ ⟨m, hm, rfl⟩
        show 1 - ε ≤ P m (π (κ j))
        rw [hj]
        exact (hN m (le_trans hjN hm)).le
      exact le_limsup_of_frequently_le hfreq habove
    by_contra hlt
    rw [not_le] at hlt
    have := hge ((1 - limsup I atTop) / 2) (by linarith)
    linarith

end Cleanroom.Li.LiDiagonal
