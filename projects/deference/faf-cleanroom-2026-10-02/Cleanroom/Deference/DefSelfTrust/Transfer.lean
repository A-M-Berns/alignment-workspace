import Cleanroom.Deference.DefSelfTrust.Comb

/-!
# `def-self-trust` — target 1c: the quote-transfer lemma

FAF's `thm:cee`/`thm:ccee`/`thm:st` endpoints are stated at FAF's **own** quote LUVs (the
`RationalQuoteCode` families the market program names). `def-lattice`'s notions quantify over
**every** e.c. quote LUV that reflects the same number in every completed-theory world
(`Reflects`, `WeightQuote`, `CondQuote`). The bridge is the lemma below: two e.c. LUV families
valued, in every completed-theory world, within vanishing slacks of the *same* world-indexed
number have asymptotically equal diagonal expectations. It is `thm:expprovind` on the two-term
bet `Z₁ − Z₂` (world value within `s₁ n + s₂ n` of `0`), through the eventual form of
`Comb.lean` (the slacks make the bound eventual, not uniform).

With it, every "at my own quote" theorem of FAF becomes the corresponding "at every reflecting
quote" notion of `def-lattice`, which is what targets 1a, 1b, 2, 4, 9, 10 use.
-/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice

variable {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]

/-- **The quote-transfer lemma.** Two e.c. LUV families `Z₁ Z₂` and a world-indexed value map
`ν`: if every completed-theory world `v` values `Zᵢ n` within `sᵢ n` of `ν n v`, with
`s₁, s₂ → 0`, then `E_n(Z₁ n) ≈ₙ E_n(Z₂ n)`. The witness pair of record is FAF's
`paperDeferredExpectationQuoteCode` against any `Reflects`-quote of the same deferred
expectation (target 1a: `ν n v := E_{f n}(X n)`, both slacks `0`).
Source: mandate target 1c; LI paper `thm:expprovind` (`main.tex` 4.8.10) on the bet `Z₁ − Z₂`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem expect_asympEq_of_reflected_within {Z₁ Z₂ : ℕ → LUV}
    (h₁ : LUV.MachineThresholdCodeSeq Z₁) (h₂ : LUV.MachineThresholdCodeSeq Z₂)
    (ν : ℕ → PCWorld → ℝ) {s₁ s₂ : ℕ → ℝ}
    (hs₁ : Tendsto s₁ atTop (𝓝 0)) (hs₂ : Tendsto s₂ atTop (𝓝 0))
    (hr₁ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ z, v.ValuesAt (Z₁ n) z ∧ |z - ν n v| ≤ s₁ n)
    (hr₂ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ z, v.ValuesAt (Z₂ n) z ∧ |z - ν n v| ≤ s₂ n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (Z₁ n).expect P n) ≈ₙ (fun n => (Z₂ n).expect P n) := by
  set terms : List (ℚ × (ℕ → LUV)) := [(1, Z₁), (-1, Z₂)] with hterms
  have hcodes : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h₁
    · exact h₂
  have hbdd : ∀ n, (constComb 0 terms n).l1Norm P ≤ 2 := fun n => by
    norm_num [constComb_l1Norm, hterms]
  have hwv : LUVCombination.WorldValued (constComb 0 terms) DP := fun n v hv => by
    obtain ⟨z₁, hz₁, -⟩ := hr₁ n v hv
    obtain ⟨z₂, hz₂, -⟩ := hr₂ n v hv
    refine ⟨worldValue v, fun p hp => ?_⟩
    obtain ⟨q, hq, hpq⟩ := mem_constComb_terms hp
    rw [hpq]
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact valuesAt_worldValue hz₁
    · exact valuesAt_worldValue hz₂
  have hval : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ∀ ν', (constComb 0 terms n).ValuesAt v ν' → |(constComb 0 terms n).value P ν'| ≤ ε := by
    intro ε hε
    have hsum : Tendsto (fun n => s₁ n + s₂ n) atTop (𝓝 0) := by simpa using hs₁.add hs₂
    filter_upwards [hsum.eventually (gt_mem_nhds hε)] with n hn v hv ν' hν'
    obtain ⟨z₁, hz₁, hb₁⟩ := hr₁ n v hv
    obtain ⟨z₂, hz₂, hb₂⟩ := hr₂ n v hv
    have e₁ : ν' (Z₁ n) = z₁ :=
      (hν' (EF.const 1, Z₁ n) (by simp [constComb, hterms])).eq hz₁
    have e₂ : ν' (Z₂ n) = z₂ :=
      (hν' (EF.const (-1), Z₂ n) (by simp [constComb, hterms])).eq hz₂
    have hkey : (constComb 0 terms n).value P ν' = z₁ - z₂ := by
      rw [constComb_value]
      simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e₁, e₂]
      push_cast
      ring
    rw [hkey]
    calc |z₁ - z₂| = |(z₁ - ν n v) - (z₂ - ν n v)| := by ring_nf
      _ ≤ |z₁ - ν n v| + |z₂ - ν n v| := abs_sub _ _
      _ ≤ s₁ n + s₂ n := add_le_add hb₁ hb₂
      _ ≤ ε := hn.le
  have hD := expect_asympEq_zero_of_eventually_abs_le (constCombSyntax 0 terms hcodes) hbdd
    hwv hval hworld
  have hE : ∀ n, (constComb 0 terms n).expect P n =
      (Z₁ n).expect P n - (Z₂ n).expect P n := fun n => by
    rw [constComb_expect]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring
  unfold AsympEq at hD ⊢
  simpa [hE] using hD

/-- **The exact case:** both families valued exactly at `ν n v` (slack `0`).
Source: mandate target 1c ("also the exact case")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem expect_asympEq_of_reflected_exact {Z₁ Z₂ : ℕ → LUV}
    (h₁ : LUV.MachineThresholdCodeSeq Z₁) (h₂ : LUV.MachineThresholdCodeSeq Z₂)
    (ν : ℕ → PCWorld → ℝ)
    (hr₁ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.ValuesAt (Z₁ n) (ν n v))
    (hr₂ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.ValuesAt (Z₂ n) (ν n v))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (Z₁ n).expect P n) ≈ₙ (fun n => (Z₂ n).expect P n) :=
  expect_asympEq_of_reflected_within h₁ h₂ ν (s₁ := fun _ => 0) (s₂ := fun _ => 0)
    tendsto_const_nhds tendsto_const_nhds
    (fun n v hv => ⟨_, hr₁ n v hv, by simp⟩) (fun n v hv => ⟨_, hr₂ n v hv, by simp⟩) hworld

/-- Transport of a product-form inequality `A − s·B ≳ₙ 0` along `A₁ ≈ₙ A₂`, `B₁ ≈ₙ B₂`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem asympGE_zero_of_asympEq_pair {A₁ A₂ B₁ B₂ : ℕ → ℝ} (s : ℝ) (hA : A₁ ≈ₙ A₂)
    (hB : B₁ ≈ₙ B₂) (h : (fun n => A₂ n - s * B₂ n) ≳ₙ (fun _ => (0 : ℝ))) :
    (fun n => A₁ n - s * B₁ n) ≳ₙ (fun _ => (0 : ℝ)) :=
  AsympLE.trans_asympEq h (hA.sub (hB.const_mul s)).symm

/-- Transport of a product-form inequality `A − s·B ≲ₙ 0` along `A₁ ≈ₙ A₂`, `B₁ ≈ₙ B₂`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem asympLE_zero_of_asympEq_pair {A₁ A₂ B₁ B₂ : ℕ → ℝ} (s : ℝ) (hA : A₁ ≈ₙ A₂)
    (hB : B₁ ≈ₙ B₂) (h : (fun n => A₂ n - s * B₂ n) ≲ₙ (fun _ => (0 : ℝ))) :
    (fun n => A₁ n - s * B₁ n) ≲ₙ (fun _ => (0 : ℝ)) :=
  AsympEq.trans_asympLE (hA.sub (hB.const_mul s)) h

end Cleanroom.Deference.DefSelfTrust
