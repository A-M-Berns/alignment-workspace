import Cleanroom.Deference.DefSelfTrust.Comb
import Cleanroom.Deference.DefSelfTrust.Weights

/-!
# `def-self-trust` — LUV combinations with generable-feature coefficients

`Comb.lean`'s `constComb` has literal rational coefficients. Lemma B (target 5, vq-wiki-062)
needs the bet `c_n · X_n − ⌜X_n c_n⌝` whose coefficient `c_n` is a **P-generable rational** —
a feature of the market's own prices, not a literal (FAF's `lic_linearity_of_expectation_seq`
makes the same point: "the coefficients are the paper's ℙ-generable sequences, carried by their
generating features"). `featComb` is the constant-coefficient constructor with the constant and
every coefficient a `PGenerableWeighting` progression (`GeneratedRatFeature` minus its
denotation clause), with the same dispatch-by-list syntax as `constComb`.
-/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology

noncomputable section

/-- The LUV combination `c₀(n) + Σ pᵢ.1(n) · pᵢ.2(n)` with feature progressions as the constant
and the coefficients.
Source: none: infrastructure (FAF `LUVCombination`, `def:luv`; `thm:loe`'s feature coefficients)
Kind: D
Fidelity: n/a -/
def featComb (c₀ : ℕ → EF) (terms : List ((ℕ → EF) × (ℕ → LUV))) (n : ℕ) : LUVCombination :=
  ⟨c₀ n, terms.map (fun p => (p.1 n, p.2 n))⟩

/-- The diagonal expectation of a feature-coefficient combination.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma featComb_expect (P : History) (c₀ : ℕ → EF) (terms : List ((ℕ → EF) × (ℕ → LUV)))
    (n : ℕ) :
    (featComb c₀ terms n).expect P n =
      (c₀ n).denote P + (terms.map (fun p => (p.1 n).denote P * (p.2 n).expect P n)).sum := by
  simp [featComb, LUVCombination.expect, LUVCombination.expectAt, LUV.expect, List.map_map,
    Function.comp_def]

/-- The world value of a feature-coefficient combination under a valuation `ν`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma featComb_value (P : History) (c₀ : ℕ → EF) (terms : List ((ℕ → EF) × (ℕ → LUV)))
    (n : ℕ) (ν : LUV → ℝ) :
    (featComb c₀ terms n).value P ν =
      (c₀ n).denote P + (terms.map (fun p => (p.1 n).denote P * ν (p.2 n))).sum := by
  simp [featComb, LUVCombination.value, List.map_map, Function.comp_def]

/-- The `L¹` norm of a feature-coefficient combination at day `n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma featComb_l1Norm (P : History) (c₀ : ℕ → EF) (terms : List ((ℕ → EF) × (ℕ → LUV)))
    (n : ℕ) :
    (featComb c₀ terms n).l1Norm P =
      |(c₀ n).denote P| + (terms.map (fun p => |(p.1 n).denote P|)).sum := by
  simp [featComb, LUVCombination.l1Norm, LUVCombination.shareNorm, List.map_map,
    Function.comp_def]

/-- A term of `featComb` is a coefficient paired with a member LUV read at day `n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_featComb_terms {c₀ : ℕ → EF} {terms : List ((ℕ → EF) × (ℕ → LUV))} {n : ℕ}
    {p : EF × LUV} (hp : p ∈ (featComb c₀ terms n).terms) :
    ∃ q ∈ terms, p.2 = q.2 n := by
  simp only [featComb, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact ⟨q, hq, rfl⟩

/-- The default coefficient progression (the constant `0`), never read by `terms_eq`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev defaultCoeff : ℕ → EF := fun _ => EF.const 0

/-- The coefficient stream of `featComb`: the `j`-th progression at day `n`, read at the paired
index `⟨n, j⟩`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def featDispatch (cs : List (ℕ → EF)) (z : ℕ) : EF :=
  (cs.getD z.unpair.2 defaultCoeff) z.unpair.1

/-- Every entry of the dispatch is a generable weighting when the listed ones are.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma getD_pgenerable (cs : List (ℕ → EF)) (hcs : ∀ c ∈ cs, PGenerableWeighting c) (j : ℕ) :
    PGenerableWeighting (cs.getD j defaultCoeff) := by
  by_cases hj : j < cs.length
  · rw [List.getD_eq_getElem cs defaultCoeff hj]
    exact hcs _ (List.getElem_mem hj)
  · rw [List.getD_eq_default cs defaultCoeff (not_lt.1 hj)]
    exact constWeighting 0

/-- The coefficient stream is machine-metered (list induction over the progressions' emitters).
Source: none: infrastructure (FAF `MachineSpliceStream.ifZero`, `.comp`)
Kind: L
Fidelity: n/a -/
lemma featDispatch_spliceStream (cs : List (ℕ → EF)) (hcs : ∀ c ∈ cs, PGenerableWeighting c) :
    MachineSpliceStream (fun z => (featDispatch cs z).serialize) := by
  induction cs with
  | nil =>
      exact (MachineSpliceStream.serialize_const 0).of_eq (fun z => by simp [featDispatch])
  | cons c cs ih =>
      have hc : PGenerableWeighting c := hcs c (by simp)
      have ih' := ih (fun d hd => hcs d (by simp [hd]))
      have hrest := ih'.comp unaryRuler_peel
      have hhead := hc.polySeg.comp UnaryRuler.unpairFst
      refine (MachineSpliceStream.ifZero hhead hrest UnaryRuler.unpairSnd).of_eq (fun z => ?_)
      simp only [featDispatch, Nat.unpair_pair]
      split_ifs with hz
      · rw [hz, List.getD_cons_zero]
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
        rw [hk, List.getD_cons_succ, Nat.succ_sub_one]

/-- The term list of `featComb` is the dispatch streams reassembled along `List.range`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma featComb_terms_eq (c₀ : ℕ → EF) (terms : List ((ℕ → EF) × (ℕ → LUV))) (n : ℕ) :
    (featComb c₀ terms n).terms = (List.range terms.length).map (fun j =>
      (featDispatch (terms.map Prod.fst) (Nat.pair n j),
        luvDispatch (terms.map Prod.snd) (Nat.pair n j))) := by
  induction terms with
  | nil => simp [featComb]
  | cons p ps ih =>
      simp only [featComb, List.map_cons, List.length_cons, List.range_succ_eq_map,
        List.map_map, Function.comp_def, featDispatch, luvDispatch, Nat.unpair_pair,
        List.getD_cons_zero, List.getD_cons_succ]
      simp only [featComb] at ih
      rw [ih]
      simp only [featDispatch, luvDispatch, Nat.unpair_pair]

/-- **Compact syntax for the feature-coefficient combination**, from `PGenerableWeighting`
certificates of the constant and the coefficients and `MachineThresholdCodeSeq` certificates of
the members.
Source: none: infrastructure (FAF API request, feature-coefficient form of `def-lattice` F18)
Kind: D
Fidelity: n/a -/
def featCombSyntax (c₀ : ℕ → EF) (hc₀ : PGenerableWeighting c₀)
    (terms : List ((ℕ → EF) × (ℕ → LUV)))
    (hcoeff : ∀ p ∈ terms, PGenerableWeighting p.1)
    (hluv : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2) :
    LUVCombinationSyntax (featComb c₀ terms) where
  termCount _ := terms.length
  coefficient := featDispatch (terms.map Prod.fst)
  luv := luvDispatch (terms.map Prod.snd)
  termCount_poly := UnaryRuler.const terms.length
  const_poly := hc₀.polySeg
  coefficient_poly := featDispatch_spliceStream _ (fun c hc => by
    simp only [List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    exact hcoeff p hp)
  threshold_poly := luvDispatch_machineThresholdCodeSeq _ (fun X hX => by
    simp only [List.mem_map] at hX
    obtain ⟨p, hp, rfl⟩ := hX
    exact hluv p hp)
  terms_eq n := featComb_terms_eq c₀ terms n
  const_rank n := hc₀.rank_le n
  coefficient_rank n j _ := by
    simp only [featDispatch, Nat.unpair_pair]
    exact (getD_pgenerable _ (fun c hc => by
      simp only [List.mem_map] at hc
      obtain ⟨p, hp, rfl⟩ := hc
      exact hcoeff p hp) j).rank_le n
  const_closed n ρ V := hc₀.closed n ρ V
  coefficient_closed z ρ V := by
    simp only [featDispatch]
    exact (getD_pgenerable _ (fun c hc => by
      simp only [List.mem_map] at hc
      obtain ⟨p, hp, rfl⟩ := hc
      exact hcoeff p hp) z.unpair.2).closed z.unpair.1 ρ V

end

end Cleanroom.Deference.DefSelfTrust
