import Cleanroom.Found.DefLattice.TwoOptionLUV
import Cleanroom.Found.LiAsympCalc.Ramp

/-!
# `def-lattice-arrows` — packages and the eventual/slack forms of provability induction

Package `def-lattice-arrows` (faf-cleanroom run, 2026-09-30), file 1. Three things every arrow
of the deference lattice consumes:

* **A. Constant-coefficient LUV combinations over a list of LUV sequences** (`listComb`), with
  their `LUVCombinationSyntax` and `BoundedSequence` certificates built from the code
  certificates of the member sequences and a machine-metered constant stream. This is the
  general form of def-lattice's `hardSelectionSyntax` (finding F18's FAF API request): a
  combination with arbitrarily many constant-coefficient terms, and a **day-dependent**
  constant, which is what the finite patch below needs.
* **B. The ε-outside pattern, once** (T0). FAF's `lic_expect_combination_provind_ge/le/eq`
  want the world bound on *every* day; the deference packages deliver it *eventually* (the
  weight is eventually `1`; the follower is eventually the gap-bet) or *within a vanishing
  slack*. `expect_listComb_ge_of_eventually` and friends close the gap by patching the
  combination's constant below the day `N` from which the bound holds (`patchConst`), so that
  the patched combination satisfies FAF's all-days premise at `c − ε` and has the same
  expectations from `N` on. FAF's own proof of `thm:expprovind` uses its `hval` only
  eventually, but the two lemmas that would show it (`exists_meshAffine_bounds`,
  `meshAffine_eventually_near`) are `private` in `Construction/LUV/Endpoints.lean`, hence
  this route (an FAF API request: an eventual-`hval` form of `lic_expect_combination_provind_*`).
* **C. The hypothesis packages of the mandate's design decision 2** (`ExpertFoldAt`,
  `ExpertFoldCond`, `ExpertPin`, `GapQuote`, `constLUV`), all in reflection form, all
  asymptotic on the expert side, none containing FAF's `affine` certificate and none asserting
  existence.
* **D. Asymptotic plumbing**: diagonalizing a rational margin, list sums of `≳ₙ 0`, the
  deferred-day subsequence.

Conventions: FAF pin `159ec3f`; `≈ₙ ≲ₙ ≳ₙ` are FAF's `AsympEq/LE/GE`; every `hworld` is the
caller obligation of [[faf-map-li]] §5 gap 12.
-/

namespace Cleanroom.Deference.DefLatticeArrows

open LogicalInduction Filter Topology Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc

noncomputable section

/-! ## A. Constant-coefficient combinations over lists of LUV sequences -/

/-- The all-`⊥` threshold family: the out-of-range default of `luvAt`, never valued, never
reached by `terms_eq`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def junkLUV : LUV := ⟨fun _ => (⊥ : Sentence)⟩

/-- The constant junk family is machine-metered (every threshold sentence is `⊥`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma junkLUV_codes : LUV.MachineThresholdCodeSeq (fun _ => junkLUV) :=
  MachineSentenceCodes.const (⊥ : Sentence)

/-- **The combination `c n + ∑ aᵢ · Xᵢ n`** for a rational constant stream `c`, constant
rational coefficients `aᵢ` and LUV sequences `Xᵢ`, given as the list `ts = [(a₁, X₁), …]`.
Every combination this package feeds to `thm:expprovind` is one of these.
Source: none: infrastructure (FAF `LUVCombination`; def-lattice F18)
Kind: D
Fidelity: n/a -/
def listComb (c : ℕ → ℚ) (ts : List (ℚ × (ℕ → LUV))) (n : ℕ) : LUVCombination :=
  ⟨EF.const (c n), ts.map (fun p => (EF.const p.1, p.2 n))⟩

/-- The day-`n` expectation of `listComb` is `c n + ∑ aᵢ · E^H_n(Xᵢ n)` — by definition of
`LUVCombination.expect` (linear in the prices; design decision 4: no `hLoe`).
Source: none: infrastructure (FAF `LUVCombination.expect`)
Kind: L
Fidelity: n/a -/
theorem listComb_expect (P : History) (c : ℕ → ℚ) (ts : List (ℚ × (ℕ → LUV))) (n : ℕ) :
    (listComb c ts n).expect P n =
      (c n : ℝ) + (ts.map (fun p => (p.1 : ℝ) * (p.2 n).expect P n)).sum := by
  simp [listComb, LUVCombination.expect, LUVCombination.expectAt, LUV.expect, List.map_map,
    Function.comp_def]

/-- The world value of `listComb` under a LUV valuation `ν` is `c n + ∑ aᵢ · ν (Xᵢ n)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem listComb_value (P : History) (c : ℕ → ℚ) (ts : List (ℚ × (ℕ → LUV))) (n : ℕ)
    (ν : LUV → ℝ) :
    (listComb c ts n).value P ν = (c n : ℝ) + (ts.map (fun p => (p.1 : ℝ) * ν (p.2 n))).sum := by
  simp [listComb, LUVCombination.value, List.map_map, Function.comp_def]

/-- The `L¹` norm of `listComb` is `|c n| + ∑ |aᵢ|`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem listComb_l1Norm (P : History) (c : ℕ → ℚ) (ts : List (ℚ × (ℕ → LUV))) (n : ℕ) :
    (listComb c ts n).l1Norm P = |(c n : ℝ)| + (ts.map (fun p => |(p.1 : ℝ)|)).sum := by
  simp [listComb, LUVCombination.l1Norm, LUVCombination.shareNorm, List.map_map,
    Function.comp_def]

/-- A world valuation of `listComb` values each member LUV at `ν` of it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem listComb_valuesAt_mem {c : ℕ → ℚ} {ts : List (ℚ × (ℕ → LUV))} {n : ℕ} {v : PCWorld}
    {ν : LUV → ℝ} (hν : (listComb c ts n).ValuesAt v ν) {p : ℚ × (ℕ → LUV)} (hp : p ∈ ts) :
    v.ValuesAt (p.2 n) (ν (p.2 n)) :=
  hν (EF.const p.1, p.2 n) (List.mem_map.mpr ⟨p, hp, rfl⟩)

/-- Every member value of a world valuation of `listComb` lies in `[0,1]`.
Source: none: infrastructure (FAF `PCWorld.ValuesAt`)
Kind: L
Fidelity: n/a -/
theorem listComb_valuesAt_mem_Icc {c : ℕ → ℚ} {ts : List (ℚ × (ℕ → LUV))} {n : ℕ}
    {v : PCWorld} {ν : LUV → ℝ} (hν : (listComb c ts n).ValuesAt v ν) {p : ℚ × (ℕ → LUV)}
    (hp : p ∈ ts) : 0 ≤ ν (p.2 n) ∧ ν (p.2 n) ≤ 1 :=
  ⟨(listComb_valuesAt_mem hν hp).1, (listComb_valuesAt_mem hν hp).2.1⟩

/-- **World-valuedness of `listComb` from world-valuedness of its members** (FAF's
representation premise, derived — no `(b)`, no `(c)`).
Source: none: infrastructure (FAF `LUVCombination.WorldValued`)
Kind: L
Fidelity: n/a -/
theorem listComb_worldValued {DP : DeductiveProcess} (c : ℕ → ℚ) {ts : List (ℚ × (ℕ → LUV))}
    (hts : ∀ p ∈ ts, Valued DP p.2) :
    LUVCombination.WorldValued (listComb c ts) DP := by
  intro n v hv
  refine ⟨worldValue v, ?_⟩
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  obtain ⟨x, hx⟩ := hts p hp n v hv
  exact valuesAt_worldValue hx

/-- `WorldValued` does not see the constant: the terms of `listComb c ts` and `listComb c' ts`
are the same list.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem listComb_worldValued_congr {DP : DeductiveProcess} (c c' : ℕ → ℚ)
    (ts : List (ℚ × (ℕ → LUV))) :
    LUVCombination.WorldValued (listComb c ts) DP ↔
      LUVCombination.WorldValued (listComb c' ts) DP := Iff.rfl

/-- Lower bound on a member sum: with every `ν (Xᵢ n) ∈ [0,1]`, `∑ aᵢ ν(Xᵢ n) ≥ −∑ |aᵢ|`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem listComb_sum_ge_neg {n : ℕ} {ν : LUV → ℝ} :
    ∀ (ts : List (ℚ × (ℕ → LUV))), (∀ p ∈ ts, 0 ≤ ν (p.2 n) ∧ ν (p.2 n) ≤ 1) →
      -(ts.map (fun p => |(p.1 : ℝ)|)).sum ≤ (ts.map (fun p => (p.1 : ℝ) * ν (p.2 n))).sum := by
  intro ts
  induction ts with
  | nil => intro _; simp
  | cons p ts ih =>
    intro h
    have hp := h p (List.mem_cons_self ..)
    have hrest := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons, List.sum_cons]
    have : -|(p.1 : ℝ)| ≤ (p.1 : ℝ) * ν (p.2 n) := by
      rcases le_or_gt 0 (p.1 : ℝ) with h1 | h1
      · rw [abs_of_nonneg h1]; nlinarith [hp.1]
      · rw [abs_of_neg h1]; nlinarith [hp.2]
    linarith

/-- Upper bound on a member sum: `∑ aᵢ ν(Xᵢ n) ≤ ∑ |aᵢ|` when every `ν (Xᵢ n) ∈ [0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem listComb_sum_le {n : ℕ} {ν : LUV → ℝ} :
    ∀ (ts : List (ℚ × (ℕ → LUV))), (∀ p ∈ ts, 0 ≤ ν (p.2 n) ∧ ν (p.2 n) ≤ 1) →
      (ts.map (fun p => (p.1 : ℝ) * ν (p.2 n))).sum ≤ (ts.map (fun p => |(p.1 : ℝ)|)).sum := by
  intro ts
  induction ts with
  | nil => intro _; simp
  | cons p ts ih =>
    intro h
    have hp := h p (List.mem_cons_self ..)
    have hrest := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons, List.sum_cons]
    have : (p.1 : ℝ) * ν (p.2 n) ≤ |(p.1 : ℝ)| := by
      rcases le_or_gt 0 (p.1 : ℝ) with h1 | h1
      · rw [abs_of_nonneg h1]; nlinarith [hp.2]
      · rw [abs_of_neg h1]; nlinarith [hp.1]
    linarith

/-! ### The syntax certificate -/

/-- The coefficient stream of `listComb`: `EF.const` of the `j`-th coefficient (`0` beyond).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def coeffAt (l : List ℚ) (j : ℕ) : EF := EF.const (l.getD j 0)

/-- The LUV stream of `listComb`: the `j`-th member at day `n` (`junkLUV` beyond).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def luvAt (l : List (ℕ → LUV)) (j n : ℕ) : LUV := (l.getD j (fun _ => junkLUV)) n

/-- The coefficient stream is machine-splice-metered along any ruler: two-way dispatch on
the list, by induction, over `serialize_const`.
Source: none: infrastructure (FAF `MachineSpliceStream.ifZero`)
Kind: L
Fidelity: n/a -/
theorem coeffAt_spliceStream (l : List ℚ) :
    ∀ {g : ℕ → ℕ}, UnaryRuler g →
      MachineSpliceStream (fun z => (coeffAt l (g z)).serialize) := by
  induction l with
  | nil =>
    intro g _
    exact (MachineSpliceStream.serialize_const 0).of_eq (fun z => by simp [coeffAt])
  | cons a l ih =>
    intro g hg
    refine (MachineSpliceStream.ifZero (MachineSpliceStream.serialize_const a)
      (ih (hg.sub (UnaryRuler.const 1))) hg).of_eq (fun z => ?_)
    simp only [coeffAt]
    rcases h : g z with _ | k
    · simp
    · simp

/-- The LUV stream is machine-threshold-metered along any pair of rulers, from the members'
certificates: two-way dispatch on the list over `LUV.MachineThresholdCodeSeq.reindex`.
Source: none: infrastructure (FAF `MachineSentenceCodes.ifZero`, def-lattice's
`hardSelectionLuv_machineThresholdCodeSeq` pattern)
Kind: L
Fidelity: n/a -/
theorem luvAt_codes (l : List (ℕ → LUV)) (hl : ∀ X ∈ l, LUV.MachineThresholdCodeSeq X) :
    ∀ {g h : ℕ → ℕ}, UnaryRuler g → UnaryRuler h →
      LUV.MachineThresholdCodeSeq (fun z => luvAt l (g z) (h z)) := by
  induction l with
  | nil =>
    intro g h _ _
    show MachineSentenceCodes (fun m => (luvAt [] (g m.unpair.1) (h m.unpair.1)).gt _)
    exact (MachineSentenceCodes.const (⊥ : Sentence)).of_eq (fun m => by simp [luvAt, junkLUV])
  | cons X l ih =>
    intro g h hg hh
    have hX : LUV.MachineThresholdCodeSeq (fun z => X (h z)) :=
      (hl X (List.mem_cons_self ..)).reindex hh
    have hrest := ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY))
      (hg.sub (UnaryRuler.const 1)) hh
    have hrul : UnaryRuler (fun m : ℕ => g m.unpair.1) := hg.comp UnaryRuler.unpairFst
    unfold LUV.MachineThresholdCodeSeq at hX hrest ⊢
    refine (MachineSentenceCodes.ifZero hX hrest hrul).of_eq (fun m => ?_)
    simp only [luvAt]
    rcases hgm : g m.unpair.1 with _ | k
    · simp
    · simp

/-- **Compact syntax for `listComb`**, from a machine-metered constant stream and the members'
threshold certificates. The paired index `⟨n, j⟩` reads term `j` of day `n`.
Source: none: infrastructure (FAF `LUVCombinationSyntax`; def-lattice F18's API request,
closed here for arbitrary finite term lists and day-dependent constants)
Kind: D
Fidelity: n/a -/
def listCombSyntax (c : ℕ → ℚ) (hc : MachineSpliceStream (fun n => (EF.const (c n)).serialize))
    (ts : List (ℚ × (ℕ → LUV))) (hts : ∀ p ∈ ts, LUV.MachineThresholdCodeSeq p.2) :
    LUVCombinationSyntax (listComb c ts) where
  termCount _ := ts.length
  coefficient z := coeffAt (ts.map Prod.fst) z.unpair.2
  luv z := luvAt (ts.map Prod.snd) z.unpair.2 z.unpair.1
  termCount_poly := UnaryRuler.const _
  const_poly := hc
  coefficient_poly := coeffAt_spliceStream _ UnaryRuler.unpairSnd
  threshold_poly := luvAt_codes _ (fun X hX => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hX
      exact hts p hp) UnaryRuler.unpairSnd UnaryRuler.unpairFst
  terms_eq n := by
    simp only [listComb, Nat.unpair_pair]
    apply List.ext_getElem
    · simp
    · intro j hj₁ hj₂
      simp only [List.length_map] at hj₁
      simp [coeffAt, luvAt, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj₁]
  const_rank n := by simp [listComb]
  coefficient_rank n j _ := by simp [coeffAt]
  const_closed n ρ V := by simp [listComb]
  coefficient_closed z ρ V := by simp [coeffAt]

/-- **`BoundedSequence` for `listComb`** from the syntax certificate and a bound on the
constant stream (the `L¹` norm is `|c n| + ∑ |aᵢ|`).
Source: none: infrastructure (FAF `LUVCombination.BoundedSequence`)
Kind: D
Fidelity: n/a -/
def listComb_boundedSequence (P : History) (c : ℕ → ℚ)
    (hc : MachineSpliceStream (fun n => (EF.const (c n)).serialize)) (B : ℝ)
    (hcB : ∀ n, |(c n : ℝ)| ≤ B) (ts : List (ℚ × (ℕ → LUV)))
    (hts : ∀ p ∈ ts, LUV.MachineThresholdCodeSeq p.2) :
    LUVCombination.BoundedSequence (listComb c ts) P where
  poly := (listCombSyntax c hc ts hts).polySequence
  bounded := ⟨B + (ts.map (fun p => |(p.1 : ℝ)|)).sum, fun n => by
    rw [listComb_l1Norm]; linarith [hcB n]⟩

/-- A constant constant-stream is machine-metered.
Source: none: infrastructure (FAF `MachineSpliceStream.serialize_const`)
Kind: L
Fidelity: n/a -/
theorem constStream_splice (c : ℚ) :
    MachineSpliceStream (fun n : ℕ => (EF.const ((fun _ : ℕ => c) n)).serialize) :=
  MachineSpliceStream.serialize_const c

/-- The finite patch of a constant stream: `L` below day `N`, `c n` from `N` on.
Source: none: infrastructure (the "patch the finitely many early days" step of
[[total-trust-implies-value]] Lemma 1 and [[value-implies-tower]] Step 3)
Kind: D
Fidelity: n/a -/
def patchConst (c : ℕ → ℚ) (N : ℕ) (L : ℚ) : ℕ → ℚ := fun n => if n < N then L else c n

/-- The patched constant stream is machine-metered: dispatch on the ruler `n + 1 − N`, which
vanishes exactly below `N`.
Source: none: infrastructure (FAF `MachineSpliceStream.ifZero`, `UnaryRuler.sub`)
Kind: L
Fidelity: n/a -/
theorem patchConst_splice {c : ℕ → ℚ}
    (hc : MachineSpliceStream (fun n => (EF.const (c n)).serialize)) (N : ℕ) (L : ℚ) :
    MachineSpliceStream (fun n => (EF.const (patchConst c N L n)).serialize) := by
  have hrul : UnaryRuler (fun n : ℕ => n + 1 - N) := UnaryRuler.id.succ.sub (UnaryRuler.const N)
  refine (MachineSpliceStream.ifZero (MachineSpliceStream.serialize_const L) hc hrul).of_eq
    (fun n => ?_)
  simp only [patchConst]
  by_cases h : n < N
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- The patched stream is bounded by the larger of the original bound and `|L|`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem patchConst_bound {c : ℕ → ℚ} {B : ℝ} (hcB : ∀ n, |(c n : ℝ)| ≤ B) (N : ℕ) (L : ℚ)
    (n : ℕ) : |(patchConst c N L n : ℝ)| ≤ max B |(L : ℝ)| := by
  simp only [patchConst]
  split_ifs
  · exact le_max_right _ _
  · exact (hcB n).trans (le_max_left _ _)

/-- From day `N` on the patched and the original combination have the same expectation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem listComb_patch_expect (P : History) (c : ℕ → ℚ) (N : ℕ) (L : ℚ)
    (ts : List (ℚ × (ℕ → LUV))) {n : ℕ} (hn : N ≤ n) :
    (listComb (patchConst c N L) ts n).expect P n = (listComb c ts n).expect P n := by
  simp [listComb_expect, patchConst, not_lt.mpr hn]

/-- The patched and the original combination have the same terms, so the same world
valuations.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem listComb_patch_valuesAt_iff (c : ℕ → ℚ) (N : ℕ) (L : ℚ) (ts : List (ℚ × (ℕ → LUV)))
    (n : ℕ) (v : PCWorld) (ν : LUV → ℝ) :
    (listComb (patchConst c N L) ts n).ValuesAt v ν ↔ (listComb c ts n).ValuesAt v ν :=
  Iff.rfl

/-! ## B. T0 — the ε-outside pattern: eventual and slack-tolerant provability induction -/

/-- **Eventual world bound from below ⟹ asymptotic lower bound** (T0, `≥` form). If for every
`ε > 0` there is a day from which every consistent world values the combination at least
`b − ε`, then `E^H_n(As n) ≳ₙ b`. Proof: fix `ε`; patch the constant of the combination below
the day `N` given by `ε/2` to a rational `L` so large that the patched value is `≥ b − ε/2`
on every day (member values lie in `[0,1]`, so the sum is at least `−∑|aᵢ|`); FAF's
`lic_expect_combination_provind_ge` at `b − ε/2` on the patched sequence (whose
`BoundedSequence` certificate is `listComb_boundedSequence` on the patched stream); from `N`
on the two expectations agree. The world bound is asked *eventually*, never on all days —
the mandate's T0 trap avoided.
Source: mandate T0; [[total-trust-implies-value]] §Lemma 1 (the ε-outside pattern);
FAF `thm:expprovind` (`Construction/LUV/Endpoints.lean`)
Kind: C
Fidelity: stronger: FAF's all-days `hval` relaxed to an eventual one (finite patch)
Hyps: (a) — the combination's code certificates, `hworld` (FAF endpoint premise) -/
theorem expect_listComb_ge_of_eventually {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] {c : ℕ → ℚ}
    (hc : MachineSpliceStream (fun n => (EF.const (c n)).serialize)) {B : ℝ}
    (hcB : ∀ n, |(c n : ℝ)| ≤ B) {ts : List (ℚ × (ℕ → LUV))}
    (hts : ∀ p ∈ ts, LUV.MachineThresholdCodeSeq p.2)
    (hwv : LUVCombination.WorldValued (listComb c ts) DP) (b : ℝ)
    (hval : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ∀ ν, (listComb c ts n).ValuesAt v ν → b - ε ≤ (listComb c ts n).value P ν)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (listComb c ts n).expect P n) ≳ₙ (fun _ => b) := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hval (ε / 2) (by positivity))
  obtain ⟨L, hL⟩ := exists_rat_gt (|b| + (ts.map (fun p => |(p.1 : ℝ)|)).sum)
  have hpatch := lic_expect_combination_provind_ge
    (listComb_boundedSequence P (patchConst c N L) (patchConst_splice hc N L)
      (max B |(L : ℝ)|) (patchConst_bound hcB N L) ts hts)
    ((listComb_worldValued_congr c (patchConst c N L) ts).mp hwv) (b - ε / 2)
    (fun n v hv ν hν => by
      rw [listComb_patch_valuesAt_iff] at hν
      by_cases hn : n < N
      · rw [listComb_value]
        simp only [patchConst, if_pos hn]
        have hsum := listComb_sum_ge_neg (ν := ν) (n := n) ts
          (fun p hp => listComb_valuesAt_mem_Icc hν hp)
        have hb : b ≤ |b| := le_abs_self b
        linarith
      · have h := hN n (not_lt.mp hn) v hv ν hν
        rw [listComb_value] at h ⊢
        simp only [patchConst, if_neg hn]
        exact h) hworld
  have h2 := hpatch (ε / 2) (by positivity)
  filter_upwards [h2, eventually_ge_atTop N] with n hn hNn
  rw [listComb_patch_expect P c N L ts hNn] at hn
  linarith

/-- **Eventual world bound from above ⟹ asymptotic upper bound** (T0, `≤` form): the mirror
of `expect_listComb_ge_of_eventually` (patch with a very negative constant).
Source: mandate T0; FAF `thm:expprovind`
Kind: C
Fidelity: stronger: eventual `hval`
Hyps: (a) -/
theorem expect_listComb_le_of_eventually {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] {c : ℕ → ℚ}
    (hc : MachineSpliceStream (fun n => (EF.const (c n)).serialize)) {B : ℝ}
    (hcB : ∀ n, |(c n : ℝ)| ≤ B) {ts : List (ℚ × (ℕ → LUV))}
    (hts : ∀ p ∈ ts, LUV.MachineThresholdCodeSeq p.2)
    (hwv : LUVCombination.WorldValued (listComb c ts) DP) (b : ℝ)
    (hval : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ∀ ν, (listComb c ts n).ValuesAt v ν → (listComb c ts n).value P ν ≤ b + ε)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (listComb c ts n).expect P n) ≲ₙ (fun _ => b) := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hval (ε / 2) (by positivity))
  obtain ⟨L, hL⟩ := exists_rat_gt (|b| + (ts.map (fun p => |(p.1 : ℝ)|)).sum)
  have hpatch := lic_expect_combination_provind_le
    (listComb_boundedSequence P (patchConst c N (-L)) (patchConst_splice hc N (-L))
      (max B |((-L : ℚ) : ℝ)|) (patchConst_bound hcB N (-L)) ts hts)
    ((listComb_worldValued_congr c (patchConst c N (-L)) ts).mp hwv) (b + ε / 2)
    (fun n v hv ν hν => by
      rw [listComb_patch_valuesAt_iff] at hν
      by_cases hn : n < N
      · rw [listComb_value]
        simp only [patchConst, if_pos hn]
        have hsum := listComb_sum_le (ν := ν) (n := n) ts
          (fun p hp => listComb_valuesAt_mem_Icc hν hp)
        have hb : -b ≤ |b| := neg_le_abs b
        push_cast
        linarith
      · have h := hN n (not_lt.mp hn) v hv ν hν
        rw [listComb_value] at h ⊢
        simp only [patchConst, if_neg hn]
        exact h) hworld
  have h2 := hpatch (ε / 2) (by positivity)
  filter_upwards [h2, eventually_ge_atTop N] with n hn hNn
  rw [listComb_patch_expect P c N (-L) ts hNn] at hn
  linarith

/-- **Eventual two-sided world bound ⟹ asymptotic equality** (T0, `=` form).
Source: mandate T0; FAF `thm:expprovind`
Kind: C
Fidelity: stronger: eventual `hval`
Hyps: (a) -/
theorem expect_listComb_eq_of_eventually {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] {c : ℕ → ℚ}
    (hc : MachineSpliceStream (fun n => (EF.const (c n)).serialize)) {B : ℝ}
    (hcB : ∀ n, |(c n : ℝ)| ≤ B) {ts : List (ℚ × (ℕ → LUV))}
    (hts : ∀ p ∈ ts, LUV.MachineThresholdCodeSeq p.2)
    (hwv : LUVCombination.WorldValued (listComb c ts) DP) (b : ℝ)
    (hval : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ∀ ν, (listComb c ts n).ValuesAt v ν → |(listComb c ts n).value P ν - b| ≤ ε)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (listComb c ts n).expect P n) ≈ₙ (fun _ => b) := by
  rw [asympEq_iff_asympLE_asympGE]
  constructor
  · refine expect_listComb_le_of_eventually hc hcB hts hwv b (fun ε hε => ?_) hworld
    filter_upwards [hval ε hε] with n hn v hv ν hν
    have := hn v hv ν hν
    rw [abs_le] at this
    linarith [this.2]
  · refine expect_listComb_ge_of_eventually hc hcB hts hwv b (fun ε hε => ?_) hworld
    filter_upwards [hval ε hε] with n hn v hv ν hν
    have := hn v hv ν hν
    rw [abs_le] at this
    linarith [this.1]

/-- **World bound within a vanishing slack on every day ⟹ asymptotic equality** (T0, slack
form: the `dd:mesh` shape the quote packages deliver).
Source: mandate T0; FAF `thm:expprovind`, `dd:mesh`
Kind: C
Fidelity: stronger: the bound within a vanishing slack rather than exact
Hyps: (a) -/
theorem expect_listComb_eq_of_slack {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] {c : ℕ → ℚ}
    (hc : MachineSpliceStream (fun n => (EF.const (c n)).serialize)) {B : ℝ}
    (hcB : ∀ n, |(c n : ℝ)| ≤ B) {ts : List (ℚ × (ℕ → LUV))}
    (hts : ∀ p ∈ ts, LUV.MachineThresholdCodeSeq p.2)
    (hwv : LUVCombination.WorldValued (listComb c ts) DP) (b : ℝ) {slack : ℕ → ℝ}
    (hsl : Tendsto slack atTop (𝓝 0))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∀ ν, (listComb c ts n).ValuesAt v ν → |(listComb c ts n).value P ν - b| ≤ slack n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (listComb c ts n).expect P n) ≈ₙ (fun _ => b) := by
  refine expect_listComb_eq_of_eventually hc hcB hts hwv b (fun ε hε => ?_) hworld
  filter_upwards [hsl.eventually (gt_mem_nhds hε)] with n hn v hv ν hν
  exact (hval n v hv ν hν).trans hn.le

/-! ## C. The hypothesis packages (design decision 2) -/

/-- **The expert's fold at a weight function** (asymptotic; never exact): the expert's estimate
of the product quote `XW` is asymptotically the weight of its estimate times its estimate,
`E*(XW_n) ≈ₙ wt(E*(X_n)) · E*(X_n)`. This is [[tower-implies-total-trust]] fact (b) ("the
expert folds the weight out", its own `loe` with the weight as a generable coefficient) in the
ε-slack form. For the self-expert it is the shape of FAF's `thm:loe`/`thm:er` at the deferred
day `f n` (a pull-back not in FAF: `li-quote-lane` target (5)), hence `(b)`; for a general
expert `(c)`. An exact fold `∀ n, E*(XW_n) = wt(E*(X_n)) · E*(X_n)` is false on FAF's grid
expectation (def-lattice F3; `bli-exactness` X2) and is never assumed here.
Source: [[tower-implies-total-trust]] §Three facts (b); mandate design decision 2
Kind: D
Fidelity: variant: asymptotic (the corpus's "provably" is the exact grade, refuted at
finite days) -/
def ExpertFoldAt (DP : DeductiveProcess) (E : Expert DP) (X : ℕ → LUV) (wt : ℝ → ℝ)
    (XW : ℕ → LUV) : Prop :=
  (fun n => E.estimate XW n) ≈ₙ (fun n => wt (E.estimate X n) * E.estimate X n)

/-- **The expert's fold at a P-generable weight sequence** (the `ccee`-shaped fold), at FAF's
deferred-day index: `E*(Z_n) ≈ₙ E*(X_n) · w (f n)` for the left product `Z` of a `CondQuote`.
Source: [[tower-implies-total-trust]] §The other direction (the fold equality); v6 §1.5;
mandate T3 (the introspection input, precisely)
Kind: D
Fidelity: variant: asymptotic; weight at `w (E.f n)` (def-lattice F2) -/
def ExpertFoldCond (DP : DeductiveProcess) (E : Expert DP) (X : ℕ → LUV) (w : ℕ → ℚ)
    (Z : ℕ → LUV) : Prop :=
  (fun n => E.estimate Z n) ≈ₙ (fun n => E.estimate X n * (w (E.f n) : ℝ))

/-- **The expert's pin**: its estimate of the sequence `G` converges to the constant `c`
(asymptotic, never exact — def-lattice F3: even the estimate of a LUV valued `c` in every
world is a grid average).
Source: [[value-implies-tower]] §Proof Step 1 ("the expert quotes the gap-bet at zero");
[[total-trust-implies-mart]] ⚠ ("`E^A_n(D_n) → 0`"); mandate design decision 2
Kind: D
Fidelity: variant: asymptotic -/
def ExpertPin {DP : DeductiveProcess} (E : Expert DP) (G : ℕ → LUV) (c : ℝ) : Prop :=
  (fun n => E.estimate G n) ≈ₙ (fun _ => c)

/-- The `[0,1]`-rescaled signed gap: `(a · (z − y) + 1) / 2`, with `a = 1` the gap-bet
`Z − ⌜E*(Z)⌝` and `a = −1` its mirror, both rescaled from `[−1, 1]` to `[0, 1]`.
Source: [[total-trust-implies-mart]] §Threshold-range remark (`D' := (D + 1)/2`);
[[value-implies-tower]] §Setting (the gap-bet `G_n`)
Kind: D
Fidelity: variant: rescaled -/
def gapValue (a : ℚ) (z y : ℝ) : ℝ := ((a : ℝ) * (z - y) + 1) / 2

/-- **The gap-bet quote package**: `Y` reflects `E*(Z)`, `Z` is world-valued, and the e.c. LUV
`G` is valued within a vanishing `slack n` at the rescaled signed gap
`gapValue a z (E*(Z_n)) = (a (z − E*(Z_n)) + 1)/2` whenever `Z n` is valued at `z`. The
gap-bet `Z − ⌜E*(Z)⌝` is a `LUVCombination`; the menu and Total-Trust quantifiers of
`def-lattice` range over LUVs, so the arrows T5 and T11 need it *as a LUV*, which is what `G`
is (the `[0,1]` rescaling is forced by FAF's `[0,1]`-LUVs). No existence is claimed: for a
general expert this package is `li-quote-lane`'s, and every headline that assumes one exists
discloses it.
Source: [[value-implies-tower]] §Setting; [[total-trust-implies-mart]] §Proof;
mandate design decision 2
Kind: D
Fidelity: variant: rescaled to `[0,1]`; within FAF's vanishing slack -/
structure GapQuote (DP : DeductiveProcess) (E : Expert DP) (Z Y : ℕ → LUV) (a : ℚ)
    (G : ℕ → LUV) where
  /-- the gap LUV is efficiently describable -/
  codes : LUV.MachineThresholdCodeSeq G
  /-- the per-day reflection slack -/
  slack : ℕ → ℝ
  /-- the slack vanishes -/
  slack_tendsto : Tendsto slack atTop (𝓝 0)
  /-- every completed-theory world values the source -/
  source_valued : Valued DP Z
  /-- `Y` is the quote `⌜E*(Z)⌝` -/
  reflects : Reflects DP E Z Y
  /-- the gap LUV is valued within `slack n` of the rescaled signed gap -/
  gap_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∀ z,
    v.ValuesAt (Z n) z → ∃ g, v.ValuesAt (G n) g ∧ |g - gapValue a z (E.estimate Z n)| ≤ slack n

/-- **The constant LUV** valued `s`: threshold `⊤` below `s`, `⊥` from `s` (FAF has no constant
LUV; constants otherwise enter only through `LUVCombination.const`). A menu needs its constant
option *as a LUV*.
Source: [[value-implies-tower]] §The probe menu (`const(−ε)`, rescaled); mandate design
decision 2
Kind: D
Fidelity: exact (for `s ∈ [0,1]`, the range of FAF's LUVs) -/
def constLUV (s : ℚ) : LUV where
  gt r := if r < s then (⊤ : Sentence) else (⊥ : Sentence)

/-- Every world values `constLUV s` at `s`, for `s ∈ [0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem constLUV_valuesAt {s : ℚ} (hs : 0 ≤ s ∧ s ≤ 1) (v : PCWorld) :
    v.ValuesAt (constLUV s) s := by
  refine ⟨by exact_mod_cast hs.1, by exact_mod_cast hs.2, fun r => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h' : r < s := by exact_mod_cast h
    simpa [constLUV, h'] using PCWorld.holds_top v
  · have h' : ¬ r < s := not_lt.mpr (by exact_mod_cast h.le)
    simp only [constLUV, if_neg h']
    simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val]

/-- The constant family `fun _ => constLUV s` is world-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem constLUV_valued {s : ℚ} (hs : 0 ≤ s ∧ s ≤ 1) (DP : DeductiveProcess) :
    Valued DP (fun _ => constLUV s) :=
  fun _ v _ => ⟨s, constLUV_valuesAt hs v⟩

/-- The rational comparison `i / k < p / q` (naturals, `q > 0`) as a ruler test: zero exactly
when the comparison holds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem constLUV_test_ruler (p q : ℕ) :
    UnaryRuler (fun m : ℕ => if m.unpair.2.unpair.1 = 0 then (if 0 < p then 0 else 1)
      else m.unpair.2.unpair.2 * q + 1 - p * m.unpair.2.unpair.1) := by
  have hk : UnaryRuler (fun m : ℕ => m.unpair.2.unpair.1) :=
    UnaryRuler.unpairFst.comp UnaryRuler.unpairSnd
  have hi : UnaryRuler (fun m : ℕ => m.unpair.2.unpair.2) :=
    UnaryRuler.unpairSnd.comp UnaryRuler.unpairSnd
  exact hk.ifZero (UnaryRuler.const _) (((hi.mul (UnaryRuler.const q)).succ).sub
    ((UnaryRuler.const p).mul hk))

/-- **The constant family is machine-metered** for `s ≥ 0`: the threshold sentence at the
grid point `i/k` is `⊤` iff `i/k < s = p/q`, which the ruler `constLUV_test_ruler` decides
(`i·q < p·k` for `k > 0`; `0 < p` at `k = 0`, where FAF's `i/0 = 0`).
Source: none: infrastructure (FAF `MachineSentenceCodes.ifZero`; mandate design decision 2)
Kind: L
Fidelity: n/a -/
theorem constLUV_codes {s : ℚ} (hs : 0 ≤ s) :
    LUV.MachineThresholdCodeSeq (fun _ => constLUV s) := by
  set p : ℕ := s.num.toNat with hp
  set q : ℕ := s.den with hq
  have hnum : (s.num.toNat : ℤ) = s.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hs)
  have hsq : s = (p : ℚ) / (q : ℚ) := by
    rw [← Rat.num_div_den s]
    congr 1
    · rw [hp]; exact_mod_cast hnum.symm
  have hqpos : (0 : ℚ) < q := by rw [hq]; exact_mod_cast s.den_pos
  unfold LUV.MachineThresholdCodeSeq
  refine (MachineSentenceCodes.ifZero (MachineSentenceCodes.const (⊤ : Sentence))
    (MachineSentenceCodes.const (⊥ : Sentence)) (constLUV_test_ruler p q)).of_eq (fun m => ?_)
  simp only [constLUV]
  set k : ℕ := m.unpair.2.unpair.1
  set i : ℕ := m.unpair.2.unpair.2
  by_cases hk : k = 0
  · simp only [hk, if_true, Nat.cast_zero, div_zero]
    by_cases hp0 : 0 < p
    · have : (0 : ℚ) < s := by rw [hsq]; positivity
      simp [hp0, this]
    · have hp0' : p = 0 := by omega
      have : ¬ (0 : ℚ) < s := by rw [hsq, hp0']; simp
      simp [hp0, this]
  · have hkpos : (0 : ℚ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    simp only [hk, if_false]
    have key : ((i : ℚ) / (k : ℚ) < s) ↔ (i * q + 1 - p * k = 0) := by
      rw [hsq, div_lt_div_iff₀ hkpos hqpos]
      constructor
      · intro h
        have : i * q < p * k := by exact_mod_cast h
        omega
      · intro h
        have : i * q < p * k := by omega
        exact_mod_cast this
    by_cases hlt : (i : ℚ) / (k : ℚ) < s
    · rw [if_pos (key.mp hlt), if_pos hlt]
    · rw [if_neg (fun hc => hlt (key.mpr hc)), if_neg hlt]

/-! ## D. Asymptotic plumbing -/

/-- The ramp on its linear piece: `ctsInd δ x t = (x − t)/δ` for `t ≤ x ≤ t + δ`.
Source: none: infrastructure (FAF `ctsInd`)
Kind: L
Fidelity: n/a -/
theorem ctsInd_eq_div {δ : ℚ} (hδ : 0 < δ) {x t : ℝ} (h1 : t ≤ x) (h2 : x ≤ t + δ) :
    ctsInd δ x t = (x - t) / δ := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold ctsInd
  have h0 : 0 ≤ (x - t) / (δ : ℝ) := div_nonneg (by linarith) hδR.le
  have h1' : (x - t) / (δ : ℝ) ≤ 1 := by rw [div_le_one hδR]; linarith
  rw [max_eq_right h0, min_eq_right h1']

/-- **Diagonalizing a rational margin**: `f ≳ₙ v − ε` for every rational `ε > 0` gives
`f ≳ₙ v`.
Source: none: infrastructure ([[total-trust-implies-value]] Lemma 1: "ε > 0 was arbitrary")
Kind: L
Fidelity: n/a -/
theorem asympGE_of_forall_rat_sub {f : ℕ → ℝ} {v : ℝ}
    (h : ∀ ε : ℚ, 0 < ε → f ≳ₙ (fun _ => v - (ε : ℝ))) : f ≳ₙ (fun _ => v) := by
  intro ε hε
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn (half_pos hε)
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  filter_upwards [h q hq0' (ε / 2) (half_pos hε)] with n hn
  linarith

/-- **Diagonalizing a rational margin, small margins only**: `f ≳ₙ v − ε` for every rational
`0 < ε ≤ η` gives `f ≳ₙ v` (what an arrow that may only use thresholds in `[0,1]` needs).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem asympGE_of_forall_rat_sub_le {f : ℕ → ℝ} {v : ℝ} {η : ℚ} (hη : 0 < η)
    (h : ∀ ε : ℚ, 0 < ε → ε ≤ η → f ≳ₙ (fun _ => v - (ε : ℝ))) : f ≳ₙ (fun _ => v) := by
  intro ε hε
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn (half_pos hε)
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  have hmin0 : (0 : ℚ) < min q η := lt_min hq0' hη
  have hminε : ((min q η : ℚ) : ℝ) ≤ ε / 2 := by
    have : ((min q η : ℚ) : ℝ) ≤ q := by exact_mod_cast min_le_left q η
    linarith
  filter_upwards [h (min q η) hmin0 (min_le_right q η) (ε / 2) (half_pos hε)] with n hn
  linarith

/-- **Diagonalizing a rational margin**, upper form: `f ≲ₙ v + ε` for every rational `ε > 0`
gives `f ≲ₙ v`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem asympLE_of_forall_rat_add {f : ℕ → ℝ} {v : ℝ}
    (h : ∀ ε : ℚ, 0 < ε → f ≲ₙ (fun _ => v + (ε : ℝ))) : f ≲ₙ (fun _ => v) := by
  intro ε hε
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn (half_pos hε)
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  filter_upwards [h q hq0' (ε / 2) (half_pos hε)] with n hn
  linarith

/-- A list sum of sequences each `≳ₙ 0` is `≳ₙ 0`.
Source: none: infrastructure (FAF `AsympLE.add`)
Kind: L
Fidelity: n/a -/
theorem asympGE_zero_list_sum {ι : Type*} (f : ι → ℕ → ℝ) :
    ∀ (l : List ι), (∀ k ∈ l, f k ≳ₙ (fun _ => (0 : ℝ))) →
      (fun n => (l.map (fun k => f k n)).sum) ≳ₙ (fun _ => (0 : ℝ)) := by
  intro l
  induction l with
  | nil => intro _; simpa using AsympEq.asympGE (AsympEq.refl (fun _ => (0 : ℝ)))
  | cons k l ih =>
    intro h
    have hk := h k (List.mem_cons_self ..)
    have hl := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    have := AsympLE.add hk hl
    simp only [List.map_cons, List.sum_cons]
    intro ε hε
    filter_upwards [this ε hε] with n hn
    simpa using hn

/-- `AsympEq` transported along the deferral: a day-`m` asymptotic identity holds along the
deferred days `f n`, since `f n > n → ∞`.
Source: none: infrastructure (FAF `DeferralFunction.lt`)
Kind: L
Fidelity: n/a -/
theorem asympEq_comp_deferral {g : ℕ → ℝ} {c : ℝ} (h : g ≈ₙ (fun _ => c))
    (f : DeferralFunction) : (fun n => g (f n)) ≈ₙ (fun _ => c) := by
  unfold AsympEq at h ⊢
  have hf : Tendsto (fun n => f n) atTop atTop :=
    tendsto_atTop_mono (fun n => (f.lt n).le) tendsto_id
  exact h.comp hf

/-- `≈ₙ` gives, for every `ε > 0`, eventual closeness within `ε` (FAF's
`asympEq_iff_eventuallyWithin`, unpacked).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem asympEq_eventually_abs_le {f g : ℕ → ℝ} (h : f ≈ₙ g) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, |f n - g n| ≤ ε :=
  (asympEq_iff_eventuallyWithin.mp h) ε hε

/-- An expert whose history is an inductor pins every constant LUV at its value: the
deferred-day expectation of `constLUV s` tends to `s` (`thm:expprovind` on the single-LUV
combination for the expert's own market, then the deferred subsequence). This discharges the
constant's `ExpertPin` at grade (a) for inductor experts — the self-expert included — where
def-lattice F3 records that the *exact* identity fails.
Source: def-lattice F3 (nearest well-posed version (iii)); mandate T11
Kind: C
Fidelity: exact (asymptotic pin)
Hyps: (a) — `[IsLogicalInductor E.A DP]`, `hworld` -/
theorem expertPin_constLUV {DP : DeductiveProcess} (E : Expert DP) [IsLogicalInductor E.A DP]
    {s : ℚ} (hs : 0 ≤ s ∧ s ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ExpertPin E (fun _ => constLUV s) (s : ℝ) := by
  have h := expect_listComb_eq_of_slack (P := E.A) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp) (ts := [(1, fun _ => constLUV s)])
    (fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact constLUV_codes hs.1)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact constLUV_valued hs DP))
    (s : ℝ) (slack := fun _ => 0) tendsto_const_nhds
    (fun n v hv ν hν => by
      have := listComb_valuesAt_mem hν (p := (1, fun _ => constLUV s)) (List.mem_singleton_self _)
      rw [listComb_value]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [this.eq (constLUV_valuesAt hs v)]
      simp) hworld
  have h' : (fun m => (constLUV s).expect E.A m) ≈ₙ (fun _ => (s : ℝ)) := by
    refine (tendsto_congr (fun m => ?_)).mp h
    simp [listComb_expect]
  exact asympEq_comp_deferral h' E.f

/-! ## E. Tower on valued sources -/

/-- **Tower on valued sources**: `E^H_n(X_n) ≈ₙ E^H_n(Y_n)` for every e.d. *world-valued* source
`X` and every e.d. quote `Y` reflecting `E*(X)`. def-lattice's `Tower` ranges also over
unvalued e.c. sources (its audit round 2, fidelity item 2), which no arrow *into* the tower can
reach (their packages carry `source_valued`); every arrow *out of* the tower consumes only
valued sources (`WeightQuote.source_valued`, `Menu.Valued`), so nothing downstream weakens
when `Tower` is replaced by this predicate. `Tower → TowerValued` is immediate
(`towerValued_of_tower`); the converse is not claimed.
Source: [[deference-notions]] §Mart (over e.d. LUVs, which the corpus takes to be valued);
def-lattice audit r2 fidelity 2; mandate T3 (the converse remark)
Kind: D
Fidelity: variant: restricted to world-valued sources (weaker than `Tower` as a hypothesis,
the corpus's own quantifier) -/
def TowerValued (P : History) (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ X Y : ℕ → LUV, LUV.MachineThresholdCodeSeq X → LUV.MachineThresholdCodeSeq Y →
    Valued DP X → Reflects DP E X Y →
      (fun n => (X n).expect P n) ≈ₙ (fun n => (Y n).expect P n)

/-- `Tower` implies `TowerValued` (drop the valuedness).
Source: none: infrastructure
Kind: L
Fidelity: exact -/
theorem towerValued_of_tower {P : History} {DP : DeductiveProcess} {E : Expert DP}
    (hT : Tower P DP E) : TowerValued P DP E :=
  fun X Y hX hY _ hR => hT X Y hX hY hR

/-- **Two quotes reflecting the same estimates have asymptotically equal novice expectations**:
if `Y` and `Y'` are both valued at `E*(X_n)` in every consistent world, the combination
`Y − Y'` is valued `0` there, so `E^H_n(Y_n) ≈ₙ E^H_n(Y'_n)` (T0, slack `0`). This is what
moves a Tower instance from one quote of `X` to any other — for the self-expert, from FAF's
closed `cee` quote to every reflecting `Y` (`Witness.towerValued_self`).
Source: none: infrastructure (a T0 corollary; audit r1 adversarial N1's probe)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem expect_reflects_congr {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {E : Expert DP} {X Y Y' : ℕ → LUV} (hY : LUV.MachineThresholdCodeSeq Y)
    (hY' : LUV.MachineThresholdCodeSeq Y') (hR : Reflects DP E X Y) (hR' : Reflects DP E X Y')
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (Y n).expect P n) ≈ₙ (fun n => (Y' n).expect P n) := by
  have h := expect_listComb_eq_of_slack (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp) (ts := [(1, Y), (-1, Y')])
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hY
      · exact hY')
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact fun n v hv => ⟨_, hR n v hv⟩
      · exact fun n v hv => ⟨_, hR' n v hv⟩))
    (0 : ℝ) (slack := fun _ => 0) tendsto_const_nhds
    (fun n v hv ν hν => by
      have h1 := listComb_valuesAt_mem hν (p := (1, Y)) (by simp)
      have h2 := listComb_valuesAt_mem hν (p := (-1, Y')) (by simp)
      rw [listComb_value]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [h1.eq (hR n v hv), h2.eq (hR' n v hv)]
      simp) hworld
  have h' : (fun n => (Y n).expect P n - (Y' n).expect P n) ≈ₙ (fun _ => (0 : ℝ)) := by
    refine (tendsto_congr (fun n => ?_)).mp h
    simp [listComb_expect, sub_eq_add_neg]
  exact asympEq_sub_zero_iff.mp h'

end

end Cleanroom.Deference.DefLatticeArrows
