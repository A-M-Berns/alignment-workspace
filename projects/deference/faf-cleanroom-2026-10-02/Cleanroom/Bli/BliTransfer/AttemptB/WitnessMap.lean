import Cleanroom.Bli.BliTransfer.AttemptB.OracleBridge

/-!
# `bli-transfer` · attempt B · WitnessMap: T1's non-vacuity, over an abstract inductor

The hypothesis package of T1 is `IsLogicalInductor Q DP` plus an expression map that
*actually changes prices*, plus (for the class form) a presented trader the rewrite actually
touches. This file inhabits everything but the inductor, for **every** logical inductor `Q`
(the LIA instance is `WitnessLia.lean`, the one file importing the construction):

* `witnessAtom` — the reserved family `7` (overlay-witness atoms) of `bli-found`'s allocator,
  payload `⟨0, 4^{sizeBound 1}⟩` (day first, as every family must); it is large on days `0`
  and `1` (`witnessAtom_not_smallOn_one`, by the digit-count arithmetic of
  `largeOn_witness`) and small from day `2` on.
* `witnessEntries q₀ q₁` — the two-cell table `{(0, witnessAtom) ↦ q₀, (1, witnessAtom) ↦ q₁}`;
  `witnessExpr q₀ q₁` its constant-body map; `witnessOracle q₀ q₁ : SpliceOracle _` its
  machine-checked oracle (`SpliceOracle.ofTable`: FAF's `FP` recognizer, every spelling);
  `witnessOv` the matching re-pricing (`quote` off the two cells).
* `witnessExprMap` — the `ExprMap` for any `Q` with a rational quote table (every
  `IsLogicalInductor` has one, `ComputableMarket`).
* **Non-degeneracy, proved not assumed**: the cell value `witnessValue Q` is chosen to differ
  from `Q 0 witnessAtom` (`1/4` if that price is `1/2`, else `1/2`), so
  `overlay Q ov ≠ Q` (`overlay_witness_ne`). On the trader side, `witnessReader` (a
  `SpliceBuiltTrader` reading `price witnessAtom 0` daily) is rewritten non-trivially.
* `transfer_witness` — the package: for every logical inductor `Q` there are `ov`, `E`, `C`
  with `overlay Q ov ≠ Q`, and a presented trader the rewrite changes and which does not
  exploit the overlay.

**Grade.** N+ on the map side in the sense the mandate asks (the overlay differs from `Q` at a
large sentence; not a small-only change, trap (iii)) and on the trader side (a non-identity
rewrite of an e.c. trader) — but the map is **finite** (two cells), so the overlay is also a
finite-support perturbation of `Q` (FAF's `lic_iff_of_finiteSupportPerturbation` already
covers it). A witness map with infinitely many fired cells needs an oracle recognizing an
infinite atom family from every spelling — the tag test plus a doubly-exponential length
comparison the mandate sketches — which is not built here (see the report, T1.5).

Sources: mandate T1.5; `Cleanroom/Bli/BliFound/Tags.lean` (family registry, row `7`);
`Cleanroom/Bli/BliFound/Witnesses.lean` (`largeOn_witness`).
-/

namespace Cleanroom.Bli.BliTransfer.AttemptB

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound
open LogicalInduction.FreezeOracle

/-! ## The witness atom -/

/-- The reserved allocator family `7`: overlay-witness atoms (owner: `bli-transfer`).
Source: mandate T1.5; `Cleanroom/Bli/BliFound/Tags.lean` registry
Kind: D
Fidelity: n/a -/
abbrev overlayWitnessFamily : ℕ := 7

/-- **The witness atom**: family `7`, payload `⟨0, 4^{sizeBound 1}⟩` (day `0` first).
Source: mandate T1.5
Kind: D
Fidelity: n/a -/
def witnessAtom : Sentence := freshAtom overlayWitnessFamily (Nat.pair 0 (4 ^ sizeBound 1))

/-- The witness atom's index is at least `4^{sizeBound 1}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma le_witnessAtom_code :
    4 ^ sizeBound 1 ≤ freshAtomCode overlayWitnessFamily (Nat.pair 0 (4 ^ sizeBound 1)) :=
  le_trans (Nat.right_le_pair _ _) (Nat.right_le_pair _ _)

/-- **The witness atom is large on day `1`** (hence on day `0`): its index has more than
`sizeBound 1` base-4 digits.
Source: mandate T1.5 (largeness of the witness family)
Kind: P
Fidelity: exact -/
theorem witnessAtom_not_smallOn_one : ¬ SmallOn 1 witnessAtom := by
  unfold SmallOn witnessAtom freshAtom
  rw [tokenSize_atom]
  intro h
  have h1 := le_witnessAtom_code
  have h2 := lt_pow_length_natDigits4
    (freshAtomCode overlayWitnessFamily (Nat.pair 0 (4 ^ sizeBound 1)) + 5)
  have h3 : 4 ^ sizeBound 1 < 4 ^ (natDigits4
      (freshAtomCode overlayWitnessFamily (Nat.pair 0 (4 ^ sizeBound 1)) + 5)).length := by
    omega
  have h4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 4)).mp h3
  omega

/-- The witness atom is large on day `0` as well.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem witnessAtom_not_smallOn_zero : ¬ SmallOn 0 witnessAtom :=
  fun h => witnessAtom_not_smallOn_one (SmallOn.mono (by norm_num) h)

/-! ## The table, its map and its oracle -/

/-- The two-cell table: `(0, witnessAtom) ↦ q₀`, `(1, witnessAtom) ↦ q₁`.
Source: mandate T1.5
Kind: D
Fidelity: n/a -/
def witnessEntries (q₀ q₁ : ℚ) : List TableEntry :=
  [⟨0, witnessAtom, q₀⟩, ⟨1, witnessAtom, q₁⟩]

/-- The witness expression map: `const q₀` at `(0, witnessAtom)`, `const q₁` at
`(1, witnessAtom)`, `none` elsewhere.
Source: mandate T1.5
Kind: D
Fidelity: n/a -/
def witnessExpr (q₀ q₁ : ℚ) : ℕ → Sentence → Option LogicalInduction.EF :=
  constMap (tableSel (witnessEntries q₀ q₁)) (tableQuote (witnessEntries q₀ q₁))

/-- **The witness oracle** — the first `SpliceOracle`, machine-checked: FAF's finite-table
recognizer on the two cells, correct on every spelling of `witnessAtom`.
Source: mandate T1.5 ("your first `SpliceCertificate`")
Kind: N+
Fidelity: n/a -/
def witnessOracle (q₀ q₁ : ℚ) : SpliceOracle (witnessExpr q₀ q₁) :=
  SpliceOracle.ofTable (witnessEntries q₀ q₁)

/-- The witness map, cell by cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma witnessExpr_eq (q₀ q₁ : ℚ) (k : ℕ) (ψ : Sentence) :
    witnessExpr q₀ q₁ k ψ =
      if k = 0 ∧ ψ = witnessAtom then some (.const q₀)
      else if k = 1 ∧ ψ = witnessAtom then some (.const q₁) else none := by
  rw [witnessExpr, constMap_table_eq]
  simp only [witnessEntries, tableLookupOn]
  by_cases h0 : k = 0 ∧ ψ = witnessAtom
  · simp [h0.1, h0.2]
  · by_cases h1 : k = 1 ∧ ψ = witnessAtom
    · simp [h1.1, h1.2]
    · have h0' : ¬ (0 = k ∧ witnessAtom = ψ) := fun h => h0 ⟨h.1.symm, h.2.symm⟩
      have h1' : ¬ (1 = k ∧ witnessAtom = ψ) := fun h => h1 ⟨h.1.symm, h.2.symm⟩
      simp [h0', h1', h0, h1]

/-- The witness re-pricing: `q₀`/`q₁` on the two cells, the base's rational quote elsewhere.
Source: mandate T1.5
Kind: D
Fidelity: n/a -/
def witnessOv (quote : ℕ → Sentence → ℚ) (q₀ q₁ : ℚ) : ℕ → Sentence → ℚ :=
  fun k ψ => if k = 0 ∧ ψ = witnessAtom then q₀
    else if k = 1 ∧ ψ = witnessAtom then q₁ else quote k ψ

/-- **The witness expression map** for any market `Q` with a rational quote table in `[0, 1]`.
Source: mandate T1.5
Kind: N+
Fidelity: n/a
Hyps: (a) -/
def witnessExprMap (Q : History) (quote : ℕ → Sentence → ℚ) (hq : ∀ k ψ, Q k ψ = quote k ψ)
    (hrange : ∀ k ψ, 0 ≤ Q k ψ ∧ Q k ψ ≤ 1) (q₀ q₁ : ℚ) (h0 : 0 ≤ q₀ ∧ q₀ ≤ 1)
    (h1 : 0 ≤ q₁ ∧ q₁ ≤ 1) : ExprMap Q (witnessOv quote q₀ q₁) where
  expr := witnessExpr q₀ q₁
  closed := fun k ψ e he => by
    rw [witnessExpr_eq] at he
    split_ifs at he <;> simp only [Option.some.injEq] at he <;> subst he <;> rfl
  leaves := fun k ψ e he => by
    rw [witnessExpr_eq] at he
    split_ifs at he <;> simp only [Option.some.injEq] at he <;> subst he <;>
      simp [LogicalInduction.EF.priceQueries]
  fires := fun k ψ e he => by
    rw [witnessExpr_eq] at he
    split_ifs at he with hc0 hc1 <;> simp only [Option.some.injEq] at he <;> subst he
    · obtain ⟨rfl, rfl⟩ := hc0
      rw [overlay_large witnessAtom_not_smallOn_zero]
      simp [LogicalInduction.EF.denote, witnessOv]
    · obtain ⟨rfl, rfl⟩ := hc1
      rw [overlay_large witnessAtom_not_smallOn_one]
      simp [LogicalInduction.EF.denote, witnessOv]
  silent := fun k ψ hn => by
    rw [witnessExpr_eq] at hn
    split_ifs at hn with hc0 hc1
    left
    simp [witnessOv, hc0, hc1, hq]
  ov_range := fun k ψ => by
    simp only [witnessOv]
    split_ifs
    · exact h0
    · exact h1
    · have := hrange k ψ
      rw [hq] at this
      exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

/-- The overlay's price at the day-`0` cell is `q₀`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma overlay_witnessOv_zero (Q : History) (quote : ℕ → Sentence → ℚ) (q₀ q₁ : ℚ) :
    overlay Q (witnessOv quote q₀ q₁) 0 witnessAtom = (q₀ : ℝ) := by
  rw [overlay_large witnessAtom_not_smallOn_zero]
  simp [witnessOv]

/-! ## Non-degeneracy -/

open scoped Classical in
/-- A cell value that differs from `Q`'s day-`0` price of the witness atom: `1/4` if that price
is `1/2`, else `1/2`.
Source: mandate T1.5 (non-degeneracy)
Kind: D
Fidelity: n/a -/
noncomputable def witnessValue (Q : History) : ℚ :=
  if Q 0 witnessAtom = (1 / 2 : ℝ) then 1 / 4 else 1 / 2

/-- The chosen value differs from `Q`'s price.
Source: mandate T1.5 (non-degeneracy)
Kind: L
Fidelity: n/a -/
lemma witnessValue_ne (Q : History) : ((witnessValue Q : ℚ) : ℝ) ≠ Q 0 witnessAtom := by
  unfold witnessValue
  split_ifs with h
  · rw [h]; norm_num
  · intro h'; apply h; rw [← h']; norm_num

/-- The chosen value lies in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma witnessValue_mem_Icc (Q : History) : 0 ≤ witnessValue Q ∧ witnessValue Q ≤ 1 := by
  unfold witnessValue
  split_ifs <;> norm_num

/-- **The overlay differs from `Q`** — at the large sentence `witnessAtom` on day `0`
(proved, not assumed; trap (iii)).
Source: mandate T1.5 (non-degeneracy)
Kind: N+
Fidelity: n/a -/
theorem overlay_witness_ne (Q : History) (quote : ℕ → Sentence → ℚ) (q₁ : ℚ) :
    overlay Q (witnessOv quote (witnessValue Q) q₁) ≠ Q := by
  intro h
  have := congrFun (congrFun h 0) witnessAtom
  rw [overlay_witnessOv_zero] at this
  exact witnessValue_ne Q this

/-- **The trader side**: a presented trader reading `price witnessAtom 0` on every day, with
coefficient exactly that leaf and traded sentence `⊥`.
Source: mandate T1.5 ("the trader side is exercised")
Kind: D
Fidelity: n/a -/
def witnessReader : Trader where
  strat _ := { trades := [(.price witnessAtom 0, ⊥)], rank_le := by simp }

/-- `witnessReader` is a `SpliceBuiltTrader` (constant families throughout).
Source: mandate T1.5
Kind: N+
Fidelity: n/a -/
theorem witnessReader_spliceBuilt : SpliceBuiltTrader witnessReader :=
  ⟨fun _ => 1, fun _ => .price witnessAtom 0, fun _ => ⊥, UnaryRuler.const 1,
    (SpliceBuilt.price (MachineSentenceCodes.const witnessAtom) (UnaryRuler.const 0)
      (MachineDigits.const 0)).of_eq (fun _ => rfl),
    MachineSentenceCodes.const ⊥, fun _ => by simp [witnessReader]⟩

/-- The witness map rewrites `witnessReader` non-trivially.
Source: mandate T1.5
Kind: N+
Fidelity: n/a -/
theorem witnessExprMap_spliceTrader_ne (Q : History) (quote : ℕ → Sentence → ℚ)
    (hq : ∀ k ψ, Q k ψ = quote k ψ) (hrange : ∀ k ψ, 0 ≤ Q k ψ ∧ Q k ψ ≤ 1) (q₀ q₁ : ℚ)
    (h0 : 0 ≤ q₀ ∧ q₀ ≤ 1) (h1 : 0 ≤ q₁ ∧ q₁ ≤ 1) :
    (witnessExprMap Q quote hq hrange q₀ q₁ h0 h1).spliceTrader witnessReader ≠ witnessReader := by
  intro heq
  have h0' := congrArg (fun Tr : Trader => (Tr.strat 0).trades) heq
  have hfire : (witnessExprMap Q quote hq hrange q₀ q₁ h0 h1).expr 0 witnessAtom
      = some (.const q₀) := by
    show witnessExpr q₀ q₁ 0 witnessAtom = _
    rw [witnessExpr_eq]; simp
  simp [witnessReader, ExprMap.spliceTrader, Trader.spliceOn_strat, Strategy.spliceOn_trades,
    EF.spliceLeaf_some hfire] at h0'

/-! ## The package -/

/-- **T1's non-vacuity over any logical inductor** (the LIA instance is `WitnessLia.lean`):
for every `Q` with `IsLogicalInductor Q DP` there are a re-pricing `ov`, an expression map `E`
and a machine-checked splice oracle `C` such that the overlay differs from `Q` (at a
day-large sentence), and a presented trader that the rewrite changes and that does not exploit
the overlay. The rational quote table comes from `Q`'s own `ComputableMarket` certificate.
Source: mandate T1.5
Kind: N+
Fidelity: n/a (finite-support map; see the file header)
Hyps: (a) -/
theorem transfer_witness (Q : History) (DP : DeductiveProcess) [hQ : IsLogicalInductor Q DP] :
    ∃ (ov : ℕ → Sentence → ℚ) (E : ExprMap Q ov) (_ : SpliceOracle E.expr),
      overlay Q ov ≠ Q ∧
      ∃ Tr : Trader, SpliceBuiltTrader Tr ∧ E.spliceTrader Tr ≠ Tr ∧
        ¬ Tr.Exploits (overlay Q ov) DP := by
  obtain ⟨hrange, quote, _, hquote, _⟩ := hQ.marketComputable
  let q : ℕ → Sentence → ℚ := fun k ψ => quote k (Encodable.encode ψ)
  have hq : ∀ k ψ, Q k ψ = q k ψ := fun k ψ => hquote k ψ
  let E := witnessExprMap Q q hq hrange (witnessValue Q) (1 / 2) (witnessValue_mem_Icc Q)
    (by norm_num)
  refine ⟨witnessOv q (witnessValue Q) (1 / 2), E, witnessOracle _ _,
    overlay_witness_ne Q q (1 / 2), witnessReader, witnessReader_spliceBuilt,
    witnessExprMap_spliceTrader_ne Q q hq hrange _ _ _ _, ?_⟩
  exact overlay_noExploit_spliceBuilt Q DP _ E (witnessOracle _ _) witnessReader
    witnessReader_spliceBuilt

end Cleanroom.Bli.BliTransfer.AttemptB
