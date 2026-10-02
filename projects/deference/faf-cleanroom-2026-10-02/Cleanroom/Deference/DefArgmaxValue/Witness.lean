import Cleanroom.Deference.DefArgmaxValue.Selector
import Cleanroom.Deference.DefArgmaxValue.CondStable
import Cleanroom.Deference.DefSqueezeDiamond.GapMesh

/-!
# `def-argmax-value` · Witness: the self-expert's selection package on every valued menu (4d)

For the self-expert `Expert.self (liaHistory (paperDP T)) (paperDP T) f` and **any** e.c. menu
`M : Menu k`, the selection bit `1[sel_n = j]` is a computable `{0,1}`-rational: the least-index
argmax of the `k+1` deferred-day mesh expectations `expectQuoteAt (O i) n (f n)`
(`def-squeeze-diamond`'s `deferredExpectSeq`, FAF's `expectQuoteAt_computable`), compared with
`j` — `followBit_computable`'s proof generalized through `argmaxList_primrec`. It is quoted by
FAF's `RationalQuoteCode.ofComputable` (`argmaxBitCode`), so the selection-indicator LUV
`selI j n := (argmaxBitCode j).luv n` is e.c. and valued **exactly** `1[M.argmax E n = j]` in
every `paperDP T`-world (`selI_reflected`, through `argmax_eq_of_argmaxList`), and the product
`selQ j n := meshProductLUV (argmaxBitCode j) (O j) n` is e.c. and valued within `1/(n+1)` of
`x_j · 1[sel_n = j]` (`meshProductLUV_valuesAt`). This is `SelectionPackage` for the self-expert
on the whole e.c. class — the `(a)` discharge of `SelectionPackagesAvailable`, and the N+ of
target 4a's predicate. Selection bits enter only as quoted decided numbers, never as trade
weights (design decision 3).

Construction-facing; single market (self).
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSqueezeDiamond
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
variable (f : DeferralFunction) {k : ℕ} (M : Menu k)

/-- The self-expert's rational quotes on day `n`: the deferred-day mesh expectations of the
options, as computable rationals (`deferredExpectSeq`).
Source: none: infrastructure (FAF `expectQuoteAt`)
Kind: D
Fidelity: exact -/
def selfQuotes (n : ℕ) : Fin (k + 1) → ℚ := fun i => deferredExpectSeq T f (M.O i) n

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The rational quotes cast to the self-expert's real quotes.
Source: none: infrastructure (`deferredExpectSeq_cast`)
Kind: L
Fidelity: n/a -/
theorem selfQuotes_cast (n : ℕ) (i : Fin (k + 1)) :
    ((selfQuotes T f M n i : ℚ) : ℝ) =
      M.quote (Expert.self (liaHistory (paperDP T)) (paperDP T) f) i n :=
  deferredExpectSeq_cast T f (M.O i) n

/-- **The selection bit** `1[sel_n = j]` as a computable `{0,1}`-rational: `argmaxList` of the
rational quotes compared with `j`.
Source: mandate target 4d ("the computable `{0,1}`-sequence `if argmaxBit M n = j then 1 else 0`")
Kind: D
Fidelity: exact -/
def argmaxBit (j : Fin (k + 1)) (n : ℕ) : ℚ :=
  if argmaxList (List.ofFn (selfQuotes T f M n)) = (j : ℕ) then 1 else 0

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The selection bit is computable (`Computable.list_ofFn` over the `k+1` computable deferred
expectations, `argmaxList_primrec`, a decided equality).
Source: none: infrastructure (`followBit_computable` generalized)
Kind: L
Fidelity: n/a -/
theorem argmaxBit_computable (j : Fin (k + 1)) : Computable (argmaxBit T f M j) := by
  have hl : Computable fun n => List.ofFn (selfQuotes T f M n) :=
    Computable.list_ofFn (fun i => deferredExpectSeq_computable T f (M.codes i))
  have ha : Computable fun n => argmaxList (List.ofFn (selfQuotes T f M n)) :=
    argmaxList_primrec.to_comp.comp hl
  have hd : Computable fun n => decide (argmaxList (List.ofFn (selfQuotes T f M n)) = (j : ℕ)) :=
    ((((Primrec.eq.comp Primrec.id (Primrec.const (j : ℕ))).decide).to_comp.comp ha).of_eq
      (fun n => by rfl))
  exact (Computable.cond hd (Computable.const (1 : ℚ)) (Computable.const (0 : ℚ))).of_eq
    (fun n => by simp [argmaxBit, Bool.cond_decide])

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The selection bit lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem argmaxBit_mem (j : Fin (k + 1)) (n : ℕ) :
    0 ≤ argmaxBit T f M j n ∧ argmaxBit T f M j n ≤ 1 := by
  unfold argmaxBit
  split_ifs <;> norm_num

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- **The selection bit is the selection**: as a real it is `1[M.argmax E n = j]` for the
self-expert (`argmax_eq_of_argmaxList`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem argmaxBit_cast (j : Fin (k + 1)) (n : ℕ) :
    ((argmaxBit T f M j n : ℚ) : ℝ) =
      if M.argmax (Expert.self (liaHistory (paperDP T)) (paperDP T) f) n = j then 1 else 0 := by
  unfold argmaxBit
  have h := argmax_eq_of_argmaxList (Expert.self (liaHistory (paperDP T)) (paperDP T) f) M n
    (selfQuotes T f M n) (selfQuotes_cast T f M n) j
  by_cases hc : argmaxList (List.ofFn (selfQuotes T f M n)) = (j : ℕ)
  · rw [if_pos hc, if_pos (h.2 hc)]
    simp
  · rw [if_neg hc, if_neg (fun h' => hc (h.1 h'))]
    simp

/-- FAF's quote code of the selection bit.
Source: mandate target 4d; design decision 3 (selection bits as quoted decided numbers)
Kind: D
Fidelity: exact -/
def argmaxBitCode (j : Fin (k + 1)) : RationalQuoteCode T (argmaxBit T f M j) :=
  RationalQuoteCode.ofComputable T (argmaxBit_computable T f M j) (argmaxBit_mem T f M j)

/-- **The selection-indicator LUV** `I j n := ⌜1[sel_n = j]⌝`.
Source: mandate target 4d
Kind: D
Fidelity: exact -/
def selI (j : Fin (k + 1)) (n : ℕ) : LUV := (argmaxBitCode T f M j).luv n

/-- **The product LUV** `Q j n := ⌜O^j_n · 1[sel_n = j]⌝`, FAF's mesh product of the option with
the quoted bit (`meshProductLUV`: a quoted rational times a LUV, within `1/(n+1)`).
Source: mandate target 4d ("use `meshProductLUV` … with `slack n := 1/(n+1)`")
Kind: D
Fidelity: variant: within FAF's `1/(n+1)` mesh slack -/
def selQ (j : Fin (k + 1)) (n : ℕ) : LUV := meshProductLUV (argmaxBitCode T f M j) (M.O j) n

omit [Entailment.Consistent T] in
/-- The selection indicators are e.c.
Source: none: infrastructure (FAF `RationalQuoteCode.poly`)
Kind: L
Fidelity: n/a -/
theorem selI_codes (j : Fin (k + 1)) : LUV.MachineThresholdCodeSeq (selI T f M j) :=
  (argmaxBitCode T f M j).poly

omit [Entailment.Consistent T] in
/-- The products are e.c.
Source: none: infrastructure (FAF `meshProductLUV_machineThresholdCodeSeq`)
Kind: L
Fidelity: n/a -/
theorem selQ_codes (j : Fin (k + 1)) : LUV.MachineThresholdCodeSeq (selQ T f M j) :=
  meshProductLUV_machineThresholdCodeSeq _ (M.codes j)

omit [Entailment.Consistent T] in
/-- **The selection indicator is reflected exactly** at `1[M.argmax E n = j]`.
Source: none: infrastructure (FAF `RationalQuoteCode.reflected`)
Kind: L
Fidelity: n/a -/
theorem selI_reflected (j : Fin (k + 1)) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (selI T f M j n)
      (if M.argmax (Expert.self (liaHistory (paperDP T)) (paperDP T) f) n = j then 1 else 0) := by
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T) (argmaxBitCode T f M j) n v hv
  rwa [argmaxBit_cast] at h

omit [Entailment.Consistent T] in
/-- **The product is reflected within the mesh slack** at `x · 1[M.argmax E n = j]`.
Source: none: infrastructure (FAF `meshProductLUV_valuesAt`)
Kind: L
Fidelity: n/a -/
theorem selQ_reflected (j : Fin (k + 1)) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) (x : ℝ) (hx : v.ValuesAt (M.O j n) x) :
    ∃ z, v.ValuesAt (selQ T f M j n) z ∧
      |z - x * (if M.argmax (Expert.self (liaHistory (paperDP T)) (paperDP T) f) n = j
        then 1 else 0)| ≤ 1 / ((n : ℝ) + 1) := by
  obtain ⟨z, hz, hb⟩ := meshProductLUV_valuesAt (paperQuotationPresentation T)
    (argmaxBitCode T f M j) (M.O j) n v hv hx
  refine ⟨z, hz, ?_⟩
  rwa [argmaxBit_cast] at hb

omit [Entailment.Consistent T] in
/-- **The self-expert's selection package on every e.c. menu** (target 4d, (a)): the
indicators `selI`, the products `selQ`, slack `1/(n+1)`. The N+ of `SelectionPackage`: it
exists on the whole e.c. class, with the bits decided by the market's own day-`f n` prices.
Source: mandate target 4d; [[total-trust-implies-value]] §Setting ("ledger-decided tie-break")
Kind: C
Fidelity: exact (indicators exact; products within FAF's mesh slack)
Hyps: (a) none -/
def selectionPackage_self :
    SelectionPackage (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) M
      (selI T f M) (selQ T f M) where
  codes_I := selI_codes T f M
  codes_Q := selQ_codes T f M
  slack := fun n => 1 / ((n : ℝ) + 1)
  slack_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat
  reflected_I := selI_reflected T f M
  reflected_Q := selQ_reflected T f M

omit [Entailment.Consistent T] in
/-- `SelectionPackagesAvailable` for the self-expert, discharged.
Source: mandate target 4a ("for the self-expert it is a theorem")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem selectionPackagesAvailable_self :
    SelectionPackagesAvailable (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  fun _ M _ => ⟨_, _, ⟨selectionPackage_self T f M⟩⟩

end

end Cleanroom.Deference.DefArgmaxValue
