import Cleanroom.Found.LiQuoteLane.Defs
import LogicalInduction.Framework.Machine.SentenceMachine
import LogicalInduction.Construction.Primcodable
import Complexitylib.Classes.P.FinsetDomain

/-!
# `li-coupled-pair` · B · Clocked: the fuel-paid quote ledger and its write-out certificate

Angle B of [[li-coupled-pair-mandate]]: the conditioning route. `li-quote-lane`'s conditioning
route (`Conditioning.lean`) conditions an inductor on the growing conjunction of ledger literals
`ledgerSeq a e`, and FAF's `lic_conditioned_growing_ofSequence` needs the certificate
`MachineSentenceCodes (ledgerSeq a e)` — a `Complexity.FP` machine of the *unary position* that
writes out the literal, polarity included. The polarity is `decide (r < a j n)`, so the machine
must *produce the published number* within polynomial time in the position; for a LIA table it
cannot (li-quote-lane findings F8), and the route carried the certificate as its one `(c)`.

**What this file does.** It replaces the schedule-indexed sequence by a **clocked** one. Position
`t` unpairs to `⟨payload, d⟩` with `payload = ⟨n, ⟨j, c⟩⟩` (`li-quote-lane`'s `ledgerPayload`), and
the literal for `(j, n, c)` is written at position `t` exactly when a fixed program `c₁` for the
polarity, run on the payload with fuel `clock t = (t + 1)² + 1` (FAF's `clockOf 1 2`), **halts
within that fuel** — otherwise the position carries `⊤`. The delay coordinate `d` is free, so every
literal is eventually written (`clockedSeq_eventually`); the stage at which it first appears is the
*cost* of the published number, metered in FAF's own fuel. This is anson-2-007's `σ ≥ R(F(n))`
("publication after the quote's own production cost") rendered inside FAF, with the cost model
FAF has — `Nat.Partrec.Code.evaln` fuel — rather than a runtime it lacks.

**Why the certificate is now a theorem** (`clockedSeq_codes`, no hypothesis). FAF's fuel calculus
(`PolyFueled`, `PolySegStream`, `BigTokenStream`, `UnaryRuler.of_polyFueled`) is stated with
`Fueled c f b := ∀ n, evaln (b n) c n = some (f n)` — the run must *succeed* — and Mathlib's
`evaln` has no catch: a timed-out sub-evaluation propagates `none`. So "read the value if it has
been computed by now, else ⊤" is **not expressible in the fuel calculus**; that is the precise
sense in which FAF's write-out classes cannot express "computed earlier, read now" at the fuel
level. But the *machine* classes are `∈ Complexity.FP`, and FAF's one exported polynomial-time
run of an arbitrary code pair under a polynomial clock — `TraderMachine.traderOutput_mem_FP`,
the function that compiles `clockedTokens` — tolerates timeouts (`Option.getD 0` after the
top-level `evaln`). Run it with the length program `Code.const 1` and the token program
`tokenCode c₁`: its output word is `digitsToBits [clockDigit t]` for a digit in `{0, …, 4}`, and
post-composing with a hard-wired finite table (`Complexity.ite_mem_finset_mem_FP`) turns the
digit into a `UnaryRuler` (`clockDigit_ruler`). The sentence calculus (`ifZero`, `neg`, `const`,
the atom family as a `MachineDigits`) then assembles the certificate. No `(c)` remains.

**What is *not* claimed.** The clock is a *schedule*: the literal for day `n` may appear at a
position `t ≥ n` well below any day the value "is about" — the sequence is a timed *record* of a
computable table, not a claim that the table is cheap. The explicit gate `(σ j).e n ≤ t` (a
`UnaryRuler` schedule, `hσ`) is what a two-way recursion would use to keep `A`'s day-`t` stage
away from `H`'s day-`≥ t` states; this file builds the record, `Conditioned.lean` the inductor.
Scope: one-way (the sequence records a fixed table).
-/

namespace Cleanroom.Li.LiCoupledPair.B

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Nat.Partrec (Code)

-- FAF's gotcha (`notes/lean-gotchas.md`): keep the unifier from evaluating `Nat.unpair` on
-- open terms.
attribute [local irreducible] Nat.sqrt

/-! ## A. The clock and the clocked digit -/

/-- **The route's clock**: fuel `(t + 1)² + 1` at position `t` — FAF's `TraderMachine.clockOf 1 2`,
the polynomial clock of a `PolyFueledTrader` with `a = 1`, `k = 2`. Any `clockOf a k` with
`a ≥ 1`, `k ≥ 2` would do; this one is fixed so the sequence is a `def` with no clock parameter.
Source: anson-2-007 (chat 04, the `σ ≥ R(F(n))` schedule; mandate T2.1); FAF `dd:fuel`
Kind: D
Fidelity: variant: the production cost is metered in `Nat.Partrec.Code.evaln` fuel, FAF's only cost model
Hyps: n/a -/
def clock (t : ℕ) : ℕ := TraderMachine.clockOf 1 2 t

/-- `clock_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clock_eq (t : ℕ) : clock t = (t + 1) ^ 2 + 1 := by
  simp [clock, TraderMachine.clockOf]

/-- The clock exceeds the position.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lt_clock (t : ℕ) : t < clock t := by
  rw [clock_eq]; nlinarith

/-- The clock exceeds the clocked interpreter's packed input `⟨t, 0⟩ = t² + t`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pair_zero_lt_clock (t : ℕ) : Nat.pair t 0 < clock t := by
  rw [clock_eq, Nat.pair]
  simp only [Nat.not_lt_zero, ite_false]
  nlinarith

/-- **The clocked digit** of a token program `tc` at position `t`: the output of `tc` on the
clocked interpreter's packed input `⟨t, 0⟩` under fuel `clock t`, `0` on timeout, clamped at FAF's
digit terminator `4` (the clamp `min · 4` is the trader machine's; it is the identity on the
values `0`, `1`, `2` the route uses).
Source: mandate angle B ("using the delay to pay for the value")
Kind: D
Fidelity: n/a -/
def clockDigit (tc : Code) (t : ℕ) : ℕ :=
  min ((Code.evaln (clock t) tc (Nat.pair t 0)).getD 0) 4

/-- `clockDigit_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clockDigit_le (tc : Code) (t : ℕ) : clockDigit tc t ≤ 4 := min_le_right _ _

/-- The length program `Code.const 1` answers `1` under any fuel exceeding its input.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma evaln_const_one (K t : ℕ) (h : t ≤ K) :
    Code.evaln (K + 1) (Code.const 1) t = some 1 := by
  simp [Code.const, Code.evaln, h]

/-- The clocked interpreter with length program `Code.const 1` emits exactly one token: the
clocked run of the token program on `⟨t, 0⟩`, `0` on timeout.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clockedTokens_const_one (tc : Code) (t : ℕ) :
    clockedTokens (Code.const 1) tc (clock t) t =
      [(Code.evaln (clock t) tc (Nat.pair t 0)).getD 0] := by
  obtain ⟨K, hK⟩ : ∃ K, clock t = K + 1 := ⟨clock t - 1, by have := lt_clock t; omega⟩
  have ht : t ≤ K := by have := lt_clock t; omega
  unfold clockedTokens
  rw [hK, evaln_const_one K t ht]
  dsimp only
  have hof := TraderMachine.ofFn_val_eq_map_range (min 1 (K + 1))
    (fun i => (Code.evaln (K + 1) tc (Nat.pair t i)).getD 0)
  beta_reduce at hof
  have hmin : min 1 (K + 1) = 1 := by omega
  rw [hof, hmin]
  simp

/-- **The trader machine's word at `(Code.const 1, tc, 1, 2)`** is the three-bit block of the
clocked digit: `traderOutput` is `digitsToBits` of the clamped clocked tokens.
Source: none: infrastructure (FAF `TraderMachine.traderOutput`)
Kind: L
Fidelity: n/a -/
lemma traderOutput_const_one (tc : Code) (x : List Bool) :
    TraderMachine.traderOutput (Code.const 1) tc 1 2 x = digitsToBits [clockDigit tc x.length] := by
  unfold TraderMachine.traderOutput
  rw [show TraderMachine.clockOf 1 2 x.length = clock x.length from rfl, clockedTokens_const_one]
  rfl

/-- The five words a clocked digit can be written as.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def digitWords : Finset (List Bool) := ((List.range 5).map fun d => digitsToBits [d]).toFinset

/-- `mem_digitWords`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_digitWords {d : ℕ} (hd : d ≤ 4) : digitsToBits [d] ∈ digitWords := by
  simp only [digitWords, List.mem_toFinset, List.mem_map, List.mem_range]
  exact ⟨d, by omega, rfl⟩

/-- **The clocked digit is machine-readable: any function of it is a `UnaryRuler`.** The
polynomial-time machine is FAF's `traderMachine` at `(Code.const 1, tc, 1, 2)`
(`TraderMachine.traderOutput_mem_FP`), whose word is `digitsToBits [clockDigit tc t]`, post-composed
with the finite lookup table `digitsToBits [d] ↦ replicate (g d) false` on the five possible words
(`Complexity.ite_mem_finset_mem_FP`). This is the one place the route catches a timeout: the
trader machine's `Option.getD 0` after its top-level `evaln`. Nothing in FAF's fuel calculus
(`PolyFueled`/`Fueled`, which require success) could supply it.
Source: mandate angle B; FAF `TraderMachine.traderOutput_mem_FP`, `Complexity.ite_mem_finset_mem_FP`
Kind: P
Fidelity: n/a (infrastructure of the certificate)
Hyps: (a) none -/
theorem clockDigit_ruler (tc : Code) (g : ℕ → ℕ) :
    UnaryRuler fun t => g (clockDigit tc t) := by
  have hF := TraderMachine.traderOutput_mem_FP (Code.const 1) tc 1 2
  have hG := Complexity.ite_mem_finset_mem_FP
    (fun s => List.replicate (g ((bitsToDigits s).headD 0)) false) digitWords
  have h := Complexity.mem_FP_comp hF hG
  show (fun z : List Bool => List.replicate (g (clockDigit tc z.length)) false) ∈ Complexity.FP
  convert h using 1
  funext z
  simp only [Function.comp_def, traderOutput_const_one]
  rw [if_pos (mem_digitWords (clockDigit_le tc z.length))]
  rw [bitsToDigits_digitsToBits [clockDigit tc z.length]
    (by
      intro d hd
      simp only [List.mem_singleton] at hd
      subst hd
      have := clockDigit_le tc z.length
      omega)]
  rfl

/-! ## B. Positions -/

/-- The payload of a position `t = ⟨payload, d⟩`: `li-quote-lane`'s `ledgerPayload j n c =
⟨n, ⟨j, c⟩⟩`, delay `d` discarded (the same packing as `ledgerSeq`'s `ledgerIndex`).
Source: none: infrastructure (li-quote-lane `ledgerIndex`)
Kind: D
Fidelity: n/a -/
def posPayload (t : ℕ) : ℕ := (Nat.unpair t).1

/-- The day of a position's payload.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def posDay (t : ℕ) : ℕ := (Nat.unpair (posPayload t)).1

/-- The item index of a position's payload.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def posItem (t : ℕ) : ℕ := (Nat.unpair (Nat.unpair (posPayload t)).2).1

/-- The threshold code of a position's payload.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def posCode (t : ℕ) : ℕ := (Nat.unpair (Nat.unpair (posPayload t)).2).2

/-- `posPayload_pair`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma posPayload_pair (p d : ℕ) : posPayload (Nat.pair p d) = p := by
  simp [posPayload]

/-- `posDay_pair`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma posDay_pair (j n c d : ℕ) : posDay (Nat.pair (ledgerPayload j n c) d) = n := by
  simp [posDay, ledgerPayload]

/-- `posItem_pair`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma posItem_pair (j n c d : ℕ) : posItem (Nat.pair (ledgerPayload j n c) d) = j := by
  simp [posItem, ledgerPayload]

/-- `posCode_pair`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma posCode_pair (j n c d : ℕ) : posCode (Nat.pair (ledgerPayload j n c) d) = c := by
  simp [posCode, ledgerPayload]

/-- Every position's payload is a ledger payload.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma posPayload_eq (t : ℕ) : posPayload t = ledgerPayload (posItem t) (posDay t) (posCode t) := by
  simp [posDay, posItem, posCode, ledgerPayload, Nat.pair_unpair]

/-- The day a position carries is at most the position.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma posDay_le (t : ℕ) : posDay t ≤ t :=
  le_trans (Nat.unpair_left_le _) (Nat.unpair_left_le _)

/-- `posPayload_ruler`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma posPayload_ruler : UnaryRuler posPayload := UnaryRuler.unpairFst

/-- `posDay_ruler`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma posDay_ruler : UnaryRuler posDay :=
  (UnaryRuler.unpairFst.comp UnaryRuler.unpairFst).of_eq fun _ => rfl

/-- `posItem_ruler`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma posItem_ruler : UnaryRuler posItem :=
  (UnaryRuler.unpairFst.comp (UnaryRuler.unpairSnd.comp UnaryRuler.unpairFst)).of_eq fun _ => rfl

/-! ## C. The polarity program and the token program -/

/-- **The gate value** of a payload `p = ⟨n, ⟨j, c⟩⟩` under a table `a`: `0` when `c` codes no
rational, else `2` when the ledger literal is affirmed (`ratOfCode c < a j n`, FAF's strict
`⌜X > r⌝` polarity, li-quote-lane disclosure (β)) and `1` when denied. The three values are what
the clocked digit reads back: `0` is also what a timeout reads as.
Source: mandate angle B; li-quote-lane `ledgerEntry`
Kind: D
Fidelity: n/a -/
def gateVal (a : ℕ → ℕ → ℚ) (p : ℕ) : ℕ :=
  bif (Encodable.decode (α := ℚ) (Nat.unpair (Nat.unpair p).2).2).isSome then
    (bif decide (ratOfCode (Nat.unpair (Nat.unpair p).2).2 <
        a (Nat.unpair (Nat.unpair p).2).1 (Nat.unpair p).1) then 2 else 1)
  else 0

/-- `gateVal_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gateVal_le (a : ℕ → ℕ → ℚ) (p : ℕ) : gateVal a p ≤ 2 := by
  unfold gateVal
  cases (Encodable.decode (α := ℚ) (Nat.unpair (Nat.unpair p).2).2).isSome <;>
    cases decide (ratOfCode (Nat.unpair (Nat.unpair p).2).2 <
      a (Nat.unpair (Nat.unpair p).2).1 (Nat.unpair p).1) <;> simp

/-- The gate value at a ledger payload.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gateVal_ledgerPayload (a : ℕ → ℕ → ℚ) (j n c : ℕ) :
    gateVal a (ledgerPayload j n c) =
      bif (Encodable.decode (α := ℚ) c).isSome then
        (bif decide (ratOfCode c < a j n) then 2 else 1) else 0 := by
  simp [gateVal, ledgerPayload]

/-- **The gate value is computable from a computable table** (`ratLE_prim`, `Primrec.decode`,
`Computable.cond`): this is the computation the clock meters.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gateVal_computable {a : ℕ → ℕ → ℚ} (ha : Computable fun q : ℕ × ℕ => a q.1 q.2) :
    Computable (gateVal a) := by
  have hn : Primrec fun p : ℕ => (Nat.unpair p).1 := Primrec.fst.comp Primrec.unpair
  have hjc : Primrec fun p : ℕ => (Nat.unpair p).2 := Primrec.snd.comp Primrec.unpair
  have hj : Primrec fun p : ℕ => (Nat.unpair (Nat.unpair p).2).1 :=
    Primrec.fst.comp (Primrec.unpair.comp hjc)
  have hc : Primrec fun p : ℕ => (Nat.unpair (Nat.unpair p).2).2 :=
    Primrec.snd.comp (Primrec.unpair.comp hjc)
  have hsome : Primrec fun p : ℕ =>
      (Encodable.decode (α := ℚ) (Nat.unpair (Nat.unpair p).2).2).isSome :=
    Primrec.option_isSome.comp ((Primrec.decode (α := ℚ)).comp hc)
  have hrat : Primrec fun p : ℕ => ratOfCode (Nat.unpair (Nat.unpair p).2).2 :=
    (Primrec.option_getD.comp Primrec.decode (Primrec.const 0)).comp hc
  have hle : Computable fun p : ℕ =>
      decide (a (Nat.unpair (Nat.unpair p).2).1 (Nat.unpair p).1 ≤
        ratOfCode (Nat.unpair (Nat.unpair p).2).2) :=
    ((Primrec₂.to_comp ratLE_prim.decide).comp (ha.comp (hj.to_comp.pair hn.to_comp))
      hrat.to_comp : _)
  have hlt : Computable fun p : ℕ =>
      decide (ratOfCode (Nat.unpair (Nat.unpair p).2).2 <
        a (Nat.unpair (Nat.unpair p).2).1 (Nat.unpair p).1) := by
    refine ((Primrec.dom_bool Bool.not).to_comp.comp hle).of_eq fun p => ?_
    rw [← decide_not]
    exact decide_eq_decide.mpr not_le
  exact (Computable.cond hsome.to_comp
    (Computable.cond hlt (Computable.const 2) (Computable.const 1)) (Computable.const 0)).of_eq
    fun p => rfl

/-- **A program for the gate value exists** for every computable table (Mathlib's
`Nat.Partrec.Code.exists_code`). The route takes the program `c₁` as a parameter and this is
how a caller obtains one; the sequence is defined for *any* `c₁`, the semantics
(`clockedSeq_cases`, `clockedSeq_eventually`) for one computing `gateVal a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gateCode_exists {a : ℕ → ℕ → ℚ} (ha : Computable fun q : ℕ × ℕ => a q.1 q.2) :
    ∃ c₁ : Code, ∀ p, c₁.eval p = Part.some (gateVal a p) := by
  have h : Nat.Partrec (fun p => (gateVal a p : Part ℕ)) :=
    Partrec.nat_iff.mp (gateVal_computable ha)
  obtain ⟨c, hc⟩ := Code.exists_code.mp h
  exact ⟨c, fun p => by rw [hc]; rfl⟩

/-- **The token program** of the route: the clocked interpreter hands the token program the
packed `⟨t, 0⟩`; two `left`s strip the token index and the delay coordinate, leaving the payload,
on which `c₁` runs. The two `left`s are *explicit* (not folded into `c₁`) so that the fuel `c₁`
needs depends on the payload only, not on the delay — which is what makes every literal
eventually written (`clockDigit_eventually`): an opaque program taking the whole position could
burn fuel in the delay coordinate.
Source: mandate angle B
Kind: D
Fidelity: n/a -/
def tokenCode (c₁ : Code) : Code := c₁.comp (Code.left.comp Code.left)

/-- The token program's unclocked value at `⟨t, 0⟩` is the gate value of `t`'s payload.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tokenCode_eval {a : ℕ → ℕ → ℚ} (c₁ : Code) (hc : ∀ p, c₁.eval p = Part.some (gateVal a p))
    (t : ℕ) : (tokenCode c₁).eval (Nat.pair t 0) = Part.some (gateVal a (posPayload t)) := by
  simp [tokenCode, Code.eval, hc, posPayload]

/-- **Soundness of the clocked digit**: it is `0` (timeout, or a gate value `0`) or the gate value
of the position's payload — never anything else (`evaln_sound`).
Source: none: infrastructure (Mathlib `evaln_sound`)
Kind: L
Fidelity: n/a -/
lemma clockDigit_tokenCode {a : ℕ → ℕ → ℚ} (c₁ : Code)
    (hc : ∀ p, c₁.eval p = Part.some (gateVal a p)) (t : ℕ) :
    clockDigit (tokenCode c₁) t = 0 ∨ clockDigit (tokenCode c₁) t = gateVal a (posPayload t) := by
  unfold clockDigit
  rcases h : Code.evaln (clock t) (tokenCode c₁) (Nat.pair t 0) with _ | v
  · left; simp
  · right
    have hv : v ∈ (tokenCode c₁).eval (Nat.pair t 0) := Code.evaln_sound (Option.mem_def.mpr h)
    rw [tokenCode_eval c₁ hc, Part.mem_some_iff] at hv
    subst hv
    simp only [Option.getD_some]
    exact min_eq_left (le_trans (gateVal_le a _) (by norm_num))

/-- The token program halts under fuel `K + 1` on `⟨t, 0⟩` as soon as `⟨t, 0⟩ ≤ K` and `c₁` halts
on the payload under that fuel (the two `left`s cost only their guards).
Source: none: infrastructure (Mathlib `evaln`, `comp`/`left` clauses)
Kind: L
Fidelity: n/a -/
lemma tokenCode_evaln_of_le {a : ℕ → ℕ → ℚ} (c₁ : Code) (t K : ℕ) (hK : Nat.pair t 0 ≤ K)
    (hsucc : gateVal a (posPayload t) ∈ Code.evaln (K + 1) c₁ (posPayload t)) :
    Code.evaln (K + 1) (tokenCode c₁) (Nat.pair t 0) = some (gateVal a (posPayload t)) := by
  have ht : t ≤ K := le_trans (Nat.left_le_pair t 0) hK
  have hcomp : ∀ (cf cg : Code) (n : ℕ), n ≤ K →
      Code.evaln (K + 1) (cf.comp cg) n = (Code.evaln (K + 1) cg n).bind (Code.evaln (K + 1) cf) :=
    fun cf cg n hn => by simp [Code.evaln, hn]
  have h3 : Code.evaln (K + 1) (Code.left.comp Code.left) (Nat.pair t 0) = some (posPayload t) := by
    simp [Code.evaln, hK, ht, posPayload]
  have hsucc' : Code.evaln (K + 1) c₁ (posPayload t) = some (gateVal a (posPayload t)) :=
    Option.mem_def.mp hsucc
  rw [tokenCode, hcomp _ _ _ hK, h3]
  simpa using hsucc'

/-- **Every payload's gate value is eventually read**: for every payload `p` and every bound
`N` there is a delay `d ≥ N` at which the clocked digit at position `⟨p, d⟩` is the gate value of
`p` (`evaln_complete` gives a fuel that works on the payload; the delay pushes the clock past it).
Source: mandate angle B (the delay pays for the value)
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem clockDigit_eventually {a : ℕ → ℕ → ℚ} (c₁ : Code)
    (hc : ∀ p, c₁.eval p = Part.some (gateVal a p)) (p N : ℕ) :
    ∃ d, N ≤ d ∧ clockDigit (tokenCode c₁) (Nat.pair p d) = gateVal a p := by
  have hmem : gateVal a p ∈ c₁.eval p := by rw [hc p]; exact Part.mem_some _
  obtain ⟨k₀, hk₀⟩ := Code.evaln_complete.mp hmem
  refine ⟨max N k₀, le_max_left _ _, ?_⟩
  set t := Nat.pair p (max N k₀) with ht
  obtain ⟨K, hK⟩ : ∃ K, clock t = K + 1 := ⟨clock t - 1, by have := lt_clock t; omega⟩
  have hpair : Nat.pair t 0 ≤ K := by have := pair_zero_lt_clock t; omega
  have hk₀K : k₀ ≤ K + 1 := by
    have h1 : k₀ ≤ t := le_trans (le_max_right _ _) (Nat.right_le_pair _ _)
    have := lt_clock t; omega
  have hsucc : gateVal a (posPayload t) ∈ Code.evaln (K + 1) c₁ (posPayload t) := by
    rw [ht, posPayload_pair]; exact Code.evaln_mono hk₀K hk₀
  unfold clockDigit
  rw [hK, tokenCode_evaln_of_le c₁ t K hpair hsucc, ht, posPayload_pair]
  simp only [Option.getD_some]
  exact min_eq_left (le_trans (gateVal_le a p) (by norm_num))

/-! ## D. The clocked quote sequence -/

/-- **The clocked quote sequence** (angle B's conditioning sequence). Position `t = ⟨payload, d⟩`
carries, when the item's publication schedule allows (`(σ j).e n ≤ t`, a `UnaryRuler` schedule),
the ledger literal of `li-quote-lane`'s family `3` for the payload `⟨n, ⟨j, c⟩⟩` — affirmed when the
clocked digit reads `2`, denied when it reads `1` — and `⊤` otherwise (the clocked run of the
polarity program `c₁` timed out, `c` codes no rational, or the schedule has not published). It is
defined for *any* program `c₁`; its semantics for one computing `gateVal a` is `clockedSeq_cases`
and `clockedSeq_eventually`. Scope: one-way (a timed record of a fixed table).
Source: mandate angle B ("adjoins the literal only at stages `≥ (σ j).e n`, using the delay to pay for the value"); anson-2-007 (`σ ≥ R(F(n))`); li-quote-lane `ledgerSeq` (the schedule-indexed original)
Kind: D
Fidelity: variant: the position at which a literal is first written is its clocked production cost (FAF's `evaln` fuel), not a stage chosen by the publisher; the explicit schedule gate `σ` is in addition
Hyps: n/a -/
def clockedSeq (c₁ : Code) (σ : ℕ → PublicationSchedule) (t : ℕ) : Sentence :=
  if (σ (posItem t)).e (posDay t) ≤ t then
    if clockDigit (tokenCode c₁) t = 2 then freshAtom ledgerFamily (posPayload t)
    else if clockDigit (tokenCode c₁) t = 1 then ∼freshAtom ledgerFamily (posPayload t)
    else ⊤
  else ⊤

/-- The family-3 atom at a position's payload is machine-metered: its atom code
`⟨cleanroomBaseTag + 3, payload⟩ + 5` is a `UnaryRuler`, hence a `MachineDigits` one-token stream,
and `rpn (atom a) = [a + 5]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshAtom_payload_codes :
    MachineSentenceCodes fun t => freshAtom ledgerFamily (posPayload t) := by
  apply MachineSentenceCodes.ofCanonical
  have hr : UnaryRuler fun t => freshAtomCode ledgerFamily (posPayload t) + 5 :=
    ((UnaryRuler.const (cleanroomBaseTag + ledgerFamily)).pair posPayload_ruler).add
      (UnaryRuler.const 5)
  exact MachineTokenStream.of_eq (MachineDigits.ofUnaryRuler hr) fun _ => rfl

/-- **The certificate, discharged**: the clocked quote sequence is an efficiently computable
sequence of sentences (`MachineSentenceCodes`) for *every* polarity program `c₁` and every
`UnaryRuler` publication schedule — with **no** hypothesis on the table it records. The schedule
gate and the two clocked-digit tests are rulers (`clockDigit_ruler`), the atom family is
`freshAtom_payload_codes`, and FAF's sentence calculus (`ifZero`, `neg`, `const`) assembles the
three-way dispatch. This is the hypothesis `hψ` of li-quote-lane's `conditioningRoute_inductor`
(its one `(c)`), now a theorem at the clocked sequence.
Source: mandate angle B (the (c) to discharge); li-quote-lane findings F8; anson-2-007 (the `e ≥ Λ` argument)
Kind: P
Fidelity: variant: the source's cost-domination schedule `e(i) ≥ T_A(i)` is realized as the clock (FAF's fuel) rather than as a runtime bound FAF lacks
Hyps: (a) none (`hσ` is the schedule's own poly-time certificate, discharged for `n + 2` and `n + 1` in `Conditioned.lean`) -/
theorem clockedSeq_codes (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (hσ : UnaryRuler fun p => (σ p.unpair.1).e p.unpair.2) :
    MachineSentenceCodes (clockedSeq c₁ σ) := by
  have hsched : UnaryRuler fun t => (σ (posItem t)).e (posDay t) :=
    (hσ.comp (posItem_ruler.pair posDay_ruler)).of_eq fun t => by simp
  have hg₁ : UnaryRuler fun t => (σ (posItem t)).e (posDay t) - t := hsched.sub UnaryRuler.id
  have hg₂ : UnaryRuler fun t => if clockDigit (tokenCode c₁) t = 2 then 0 else 1 :=
    clockDigit_ruler (tokenCode c₁) fun d => if d = 2 then 0 else 1
  have hg₃ : UnaryRuler fun t => if clockDigit (tokenCode c₁) t = 1 then 0 else 1 :=
    clockDigit_ruler (tokenCode c₁) fun d => if d = 1 then 0 else 1
  have hpos := freshAtom_payload_codes
  have hneg := hpos.neg
  have htop := MachineSentenceCodes.const (⊤ : Sentence)
  refine ((hpos.ifZero (hneg.ifZero htop hg₃) hg₂).ifZero htop hg₁).of_eq fun t => ?_
  unfold clockedSeq
  simp only [Nat.sub_eq_zero_iff_le]
  by_cases hs : (σ (posItem t)).e (posDay t) ≤ t
  · rw [if_pos hs, if_pos hs]
    by_cases h2 : clockDigit (tokenCode c₁) t = 2
    · simp [h2]
    · by_cases h1 : clockDigit (tokenCode c₁) t = 1
      · simp [h1]
      · simp [h1, h2]
  · rw [if_neg hs, if_neg hs]

/-- **What the sequence writes**: every position is `⊤` or, for a published, well-coded payload
`⟨n, ⟨j, c⟩⟩`, the ledger literal `literalOf (ledgerEntry a j n c)` — the same literal li-quote-lane's
`ledgerSeq a σ` carries at that payload, now at a clock-determined position.
Source: none: infrastructure (the semantics of `clockedSeq`)
Kind: L
Fidelity: n/a -/
theorem clockedSeq_cases {a : ℕ → ℕ → ℚ} (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (hc : ∀ p, c₁.eval p = Part.some (gateVal a p)) (t : ℕ) :
    clockedSeq c₁ σ t = ⊤ ∨
      ∃ n j c, (Encodable.decode (α := ℚ) c).isSome = true ∧ (σ j).e n ≤ t ∧
        posPayload t = ledgerPayload j n c ∧
        clockedSeq c₁ σ t = literalOf (ledgerEntry a j n c) := by
  unfold clockedSeq
  by_cases hs : (σ (posItem t)).e (posDay t) ≤ t
  · rw [if_pos hs]
    rcases clockDigit_tokenCode c₁ hc t with h0 | hg
    · left; rw [h0]; simp
    · rw [hg, posPayload_eq t, gateVal_ledgerPayload]
      by_cases hd : (Encodable.decode (α := ℚ) (posCode t)).isSome = true
      · right
        refine ⟨posDay t, posItem t, posCode t, hd, hs, rfl, ?_⟩
        rw [hd, cond_true]
        by_cases hlt : ratOfCode (posCode t) < a (posItem t) (posDay t)
        · simp [hlt, ledgerEntry, literalOf]
        · simp [hlt, ledgerEntry, literalOf]
      · left
        simp only [Bool.not_eq_true] at hd
        simp [hd]
  · left; rw [if_neg hs]

/-- **Every ledger literal is eventually written**: for every item `j`, day `n` and rational code
`c` there is a position carrying `literalOf (ledgerEntry a j n c)` — the delay coordinate pushes
the clock past the fuel `c₁` needs on the payload (`clockDigit_eventually`) and past the
publication stage. The position is *not* under the publisher's control beyond the gate: it is
the clocked cost. Scope: one-way.
Source: mandate angle B; anson-2-007 (every quote is eventually published, after its cost)
Kind: P
Fidelity: exact (eventual publication); the stage is the clocked cost, not a chosen `e(n)`
Hyps: (a) none -/
theorem clockedSeq_eventually {a : ℕ → ℕ → ℚ} (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (hc : ∀ p, c₁.eval p = Part.some (gateVal a p)) (j n c : ℕ)
    (hd : (Encodable.decode (α := ℚ) c).isSome = true) :
    ∃ t, posPayload t = ledgerPayload j n c ∧
      clockedSeq c₁ σ t = literalOf (ledgerEntry a j n c) := by
  obtain ⟨d, hNd, hdig⟩ := clockDigit_eventually c₁ hc (ledgerPayload j n c) ((σ j).e n)
  refine ⟨Nat.pair (ledgerPayload j n c) d, posPayload_pair _ _, ?_⟩
  have hs : (σ j).e n ≤ Nat.pair (ledgerPayload j n c) d :=
    le_trans hNd (Nat.right_le_pair _ _)
  unfold clockedSeq
  rw [posItem_pair, posDay_pair, posPayload_pair, if_pos hs, hdig, gateVal_ledgerPayload, hd,
    cond_true]
  by_cases hlt : ratOfCode c < a j n
  · simp [hlt, ledgerEntry, literalOf]
  · simp [hlt, ledgerEntry, literalOf]

/-- **Both polarities are written** (N+ grounds, as li-quote-lane's `ledgerSchedule_both_polarities`):
for a `[0,1]`-valued table the threshold `-1` is affirmed and the threshold `2` denied at some
position, for every item and day.
Source: mandate T1.3 / T4.1 (N+ criteria: both polarities occur)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem clockedSeq_both_polarities {a : ℕ → ℕ → ℚ} (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (hc : ∀ p, c₁.eval p = Part.some (gateVal a p)) (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1)
    (j n : ℕ) :
    (∃ t, clockedSeq c₁ σ t = freshAtom ledgerFamily (ledgerPayload j n (Encodable.encode (-1 : ℚ)))) ∧
      ∃ t, clockedSeq c₁ σ t = ∼freshAtom ledgerFamily (ledgerPayload j n (Encodable.encode (2 : ℚ))) := by
  constructor
  · obtain ⟨t, -, ht⟩ := clockedSeq_eventually c₁ σ hc j n (Encodable.encode (-1 : ℚ)) (by simp)
    refine ⟨t, ht.trans ?_⟩
    have : (-1 : ℚ) < a j n := by linarith [(hmem j n).1]
    simp [ledgerEntry, this]
  · obtain ⟨t, -, ht⟩ := clockedSeq_eventually c₁ σ hc j n (Encodable.encode (2 : ℚ)) (by simp)
    refine ⟨t, ht.trans ?_⟩
    have : ¬ ((2 : ℚ) < a j n) := by linarith [(hmem j n).2]
    simp [ledgerEntry, this]

end Cleanroom.Li.LiCoupledPair.B
