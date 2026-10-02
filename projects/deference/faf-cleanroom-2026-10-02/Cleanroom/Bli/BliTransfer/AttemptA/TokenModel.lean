import Cleanroom.Bli.BliTransfer.AttemptA.Splice
import LogicalInduction.Framework.Emission.FreezeTransducer

/-!
# `bli-transfer` (attempt A) · TokenModel: the splice on the contracted token stream

The token model of `EF.spliceOn`, mirroring FAF's `EF.freezeTokenRunOn`
(`Framework/Emission/FreezeTransducer.lean:262–640`): a bounded streaming transducer over the
*contracted* strategy stream (one code token per sentence) that copies every token and, right after
a price frame `[0, ⌜ψ⌝, k]` whose leaf the map fires on, appends the serialized body and the
`letE` close `8`. The parser control is FAF's own `EF.freezeTokenNext` (modes as in
`EF.streamStep`; only mode `2` uses the pending sentence code), so `EF.FreezeTokenState.Matches`
is reused verbatim.

The body is looked up at the **code** level, `exprCode expr day code`, which decodes the pending
code and serializes the map's body — the token model is never executed by a machine, so nothing
here needs an oracle; it is the specification the flat-stream pass (`Contraction.lean`,
`Certificate.lean`) is proved against.

The law is `strategyOfTokens_spliceTokenRunOn_trades`: on **every** token stream, well-formed or
garbage, decoding the transducer's output gives exactly the `EF.spliceOn`-rewritten trades of the
decoded source (FAF's `strategyOfTokens_freezeTokenRunOn_trades`, whose one-token commutation
`streamReadFrom_freezeTokenEmitOn` is re-run here with the body case
`EF.streamReadFrom_serialize_self` in place of the frozen constant). Rank validation commutes
because the splice preserves rank exactly under the map's rank discipline (`EF.spliceOn_rank`).

Sources: mandate T1.3 (the contracted-stream transducer law); FAF `FreezeTransducer.lean`.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptA

open LogicalInduction LO.Propositional

/-! ## The transducer -/

/-- The code-level body: decode the pending sentence code, look the map up at the day, serialize.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def exprCode (expr : ℕ → Sentence → Option EF) (day code : ℕ) : Option (List ℕ) :=
  (Encodable.decode (α := Sentence) code).bind fun φ => (expr day φ).map EF.serialize

/-- Tokens emitted while consuming one source token: at a price-day slot whose leaf the map
fires on, the day, the serialized body and the `letE` close; otherwise the token itself.
Source: mandate T1.3; FAF `EF.freezeTokenEmitOn`
Kind: D
Fidelity: n/a -/
def spliceTokenEmitOn (expr : ℕ → Sentence → Option EF) (state : EF.FreezeTokenState)
    (token : ℕ) : List ℕ :=
  if state.1 = 2 then
    match exprCode expr token state.2 with
    | some body => token :: (body ++ [8])
    | none => [token]
  else [token]

/-- Run the splice transducer, returning its final parser control and emitted stream.
Source: mandate T1.3; FAF `EF.freezeTokenRunOn`
Kind: D
Fidelity: n/a -/
def spliceTokenRunOn (expr : ℕ → Sentence → Option EF) :
    EF.FreezeTokenState → List ℕ → EF.FreezeTokenState × List ℕ
  | state, [] => (state, [])
  | state, token :: tokens =>
      let rest := spliceTokenRunOn expr (EF.freezeTokenNext state token) tokens
      (rest.1, spliceTokenEmitOn expr state token ++ rest.2)

/-- The transducer on the empty stream.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceTokenRunOn_nil (expr : ℕ → Sentence → Option EF)
    (state : EF.FreezeTokenState) : spliceTokenRunOn expr state [] = (state, []) := rfl

/-- The transducer over a concatenation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceTokenRunOn_append (expr : ℕ → Sentence → Option EF)
    (state : EF.FreezeTokenState) (xs ys : List ℕ) :
    spliceTokenRunOn expr state (xs ++ ys) =
      let first := spliceTokenRunOn expr state xs
      let second := spliceTokenRunOn expr first.1 ys
      (second.1, first.2 ++ second.2) := by
  induction xs generalizing state with
  | nil => rfl
  | cons token tokens ih =>
      simp only [List.cons_append, spliceTokenRunOn]
      rw [ih]
      simp [List.append_assoc]

/-- Apply the splice to every feature currently held by the streaming decoder.
Source: none: infrastructure; FAF `EF.freezeStreamStateOn`
Kind: D
Fidelity: n/a -/
def spliceStreamStateOn (expr : ℕ → Sentence → Option EF) : EF.StreamState → EF.StreamState
  | (control, stack, trades) =>
      (control, stack.map (EF.spliceOn expr),
        trades.map fun trade => (EF.spliceOn expr trade.1, trade.2))

/-! ## One token commutes with the decoder -/

section TokenDispatch

attribute [local simp] spliceTokenEmitOn EF.freezeTokenNext spliceStreamStateOn
  EF.streamReadFrom EF.streamStep

/-- **One source token and the suffix emitted for it commute with the streaming decoder**,
malformed inputs included (the copied offending token fails before an inserted suffix could
repair it). The body case: the decoder reads the day, pushes `price ψ k`, reads the serialized
body and pushes it (`EF.streamReadFrom_serialize_self`), then reads `8` and pushes
`letE (price ψ k) e`, which is `EF.spliceOn` at that leaf.
Source: mandate T1.3; FAF `EF.streamReadFrom_freezeTokenEmitOn`
Kind: L
Fidelity: exact -/
lemma streamReadFrom_spliceTokenEmitOn (expr : ℕ → Sentence → Option EF)
    (control : EF.FreezeTokenState) (state : EF.StreamState) (token : ℕ)
    (hmatch : control.Matches state) :
    EF.streamReadFrom (spliceTokenEmitOn expr control token)
        (some (spliceStreamStateOn expr state)) =
      (EF.streamStep (some state) token).map (spliceStreamStateOn expr) ∧
    ∀ next, EF.streamStep (some state) token = some next →
      (EF.freezeTokenNext control token).Matches next := by
  rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
  simp only [EF.FreezeTokenState.Matches] at hmatch ⊢
  rcases hmatch with ⟨hmode, hpending⟩
  rcases control with ⟨controlMode, code⟩
  simp only at hmode
  subst controlMode
  cases mode with
  | zero =>
      by_cases h0 : token = 0
      · subst token
        simp
      by_cases h1 : token = 1
      · subst token
        simp
      by_cases h2 : token = 2
      · subst token
        cases stack with
        | nil => simp
        | cons a stack =>
          cases stack with
          | nil => simp
          | cons b stack => simp
      by_cases h3 : token = 3
      · subst token
        cases stack with
        | nil => simp
        | cons a stack =>
          cases stack with
          | nil => simp
          | cons b stack => simp
      by_cases h4 : token = 4
      · subst token
        cases stack with
        | nil => simp
        | cons a stack =>
          cases stack with
          | nil => simp
          | cons b stack => simp
      by_cases h5 : token = 5
      · subst token
        cases stack <;> simp
      by_cases h6 : token = 6
      · subst token
        simp
      by_cases h7 : token = 7
      · subst token
        simp
      by_cases h8 : token = 8
      · subst token
        cases stack with
        | nil => simp
        | cons a stack =>
          cases stack with
          | nil => simp
          | cons b stack => simp
      · simp [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  | succ mode =>
      cases mode with
      | zero =>
          cases hdecode : Encodable.decode (α := Sentence) token <;>
            simp [hdecode]
      | succ mode =>
          cases mode with
          | zero =>
              obtain ⟨φ, hpendingEq, hdecode⟩ := hpending rfl
              subst pending
              have hcode : exprCode expr token code = (expr token φ).map EF.serialize := by
                simp [exprCode, hdecode]
              cases hexpr : expr token φ with
              | none =>
                  simp [hcode, hexpr]
              | some e =>
                  have hemit : spliceTokenEmitOn expr (0 + 1 + 1, code) token
                      = token :: (e.serialize ++ [8]) := by
                    simp [spliceTokenEmitOn, hcode, hexpr]
                  rw [hemit]
                  constructor
                  · have hstep : EF.streamReadFrom [token]
                        (some (spliceStreamStateOn expr ((0 + 1 + 1, some φ), (stack, trades))))
                        = some ((0, none), (EF.price φ token :: stack.map (EF.spliceOn expr),
                            trades.map fun trade => (EF.spliceOn expr trade.1, trade.2))) := by
                      simp
                    rw [show token :: (e.serialize ++ [8]) = [token] ++ e.serialize ++ [8] by simp,
                      EF.streamReadFrom_append, EF.streamReadFrom_append, hstep,
                      EF.streamReadFrom_serialize_self]
                    simp [EF.spliceOn_price_some expr hexpr]
                  · intro next hnext
                    simp at hnext
                    subst hnext
                    simp
          | succ mode =>
              cases mode with
              | zero =>
                  cases hdecode : Encodable.decode (α := ℚ) token <;>
                    simp [hdecode]
              | succ mode =>
                  cases mode with
                  | zero =>
                      cases stack with
                      | nil => simp
                      | cons e stack =>
                        cases hdecode : Encodable.decode (α := Sentence) token <;>
                          simp [hdecode]
                  | succ mode =>
                      cases mode with
                      | zero => simp
                      | succ mode => simp

end TokenDispatch

/-- The whole run commutes with the decoder, carrying the control match along.
Source: mandate T1.3; FAF `EF.streamReadFrom_freezeTokenRunOn`
Kind: L
Fidelity: exact -/
lemma streamReadFrom_spliceTokenRunOn (expr : ℕ → Sentence → Option EF)
    (control : EF.FreezeTokenState) (state : EF.StreamState) (tokens : List ℕ)
    (hmatch : control.Matches state) :
    let run := spliceTokenRunOn expr control tokens
    EF.streamReadFrom run.2 (some (spliceStreamStateOn expr state)) =
        (EF.streamReadFrom tokens (some state)).map (spliceStreamStateOn expr) ∧
      ∀ next, EF.streamReadFrom tokens (some state) = some next → run.1.Matches next := by
  induction tokens generalizing control state with
  | nil =>
      simp [spliceTokenRunOn, EF.streamReadFrom, hmatch]
  | cons token tokens ih =>
      simp only [spliceTokenRunOn]
      have hstep := streamReadFrom_spliceTokenEmitOn expr control state token hmatch
      rcases hstep with ⟨hstep, hnext⟩
      cases hs : EF.streamStep (some state) token with
      | none =>
          constructor
          · rw [EF.streamReadFrom_append, hstep]
            rw [hs]
            simp only [Option.map_none]
            rw [EF.streamReadFrom_none]
            change none = (EF.streamReadFrom tokens
              (EF.streamStep (some state) token)).map (spliceStreamStateOn expr)
            rw [hs, EF.streamReadFrom_none]
            rfl
          · intro final hfinalSource
            change EF.streamReadFrom tokens (EF.streamStep (some state) token) =
              some final at hfinalSource
            rw [hs, EF.streamReadFrom_none] at hfinalSource
            contradiction
      | some next =>
          have hmatches := hnext next hs
          have hrest := ih (EF.freezeTokenNext control token) next hmatches
          simp only at hrest
          rcases hrest with ⟨hrest, hfinal⟩
          constructor
          · rw [EF.streamReadFrom_append, hstep, hs]
            simp only [Option.map_some]
            rw [hrest]
            simp [EF.streamReadFrom, hs]
          · intro final hfinalSource
            apply hfinal final
            simpa [EF.streamReadFrom, hs] using hfinalSource

/-- Decoding the transducer's output is the splice of the decoded source.
Source: mandate T1.3; FAF `EF.deserializeTrades_freezeTokenRunOn`
Kind: L
Fidelity: exact -/
lemma deserializeTrades_spliceTokenRunOn (expr : ℕ → Sentence → Option EF) (tokens : List ℕ) :
    let run := spliceTokenRunOn expr (0, 0) tokens
    deserializeTrades run.2 =
      (deserializeTrades tokens).map fun trades =>
        trades.map fun trade => (EF.spliceOn expr trade.1, trade.2) := by
  have hrun := (streamReadFrom_spliceTokenRunOn expr (0, 0) EF.streamInitial tokens
    EF.freezeToken_initial_matches).1
  simp only at hrun ⊢
  have hinitial : spliceStreamStateOn expr EF.streamInitial = EF.streamInitial := rfl
  rw [hinitial] at hrun
  unfold deserializeTrades
  rw [hrun]
  cases hread : EF.streamReadFrom tokens (some EF.streamInitial) with
  | none => rfl
  | some state =>
      rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
      cases mode <;> cases pending <;> cases stack <;>
        simp [spliceStreamStateOn]

/-! ## The strategy-level law -/

/-- Rank-validate a decoded trade list (the branch `strategyOfTokens` takes on a successful
decode).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def validatedTrades (n : ℕ) (trades : List (EF × Sentence)) : List (EF × Sentence) :=
  if ∀ trade ∈ trades, trade.1.rank ≤ n then trades else []

/-- `strategyOfTokens` unfolded on its trades.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma strategyOfTokens_trades_eq (n : ℕ) (tokens : List ℕ) :
    (strategyOfTokens n tokens).trades =
      match deserializeTrades tokens with
      | none => []
      | some trades => validatedTrades n trades := by
  unfold strategyOfTokens validatedTrades
  split <;> rename_i hdecode
  · simp [hdecode]
  · split <;> simp_all

/-- **The contracted-stream transducer law**: decoding the transducer's output gives exactly the
`EF.spliceOn`-rewritten trades of the decoded source — on every token stream, well-formed or
garbage. Rank validation commutes because the splice preserves rank exactly under the map's rank
discipline. Not an efficiency certificate: exhibiting the transducer as an `FP` rewrite of the
machine's raw word is `Certificate.lean`.
Source: mandate T1.3 (`strategyOfTokens_spliceTokenRunOn_trades`); FAF `strategyOfTokens_freezeTokenRunOn_trades`
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma strategyOfTokens_spliceTokenRunOn_trades (expr : ℕ → Sentence → Option EF)
    (hrank : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k) (n : ℕ) (tokens : List ℕ) :
    let run := spliceTokenRunOn expr (0, 0) tokens
    (strategyOfTokens n run.2).trades =
      (strategyOfTokens n tokens).trades.map fun trade =>
        (EF.spliceOn expr trade.1, trade.2) := by
  have hdecode := deserializeTrades_spliceTokenRunOn expr tokens
  simp only at hdecode ⊢
  rw [strategyOfTokens_trades_eq, strategyOfTokens_trades_eq, hdecode]
  cases hs : deserializeTrades tokens with
  | none => simp
  | some trades =>
      simp only [Option.map_some]
      have hrankIff :
          (∀ trade ∈ trades.map (fun trade =>
              (EF.spliceOn expr trade.1, trade.2)), trade.1.rank ≤ n) ↔
            ∀ trade ∈ trades, trade.1.rank ≤ n := by
        constructor
        · intro h trade hmem
          have hmapped : (EF.spliceOn expr trade.1, trade.2) ∈
              trades.map (fun trade => (EF.spliceOn expr trade.1, trade.2)) :=
            List.mem_map_of_mem hmem
          have := h _ hmapped
          simpa [EF.spliceOn_rank expr hrank] using this
        · intro h trade hmem
          simp only [List.mem_map] at hmem
          obtain ⟨source, hsource, rfl⟩ := hmem
          simpa [EF.spliceOn_rank expr hrank] using h source hsource
      by_cases hvalid : ∀ trade ∈ trades, trade.1.rank ≤ n
      · have hsplicedValid := hrankIff.mpr hvalid
        unfold validatedTrades
        rw [if_pos hsplicedValid, if_pos hvalid]
      · have hsplicedInvalid : ¬∀ trade ∈ trades.map (fun trade =>
            (EF.spliceOn expr trade.1, trade.2)), trade.1.rank ≤ n :=
          fun h => hvalid (hrankIff.mp h)
        unfold validatedTrades
        rw [if_neg hsplicedInvalid, if_neg hvalid]
        rfl

end Cleanroom.Bli.BliTransfer.AttemptA
