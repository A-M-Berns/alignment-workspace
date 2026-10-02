import Cleanroom.Bli.BliTransfer.Transfer
import Cleanroom.Bli.BliTransfer.Certificate
import Cleanroom.Bli.BliTrajectory
import Cleanroom.Bli.BliSuperbelief.Expr

/-!
# `bli-assemble` · Defs: the re-pricing, the identity with the overlay, the chain expression

Package `bli-assemble` (area `bli`, namespace `Cleanroom.Bli.BliAssemble`): the assembly of the
BLI program's 70 % milestone, L2 — `bli-trajectory`'s constructed market `bliHistory` **is** an
overlay in `bli-transfer`'s sense, its re-pricing is expressible by `bli-superbelief`'s tent
terms, and the criterion transfers from the base.

This file holds the definitions of record (mandate target 0, minus the coding, which is
`Coding.lean`) and target 1:

* `bliOv` — the re-pricing: `bliPrice`'s large branch verbatim (Tier A by `tierAPrice` from the
  unrounded actual table; Tier B by the base), so that `bliPrice = if SmallOn then Q else bliOv`
  is `rfl` (`bliPrice_eq_ite`).
* `bliHistory_eq_overlay` — **target 1**: `bliHistory Q 𝓜 sk c = overlay (ratHistory Q) (bliOv Q 𝓜 sk c)`.
* `minEntry` — the earliest entry of a chain (the chain's first future day), with `minEntry_mem`
  and `minEntry_le`.
* `chainExpr` — the expression for a Tier-A parse: the tent term for the chain's earliest entry
  (`tentExpr 𝓜 n h (decode m₁ q₁)` with `m₁ = n + h + 1`) times the constant
  `chainProbH … l m₁ (decode m₁ q₁) (latest − m₁) · smallFactor` (the rest of the chain restarted
  from the known table, times the small part's table value). `const 0` for an inconsistent chain
  or a chain with no future entry (the latter never comes out of `tierA`).
* `tentExprMap` — the expression map: `none` on small sentences (so the guard question of
  `bli-transfer` Known issue 6 never arises) and on Tier B; `chainExpr` on Tier A.
* `dyadicMesh` — the mesh `d m = 2 ^ m`, the computable mesh the open computability statements
  are stated at (the mandate's "constant or `2^m` mesh").

Sources: [[bli-program]] §2.5, §3.1, §3.4; mandate targets 0, 1, 2, 3.
-/

namespace Cleanroom.Bli.BliAssemble

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliTransfer Cleanroom.Bli.BliSuperbelief

open Classical

noncomputable section

/-! ## The re-pricing -/

/-- **The re-pricing of record**: exactly `bliPrice`'s large branch — a Tier-A sentence by
`tierAPrice` from the **unrounded** actual table, a Tier-B sentence by the base. Defined so that
`bliPrice Q 𝓜 sk c n ψ = if SmallOn n ψ then Q n ψ else bliOv Q 𝓜 sk c n ψ` holds by `rfl`;
in particular Tier B returns `Q n ψ` exactly (program §7 row L2 "en"), and past state atoms,
which `tierA` parses as Tier B, are the base's (Known issue 9).
Source: [[bli-program]] §2.5, §3.1; mandate target 0 (`bliOv`)
Kind: D
Fidelity: exact -/
def bliOv (Q : RatHistory) (𝓜 : Mesh) (sk : Skeleton smallIndex 𝓜.d) (c : StateCoding 𝓜)
    (n : ℕ) (ψ : Sentence) : ℚ :=
  match tierA c n ψ with
  | some s => tierAPrice sk c n (actualTable smallIndex Q n) s
  | none => Q n ψ

/-- `bliPrice` is the small-first split of the base and the re-pricing, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma bliPrice_eq_ite (Q : RatHistory) (𝓜 : Mesh) (sk : Skeleton smallIndex 𝓜.d)
    (c : StateCoding 𝓜) (n : ℕ) (ψ : Sentence) :
    bliPrice Q 𝓜 sk c n ψ = if SmallOn n ψ then Q n ψ else bliOv Q 𝓜 sk c n ψ := rfl

/-- The re-pricing on a Tier-A sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma bliOv_of_tierA {Q : RatHistory} {𝓜 : Mesh} {sk : Skeleton smallIndex 𝓜.d}
    {c : StateCoding 𝓜} {n : ℕ} {ψ : Sentence} {s : List (ℕ × ℕ) × Option Sentence}
    (h : tierA c n ψ = some s) :
    bliOv Q 𝓜 sk c n ψ = tierAPrice sk c n (actualTable smallIndex Q n) s := by
  unfold bliOv; rw [h]

/-- The re-pricing on a Tier-B sentence is the base's price.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma bliOv_of_tierB {Q : RatHistory} {𝓜 : Mesh} {sk : Skeleton smallIndex 𝓜.d}
    {c : StateCoding 𝓜} {n : ℕ} {ψ : Sentence} (h : tierA c n ψ = none) :
    bliOv Q 𝓜 sk c n ψ = Q n ψ := by
  unfold bliOv; rw [h]

/-- The re-pricing lies in `[0, 1]` when the base does.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma bliOv_mem_Icc {Q : RatHistory} (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) (𝓜 : Mesh)
    (sk : Skeleton smallIndex 𝓜.d) (c : StateCoding 𝓜) (n : ℕ) (ψ : Sentence) :
    0 ≤ bliOv Q 𝓜 sk c n ψ ∧ bliOv Q 𝓜 sk c n ψ ≤ 1 := by
  cases h : tierA c n ψ with
  | none => rw [bliOv_of_tierB h]; exact hQ n ψ
  | some s => rw [bliOv_of_tierA h]; exact tierAPrice_mem_Icc c sk _ s

/-! ## Target 1: the identity -/

/-- **`bliHistory` is an overlay** (target 1): `bli-trajectory`'s constructed market is
`bli-transfer`'s `overlay` of the base's real history by the re-pricing `bliOv`. Pointwise:
both test `SmallOn n ψ` first; on a small sentence both are the base; on a large one
`bliPrice`'s large branch *is* `bliOv` by definition, and the cast `((q : ℚ) : ℝ)` is the same
on both sides. The right-hand side is built from `tierA`/`tierAPrice` unchanged (mandate trap:
no other `bliOv`).
Source: [[bli-program]] §3.1 ("its instantiation for B1 is the identity `bliHistory = overlay Q (bliOverlay)`"); mandate target 1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bliHistory_eq_overlay (Q : RatHistory) (𝓜 : Mesh) (sk : Skeleton smallIndex 𝓜.d)
    (c : StateCoding 𝓜) :
    bliHistory Q 𝓜 sk c = overlay (ratHistory Q) (bliOv Q 𝓜 sk c) := by
  funext n ψ
  by_cases h : SmallOn n ψ
  · rw [overlay_small h]
    unfold bliHistory ratHistory
    rw [bliPrice_of_small h]
  · rw [overlay_large h]
    unfold bliHistory
    rw [bliPrice_eq_ite, if_neg h]

/-! ## The earliest entry of a chain -/

/-- The entry of a chain with the earliest day (leftmost among ties; `(0, 0)` for the empty
list) — the chain's first future day, where the tent term starts.
Source: mandate target 0 (`chainExpr`: "first future entry")
Kind: D
Fidelity: n/a -/
def minEntry : List (ℕ × ℕ) → ℕ × ℕ
  | [] => (0, 0)
  | [x] => x
  | x :: y :: ys => if x.1 ≤ (minEntry (y :: ys)).1 then x else minEntry (y :: ys)

/-- `minEntry` of a singleton.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma minEntry_singleton (x : ℕ × ℕ) : minEntry [x] = x := rfl

/-- `minEntry` of a nonempty chain is an entry of it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma minEntry_mem : ∀ {l : List (ℕ × ℕ)}, l ≠ [] → minEntry l ∈ l
  | [], h => absurd rfl h
  | [x], _ => by simp
  | x :: y :: ys, _ => by
      simp only [minEntry]
      split_ifs
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (minEntry_mem (List.cons_ne_nil y ys))

/-- Every entry's day is at least `minEntry`'s.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma minEntry_le : ∀ {l : List (ℕ × ℕ)}, ∀ x ∈ l, (minEntry l).1 ≤ x.1
  | [], x, hx => by simp at hx
  | [y], x, hx => by
      rw [List.mem_singleton] at hx
      subst hx
      exact le_rfl
  | y :: z :: zs, x, hx => by
      simp only [minEntry]
      rcases List.mem_cons.mp hx with rfl | hx
      · split_ifs with h
        · exact le_rfl
        · omega
      · have := minEntry_le x hx
        split_ifs with h
        · exact h.trans this
        · exact this

/-! ## The chain expression and the expression map -/

/-- **The expression for a Tier-A parse `(l, s)` at day `n`** (target 0, `chainExpr`). For a
consistent chain whose earliest entry `(m₁, q₁)` is in the future (`n < m₁`, always the case
for a chain `tierA` returns): the tent term `tentExpr 𝓜 n h (decode m₁ q₁)` with `h = m₁ − n − 1`
(so `m₁ = n + h + 1`), whose denotation is the day-`m₁` marginal of the tent chain started at
the day-`n` actual table (`tentExpr_denoteRat`), times the constant
`chainProbH … l m₁ (decode m₁ q₁) (latest − m₁) · smallFactor c l s` — the rest of the chain
**restarted from the known table** `decode m₁ q₁` (a rational that depends only on the codes),
times the small part's table value on the latest day. `const 0` otherwise. The `Nat`
subtractions `m₁ − n − 1` and `latest − m₁` are guarded: the first by `n < m₁` in the condition,
the second by `minEntry_le`/`le_latestEntry` (`m₁ ≤ latest`).
Source: [[bli-program]] §3.4 (the `expr` map); mandate target 0 (`chainExpr`)
Kind: D
Fidelity: exact -/
def chainExpr (𝓜 : Mesh) (c : StateCoding 𝓜) (n : ℕ)
    (p : List (ℕ × ℕ) × Option Sentence) : EF :=
  if Consistent p.1 ∧ n < (minEntry p.1).1 then
    EF.mul
      (tentExpr 𝓜 n ((minEntry p.1).1 - n - 1)
        (c.decode (n + ((minEntry p.1).1 - n - 1) + 1) (minEntry p.1).2))
      (EF.const (chainProbH (tentSkeleton smallIndex 𝓜) c p.1 (minEntry p.1).1
          (c.decode (minEntry p.1).1 (minEntry p.1).2)
          ((latestEntry p.1).1 - (minEntry p.1).1) *
        smallFactor c p.1 p.2))
  else EF.const 0

/-- Unfolding `chainExpr` on a consistent future chain.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainExpr_of_consistent (𝓜 : Mesh) (c : StateCoding 𝓜) (n : ℕ)
    {l : List (ℕ × ℕ)} (s : Option Sentence) (hc : Consistent l) (hn : n < (minEntry l).1) :
    chainExpr 𝓜 c n (l, s) =
      EF.mul
        (tentExpr 𝓜 n ((minEntry l).1 - n - 1)
          (c.decode (n + ((minEntry l).1 - n - 1) + 1) (minEntry l).2))
        (EF.const (chainProbH (tentSkeleton smallIndex 𝓜) c l (minEntry l).1
            (c.decode (minEntry l).1 (minEntry l).2) ((latestEntry l).1 - (minEntry l).1) *
          smallFactor c l s)) := by
  unfold chainExpr; rw [if_pos ⟨hc, hn⟩]

/-- Unfolding `chainExpr` on an inconsistent chain.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainExpr_of_not_consistent (𝓜 : Mesh) (c : StateCoding 𝓜) (n : ℕ)
    {l : List (ℕ × ℕ)} (s : Option Sentence) (hc : ¬ Consistent l) :
    chainExpr 𝓜 c n (l, s) = EF.const 0 := by
  unfold chainExpr; rw [if_neg (fun h => hc h.1)]

/-- **The expression map of record** (target 0, `tentExprMap`): `none` on a small sentence
(the map never fires there, so `bli-transfer`'s dropped guard — Known issue 6 — is moot), `none`
on Tier B (where `bliOv` is the base, `ExprMap.silent`), and `chainExpr` of the Tier-A parse
otherwise. Independent of the base `Q` and of the skeleton: the bodies read the day-`n` small
prices and compute the tent chain's marginal for **every** rational history
(`tentExpr_denoteRat`).
Source: [[bli-program]] §3.1 (i)–(ii), §3.4; mandate target 0 (`tentExprMap`)
Kind: D
Fidelity: exact -/
def tentExprMap (𝓜 : Mesh) (c : StateCoding 𝓜) (n : ℕ) (ψ : Sentence) : Option EF :=
  if SmallOn n ψ then none else (tierA c n ψ).map (chainExpr 𝓜 c n)

/-- When the map fires: the sentence is large and Tier A, and the body is `chainExpr` of its parse.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tentExprMap_eq_some {𝓜 : Mesh} {c : StateCoding 𝓜} {n : ℕ} {ψ : Sentence} {e : EF}
    (h : tentExprMap 𝓜 c n ψ = some e) :
    ¬ SmallOn n ψ ∧ ∃ s, tierA c n ψ = some s ∧ e = chainExpr 𝓜 c n s := by
  unfold tentExprMap at h
  by_cases hs : SmallOn n ψ
  · rw [if_pos hs] at h; exact absurd h (by simp)
  · rw [if_neg hs] at h
    refine ⟨hs, ?_⟩
    cases ht : tierA c n ψ with
    | none => rw [ht] at h; simp at h
    | some s => rw [ht] at h; exact ⟨s, rfl, (Option.some.inj h).symm⟩

/-- When the map is silent: the sentence is small, or Tier B.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tentExprMap_eq_none {𝓜 : Mesh} {c : StateCoding 𝓜} {n : ℕ} {ψ : Sentence}
    (h : tentExprMap 𝓜 c n ψ = none) : SmallOn n ψ ∨ tierA c n ψ = none := by
  unfold tentExprMap at h
  by_cases hs : SmallOn n ψ
  · exact Or.inl hs
  · rw [if_neg hs] at h
    right
    cases ht : tierA c n ψ with
    | none => rfl
    | some s => rw [ht] at h; simp at h

/-- The map fires on every large Tier-A sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tentExprMap_of_tierA {𝓜 : Mesh} {c : StateCoding 𝓜} {n : ℕ} {ψ : Sentence}
    (hs : ¬ SmallOn n ψ) {s : List (ℕ × ℕ) × Option Sentence} (h : tierA c n ψ = some s) :
    tentExprMap 𝓜 c n ψ = some (chainExpr 𝓜 c n s) := by
  unfold tentExprMap; rw [if_neg hs, h]; rfl

/-! ## The dyadic mesh -/

/-- **The dyadic mesh** `d m = 2 ^ m`: positive, nested, and (unlike `bli-trajectory`'s
`denominatorMesh`) computable — the mesh the open computability statements are stated at.
Source: mandate target 5 ("take a constant or `d m = 2^m` mesh, and say so")
Kind: D
Fidelity: n/a -/
def dyadicMesh : Mesh where
  d m := 2 ^ m
  d_pos m := by positivity
  d_dvd m := pow_dvd_pow 2 (Nat.le_succ m)

end

end Cleanroom.Bli.BliAssemble
