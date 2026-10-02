import Cleanroom.Bli.BliAssemble.Inherit
import Cleanroom.Bli.BliAssemble.Process
import Cleanroom.Bli.BliAssemble.Fixpoint
import Cleanroom.Bli.BliSuperbelief.Paper
import Cleanroom.Bli.BliOverlay.FirmSupport
import LogicalInduction.Framework.Machine.SpliceMachine
import LogicalInduction.Construction.Paper.TheoremDP

/-!
# `bli-assemble` · Lia: non-vacuity at FAF's logical inductor over `paperDP 𝗜𝚺₁` (target 8)

The base of record is `liaBase := liaQuote (paperDP 𝗜𝚺₁)`, for which
`ratHistory liaBase = liaHistory (paperDP 𝗜𝚺₁)` **definitionally** — so the instance
`[IsLogicalInductor (ratHistory liaBase) (paperDP 𝗜𝚺₁)]` is FAF's `paperLIA 𝗜𝚺₁` itself and the
`Q` inside `bliHistory` is the same term (mandate trap: the wrong market).

* `bli_hypotheses_paperDP` — the hypothesis package of L2's row of record is inhabited at the
  real inductor, with a day-varying large family (every conjunct proved): `paperLIA 𝗜𝚺₁`;
  `paperDP_hworld 𝗜𝚺₁` (every stage has a consistent world — a conjunct, not a side remark); the
  map fires on **every** day at the day-`(n+1)` zero state's atom; `𝐏` charges a face point's
  atom on every day (positive tent mass); the splice of the e.c. `stateReader` (reading the
  day-`1` zero state's atom at day `0`) is not the identity on any day; on every day, either `𝐏`
  and the LIA disagree on some day-`(n+1)` candidate atom or the LIA already distributes mass one
  over the candidates (the dichotomy, `E5` plus a case split); **from `bli-overlay`'s `N₀` on,
  `𝐏` and the LIA differ outright on some sentence every day** (`bliHistory_ne_lia_from`, repair
  round 1 — the mandate's conjunct, unconditional). Also `bliDP_paperDP_hworld` for the
  state-learning process (target 9's non-vacuity).
* `bliHistory_ne_lia_of_offSupport` — `𝐏 ≠ liaHistory` on day `n` outright, **given** that some
  face point's day-`(n+1)` atom is off the LIA's finite day-`n` support (then the LIA quotes it
  `0`, `liaQuote_eq_zero_of_not_mem_support`, while the tent charges it). A composition under a
  named hypothesis (`C`), discharged by:
* `bliHistory_ne_lia_from` — the hypothesis holds from `N₀` on: `bli-overlay`'s gated
  `firm_support_subset_smallSet` (every sentence the trading firm trades on day `n ≥ N₀` is small
  on day `n`), `bli-superbelief`'s `liaStates_support_subset_firm` (the LIA's day-`n` support is
  inside the firm's), and `bli-found`'s `stateAtom_large` (a day-`(n+1)` candidate atom is not
  small on day `n`). Days `< N₀` keep the dichotomy. Round-1 fidelity audit B1 (the composition is
  the auditor's probe, landed).
* `bli_package_paperDP` — the package **with** the criterion at `dyadicMesh`/`writeOutCoding`,
  resting on the open rows (`tentOracle_exists`, `bliOv_computableTable`); listed. The grade of
  record is therefore `bli_hypotheses_paperDP`'s: **N+ for the hypothesis package of
  `bliHistory_isLogicalInductor_of`, everything except the certificate and the table.**
* `exists_stateLearns_fixpoint_paperDP` — target 9(c): the self-consistent instance over
  `bliDP (paperDP 𝗜𝚺₁) c.states actual` with `StateLearns` for its own `liaQuote` — the fixpoint in
  `actual`, from `Fixpoint.lean` (proved for every process through the day-locality of
  `liaStates` in the deductive process). This is the self-consistent state-learning process of
  [[bli-program]] §2.5's B2 encoding (the market exists and rounds to its own states); it is
  **not** `bli-linkage`'s K5 (a linked superbelief whose pinned marginals are the base's quotes,
  iff the bracket balance holds), which it does not touch. The process `bliDP … actualFix` is not
  shown computable (`actualFix` goes through the noncomputable `liaQuote`, `roundTo` and
  `writeOutCoding`), so no `IsLogicalInductor` instance over it is claimed.

A note on the e.c. reader's family: the mandate asked for a reader with a *day-varying* payload.
An e.c. trader cannot read a day-`n` state atom on day `n` (`not_machineSentenceCodes_nextStateAtoms`);
a day-varying e.c. reader of `price ⌜𝑸_{m(n)} = …⌝ (m(n) − 1)` with `m(n)` growing like
`log log log n` is not ruled out, but its `MachineSentenceCodes` certificate needs an enumeration
of the candidate codes in `FP`, the same obstacle as target 6 — **not delivered**. The reader of
record names one fixed state atom at day `0`, which the map rewrites on every day; "day-varying"
is the *market-side* family of face points, on which `𝐏` and the base differ.

Memory: this is the only file importing `Construction.*`; it also imports `bli-overlay`'s
`FirmSupport` (for `bliHistory_ne_lia_from`), which elaborates in about 20 s warm.

Sources: mandate target 8, target 9(c); FAF `Construction/Paper/TheoremDP.lean`,
`Construction/LIA.lean`; `bli-superbelief` `Paper.lean`; `bli-transfer` `WitnessLia.lean`
(template).
-/

namespace Cleanroom.Bli.BliAssemble

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliTransfer
open Cleanroom.Bli.BliSuperbelief hiding smallIndex

open Classical

noncomputable section

/-! ## The base of record -/

/-- **The base of record**: FAF's LIA over `paperDP 𝗜𝚺₁`, as a rational history.
Source: mandate target 8
Kind: D
Fidelity: exact -/
def liaBase : RatHistory := liaQuote (paperDP 𝗜𝚺₁)

/-- `ratHistory liaBase` **is** `liaHistory (paperDP 𝗜𝚺₁)` (the same term up to unfolding).
Source: FAF `liaHistory_eq_quote_cast`; mandate target 4 (trap: the wrong market)
Kind: L
Fidelity: exact -/
theorem ratHistory_liaBase : ratHistory liaBase = liaHistory (paperDP 𝗜𝚺₁) := rfl

/-- The base is a logical inductor over `paperDP 𝗜𝚺₁`: FAF's `paperLIA`.
Source: FAF `paperLIA` (`Construction/Paper/TheoremDP.lean:442`)
Kind: L
Fidelity: exact -/
instance liaBase_isLogicalInductor : IsLogicalInductor (ratHistory liaBase) (paperDP 𝗜𝚺₁) :=
  paperLIA 𝗜𝚺₁

/-! ## A candidate on every day, and the reader -/

/-- The zero table is a grid table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma zeroTable_mem_grid (𝓜 : Mesh) (m : ℕ) :
    (fun _ => 0 : Table smallIndex m) ∈ grid smallIndex 𝓜.d m := by
  rw [mem_grid_iff]; intro φ; exact zero_mem_gridVals _

/-- The code of the day-`m` zero table under the write-out coding.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def zeroState (𝓜 : Mesh) (m : ℕ) : ℕ := (writeOutCoding 𝓜).code m (fun _ => 0)

/-- The zero state's code is a candidate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma zeroState_mem (𝓜 : Mesh) (m : ℕ) : zeroState 𝓜 m ∈ (writeOutCoding 𝓜).states m :=
  (writeOutCoding 𝓜).code_mem_states (zeroTable_mem_grid 𝓜 m)

/-- **The map fires on every day**: at the day-`(n+1)` zero state's atom.
Source: mandate target 8 ("the map fires on every day `n` at some `ψ`")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem tentExprMap_fires_every_day (𝓜 : Mesh) (n : ℕ) :
    tentExprMap 𝓜 (writeOutCoding 𝓜) n (stateAtom (n + 1) (zeroState 𝓜 (n + 1))) ≠ none := by
  rw [tentExprMap_of_tierA
    (not_smallOn_stateAtom (writeOutCoding 𝓜) (Nat.lt_succ_self n) (zeroState_mem 𝓜 (n + 1)))
    (tierA_stateAtom (writeOutCoding 𝓜) (Nat.lt_succ_self n) (zeroState_mem 𝓜 (n + 1)))]
  exact Option.some_ne_none _

/-- **The state reader**: every day, one share of `⊥` at the coefficient `price ⌜𝑸_1 = 0⌝ 0` —
the day-`1` zero state's atom read at day `0`, where the map fires. (An e.c. trader can only
name sentences of polynomial size, so a reader of a *day-`n`* state atom on day `n` is not e.c.)
Source: mandate target 8 (trader side); `bli-transfer` `familyReader` (template)
Kind: D
Fidelity: n/a -/
def stateReader (𝓜 : Mesh) : Trader where
  strat n :=
    { trades := (List.range 1).map fun _ =>
        (EF.price (stateAtom 1 (zeroState 𝓜 1)) 0, (⊥ : Sentence))
      rank_le := by
        intro p hp
        simp only [List.mem_map] at hp
        obtain ⟨j, _, rfl⟩ := hp
        simp [EF.rank] }

/-- The state reader is efficiently computable (fixed coefficient, fixed sentence).
Source: mandate target 8 (trader side); FAF `EfficientlyComputable.ofTradeBlocksBig`
Kind: C
Fidelity: exact
Hyps: (a) none -/
lemma stateReader_ec (𝓜 : Mesh) : EfficientlyComputable (stateReader 𝓜) :=
  EfficientlyComputable.ofTradeBlocksBig (stateReader 𝓜) (fun _ => 1)
    (fun _ => EF.price (stateAtom 1 (zeroState 𝓜 1)) 0) (fun _ => (⊥ : Sentence))
    (UnaryRuler.const 1)
    (MachineSpliceStream.serialize_price (MachineSentenceCodes.const (stateAtom 1 (zeroState 𝓜 1)))
      (UnaryRuler.const 0) (MachineDigits.const 0))
    (MachineSentenceCodes.const ⊥)
    (fun _ => rfl)

/-- **The trader side is exercised**: the state reader's splice is not the identity on any day
(its day-`n` trade list changes: the coefficient becomes `letE (price ⌜𝑸_1 = 0⌝ 0) (chainExpr …)`).
Syntactic: the spliced coefficient evaluates on the base to what the original evaluates to on the
overlay — that is L1's point and what makes the splice harmless. The payload is fixed (day `0`),
not day-varying (module docstring).
Source: mandate target 8 (trader side)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem stateReader_splice_ne (𝓜 : Mesh) (n : ℕ) :
    ((Trader.spliceOn (tentExprMap 𝓜 (writeOutCoding 𝓜)) (tentExprMap_rank 𝓜 (writeOutCoding 𝓜))
        (stateReader 𝓜)).strat n).trades ≠ ((stateReader 𝓜).strat n).trades := by
  have hfire : tentExprMap 𝓜 (writeOutCoding 𝓜) 0 (stateAtom 1 (zeroState 𝓜 1)) =
      some (chainExpr 𝓜 (writeOutCoding 𝓜) 0 ([(1, zeroState 𝓜 1)], none)) :=
    tentExprMap_of_tierA
      (not_smallOn_stateAtom (writeOutCoding 𝓜) zero_lt_one (zeroState_mem 𝓜 1))
      (tierA_stateAtom (writeOutCoding 𝓜) zero_lt_one (zeroState_mem 𝓜 1))
  simp [stateReader, Cleanroom.Bli.BliTransfer.AttemptA.EF.spliceOn_price_some _ hfire]

/-! ## The difference from the LIA -/

/-- **`𝐏 ≠ liaHistory` on day `n`, given a face point's atom off the LIA's support** (named
hypothesis `hoff`): the LIA quotes it `0` (`liaQuote_eq_zero_of_not_mem_support`), the tent
charges every face point. A composition under a named hypothesis, not a witness; `hoff` is
discharged from `bli-overlay`'s `N₀` on by `bliHistory_ne_lia_from`.
Source: mandate target 8 ("the overlay differs from the LIA on every day"); `bli-superbelief` `liaQuote_eq_zero_of_not_mem_support`
Kind: C
Fidelity: weaker: under the named support hypothesis (discharged for `n ≥ N₀` below)
Hyps: (a) the LIA's range; `hoff` named -/
theorem bliHistory_ne_lia_of_offSupport (𝓜 : Mesh) (n : ℕ)
    (hoff : ∃ A ∈ faceProd smallIndex 𝓜.d n (actualTable smallIndex liaBase n),
      stateAtom (n + 1) ((writeOutCoding 𝓜).code (n + 1) A) ∉ (liaStates (paperDP 𝗜𝚺₁) n).support) :
    ∃ ψ, bliHistory liaBase 𝓜 (tentSkeleton smallIndex 𝓜) (writeOutCoding 𝓜) n ψ ≠
      liaHistory (paperDP 𝗜𝚺₁) n ψ := by
  obtain ⟨A, hA, hoff⟩ := hoff
  obtain ⟨A', -, hne⟩ := bliHistory_ne_base_on_stateAtoms_of_zero liaBase 𝓜 (writeOutCoding 𝓜)
    (range_of_isLogicalInductor liaBase (paperDP 𝗜𝚺₁)) n
    ⟨A, hA, liaQuote_eq_zero_of_not_mem_support (paperDP 𝗜𝚺₁) n hoff⟩
  exact ⟨_, hne⟩

/-- **`𝐏` and FAF's LIA over `paperDP 𝗜𝚺₁` differ on some sentence every day from `N₀` on** —
the mandate's "the overlay differs from the LIA on every day", unconditional for `n ≥ N₀`
(`bli-overlay`'s `firm_support_subset_smallSet`: `N₀ = (C + 16)^2` for the structured-escape
constant `C`). Composition: every sentence the trading firm trades on day `n ≥ N₀` is small on
day `n`; the LIA's day-`n` support is inside the firm's (`liaStates_support_subset_firm`); a
day-`(n+1)` candidate atom is not small on day `n` (`stateAtom_large`); so a face point's atom is
off the LIA's support, and `bliHistory_ne_lia_of_offSupport` applies. For days `< N₀` only the
dichotomy is available. This is the witness of record for target 8's fourth conjunct (round-1
fidelity audit B1: the auditor's probe, landed).
Source: mandate target 8 ("the overlay differs from the LIA on every day"); `bli-overlay` T2 (`firm_support_subset_smallSet`); `bli-superbelief` `liaStates_support_subset_firm`; `bli-found` `stateAtom_large`
Kind: N+
Fidelity: weaker: from `N₀` on (days `< N₀` keep the dichotomy)
Hyps: (a) none -/
theorem bliHistory_ne_lia_from (𝓜 : Mesh) :
    ∃ N₀, ∀ n ≥ N₀, ∃ ψ,
      bliHistory liaBase 𝓜 (tentSkeleton smallIndex 𝓜) (writeOutCoding 𝓜) n ψ ≠
        liaHistory (paperDP 𝗜𝚺₁) n ψ := by
  obtain ⟨N₀, hN₀⟩ := Cleanroom.Bli.BliOverlay.firm_support_subset_smallSet
  refine ⟨N₀, fun n hn => ?_⟩
  apply bliHistory_ne_lia_of_offSupport 𝓜 n
  obtain ⟨A, hA⟩ := exists_mem_faceProd 𝓜 n (actualTable smallIndex liaBase n)
  refine ⟨A, hA, fun hmem => ?_⟩
  have hfirm := liaStates_support_subset_firm (paperDP 𝗜𝚺₁) n hmem
  have hsmall : SmallOn n (stateAtom (n + 1) ((writeOutCoding 𝓜).code (n + 1) A)) :=
    mem_smallSet.mp (hN₀ n hn (paperDP 𝗜𝚺₁) _ hfirm)
  exact stateAtom_large
    ((writeOutCoding 𝓜).large_of_mem
      ((writeOutCoding 𝓜).code_mem_states (faceProd_subset_grid _ _ hA)))
    n (Nat.le_succ n) hsmall

/-! ## The package -/

/-- **The hypothesis package of L2's row of record is inhabited at FAF's logical inductor**
(target 8, the grade of record: N+ for everything except the certificate and the table). At
`liaBase = liaQuote (paperDP 𝗜𝚺₁)`, every mesh `𝓜` and the write-out coding: (1) the base is a
logical inductor over `paperDP 𝗜𝚺₁` (`paperLIA`); (2) every stage of `paperDP 𝗜𝚺₁` has a
consistent world (`paperDP_hworld`, so the criterion is not vacuous there); (3) the map fires on
every day; (4) `𝐏` charges a face point's atom on every day; (5) the splice of the e.c.
`stateReader` is not the identity on any day; (6) on every day, `𝐏` and the LIA disagree on some
day-`(n+1)` candidate atom unless the LIA already distributes mass one over the candidates (`E5`
plus a case split); (7) every stage of the state-learning process `bliDP (paperDP 𝗜𝚺₁) states actual`
has a consistent world, for every `states`, `actual` (`bliDP_paperDP_hworld`); (8) **from some
`N₀` on, `𝐏` and the LIA differ on some sentence every day** (`bliHistory_ne_lia_from`: the
mandate's "differs from the LIA on every day", unconditional for `n ≥ N₀`; days `< N₀` have (6)).
Not claimed: the criterion for `𝐏` (open rows), and a day-varying e.c. reader (module docstring).
Source: mandate target 8; [[bli-program]] §7 row L2 ("va"); FAF `paperLIA`, `paperDP_hworld`; `bli-found` `bliDP_paperDP_hworld`; `bli-overlay` T2
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem bli_hypotheses_paperDP (𝓜 : Mesh) :
    IsLogicalInductor (ratHistory liaBase) (paperDP 𝗜𝚺₁) ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n)) ∧
      (∀ n, ∃ ψ, tentExprMap 𝓜 (writeOutCoding 𝓜) n ψ ≠ none) ∧
      (∀ n, ∃ A ∈ faceProd smallIndex 𝓜.d n (actualTable smallIndex liaBase n),
        0 < bliHistory liaBase 𝓜 (tentSkeleton smallIndex 𝓜) (writeOutCoding 𝓜) n
          (stateAtom (n + 1) ((writeOutCoding 𝓜).code (n + 1) A))) ∧
      (EfficientlyComputable (stateReader 𝓜) ∧ ∀ n,
        ((Trader.spliceOn (tentExprMap 𝓜 (writeOutCoding 𝓜))
            (tentExprMap_rank 𝓜 (writeOutCoding 𝓜)) (stateReader 𝓜)).strat n).trades ≠
          ((stateReader 𝓜).strat n).trades) ∧
      (∀ n, (∃ q ∈ (writeOutCoding 𝓜).states (n + 1),
          bliHistory liaBase 𝓜 (tentSkeleton smallIndex 𝓜) (writeOutCoding 𝓜) n
              (stateAtom (n + 1) q) ≠ liaHistory (paperDP 𝗜𝚺₁) n (stateAtom (n + 1) q)) ∨
        ∑ q ∈ (writeOutCoding 𝓜).states (n + 1), liaBase n (stateAtom (n + 1) q) = 1) ∧
      (∀ (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) (n : ℕ),
        ∃ v : PCWorld, v.ConsistentWith ((bliDP (paperDP 𝗜𝚺₁) states actual).D n)) ∧
      (∃ N₀, ∀ n ≥ N₀, ∃ ψ,
        bliHistory liaBase 𝓜 (tentSkeleton smallIndex 𝓜) (writeOutCoding 𝓜) n ψ ≠
          liaHistory (paperDP 𝗜𝚺₁) n ψ) :=
  ⟨paperLIA 𝗜𝚺₁, paperDP_hworld 𝗜𝚺₁,
    fun n => ⟨_, tentExprMap_fires_every_day 𝓜 n⟩,
    bliHistory_pos_on_face liaBase 𝓜 (writeOutCoding 𝓜)
      (range_of_isLogicalInductor liaBase (paperDP 𝗜𝚺₁)),
    ⟨stateReader_ec 𝓜, stateReader_splice_ne 𝓜⟩,
    bliHistory_ne_base_on_stateAtoms_dichotomy liaBase 𝓜 (tentSkeleton smallIndex 𝓜)
      (writeOutCoding 𝓜),
    fun states actual => bliDP_paperDP_hworld states actual,
    bliHistory_ne_lia_from 𝓜⟩

/-- **The package with the criterion**, at `dyadicMesh` and the write-out coding: the package
above and `IsLogicalInductor (bliHistory liaBase dyadicMesh …) (paperDP 𝗜𝚺₁)` — the last conjunct
is `bliHistory_isLogicalInductor`, which rests on the open rows. Listed as open for that reason;
the grade of record is `bli_hypotheses_paperDP`'s.
Source: mandate target 8
Kind: OPEN
Fidelity: n/a (rests on `tentOracle_exists`, `bliOv_computableTable`)
Hyps: (a) none beyond the open rows -/
theorem bli_package_paperDP :
    (IsLogicalInductor (ratHistory liaBase) (paperDP 𝗜𝚺₁) ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n)) ∧
      (∀ n, ∃ ψ, tentExprMap dyadicMesh (writeOutCoding dyadicMesh) n ψ ≠ none) ∧
      (∀ n, ∃ A ∈ faceProd smallIndex dyadicMesh.d n (actualTable smallIndex liaBase n),
        0 < bliHistory liaBase dyadicMesh (tentSkeleton smallIndex dyadicMesh)
          (writeOutCoding dyadicMesh) n
          (stateAtom (n + 1) ((writeOutCoding dyadicMesh).code (n + 1) A))) ∧
      (EfficientlyComputable (stateReader dyadicMesh) ∧ ∀ n,
        ((Trader.spliceOn (tentExprMap dyadicMesh (writeOutCoding dyadicMesh))
            (tentExprMap_rank dyadicMesh (writeOutCoding dyadicMesh))
            (stateReader dyadicMesh)).strat n).trades ≠
          ((stateReader dyadicMesh).strat n).trades) ∧
      (∀ n, (∃ q ∈ (writeOutCoding dyadicMesh).states (n + 1),
          bliHistory liaBase dyadicMesh (tentSkeleton smallIndex dyadicMesh)
              (writeOutCoding dyadicMesh) n (stateAtom (n + 1) q) ≠
            liaHistory (paperDP 𝗜𝚺₁) n (stateAtom (n + 1) q)) ∨
        ∑ q ∈ (writeOutCoding dyadicMesh).states (n + 1), liaBase n (stateAtom (n + 1) q) = 1) ∧
      (∀ (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) (n : ℕ),
        ∃ v : PCWorld, v.ConsistentWith ((bliDP (paperDP 𝗜𝚺₁) states actual).D n)) ∧
      (∃ N₀, ∀ n ≥ N₀, ∃ ψ,
        bliHistory liaBase dyadicMesh (tentSkeleton smallIndex dyadicMesh) (writeOutCoding dyadicMesh)
            n ψ ≠
          liaHistory (paperDP 𝗜𝚺₁) n ψ)) ∧
    IsLogicalInductor
      (bliHistory liaBase dyadicMesh (tentSkeleton smallIndex dyadicMesh) (writeOutCoding dyadicMesh))
      (paperDP 𝗜𝚺₁) :=
  ⟨bli_hypotheses_paperDP dyadicMesh, bliHistory_isLogicalInductor liaBase (paperDP 𝗜𝚺₁)⟩

/-! ## The self-consistent instance over `bliDP` (target 9(c)) -/

/-- **The self-consistent state-learning instance at `paperDP 𝗜𝚺₁`** (target 9(c)): a
realized-state sequence `actual` such that the LIA over `bliDP (paperDP 𝗜𝚺₁) c.states actual`
rounds to **its own** states — the self-consistent process of [[bli-program]] §2.5's B2 encoding.
Instance of `Fixpoint.exists_stateLearns_fixpoint` (every process), built from the day-locality
of `liaStates` in the deductive process (`liaStates_eq_of_eq_prefix`) and of `bliDP`'s schedule.
Not `bli-linkage`'s K5 (linked superbelief, bracket balance) — the mandate's cross-reference
oversold; and no `IsLogicalInductor` instance over `bliDP … actual` is claimed (`actualFix` is
noncomputable as defined, so `bliDP_computable` does not apply).
Source: [[bli-program]] §2.5; mandate target 9(c)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem exists_stateLearns_fixpoint_paperDP (𝓜 : Mesh) (c : StateCoding 𝓜) :
    ∃ actual : ℕ → ℕ,
      StateLearns (liaQuote (bliDP (paperDP 𝗜𝚺₁) c.states actual)) 𝓜 c c.states actual :=
  exists_stateLearns_fixpoint 𝓜 c (paperDP 𝗜𝚺₁)

end

end Cleanroom.Bli.BliAssemble
