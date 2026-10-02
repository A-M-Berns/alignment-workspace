import Cleanroom.Bli.BliAssemble.Certificate

/-!
# `bli-assemble` · Headline: L2 (target 4), the non-degeneracy bundle (target 7), the
denominator-grid variant (target 11)

**L2, three forms**, from hypothetical to the one that would be of record, mirroring
`bli-transfer`:

* `bliHistory_isLogicalInductor_of` — **the row of record**: for every base `Q` that is a
  logical inductor over `DP` (as `ratHistory Q`), every mesh and coding, the constructed market
  `bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c` is a logical inductor over `DP`, given a
  `SpliceCertificate` for `tentExprMap 𝓜 c` and a `ComputableTable` for `bliOv` — both **named
  hypotheses**, never fields of a structure. Target 1 rewrites `bliHistory` as an overlay, target
  3 supplies the expression map (its range hypothesis derived from the inductor instance, not
  assumed), and `bli-transfer`'s `overlay_isLogicalInductor'` concludes. Ledger Status:
  `partial: rewrite certificate open` (the certificate and the table are `tentCertificate` and
  `bliOv_computableTable`, both open at the dyadic mesh and the write-out coding).
* `bliHistory_isLogicalInductor_of_certificate` — `hov` discharged by the **open**
  `bliOv_computableTable` at the dyadic mesh and the write-out coding; the base's own table is
  derived from the inductor instance (`computableTable_of_isLogicalInductor`). Rests on an open
  statement; listed.
* `bliHistory_isLogicalInductor` — both discharged (`tentCertificate`, open). Rests on two open
  statements; listed. **Not** the row the ledger calls L2.

The instance `[IsLogicalInductor (ratHistory Q) DP]` and the `Q` inside `bliHistory` are the same
term (mandate trap: the wrong market); `Lia.lean` instantiates `Q := liaQuote (paperDP 𝗜𝚺₁)`, for
which `ratHistory (liaQuote DP) = liaHistory DP` definitionally.

**Target 7** — `bliHistory_tent_package`: the scoped Roman bundle, face non-degeneracy, the
small-sentence update bound and the range, conjoined (`C`, transport of `bli-trajectory`'s rows);
`bliHistory_tent_LI_and_BLI` conjoins it with L2's row of record. Scope: faith is the **scoped**
`E2xScoped`/`E3Scoped` (full-scope `E2x` fails for the tent instance, `e2x_full_scope_fails`), and
non-degeneracy is on the **product face** (dogmatic at `0/1` prices), not full support.

**Target 11** — `bliHistory_isLogicalInductor_denominator`: L2's row of record at
`denominatorMesh Q` (noncomputable), conjoined with the exact Tier-A Bayesian update
`bli_TB_on_tierA_denominator`; the certificate and table are hypotheses for a noncomputable
mesh — `partial: certificate and table open at a noncomputable mesh`.

Sources: [[bli-program]] §0, §3.1, §5, §7 items 3, 8; bli-slides-046, bli-slides-040; mandate targets 4, 7, 11.
-/

namespace Cleanroom.Bli.BliAssemble

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliTransfer Cleanroom.Bli.BliSuperbelief

open Classical

noncomputable section

/-! ## Facts derived from the inductor instance (never assumed) -/

/-- The base's range `[0, 1]`, derived from its inductor certificate.
Source: none: infrastructure (FAF `IsLogicalInductor.price_mem_Icc`)
Kind: L
Fidelity: n/a -/
lemma range_of_isLogicalInductor (Q : RatHistory) (DP : DeductiveProcess)
    [hQ : IsLogicalInductor (ratHistory Q) DP] : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1 := by
  intro n φ
  have h := IsLogicalInductor.price_mem_Icc (P := ratHistory Q) (DP := DP) n φ
  unfold ratHistory at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- The base's computable table, derived from its inductor certificate.
Source: none: infrastructure (FAF `IsLogicalInductor.marketComputable`; `bli-transfer`'s `ComputableMarket.exists_computableTable`)
Kind: L
Fidelity: n/a -/
lemma computableTable_of_isLogicalInductor (Q : RatHistory) (DP : DeductiveProcess)
    [hQ : IsLogicalInductor (ratHistory Q) DP] : ComputableTable Q := by
  obtain ⟨tab, hex, hcomp⟩ := ComputableMarket.exists_computableTable hQ.marketComputable
  refine ⟨tab, fun n φ => ?_, hcomp⟩
  have h := hex n φ
  unfold ratHistory at h
  exact_mod_cast h

/-! ## Target 4: L2 -/

/-- **L2, the row of record** (target 4, first form). For every base `Q` with
`[IsLogicalInductor (ratHistory Q) DP]`, every mesh `𝓜` and coding `c`, the constructed market
`bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c` — which copies `Q`'s day-`n` small prices
exactly and prices the state algebra by the tent trajectory prior — is a logical inductor over
`DP`, **given** a splice certificate `C` for the tent expression map and a computable table
`hov` for the re-pricing. Both are named hypotheses: `C` is the polynomial-time run-level oracle
with its spec on every spelling (open: `tentOracle_exists`), `hov` the explicit computable
function behind "computability in name only" (open: `bliOv_computableTable`). Proof: target 1
rewrites `bliHistory` as `overlay (ratHistory Q) (bliOv …)`, target 3's `tentMap` (range derived
from the instance) is the expression map, and `bli-transfer`'s `overlay_isLogicalInductor'`
concludes — `marketComputable` through `overlay_computableMarket` from the base's certificate
and `hov`, `processComputable` inherited, `noExploit` at the criterion's own quantifier. No
coherence hypothesis on the base (Known issue 1: the slide's coherence clause is false for FAF's
LIA and is not needed).
Source: bli-slides-046 (the conjecture), bli-slides-040; [[bli-program]] §3.1 (Route T), §5 (L2), §7 items 3, 8; mandate target 4 (first form)
Kind: C
Fidelity: exact for the stated hypotheses (the program's L2 with the certificate and the table named)
Hyps: (a) the inductor instance, the mesh and coding; `C` and `hov` named — the instance's obligations, both OPEN at `dyadicMesh`/`writeOutCoding` (`tentCertificate`, `bliOv_computableTable`); no (b), no (c) -/
theorem bliHistory_isLogicalInductor_of (Q : RatHistory) (DP : DeductiveProcess) (𝓜 : Mesh)
    (c : StateCoding 𝓜) [IsLogicalInductor (ratHistory Q) DP]
    (C : SpliceCertificate (tentExprMap 𝓜 c))
    (hov : ComputableTable (bliOv Q 𝓜 (tentSkeleton smallIndex 𝓜) c)) :
    IsLogicalInductor (bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c) DP := by
  rw [bliHistory_eq_overlay]
  exact overlay_isLogicalInductor' (ratHistory Q) DP _
    (tentMap Q 𝓜 c (range_of_isLogicalInductor Q DP)) C hov

/-- **L2 with the table discharged** (target 4, second form), at the dyadic mesh and the
write-out coding: the re-pricing's computable table is the **open** `bliOv_computableTable`
(the base's own table is derived from the instance). Rests on an open statement.
Source: mandate target 4 (second form), target 5
Kind: OPEN
Fidelity: n/a (rests on `bliOv_computableTable`)
Hyps: (a) the inductor instance; `C` named -/
theorem bliHistory_isLogicalInductor_of_certificate (Q : RatHistory) (DP : DeductiveProcess)
    [IsLogicalInductor (ratHistory Q) DP]
    (C : SpliceCertificate (tentExprMap dyadicMesh (writeOutCoding dyadicMesh))) :
    IsLogicalInductor
      (bliHistory Q dyadicMesh (tentSkeleton smallIndex dyadicMesh) (writeOutCoding dyadicMesh))
      DP :=
  bliHistory_isLogicalInductor_of Q DP dyadicMesh (writeOutCoding dyadicMesh) C
    (bliOv_computableTable Q (computableTable_of_isLogicalInductor Q DP))

/-- **L2 with both obligations discharged** (target 4, third form): the certificate is
`tentCertificate` (open oracle) and the table `bliOv_computableTable` (open). Rests on two open
statements; **not** the ledger's L2 row — that is `bliHistory_isLogicalInductor_of`.
Source: mandate target 4 (third form), targets 5–6
Kind: OPEN
Fidelity: n/a (rests on `tentOracle_exists` and `bliOv_computableTable`)
Hyps: (a) the inductor instance -/
theorem bliHistory_isLogicalInductor (Q : RatHistory) (DP : DeductiveProcess)
    [IsLogicalInductor (ratHistory Q) DP] :
    IsLogicalInductor
      (bliHistory Q dyadicMesh (tentSkeleton smallIndex dyadicMesh) (writeOutCoding dyadicMesh))
      DP :=
  bliHistory_isLogicalInductor_of_certificate Q DP tentCertificate

/-! ## Target 7: the non-degeneracy bundle (transport) -/

/-- **The non-degeneracy bundle of the tent instance** (target 7): one conjunction of
`bli-trajectory`'s rows at `sk := tentSkeleton smallIndex 𝓜` — the scoped Roman bundle
`IsBLI_RomanScoped` (`E1x ∧ E2xScoped ∧ E3Scoped ∧ E4 ∧ E5`), face non-degeneracy of every
day's superbelief (`bliHistory_tent_nonDegenerate`), the small-sentence Bayesian update up to
the mesh (`bli_update_small`), and the range (`bliHistory_mem_Icc`). Plumbing: every conjunct is
a cited theorem; nothing is proved here. Scope, honestly: faith is **scoped** (full-scope `E2x`
fails for the tent instance, `e2x_full_scope_fails`), and non-degeneracy is on the **product
face** — dogmatic at `0/1` prices (`bli-superbelief`'s `dogmatism`, `supportEntry_null`), not
full support.
Source: [[bli-program]] §3.4, §3.5; bli-slides-017/018; mandate target 7
Kind: C
Fidelity: weaker: faith scoped, non-degeneracy on the face (as `bli-trajectory`'s rows)
Hyps: (a) `hQ` -/
theorem bliHistory_tent_package (Q : RatHistory) (𝓜 : Mesh) (c : StateCoding 𝓜)
    (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) :
    IsBLI_RomanScoped c (bliStateSystem Q 𝓜 c) (ratHistory Q)
        (bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c) ∧
      (∀ n, NonDegenerate 𝓜.d
        (fun A => bliPrice Q 𝓜 (tentSkeleton smallIndex 𝓜) c n (stateAtom (n + 1) (c.code (n + 1) A)))
        (actualTable smallIndex Q n)) ∧
      (∀ n, ∀ φ ∈ smallSet n,
        |bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c (n + 1) φ *
            bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c n
              (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) -
          bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c n
            (φ ⋏ stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1)))|
          ≤ (1 / (2 * (𝓜.d (n + 1) : ℝ))) *
            bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c n
              (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1)))) ∧
      (∀ n ψ, 0 ≤ bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c n ψ ∧
        bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c n ψ ≤ 1) :=
  ⟨bliHistory_isBLI_scoped c _ Q hQ, bliHistory_tent_nonDegenerate c Q hQ,
    fun n _ hφ => bli_update_small c _ Q hQ n hφ, bliHistory_mem_Icc c _ Q hQ⟩

/-- **L2 and the bundle together** (target 7): the criterion (row of record, named `C`/`hov`)
next to all the F8 rows, the range derived from the instance. Plumbing.
Source: [[bli-program]] §5 (the 70 % milestone: "a non-degenerate BLI over FAF's own inductor that no e.c. trader exploits, with computability inherited"); mandate target 7
Kind: C
Fidelity: as `bliHistory_isLogicalInductor_of` and `bliHistory_tent_package`
Hyps: (a) the inductor instance; `C`, `hov` named (OPEN at `dyadicMesh`/`writeOutCoding`) -/
theorem bliHistory_tent_LI_and_BLI (Q : RatHistory) (DP : DeductiveProcess) (𝓜 : Mesh)
    (c : StateCoding 𝓜) [IsLogicalInductor (ratHistory Q) DP]
    (C : SpliceCertificate (tentExprMap 𝓜 c))
    (hov : ComputableTable (bliOv Q 𝓜 (tentSkeleton smallIndex 𝓜) c)) :
    IsLogicalInductor (bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c) DP ∧
      IsBLI_RomanScoped c (bliStateSystem Q 𝓜 c) (ratHistory Q)
        (bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c) ∧
      (∀ n, NonDegenerate 𝓜.d
        (fun A => bliPrice Q 𝓜 (tentSkeleton smallIndex 𝓜) c n (stateAtom (n + 1) (c.code (n + 1) A)))
        (actualTable smallIndex Q n)) :=
  ⟨bliHistory_isLogicalInductor_of Q DP 𝓜 c C hov,
    (bliHistory_tent_package Q 𝓜 c (range_of_isLogicalInductor Q DP)).1,
    (bliHistory_tent_package Q 𝓜 c (range_of_isLogicalInductor Q DP)).2.1⟩

/-! ## Target 11: the denominator-grid variant -/

/-- **L2 at the denominator mesh, with the exact Tier-A update** (target 11): at
`bli-trajectory`'s `denominatorMesh Q` (noncomputable — products of the base's denominators),
the row of record's hypotheses `C`/`hov` are for a noncomputable mesh, so this is the
*hypothetical* form only; what the mesh buys is `bli_TB_on_tierA_denominator` with no grid
hypothesis: the total Bayesian update `𝐏_{n+1}(ψ) · 𝐏_n(σ) = 𝐏_n(ψ ⋏ σ)` holds **exactly** on
every day for every Tier-A `ψ` whose small part mentions no day-`(n+1)` atom. Ledger Status:
`partial: certificate and table open at a noncomputable mesh`.
Source: [[bli-program]] §3.5 (iii); mandate target 11
Kind: C
Fidelity: exact for the stated hypotheses
Hyps: (a) the inductor instance; `C`, `hov` named for a noncomputable mesh (not discharged, not dischargeable by the open rows, which are at `dyadicMesh`) -/
theorem bliHistory_isLogicalInductor_denominator (Q : RatHistory) (DP : DeductiveProcess)
    (c : StateCoding (denominatorMesh Q)) [IsLogicalInductor (ratHistory Q) DP]
    (C : SpliceCertificate (tentExprMap (denominatorMesh Q) c))
    (hov : ComputableTable
      (bliOv Q (denominatorMesh Q) (tentSkeleton smallIndex (denominatorMesh Q)) c)) :
    IsLogicalInductor
        (bliHistory Q (denominatorMesh Q) (tentSkeleton smallIndex (denominatorMesh Q)) c) DP ∧
      TB_on (TierAUpdatable c) (bliStateSystem Q (denominatorMesh Q) c)
        (bliHistory Q (denominatorMesh Q) (tentSkeleton smallIndex (denominatorMesh Q)) c) :=
  ⟨bliHistory_isLogicalInductor_of Q DP (denominatorMesh Q) c C hov,
    bli_TB_on_tierA_denominator c _ (range_of_isLogicalInductor Q DP)⟩

end

end Cleanroom.Bli.BliAssemble
