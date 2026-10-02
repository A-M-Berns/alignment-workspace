import Cleanroom.Udt.UdtCommTrust.Factor
import FiniteFactoredSets.Basic
import FiniteFactoredSets.Orthogonality

/-!
# `Cleanroom.Udt.UdtCommTrust.FfsBridge`: "factors as" is an FFS factorization of the image

Work package `udt-comm-trust`, targets T1(b) (the bridge) and T1(c) (orthogonality). The
paper says its formalism "was significantly inspired by Finite Factored Sets"
([[communication-trust-translated]] line 184); this file makes the inspiration a theorem: on the
image `S = Set.range (Yv, Zv)`, with the two coordinate partitions `bY`, `bZ`, support independence
of `Yv` and `Zv` is exactly FAF's `FiniteFactoredSets.IsFactorization {bY, bZ}` — provided the two
partitions are distinct and each coordinate takes two values (FFS's `nontrivial` clause excludes
constant coordinates, and a collapsed set `{bY, bZ} = {bY}` changes the meaning:
`eq_bot_of_isFactorization_singleton`).
-/

namespace Cleanroom.Udt.UdtCommTrust

open FiniteFactoredSets

variable {Ω Y Z : Type}

/-- The image of the product variable `(Yv, Zv)`: the finite set FFS's factorization lives on.
Source: none: infrastructure (T1(b))
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev prodRange (Yv : Ω → Y) (Zv : Ω → Z) : Type := Set.range fun ω => (Yv ω, Zv ω)

/-- The first-coordinate partition of the image.
Source: none: infrastructure (T1(b))
Kind: D
Fidelity: n/a
Hyps: n/a -/
def bY (Yv : Ω → Y) (Zv : Ω → Z) : Setoid (prodRange Yv Zv) := Setoid.comap (fun s => s.1.1) ⊥

/-- The second-coordinate partition of the image.
Source: none: infrastructure (T1(b))
Kind: D
Fidelity: n/a
Hyps: n/a -/
def bZ (Yv : Ω → Y) (Zv : Ω → Z) : Setoid (prodRange Yv Zv) := Setoid.comap (fun s => s.1.2) ⊥

/-- `X` takes at least two values on `Ω`.
Source: none: infrastructure (T1(b))
Kind: D
Fidelity: n/a
Hyps: n/a -/
def TwoValued {V : Type} (X : Ω → V) : Prop := ∃ ω ω', X ω ≠ X ω'

/-- Supporting lemma `bY_rel`: the relation of `bY` is equality of first coordinates.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem bY_rel (Yv : Ω → Y) (Zv : Ω → Z) (s t : prodRange Yv Zv) :
    bY Yv Zv s t ↔ s.1.1 = t.1.1 := Iff.rfl

/-- Supporting lemma `bZ_rel`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem bZ_rel (Yv : Ω → Y) (Zv : Ω → Z) (s t : prodRange Yv Zv) :
    bZ Yv Zv s t ↔ s.1.2 = t.1.2 := Iff.rfl

/-- Under support independence and a two-valued `Yv`, the two coordinate partitions are distinct:
a `bZ`-related pair with different `bY`-classes exists. Without this the set `{bY, bZ}` collapses
to a singleton and FFS's factorization predicate changes meaning (T1(b) trap).
Source: mandate T1(b)
Kind: P
Fidelity: n/a
Hyps: (a) -/
theorem bY_ne_bZ {Yv : Ω → Y} {Zv : Ω → Z} (hfac : FactorsAs Yv Zv) (hY : TwoValued Yv) :
    bY Yv Zv ≠ bZ Yv Zv := by
  intro heq
  obtain ⟨ω₁, ω₂, hne⟩ := hY
  obtain ⟨ω, hω₁, hω₂⟩ := hfac (Yv ω₁) ⟨ω₁, rfl⟩ (Zv ω₂) ⟨ω₂, rfl⟩
  let s : prodRange Yv Zv := ⟨(Yv ω, Zv ω), ⟨ω, rfl⟩⟩
  let t : prodRange Yv Zv := ⟨(Yv ω₂, Zv ω₂), ⟨ω₂, rfl⟩⟩
  have hZ : bZ Yv Zv s t := (bZ_rel Yv Zv s t).2 hω₂
  have hYst : bY Yv Zv s t := by rw [heq]; exact hZ
  exact hne (hω₁ ▸ (bY_rel Yv Zv s t).1 hYst)

/-- **The FFS bridge (T1(b))**: for two-valued coordinates, `Yv` and `Zv` are independent in
support iff the coordinate partitions are distinct and form an FFS factorization of the image.
Injectivity of the coordinate map is free (a point of the image is its two coordinates);
surjectivity is support independence; `nontrivial` is two-valuedness; and the distinctness
conjunct is what the singleton-collapse trap requires (the failure witness `Zv = Yv` in
`Witness.lean` fails *there*, while `IsFactorization {⊥}` holds).
Source: [[communication-trust-translated]] lines 184, 225–233; udt-rep-089, udt-rep-2-034
Kind: P
Fidelity: exact (bridge; the FFS side is FAF's `IsFactorization`)
Hyps: (a) -/
theorem factorsAs_iff_isFactorization {Yv : Ω → Y} {Zv : Ω → Z} (hY : TwoValued Yv)
    (hZ : TwoValued Zv) :
    FactorsAs Yv Zv ↔
      bY Yv Zv ≠ bZ Yv Zv ∧ IsFactorization ({bY Yv Zv, bZ Yv Zv} : Set (Setoid (prodRange Yv Zv))) := by
  constructor
  · intro hfac
    refine ⟨bY_ne_bZ hfac hY, ?_, ?_⟩
    · rintro b (rfl | rfl) ⟨-, h⟩
      · obtain ⟨ω₁, ω₂, hne⟩ := hY
        exact hne ((bY_rel Yv Zv _ _).1 (h ⟨(Yv ω₁, Zv ω₁), ⟨ω₁, rfl⟩⟩ ⟨(Yv ω₂, Zv ω₂), ⟨ω₂, rfl⟩⟩))
      · obtain ⟨ω₁, ω₂, hne⟩ := hZ
        exact hne ((bZ_rel Yv Zv _ _).1 (h ⟨(Yv ω₁, Zv ω₁), ⟨ω₁, rfl⟩⟩ ⟨(Yv ω₂, Zv ω₂), ⟨ω₂, rfl⟩⟩))
    · refine ⟨fun s t h => Subtype.ext (Prod.ext
        (Quotient.exact (congrFun h ⟨bY Yv Zv, Or.inl rfl⟩))
        (Quotient.exact (congrFun h ⟨bZ Yv Zv, Or.inr rfl⟩))), fun y => ?_⟩
      set p := Quotient.out (y ⟨bY Yv Zv, Or.inl rfl⟩) with hp
      set q := Quotient.out (y ⟨bZ Yv Zv, Or.inr rfl⟩) with hq
      obtain ⟨ωp, hωp⟩ := p.2
      obtain ⟨ωq, hωq⟩ := q.2
      obtain ⟨ω, hω₁, hω₂⟩ := hfac (Yv ωp) ⟨ωp, rfl⟩ (Zv ωq) ⟨ωq, rfl⟩
      refine ⟨⟨(Yv ω, Zv ω), ⟨ω, rfl⟩⟩, funext fun b => ?_⟩
      obtain ⟨b, hb⟩ := b
      rcases hb with rfl | rfl
      · refine Eq.trans (Quotient.sound (?_ : bY Yv Zv _ p)) (Quotient.out_eq _)
        show Yv ω = p.1.1
        rw [hω₁, ← hωp]
      · refine Eq.trans (Quotient.sound (?_ : bZ Yv Zv _ q)) (Quotient.out_eq _)
        show Zv ω = q.1.2
        rw [hω₂, ← hωq]
  · rintro ⟨hne, hfac⟩
    classical
    rw [factorsAs_iff]
    intro ω₁ ω₂
    let p₁ : prodRange Yv Zv := ⟨(Yv ω₁, Zv ω₁), ⟨ω₁, rfl⟩⟩
    let p₂ : prodRange Yv Zv := ⟨(Yv ω₂, Zv ω₂), ⟨ω₂, rfl⟩⟩
    have hB := (isFactorization_iff_existsUnique hfac.nontrivial).1 hfac
    obtain ⟨s, hs, -⟩ := hB fun b => if (b : Setoid _) = bY Yv Zv then p₁ else p₂
    have h1 : bY Yv Zv s p₁ := by simpa using hs ⟨bY Yv Zv, Or.inl rfl⟩
    have h2 : bZ Yv Zv s p₂ := by
      have := hs ⟨bZ Yv Zv, Or.inr rfl⟩
      simpa [hne.symm] using this
    obtain ⟨ω, hω⟩ := s.2
    refine ⟨ω, ?_, ?_⟩
    · have := (bY_rel Yv Zv s p₁).1 h1
      rw [← hω] at this
      exact this
    · have := (bZ_rel Yv Zv s p₂).1 h2
      rw [← hω] at this
      exact this

/-- The factored set of a support-independent pair with two-valued coordinates.
Source: none: infrastructure (T1(c))
Kind: D
Fidelity: n/a
Hyps: n/a -/
def factoredSetOf {Yv : Ω → Y} {Zv : Ω → Z} (hY : TwoValued Yv) (hZ : TwoValued Zv)
    (hfac : FactorsAs Yv Zv) : FactoredSet (prodRange Yv Zv) :=
  ⟨{bY Yv Zv, bZ Yv Zv}, ((factorsAs_iff_isFactorization hY hZ).1 hfac).2⟩

/-- The history of a basis element is contained in the singleton of that element
(`{b}` generates `b`, so `history b ⊆ {b}`).
Source: none: infrastructure (T1(c); FAF API request: `history_of_mem_basis`)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem history_subset_singleton_of_mem {S : Type} (F : FactoredSet S) {b : Setoid S}
    (hb : b ∈ F.B) : F.history b ⊆ {b} := by
  refine F.history_subset_of_generates (Set.singleton_subset_iff.2 hb) ?_
  rw [F.generates_iff_sInf_le (Set.singleton_subset_iff.2 hb)]
  simp [commonRefinement]

/-- **Orthogonality corollary (T1(c))**: in the factored set of a support-independent two-valued
pair, the two coordinate partitions are orthogonal (disjoint histories), so FFS orthogonality is a
consequence of the paper's "factors as".
Source: udt-rep-2-034(a); [[communication-trust-translated]] line 184
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem orthogonal_bY_bZ {Yv : Ω → Y} {Zv : Ω → Z} (hY : TwoValued Yv) (hZ : TwoValued Zv)
    (hfac : FactorsAs Yv Zv) :
    (factoredSetOf hY hZ hfac).Orthogonal (bY Yv Zv) (bZ Yv Zv) := by
  have hne := bY_ne_bZ hfac hY
  rw [FactoredSet.orthogonal_def]
  apply Set.eq_empty_of_subset_empty
  intro b ⟨hb1, hb2⟩
  have h1 := history_subset_singleton_of_mem (factoredSetOf hY hZ hfac) (Or.inl rfl) hb1
  have h2 := history_subset_singleton_of_mem (factoredSetOf hY hZ hfac) (Or.inr rfl) hb2
  simp only [Set.mem_singleton_iff] at h1 h2
  exact hne (h1 ▸ h2)

/-- **Orthogonality does not give a factorization** (udt-rep-2-034's "strict" direction), in the
degenerate form: in the trivial factored set `{⊥}` on `Fin 3`, `⊥` and `⊤` are orthogonal (`⊤` has
empty history) but `{⊥, ⊤}` is not a factorization (`⊤` is a trivial partition). Grade N−: a
non-degenerate witness (two non-trivial orthogonal partitions that are not jointly a factorization,
e.g. a coordinate and a coarsening of the other coordinate on `Fin 2 × Fin 3`) needs the history of
a coarsening, which is `history_spec`; not pursued.
Source: udt-rep-2-034
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem orthogonal_not_isFactorization :
    ∃ (F : FactoredSet (Fin 3)) (X Y : Setoid (Fin 3)),
      F.Orthogonal X Y ∧ ¬ IsFactorization ({X, Y} : Set (Setoid (Fin 3))) := by
  have hfac : IsFactorization ({⊥} : Set (Setoid (Fin 3))) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro b rfl ⟨-, h⟩
      exact absurd (h 0 1) (show (0 : Fin 3) ≠ 1 by decide)
    · intro s t h
      exact Quotient.exact (congrFun h ⟨⊥, rfl⟩)
    · intro y
      refine ⟨Quotient.out (y ⟨⊥, rfl⟩), funext fun b => ?_⟩
      obtain ⟨b, hb⟩ := b
      simp only [Set.mem_singleton_iff] at hb
      subst hb
      exact Quotient.out_eq _
  let F : FactoredSet (Fin 3) := ⟨{⊥}, hfac⟩
  refine ⟨F, ⊥, ⊤, ?_, ?_⟩
  · rw [FactoredSet.orthogonal_def]
    have htop : F.history ⊤ = ∅ := (F.history_spec ⊤ ⊤).2.2.1.2 rfl
    rw [htop, Set.inter_empty]
  · intro h
    exact h.nontrivial ⊤ (Or.inr rfl) (isTrivialPartition_top)

end Cleanroom.Udt.UdtCommTrust
