import Mathlib.Topology.Sequences
import Mathlib.Topology.Constructions.SumProd

/-!
# Closed graphs over a set: the definition of record of the `fix-kakutani` package

`HasClosedGraphOn F K` says that the graph of the correspondence `F : α → Set β` *restricted to
the domain `K`* — the set `{(x, y) | x ∈ K ∧ y ∈ F x}` — is closed in `α × β`. Values of `F`
off `K` play no role, so a consumer never has to define its correspondence outside the domain
it cares about. This is the one hypothesis of Kakutani's theorem that consumers must *check*
(plan §0.4 rule 11); the sequential characterization below is how they usually check it.

Package: `Cleanroom.Found.FixKakutani` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Found.FixKakutani

open Set Filter Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- The correspondence `F` has a closed graph over `K`: `{(x, y) | x ∈ K ∧ y ∈ F x}` is closed in
`α × β`. Values of `F` outside `K` are irrelevant. For a **non-closed** `K` this is closedness in
the ambient product, strictly stronger than closedness relative to `K × β` (the identity
correspondence `x ↦ {x}` on `Ioo 0 1` fails it, since its graph accumulates at `(0, 0)`); the
corpus's domains are compact, every domain in this package is compact, and consumers should
state closed domains.
Source: [[fixpoint-lit-inventory]] 017 (mathematical-formulation §1: "F has a closed graph")
Kind: D
Fidelity: exact for a closed (in particular compact) `K`, which is the corpus's setting (the graph
is taken over the domain `K` only; see the module docstring)
Hyps: n/a -/
def HasClosedGraphOn (F : α → Set β) (K : Set α) : Prop :=
  IsClosed {p : α × β | p.1 ∈ K ∧ p.2 ∈ F p.1}

/-- A closed graph over `K` has closed values at every point of `K` (each value is a section of
the graph).
Source: none: infrastructure (target 3 of the mandate, the section-closedness lemma)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HasClosedGraphOn.isClosed_apply {F : α → Set β} {K : Set α} (h : HasClosedGraphOn F K)
    {x : α} (hx : x ∈ K) : IsClosed (F x) := by
  have : F x = (fun y : β => (x, y)) ⁻¹' {p : α × β | p.1 ∈ K ∧ p.2 ∈ F p.1} := by
    ext y
    simp [hx]
  rw [this]
  exact h.preimage (Continuous.prodMk_right x)

/-- Limits along any filter stay in a closed graph: if `xs n ∈ K`, `ys n ∈ F (xs n)` eventually,
`xs → x` and `ys → y`, then `x ∈ K` and `y ∈ F x`. This is the direction of the sequential
characterization that consumers use to pass to limits.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem HasClosedGraphOn.mem_of_tendsto {F : α → Set β} {K : Set α} (h : HasClosedGraphOn F K)
    {ι : Type*} {l : Filter ι} [l.NeBot] {xs : ι → α} {ys : ι → β} {x : α} {y : β}
    (hmem : ∀ᶠ n in l, xs n ∈ K ∧ ys n ∈ F (xs n))
    (hxs : Tendsto xs l (𝓝 x)) (hys : Tendsto ys l (𝓝 y)) : x ∈ K ∧ y ∈ F x := by
  unfold HasClosedGraphOn at h
  have hxy : (x, y) ∈ {p : α × β | p.1 ∈ K ∧ p.2 ∈ F p.1} :=
    IsClosed.mem_of_tendsto h (hxs.prodMk_nhds hys) hmem
  exact hxy

/-- **Sequential characterization of a closed graph** (first-countable spaces, e.g. metric
spaces): `F` has a closed graph over `K` iff for all sequences `xs` in `K` and `ys` with
`ys n ∈ F (xs n)`, `xs → x` and `ys → y` imply `x ∈ K` and `y ∈ F x`.
Source: none: infrastructure (target 1 of the mandate, "the sequential form")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem hasClosedGraphOn_iff_seq [FirstCountableTopology α] [FirstCountableTopology β]
    {F : α → Set β} {K : Set α} :
    HasClosedGraphOn F K ↔
      ∀ (xs : ℕ → α) (ys : ℕ → β) (x : α) (y : β), (∀ n, xs n ∈ K ∧ ys n ∈ F (xs n)) →
        Tendsto xs atTop (𝓝 x) → Tendsto ys atTop (𝓝 y) → x ∈ K ∧ y ∈ F x := by
  constructor
  · intro h xs ys x y hmem hxs hys
    exact h.mem_of_tendsto (Eventually.of_forall hmem) hxs hys
  · intro h
    unfold HasClosedGraphOn
    rw [← isSeqClosed_iff_isClosed]
    intro p q hp hq
    have h1 : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hq
    have h2 : Tendsto (fun n => (p n).2) atTop (𝓝 q.2) := (continuous_snd.tendsto q).comp hq
    exact h (fun n => (p n).1) (fun n => (p n).2) q.1 q.2 hp h1 h2

/-- Sequential characterization when the domain `K` is closed: the limit `x` is then in `K`
automatically, and only `y ∈ F x` has to be shown. This is the form consumers with explicit
best-response maps prove.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem hasClosedGraphOn_iff_seq_of_isClosed [FirstCountableTopology α]
    [FirstCountableTopology β] {F : α → Set β} {K : Set α} (hK : IsClosed K) :
    HasClosedGraphOn F K ↔
      ∀ (xs : ℕ → α) (ys : ℕ → β) (x : α) (y : β), (∀ n, xs n ∈ K ∧ ys n ∈ F (xs n)) →
        Tendsto xs atTop (𝓝 x) → Tendsto ys atTop (𝓝 y) → y ∈ F x := by
  rw [hasClosedGraphOn_iff_seq]
  constructor
  · intro h xs ys x y hmem hxs hys
    exact (h xs ys x y hmem hxs hys).2
  · intro h xs ys x y hmem hxs hys
    exact ⟨hK.mem_of_tendsto hxs (Eventually.of_forall fun n => (hmem n).1),
      h xs ys x y hmem hxs hys⟩

/-- `F` restricted to `K` and extended by `∅` off `K`: `restrictTo F K x = F x` for `x ∈ K` and
`= ∅` otherwise. Used to move between statements "over `K`" and Mathlib's hemicontinuity
predicates, which are stated for correspondences defined everywhere.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def restrictTo (F : α → Set β) (K : Set α) : α → Set β :=
  fun x => {y | x ∈ K ∧ y ∈ F x}

omit [TopologicalSpace α] [TopologicalSpace β] in
/-- `restrictTo F K` agrees with `F` on `K`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem restrictTo_of_mem {F : α → Set β} {K : Set α} {x : α} (hx : x ∈ K) :
    restrictTo F K x = F x := by
  ext y
  simp [restrictTo, hx]

omit [TopologicalSpace α] [TopologicalSpace β] in
/-- `restrictTo F K` is `∅` off `K`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem restrictTo_of_not_mem {F : α → Set β} {K : Set α} {x : α} (hx : x ∉ K) :
    restrictTo F K x = ∅ := by
  ext y
  simp [restrictTo, hx]

omit [TopologicalSpace α] [TopologicalSpace β] in
/-- Membership in `restrictTo F K x` unfolds to `x ∈ K ∧ y ∈ F x`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mem_restrictTo {F : α → Set β} {K : Set α} {x : α} {y : β} :
    y ∈ restrictTo F K x ↔ x ∈ K ∧ y ∈ F x := Iff.rfl

omit [TopologicalSpace α] [TopologicalSpace β] in
/-- If the values of `F` on `K` lie in `L`, so do the values of `restrictTo F K` everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem restrictTo_subset {F : α → Set β} {K : Set α} {L : Set β} (hF : ∀ x ∈ K, F x ⊆ L)
    (x : α) : restrictTo F K x ⊆ L := by
  intro y hy
  exact hF x hy.1 hy.2

/-- The graph of `F` over `K` is the graph of `restrictTo F K` over the whole space.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem hasClosedGraphOn_restrictTo_univ_iff {F : α → Set β} {K : Set α} :
    HasClosedGraphOn (restrictTo F K) univ ↔ HasClosedGraphOn F K := by
  unfold HasClosedGraphOn
  simp [mem_restrictTo]

end Cleanroom.Found.FixKakutani
