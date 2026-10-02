import Cleanroom.Corrigibility.CorrGeneralObject.Resist
import Cleanroom.Found.LitDdbFrames.Blackwell

/-!
# corr-general-object — T19(c): the Blackwell clause, settled both ways (repair round 1)

The mandate's T19(c) asks whether `procureValue` is monotone in the Blackwell order for fixed
`Q`. Two answers, over `lit-ddb-frames`' `Experiment`/`BlackwellLE` (Blackwell 1953):

* **Refuted as stated.** The push is a *labelled* signal — the modification is forced on
  "push", not on "no push". Relabelling the binary experiment, `k' = 1 − k`, is a garbling in
  both directions (Blackwell-equivalent), yet it changes which worlds are forced to `πQ`: on
  Example A the relabelling of `k₇ = (0, 1, 0)` takes `procureValue` from `3` to `0`
  (`procureValue_not_blackwell_monotone`). So `procureValue` is not a function of the Blackwell
  class of the push experiment at all, and monotonicity in the (unlabelled) order fails.
* **Proved for label-preserving garblings.** If `k = (p − q) k' + q` with `0 ≤ q ≤ p ≤ 1` — the
  garbled push fires with probability `p` when the original fires and `q` when it does not, so
  "push" stays "push" — then `pushExperiment k ≤_B pushExperiment k'` and
  `procureValue P k V πQ ≤ procureValue P k' V πQ` (`procureValue_blackwell_monotone_labelled`).
  The proof is one identity: `M(k)` is the convex combination
  `(1−p)·E_P[V a*] + (p−q)·[off_{k'}(V a*) + push_{k'}(V πQ)] + q·E_P[V πQ]` of three
  quantities each `≤ max(U, M(k'))` (`modifiedValue_le_max_of_garble`). The sign-reversing
  garblings (`p < q`) are exactly what this proof does not cover, and the refutation shows it
  cannot.

`resistanceValue` is monotone in neither direction (a less informative push that fires more
often is resisted more: on `Ω = {θ₁, θ₂}`, `P` uniform, `V a = (10, 10)`, `V πQ = (0, 0)`,
the garblings `(q, p)` of the perfect push `(0, 1)` have `R = 5(p + q)`); not formalized.

Sources: mandate T19(c) (extension tier); [[general-object-final]] D8, Open problem 10;
findings F-22; `lit-ddb-frames` `Experiment`, `Stochastic`, `IsGarbling`, `BlackwellLE`.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.LitDdbFrames
  Cleanroom.Found.LitDdbFrames.Blackwell
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]

/-! ## The push as a binary experiment -/

/-- The push as a binary experiment: signal `true` = "the push fires", with likelihood `k ω`.
Source: mandate T19(c); [[general-object-final]] D4; `lit-ddb-frames` `Experiment`
Kind: D
Fidelity: exact -/
def pushExperiment (k : Ω → ℝ) (hk : IsKernel k) : Experiment Ω Bool where
  k ω s := if s then k ω else 1 - k ω
  k_mem ω := by
    refine ⟨fun s => ?_, ?_⟩
    · cases s <;> simp <;> linarith [(hk ω).1, (hk ω).2]
    · simp [Fintype.sum_bool]

/-- The binary channel `g true = (p, 1 − p)`, `g false = (q, 1 − q)`: a fired push is reported
as fired with probability `p`, a silent one with probability `q`.
Source: none: infrastructure (Blackwell 1953, binary garblings)
Kind: D
Fidelity: exact -/
def binaryChannel (p q : ℝ) : Bool → Bool → ℝ :=
  fun s t => if s then (if t then p else 1 - p) else (if t then q else 1 - q)

/-- The binary channel is stochastic for `p, q ∈ [0, 1]`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem binaryChannel_stochastic {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : Stochastic (binaryChannel p q) := by
  intro s
  refine ⟨fun t => ?_, ?_⟩
  · cases s <;> cases t <;> simp [binaryChannel] <;> linarith
  · cases s <;> simp [binaryChannel, Fintype.sum_bool]

/-- **The garbled push is Blackwell-below the original**: if `k = (p − q) k' + q` with
`p, q ∈ [0, 1]`, then `pushExperiment k` is the garbling of `pushExperiment k'` through the
binary channel `(p, q)` — `BlackwellLE (pushExperiment k) (pushExperiment k')`.
Source: none: infrastructure (Blackwell 1953); mandate T19(c)
Kind: L
Fidelity: exact -/
theorem blackwellLE_pushExperiment_of_garble {k' k : Ω → ℝ} (hk' : IsKernel k') (hk : IsKernel k)
    {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : ∀ ω, k ω = (p - q) * k' ω + q) :
    BlackwellLE (pushExperiment k hk) (pushExperiment k' hk') := by
  refine ⟨binaryChannel p q, binaryChannel_stochastic hp0 hp1 hq0 hq1, ?_⟩
  intro ω t
  cases t <;> simp [pushExperiment, binaryChannel, Fintype.sum_bool, h ω] <;> ring

/-! ## The label-preserving clause, proved -/

/-- **`M(k)` under a label-preserving garbling is a convex combination** of `E_P[V a*]`,
`off_{k'}(V a*) + push_{k'}(V πQ)` and `E_P[V πQ]` with weights `1 − p`, `p − q`, `q` (where
`a*` is the off-cell maximiser for `k`), hence `M(k) ≤ max(U, M(k'))`.
Source: mandate T19(c); repair round 1
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q ≤ p ≤ 1`, `k = (p − q) k' + q` -/
theorem modifiedValue_le_max_of_garble (P : Distr Ω) (V : A → Ω → ℝ) (πQ : A) (k' k : Ω → ℝ)
    {p q : ℝ} (hq0 : 0 ≤ q) (hqp : q ≤ p) (hp1 : p ≤ 1) (h : ∀ ω, k ω = (p - q) * k' ω + q) :
    modifiedValue P k V πQ ≤ max (priorValue P V) (modifiedValue P k' V πQ) := by
  obtain ⟨a, _, ha⟩ := exists_max_image univ (fun a => offExpect P k (V a)) univ_nonempty
  have hsup : univ.sup' univ_nonempty (fun b => offExpect P k (V b)) = offExpect P k (V a) :=
    le_antisymm (sup'_le _ _ fun b hb => ha b hb)
      (le_sup' (fun b => offExpect P k (V b)) (mem_univ a))
  have hM : modifiedValue P k V πQ = offExpect P k (V a) + pushExpect P k (V πQ) := by
    unfold modifiedValue; rw [hsup]
  have key : offExpect P k (V a) + pushExpect P k (V πQ) =
      (1 - p) * expect P (V a) +
        (p - q) * (offExpect P k' (V a) + pushExpect P k' (V πQ)) + q * expect P (V πQ) := by
    unfold offExpect pushExpect expect
    simp only [mul_sum, mul_add, ← sum_add_distrib]
    exact sum_congr rfl fun ω _ => by rw [h ω]; ring
  have h1 : expect P (V a) ≤ priorValue P V := le_sup' (fun b => expect P (V b)) (mem_univ a)
  have h2 : expect P (V πQ) ≤ priorValue P V := le_sup' (fun b => expect P (V b)) (mem_univ πQ)
  have h3 : offExpect P k' (V a) + pushExpect P k' (V πQ) ≤ modifiedValue P k' V πQ := by
    unfold modifiedValue
    exact add_le_add (le_sup' (fun b => offExpect P k' (V b)) (mem_univ a)) le_rfl
  have hm1 : expect P (V a) ≤ max (priorValue P V) (modifiedValue P k' V πQ) :=
    le_trans h1 (le_max_left _ _)
  have hm2 : offExpect P k' (V a) + pushExpect P k' (V πQ) ≤
      max (priorValue P V) (modifiedValue P k' V πQ) := le_trans h3 (le_max_right _ _)
  have hm3 : expect P (V πQ) ≤ max (priorValue P V) (modifiedValue P k' V πQ) :=
    le_trans h2 (le_max_left _ _)
  rw [hM, key]
  have e1 := mul_le_mul_of_nonneg_left hm1 (by linarith : (0 : ℝ) ≤ 1 - p)
  have e2 := mul_le_mul_of_nonneg_left hm2 (by linarith : (0 : ℝ) ≤ p - q)
  have e3 := mul_le_mul_of_nonneg_left hm3 hq0
  linarith

/-- **`procureValue` is monotone under label-preserving garblings**: `k = (p − q) k' + q` with
`0 ≤ q ≤ p ≤ 1` gives `procureValue P k V πQ ≤ procureValue P k' V πQ` (if `M(k) ≤ U` the
left side is `0`; otherwise `M(k) ≤ M(k')`).
Source: mandate T19(c); repair round 1
Kind: C
Fidelity: exact
Hyps: (a) `0 ≤ q ≤ p ≤ 1`, `k = (p − q) k' + q` -/
theorem procureValue_le_of_garble (P : Distr Ω) (V : A → Ω → ℝ) (πQ : A) (k' k : Ω → ℝ)
    {p q : ℝ} (hq0 : 0 ≤ q) (hqp : q ≤ p) (hp1 : p ≤ 1) (h : ∀ ω, k ω = (p - q) * k' ω + q) :
    procureValue P k V πQ ≤ procureValue P k' V πQ := by
  have hle := modifiedValue_le_max_of_garble P V πQ k' k hq0 hqp hp1 h
  unfold procureValue
  rcases le_max_iff.1 hle with h1 | h1
  · rw [max_eq_left (by linarith)]; exact le_max_left _ _
  · exact max_le_max le_rfl (by linarith)

/-- **T19(c), the label-preserving Blackwell clause (proved)**: for kernels `k = (p − q) k' + q`
with `0 ≤ q ≤ p ≤ 1`, the garbled push is Blackwell-below the original *and* the procurement
value is monotone, `procureValue P k V πQ ≤ procureValue P k' V πQ`.
Source: mandate T19(c) ("`procureValue` is monotone in the Blackwell order for fixed `Q`");
[[general-object-final]] Open problem 10; repair round 1
Kind: C
Fidelity: variant: the Blackwell order restricted to label-preserving binary garblings
(`p ≥ q`); the unrestricted clause is refuted (`procureValue_not_blackwell_monotone`)
Hyps: (a) `IsKernel k'`, `IsKernel k`, `0 ≤ q ≤ p ≤ 1`, `k = (p − q) k' + q` -/
theorem procureValue_blackwell_monotone_labelled (P : Distr Ω) (V : A → Ω → ℝ) (πQ : A)
    {k' k : Ω → ℝ} (hk' : IsKernel k') (hk : IsKernel k) {p q : ℝ} (hq0 : 0 ≤ q) (hqp : q ≤ p)
    (hp1 : p ≤ 1) (h : ∀ ω, k ω = (p - q) * k' ω + q) :
    BlackwellLE (pushExperiment k hk) (pushExperiment k' hk') ∧
      procureValue P k V πQ ≤ procureValue P k' V πQ :=
  ⟨blackwellLE_pushExperiment_of_garble hk' hk (le_trans hq0 hqp) hp1 hq0 (le_trans hqp hp1) h,
    procureValue_le_of_garble P V πQ k' k hq0 hqp hp1 h⟩

/-! ## The unrestricted clause, refuted on Example A -/

/-- The relabelling of Example A's `k₇ = (0, 1, 0)`: `k₇' = 1 − k₇ = (1, 0, 1)`.
Source: mandate T19(c); repair round 1. Kind: D. Fidelity: exact -/
def exA_k7' : Fin 3 → ℝ := ![1, 0, 1]

/-- `k₇'` is a kernel. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem exA_k7'_isKernel : IsKernel exA_k7' := fun ω => by fin_cases ω <;> norm_num [exA_k7']

/-- `k₇' = (0 − 1) k₇ + 1`: the relabelling is the garbling `(p, q) = (0, 1)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem exA_k7'_eq (ω : Fin 3) : exA_k7' ω = (0 - 1) * exA_k7 ω + 1 := by
  fin_cases ω <;> simp [exA_k7', exA_k7]

/-- `k₇ = (0 − 1) k₇' + 1`: and back. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem exA_k7_eq (ω : Fin 3) : exA_k7 ω = (0 - 1) * exA_k7' ω + 1 := by
  fin_cases ω <;> simp [exA_k7', exA_k7]

/-- Under the relabelled push `M = 1 < U = 4`, so `procureValue = 0` (off-cell best `5/2` at
`plan₂` on `{θ₂}`, push term `−3/2`).
Source: mandate T19(c); repair round 1. Kind: L. Fidelity: exact -/
theorem exA_k7'_procure :
    procureValue exA_P exA_k7' exA_V 1 = 0 ∧ modifiedValue exA_P exA_k7' exA_V 1 = 1 := by
  have hoff : (univ : Finset (Fin 3)).sup' univ_nonempty
      (fun a => offExpect exA_P exA_k7' (exA_V a)) = 5/2 := by
    rw [sup'_fin3]; simp [offExpect, exA_P, exA_k7', exA_V, Fin.sum_univ_three]; norm_num [max_def]
  have hπ : pushExpect exA_P exA_k7' (exA_V 1) = -3/2 := by
    simp [pushExpect, exA_P, exA_k7', exA_V, Fin.sum_univ_three]; norm_num
  have hM : modifiedValue exA_P exA_k7' exA_V 1 = 1 := by
    unfold modifiedValue; rw [hoff, hπ]; norm_num
  refine ⟨?_, hM⟩
  unfold procureValue; rw [exA_priorValue, hM]; norm_num

/-- **T19(c) as stated is refuted**: on Example A the pushes `k₇ = (0, 1, 0)` and its
relabelling `k₇' = (1, 0, 1)` are Blackwell-equivalent (each a garbling of the other through the
channel `(p, q) = (0, 1)`), yet `procureValue` is `3` for `k₇` and `0` for `k₇'`. So
`procureValue` is not monotone — not even a function of the Blackwell class — in the
unlabelled Blackwell order; the labelled (`p ≥ q`) clause is what holds
(`procureValue_blackwell_monotone_labelled`).
Source: mandate T19(c) ("`procureValue` is monotone in the Blackwell order for fixed `Q`");
findings F-22; repair round 1
Kind: N+
Fidelity: exact (refutation of the unrestricted clause)
Hyps: (a) none -/
theorem procureValue_not_blackwell_monotone :
    BlackwellLE (pushExperiment exA_k7 exA_kernels.2.2.2.2.2)
        (pushExperiment exA_k7' exA_k7'_isKernel) ∧
      BlackwellLE (pushExperiment exA_k7' exA_k7'_isKernel)
        (pushExperiment exA_k7 exA_kernels.2.2.2.2.2) ∧
      procureValue exA_P exA_k7' exA_V 1 < procureValue exA_P exA_k7 exA_V 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact blackwellLE_pushExperiment_of_garble exA_k7'_isKernel exA_kernels.2.2.2.2.2 le_rfl
      zero_le_one zero_le_one le_rfl exA_k7_eq
  · exact blackwellLE_pushExperiment_of_garble exA_kernels.2.2.2.2.2 exA_k7'_isKernel le_rfl
      zero_le_one zero_le_one le_rfl exA_k7'_eq
  · rw [exA_k7'_procure.1, exA_k7_procure.2]; norm_num

/-! ## The labelled clause, strict on Example A (audit r2 adversarial 3.1)

`procureValue_blackwell_monotone_labelled` has trivially satisfiable hypotheses (`p = 1, q = 0`
is `k = k'`), so STANDARDS §3 does not require a witness; but no declaration above inhabits it
with `p < 1`, and the refutation inhabits the *opposite* hypothesis (`p = 0 < q = 1`). The
`(p, q) = (1/2, 0)`-garbling of `k₇ = (0, 1, 0)` is `(0, 1/2, 0)`: Blackwell-below `k₇` through
the theorem, with `procureValue` dropping from `3` to `3/2`. -/

/-- The `(p, q) = (1/2, 0)`-garbling of `k₇`: `k₇ᵍ = (0, 1/2, 0)`. Source: audit r2 adversarial
probe `GarbleStrict.lean`. Kind: D. Fidelity: exact -/
def exA_k7g : Fin 3 → ℝ := ![0, 1/2, 0]

/-- `k₇ᵍ` is a kernel. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem exA_k7g_isKernel : IsKernel exA_k7g := fun ω => by fin_cases ω <;> norm_num [exA_k7g]

/-- `k₇ᵍ = (1/2 − 0) k₇ + 0`: the label-preserving garbling with `(p, q) = (1/2, 0)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem exA_k7g_eq (ω : Fin 3) : exA_k7g ω = (1/2 - 0) * exA_k7 ω + 0 := by
  fin_cases ω <;> simp [exA_k7g, exA_k7]

/-- Under the garbled push `M = 11/2` (off-cell best `17/4` at `plan₁`, push term `5/4`), so
`procureValue = 3/2`. Source: audit r2 adversarial probe. Kind: L. Fidelity: exact -/
theorem exA_k7g_procure : procureValue exA_P exA_k7g exA_V 1 = 3/2 := by
  have hoff : (univ : Finset (Fin 3)).sup' univ_nonempty
      (fun a => offExpect exA_P exA_k7g (exA_V a)) = 17/4 := by
    rw [sup'_fin3]; simp [offExpect, exA_P, exA_k7g, exA_V, Fin.sum_univ_three]; norm_num [max_def]
  have hπ : pushExpect exA_P exA_k7g (exA_V 1) = 5/4 := by
    simp [pushExpect, exA_P, exA_k7g, exA_V, Fin.sum_univ_three]; norm_num
  have hM : modifiedValue exA_P exA_k7g exA_V 1 = 11/2 := by
    unfold modifiedValue; rw [hoff, hπ]; norm_num
  unfold procureValue; rw [exA_priorValue, hM]; norm_num

/-- **N+ for the labelled clause**, strict with `p < 1`: through
`procureValue_blackwell_monotone_labelled` at `(p, q) = (1/2, 0)`, the garbled push `k₇ᵍ` is
Blackwell-below `k₇` and `procureValue` drops from `3` to `3/2` — the inequality is strict and
both sides positive, so the theorem is live beyond its trivial instances.
Source: mandate T19(c); audit r2 adversarial 3.1 (`audit-r2-probes/GarbleStrict.lean`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem procureValue_garble_strict :
    BlackwellLE (pushExperiment exA_k7g exA_k7g_isKernel)
        (pushExperiment exA_k7 exA_kernels.2.2.2.2.2) ∧
      procureValue exA_P exA_k7g exA_V 1 ≤ procureValue exA_P exA_k7 exA_V 1 ∧
      procureValue exA_P exA_k7g exA_V 1 = 3/2 ∧ procureValue exA_P exA_k7 exA_V 1 = 3 := by
  have h := procureValue_blackwell_monotone_labelled exA_P exA_V 1 exA_kernels.2.2.2.2.2
    exA_k7g_isKernel (p := 1/2) (q := 0) le_rfl (by norm_num) (by norm_num) exA_k7g_eq
  exact ⟨h.1, h.2, exA_k7g_procure, exA_k7_procure.2⟩

end

end Cleanroom.Corrigibility.CorrGeneralObject
