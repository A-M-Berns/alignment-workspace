import Cleanroom.Found.LitDdbFrames.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# The finite collapse: conditional martingales force immodesty; mutual trust collapses two experts

Package `tt-finite-frames`, Targets I1 and I3 (I2, the soft ⟹ hard step, is `SoftCollapse.lean`).

* **I1** (hard core): if the conditional-martingale identity
  `E_{P_w}(X) · π(P = P_w) = ∑_{v ∈ [P = P_w]} π v X v` holds at a world `w` with `π w > 0` for
  every `X`, the expert is immodest there: `P_w(P = P_w) = 1`. Instantiate the cell's indicator.
* **I3** (the "size problem"): two experts `P, Q` on one frame that conditionally-martingale
  toward each other at every world (reading R1: `Q_w` is `P_w` conditioned on `Q`'s cell, and
  symmetrically) coincide, `P = Q`, and both are immodest. Under the weaker reading R2 — each
  expert merely certain of the other's cell — the partitions coincide and both are immodest, but
  `P = Q` fails (witness on `Fin 3`). So the lab's critique is right that S5 alone gives no common
  partition, and the cross-condition does; "into one" is exact under R1, false under R2.
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## I1: the hard core -/

/-- The **conditional-martingale identity at `w`** for a deferrer `π` and frame `F`: for every
`X`, `E_{P_w}(X) · π(P = P_w) = ∑_{v ∈ [P = P_w]} π v X v` — in product form, `P_w` is `π`
conditioned on `w`'s own cell.
Source: [[deference-in-logical-induction-v6]] §2.2; lean-deference-005 `CM_implies_immodest`
(its `hCM`, product form)
Kind: D
Fidelity: exact (product form of the source's ratio hypothesis) -/
def CondMartingaleAt (π : W → ℝ) (F : Frame W) (w : W) : Prop :=
  ∀ X : W → ℝ, E (F.P w) X * mass π (F.cell (F.P w)) = ∑ v ∈ F.cell (F.P w), π v * X v

/-- The identity at the indicator of a single world `v`: `P_w v · π(P = P_w) = 𝟙[v ∈ cell] π v`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CondMartingaleAt.apply_single {π : W → ℝ} {F : Frame W} {w : W}
    (h : CondMartingaleAt π F w) (v : W) :
    F.P w v * mass π (F.cell (F.P w)) = if v ∈ F.cell (F.P w) then π v else 0 := by
  have := h (ind {v})
  rw [E_ind] at this
  have hm : mass (F.P w) {v} = F.P w v := by simp [mass]
  rw [hm] at this
  rw [this]
  split_ifs with hv
  · rw [sum_eq_single v]
    · simp [ind]
    · intro b _ hb; simp [ind, hb]
    · intro hnot; exact absurd hv hnot
  · apply sum_eq_zero
    intro b hb
    have : b ≠ v := fun e => hv (e ▸ hb)
    simp [ind, this]

/-- The identity at the cell's indicator: `P_w(P = P_w) · π(P = P_w) = π(P = P_w)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CondMartingaleAt.apply_cell {π : W → ℝ} {F : Frame W} {w : W}
    (h : CondMartingaleAt π F w) :
    F.selfMass (F.P w) * mass π (F.cell (F.P w)) = mass π (F.cell (F.P w)) := by
  have := h (ind (F.cell (F.P w)))
  rw [E_ind] at this
  rw [Frame.selfMass, this]
  unfold mass
  apply sum_congr rfl
  intro v hv
  simp [ind, hv]

/-- Immodesty at `w` from the conditional martingale, given that `w`'s cell has positive `π`-mass.
Source: none: infrastructure (the engine of I1 and I3)
Kind: L
Fidelity: n/a -/
theorem CondMartingaleAt.selfMass_eq_one_of_mass_pos {π : W → ℝ} {F : Frame W} {w : W}
    (hm : 0 < mass π (F.cell (F.P w))) (h : CondMartingaleAt π F w) :
    F.selfMass (F.P w) = 1 :=
  mul_right_cancel₀ hm.ne' (by rw [h.apply_cell, one_mul])

/-- **I1. A conditional martingale at a world forces immodesty there.** If `π w > 0` and the
conditional-martingale identity holds at `w` for every `X`, then `P_w(P = P_w) = 1`: instantiate
`X = 𝟙[P = P_w]`, giving `P_w(P = P_w) · π(P = P_w) = π(P = P_w)`, and `π(P = P_w) ≠ 0` because
the identity at `𝟙_{w}` reads `P_w w · π(P = P_w) = π w > 0`. No sign condition on `π` off `w`
is needed.
Source: lean-deference-005 `CM_implies_immodest`; root-deference-011 (hard core);
vq-wiki-027 (b); [[deference-in-logical-induction-v6]] §2.2
Kind: P (easy)
Fidelity: exact
Hyps: (a) `hw : 0 < π w`, `hCM` (the identity) -/
theorem CondMartingaleAt.selfMass_eq_one {π : W → ℝ} {F : Frame W} {w : W} (hw : 0 < π w)
    (hCM : CondMartingaleAt π F w) : F.selfMass (F.P w) = 1 := by
  apply hCM.selfMass_eq_one_of_mass_pos
  rcases lt_or_ge 0 (mass π (F.cell (F.P w))) with h | h
  · exact h
  · exfalso
    have h1 := hCM.apply_single w
    rw [if_pos (F.mem_cell_self w)] at h1
    have h2 : F.P w w * mass π (F.cell (F.P w)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (F.P_nonneg w w) h
    linarith

/-- **I1, corollary.** A conditional martingale at every world of the support makes the frame
immodest on the support.
Source: lean-deference-005; root-deference-011
Kind: L
Fidelity: exact -/
theorem immodest_on_supp_of_condMartingale {π : W → ℝ} {F : Frame W}
    (h : ∀ w, 0 < π w → CondMartingaleAt π F w) : ∀ w ∈ supp π, F.selfMass (F.P w) = 1 :=
  fun w hw => (h w (by simpa [supp] using hw)).selfMass_eq_one (by simpa [supp] using hw)

/-! ## I3: mutual conditional-martingale trust collapses two experts into one -/

/-- **Reading R1**: expert `Q` conditionally-martingales toward expert `P` at `w` when
`P_w(Q = Q_w) > 0` and `Q_w` is `P_w` conditioned on `Q`'s cell at `w`, in product form
`∀ X, E_{Q_w}(X) · P_w(Q = Q_w) = ∑_{v ∈ [Q = Q_w]} P_w v X v`. This is I1's shape with `P_w`
in the deferrer's place. ATTRIBUTION-UNVETTED as the reading of trust-lab-006's "soft
conditional-martingale toward each other".
Source: trust-lab-006 ([[lateral]] §3.2 conjecture box), read through lean-deference-005
Kind: D
Fidelity: variant: reading R1 of the source's informal condition -/
def CMToward (Q P : Frame W) (w : W) : Prop :=
  0 < mass (P.P w) (Q.cell (Q.P w)) ∧ CondMartingaleAt (P.P w) Q w

/-- Under R1 at `w`, `Q` is immodest at `w` (I1 with `π := P_w`).
Source: trust-lab-006 (the step "by 005 both are immodest")
Kind: L
Fidelity: n/a -/
theorem CMToward.selfMass_eq_one {Q P : Frame W} {w : W} (h : CMToward Q P w) :
    Q.selfMass (Q.P w) = 1 :=
  h.2.selfMass_eq_one_of_mass_pos h.1

/-- Under R1 at `w`, `Q_w` vanishes off `Q`'s cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CMToward.eq_zero_of_notMem {Q P : Frame W} {w : W} (h : CMToward Q P w) {v : W}
    (hv : v ∉ Q.cell (Q.P w)) : Q.P w v = 0 := by
  have := h.2.apply_single v
  rw [if_neg hv] at this
  exact (mul_eq_zero.1 this).resolve_right h.1.ne'

/-- Under R1 at `w`, on `Q`'s cell `Q_w v · P_w(Q = Q_w) = P_w v`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CMToward.mul_mass_eq {Q P : Frame W} {w : W} (h : CMToward Q P w) {v : W}
    (hv : v ∈ Q.cell (Q.P w)) : Q.P w v * mass (P.P w) (Q.cell (Q.P w)) = P.P w v := by
  have := h.2.apply_single v
  rwa [if_pos hv] at this

/-- Under R1 at `w`, a world `Q_w` gives positive probability lies in `Q`'s cell and gets positive
`P_w`-probability.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CMToward.mem_and_pos_of_pos {Q P : Frame W} {w : W} (h : CMToward Q P w) {v : W}
    (hv : 0 < Q.P w v) : v ∈ Q.cell (Q.P w) ∧ 0 < P.P w v := by
  have hmem : v ∈ Q.cell (Q.P w) := by
    by_contra hnot
    have := h.eq_zero_of_notMem hnot
    linarith
  refine ⟨hmem, ?_⟩
  rw [← h.mul_mass_eq hmem]
  exact mul_pos hv h.1

/-- **I3, reading R1 (the "size problem", resolved).** If two experts on one frame
conditionally-martingale toward each other at every world, they coincide — `P = Q` as frames'
rows — and both are immodest. The argument: each is immodest by I1; `supp Q_w ⊆ [P = P_w]` and
symmetrically (a world `Q_w` weights has positive `P_w`-probability, hence lies in `P`'s cell);
if `Q_v = Q_w` then `supp Q_w` meets both `[P = P_v]` and `[P = P_w]`, so `P_v = P_w` — the
partitions coincide; and then `Q_w = P_w(· | [Q = Q_w]) = P_w(· | [P = P_w]) = P_w`.
Source: trust-lab-006 (conjecture; its critique flagged the "common partition" step as unargued —
this supplies the cross-condition argument)
Kind: P
Fidelity: variant: reading R1 of the source's informal mutual soft trust (the finite hard form;
the soft ⟹ hard step is I2)
Hyps: (a) `hQP`, `hPQ` (mutual R1 at every world) -/
theorem mutual_cmToward_eq {P Q : Frame W} (hQP : ∀ w, CMToward Q P w)
    (hPQ : ∀ w, CMToward P Q w) : P.P = Q.P ∧ P.Immodest ∧ Q.Immodest := by
  -- support inclusions
  have hsuppQ : ∀ w v, 0 < Q.P w v → P.P v = P.P w := by
    intro w v hv
    obtain ⟨_, hPv⟩ := (hQP w).mem_and_pos_of_pos hv
    obtain ⟨hmem, _⟩ := (hPQ w).mem_and_pos_of_pos hPv
    exact Frame.mem_cell.1 hmem
  have hsuppP : ∀ w v, 0 < P.P w v → Q.P v = Q.P w := by
    intro w v hv
    obtain ⟨_, hQv⟩ := (hPQ w).mem_and_pos_of_pos hv
    obtain ⟨hmem, _⟩ := (hQP w).mem_and_pos_of_pos hQv
    exact Frame.mem_cell.1 hmem
  -- the partitions coincide
  have hcell : ∀ w v, Q.P v = Q.P w → P.P v = P.P w := by
    intro w v hvw
    obtain ⟨u, hu⟩ := supp_nonempty (Q.P_mem w)
    rw [mem_supp] at hu
    have h1 := hsuppQ w u hu
    have h2 := hsuppQ v u (by rw [hvw]; exact hu)
    rw [← h2, h1]
  have hcell' : ∀ w v, P.P v = P.P w → Q.P v = Q.P w := by
    intro w v hvw
    obtain ⟨u, hu⟩ := supp_nonempty (P.P_mem w)
    rw [mem_supp] at hu
    have h1 := hsuppP w u hu
    have h2 := hsuppP v u (by rw [hvw]; exact hu)
    rw [← h2, h1]
  have hcells : ∀ w, Q.cell (Q.P w) = P.cell (P.P w) := by
    intro w
    ext v
    simp only [Frame.mem_cell]
    exact ⟨hcell w v, hcell' w v⟩
  refine ⟨?_, fun w => (hPQ w).selfMass_eq_one, fun w => (hQP w).selfMass_eq_one⟩
  funext w v
  by_cases hv : v ∈ Q.cell (Q.P w)
  · have h1 := (hQP w).mul_mass_eq hv
    have h2 : mass (P.P w) (Q.cell (Q.P w)) = 1 := by
      rw [hcells]
      exact (hPQ w).selfMass_eq_one
    rw [h2, mul_one] at h1
    exact h1.symm
  · rw [(hQP w).eq_zero_of_notMem hv]
    by_contra hne
    have hpos : 0 < P.P w v := lt_of_le_of_ne (P.P_nonneg w v) (Ne.symm hne)
    obtain ⟨hmem, _⟩ := (hPQ w).mem_and_pos_of_pos hpos
    rw [← hcells] at hmem
    exact hv hmem

/-- **Reading R2** (weaker): expert `P` is *certain of `Q`'s cell* at `w`, `P_w(Q = Q_w) = 1`.
Source: trust-lab-006 (the critique's reading: "each S5 on its own partition")
Kind: D
Fidelity: variant: reading R2, strictly weaker than R1 -/
def CertainOfCell (P Q : Frame W) (w : W) : Prop := mass (P.P w) (Q.cell (Q.P w)) = 1

/-- R1 implies R2: conditioning on a cell puts all mass on it, so `P_w(Q = Q_w) = 1` follows
from... no: R1 gives `Q_w(Q = Q_w) = 1`, i.e. `Q` certain of its *own* cell. What R1 gives
toward R2 is the support inclusion `supp Q_w ⊆ [P = P_w]` used above; R2 for `P` toward `Q` is
not a consequence of R1 for `Q` toward `P` alone. Recorded as a lemma of what R1 does give.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CMToward.certainOfCell_self {Q P : Frame W} {w : W} (h : CMToward Q P w) :
    CertainOfCell Q Q w := h.selfMass_eq_one

/-- **I3, reading R2.** If each expert is certain of the other's cell at every world, the
partitions coincide and both experts are immodest — but `P = Q` does **not** follow (see
`R2Witness`). Argument: `supp P_w ⊆ [Q = Q_w]` and `supp Q_w ⊆ [P = P_w]`; if `Q_v = Q_w` then
`supp Q_w` lies in `[P = P_v] ∩ [P = P_w]`, so `P_v = P_w`; symmetrically; immodesty is the
inclusion `supp P_w ⊆ [Q = Q_w] ⊆ [P = P_w]`.
Source: trust-lab-006 (the critique's doubt: "both S5 ⇒ common partition is unargued" — under
R2 the cross-certainty is what supplies it)
Kind: P
Fidelity: variant: reading R2
Hyps: (a) `hPQ`, `hQP` -/
theorem mutual_certainOfCell {P Q : Frame W} (hPQ : ∀ w, CertainOfCell P Q w)
    (hQP : ∀ w, CertainOfCell Q P w) :
    (∀ w, P.cell (P.P w) = Q.cell (Q.P w)) ∧ P.Immodest ∧ Q.Immodest := by
  have hsP : ∀ w v, 0 < P.P w v → Q.P v = Q.P w := fun w v hv =>
    Frame.mem_cell.1 (mem_of_mass_eq_one (P.P_mem w) (hPQ w) hv)
  have hsQ : ∀ w v, 0 < Q.P w v → P.P v = P.P w := fun w v hv =>
    Frame.mem_cell.1 (mem_of_mass_eq_one (Q.P_mem w) (hQP w) hv)
  have hcell : ∀ w v, Q.P v = Q.P w → P.P v = P.P w := by
    intro w v hvw
    obtain ⟨u, hu⟩ := supp_nonempty (Q.P_mem w)
    rw [mem_supp] at hu
    have h1 := hsQ w u hu
    have h2 := hsQ v u (by rw [hvw]; exact hu)
    rw [← h2, h1]
  have hcell' : ∀ w v, P.P v = P.P w → Q.P v = Q.P w := by
    intro w v hvw
    obtain ⟨u, hu⟩ := supp_nonempty (P.P_mem w)
    rw [mem_supp] at hu
    have h1 := hsP w u hu
    have h2 := hsP v u (by rw [hvw]; exact hu)
    rw [← h2, h1]
  have hcells : ∀ w, P.cell (P.P w) = Q.cell (Q.P w) := by
    intro w
    ext v
    simp only [Frame.mem_cell]
    exact ⟨hcell' w v, hcell w v⟩
  refine ⟨hcells, fun w => ?_, fun w => ?_⟩
  · rw [Frame.selfMass, hcells]; exact hPQ w
  · rw [Frame.selfMass, ← hcells]; exact hQP w

/-! ### The R2 witness: same partition, both immodest, `P ≠ Q` -/

namespace R2Witness

/-- `P`'s rows: `δ₀, δ₀, δ₂`.
Source: mandate I3 (reading R2 witness)
Kind: D
Fidelity: exact -/
def P : Frame (Fin 3) where
  P := ![![1, 0, 0], ![1, 0, 0], ![0, 0, 1]]
  P_mem := by
    intro w
    fin_cases w <;> refine ⟨fun v => ?_, ?_⟩ <;> (try fin_cases v) <;> simp [Fin.sum_univ_three]

/-- `Q`'s rows: `(1/3, 2/3, 0), (1/3, 2/3, 0), δ₂`.
Source: mandate I3 (reading R2 witness, `a = 1/3`)
Kind: D
Fidelity: exact -/
def Q : Frame (Fin 3) where
  P := ![![1 / 3, 2 / 3, 0], ![1 / 3, 2 / 3, 0], ![0, 0, 1]]
  P_mem := by
    intro w
    fin_cases w <;> refine ⟨fun v => ?_, ?_⟩ <;> (try fin_cases v) <;>
      simp [Fin.sum_univ_three] <;> norm_num

/-- The cells of both experts are `{0, 1}` at worlds `0, 1` and `{2}` at world `2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cells : P.cell (P.P 0) = {0, 1} ∧ P.cell (P.P 1) = {0, 1} ∧ P.cell (P.P 2) = {2} ∧
    Q.cell (Q.P 0) = {0, 1} ∧ Q.cell (Q.P 1) = {0, 1} ∧ Q.cell (Q.P 2) = {2} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext v <;> fin_cases v <;> simp [Frame.cell, P, Q]

/-- **The R2 witness.** `P` and `Q` are each certain of the other's cell at every world, share
the partition `{{0,1}, {2}}`, are both immodest — and differ. So mutual cell-certainty (R2) does
not collapse two experts into one; R1 does.
Source: mandate I3
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem witness : (∀ w, CertainOfCell P Q w) ∧ (∀ w, CertainOfCell Q P w) ∧ P.P ≠ Q.P := by
  obtain ⟨p0, p1, p2, q0, q1, q2⟩ := cells
  have c0 : CertainOfCell P Q 0 := by simp only [CertainOfCell]; rw [q0]; simp [mass, P]
  have c1 : CertainOfCell P Q 1 := by simp only [CertainOfCell]; rw [q1]; simp [mass, P]
  have c2 : CertainOfCell P Q 2 := by simp only [CertainOfCell]; rw [q2]; simp [mass, P]
  have d0 : CertainOfCell Q P 0 := by
    simp only [CertainOfCell]; rw [p0]; simp [mass, Q]; norm_num
  have d1 : CertainOfCell Q P 1 := by
    simp only [CertainOfCell]; rw [p1]; simp [mass, Q]; norm_num
  have d2 : CertainOfCell Q P 2 := by simp only [CertainOfCell]; rw [p2]; simp [mass, Q]
  refine ⟨fun w => ?_, fun w => ?_, ?_⟩
  · fin_cases w
    exacts [c0, c1, c2]
  · fin_cases w
    exacts [d0, d1, d2]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [P, Q] at this

end R2Witness

/-! ## Repair round 1: the self-witness, the pointwise form of I3, and reading R1′ -/

/-- Every immodest frame conditionally-martingales toward itself at every world: the self-cell
has mass one and the row vanishes off it. So the hypothesis package of `mutual_cmToward_eq` is
consistent — inhabited with `P = Q`, which is what the theorem forces; graded N− because the
witness cannot exhibit more than the conclusion allows (`T4.FA_witness` in `Witnesses.lean`
picks a non-omniscient inhabitant).
Source: none: audit r1 (fidelity N1, adversarial N2)
Kind: N−
Fidelity: n/a -/
theorem cmToward_self_of_immodest {P : Frame W} (hP : P.Immodest) (w : W) : CMToward P P w := by
  have h1 : mass (P.P w) (P.cell (P.P w)) = 1 := hP w
  refine ⟨by rw [h1]; exact one_pos, ?_⟩
  intro X
  rw [h1, mul_one]
  unfold E
  symm
  apply sum_subset (subset_univ _)
  intro v _ hv
  have : P.P w v = 0 := by
    by_contra hne
    have hpos : 0 < P.P w v := lt_of_le_of_ne (P.P_nonneg w v) (Ne.symm hne)
    exact hv (mem_of_mass_eq_one (P.P_mem w) h1 hpos)
  rw [this, zero_mul]

/-- **I3 (R1), pointwise.** Mutual R1 at a *single* world `w` already forces `P_w = Q_w`: from
`CMToward P Q w` and `CMToward Q P w`, `supp P_w ⊆ supp Q_w ⊆ [Q = Q_w]`, so `P_w(Q = Q_w) = 1`,
and the identity of `CMToward Q P w` then reads `Q_w v = P_w v` on the cell and `0 = 0` off it.
`mutual_cmToward_eq` is this at every world plus the immodesty of both.
Source: none: agenda push (the shortcut noted in audit r1 adversarial §4 at I3)
Kind: P
Fidelity: stronger: pointwise (no quantifier over worlds)
Hyps: (a) `hQP`, `hPQ` (mutual R1 at `w`) -/
theorem cmToward_mutual_eq_at {P Q : Frame W} {w : W} (hQP : CMToward Q P w)
    (hPQ : CMToward P Q w) : P.P w = Q.P w := by
  have hsub : ∀ v, 0 < P.P w v → v ∈ Q.cell (Q.P w) := fun v hv =>
    (hQP.mem_and_pos_of_pos (hPQ.mem_and_pos_of_pos hv).2).1
  have hmass : mass (P.P w) (Q.cell (Q.P w)) = 1 := by
    have h0 : ∀ v ∈ (univ : Finset W), v ∉ Q.cell (Q.P w) → P.P w v = 0 := by
      intro v _ hv
      by_contra hne
      exact hv (hsub v (lt_of_le_of_ne (P.P_nonneg w v) (Ne.symm hne)))
    rw [mass, sum_subset (subset_univ _) h0]
    exact (P.P_mem w).2
  funext v
  by_cases hv : v ∈ Q.cell (Q.P w)
  · have h1 := hQP.mul_mass_eq hv
    rw [hmass, mul_one] at h1
    exact h1.symm
  · rw [hQP.eq_zero_of_notMem hv]
    by_contra hne
    exact hv (hsub v (lt_of_le_of_ne (P.P_nonneg w v) (Ne.symm hne)))

/-- **Reading R1′** (the corpus-shaped reading; audit r1 fidelity N4): `Q` conditionally-
martingales toward `P` at every world `v` that `P_w` weights, for every `w` — what I2 (hard
indicator) makes of "the soft conditional-martingale identity for deferrer `P_w`" at every
`P_w`-supported world, not only at `v = w`. No positivity guard is needed: the identity at
`𝟙_{v}` gives `Q_v(v) · P_w(Q = Q_v) = P_w(v) > 0`. R1 and R1′ are incomparable in general
(R1 constrains `w` even when `P_w w = 0`; R1′ says nothing there).
Source: trust-lab-006 read through I2 (reading R1′; ATTRIBUTION-UNVETTED like R1)
Kind: D
Fidelity: variant: reading R1′ -/
def CMTowardSupp (Q P : Frame W) : Prop :=
  ∀ w v, 0 < P.P w v → CondMartingaleAt (P.P w) Q v

/-- Under R1′, at a world `v` that `P_w` weights: `Q_v(v) > 0` and `P_w(Q = Q_v) > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CMTowardSupp.pos_of_pos {Q P : Frame W} (h : CMTowardSupp Q P) {w v : W}
    (hv : 0 < P.P w v) : 0 < Q.P v v ∧ 0 < mass (P.P w) (Q.cell (Q.P v)) := by
  have hid := (h w v hv).apply_single v
  rw [if_pos (Q.mem_cell_self v)] at hid
  have hprod : 0 < Q.P v v * mass (P.P w) (Q.cell (Q.P v)) := by rw [hid]; exact hv
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hprod with ⟨ha, hb⟩ | ⟨ha, _⟩
  · exact ⟨ha, hb⟩
  · exact absurd ha (not_lt.2 (Q.P_nonneg v v))

/-- **I3 under R1′.** Mutual R1′ forces `P_v = Q_v` and immodesty of both at every world `v`
that some row of `P` weights — and, in general, at no other world (`R1SuppWitness.witness`).
Proof: `Q_v(v) > 0` by `pos_of_pos`, hence `P_v(v) > 0` by the symmetric clause, so R1′ at
`(v, v)` in both directions is mutual R1 at `v`, and `cmToward_mutual_eq_at` applies.
Source: trust-lab-006 (reading R1′; the open question of audit r1 fidelity N4, answered)
Kind: P
Fidelity: variant: reading R1′; the conclusion is on the union of the rows' supports
Hyps: (a) `hQP`, `hPQ` (mutual R1′), `hv` -/
theorem mutual_cmTowardSupp_eq_of_pos {P Q : Frame W} (hQP : CMTowardSupp Q P)
    (hPQ : CMTowardSupp P Q) {w v : W} (hv : 0 < P.P w v) :
    P.P v = Q.P v ∧ P.selfMass (P.P v) = 1 ∧ Q.selfMass (Q.P v) = 1 := by
  have hQv : 0 < Q.P v v := (hQP.pos_of_pos hv).1
  have hPv : 0 < P.P v v := (hPQ.pos_of_pos hQv).1
  have h1 : CMToward Q P v := ⟨(hQP.pos_of_pos hPv).2, hQP v v hPv⟩
  have h2 : CMToward P Q v := ⟨(hPQ.pos_of_pos hQv).2, hPQ v v hQv⟩
  exact ⟨cmToward_mutual_eq_at h1 h2, h2.selfMass_eq_one, h1.selfMass_eq_one⟩

namespace R1SuppWitness

/-- `P`'s rows: `δ₀, δ₁, δ₀`.
Source: none: audit r1 fidelity N4 (witness)
Kind: D
Fidelity: exact -/
def P : Frame (Fin 3) where
  P := ![![1, 0, 0], ![0, 1, 0], ![1, 0, 0]]
  P_mem := by
    intro w
    fin_cases w <;> refine ⟨fun v => ?_, ?_⟩ <;> (try fin_cases v) <;> simp [Fin.sum_univ_three]

/-- `Q`'s rows: `δ₀, δ₁, δ₁`.
Source: none: audit r1 fidelity N4 (witness)
Kind: D
Fidelity: exact -/
def Q : Frame (Fin 3) where
  P := ![![1, 0, 0], ![0, 1, 0], ![0, 1, 0]]
  P_mem := by
    intro w
    fin_cases w <;> refine ⟨fun v => ?_, ?_⟩ <;> (try fin_cases v) <;> simp [Fin.sum_univ_three]

/-- **The R1′ witness.** `P` and `Q` satisfy mutual R1′; no row of either weights world `2`;
they agree on `{0, 1}` (as `mutual_cmTowardSupp_eq_of_pos` says they must) and differ at `2`.
So R1′ says nothing off the union of the supports, the restriction in
`mutual_cmTowardSupp_eq_of_pos` is sharp, and "into one" fails under R1′ off the support.
Source: none: audit r1 fidelity N4
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem witness : CMTowardSupp Q P ∧ CMTowardSupp P Q ∧ (∀ w, P.P w 2 = 0) ∧
    (∀ w, Q.P w 2 = 0) ∧ P.P ≠ Q.P := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w v hv
    fin_cases w <;> fin_cases v <;> norm_num [P] at hv <;> intro X <;>
      simp [E, mass, Frame.cell, sum_filter, Fin.sum_univ_three, P, Q]
  · intro w v hv
    fin_cases w <;> fin_cases v <;> norm_num [Q] at hv <;> intro X <;>
      simp [E, mass, Frame.cell, sum_filter, Fin.sum_univ_three, P, Q]
  · intro w; fin_cases w <;> simp [P]
  · intro w; fin_cases w <;> simp [Q]
  · intro h
    have := congrFun (congrFun h 2) 0
    simp [P, Q] at this

end R1SuppWitness

end

end Cleanroom.Trust.TtFiniteFrames
