import Cleanroom.Udt.UdtCommTrust.Prob

/-!
# `Cleanroom.Udt.UdtCommTrust.Count`: integer-weight distributions and counting

Work package `udt-comm-trust`, witness infrastructure. A witness distribution is given by
positive integer weights `wt : Ω → ℕ` summing to `N`; its mass on an event is `cnt E / N` where
`cnt E = ∑ ω ∈ E, wt ω` is a natural number that `decide` can evaluate on `Fin`-carriers. Every
numeric check on a witness (a product identity, an equality or a strict inequality of conditional
expectations or probabilities) is reduced here to a statement about counts, proved by `decide`, and
lifted to `ℝ` once. No `native_decide`.
-/

namespace Cleanroom.Udt.UdtCommTrust

open Cleanroom.Udt.UdtPolicyCalc Finset

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- **Integer weights**: positive natural weights with total `N`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
structure IntWeights (Ω : Type) [Fintype Ω] where
  /-- The weights. -/
  wt : Ω → ℕ
  /-- All positive (the carrier is the support). -/
  pos : ∀ ω, 0 < wt ω
  /-- The total. -/
  N : ℕ
  /-- The weights sum to the total. -/
  sum_eq : ∑ ω, wt ω = N

namespace IntWeights

variable (W : IntWeights Ω)

/-- Supporting lemma `N_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem N_pos [Nonempty Ω] : 0 < W.N := by
  rw [← W.sum_eq]
  exact Finset.sum_pos (fun ω _ => W.pos ω) Finset.univ_nonempty

/-- The count of an event: the sum of its weights.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def cnt (E : Finset Ω) : ℕ := ∑ ω ∈ E, W.wt ω

/-- The real weight `wt ω / N`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def w (ω : Ω) : ℝ := (W.wt ω : ℝ) / W.N

/-- The distribution with weights `wt ω / N`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def dist [Nonempty Ω] : FinDist Ω where
  w := W.w
  nonneg ω := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  sum_one := by
    unfold w
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Nat.cast_sum, W.sum_eq, mul_inv_cancel₀]
    exact_mod_cast W.N_pos.ne'

/-- Supporting lemma `w_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem w_pos [Nonempty Ω] (ω : Ω) : 0 < W.w ω :=
  div_pos (by exact_mod_cast W.pos ω) (by exact_mod_cast W.N_pos)

/-- Supporting lemma `dist_w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem dist_w [Nonempty Ω] : W.dist.w = W.w := rfl

/-- **Mass is count over total.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_eq_cnt (E : Finset Ω) : mass W.w E = (W.cnt E : ℝ) / W.N := by
  unfold mass w cnt
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, Nat.cast_sum]

/-- Supporting lemma `cnt_pos_iff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cnt_pos_iff (E : Finset Ω) : 0 < W.cnt E ↔ E.Nonempty := by
  constructor
  · intro h
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp [cnt] at h
  · intro h
    exact Finset.sum_pos (fun ω _ => W.pos ω) h

/-- Supporting lemma `cnt_ne_zero_of_nonempty`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cnt_ne_zero_of_nonempty {E : Finset Ω} (h : E.Nonempty) : W.cnt E ≠ 0 :=
  ((W.cnt_pos_iff E).2 h).ne'

/-- Supporting lemma `nonempty_of_cnt_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem nonempty_of_cnt_pos {E : Finset Ω} (h : 0 < W.cnt E) : E.Nonempty := (W.cnt_pos_iff E).1 h

/-- **A product identity of masses from a product identity of counts.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_mul_eq_of_cnt {A B C D : Finset Ω} (h : W.cnt A * W.cnt B = W.cnt C * W.cnt D) :
    mass W.w A * mass W.w B = mass W.w C * mass W.w D := by
  rw [mass_eq_cnt, mass_eq_cnt, mass_eq_cnt, mass_eq_cnt, div_mul_div_comm, div_mul_div_comm]
  congr 1
  exact_mod_cast h

/-- **Equality of junk conditional probabilities from counts** (both conditioning events
non-empty).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condProbJunk_eq_of_cnt [Nonempty Ω] {E F E' F' : Finset Ω} (hF : F.Nonempty)
    (hF' : F'.Nonempty) (h : W.cnt (E ∩ F) * W.cnt F' = W.cnt (E' ∩ F') * W.cnt F) :
    condProbJunk W.w E F 0 = condProbJunk W.w E' F' 0 := by
  rw [condProbJunk_of_nonempty W.w_pos hF, condProbJunk_of_nonempty W.w_pos hF', mass_eq_cnt,
    mass_eq_cnt, mass_eq_cnt, mass_eq_cnt, div_div_div_cancel_right₀ (by exact_mod_cast W.N_pos.ne'),
    div_div_div_cancel_right₀ (by exact_mod_cast W.N_pos.ne'),
    div_eq_div_iff (by exact_mod_cast W.cnt_ne_zero_of_nonempty hF)
      (by exact_mod_cast W.cnt_ne_zero_of_nonempty hF')]
  exact_mod_cast h

/-- **A `{0,1}`-valued utility's conditional expectation is a ratio of counts**: for
`U = 1_Q`, `E[U ∣ E] = cnt (E ∩ Q) / cnt E` on a non-empty `E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpJunk_indicator [Nonempty Ω] (Q : Ω → Prop) [DecidablePred Q] {E : Finset Ω}
    (hE : E.Nonempty) (j : ℝ) :
    condExpJunk W.w (fun ω => if Q ω then (1 : ℝ) else 0) E j =
      (W.cnt (E.filter Q) : ℝ) / W.cnt E := by
  rw [condExpJunk_of_pos (mass_pos_of_nonempty W.w_pos hE), mass_eq_cnt]
  have : ∑ ω ∈ E, W.w ω * (if Q ω then (1 : ℝ) else 0) = (W.cnt (E.filter Q) : ℝ) / W.N := by
    rw [← mass_eq_cnt, mass, Finset.sum_filter]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs <;> simp
  rw [this, div_div_div_cancel_right₀ (by exact_mod_cast W.N_pos.ne')]

/-- **A strict inequality of indicator conditional expectations from counts.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpJunk_indicator_lt [Nonempty Ω] (Q : Ω → Prop) [DecidablePred Q] {E F : Finset Ω}
    (hE : E.Nonempty) (hF : F.Nonempty)
    (h : W.cnt (E.filter Q) * W.cnt F < W.cnt (F.filter Q) * W.cnt E) (j : ℝ) :
    condExpJunk W.w (fun ω => if Q ω then (1 : ℝ) else 0) E j <
      condExpJunk W.w (fun ω => if Q ω then (1 : ℝ) else 0) F j := by
  rw [W.condExpJunk_indicator Q hE, W.condExpJunk_indicator Q hF,
    div_lt_div_iff₀ (by exact_mod_cast (W.cnt_pos_iff E).2 hE)
      (by exact_mod_cast (W.cnt_pos_iff F).2 hF)]
  exact_mod_cast h

/-- **An equality of indicator conditional expectations from counts.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpJunk_indicator_eq [Nonempty Ω] (Q : Ω → Prop) [DecidablePred Q] {E F : Finset Ω}
    (hE : E.Nonempty) (hF : F.Nonempty)
    (h : W.cnt (E.filter Q) * W.cnt F = W.cnt (F.filter Q) * W.cnt E) (j : ℝ) :
    condExpJunk W.w (fun ω => if Q ω then (1 : ℝ) else 0) E j =
      condExpJunk W.w (fun ω => if Q ω then (1 : ℝ) else 0) F j := by
  rw [W.condExpJunk_indicator Q hE, W.condExpJunk_indicator Q hF,
    div_eq_div_iff (by exact_mod_cast W.cnt_ne_zero_of_nonempty hE)
      (by exact_mod_cast W.cnt_ne_zero_of_nonempty hF)]
  exact_mod_cast h

/-- **Two masses are equal iff the counts are.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_eq_of_cnt {A B : Finset Ω} (h : W.cnt A = W.cnt B) : mass W.w A = mass W.w B := by
  rw [mass_eq_cnt, mass_eq_cnt, h]

/-- **`mass = 1` from `cnt = N`.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_eq_one_of_cnt [Nonempty Ω] {A : Finset Ω} (h : W.cnt A = W.N) : mass W.w A = 1 := by
  rw [mass_eq_cnt, h, div_self]
  exact_mod_cast W.N_pos.ne'

end IntWeights

/-- Supporting lemma `event_congr`: two events with pointwise-equivalent predicates are equal
(whatever their decidability instances).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem event_congr {P Q : Ω → Prop} [DecidablePred P] [DecidablePred Q] (h : ∀ ω, P ω ↔ Q ω) :
    event P = event Q := Finset.filter_congr fun ω _ => h ω

end Cleanroom.Udt.UdtCommTrust
