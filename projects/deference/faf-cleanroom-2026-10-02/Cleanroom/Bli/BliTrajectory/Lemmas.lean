import Cleanroom.Bli.BliTrajectory.Parser

/-!
# `bli-trajectory` · Lemmas: the constraint lemmas of `𝐏` (M1, F8) and the tent instance (M3)

**Every F8 row is definitional (`Kind: L`)**: these lemmas say what `bliPrice` *means* — they
unfold the parser on the constraint shape and read off the price. They are not theorems about
the sources; listing one as `P` is the area's characteristic fake ([[bli-program]] §7 item 1).
The theorems are elsewhere (`Partition.lean`, `Update.lean`, `Refutations.lean`).

Scope: `bli_cond2_scoped`/`bli_cond3_scoped`/`bli_cond3fin_scoped` carry the restriction
`NoFutureState c n φ` (Known issue 1; `Refutations.e2x_full_scope_fails` shows the full-scope
predicate is false for the tent instance). `bli_update_small` needs no restriction: a
day-`n`-small sentence mentions no future candidate atom (`noFutureState_of_smallOn`).

`M3`: `bliHistory_isBLI_scoped` collects M1; `bliHistory_tent_nonDegenerate` and
`bliHistory_tent_two_states` are the package's N+ (the tent skeleton from a base with an
interior price charges two distinct codes).
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite

open Classical

variable {𝓜 : Mesh} (c : StateCoding 𝓜) (sk : Skeleton smallIndex 𝓜.d) (Q : RatHistory)

/-! ## Rational-level readings of the price on the constraint shapes -/

/-- The price of a future candidate atom is its chain mass.
Source: [[bli-program]] §2.5
Kind: L
Fidelity: n/a -/
lemma bliPrice_stateAtom {n m q : ℕ} (hnm : n < m) (hq : q ∈ c.states m) :
    bliPrice Q 𝓜 sk c n (stateAtom m q) = chainMass sk c n (actualTable smallIndex Q n) [(m, q)] := by
  rw [bliPrice_of_tierA (not_smallOn_stateAtom c hnm hq) (tierA_stateAtom c hnm hq),
    tierAPrice_of_consistent c sk _ (consistent_singleton _), smallFactor_none, mul_one]

/-- **The superbelief is the kernel entry** (rational form): the price of the day-`(n+1)` state
atom coding a grid table `A` is `κ_n(actualTable Q n)(A)`. Uses `StateCoding.large` (the atom
misses the small case).
Source: [[bli-program]] §2.5 (`bli_state`); mandate M1
Kind: L
Fidelity: exact -/
lemma bliPrice_state (n : ℕ) {A : Table smallIndex (n + 1)} (hA : A ∈ grid smallIndex 𝓜.d (n + 1)) :
    bliPrice Q 𝓜 sk c n (stateAtom (n + 1) (c.code (n + 1) A)) =
      (sk.κ n).law (actualTable smallIndex Q n) A := by
  rw [bliPrice_stateAtom c sk Q (Nat.lt_succ_self n) (c.code_mem_states hA),
    chainMass_singleton_code c sk hA]

/-- The price of `φ ⋏ σ` (`φ` mentioning no future candidate atom, small on `σ`'s day) is the
table value times the price of `σ`.
Source: [[bli-program]] §2.5 (constraint 2 in product form)
Kind: L
Fidelity: n/a -/
lemma bliPrice_and_stateAtom {n m q : ℕ} (hnm : n < m) (hq : q ∈ c.states m) {φ : Sentence}
    (hno : NoFutureState c n φ) (hsm : SmallOn m φ) :
    bliPrice Q 𝓜 sk c n (φ ⋏ stateAtom m q) =
      c.tableVal m q φ * bliPrice Q 𝓜 sk c n (stateAtom m q) := by
  rw [bliPrice_of_tierA (not_smallOn_and_of_right (not_smallOn_stateAtom c hnm hq))
      (tierA_and_stateAtom c hnm hq hno hsm),
    tierAPrice_of_consistent c sk _ (consistent_singleton _), smallFactor_some,
    latestEntry_singleton, bliPrice_stateAtom c sk Q hnm hq, mul_comm]

/-! ## M1 — the constraint lemmas (all `L`) -/

/-- **`bli_small` — constraint 1, exact** (`E1x`): `𝐏` copies the base on every day-`n` small
sentence. Definitional (the small-first case of `bliPrice`).
Source: Appendix B constraint 1 (`main.tex:431`, exact form); bli-slides-017 (1); mandate M1
Kind: L
Fidelity: exact (`E1x`, not Appendix B's rounded `E1r`) -/
theorem bli_small : E1x (ratHistory Q) (bliHistory Q 𝓜 sk c) := by
  intro n φ hφ
  unfold bliHistory ratHistory
  rw [bliPrice_of_small (mem_smallSet.mp hφ)]

/-- **`bli_state` — the superbelief is the kernel entry**: for every grid table `A` of day `n+1`,
`𝐏_n(⌜𝐐_{n+1} = code A⌝) = κ_n(actualTable Q n)(A)`. Definitional; uses `StateCoding.large`
through `stateAtom_large` to keep the atom out of the small case.
Source: [[bli-program]] §2.5 (`bli_state`); mandate M1
Kind: L
Fidelity: exact -/
theorem bli_state (n : ℕ) {A : Table smallIndex (n + 1)} (hA : A ∈ grid smallIndex 𝓜.d (n + 1)) :
    superbelief (bliHistory Q 𝓜 sk c) n (c.code (n + 1) A) =
      ((sk.κ n).law (actualTable smallIndex Q n) A : ℝ) := by
  unfold superbelief bliHistory
  rw [bliPrice_state c sk Q n hA]

/-- **`bli_cond2_scoped` — constraint 2, restricted** (`E2xScoped c`): for `n < m`, a candidate
`q`, and `φ ∈ Sminus m m` **mentioning no state atom of a day `> n`**,
`𝐏_n(φ ⋏ σ_{m,q}) = Q̂_q[φ] · 𝐏_n(σ_{m,q})`. Definitional. The restriction is Known issue 1's
antecedent; `bli-found`'s full-scope `E2x` is false for the tent instance
(`Refutations.e2x_full_scope_fails`).
Source: Appendix B constraint 2 (`main.tex:432`); bli-slides-017 (2); mandate M1
Kind: L
Fidelity: weaker: scope minus sentences mentioning a candidate state atom of a day in `(n, m)` -/
theorem bli_cond2_scoped : E2xScoped c (bliStateSystem Q 𝓜 c) (bliHistory Q 𝓜 sk c) := by
  intro n m hnm q hq φ hφ hno
  simp only [bliStateSystem_states] at hq
  have hsm : SmallOn m φ := mem_smallSet.mp (Sminus_subset_smallSet m m hφ)
  unfold bliHistory
  rw [bliPrice_and_stateAtom c sk Q hnm hq hno hsm, bliStateSystem_val]
  push_cast; ring

/-- **`bli_cond3_scoped` — constraint 3 ("latest state wins"), restricted** (`E3Scoped c`):
for `n < m < o`, candidates `q₁`, `q₂`, and `φ ∈ Sminus m m` mentioning no state atom of a day
`> n`, `𝐏_n(φ ⋏ (σ_m ⋏ σ_o)) = Q̂_{q₂}[φ] · 𝐏_n(σ_m ⋏ σ_o)` — the **later** table prices `φ`.
Definitional.
Source: Appendix B constraint 3 (`main.tex:433`); bli-slides-017 (3); mandate M1
Kind: L
Fidelity: weaker: scope restricted as `bli_cond2_scoped` -/
theorem bli_cond3_scoped : E3Scoped c (bliStateSystem Q 𝓜 c) (bliHistory Q 𝓜 sk c) := by
  intro n m o hnm hmo q₁ hq₁ q₂ hq₂ φ hφ hno
  simp only [bliStateSystem_states] at hq₁ hq₂
  have hno' : n < o := hnm.trans hmo
  have hso : SmallOn o φ := (mem_smallSet.mp (Sminus_subset_smallSet m m hφ)).mono hmo.le
  have hlarge : ¬ SmallOn n (stateAtom m q₁ ⋏ stateAtom o q₂) :=
    not_smallOn_and_of_left (not_smallOn_stateAtom c hnm hq₁)
  unfold bliHistory
  rw [bliPrice_of_tierA (not_smallOn_and_of_right hlarge) (tierA_and_two c hnm hq₁ hno' hq₂ hmo hno hso),
    bliPrice_of_tierA hlarge (tierA_stateAtom_and_stateAtom c hnm hq₁ hno' hq₂),
    tierAPrice_of_consistent c sk _ (consistent_pair_of_ne hmo.ne),
    tierAPrice_of_consistent c sk _ (consistent_pair_of_ne hmo.ne),
    smallFactor_some, smallFactor_none, latestEntry_pair_of_lt hmo, bliStateSystem_val]
  push_cast; ring

/-- **`bli_cond3fin_scoped` — constraint 3 for finite chains, restricted** (`E3finScoped c`):
for a nonempty strictly increasing chain of candidates after `n` and `φ` in the earliest day's
scope mentioning no state atom of a day `> n`, `𝐏_n(φ ⋏ ⋀σ) = Q̂_last[φ] · 𝐏_n(⋀σ)`. The
trailing `⊤` of `stateConj` is neutral in the parser. Definitional.
Source: Appendix B constraint 3 ("similarly for longer conjunctions"); mandate M1
Kind: L
Fidelity: weaker: scope restricted as `bli_cond2_scoped` -/
theorem bli_cond3fin_scoped : E3finScoped c (bliStateSystem Q 𝓜 c) (bliHistory Q 𝓜 sk c) := by
  intro n l hne hl hchain φ hφ hno
  simp only [bliStateSystem_states] at hl
  have hlast := latestEntry_isChain hne hchain
  have hhead : l.head hne ∈ l := List.head_mem hne
  have hsm : SmallOn (l.head hne).1 φ := mem_smallSet.mp (Sminus_subset_smallSet _ _ hφ)
  have hsl : SmallOn (latestEntry l).1 φ := hsm.mono (le_latestEntry _ hhead)
  have hlarge : ¬ SmallOn n (stateConj l) := by
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
    rw [stateConj_cons]
    exact not_smallOn_and_of_left
      (not_smallOn_stateAtom c (hl x List.mem_cons_self).1 (hl x List.mem_cons_self).2)
  unfold bliHistory
  rw [bliPrice_of_tierA (not_smallOn_and_of_right hlarge) (tierA_and_stateConj c hne hl hno hsl),
    bliPrice_of_tierA hlarge (tierA_stateConj c hne hl),
    tierAPrice_of_consistent c sk _ (consistent_of_isChain hchain),
    tierAPrice_of_consistent c sk _ (consistent_of_isChain hchain),
    smallFactor_some, smallFactor_none, hlast, bliStateSystem_val]
  push_cast; ring

/-- **`bli_balance` — constraint 4** (`E4`): for every day-`n` small `φ`,
`𝐏_n(φ) = ∑_q 𝐏_n(σ_{n+1,q}) · Q̂_q[φ]`. Reindex the codes by the grid (`inj`), read the
superbeliefs as kernel entries (`bli_state`), and apply `Kernel.balanced` at the **unrounded**
actual table (in the unit cube by `hQ`). Definitional in the kernel's balance field.
Source: Appendix B constraint 4 (`main.tex:434–435`); bli-slides-017 (4); mandate M1
Kind: L
Fidelity: exact (bli-slides-017's scope `φ ∈ smallSet n`)
Hyps: (a) `hQ`: the base's prices lie in `[0,1]` (`ofBeliefStates_inUnit` for FAF markets) -/
theorem bli_balance (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) :
    E4 (bliStateSystem Q 𝓜 c) (bliHistory Q 𝓜 sk c) := by
  intro n φ hφ
  have hφ' : φ ∈ smallSet (n + 1) := smallSet_mono (Nat.le_succ n) hφ
  have hL : bliHistory Q 𝓜 sk c n φ = (Q n φ : ℝ) := by
    unfold bliHistory; rw [bliPrice_of_small (mem_smallSet.mp hφ)]
  rw [hL]
  simp only [bliStateSystem_states, StateCoding.states]
  rw [Finset.sum_image (fun x hx y hy h => c.inj (n + 1) hx hy h)]
  have key : ∀ A ∈ grid smallIndex 𝓜.d (n + 1),
      bliHistory Q 𝓜 sk c n (stateAtom (n + 1) (c.code (n + 1) A)) *
          (bliStateSystem Q 𝓜 c).val (n + 1) (c.code (n + 1) A) φ
        = (((sk.κ n).law (actualTable smallIndex Q n) A * A ⟨φ, hφ'⟩ : ℚ) : ℝ) := by
    intro A hA
    rw [bliStateSystem_val, c.tableVal_code hA hφ']
    have := bli_state c sk Q n hA
    unfold superbelief at this
    rw [this]; push_cast; ring
  rw [Finset.sum_congr rfl key, ← Rat.cast_sum]
  congr 1
  have hbal := (sk.κ n).balanced (actualTable smallIndex Q n) (actualTable_inUnit hQ) ⟨φ, hφ⟩
  rw [Table.restrict_apply] at hbal
  unfold mean meanOn at hbal
  exact hbal.symm

/-- **`bli_partition` — constraint 5** (`E5`): the superbeliefs over the day-`(n+1)` candidates
sum to `1` (`Kernel.sum_law`), and two distinct candidates are exclusive (their conjunction is
an inconsistent chain, priced `0`). Definitional.
Source: bli-slides-017 (5); Appendix B's implicit partition; mandate M1
Kind: L
Fidelity: exact -/
theorem bli_partition : E5 (bliStateSystem Q 𝓜 c) (bliHistory Q 𝓜 sk c) := by
  intro n
  constructor
  · simp only [bliStateSystem_states, StateCoding.states]
    rw [Finset.sum_image (fun x hx y hy h => c.inj (n + 1) hx hy h)]
    have key : ∀ A ∈ grid smallIndex 𝓜.d (n + 1),
        bliHistory Q 𝓜 sk c n (stateAtom (n + 1) (c.code (n + 1) A)) =
          (((sk.κ n).law (actualTable smallIndex Q n) A : ℚ) : ℝ) :=
      fun A hA => bli_state c sk Q n hA
    rw [Finset.sum_congr rfl key, ← Rat.cast_sum, (sk.κ n).sum_law]
    simp
  · intro q₁ hq₁ q₂ hq₂ hne
    simp only [bliStateSystem_states] at hq₁ hq₂
    unfold bliHistory
    rw [bliPrice_of_tierA (not_smallOn_and_of_left (not_smallOn_stateAtom c (Nat.lt_succ_self n) hq₁))
        (tierA_stateAtom_and_stateAtom c (Nat.lt_succ_self n) hq₁ (Nat.lt_succ_self n) hq₂),
      tierAPrice_of_not_consistent c sk _ (not_consistent_pair hne)]
    simp

/-- **`bliHistory_mem_Icc`**: every price of `𝐏` lies in `[0,1]`.
Source: [[bli-program]] §2.5; mandate M1
Kind: L
Fidelity: exact
Hyps: (a) `hQ` -/
theorem bliHistory_mem_Icc (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) (n : ℕ) (ψ : Sentence) :
    0 ≤ bliHistory Q 𝓜 sk c n ψ ∧ bliHistory Q 𝓜 sk c n ψ ≤ 1 := by
  unfold bliHistory
  have : 0 ≤ bliPrice Q 𝓜 sk c n ψ ∧ bliPrice Q 𝓜 sk c n ψ ≤ 1 := by
    by_cases h : SmallOn n ψ
    · rw [bliPrice_of_small h]; exact hQ n ψ
    · cases ht : tierA c n ψ with
      | none => rw [bliPrice_of_tierB h ht]; exact hQ n ψ
      | some s => rw [bliPrice_of_tierA h ht]; exact tierAPrice_mem_Icc c sk _ s
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

/-- **`bli_update_small` — Bayesian update on small sentences, product form, up to the mesh**:
for every day-`n` small `φ` and the realized day-`(n+1)` atom `σ`,
`|𝐏_{n+1}(φ) · 𝐏_n(σ) − 𝐏_n(φ ⋏ σ)| ≤ (1 / (2 d_{n+1})) · 𝐏_n(σ)`. The left factor is the
base's exact price, the joint reads the **rounded** actual table (`actualState`), and the gap is
`roundTo_err`. Exact when `actualTable Q (n+1)` is a grid table (`Update.lean`). Holds on
**all** of `smallSet n` (a day-`n`-small sentence mentions no future candidate atom).
Source: Appendix B (`main.tex:440–442`); bli-slides-004; mandate M1/M5
Kind: L
Fidelity: weaker: up to `1/(2 d_{n+1})`, product form; exact on the denominator grid
Hyps: (a) `hQ` -/
theorem bli_update_small (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) (n : ℕ) {φ : Sentence}
    (hφ : φ ∈ smallSet n) :
    |bliHistory Q 𝓜 sk c (n + 1) φ *
        bliHistory Q 𝓜 sk c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) -
      bliHistory Q 𝓜 sk c n (φ ⋏ stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1)))|
      ≤ (1 / (2 * (𝓜.d (n + 1) : ℝ))) *
        bliHistory Q 𝓜 sk c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) := by
  have hφ' : φ ∈ smallSet (n + 1) := smallSet_mono (Nat.le_succ n) hφ
  have hA : actualState smallIndex 𝓜.d Q (n + 1) ∈ grid smallIndex 𝓜.d (n + 1) :=
    actualState_mem_grid
  simp only [bliStateSystem_actual]
  have hq : c.code (n + 1) (actualState smallIndex 𝓜.d Q (n + 1)) ∈ c.states (n + 1) :=
    c.code_mem_states hA
  have hno : NoFutureState c n φ := noFutureState_of_smallOn c (mem_smallSet.mp hφ)
  have h1 : bliHistory Q 𝓜 sk c (n + 1) φ = (Q (n + 1) φ : ℝ) := by
    unfold bliHistory; rw [bliPrice_of_small (mem_smallSet.mp hφ')]
  have h3 : bliHistory Q 𝓜 sk c n
      (φ ⋏ stateAtom (n + 1) (c.code (n + 1) (actualState smallIndex 𝓜.d Q (n + 1)))) =
      ((actualState smallIndex 𝓜.d Q (n + 1) ⟨φ, hφ'⟩ : ℚ) : ℝ) *
        bliHistory Q 𝓜 sk c n
          (stateAtom (n + 1) (c.code (n + 1) (actualState smallIndex 𝓜.d Q (n + 1)))) := by
    unfold bliHistory
    rw [bliPrice_and_stateAtom c sk Q (Nat.lt_succ_self n) hq hno (mem_smallSet.mp hφ'),
      c.tableVal_code hA hφ']
    push_cast; ring
  have hPnn : 0 ≤ bliHistory Q 𝓜 sk c n
      (stateAtom (n + 1) (c.code (n + 1) (actualState smallIndex 𝓜.d Q (n + 1)))) :=
    (bliHistory_mem_Icc c sk Q hQ n _).1
  rw [h1, h3, ← sub_mul, abs_mul, abs_of_nonneg hPnn]
  refine mul_le_mul_of_nonneg_right ?_ hPnn
  have herr : |actualState smallIndex 𝓜.d Q (n + 1) ⟨φ, hφ'⟩ - Q (n + 1) φ| ≤
      1 / (2 * (𝓜.d (n + 1) : ℚ)) := by
    have := actualState_err (𝒮 := smallIndex) (d := 𝓜.d) hQ (𝓜.d_pos (n + 1)) ⟨φ, hφ'⟩
    push_cast at this
    exact this
  rw [abs_sub_comm] at herr
  obtain ⟨hl, hr⟩ := abs_le.mp herr
  have hl' := (Rat.cast_le (K := ℝ)).mpr hl
  have hr' := (Rat.cast_le (K := ℝ)).mpr hr
  push_cast at hl' hr'
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith
  · linarith

/-- **`E1r` on the denominator grid**: Appendix B's *rounded* constraint 1 holds for `𝐏` exactly
when the actual tables are grid tables (then rounding is the identity). Off the grid `E1r` is
false for the exact construction; B1 of record is `E1x` (program §3.2: rounding small prices
breaks the transfer theorem). Known issue 4.
Source: Appendix B constraint 1 (`main.tex:431`); mandate M1 (E1x-vs-E1r remark)
Kind: L
Fidelity: weaker: needs the denominator-grid hypothesis
Hyps: (a) `hgrid`: every actual table is a grid table -/
theorem bli_E1r_of_grid (hgrid : ∀ n, actualTable smallIndex Q n ∈ grid smallIndex 𝓜.d n) :
    E1r (bliStateSystem Q 𝓜 c) (bliHistory Q 𝓜 sk c) := by
  intro n φ hφ
  unfold bliHistory
  rw [bliPrice_of_small (mem_smallSet.mp hφ), bliStateSystem_val, bliStateSystem_actual,
    c.tableVal_code actualState_mem_grid hφ, actualState_eq_of_mem_grid (𝓜.d_pos n) (hgrid n)]
  rfl

/-! ## M3 — the bundle and the tent instance -/

/-- **`bliHistory_isBLI_scoped`** (T1, finite): over any skeleton, `𝐏` satisfies the scoped
Roman bundle `E1x ∧ E2xScoped ∧ E3Scoped ∧ E4 ∧ E5`. Composition of the M1 rows. **Not**
`IsBLI_Roman` itself: its full-scope `E2x` fails (`Refutations.e2x_full_scope_fails`).
Source: bli-slides-017; [[bli-program]] §2.5/§3.5 (i); mandate M3
Kind: C
Fidelity: weaker: faith predicates scoped (Known issue 1)
Hyps: (a) `hQ` -/
theorem bliHistory_isBLI_scoped (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) :
    IsBLI_RomanScoped c (bliStateSystem Q 𝓜 c) (ratHistory Q) (bliHistory Q 𝓜 sk c) :=
  ⟨bli_small c sk Q, bli_cond2_scoped c sk Q, bli_cond3_scoped c sk Q, bli_balance c sk Q hQ,
    bli_partition c sk Q⟩

/-- **The tent instance is non-degenerate**: with `sk := tentSkeleton`, every superbelief of `𝐏`
(read through the coding) charges every point of the product face of the actual table.
Source: [[bli-program]] §3.4; bli-slides-018; mandate M3
Kind: L
Fidelity: exact
Hyps: (a) `hQ` -/
theorem bliHistory_tent_nonDegenerate (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) (n : ℕ) :
    NonDegenerate 𝓜.d
      (fun A => bliPrice Q 𝓜 (tentSkeleton smallIndex 𝓜) c n (stateAtom (n + 1) (c.code (n + 1) A)))
      (actualTable smallIndex Q n) := by
  intro A hA
  have hA' : A ∈ grid smallIndex 𝓜.d (n + 1) := faceProd_subset_grid _ _ hA
  show 0 < bliPrice Q 𝓜 (tentSkeleton smallIndex 𝓜) c n (stateAtom (n + 1) (c.code (n + 1) A))
  rw [bliPrice_state c (tentSkeleton smallIndex 𝓜) Q n hA']
  exact tentLaw_nonDegenerate (actualTable_inUnit hQ) A hA

/-- **N+ for the tent instance**: if the base prices some day-`n` small sentence strictly inside
`(0, 1)`, then two *distinct* day-`(n+1)` candidates carry positive superbelief — the
superbelief is not a point mass (contrast B0, `Degenerate.lean`). The two witnesses are the
face points sending `φ` to `0` and to `1` and copying the base's `0/1` prices elsewhere
(`0` on new coordinates), both in the face by `tentLaw_pos_iff`.
Source: [[bli-program]] §3.4 (non-degeneracy); mandate M3 (the package's N+)
Kind: N+
Fidelity: n/a
Hyps: (a) `hQ`; (a) an interior price -/
theorem bliHistory_tent_two_states (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) (n : ℕ) {φ : Sentence}
    (hφ : φ ∈ smallSet n) (h0 : 0 < Q n φ) (h1 : Q n φ < 1) :
    ∃ q₁ ∈ c.states (n + 1), ∃ q₂ ∈ c.states (n + 1), q₁ ≠ q₂ ∧
      0 < superbelief (bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c) n q₁ ∧
      0 < superbelief (bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c) n q₂ := by
  -- the two face points
  let mk : ℚ → Table smallIndex (n + 1) := fun v ψ =>
    if ψ.1 = φ then v else if ψ.1 ∈ smallSet n ∧ Q n ψ.1 = 1 then 1 else 0
  have hgrid : ∀ v, v ∈ gridVals (𝓜.d (n + 1)) → mk v ∈ grid smallIndex 𝓜.d (n + 1) := by
    intro v hv
    rw [mem_grid_iff]
    intro ψ
    show (if ψ.1 = φ then v else if ψ.1 ∈ smallSet n ∧ Q n ψ.1 = 1 then 1 else 0) ∈ _
    split_ifs
    · exact hv
    · exact one_mem_gridVals (𝓜.d_pos _)
    · exact zero_mem_gridVals _
  have hface : ∀ v, v ∈ gridVals (𝓜.d (n + 1)) →
      mk v ∈ faceProd smallIndex 𝓜.d n (actualTable smallIndex Q n) := by
    intro v hv
    rw [mem_faceProd_iff]
    refine ⟨hgrid v hv, fun ψ hψ => ?_⟩
    rw [Table.restrict_apply]
    show (if ψ.1 = φ then v else if ψ.1 ∈ smallSet n ∧ Q n ψ.1 = 1 then 1 else 0) = Q n ψ.1
    have hne : ψ.1 ≠ φ := by
      intro h
      change Q n ψ.1 = 0 ∨ Q n ψ.1 = 1 at hψ
      rw [h] at hψ
      rcases hψ with h' | h' <;> linarith
    rw [if_neg hne]
    change Q n ψ.1 = 0 ∨ Q n ψ.1 = 1 at hψ
    rcases hψ with h' | h'
    · rw [if_neg (fun h => by rw [h'] at h; exact zero_ne_one h.2), h']
    · rw [if_pos ⟨ψ.2, h'⟩, h']
  have hpos : ∀ v, v ∈ gridVals (𝓜.d (n + 1)) →
      0 < superbelief (bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c) n (c.code (n + 1) (mk v)) := by
    intro v hv
    rw [bli_state c (tentSkeleton smallIndex 𝓜) Q n (hgrid v hv)]
    exact_mod_cast tentLaw_nonDegenerate (actualTable_inUnit hQ) (mk v) (hface v hv)
  have hne : mk 0 ≠ mk 1 := by
    intro h
    have := congrFun h ⟨φ, smallSet_mono (Nat.le_succ n) hφ⟩
    simp [mk] at this
  refine ⟨c.code (n + 1) (mk 0), c.code_mem_states (hgrid 0 (zero_mem_gridVals _)),
    c.code (n + 1) (mk 1), c.code_mem_states (hgrid 1 (one_mem_gridVals (𝓜.d_pos _))), ?_,
    hpos 0 (zero_mem_gridVals _), hpos 1 (one_mem_gridVals (𝓜.d_pos _))⟩
  intro h
  exact hne (c.inj (n + 1) (hgrid 0 (zero_mem_gridVals _)) (hgrid 1 (one_mem_gridVals (𝓜.d_pos _))) h)

/-! ## M3: additivity on the state algebra -/

/-- **`bli_stateAlgebra_additive` — every future day's candidates carry total mass one**: for
`n < m`, `∑_{q ∈ states m} 𝐏_n(⌜𝑸_m = q⌝) = 1` (not only the next day's, which is `bli_partition`).
The chain-level identity is `Parser.chainProbH_sum_states` at the empty chain and horizon
`m − n`; the Tier-A prices are the marginals of one probability.
Source: [[bli-program]] §3.5 (i); mandate M3
Kind: C
Fidelity: exact (the day-`m` marginal identity for the state atoms; the general additivity is `chainProbH_sum_states`)
Hyps: (a) `n < m` -/
theorem bli_stateAlgebra_additive {n m : ℕ} (hnm : n < m) :
    ∑ q ∈ c.states m, bliHistory Q 𝓜 sk c n (stateAtom m q) = 1 := by
  unfold bliHistory
  rw [← Rat.cast_sum]
  have : ∑ q ∈ c.states m, bliPrice Q 𝓜 sk c n (stateAtom m q) = 1 := by
    rw [Finset.sum_congr rfl (fun q hq => bliPrice_stateAtom c sk Q hnm hq)]
    unfold chainMass
    simp only [latestEntry_singleton]
    rw [chainProbH_sum_states [] (m - n) n _ m hnm (by omega), chainProbH_nil]
  rw [this, Rat.cast_one]

end Cleanroom.Bli.BliTrajectory
