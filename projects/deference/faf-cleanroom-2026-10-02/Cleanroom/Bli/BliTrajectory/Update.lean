import Cleanroom.Bli.BliTrajectory.Degenerate

/-!
# `bli-trajectory` · Update: Bayesian update on small sentences (M5, T3) and on the state
algebra (M6, T4)

**Scope sentence (plan §0.4 rule 9).** The claim "`𝐏`'s updates are Bayesian"
(`main.tex:440`, bli-paper-040; bli-slides-004's flag) is proved here **on small sentences up to
the mesh, under positivity of the realized next state, and on the Tier-A state algebra exactly
on the denominator grid — and nowhere else**: on Tier B the update identity is false
(`Refutations.tb_refuted`), and constraints 1–4 do not imply it on large sentences
(`Refutations.constraints_not_imply_update`).

**Positivity.** Every ratio here carries `0 < 𝐏_n(σ)` explicitly and uses Lean's `/` on `ℝ`.
FAF's `conditionalQuote` (junk value `1` at price `0`) is **not used**: with it, the null days
(where the realized next state has mass `0` — `bli-superbelief` E6 over FAF's inductor) would
read as exact updates.

**Restart from the unrounded table (M6).** `𝐏_{n+1}` prices Tier A from `actualTable Q (n+1)`,
while `𝐏_n(· ⋏ σ)` conditions on the *rounded* `actualState (n+1)`: the two chains agree exactly
when the day-`(n+1)` actual table is a grid table (`bli_update_tierA_exact`), and otherwise
differ by one ℓ¹ contraction step of the kernel (`bli_update_tierA_modulus`, under an explicit
`KernelLip` hypothesis on the skeleton). This is the whole content of T4 ([[bli-program]]
§3.5 (iii), `C:C3`).
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite

open Classical

variable {𝓜 : Mesh} (c : StateCoding 𝓜) (sk : Skeleton smallIndex 𝓜.d) (Q : RatHistory)

/-! ## M5 — T3: the small-sentence update, ratio form -/

/-- The joint price of a day-`n` small `φ` with the realized next state is the **rounded**
day-`(n+1)` price of `φ` times the mass of that state (rational form, no hypothesis).
Source: Appendix B constraint 2 at the realized state; mandate M5
Kind: L
Fidelity: n/a -/
lemma bliPrice_and_actual (n : ℕ) {φ : Sentence} (hφ : φ ∈ smallSet n) :
    bliPrice Q 𝓜 sk c n (φ ⋏ stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) =
      actualState smallIndex 𝓜.d Q (n + 1) ⟨φ, smallSet_mono (Nat.le_succ n) hφ⟩ *
        bliPrice Q 𝓜 sk c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) := by
  have hφ' : φ ∈ smallSet (n + 1) := smallSet_mono (Nat.le_succ n) hφ
  have hA : actualState smallIndex 𝓜.d Q (n + 1) ∈ grid smallIndex 𝓜.d (n + 1) :=
    actualState_mem_grid
  simp only [bliStateSystem_actual]
  rw [bliPrice_and_stateAtom c sk Q (Nat.lt_succ_self n) (c.code_mem_states hA)
    (noFutureState_of_smallOn c (mem_smallSet.mp hφ)) (mem_smallSet.mp hφ'),
    c.tableVal_code hA hφ']

/-- **`bli_update_small_ratio` — the small-sentence update in ratio form, up to the mesh, under
positivity**: for `φ ∈ smallSet n` and `0 < 𝐏_n(σ)` (`σ` the realized day-`(n+1)` atom),
`|𝐏_{n+1}(φ) − 𝐏_n(φ ⋏ σ) / 𝐏_n(σ)| ≤ 1 / (2 d_{n+1})`. Division is Lean's `/` on `ℝ`;
`conditionalQuote` is not used (its junk `1` at price `0` would make null days look exact).
**This is the only sense in which "`𝐏`'s updates are Bayesian" (`main.tex:440`) is proved on
small sentences: up to the mesh, under positivity.**
Source: Appendix B (`main.tex:440–442`); bli-slides-004 (exact "given exact discretized
agreement"); mandate M5
Kind: C
Fidelity: weaker: up to `1/(2 d_{n+1})`; needs positivity
Hyps: (a) `hQ`; (a) `hpos` (positivity, explicit) -/
theorem bli_update_small_ratio (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) (n : ℕ) {φ : Sentence}
    (hφ : φ ∈ smallSet n)
    (hpos : 0 < bliHistory Q 𝓜 sk c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1)))) :
    |bliHistory Q 𝓜 sk c (n + 1) φ -
        bliHistory Q 𝓜 sk c n (φ ⋏ stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) /
          bliHistory Q 𝓜 sk c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1)))|
      ≤ 1 / (2 * (𝓜.d (n + 1) : ℝ)) := by
  have h := bli_update_small c sk Q hQ n hφ
  set P := bliHistory Q 𝓜 sk c
  set σ := stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))
  have e : P (n + 1) φ - P n (φ ⋏ σ) / P n σ = (P (n + 1) φ * P n σ - P n (φ ⋏ σ)) / P n σ := by
    field_simp
  rw [e, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  exact h

/-- **`bli_update_small_exact_iff`**: under positivity, the ratio `𝐏_n(φ ⋏ σ) / 𝐏_n(σ)` equals
`𝐏_{n+1}(φ)` **iff** the base's day-`(n+1)` price of `φ` is a grid value (the ratio is the
rounded price). So the small-sentence update is exact exactly on the denominator grid
(bli-slides-004's flag).
Source: bli-slides-004; Appendix B (`main.tex:440`); mandate M5
Kind: C
Fidelity: exact
Hyps: (a) `hpos` -/
theorem bli_update_small_exact_iff (n : ℕ) {φ : Sentence} (hφ : φ ∈ smallSet n)
    (hpos : 0 < bliHistory Q 𝓜 sk c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1)))) :
    bliHistory Q 𝓜 sk c n (φ ⋏ stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) /
        bliHistory Q 𝓜 sk c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) =
      bliHistory Q 𝓜 sk c (n + 1) φ ↔ Q (n + 1) φ ∈ gridVals (𝓜.d (n + 1)) := by
  have hφ' : φ ∈ smallSet (n + 1) := smallSet_mono (Nat.le_succ n) hφ
  have e1 : bliHistory Q 𝓜 sk c n (φ ⋏ stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) /
      bliHistory Q 𝓜 sk c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) =
      ((roundVal (𝓜.d (n + 1)) (Q (n + 1) φ) : ℚ) : ℝ) := by
    unfold bliHistory
    rw [bliPrice_and_actual c sk Q n hφ]
    push_cast
    rw [mul_div_assoc, div_self (by unfold bliHistory at hpos; exact_mod_cast hpos.ne'), mul_one]
    rfl
  have e2 : bliHistory Q 𝓜 sk c (n + 1) φ = (Q (n + 1) φ : ℝ) := by
    unfold bliHistory; rw [bliPrice_of_small (mem_smallSet.mp hφ')]
  rw [e1, e2, Rat.cast_inj]
  constructor
  · intro h; rw [← h]; exact roundVal_mem_gridVals _ _
  · intro h; exact roundVal_eq_self (𝓜.d_pos _) h

/-- **`BayesRatio` on small sentences on the denominator grid**: when the base's day-`(n+1)`
price of `φ` is a grid value, the ratio form of the update holds at `φ`.
Source: bli-slides-004; mandate M5
Kind: C
Fidelity: exact (on the denominator grid, under positivity) -/
theorem bli_bayesRatio_small_of_grid (n : ℕ) {φ : Sentence} (hφ : φ ∈ smallSet n)
    (hgrid : Q (n + 1) φ ∈ gridVals (𝓜.d (n + 1))) :
    BayesRatio (bliStateSystem Q 𝓜 c) (bliHistory Q 𝓜 sk c) n φ := fun hpos =>
  ((bli_update_small_exact_iff c sk Q n hφ hpos).mpr hgrid).symm

/-- **B0's small-sentence update is exact on the days its prices did not move**: if the rounded
day-`(n+1)` table is the degenerate continuation and `Q_{n+1}(φ)` is a grid value, then
`𝐏⁰_{n+1}(φ) = 𝐏⁰_n(φ ⋏ σ) / 𝐏⁰_n(σ)` (and `𝐏⁰_n(σ) = 1`). With `b0_pos_iff`: the ratio form is
available for B0 exactly on those days, and then it is exact.
Source: Appendix B (`main.tex:447–449`); bli-slides-005; mandate M5 (corollary on B0)
Kind: C
Fidelity: exact
Hyps: (a) `hmove`; (a) `hgrid` -/
theorem b0_update_small_exact (n : ℕ)
    (hmove : actualState smallIndex 𝓜.d Q (n + 1) = degStep 𝓜.d n (actualTable smallIndex Q n))
    {φ : Sentence} (hφ : φ ∈ smallSet n) (hgrid : Q (n + 1) φ ∈ gridVals (𝓜.d (n + 1))) :
    b0History Q 𝓜 c (n + 1) φ =
      b0History Q 𝓜 c n (φ ⋏ stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) /
        b0History Q 𝓜 c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) := by
  have hφ' : φ ∈ smallSet (n + 1) := smallSet_mono (Nat.le_succ n) hφ
  have hA : actualState smallIndex 𝓜.d Q (n + 1) ∈ grid smallIndex 𝓜.d (n + 1) :=
    actualState_mem_grid
  have hq := c.code_mem_states hA
  have hσ : b0History Q 𝓜 c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) = 1 := by
    simp only [bliStateSystem_actual]
    unfold b0History
    rw [b0Price_stateAtom c Q (Nat.lt_succ_self n) hq, degAt_succ 𝓜.d _ le_rfl, degAt_self,
      if_pos (by rw [hmove])]
    norm_num
  rw [hσ, div_one]
  simp only [bliStateSystem_actual] at hσ ⊢
  unfold b0History at hσ ⊢
  rw [b0Price_and_stateAtom c Q (Nat.lt_succ_self n) hq (noFutureState_of_smallOn c (mem_smallSet.mp hφ))
      (mem_smallSet.mp hφ'), c.tableVal_code hA hφ', b0Price_of_small (mem_smallSet.mp hφ')]
  have : actualState smallIndex 𝓜.d Q (n + 1) ⟨φ, hφ'⟩ = Q (n + 1) φ :=
    roundVal_eq_self (𝓜.d_pos _) hgrid
  rw [this]
  have h1 : (b0Price Q 𝓜 c n (stateAtom (n + 1) (c.code (n + 1) (actualState smallIndex 𝓜.d Q (n + 1))))
      : ℝ) = 1 := hσ
  rw [Rat.cast_mul, h1, mul_one]

/-! ## M6 — T4: the total update on the state algebra, exact on the denominator grid -/

/-- A Tier-A sentence at day `n+1` mentions a future candidate atom, hence is large.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_smallOn_of_tierA {n : ℕ} {ψ : Sentence} {l : List (ℕ × ℕ)} {s : Option Sentence}
    (hψ : tierA c n ψ = some (l, s)) : ¬ SmallOn n ψ := by
  obtain ⟨hp, hne, -⟩ := tierA_eq_some c hψ
  refine not_smallOn_of_hasFutureAtom c ?_
  by_contra h
  rw [Bool.not_eq_true] at h
  rw [parse_of_noFutureState c h] at hp
  simp only [Option.some.injEq, Prod.mk.injEq] at hp
  exact hne hp.1.symm

/-- The chain mass of `l ++ [(n+1, code A)]` from `t` on day `n` is the kernel entry at `A`
times the chain mass of `l` **restarted from `A`** on day `n+1` (the restart identity).
Source: [[bli-program]] §3.5 (iii); mandate M6
Kind: L
Fidelity: exact -/
lemma chainMass_append_actual {n : ℕ} (t : Table smallIndex n) {A : Table smallIndex (n + 1)}
    (hA : A ∈ grid smallIndex 𝓜.d (n + 1)) {l : List (ℕ × ℕ)} (hne : l ≠ [])
    (hl : ∀ x ∈ l, n + 1 < x.1) :
    chainMass sk c n t (l ++ [(n + 1, c.code (n + 1) A)]) =
      (sk.κ n).law t A * chainMass sk c (n + 1) A l := by
  unfold chainMass
  rw [latestEntry_append_singleton hne _ (fun x hx => (hl x hx).le)]
  have hlat : n + 1 < (latestEntry l).1 := hl _ (latestEntry_mem hne)
  rw [chainProbH_congr_mem c sk (l := l ++ [(n + 1, c.code (n + 1) A)])
      (l' := (n + 1, c.code (n + 1) A) :: l) (fun x => by simp [or_comm]),
    show (latestEntry l).1 - n = (latestEntry l).1 - (n + 1) + 1 by omega,
    chainProbH_cons_succ c sk hA l hl t]

/-- The small factor depends on the chain only through its latest entry.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma smallFactor_append_actual {n : ℕ} (a : ℕ) {l : List (ℕ × ℕ)} (hne : l ≠ [])
    (hl : ∀ x ∈ l, n + 1 < x.1) (s : Option Sentence) :
    smallFactor c (l ++ [(n + 1, a)]) s = smallFactor c l s := by
  cases s with
  | none => rfl
  | some φ =>
    simp only [smallFactor_some]
    rw [latestEntry_append_singleton hne _ (fun x hx => (hl x hx).le)]

/-- **`bliPrice_update_tierA_exact` (rational form).** On a day whose actual table is a grid
table, for every Tier-A `ψ` at day `n+1` whose small part mentions no state atom of a day
`> n`: `𝐏_{n+1}(ψ) · 𝐏_n(σ) = 𝐏_n(ψ ⋏ σ)` with `σ` the realized day-`(n+1)` atom. The chain of
`ψ ⋏ σ` at day `n` is `ψ`'s chain with `σ` appended (day shift + parser), and its mass factors
through the restart identity from the conditioned table, which **is** the day-`(n+1)` actual
table on the denominator grid. Graded `C` (audit r1 N4): the identity is definitional in the
forward recursion; the work is the day shift `parse_of_parse_succ`, the parser's append and
the restart identity `chainProbH_cons_succ`.
Source: Appendix B (`main.tex:440`); [[bli-program]] §3.5 (iii); mandate M6
Kind: C
Fidelity: exact (on the denominator grid; the small part may not mention a day-`(n+1)` atom)
Hyps: (a) `hgrid`; (a) the parse and small-part hypotheses (syntactic) -/
theorem bliPrice_update_tierA_exact (n : ℕ)
    (hgrid : actualTable smallIndex Q (n + 1) ∈ grid smallIndex 𝓜.d (n + 1))
    {ψ : Sentence} {l : List (ℕ × ℕ)} {s : Option Sentence} (hψ : tierA c (n + 1) ψ = some (l, s))
    (hs : ∀ φ, s = some φ → NoFutureState c n φ) :
    bliPrice Q 𝓜 sk c (n + 1) ψ *
        bliPrice Q 𝓜 sk c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) =
      bliPrice Q 𝓜 sk c n (ψ ⋏ stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) := by
  obtain ⟨hp, hne, hsmall⟩ := tierA_eq_some c hψ
  have hl : ∀ x ∈ l, n + 1 < x.1 := fun x hx => (parse_entries c hp x hx).1
  have hAeq : actualState smallIndex 𝓜.d Q (n + 1) = actualTable smallIndex Q (n + 1) :=
    actualState_eq_of_mem_grid (𝓜.d_pos _) hgrid
  simp only [bliStateSystem_actual]
  rw [hAeq]
  set A := actualTable smallIndex Q (n + 1) with hAdef
  set a := c.code (n + 1) A with hadef
  have hq : a ∈ c.states (n + 1) := c.code_mem_states hgrid
  -- the parse of `ψ ⋏ σ` at day `n`
  have hp0 : parse c n ψ = some (l, s) := parse_of_parse_succ c hp hs
  have hpσ : parse c n (stateAtom (n + 1) a) = some ([(n + 1, a)], none) :=
    parse_stateAtom c (Nat.lt_succ_self n) hq
  have hfut : hasFutureAtom c n (ψ ⋏ stateAtom (n + 1) a) = true := by
    rw [hasFutureAtom_and, hasFutureAtom_stateAtom, decide_eq_true ⟨Nat.lt_succ_self n, hq⟩]
    simp
  have hpand : parse c n (ψ ⋏ stateAtom (n + 1) a) = some (l ++ [(n + 1, a)], s) := by
    rw [parse_and_of_parse c hp0 hpσ hfut (stateAtom_ne_top _ _)]
    cases s with
    | none => rfl
    | some φ => rfl
  have htand : tierA c n (ψ ⋏ stateAtom (n + 1) a) = some (l ++ [(n + 1, a)], s) := by
    refine tierA_of_parse c hpand (by simp) ?_
    rw [latestEntry_append_singleton hne _ (fun x hx => (hl x hx).le)]
    exact hsmall
  -- both prices
  rw [bliPrice_of_tierA (not_smallOn_of_tierA c hψ) hψ,
    bliPrice_of_tierA (not_smallOn_and_of_right (not_smallOn_stateAtom c (Nat.lt_succ_self n) hq)) htand,
    bliPrice_state c sk Q n hgrid]
  have hcons : Consistent (l ++ [(n + 1, a)]) ↔ Consistent l :=
    consistent_append_singleton_iff (fun x hx => (hl x hx).ne')
  by_cases hc : Consistent l
  · rw [tierAPrice_of_consistent c sk _ hc, tierAPrice_of_consistent c sk _ (hcons.mpr hc),
      chainMass_append_actual c sk _ hgrid hne hl, smallFactor_append_actual c a hne hl]
    ring
  · rw [tierAPrice_of_not_consistent c sk _ hc,
      tierAPrice_of_not_consistent c sk _ (fun h => hc (hcons.mp h))]
    ring

/-- **`bli_update_tierA_exact` — the total update on the state algebra, exact on the denominator
grid** (real form of `bliPrice_update_tierA_exact`): `𝐏_{n+1}(ψ) · 𝐏_n(σ) = 𝐏_n(ψ ⋏ σ)` for
every Tier-A `ψ` at day `n+1` whose small part mentions no day-`(n+1)` state atom. Graded `C`
(audit r1 N4; see `bliPrice_update_tierA_exact`).
Source: Appendix B (`main.tex:440`); bli-slides-048 (constraint 5 on the state algebra); mandate M6
Kind: C
Fidelity: exact (on the denominator grid)
Hyps: (a) `hgrid`; (a) syntactic -/
theorem bli_update_tierA_exact (n : ℕ)
    (hgrid : actualTable smallIndex Q (n + 1) ∈ grid smallIndex 𝓜.d (n + 1))
    {ψ : Sentence} {l : List (ℕ × ℕ)} {s : Option Sentence} (hψ : tierA c (n + 1) ψ = some (l, s))
    (hs : ∀ φ, s = some φ → NoFutureState c n φ) :
    bliHistory Q 𝓜 sk c (n + 1) ψ *
        bliHistory Q 𝓜 sk c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) =
      bliHistory Q 𝓜 sk c n (ψ ⋏ stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) := by
  unfold bliHistory
  rw [← Rat.cast_mul, bliPrice_update_tierA_exact c sk Q n hgrid hψ hs]

/-- **Ratio form** under positivity: `𝐏_{n+1}(ψ) = 𝐏_n(ψ ⋏ σ) / 𝐏_n(σ)`.
Source: Appendix B (`main.tex:440`); mandate M6
Kind: C
Fidelity: exact (on the denominator grid, under positivity)
Hyps: (a) `hgrid`; (a) `hpos` -/
theorem bli_update_tierA_ratio (n : ℕ)
    (hgrid : actualTable smallIndex Q (n + 1) ∈ grid smallIndex 𝓜.d (n + 1))
    {ψ : Sentence} {l : List (ℕ × ℕ)} {s : Option Sentence} (hψ : tierA c (n + 1) ψ = some (l, s))
    (hs : ∀ φ, s = some φ → NoFutureState c n φ)
    (hpos : 0 < bliHistory Q 𝓜 sk c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1)))) :
    bliHistory Q 𝓜 sk c (n + 1) ψ =
      bliHistory Q 𝓜 sk c n (ψ ⋏ stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) /
        bliHistory Q 𝓜 sk c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) := by
  rw [eq_div_iff hpos.ne']
  exact bli_update_tierA_exact c sk Q n hgrid hψ hs

/-- The sentences on which the total update is proved: Tier A at day `n+1` with a small part
mentioning no state atom of a day `> n`.
Source: mandate M6 (`TB_on` Tier A)
Kind: D
Fidelity: n/a -/
def TierAUpdatable (n : ℕ) (ψ : Sentence) : Prop :=
  ∃ l s, tierA c (n + 1) ψ = some (l, s) ∧ ∀ φ, s = some φ → NoFutureState c n φ

/-- **The total-update hypothesis package is inhabited**: every day-`(n+2)` candidate atom is
`TierAUpdatable` at day `n` (chain `[(n+2, q)]`, no small part), so `bli_update_tierA_exact` and
`TB_on (TierAUpdatable c)` are not vacuous (audit r1 adversarial N9, probe
`tierAUpdatable_stateAtom`).
Source: mandate M6 (non-vacuity)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem tierAUpdatable_stateAtom (n : ℕ) {q : ℕ} (hq : q ∈ c.states (n + 2)) :
    TierAUpdatable c n (stateAtom (n + 2) q) :=
  ⟨[(n + 2, q)], none, tierA_stateAtom c (by omega) hq, fun φ h => by cases h⟩

/-- **`TB` on the state algebra, on the denominator grid**: `TB_on (TierAUpdatable c)` holds when
every actual table is a grid table. `TB` on every sentence is false (`Refutations.tb_refuted`).
Source: bli-slides-048; mandate M6/Known issue 2
Kind: C
Fidelity: weaker: Tier A only; denominator grid
Hyps: (a) `hgrid` -/
theorem bli_TB_on_tierA (hgrid : ∀ n, actualTable smallIndex Q (n + 1) ∈ grid smallIndex 𝓜.d (n + 1)) :
    TB_on (TierAUpdatable c) (bliStateSystem Q 𝓜 c) (bliHistory Q 𝓜 sk c) := by
  rintro n ψ ⟨l, s, hψ, hs⟩
  exact bli_update_tierA_exact c sk Q n (hgrid n) hψ hs

/-! ## M6 — the modulus form under an explicit ℓ¹-Lipschitz hypothesis -/

/-- **One ℓ¹ contraction step**: two start tables within `ε` give chain probabilities within
`L m · ε`, under `KernelLip sk L`.
Source: mandate M6 (modulus form)
Kind: P
Fidelity: exact
Hyps: (a) `hL : KernelLip sk L` (explicit; the tent's constant is `bli-superbelief`'s) -/
lemma chainProbH_lipschitz {L : ℕ → ℚ} (hL : KernelLip sk L) (l : List (ℕ × ℕ)) (m : ℕ)
    {t t' : Table smallIndex m} (ht : t.InUnit) (ht' : t'.InUnit) {ε : ℚ}
    (hε : ∀ φ, |t φ - t' φ| ≤ ε) (H : ℕ) :
    |chainProbH sk c l m t H - chainProbH sk c l m t' H| ≤ L m * ε := by
  have hLε : 0 ≤ L m * ε :=
    le_trans (Finset.sum_nonneg fun Q _ => abs_nonneg _) (hL m t t' ε ht ht' hε)
  cases H with
  | zero => simp [hLε]
  | succ H =>
    rw [chainProbH_succ, chainProbH_succ, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun Q _ => ?_)
      (hL m t t' ε ht ht' hε))
    rw [← sub_mul, abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [abs_le]
    split_ifs
    · exact ⟨by linarith [chainProbH_nonneg c sk l H (m + 1) Q],
        chainProbH_le_one c sk l H (m + 1) Q⟩
    · norm_num

/-- **`bli_update_tierA_modulus` — the total update up to one contraction step**: for an
abstract skeleton with ℓ¹-modulus `L`, on every day and every Tier-A `ψ` (small part mentioning
no day-`(n+1)` atom), `|𝐏_{n+1}(ψ) · 𝐏_n(σ) − 𝐏_n(ψ ⋏ σ)| ≤ 𝐏_n(σ) · L_{n+1} / (2 d_{n+1})`
(hence `≤ L_{n+1} / (2 d_{n+1})`): the two chains start from the unrounded and the rounded
day-`(n+1)` table, within `1/(2 d_{n+1})` in every coordinate. The tent's modulus is
`bli-superbelief` E2(a)'s `tentLaw_l1_le`: `L m = 4 |S m|` (the program's `2|S|` is refuted
there); it instantiates this row in `TentModulus.lean` (`kernelLip_tent`,
`bli_update_tierA_modulus_tent`), a module not imported by the root (a cross-package import —
the orchestrator's call at consolidation). Here `KernelLip` is an explicit hypothesis.
Source: [[bli-program]] §3.5 (iii); mandate M6 (modulus form)
Kind: P
Fidelity: exact (abstract skeleton; instantiated at the tent in `TentModulus.lean`)
Hyps: (a) `hQ`; (a) `hL : KernelLip sk L` (explicit); (a) syntactic -/
theorem bli_update_tierA_modulus (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) {L : ℕ → ℚ}
    (hL : KernelLip sk L) (n : ℕ) {ψ : Sentence} {l : List (ℕ × ℕ)} {s : Option Sentence}
    (hψ : tierA c (n + 1) ψ = some (l, s)) (hs : ∀ φ, s = some φ → NoFutureState c n φ) :
    |bliHistory Q 𝓜 sk c (n + 1) ψ *
        bliHistory Q 𝓜 sk c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) -
      bliHistory Q 𝓜 sk c n (ψ ⋏ stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1)))|
      ≤ bliHistory Q 𝓜 sk c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) *
          ((L (n + 1) : ℝ) / (2 * (𝓜.d (n + 1) : ℝ))) := by
  obtain ⟨hp, hne, hsmall⟩ := tierA_eq_some c hψ
  have hl : ∀ x ∈ l, n + 1 < x.1 := fun x hx => (parse_entries c hp x hx).1
  simp only [bliStateSystem_actual]
  set A := actualState smallIndex 𝓜.d Q (n + 1) with hAdef
  set t' := actualTable smallIndex Q (n + 1) with ht'def
  have hA : A ∈ grid smallIndex 𝓜.d (n + 1) := actualState_mem_grid
  set a := c.code (n + 1) A with hadef
  have hq : a ∈ c.states (n + 1) := c.code_mem_states hA
  have hp0 : parse c n ψ = some (l, s) := parse_of_parse_succ c hp hs
  have hpσ : parse c n (stateAtom (n + 1) a) = some ([(n + 1, a)], none) :=
    parse_stateAtom c (Nat.lt_succ_self n) hq
  have hfut : hasFutureAtom c n (ψ ⋏ stateAtom (n + 1) a) = true := by
    rw [hasFutureAtom_and, hasFutureAtom_stateAtom, decide_eq_true ⟨Nat.lt_succ_self n, hq⟩]
    simp
  have hpand : parse c n (ψ ⋏ stateAtom (n + 1) a) = some (l ++ [(n + 1, a)], s) := by
    rw [parse_and_of_parse c hp0 hpσ hfut (stateAtom_ne_top _ _)]
    cases s with
    | none => rfl
    | some φ => rfl
  have htand : tierA c n (ψ ⋏ stateAtom (n + 1) a) = some (l ++ [(n + 1, a)], s) := by
    refine tierA_of_parse c hpand (by simp) ?_
    rw [latestEntry_append_singleton hne _ (fun x hx => (hl x hx).le)]
    exact hsmall
  unfold bliHistory
  rw [bliPrice_of_tierA (not_smallOn_of_tierA c hψ) hψ,
    bliPrice_of_tierA (not_smallOn_and_of_right (not_smallOn_stateAtom c (Nat.lt_succ_self n) hq)) htand,
    bliPrice_state c sk Q n hA]
  have hcons : Consistent (l ++ [(n + 1, a)]) ↔ Consistent l :=
    consistent_append_singleton_iff (fun x hx => (hl x hx).ne')
  -- the ℓ¹ step in ℚ
  have hε : ∀ φ, |t' φ - A φ| ≤ 1 / (2 * (𝓜.d (n + 1) : ℚ)) := by
    intro φ
    rw [abs_sub_comm]
    exact actualState_err (𝒮 := smallIndex) (d := 𝓜.d) hQ (𝓜.d_pos (n + 1)) φ
  have hlip := chainProbH_lipschitz c sk hL l (n + 1) (actualTable_inUnit hQ) (inUnit_of_mem_grid hA)
    hε ((latestEntry l).1 - (n + 1))
  have hlaw : 0 ≤ (sk.κ n).law (actualTable smallIndex Q n) A := (sk.κ n).law_nonneg _ _
  have hLε : 0 ≤ L (n + 1) * (1 / (2 * (𝓜.d (n + 1) : ℚ))) :=
    le_trans (abs_nonneg _) hlip
  by_cases hc : Consistent l
  · rw [tierAPrice_of_consistent c sk _ hc, tierAPrice_of_consistent c sk _ (hcons.mpr hc),
      chainMass_append_actual c sk _ hA hne hl, smallFactor_append_actual c a hne hl]
    have hf := smallFactor_mem_Icc c l s
    -- rational inequality
    have key : |chainMass sk c (n + 1) t' l * smallFactor c l s * (sk.κ n).law (actualTable smallIndex Q n) A -
        (sk.κ n).law (actualTable smallIndex Q n) A * chainMass sk c (n + 1) A l * smallFactor c l s|
        ≤ (sk.κ n).law (actualTable smallIndex Q n) A * (L (n + 1) / (2 * (𝓜.d (n + 1) : ℚ))) := by
      have e : chainMass sk c (n + 1) t' l * smallFactor c l s * (sk.κ n).law (actualTable smallIndex Q n) A -
          (sk.κ n).law (actualTable smallIndex Q n) A * chainMass sk c (n + 1) A l * smallFactor c l s =
          ((sk.κ n).law (actualTable smallIndex Q n) A * smallFactor c l s) *
            (chainMass sk c (n + 1) t' l - chainMass sk c (n + 1) A l) := by ring
      rw [e, abs_mul, abs_of_nonneg (mul_nonneg hlaw hf.1)]
      unfold chainMass
      calc (sk.κ n).law (actualTable smallIndex Q n) A * smallFactor c l s *
            |chainProbH sk c l (n + 1) t' ((latestEntry l).1 - (n + 1)) -
              chainProbH sk c l (n + 1) A ((latestEntry l).1 - (n + 1))|
          ≤ (sk.κ n).law (actualTable smallIndex Q n) A * smallFactor c l s *
              (L (n + 1) * (1 / (2 * (𝓜.d (n + 1) : ℚ)))) :=
            mul_le_mul_of_nonneg_left hlip (mul_nonneg hlaw hf.1)
        _ ≤ (sk.κ n).law (actualTable smallIndex Q n) A * 1 *
              (L (n + 1) * (1 / (2 * (𝓜.d (n + 1) : ℚ)))) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf.2 hlaw) hLε
        _ = (sk.κ n).law (actualTable smallIndex Q n) A * (L (n + 1) / (2 * (𝓜.d (n + 1) : ℚ))) := by
            ring
    obtain ⟨hl', hr'⟩ := abs_le.mp key
    have hl'' := (Rat.cast_le (K := ℝ)).mpr hl'
    have hr'' := (Rat.cast_le (K := ℝ)).mpr hr'
    push_cast at hl'' hr'' ⊢
    rw [abs_le]
    constructor <;> linarith
  · rw [tierAPrice_of_not_consistent c sk _ hc,
      tierAPrice_of_not_consistent c sk _ (fun h => hc (hcons.mp h))]
    push_cast
    simp only [zero_mul, sub_zero, abs_zero]
    have hLε' : (0 : ℝ) ≤ (L (n + 1) : ℝ) / (2 * (𝓜.d (n + 1) : ℝ)) := by
      have := (Rat.cast_le (K := ℝ)).mpr hLε
      push_cast at this
      rwa [mul_one_div] at this
    exact mul_nonneg (by exact_mod_cast hlaw) hLε'

end Cleanroom.Bli.BliTrajectory
