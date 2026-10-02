import Cleanroom.Bli.BliMeasure.Measure

/-!
# `bli-measure` · Bayes: exact total Bayesian update, every sentence (target 3, the flagship)

`b3_TB`: `bli-found`'s `TB` — `𝐏_{n+1}(ψ) · 𝐏_n(σ_{n+1}) = 𝐏_n(ψ ⋏ σ_{n+1})` for **every** sentence
`ψ`, with `σ_{n+1} := ⌜𝑸_{n+1} = actual (n+1)⌝` — **the statement `bli-trajectory` refutes for
B1** (`Refutations.tb_refuted`). Proof: `𝐏_n(ψ ⋏ σ)` at horizon `h+1` decomposes at the front
(`sum_ctrajGrid_cons`, `ctrajLaw_cons`); the `σ`-indicator kills every first table but
`roundedTable (n+1)` (`eval_b3Bits_cons_sigma`, injectivity of the coding); on that branch the
B3 world of `(n, h+1, cons (rt (n+1)) τ')` **is** the B3 world of `(n+1, h, τ')`
(`b3Bits_cons_actual`: the realized-past convention at day `n+1` is exactly what conditioning on
`σ` fixes); the base worlds are the last table's vector in both; the horizons align by
`b3History_eq`. `𝐏_{n+1}` is **not** defined as a conditional of `𝐏_n` — it restarts from
`actual (n+1)`, which comes from the base's day-`(n+1)` measure independently (mandate trap);
the identity is a theorem about two independently defined objects. No positivity is needed.

Corollaries: the ratio form under positivity (`b3_bayesRatio`, `/` on `ℝ`), `BayesRatio` for
every `ψ`, `TB_on` for any scope.
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliFound Cleanroom.Bli.BliTrajectory

variable {DP : DeductiveProcess} (base : CoherentBase DP) (𝓜 : Mesh)

/-- A state atom is the atom of its fresh code.
Source: none: infrastructure (`bli-trajectory` `Parser.stateAtom_eq_atom`, restated)
Kind: L
Fidelity: n/a -/
lemma stateAtom_eq_atom' (m q : ℕ) :
    stateAtom m q = Formula.atom (freshAtomCode stateFamily (Nat.pair m q)) := rfl

/-! ## The next-day state atom at horizon one -/

/-- A candidate's day-`(n+1)` state atom is covered at horizon `1` from day `n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma covers_stateAtom_succ (n : ℕ) {q : ℕ} (hq : q ∈ wstates base.𝔅 𝓜 (n + 1)) :
    Covers base 𝓜 n 1 (stateAtom (n + 1) q) := by
  intro a ha
  rw [stateAtom_eq_atom', sentenceAtomCodes_atom, Finset.mem_singleton] at ha
  subst ha
  have hs := sysState_of_mem base 𝓜 hq
  constructor
  · intro m q' h
    rw [hs] at h
    have := Option.some.inj h
    rw [Prod.mk.injEq] at this
    omega
  · intro h; rw [hs] at h; cases h

/-- The B3 world at horizon one (first table `Q`) holds a candidate's day-`(n+1)` atom iff the
candidate is `Q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eval_b3Bits_one_stateAtom (n : ℕ) {Q : Table (wIndex base.𝔅.B) (n + 1)}
    (hQ : Q ∈ cgrid base.𝔅 𝓜 (n + 1)) (v : BoolPCWorld) {q : ℕ} (hq : q ∈ wstates base.𝔅 𝓜 (n + 1)) :
    eval (b3Bits base 𝓜 n 1 (Traj.cons Q PUnit.unit) v) (stateAtom (n + 1) q) =
      decide (Q = wdecode base.𝔅 𝓜 (n + 1) q) := by
  rw [eval_b3Bits_stateAtom, b3Bits_future base 𝓜 (sysState_of_mem base 𝓜 hq) (by omega) (by omega),
    Traj.day_cons_first]
  apply decide_eq_decide.mpr
  constructor
  · intro h
    rw [h, wdecode_wcode base.𝔅 𝓜 hQ]
  · intro h
    rw [h, wcode_wdecode base.𝔅 𝓜 hq]

/-- **The superbelief in a candidate is the kernel's mass**: `𝐏_n(⌜𝑸_{n+1} = q⌝)` at horizon one is
the face kernel's law from the rounded table at the decoded candidate.
Source: [[bli-measure-mandate]] target 2 (`FS`), target 3 (`𝐏_n(σ)`)
Kind: L
Fidelity: exact -/
theorem b3Mass_one_stateAtom (n : ℕ) {q : ℕ} (hq : q ∈ wstates base.𝔅 𝓜 (n + 1)) :
    b3Mass base 𝓜 n 1 (stateAtom (n + 1) q) =
      ((faceSkeleton base.𝔅 𝓜).κ n).law (roundedTable base 𝓜 n) (wdecode base.𝔅 𝓜 (n + 1) q) := by
  unfold b3Mass
  rw [sum_ctrajGrid_cons n 0]
  simp only [sum_ctrajGrid_zero]
  have hterm : ∀ Q ∈ cgrid base.𝔅 𝓜 (n + 1),
      ∑ u : FiniteWorld (base.𝔅.B (n + 0 + 1)),
        b3Weight base 𝓜 n (0 + 1) (Traj.cons Q PUnit.unit) u *
          (if eval (b3Bits base 𝓜 n (0 + 1) (Traj.cons Q PUnit.unit) u.toBoolPCWorld)
              (stateAtom (n + 1) q) then 1 else 0) =
        if Q = wdecode base.𝔅 𝓜 (n + 1) q then
          ((faceSkeleton base.𝔅 𝓜).κ n).law (roundedTable base 𝓜 n) Q else 0 := by
    intro Q hQ
    have hw : ∀ u : FiniteWorld (base.𝔅.B (n + 0 + 1)),
        b3Weight base 𝓜 n (0 + 1) (Traj.cons Q PUnit.unit) u =
          ((faceSkeleton base.𝔅 𝓜).κ n).law (roundedTable base 𝓜 n) Q * Q (wcSelf (n + 1) u) := by
      intro u
      unfold b3Weight
      rw [ctrajLaw_cons, ctrajLaw_zero, mul_one]
      rfl
    simp only [hw, eval_b3Bits_one_stateAtom base 𝓜 n hQ _ hq, decide_eq_true_eq]
    by_cases hQq : Q = wdecode base.𝔅 𝓜 (n + 1) q
    · subst hQq
      simp only [if_pos trivial, mul_one]
      rw [← Finset.mul_sum]
      have : ∑ u : FiniteWorld (base.𝔅.B (n + 1)),
          (wdecode base.𝔅 𝓜 (n + 1) q) (wcSelf (n + 1) u) = 1 :=
        vecOf_sum base.𝔅 𝓜 hQ
      rw [this, mul_one]
    · simp only [if_neg hQq, mul_zero, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  rw [if_pos (wdecode_mem_cgrid base.𝔅 𝓜 hq)]

/-- **`𝐏_n` of a candidate's next-state atom** is the kernel's mass (as a real).
Source: [[bli-measure-mandate]] target 2 (`FS`), target 3
Kind: L
Fidelity: exact -/
theorem b3History_stateAtom_succ (n : ℕ) {q : ℕ} (hq : q ∈ wstates base.𝔅 𝓜 (n + 1)) :
    b3History base 𝓜 n (stateAtom (n + 1) q) =
      (((faceSkeleton base.𝔅 𝓜).κ n).law (roundedTable base 𝓜 n) (wdecode base.𝔅 𝓜 (n + 1) q) : ℝ) := by
  rw [b3History_eq base 𝓜 (covers_stateAtom_succ base 𝓜 n hq), b3Mass_one_stateAtom base 𝓜 n hq]

/-! ## The restart identity on worlds -/

/-- **The B3 world of a front-cons through the realized state is the next day's B3 world**: on
every atom, `b3Bits n (h+1) (cons (rt (n+1)) τ') v = b3Bits (n+1) h τ' v`. The realized-past
convention at day `n+1` is exactly what conditioning on `σ_{n+1}` fixes.
Source: [[bli-measure-mandate]] target 3 (proof sketch: "the past-atom convention of `b3World` at
day `n+1` is exactly what conditioning on `σ` fixes")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem b3Bits_cons_actual (n h : ℕ) (τ' : Traj (wIndex base.𝔅.B) (n + 1) h) (v : BoolPCWorld) :
    b3Bits base 𝓜 n (h + 1) (Traj.cons (roundedTable base 𝓜 (n + 1)) τ') v =
      b3Bits base 𝓜 (n + 1) h τ' v := by
  funext a
  cases hs : sysState base 𝓜 a with
  | none => rw [b3Bits_of_none base 𝓜 hs, b3Bits_of_none base 𝓜 hs]
  | some p =>
      obtain ⟨m, q⟩ := p
      by_cases h1 : m ≤ n
      · rw [b3Bits_past base 𝓜 hs h1, b3Bits_past base 𝓜 hs (by omega)]
      · by_cases h2 : m = n + 1
        · subst h2
          rw [b3Bits_future base 𝓜 hs (by omega) (by omega), b3Bits_past base 𝓜 hs le_rfl,
            Traj.day_cons_first]
          rfl
        · by_cases h3 : m ≤ n + (h + 1)
          · rw [b3Bits_future base 𝓜 hs (by omega) h3, b3Bits_future base 𝓜 hs (by omega) (by omega),
              Traj.day_cons_later]
          · rw [b3Bits_beyond base 𝓜 hs (by omega), b3Bits_beyond base 𝓜 hs (by omega)]

/-- The B3 world of a front-cons with first table `Q` holds `σ_{n+1}` iff `Q` is the rounded table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eval_b3Bits_cons_sigma (n h : ℕ) {Q : Table (wIndex base.𝔅.B) (n + 1)}
    (hQ : Q ∈ cgrid base.𝔅 𝓜 (n + 1)) (τ' : Traj (wIndex base.𝔅.B) (n + 1) h) (v : BoolPCWorld) :
    eval (b3Bits base 𝓜 n (h + 1) (Traj.cons Q τ') v) (stateAtom (n + 1) (b3Actual base 𝓜 (n + 1))) =
      decide (Q = roundedTable base 𝓜 (n + 1)) := by
  rw [eval_b3Bits_stateAtom,
    b3Bits_future base 𝓜 (sysState_of_mem base 𝓜 (b3Actual_mem base 𝓜 (n + 1))) (by omega) (by omega),
    Traj.day_cons_first]
  apply decide_eq_decide.mpr
  constructor
  · intro h
    exact (wcode_injOn base.𝔅 𝓜 (n + 1) (roundedTable_mem_cgrid base 𝓜 (n + 1)) hQ h).symm
  · intro h; rw [h]; rfl

/-- Re-indexing a world sum along a transported last table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_castDay_world {B : ℕ → ℕ}
    (F : (e : ℕ) → Table (wIndex B) e → FiniteWorld (B e) → ℚ) {e e' : ℕ} (he : e = e')
    (s : Table (wIndex B) e) :
    ∑ u : FiniteWorld (B e'), F e' (s.castDay he) u = ∑ u : FiniteWorld (B e), F e s u := by
  subst he; rfl

/-- `ψ ⋏ σ_{n+1}` is covered at horizon `h+1` from day `n` when `ψ` is covered at horizon `h` from
day `n+1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma covers_and_sigma {n h : ℕ} {ψ : Sentence} (hc : Covers base 𝓜 (n + 1) h ψ) :
    Covers base 𝓜 n (h + 1) (ψ ⋏ stateAtom (n + 1) (b3Actual base 𝓜 (n + 1))) := by
  intro a ha
  rw [sentenceAtomCodes_and, Finset.mem_union] at ha
  rcases ha with ha | ha
  · obtain ⟨h1, h2⟩ := hc a ha
    refine ⟨fun m q hs => by have := h1 m q hs; omega, fun hs => ?_⟩
    have := h2 hs
    rwa [show n + 1 + h = n + (h + 1) by omega] at this
  · exact covers_mono base 𝓜 (covers_stateAtom_succ base 𝓜 n (b3Actual_mem base 𝓜 (n + 1)))
      (by omega : 1 ≤ h + 1) a ha

/-- **The restart identity on masses**: the mass of `ψ ⋏ σ_{n+1}` from day `n` at horizon `h+1` is
the kernel's mass of the realized state times the mass of `ψ` from day `n+1` at horizon `h`.
Source: [[bli-measure-mandate]] target 3 (the restart identity; `bli-assemble` `chainProbH_restart`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem b3Mass_and_sigma (n h : ℕ) (ψ : Sentence) :
    b3Mass base 𝓜 n (h + 1) (ψ ⋏ stateAtom (n + 1) (b3Actual base 𝓜 (n + 1))) =
      ((faceSkeleton base.𝔅 𝓜).κ n).law (roundedTable base 𝓜 n) (roundedTable base 𝓜 (n + 1)) *
        b3Mass base 𝓜 (n + 1) h ψ := by
  set rt := roundedTable base 𝓜 n
  set rt' := roundedTable base 𝓜 (n + 1)
  set lawQ := ((faceSkeleton base.𝔅 𝓜).κ n).law rt
  unfold b3Mass
  rw [sum_ctrajGrid_cons n h]
  have hterm : ∀ Q ∈ cgrid base.𝔅 𝓜 (n + 1),
      ∑ τ' ∈ ctrajGrid (cgrid base.𝔅 𝓜) (n + 1) h, ∑ u : FiniteWorld (base.𝔅.B (n + (h + 1))),
        b3Weight base 𝓜 n (h + 1) (Traj.cons Q τ') u *
          (if eval (b3Bits base 𝓜 n (h + 1) (Traj.cons Q τ') u.toBoolPCWorld)
              (ψ ⋏ stateAtom (n + 1) (b3Actual base 𝓜 (n + 1))) then 1 else 0) =
      if Q = rt' then
        lawQ Q * ∑ τ' ∈ ctrajGrid (cgrid base.𝔅 𝓜) (n + 1) h,
          ∑ u : FiniteWorld (base.𝔅.B (n + 1 + h)), b3Weight base 𝓜 (n + 1) h τ' u *
            (if eval (b3Bits base 𝓜 (n + 1) h τ' u.toBoolPCWorld) ψ then 1 else 0)
      else 0 := by
    intro Q hQ
    by_cases hQr : Q = rt'
    · subst hQr
      rw [if_pos rfl, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro τ' _
      have hand : ∀ v : BoolPCWorld,
          eval (b3Bits base 𝓜 n (h + 1) (Traj.cons rt' τ') v)
            (ψ ⋏ stateAtom (n + 1) (b3Actual base 𝓜 (n + 1))) =
          eval (b3Bits base 𝓜 (n + 1) h τ' v) ψ := by
        intro v
        show (eval _ ψ && eval _ _) = _
        rw [eval_b3Bits_cons_sigma base 𝓜 n h hQ τ' v, decide_eq_true rfl, Bool.and_true,
          b3Bits_cons_actual]
      simp only [hand, b3Weight, ctrajLaw_cons, Traj.last_cons]
      rw [sum_castDay_world (fun e s u => lawQ rt' * ctrajLaw (faceSkeleton base.𝔅 𝓜) (n + 1) h rt' τ' *
          s (wcSelf e u) * (if eval (b3Bits base 𝓜 (n + 1) h τ' u.toBoolPCWorld) ψ then 1 else 0))
        (by omega : n + 1 + h = n + (h + 1)) (τ'.last rt')]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    · rw [if_neg hQr]
      apply Finset.sum_eq_zero
      intro τ' _
      apply Finset.sum_eq_zero
      intro u _
      have : eval (b3Bits base 𝓜 n (h + 1) (Traj.cons Q τ') u.toBoolPCWorld)
          (ψ ⋏ stateAtom (n + 1) (b3Actual base 𝓜 (n + 1))) = false := by
        show (eval _ ψ && eval _ _) = false
        rw [eval_b3Bits_cons_sigma base 𝓜 n h hQ τ' _, decide_eq_false hQr, Bool.and_false]
      rw [this]
      simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos (roundedTable_mem_cgrid base 𝓜 (n + 1))]

/-! ## The flagship -/

/-- **T3 — exact total Bayesian update on every sentence** (`bli-found`'s `TB`, product form):
`𝐏_{n+1}(ψ) · 𝐏_n(⌜𝑸_{n+1} = actual (n+1)⌝) = 𝐏_n(ψ ⋏ ⌜𝑸_{n+1} = actual (n+1)⌝)` for every `n` and
**every** sentence `ψ` — the statement `bli-trajectory` refutes for B1 (`tb_refuted`, over B1's
table states; here over the variant world-vector state system, F1). `𝐏_{n+1}` is the chain
restarted from the rounded day-`(n+1)` table (which comes from the base's day-`(n+1)` measure,
not from `𝐏_n`); `𝐏_n(· ⋏ σ)` is the chain through that table. No positivity needed. **Read it as
an identity of the restart architecture**: it has no hypothesis and holds for every base and
every mesh (point-mass meshes and dogmatic bases included) — the restart from `actual (n+1)` with
the same stage-free kernel is what Appendix B asks of the update rule; non-degeneracy is the
witness's job (`paper_TB_witness`, N+).
Source: [[bli-measure-mandate]] target 3; Appendix B (`main.tex:440`); bli-slides-048;
[[bli-program-construction]] §2.7
Kind: P
Fidelity: exact (over the variant state system, F1)
Hyps: (a) none -/
theorem b3_TB : TB (b3StateSystem base 𝓜) (b3History base 𝓜) := by
  intro n ψ
  rw [b3StateSystem_actual]
  have hc := covers_hor base 𝓜 (n + 1) ψ
  rw [b3History_eq base 𝓜 hc,
    b3History_eq base 𝓜 (covers_stateAtom_succ base 𝓜 n (b3Actual_mem base 𝓜 (n + 1))),
    b3History_eq base 𝓜 (covers_and_sigma base 𝓜 hc), ← Rat.cast_mul]
  congr 1
  rw [b3Mass_one_stateAtom base 𝓜 n (b3Actual_mem base 𝓜 (n + 1)), wdecode_b3Actual,
    b3Mass_and_sigma, mul_comm]

/-- **The ratio form under positivity**, `/` on `ℝ`, exact (contrast B1's `≤ 1/(2d)`,
`bli-trajectory` `bli_update_small_ratio`): `𝐏_{n+1}(ψ) = 𝐏_n(ψ ⋏ σ) / 𝐏_n(σ)` whenever `𝐏_n(σ) > 0`.
Source: [[bli-measure-mandate]] target 3 (T3 ratio form); Appendix B (`main.tex:440`)
Kind: C
Fidelity: exact
Hyps: (a) `hpos` (positivity of the realized next state, explicit) -/
theorem b3_bayesRatio (n : ℕ) (ψ : Sentence)
    (hpos : 0 < b3History base 𝓜 n (stateAtom (n + 1) (b3Actual base 𝓜 (n + 1)))) :
    b3History base 𝓜 (n + 1) ψ =
      b3History base 𝓜 n (ψ ⋏ stateAtom (n + 1) (b3Actual base 𝓜 (n + 1))) /
        b3History base 𝓜 n (stateAtom (n + 1) (b3Actual base 𝓜 (n + 1))) := by
  have h := b3_TB base 𝓜 n ψ
  rw [b3StateSystem_actual] at h
  rw [eq_div_iff hpos.ne']
  exact h

/-- **`BayesRatio` for every sentence** (`bli-trajectory`'s predicate at every `(n, ψ)`).
Source: [[bli-measure-mandate]] target 3 (`BayesRatio S P n ψ` for every `ψ`)
Kind: C
Fidelity: exact
Hyps: (a) none (positivity is the predicate's antecedent) -/
theorem b3_bayesRatio_all (n : ℕ) (ψ : Sentence) :
    BayesRatio (b3StateSystem base 𝓜) (b3History base 𝓜) n ψ := by
  intro hpos
  rw [b3StateSystem_actual] at hpos ⊢
  exact b3_bayesRatio base 𝓜 n ψ hpos

/-- **`TB_on` for every scope** (T4 on the state algebra is the instance at the state-algebra
scope; B1 had it on Tier A only, on the denominator grid).
Source: [[bli-measure-mandate]] target 3 (T4); `bli-trajectory` `bli_TB_on_tierA`
Kind: C
Fidelity: stronger: every scope
Hyps: (a) none -/
theorem b3_TB_on (A : ℕ → Sentence → Prop) : TB_on A (b3StateSystem base 𝓜) (b3History base 𝓜) :=
  fun n ψ _ => b3_TB base 𝓜 n ψ

end Cleanroom.Bli.BliMeasure
