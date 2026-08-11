/-
  Kernel-checked core of LEMMA A — the independent-atom extension of
  `dose-response.md` §6.1, finitely-many-jumps case: extending a logical
  inductor to one fresh atom `u` by the affine marginal
      P_n(φ) := q_n · P̄_n(α_φ) + (1 − q_n) · P̄_n(β_φ)
  preserves the no-exploitation criterion, provided `q` is interior and
  eventually constant.

  MODELING (agreed design; the flags below are the trust surface):
  • Sentences are opaque: an `AtomExtension` bundles the base/extended sentence
    types, the substitutions α, β, the base embedding ι, the atom `u`, and the
    equations α∘ι = β∘ι = id, α(u) = ⊤, β(u) = ⊥.  No deduction is modeled.
  • FLAG (the one modeling substitution): extended plausible worlds are TAKEN
    to be `𝒲 × Bool` with indicator (W,b)(φ) = ind W (α_φ or β_φ) — the note
    derives this from "the deductive process never mentions u"; here it is the
    definition `extInd`, and its day-indexed companion `extPC` (base-plausible
    at day N × free bit — both bits stay plausible forever, same flag).
  • Traders are day-indexed finitely-supported trades (`ℕ → σ →₀ ℝ`); the
    mirror traders T^⊤, T^⊥ are CONSTRUCTED (`Finsupp.mapDomain`) and the §6.1
    value identities are PROVED — the finite accounting that is the point of
    the module.  Trade *strategies* (continuity in prices, computability, poly
    overhead) are not modeled: they live in the provenance of the closure
    hypotheses below, exactly as [LI 3.4.3–3.4.5] are cited in the note.
  • The trader classes are abstract sets; [LI 3.4.3–3.4.5] enter as the named
    closure hypotheses `hmirrorTop`/`hmirrorBot`/`hcombo`, and the LIC for the
    base market [LI 3.5.1] as `hLIC`.  The criterion (`Exploits`) is DAY-INDEXED:
    values through day N are tested only in worlds plausible at day N (`PC N`,
    the paper's 𝒫𝒞(D_N)), matching [LI 3.5.1]'s quantification; a static index
    set is the constant-`PC` instance.  The conclusion is the
    extended-market LIC — "the extension of an inductor is an inductor", at
    criterion level.  A realizability guard (`criterion_setup_realizable`)
    exhibits the full hypothesis package satisfied non-vacuously, with `hLIC`
    proved on the one-world market rather than assumed.
  • Marginal facts: on the base language the extension IS P̄ (proved,
    definitional); the atom's price satisfies P_n(u) → q_∞ given the named
    hypotheses P̄_n(⊤) → 1, P̄_n(⊥) → 0 ([LI 4.1.1 Convergence] + [LI 4.1.2
    Limit Coherence]).  This is the conclusion T2(a) consumes and the form the
    note displays; the exact `P_n(u) = q_n` would need exact price
    normalization, which LI markets do not promise.
  • SIGN NOTE: with the value convention  t·(𝟙_W − price)  and the note's
    D_n := Σ_φ t_{n,φ}(P̄_n(α_φ) − P̄_n(β_φ)), the kernel-checked identities come
    out  V(T^⊤) = V_{(W,1)}(T) − Σ(1−q_n)D_n  and  V(T^⊥) = V_{(W,0)}(T) + Σ q_n D_n
    — matching the note's §6.1 displays (the opposite signs, consistent under
    D ↦ −D and easy to write down in prose, do not survive the accounting).

  No `sorry`; axiom audit at the end.

  Map to the note (§6.1):
    AtomExtension               the extended-language setup of §2.1
    extPrice                    the Lemma-A marginal  q·P̄(α) + (1−q)·P̄(β)
    extInd / extPC              plausible worlds (W, b): indicators, day-N sets
    mirrorTop / mirrorBot       the base traders T^⊤, T^⊥
    combo                       S := λT^⊤ + (1−λ)T^⊥
    exposure                    D_n (up to the sign note above)
    value_mirrorTop, value_mirrorBot        the §6.1 value identities (proved)
    value_extension_identity    V_W(S) = λV_{(W,1)} + (1−λ)V_{(W,0)} + Σ(q_n−λ)D_n
    bounded_partial_sums_of_eventually_zero   the finitely-many-jumps correction bound
    extension_preserves_criterion   LEMMA A (criterion preservation)
    value_one_world / one_world_no_exploitation / criterion_setup_realizable
                                the realizability guard for Lemma A's package
    extPrice_base               P_n ∘ ι = P̄_n (restriction identity)
    atom_price_tendsto          P_n(u) → q_∞ (the T2(a) input)
-/
import Mathlib

open Filter Topology

namespace IndependentAtom

/-- The atom-extension syntax: base sentences `Φb`, extended sentences `Φ`, the two
    substitutions `α := ·[u:=⊤]`, `β := ·[u:=⊥]`, the embedding of the base language,
    the fresh atom, and the equations they satisfy (§2.1 of the note). -/
structure AtomExtension (Φb Φ : Type*) where
  α : Φ → Φb
  β : Φ → Φb
  ι : Φb → Φ
  u : Φ
  top : Φb
  bot : Φb
  α_ι : ∀ ψ, α (ι ψ) = ψ
  β_ι : ∀ ψ, β (ι ψ) = ψ
  α_u : α u = top
  β_u : β u = bot

/-- Non-vacuity of the setup: every base language with distinguished ⊤, ⊥ admits an
    atom extension (adjoin one fresh sentence; substitutions send it to ⊤ resp. ⊥). -/
def toyExtension (Φb : Type*) (top bot : Φb) : AtomExtension Φb (Φb ⊕ Unit) where
  α := Sum.elim id fun _ => top
  β := Sum.elim id fun _ => bot
  ι := Sum.inl
  u := Sum.inr ()
  top := top
  bot := bot
  α_ι := fun _ => rfl
  β_ι := fun _ => rfl
  α_u := rfl
  β_u := rfl

section Market

variable {σ : Type*}

/-- One day's banked value: the trade `τ` settles at indicator `J` having paid the
    day's prices `π`:  Σ_φ τ_φ · (J(φ) − π(φ)). -/
def dayValue (π J : σ → ℝ) (τ : σ →₀ ℝ) : ℝ :=
  τ.sum fun φ t => t * (J φ - π φ)

/-- The trader's banked value through day `N` (the LI accounting of §6.1). -/
def value (P : ℕ → σ → ℝ) (J : σ → ℝ) (T : ℕ → σ →₀ ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, dayValue (P n) J (T n)

/-- Exploitation [LI 3.5.1], **day-indexed**: `PC N` is the index set of worlds
    plausible AT DAY N (the paper's 𝒫𝒞(D_N)), so the criterion tests the value of
    the trade history through day `N` only in worlds still plausible on day `N` —
    plausible value bounded below, unbounded above, over pairs `(N, W ∈ PC N)`.
    (A static form — one fixed index set for all days — is the constant-`PC`
    instance.) -/
def Exploits {ι : Type*} (P : ℕ → σ → ℝ) (PC : ℕ → Set ι) (J : ι → σ → ℝ)
    (T : ℕ → σ →₀ ℝ) : Prop :=
  (∃ L, ∀ N, ∀ i ∈ PC N, -L ≤ value P (J i) T N) ∧
    (∀ B, ∃ N, ∃ i ∈ PC N, B < value P (J i) T N)

end Market

variable {Φb Φ : Type*} (E : AtomExtension Φb Φ)

/-- The Lemma-A extension: extended prices are the `q`-mixture of base prices at the
    two substitutions. -/
def extPrice (P : ℕ → Φb → ℝ) (q : ℕ → ℝ) : ℕ → Φ → ℝ :=
  fun n φ => q n * P n (E.α φ) + (1 - q n) * P n (E.β φ)

/-- Extended plausible worlds are pairs (base world, `u`-bit) — the modeling FLAG of
    the header: the note derives this from freshness of `u`, here it is definitional. -/
def extInd {𝒲 : Type*} (ind : 𝒲 → Φb → ℝ) : 𝒲 × Bool → Φ → ℝ :=
  fun Wb φ => ind Wb.1 (cond Wb.2 (E.α φ) (E.β φ))

/-- Extended plausibility, day-indexed: at every day the plausible extended worlds
    are the plausible base worlds with a FREE `u`-bit — `u` is never decided by any
    deductive process, so both bits stay plausible forever.  Like `extInd`, this
    renders the note's freshness argument as a definition (the same modeling FLAG). -/
def extPC {𝒲 : Type*} (PC : ℕ → Set 𝒲) : ℕ → Set (𝒲 × Bool) :=
  fun N => {Wb | Wb.1 ∈ PC N}

theorem mem_extPC {𝒲 : Type*} (PC : ℕ → Set 𝒲) (N : ℕ) (W : 𝒲) (b : Bool) :
    (W, b) ∈ extPC PC N ↔ W ∈ PC N := Iff.rfl

/-- The mirror trader T^⊤: execute the day's trades on the α-substituted sentences. -/
noncomputable def mirrorTop (T : ℕ → Φ →₀ ℝ) : ℕ → Φb →₀ ℝ :=
  fun n => Finsupp.mapDomain E.α (T n)

/-- The mirror trader T^⊥. -/
noncomputable def mirrorBot (T : ℕ → Φ →₀ ℝ) : ℕ → Φb →₀ ℝ :=
  fun n => Finsupp.mapDomain E.β (T n)

/-- The affine combination S := a·T₁ + (1−a)·T₂ of base traders [LI 3.4.4]. -/
noncomputable def combo {σ : Type*} (a : ℝ) (T₁ T₂ : ℕ → σ →₀ ℝ) : ℕ → σ →₀ ℝ :=
  fun n => a • T₁ n + (1 - a) • T₂ n

/-- The day's exposure to the atom: D_n of §6.1 (see the SIGN NOTE in the header). -/
def exposure (π : Φb → ℝ) (τ : Φ →₀ ℝ) : ℝ :=
  τ.sum fun φ t => t * (π (E.α φ) - π (E.β φ))

/- ==================================================================================
   The §6.1 value identities, proved (the finite accounting).
   ================================================================================== -/

section Identities

variable {𝒲 : Type*} (ind : 𝒲 → Φb → ℝ) (P : ℕ → Φb → ℝ) (q : ℕ → ℝ)

private theorem dayValue_mirrorTop (π J : Φb → ℝ) (qn : ℝ) (τ : Φ →₀ ℝ) :
    dayValue π J (Finsupp.mapDomain E.α τ)
      = dayValue (fun φ => qn * π (E.α φ) + (1 - qn) * π (E.β φ))
          (fun φ => J (E.α φ)) τ
        - (1 - qn) * exposure E π τ := by
  unfold dayValue exposure
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _)
    (fun ψ t₁ t₂ => add_mul t₁ t₂ _), Finsupp.mul_sum, ← Finsupp.sum_sub]
  exact Finsupp.sum_congr fun φ _ => by ring

private theorem dayValue_mirrorBot (π J : Φb → ℝ) (qn : ℝ) (τ : Φ →₀ ℝ) :
    dayValue π J (Finsupp.mapDomain E.β τ)
      = dayValue (fun φ => qn * π (E.α φ) + (1 - qn) * π (E.β φ))
          (fun φ => J (E.β φ)) τ
        + qn * exposure E π τ := by
  unfold dayValue exposure
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _)
    (fun ψ t₁ t₂ => add_mul t₁ t₂ _), Finsupp.mul_sum, ← Finsupp.sum_add]
  exact Finsupp.sum_congr fun φ _ => by ring

private theorem dayValue_combo {σ : Type*} (π J : σ → ℝ) (a : ℝ) (τ₁ τ₂ : σ →₀ ℝ) :
    dayValue π J (a • τ₁ + (1 - a) • τ₂)
      = a * dayValue π J τ₁ + (1 - a) * dayValue π J τ₂ := by
  unfold dayValue
  rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun ψ t₁ t₂ => add_mul t₁ t₂ _),
    Finsupp.sum_smul_index (fun _ => zero_mul _),
    Finsupp.sum_smul_index (fun _ => zero_mul _),
    Finsupp.mul_sum, Finsupp.mul_sum]
  congr 1 <;> exact Finsupp.sum_congr fun φ _ => by ring

/-- **Value identity for T^⊤** (§6.1; see the header's sign note): in base world `W`,
    the mirror's banked value is T's banked value in the extended world (W, 1), minus
    the `(1−q)`-weighted exposure. -/
theorem value_mirrorTop (T : ℕ → Φ →₀ ℝ) (W : 𝒲) (N : ℕ) :
    value P (ind W) (mirrorTop E T) N
      = value (extPrice E P q) (extInd E ind (W, true)) T N
        - ∑ n ∈ Finset.range N, (1 - q n) * exposure E (P n) (T n) := by
  unfold value mirrorTop
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ =>
    dayValue_mirrorTop E (P n) (ind W) (q n) (T n)

/-- **Value identity for T^⊥.** -/
theorem value_mirrorBot (T : ℕ → Φ →₀ ℝ) (W : 𝒲) (N : ℕ) :
    value P (ind W) (mirrorBot E T) N
      = value (extPrice E P q) (extInd E ind (W, false)) T N
        + ∑ n ∈ Finset.range N, q n * exposure E (P n) (T n) := by
  unfold value mirrorBot
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ =>
    dayValue_mirrorBot E (P n) (ind W) (q n) (T n)

theorem value_combo {σ : Type*} (π : ℕ → σ → ℝ) (J : σ → ℝ) (a : ℝ)
    (T₁ T₂ : ℕ → σ →₀ ℝ) (N : ℕ) :
    value π J (combo a T₁ T₂) N = a * value π J T₁ N + (1 - a) * value π J T₂ N := by
  unfold value combo
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => dayValue_combo (π n) J a (T₁ n) (T₂ n)

/-- **The master identity** (§6.1's display for S := λT^⊤ + (1−λ)T^⊥):
    V_W(S) = λ·V_{(W,1)}(T) + (1−λ)·V_{(W,0)}(T) + Σ (q_n − λ)·D_n. -/
theorem value_extension_identity (T : ℕ → Φ →₀ ℝ) (lam : ℝ) (W : 𝒲) (N : ℕ) :
    value P (ind W) (combo lam (mirrorTop E T) (mirrorBot E T)) N
      = lam * value (extPrice E P q) (extInd E ind (W, true)) T N
        + (1 - lam) * value (extPrice E P q) (extInd E ind (W, false)) T N
        + ∑ n ∈ Finset.range N, (q n - lam) * exposure E (P n) (T n) := by
  rw [value_combo, value_mirrorTop E ind P q, value_mirrorBot E ind P q]
  have hcorr : ∑ n ∈ Finset.range N, (q n - lam) * exposure E (P n) (T n)
      = (1 - lam) * (∑ n ∈ Finset.range N, q n * exposure E (P n) (T n))
        - lam * (∑ n ∈ Finset.range N, (1 - q n) * exposure E (P n) (T n)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hcorr]
  ring

end Identities

/-- **The finitely-many-jumps correction bound**: a sequence vanishing from `N*` on has
    uniformly bounded partial sums (the "fixed finite reals" step of §6.1). -/
theorem bounded_partial_sums_of_eventually_zero (f : ℕ → ℝ) (Nstar : ℕ)
    (hf : ∀ n, Nstar ≤ n → f n = 0) :
    ∃ C, ∀ N, |∑ n ∈ Finset.range N, f n| ≤ C := by
  refine ⟨∑ n ∈ Finset.range Nstar, |f n|, fun N => ?_⟩
  rcases le_total N Nstar with h | h
  · calc |∑ n ∈ Finset.range N, f n|
        ≤ ∑ n ∈ Finset.range N, |f n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range Nstar, |f n| :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset.2 fun x hx => Finset.mem_range.2 (lt_of_lt_of_le hx h))
            (fun i _ _ => abs_nonneg _)
  · have hsplit : ∑ n ∈ Finset.range N, f n = ∑ n ∈ Finset.range Nstar, f n := by
      rw [← Finset.sum_range_add_sum_Ico f h,
        Finset.sum_eq_zero fun i hi => hf i (Finset.mem_Ico.1 hi).1, add_zero]
    rw [hsplit]
    exact Finset.abs_sum_le_sum_abs _ _

/- ==================================================================================
   LEMMA A.
   ================================================================================== -/

section LemmaA

variable {𝒲 : Type*} (ind : 𝒲 → Φb → ℝ) (P : ℕ → Φb → ℝ) (q : ℕ → ℝ)
  (η lam : ℝ) (Nstar : ℕ)

/-- **Lemma A (independent-atom extension, finitely many jumps) — criterion
    preservation.**  Hypotheses, in the note's order:
    `hη, hq1, hq2` — the marginal is interior: q_n ∈ [η, 1−η], η > 0;
    `hqc` — finitely many jumps: q_n = λ for n ≥ N* (Lemma A(ii));
    `PC` — the day-indexed plausible-world structure of the base market (𝒫𝒞(D_N));
      the extended market's plausibility is `extPC PC`, base-plausible × free bit;
    `hmirrorTop, hmirrorBot, hcombo` — NAMED trader-closure facts [LI 3.4.3–3.4.5]
      (mirrors and affine combinations stay in the classes, with poly overhead);
    `hLIC` — the LIC for the base market P̄ [LI 3.5.1].
    Conclusion: no trader in the extended class exploits the extended market — the
    Lemma-A extension satisfies the criterion. -/
theorem extension_preserves_criterion
    (hη : 0 < η) (hq1 : ∀ n, η ≤ q n) (hq2 : ∀ n, q n ≤ 1 - η)
    (hqc : ∀ n, Nstar ≤ n → q n = lam)
    (PC : ℕ → Set 𝒲)
    (𝒞b : Set (ℕ → Φb →₀ ℝ)) (𝒞e : Set (ℕ → Φ →₀ ℝ))
    (hmirrorTop : ∀ T ∈ 𝒞e, mirrorTop E T ∈ 𝒞b)
    (hmirrorBot : ∀ T ∈ 𝒞e, mirrorBot E T ∈ 𝒞b)
    (hcombo : ∀ T₁ ∈ 𝒞b, ∀ T₂ ∈ 𝒞b, combo lam T₁ T₂ ∈ 𝒞b)
    (hLIC : ∀ T ∈ 𝒞b, ¬ Exploits P PC ind T) :
    ∀ T ∈ 𝒞e, ¬ Exploits (extPrice E P q) (extPC PC) (extInd E ind) T := by
  intro T hT hexp
  obtain ⟨⟨L0, hL0⟩, hunbdd⟩ := hexp
  -- a nonnegative lower-bound constant
  set L1 : ℝ := max L0 0 with hL1def
  have hL1nonneg : 0 ≤ L1 := le_max_right _ _
  -- the extended bound, at a day-N-plausible base world and EITHER bit (both stay plausible)
  have hL1 : ∀ N (W : 𝒲) (b : Bool), W ∈ PC N →
      -L1 ≤ value (extPrice E P q) (extInd E ind (W, b)) T N :=
    fun N W b hW => le_trans (neg_le_neg (le_max_left _ _))
      (hL0 N (W, b) ((mem_extPC PC N W b).2 hW))
  -- the correction is bounded (finitely many jumps)
  obtain ⟨C, hC⟩ := bounded_partial_sums_of_eventually_zero
    (fun n => (q n - lam) * exposure E (P n) (T n)) Nstar
    (fun n hn => by
      show (q n - lam) * exposure E (P n) (T n) = 0
      rw [hqc n hn, sub_self, zero_mul])
  have hCnonneg : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  -- interiority of the limit marginal
  have hlam1 : η ≤ lam := by have := hq1 Nstar; rwa [hqc Nstar le_rfl] at this
  have hlam2 : lam ≤ 1 - η := by have := hq2 Nstar; rwa [hqc Nstar le_rfl] at this
  -- the exploiting base trader
  refine hLIC (combo lam (mirrorTop E T) (mirrorBot E T))
    (hcombo _ (hmirrorTop T hT) _ (hmirrorBot T hT))
    ⟨⟨L1 + C, fun N W hW => ?_⟩, fun B => ?_⟩
  -- (1) plausible value bounded below (at every day-N-plausible W)
  · rw [value_extension_identity]
    have hV1 := hL1 N W true hW
    have hV0 := hL1 N W false hW
    have h1 : lam * (-L1) ≤ lam * value (extPrice E P q) (extInd E ind (W, true)) T N :=
      mul_le_mul_of_nonneg_left hV1 (by linarith)
    have h0 : (1 - lam) * (-L1)
        ≤ (1 - lam) * value (extPrice E P q) (extInd E ind (W, false)) T N :=
      mul_le_mul_of_nonneg_left hV0 (by linarith)
    have hcN := (abs_le.1 (hC N)).1
    have hring : lam * (-L1) + (1 - lam) * (-L1) = -L1 := by ring
    linarith
  -- (2) plausible value unbounded above (the witnessing W stays plausible at its own N,
  --     and so does the OTHER bit — freshness of u, definitional via extPC)
  · obtain ⟨N, ⟨W, b⟩, hWb, hgt⟩ := hunbdd (max ((B + L1 + C) / η) 0)
    have hW : W ∈ PC N := (mem_extPC PC N W b).1 hWb
    have hVpos : 0 < value (extPrice E P q) (extInd E ind (W, b)) T N :=
      lt_of_le_of_lt (le_max_right _ _) hgt
    have hVgt : (B + L1 + C) / η < value (extPrice E P q) (extInd E ind (W, b)) T N :=
      lt_of_le_of_lt (le_max_left _ _) hgt
    have hηV : B + L1 + C < η * value (extPrice E P q) (extInd E ind (W, b)) T N := by
      rw [div_lt_iff₀ hη] at hVgt
      linarith [mul_comm (value (extPrice E P q) (extInd E ind (W, b)) T N) η]
    refine ⟨N, W, hW, ?_⟩
    rw [value_extension_identity]
    have hcN := (abs_le.1 (hC N)).1
    cases b with
    | true =>
        have hcoeff : η * value (extPrice E P q) (extInd E ind (W, true)) T N
            ≤ lam * value (extPrice E P q) (extInd E ind (W, true)) T N :=
          mul_le_mul_of_nonneg_right hlam1 hVpos.le
        have hother := hL1 N W false hW
        have h0 : (1 - lam) * (-L1)
            ≤ (1 - lam) * value (extPrice E P q) (extInd E ind (W, false)) T N :=
          mul_le_mul_of_nonneg_left hother (by linarith)
        have hL1bd : L1 * (1 - lam) ≤ L1 * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hL1nonneg
        nlinarith
    | false =>
        have hcoeff : η * value (extPrice E P q) (extInd E ind (W, false)) T N
            ≤ (1 - lam) * value (extPrice E P q) (extInd E ind (W, false)) T N :=
          mul_le_mul_of_nonneg_right (by linarith) hVpos.le
        have hother := hL1 N W true hW
        have h1 : lam * (-L1)
            ≤ lam * value (extPrice E P q) (extInd E ind (W, true)) T N :=
          mul_le_mul_of_nonneg_left hother (by linarith)
        have hL1bd : L1 * lam ≤ L1 * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hL1nonneg
        nlinarith

end LemmaA

/- ==================================================================================
   Realizability guard (the corpus's `cost_setup_realizable` discipline): Lemma A's
   hypothesis package is jointly satisfiable with UNIVERSAL trader classes and the
   base criterion PROVED rather than assumed — so the theorem is exercised on a
   genuine instance, not passed vacuously (e.g. by 𝒞e = ∅).
   ================================================================================== -/

section Guard

/-- On the **one-world market** — prices identically equal to the world's
    indicator — every trader's value vanishes: each day-value is `Σ t·(J − J) = 0`. -/
theorem value_one_world {σ : Type*} (J : σ → ℝ) (T : ℕ → σ →₀ ℝ) (N : ℕ) :
    value (fun _ => J) J T N = 0 := by
  unfold value
  refine Finset.sum_eq_zero fun n _ => ?_
  unfold dayValue Finsupp.sum
  exact Finset.sum_eq_zero fun φ _ => by ring

/-- No trader exploits the one-world market, under any plausibility structure and
    any class: exploitation demands values unbounded above, and every value is `0`.
    This makes `hLIC` a THEOREM on the guard instance below. -/
theorem one_world_no_exploitation {σ 𝒲 : Type*} (J : σ → ℝ) (ind : 𝒲 → σ → ℝ)
    (hind : ∀ W, ind W = J) (PC : ℕ → Set 𝒲) (T : ℕ → σ →₀ ℝ) :
    ¬ Exploits (fun _ => J) PC ind T := by
  rintro ⟨-, hunbdd⟩
  obtain ⟨N, W, -, hgt⟩ := hunbdd 0
  rw [hind W, value_one_world] at hgt
  exact lt_irrefl 0 hgt

/-- **Realizability guard for Lemma A.**  The toy atom extension over the one-world
    market (`Φb := Bool`, prices = the truth indicator of the single world), with
    `q ≡ ½`, `η = ½`, `N* = 0`, `PC ≡ univ`, and the universal trader classes,
    satisfies EVERY hypothesis of `extension_preserves_criterion` non-vacuously:
    interiority and settledness hold definitionally, the closure facts are trivial
    for `univ`, and `hLIC` is `one_world_no_exploitation` — proved, not assumed.
    The conclusion below is the theorem's, exercised on this genuine instance:
    it rules out "the package is contradictory" and "the classes are empty". -/
theorem criterion_setup_realizable :
    ∀ T ∈ (Set.univ : Set (ℕ → (Bool ⊕ Unit) →₀ ℝ)),
      ¬ Exploits
          (extPrice (toyExtension Bool true false)
            (fun _ ψ => if ψ then 1 else 0) fun _ => 1/2)
          (extPC fun _ : ℕ => (Set.univ : Set Unit))
          (extInd (toyExtension Bool true false)
            fun _ ψ => if ψ then 1 else 0) T :=
  extension_preserves_criterion (toyExtension Bool true false)
    (fun _ ψ => if ψ then 1 else 0) (fun _ ψ => if ψ then 1 else 0) (fun _ => 1/2)
    (1/2) (1/2) 0
    (by norm_num) (fun _ => le_rfl) (fun _ => by norm_num) (fun _ _ => rfl)
    (fun _ => Set.univ) Set.univ Set.univ
    (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)
    (fun _ _ _ _ => Set.mem_univ _)
    (fun T _ => one_world_no_exploitation _ _ (fun _ => rfl) _ T)

end Guard

/- ==================================================================================
   The marginal facts (what T2 consumes).
   ================================================================================== -/

section Marginals

variable (P : ℕ → Φb → ℝ) (q : ℕ → ℝ)

/-- **Restriction identity**: on the base language the extension IS the base market
    (`P_n ↾ base = P̄_n` of Lemma A). -/
theorem extPrice_base (n : ℕ) (ψ : Φb) : extPrice E P q n (E.ι ψ) = P n ψ := by
  simp only [extPrice, E.α_ι, E.β_ι]
  ring

/-- The atom's price is the `q`-mixture of the ⊤ and ⊥ prices. -/
theorem extPrice_atom (n : ℕ) :
    extPrice E P q n E.u = q n * P n E.top + (1 - q n) * P n E.bot := by
  simp only [extPrice, E.α_u, E.β_u]

/-- **The atom's destination** (the marginal T2(a) consumes — the note's display):
    `P_n(u) → q_∞`, given the eventually-constant marginal and the NAMED hypotheses
    that the base ⊤/⊥ prices converge to their values ([LI 4.1.1] + [LI 4.1.2];
    exact normalization `P̄_n(⊤) = 1` is not an LI guarantee, so the marginal is
    the limit form — exactly as the note's Lemma A states it). -/
theorem atom_price_tendsto (lam : ℝ) (Nstar : ℕ) (hqc : ∀ n, Nstar ≤ n → q n = lam)
    (htop : Tendsto (fun n => P n E.top) atTop (𝓝 1))
    (hbot : Tendsto (fun n => P n E.bot) atTop (𝓝 0)) :
    Tendsto (fun n => extPrice E P q n E.u) atTop (𝓝 lam) := by
  have hq : Tendsto q atTop (𝓝 lam) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop Nstar] with n hn
    exact (hqc n hn).symm
  have hq' : Tendsto (fun n => 1 - q n) atTop (𝓝 (1 - lam)) :=
    tendsto_const_nhds.sub hq
  have hmix := (hq.mul htop).add (hq'.mul hbot)
  simp only [extPrice_atom]
  simpa using hmix

end Marginals

end IndependentAtom

-- Axiom audit: each must rest on ONLY [propext, Classical.choice, Quot.sound] (no `sorryAx`).
#print axioms IndependentAtom.value_mirrorTop
#print axioms IndependentAtom.value_mirrorBot
#print axioms IndependentAtom.value_combo
#print axioms IndependentAtom.value_extension_identity
#print axioms IndependentAtom.bounded_partial_sums_of_eventually_zero
#print axioms IndependentAtom.extension_preserves_criterion
#print axioms IndependentAtom.mem_extPC
#print axioms IndependentAtom.value_one_world
#print axioms IndependentAtom.one_world_no_exploitation
#print axioms IndependentAtom.criterion_setup_realizable
#print axioms IndependentAtom.extPrice_base
#print axioms IndependentAtom.extPrice_atom
#print axioms IndependentAtom.atom_price_tendsto
