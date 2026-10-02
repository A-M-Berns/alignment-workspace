import Cleanroom.Li.LiProjection.Mirror
import Cleanroom.Li.LiProjection.Certificate
import Cleanroom.Li.LiProjection.Market

/-!
# `li-projection` · LemmaA: the Projection Lemma over FAF's criterion (T1.6)

Package `Cleanroom.Li.LiProjection` ([[li-projection-mandate]]), file 4 of the layout — the
flagship. **Lemma A** (dose-response §6.1, "independent-atom extension, finitely many jumps"): for a
logical inductor `P` over `DP`, an atom `u` fresh for `DP`, and an eventually constant, efficiently
computable weight `q` with values in `[η, 1 − η]`, the projected market `project P u q` is again a
logical inductor over `DP`.

The proof is the note's. Suppose an efficiently computable `T` exploits `project P u q`, with its
plausible assessments bounded below by `L₀`. Form `S := λ T^⊤ + (1 − λ) T^⊥` with `λ := q N` the
eventual value. By the combined mirror identity (`Mirror.lean`)
`S.netWorth P W n = λ V_{(W,1),n}(T) + (1 − λ) V_{(W,0),n}(T) + Σ_{m ≤ n} (q_m − λ) D_m`, and the
correction is bounded by `C*` since only the days `m < N` contribute. Both bits are plausible at
every day (`Subst.lean`, the freshness lemma), so `S` is bounded below by `L₀ − C*` at every
plausible pair, and unbounded above because one of the coefficients `λ`, `1 − λ` is `≥ η`. So `S`
exploits `P` — contradicting `P`'s criterion, since `S` is efficiently computable by the
certificate (`Certificate.lean`). The two remaining fields of the conclusion are the computable
market (`Market.lean`) and the base process's computability.

**Status of the hypotheses.** All are (a) — nothing is cited — *except* that the efficiency of the
mirror traders rests on the two OPEN rewriter obligations of `Certificate.lean`
(`mirrorStreamRewriter`, `affineComboRewriter`); so this theorem is **proved modulo those two
`Complexity.FP` facts** and is listed with them in `li-projection-open.txt`. There are no
`hmirrorTop`/`hmirrorBot`/`hcombo` hypotheses on the statement (mandate, anson-2-028): the mirrors'
efficiency is derived from the certificate, not assumed of the trader.

**Scope clauses.** `u` fresh for `DP` (`AtomFreeProcess`, T1.2); `q` eventually constant and
efficiently computable (`MachineRatCodes`), with `η > 0` — at `q n ∈ {0, 1}` the lemma is false in
spirit, since non-dogmatism forbids `P_∞(u) ∈ {0,1}` on a never-decided atom; one-way; the base
inductor's own prices on `u`-sentences are *discarded* by `project`, not assumed anything about.
No `hworld` is needed (the note's argument never uses it, and a stage with no consistent world
makes every trader's assessment set empty).
-/

namespace Cleanroom.Li.LiProjection

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## Worlds with their own bit forced are themselves -/

lemma setAtom_eq_self_of_holds (v : PCWorld) (u : ℕ) (h : v u) : setAtom v u true = v := by
  funext a
  by_cases hau : a = u
  · rw [hau]
    show (if u = u then (true = true) else v u) = v u
    rw [if_pos rfl]
    exact propext ⟨fun _ => h, fun _ => rfl⟩
  · simp [setAtom, hau]

/-- `setAtom_eq_self_of_not_holds`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma setAtom_eq_self_of_not_holds (v : PCWorld) (u : ℕ) (h : ¬ v u) :
    setAtom v u false = v := by
  funext a
  by_cases hau : a = u
  · rw [hau]
    show (if u = u then (false = true) else v u) = v u
    rw [if_pos rfl]
    exact propext ⟨fun hf => absurd hf Bool.false_ne_true, fun hv => absurd hv h⟩
  · simp [setAtom, hau]

/-! ## The exploitation transfer -/

/-- **The economic core of Lemma A.** If `T` exploits the projected market, then
`S := λ T^⊤ + (1 − λ) T^⊥` (with `λ := q N`) exploits the base market. No efficiency is involved
here; this is the note's "bounded below / unbounded above" computation on the combined identity.
Source: [[dose-response]] §6.1 Lemma A, proof (bounded below, unbounded above)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem combo_exploits_of_exploits (P : History) (DP : DeductiveProcess) (u : ℕ)
    (hu : AtomFreeProcess u DP) (q : ℕ → ℚ) (η : ℚ) (hη : 0 < η)
    (hq : ∀ n, η ≤ q n ∧ q n ≤ 1 - η) (N : ℕ) (hjump : ∀ n, N ≤ n → q n = q N)
    (T : Trader) (hexp : T.Exploits (project P u q) DP) :
    (Trader.affineCombo (q N) (Trader.mirror u q true T) (Trader.mirror u q false T)).Exploits
      P DP := by
  classical
  obtain ⟨⟨L₀, hL₀⟩, hnotAbove⟩ := hexp
  set lam : ℚ := q N with hlam
  set C : ℝ := correctionBound T P u q lam N with hC
  have hC0 : 0 ≤ C := correctionBound_nonneg T P u q lam N
  have hcorr : ∀ n, |∑ m ∈ Finset.range (n + 1), ((q m : ℝ) - lam) * exposure T P u q m| ≤ C :=
    abs_correction_le T P u q lam N hjump
  have hηR : (0 : ℝ) < η := by exact_mod_cast hη
  have hlam_lo : (η : ℝ) ≤ lam := by exact_mod_cast (hq N).1
  have hlam_hi : (lam : ℝ) ≤ 1 - η := by exact_mod_cast (hq N).2
  have hlam0 : (0 : ℝ) ≤ lam := by linarith
  have hlam1 : (lam : ℝ) ≤ 1 := by linarith
  have hlow : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → ∀ b,
      L₀ ≤ T.netWorth (project P u q) (setAtom v u b) n := fun n v hv b =>
    hL₀ ⟨n, setAtom v u b, (consistentWith_setAtom_iff hu v b n).mp hv, rfl⟩
  refine ⟨⟨L₀ - C, ?_⟩, ?_⟩
  · rintro x ⟨n, v, hv, rfl⟩
    rw [combo_mirror_netWorth]
    have h1 := hlow n v hv true
    have h2 := hlow n v hv false
    have h3 := (abs_le.mp (hcorr n)).1
    have e1 : (lam : ℝ) * L₀ ≤ lam * T.netWorth (project P u q) (setAtom v u true) n :=
      mul_le_mul_of_nonneg_left h1 hlam0
    have e2 : (1 - (lam : ℝ)) * L₀ ≤ (1 - lam) * T.netWorth (project P u q) (setAtom v u false) n :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  · intro hAbove
    obtain ⟨B, hB⟩ := hAbove
    apply hnotAbove
    refine ⟨(|B| + |L₀| + C) / η, ?_⟩
    rintro x ⟨n, v, hv, rfl⟩
    by_contra hcon
    replace hcon := not_le.mp hcon
    have hbound0 : 0 ≤ (|B| + |L₀| + C) / η :=
      div_nonneg (by positivity) hηR.le
    have hxpos : 0 < T.netWorth (project P u q) v n := lt_of_le_of_lt hbound0 hcon
    have hηx : |B| + |L₀| + C < η * T.netWorth (project P u q) v n := by
      rwa [div_lt_iff₀ hηR, mul_comm] at hcon
    have hSB := hB ⟨n, v, hv, rfl⟩
    rw [combo_mirror_netWorth] at hSB
    have h3 := (abs_le.mp (hcorr n)).1
    have hBle : B ≤ |B| := le_abs_self B
    have hL₀le : -|L₀| ≤ L₀ := neg_abs_le L₀
    by_cases hvu : v u
    · rw [setAtom_eq_self_of_holds v u hvu] at hSB
      have h2 := hlow n v hv false
      have e2 : (1 - (lam : ℝ)) * (-|L₀|) ≤
          (1 - lam) * T.netWorth (project P u q) (setAtom v u false) n :=
        mul_le_mul_of_nonneg_left (le_trans hL₀le h2) (by linarith)
      have e3 : -|L₀| ≤ (1 - (lam : ℝ)) * (-|L₀|) := by nlinarith [abs_nonneg L₀]
      have e1 : (η : ℝ) * T.netWorth (project P u q) v n ≤ lam * T.netWorth (project P u q) v n :=
        mul_le_mul_of_nonneg_right hlam_lo hxpos.le
      linarith
    · rw [setAtom_eq_self_of_not_holds v u hvu] at hSB
      have h1 := hlow n v hv true
      have e1 : (lam : ℝ) * (-|L₀|) ≤ lam * T.netWorth (project P u q) (setAtom v u true) n :=
        mul_le_mul_of_nonneg_left (le_trans hL₀le h1) hlam0
      have e3 : -|L₀| ≤ (lam : ℝ) * (-|L₀|) := by nlinarith [abs_nonneg L₀]
      have e2 : (η : ℝ) * T.netWorth (project P u q) v n ≤
          (1 - lam) * T.netWorth (project P u q) v n :=
        mul_le_mul_of_nonneg_right (by linarith) hxpos.le
      linarith

/-! ## T1.6 Lemma A -/

/-- **Lemma A (the Projection Lemma).** For `[IsLogicalInductor P DP]`, `u` fresh for `DP`, and an
eventually constant, efficiently computable weight `q` with values in `[η, 1 − η]`, `η > 0`, the
projected market `project P u q` is a logical inductor over `DP`. Composition: the computable
market (T1.3, `Market.lean`), the base process's computability, and the exploitation transfer
`combo_exploits_of_exploits` closed by the criterion of `P` against the efficiently computable
combined mirror (T1.5, `Certificate.lean`).
Source: [[dose-response]] §6.1 Lemma A; chat 09 L5773–5811; [[self-referential-settlement-target]] §5.4; [[deference-in-logical-induction-v6]] §4.5; [[anson-inventory]] 036
Kind: C
Fidelity: exact (for the eventually-constant `q` the note proves; FAF's `Exploits` is tex:901 verbatim, day-indexed over `pcworlds(D n)`, the zip's quantifier). Hypothesis (i): `q` is a *fixed* e.c. sequence (`MachineRatCodes q`, efficient on the unary day), not a ledger-reading policy; the note's `q^{(i)}_n = Φ(m^{(i)}_{N*})` is covered only as the composition of a computable published table with an e.c. map, which is not stated here (the realized run is a single sequence, as the note says). Scope: `u` fresh for `DP`; `q` eventually constant and e.c.; `η > 0` (non-dogmatism forbids `P_∞(u) ∈ {0,1}`); one-way; the base inductor's prices on `u`-sentences are discarded, not assumed anything about; no `hworld` needed
Hyps: (a) throughout — nothing cited; the mirrors' efficiency rests on the OPEN `Complexity.FP` facts `mirrorStreamRewriter`/`affineComboRewriter` (`Certificate.lean`), so the theorem is proved modulo them and listed in `li-projection-open.txt` -/
theorem project_isLogicalInductor (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (u : ℕ) (hu : AtomFreeProcess u DP)
    (q : ℕ → ℚ) (η : ℚ) (hη : 0 < η) (hq : ∀ n, η ≤ q n ∧ q n ≤ 1 - η)
    (hqec : MachineRatCodes q) (N : ℕ) (hjump : ∀ n, N ≤ n → q n = q N) :
    IsLogicalInductor (project P u q) DP where
  marketComputable :=
    computableMarket_project_ofMachineRatCodes P u q hLI.marketComputable hqec
      (fun n => ⟨by linarith [(hq n).1], by linarith [(hq n).2]⟩)
  processComputable := hLI.processComputable
  noExploit := by
    intro T hT hexp
    have hS : EfficientlyComputable
        (Trader.affineCombo (q N) (Trader.mirror u q true T) (Trader.mirror u q false T)) :=
      EfficientlyComputable.affineCombo (affineComboRewriter (q N))
        (EfficientlyComputable.mirror (mirrorStreamRewriter u q hqec true) hT)
        (EfficientlyComputable.mirror (mirrorStreamRewriter u q hqec false) hT)
    exact hLI.noExploit _ hS (combo_exploits_of_exploits P DP u hu q η hη hq N hjump T hexp)

/-- **Lemma A at a constant weight** `q ≡ c`, `c ∈ (0,1)` rational: the form T2 uses.
Source: [[dose-response]] §6.1 Lemma A (the `N* = 0` case)
Kind: C
Fidelity: exact
Hyps: (a); rests on the OPEN certificate as `project_isLogicalInductor` does -/
theorem project_const_isLogicalInductor (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (u : ℕ) (hu : AtomFreeProcess u DP) (c : ℚ) (hc0 : 0 < c)
    (hc1 : c < 1) : IsLogicalInductor (project P u (fun _ => c)) DP :=
  project_isLogicalInductor P DP u hu (fun _ => c) (min c (1 - c))
    (lt_min hc0 (by linarith))
    (fun _ => ⟨min_le_left _ _, by linarith [min_le_right c (1 - c)]⟩)
    (MachineRatCodes.const c) 0 (fun _ _ => rfl)

end Cleanroom.Li.LiProjection
