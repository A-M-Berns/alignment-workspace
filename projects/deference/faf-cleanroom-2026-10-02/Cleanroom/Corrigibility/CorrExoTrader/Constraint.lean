import Cleanroom.Corrigibility.CorrExoTrader.Defs
import Cleanroom.Li.LiProjection.LemmaA
import Cleanroom.Li.LiProjection.Fragments

/-!
# `corr-exo-trader` · Constraint: the one unlearnable constraint and its LIC-compatibility (T8)

Package `Cleanroom.Corrigibility.CorrExoTrader` ([[corr-exo-trader-mandate]]), file 7 of the
layout. Imports `li-projection`'s Lemma A and `Fragments`.

The source's design conclusion (line 119): "Whatever handles undetectable manipulation cannot be a
budgeted trader … It has to enter as a constraint on the market … prices of `u`-sentences are
invariant to the component of a push that is causally downstream of the agent's own actions …
Since `u` never settles, the constraint can't be exploited, so it looks compatible with the LIC,
though I haven't checked."

* **T8.1** `SelfCausedInvariant u M Hc Hu`: a market map `M : ExoDemand → History` prices every
  `u`-sentence under the demand `Hc ⊕ Hu` as under `Hu` alone — the self-caused component `Hc` is
  invisible on the `u`-fragment. **The decomposition `H = Hc ⊕ Hu` is supplied, not derived** (grade
  (c): "causally downstream of the agent's own actions" has no FAF object, corr-core-045(γ)/048).
  The extreme form `PushInvariant u M`: every demand prices the `u`-fragment as no demand does.
* **T8.2** `constraint_lic_compatible` (kind L — three li-projection facts conjoined, **modulo
  li-projection's OPEN (A)**): for any inductor `P` over `DP` with `u` fresh and any rational
  `c ∈ (0,1)`, there is an inductor `P'` over `DP` agreeing with `P` on every `u`-free sentence
  whose limiting belief on `u` is `c` — Lemma A at a constant weight
  (`project_const_isLogicalInductor`) with `project_restrict` and `limitingBelief_project_const_atom`.
  **What this does and does not say** (audit r1, B2): Lemma A shows an inductor may carry *any*
  interior `u`-limit while agreeing with `P` off `u`; this is the only sense in which a pinned
  `u`-price is "LIC-compatible" that the package establishes, and **no demand enters the
  statement** — it does not involve a push. `pinnedMarket_pushInvariant` (kind T) records that the
  demand-blind map `H ↦ project P u (fun _ => c)` satisfies `PushInvariant` by `rfl` (it ignores
  `H` on *every* sentence, not only the `u`-sentences) and is an inductor at each `H`; any map
  constant in the demand, at any inductor, has the same property, so it is a sanity lemma, not a
  headline. The object the source's constraint is about — a market that *responds* to the push off
  `u` and is demand-blind on `u` — is `PushInvariantOver` (`Open.lean`), whose criterion-compliance
  is OPEN (`pushInvariantOver_compatible`) beside T8.3. **Fidelity `variant`**: the full-invariance
  reading of a *single* history; the partial form (remove only the caused component, over the
  exo-market) is T8.3. **Trap** avoided: `project P u q` prices `u` at `q_n P_n(⊤) + (1 − q_n)
  P_n(⊥)`, equal to `q_n` only in the limit, so the statement is about the limit.
* **T8.4** the VOI half is `Reflect.lean`'s `gamma_eq_alpha_of_uncaused` (cited); `udt-bli-core`'s
  Good's theorem (`good`, `Good.lean`) is the deferral-dominates-precommitment form (cited, not
  imported).
-/

namespace Cleanroom.Corrigibility.CorrExoTrader

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Li.LiProjection

/-! ## T8.1 — the constraint -/

/-- **The one unlearnable constraint, self-caused form.** A market map `M : ExoDemand → History`
prices every `u`-sentence (`¬ AtomFreeSentence u ψ`) under the demand `Hc ⊕ Hu` as under `Hu`
alone: the self-caused component `Hc` of the push is invisible on the `u`-fragment. **The
decomposition `H = Hc ⊕ Hu` is supplied, not derived** — grade (c): FAF has no causal object, and
"causally downstream of the agent's own actions" exists here only as a choice of `Hc`.
Source: line 119 ("prices of `u`-sentences are invariant to the component of a push that is causally downstream of the agent's own actions"); corr-core-048; bli-soto-b-059(iii); mandate T8.1
Kind: D
Fidelity: variant: (c) through the supplied decomposition -/
def SelfCausedInvariant (u : ℕ) (M : ExoDemand → History) (Hc Hu : ExoDemand) : Prop :=
  ∀ n ψ, ¬ AtomFreeSentence u ψ → M (Trader.join Hc Hu) n ψ = M Hu n ψ

/-- **The extreme form**: every demand prices the `u`-fragment exactly as no demand does — the
`u`-prices are pinned to a push-independent schedule. **Caveat (audit r1, B2)**: this constrains
only the `u`-fragment's *dependence on `H`*; it says nothing about the `u`-free fragment, so it is
satisfied vacuously (by `rfl`) by every market map constant in `H` — the all-`½` map included. The
meaningful object, a map that agrees with `exoHistory DP H` off `u` and is demand-blind on `u`, is
`PushInvariantOver` (`Open.lean`).
Source: line 119; mandate T8.1 (`PushInvariant`)
Kind: D
Fidelity: variant: full invariance (the strongest reading); a constraint on the `u`-fragment only -/
def PushInvariant (u : ℕ) (M : ExoDemand → History) : Prop :=
  ∀ H n ψ, ¬ AtomFreeSentence u ψ → M H n ψ = M noDemand n ψ

/-- Full invariance implies the self-caused form for every decomposition.
Source: mandate T8.1
Kind: L
Fidelity: exact -/
theorem PushInvariant.selfCausedInvariant {u : ℕ} {M : ExoDemand → History} (h : PushInvariant u M)
    (Hc Hu : ExoDemand) : SelfCausedInvariant u M Hc Hu := by
  intro n ψ hψ
  rw [h (Trader.join Hc Hu) n ψ hψ, h Hu n ψ hψ]

/-! ## T8.2 — LIC-compatibility, in li-projection's sense -/

/-- **T8.2 — a pinned `u`-price schedule is criterion-compliant.** For any inductor `P` over `DP`
with `u` fresh and a consistent world at every stage, and any rational `c ∈ (0, 1)`: there is an
inductor `P'` over `DP` that agrees with `P` on every `u`-free sentence on every day and whose
limiting belief on `u` is `c`. Lemma A at the constant weight `c`
(`project_const_isLogicalInductor`), restriction (`project_restrict`) and the marginal limit
(`limitingBelief_project_const_atom`). **Modulo li-projection's OPEN (A)** (the e.c. certificate of
the mirror traders), listed in `corr-exo-trader-open.txt`. **No demand enters this statement**
(audit r1, B2): it says an inductor may carry any interior `u`-limit while agreeing with `P` off
`u` — the only sense of "a pinned `u`-price is LIC-compatible" the package establishes. The
demand-indexed constraint over the exo-market is `pushInvariantOver_compatible` / T8.3 (OPEN).
Source: line 119 ("since `u` never settles, the constraint can't be exploited, so it looks compatible with the LIC"); corr-core-048; audit §3 Q2; mandate T8.2
Kind: L
Fidelity: variant: a single inductor with a pinned `u`-limit agreeing with `P` off `u` (limit form; the daily price is `c · P_n(⊤) + (1 − c) · P_n(⊥)`); no demand in the statement; the demand-indexed constraint is OPEN
Hyps: (a); rests on li-projection's OPEN (A) through Lemma A -/
theorem constraint_lic_compatible (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ) (hu : AtomFreeProcess u DP)
    (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ P' : History, IsLogicalInductor P' DP ∧
      (∀ n ψ, AtomFreeSentence u ψ → P' n ψ = P n ψ) ∧
      limitingBelief P' (Formula.atom u) = c :=
  ⟨project P u (fun _ => c), project_const_isLogicalInductor P DP u hu c hc0 hc1,
    fun n ψ hψ => project_restrict P u (fun _ => c) n hψ,
    limitingBelief_project_const_atom P DP hworld u c⟩

/-- **The pinned market map** `H ↦ project P u (fun _ => c)`: the same inductor whatever the demand.
Source: mandate T8.2
Kind: D
Fidelity: variant: the strongest reading of the constraint (full invariance) -/
noncomputable def pinnedMarket (P : History) (u : ℕ) (c : ℚ) : ExoDemand → History :=
  fun _ => project P u (fun _ => c)

/-- **Sanity lemma (kind T, not a headline — audit r1, B2).** The demand-blind map
`H ↦ project P u (fun _ => c)` satisfies `PushInvariant u` **by `rfl`** — it ignores `H` on every
sentence, not only the `u`-sentences — and each of its values is an inductor over `DP` (modulo
(A)), hence `NoEcExploit`. Any map constant in the demand, at any inductor and for any `u`, has
exactly this property with no projection and no (A); so the conclusion is inhabited for a reason
unrelated to pushes, and the theorem says nothing about a market that *responds* to pushes off `u`
(that object is `PushInvariantOver`, `Open.lean`, with T8.3 and `pushInvariantOver_compatible`
OPEN).
Source: line 119; corr-core-048; mandate T8.2
Kind: T
Fidelity: variant: full invariance of a demand-blind map (trivially true)
Hyps: (a); rests on li-projection's OPEN (A) -/
theorem pinnedMarket_pushInvariant (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (u : ℕ) (hu : AtomFreeProcess u DP) (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1) :
    PushInvariant u (pinnedMarket P u c) ∧
      ∀ H : ExoDemand, IsLogicalInductor (pinnedMarket P u c H) DP ∧
        NoEcExploit (pinnedMarket P u c H) DP := by
  refine ⟨fun _ _ _ _ => rfl, fun H => ?_⟩
  have hLI : IsLogicalInductor (pinnedMarket P u c H) DP :=
    project_const_isLogicalInductor P DP u hu c hc0 hc1
  exact ⟨hLI, hLI.noExploit⟩

/-- The pinned market's `u`-free prices are the base inductor's, at every demand.
Source: mandate T8.2
Kind: L
Fidelity: exact -/
theorem pinnedMarket_restrict (P : History) (u : ℕ) (c : ℚ) (H : ExoDemand) (n : ℕ) {ψ : Sentence}
    (hψ : AtomFreeSentence u ψ) : pinnedMarket P u c H n ψ = P n ψ :=
  project_restrict P u (fun _ => c) n hψ

end Cleanroom.Corrigibility.CorrExoTrader
