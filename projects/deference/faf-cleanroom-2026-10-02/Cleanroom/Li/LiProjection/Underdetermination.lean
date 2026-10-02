import Cleanroom.Li.LiProjection.LemmaA
import Cleanroom.Li.LiProjection.Marginal
import Cleanroom.Found.LiQuoteLane.Ledger

/-!
# `li-projection` · Underdetermination: two inductors, one gap (T2.2–T2.5)

Package `Cleanroom.Li.LiProjection` ([[li-projection-mandate]]), file 9 of the layout. The
replacement for the corpus's `underdetermination_off_G` (`research/lean-deference/FrozenDeliberation.lean`
l. 268), which proved that two reals in `(0,1)` differ by `γ` — the named fake of [[AUDIT]] §3.4.
Here the two witnesses are **histories**: `project P u (fun _ => c)` and `project P u (fun _ => c')`
are both logical inductors over the same `DP`, agree **exactly, on every day**, at every sentence
that does not mention the fresh atom `u` — hence at every sentence of every stage of `DP`, and at
every ledger threshold when `DP` is `li-quote-lane`'s `ledgerProcess` — and their limiting beliefs on
`u` are `c` and `c'`, any prescribed rational gap in `(0,1)`.

**What rests on what.** The agreement and the two limits are proved outright from the base
inductor's criterion (`Marginal.lean`). That the two projections are *inductors* is Lemma A
(`LemmaA.lean`), proved modulo the two OPEN `Complexity.FP` rewriter facts of `Certificate.lean`;
so the two-inductor conjuncts of every headline here — T2.2, T2.3 **and T2.4** — carry that
dependency (listed in `li-projection-open.txt`), and nothing else does. (Repair round 1: T2.4's
statement now carries freshness, the weight bounds and the two inductor conjuncts like T2.2; the
criterion-free agreement-and-limits half is the supporting lemma `project_daySet_agree_and_limits`.)

**Scope: one-way.** The ledger form (T2.3) is over `li-quote-lane`'s `OneWayPair`: a fixed `A`
publishes, `H` reads; the two projected readers are inductors over the *same* ledger process and read
the *same* published numbers. The "agree on every `G`-quantity" of anson-011 is rendered, as its own
flag demands, as agreement on atom-free sentences — stronger than agreement on settled sentences.
The entangled case (two inductors differing on a sentence the process *mentions* but never decides)
is T7.1, OPEN; the countable-atom family with a product weighting is T7.4, OPEN.
-/

namespace Cleanroom.Li.LiProjection

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Filter Topology

/-! ## T2.2 The headline: two inductors, one gap -/

/-- **Underdetermination on a fresh atom** (replaces the corpus's `underdetermination_off_G`). For
`[IsLogicalInductor P DP]`, `u` fresh for `DP`, and rationals `c, c' ∈ (0,1)`: the projections
`P₁ := project P u (fun _ => c)` and `P₂ := project P u (fun _ => c')` are (1) both logical inductors
over the same `DP`; (2) agree exactly on every day at every `u`-free sentence; (3) agree with `P`
there; and (4) have limiting beliefs `c` and `c'` on `u` — the gap is `|c − c'|`.
Conjuncts (1) rest on Lemma A (OPEN certificate); (2)–(4) are proved outright.
Source: [[anson-inventory]] 011 (chat 09 L339–343, with its flag "agree on every `G`-quantity must be restricted to atom-free sentences"); [[root-deference-inventory]] 044(ii) (v6 §5.6 T7 off `G`); [[lean-deference-inventory]] 023 (the stub replaced); [[trust-lab-2-inventory]] 037–038
Kind: C
Fidelity: stronger: agreement is exact on every day at every atom-free sentence (the source asks for agreement on settled quantities); the gap is any prescribed rational in `(0,1)`. Scope: one-way; fresh atom (the entangled case is OPEN T7.1)
Hyps: (a) throughout; (1) rests on the OPEN rewriters -/
theorem underdetermination_fresh_atom (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ)
    (hu : AtomFreeProcess u DP) (c c' : ℚ) (hc0 : 0 < c) (hc1 : c < 1) (hc'0 : 0 < c')
    (hc'1 : c' < 1) :
    IsLogicalInductor (project P u (fun _ => c)) DP ∧
    IsLogicalInductor (project P u (fun _ => c')) DP ∧
    (∀ n φ, AtomFreeSentence u φ →
      project P u (fun _ => c) n φ = project P u (fun _ => c') n φ) ∧
    (∀ n φ, AtomFreeSentence u φ → project P u (fun _ => c) n φ = P n φ) ∧
    limitingBelief (project P u (fun _ => c)) (Formula.atom u) = c ∧
    limitingBelief (project P u (fun _ => c')) (Formula.atom u) = c' :=
  ⟨project_const_isLogicalInductor P DP u hu c hc0 hc1,
   project_const_isLogicalInductor P DP u hu c' hc'0 hc'1,
   fun n φ hφ => by rw [project_restrict P u _ n hφ, project_restrict P u _ n hφ],
   fun n φ hφ => project_restrict P u _ n hφ,
   limitingBelief_project_const_atom P DP hworld u c,
   limitingBelief_project_const_atom P DP hworld u c'⟩

/-- **The witness form: any prescribed gap.** For every rational `γ ∈ (0,1)` there are two
histories, both logical inductors over `DP`, agreeing on every day at every `u`-free sentence,
whose limiting beliefs on `u` differ by exactly `γ`. The witnesses are `project P u (fun _ => (1+γ)/2)`
and `project P u (fun _ => (1−γ)/2)` — the stub's two numbers, now carried by inductors.
Source: [[lean-deference-inventory]] 023 (`underdetermination_off_G`, [[AUDIT]] §3.4); [[root-deference-inventory]] 044(ii)
Kind: C
Fidelity: stronger (see `underdetermination_fresh_atom`). Scope: one-way; fresh atom
Hyps: (a) throughout; the inductor conjuncts rest on the OPEN rewriters -/
theorem underdetermination_fresh_atom_exists (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ)
    (hu : AtomFreeProcess u DP) (γ : ℚ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ P₁ P₂ : History, IsLogicalInductor P₁ DP ∧ IsLogicalInductor P₂ DP ∧
      (∀ n φ, AtomFreeSentence u φ → P₁ n φ = P₂ n φ) ∧
      |limitingBelief P₁ (Formula.atom u) - limitingBelief P₂ (Formula.atom u)| = γ := by
  obtain ⟨h1, h2, hagree, -, hl1, hl2⟩ := underdetermination_fresh_atom P DP hworld u hu
    ((1 + γ) / 2) ((1 - γ) / 2) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨_, _, h1, h2, hagree, ?_⟩
  rw [hl1, hl2]
  have hγR : (0 : ℝ) < γ := by exact_mod_cast hγ0
  push_cast
  rw [abs_of_pos (by linarith)]
  ring

/-- The two projections agree on every sentence of every stage of `DP` (every "settled" quantity),
as a corollary of atom-free agreement.
Source: [[anson-inventory]] 011; [[root-deference-inventory]] 044(ii) ("agree on every `G`-settling quantity")
Kind: L
Fidelity: exact -/
theorem project_agree_on_stages (P : History) (DP : DeductiveProcess) (u : ℕ)
    (hu : AtomFreeProcess u DP) (q q' : ℕ → ℚ) (n k : ℕ) {φ : Sentence} (hφ : φ ∈ DP.D k) :
    project P u q n φ = project P u q' n φ := by
  rw [project_restrict P u q n (hu k φ hφ), project_restrict P u q' n (hu k φ hφ)]

/-! ## T2.4 The day-set form -/

/-- The agreement-and-limits half of the day-set form, **without** freshness of `u`, without bounds
on the weights and without the criterion for the projections: for any `G`, any family `u`-free on
`G` and equal to the atom `u` off `G`, and *any* rationals `c, c'`, the two projections agree at
every day on `G` and have limiting beliefs `c`, `c'` off `G`. This is `project_restrict` plus
`limitingBelief_project_const_atom` and nothing more — it holds at a decided atom and at weights
outside `[0,1]` (audit r1, adversarial B2, probe `DaySetNoCriterion.lean`), so it is plumbing for
`underdetermination_daySet`, not a headline. Before repair round 1 this statement carried the
headline name.
Source: mandate T2.4; audit r1 (adversarial) B2
Kind: L
Fidelity: n/a (supporting lemma: carries neither freshness nor the criterion)
Hyps: (a) -/
theorem project_daySet_agree_and_limits (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ)
    (G : Set ℕ) (φ : ℕ → Sentence) (hG : ∀ n ∈ G, AtomFreeSentence u (φ n))
    (hG' : ∀ n ∉ G, φ n = Formula.atom u) (c c' : ℚ) :
    (∀ n ∈ G, ∀ m, project P u (fun _ => c) m (φ n) = project P u (fun _ => c') m (φ n)) ∧
    (∀ n ∉ G, limitingBelief (project P u (fun _ => c)) (φ n) = c ∧
      limitingBelief (project P u (fun _ => c')) (φ n) = c') :=
  ⟨fun n hn m => by rw [project_restrict P u _ m (hG n hn), project_restrict P u _ m (hG n hn)],
   fun n hn => by
    rw [hG' n hn]
    exact ⟨limitingBelief_project_const_atom P DP hworld u c,
      limitingBelief_project_const_atom P DP hworld u c'⟩⟩

/-- **The day-set form** (instantiated by `def-frozen-sibling` at its timely fragment `G`). For
`[IsLogicalInductor P DP]`, `u` fresh for `DP`, rationals `c, c' ∈ (0,1)`, any set of days `G` (no
efficient-computability hypothesis is needed for this form) and any family `φ : ℕ → Sentence` that
is `u`-free on `G` and the atom `u` off `G`: the two projections `project P u (fun _ => c)`,
`project P u (fun _ => c')` are (1) both logical inductors over `DP`; (2) agree at every day on
`φ n` for `n ∈ G`; and (3) have limiting beliefs `c` and `c'` on `φ n` for `n ∉ G`. Conjuncts (1)
are Lemma A (OPEN certificate); (2)–(3) are proved outright (`project_daySet_agree_and_limits`).
Disclosed: the off-`G` family is the *single* atom `u` (the countable-atom family with a product
weighting is OPEN T7.4).
Source: mandate T2.4 (coverage critique 7); [[root-deference-inventory]] 044(i)/(ii) on an e.c. day-set
Kind: C
Fidelity: variant: the off-`G` family is one atom; no e.c. hypothesis on `G`
Hyps: (a) throughout; (1) rests on the OPEN rewriters -/
theorem underdetermination_daySet (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ)
    (hu : AtomFreeProcess u DP) (G : Set ℕ) (φ : ℕ → Sentence)
    (hG : ∀ n ∈ G, AtomFreeSentence u (φ n)) (hG' : ∀ n ∉ G, φ n = Formula.atom u)
    (c c' : ℚ) (hc0 : 0 < c) (hc1 : c < 1) (hc'0 : 0 < c') (hc'1 : c' < 1) :
    IsLogicalInductor (project P u (fun _ => c)) DP ∧
    IsLogicalInductor (project P u (fun _ => c')) DP ∧
    (∀ n ∈ G, ∀ m, project P u (fun _ => c) m (φ n) = project P u (fun _ => c') m (φ n)) ∧
    (∀ n ∉ G, limitingBelief (project P u (fun _ => c)) (φ n) = c ∧
      limitingBelief (project P u (fun _ => c')) (φ n) = c') :=
  ⟨project_const_isLogicalInductor P DP u hu c hc0 hc1,
   project_const_isLogicalInductor P DP u hu c' hc'0 hc'1,
   (project_daySet_agree_and_limits P DP hworld u G φ hG hG' c c').1,
   (project_daySet_agree_and_limits P DP hworld u G φ hG hG' c c').2⟩

/-! ## T2.3 The ledger (same-advisor, same-ledger) form -/

/-- A fresh atom of a family other than `4` is free of every projection atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomFreeSentence_freshAtom_of_ne {f p : ℕ} (hf : f ≠ 4) (k : ℕ) :
    AtomFreeSentence (projAtomCode k) (freshAtom f p) := by
  intro h
  rw [sentenceAtomCodes_freshAtom, Finset.mem_singleton] at h
  exact hf (freshAtomCode_inj.mp h).1.symm

/-- Adjoining decided literals of families other than `4` keeps a process free of the projection
atoms.
Source: none: infrastructure (`bli-found`'s `extendBy`)
Kind: L
Fidelity: n/a -/
theorem atomFreeProcess_extendBy {DP : DeductiveProcess} {L : LiteralSchedule} (k : ℕ)
    (hDP : AtomFreeProcess (projAtomCode k) DP) (hL : ∀ f ∈ L.families, f ≠ 4) :
    AtomFreeProcess (projAtomCode k) (extendBy DP L) := by
  intro n φ hφ
  rw [extendBy_D, Finset.mem_union] at hφ
  rcases hφ with hbase | hlit
  · exact hDP n φ hbase
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hlit
    have hf : x.1 ≠ 4 := hL x.1 ⟨n, x, hx, rfl⟩
    rcases x with ⟨f, p, b⟩
    cases b
    · exact (atomFreeSentence_freshAtom_of_ne hf k).neg
    · exact atomFreeSentence_freshAtom_of_ne hf k

/-- `li-quote-lane`'s ledger process is free of every projection atom whenever its base is: the
ledger atoms are family `3`, the projection atoms family `4` (`freshAtom_injective`).
Source: mandate T1.2 ("relative to `li-quote-lane`'s ledger it is family `4 ≠ 3`")
Kind: L
Fidelity: exact -/
theorem atomFreeProcess_ledgerProcess {base : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (k : ℕ) (hbase : AtomFreeProcess (projAtomCode k) base) :
    AtomFreeProcess (projAtomCode k) (ledgerProcess base a e) :=
  atomFreeProcess_extendBy k hbase fun f hf => by
    rw [ledgerSchedule_families a e f hf]; simp [ledgerFamily]

/-- Every ledger threshold sentence is free of every projection atom.
Source: mandate T2.3 ("every `ledgerLuv` threshold is `u`-free")
Kind: L
Fidelity: exact -/
theorem atomFreeSentence_ledgerLuv_gt (k j n : ℕ) (r : ℚ) :
    AtomFreeSentence (projAtomCode k) ((ledgerLuv j n).gt r) := by
  rw [ledgerLuv_gt]
  exact atomFreeSentence_freshAtom_of_ne (by simp [ledgerFamily]) k

/-- **The ledger form.** Over a one-way pair `p` (a fixed advisor `A` publishing into `H`'s ledger
process), with the reader's base process free of the projection atom: the two projected readers
`project p.H u (fun _ => c)`, `project p.H u (fun _ => c')` are (1) both logical inductors over the
*same* ledger process `p.process`; (2) agree exactly on every day at every `u`-free sentence;
(3) read the *same* published numbers — every ledger threshold sentence has the same price in both
as in `p.H`, and every ledger expectation `𝔼_n(α_{j,m})` is unchanged; and (4) differ by `|c − c'|`
in the limit on `u`. This is root-deference-044(ii)'s honest core: "`A` is unchanged by construction;
the interesting clause is that the two `H⁺` variants are both inductors over the same ledger". The
trust clauses of anson-2-004(ii)/Th 8 are inherited by (2)–(3) whenever they are statements about
`u`-free sentences. (1) rests on the OPEN certificate.
Source: [[root-deference-inventory]] 044(ii) (v6 §5.6 T7 off `G`, "same `A`, target and ledger"); [[anson-2-inventory]] 004(ii), Th 8; [[anson-inventory]] 011
Kind: C
Fidelity: variant/stronger: stronger in the agreement clause (exact, every day, every atom-free sentence); variant in the target (a fresh atom in place of the source's fixed off-`G` `P`); silent on the source's "(A1)–(A5)" and Th 8's tracking/externalized self-trust. Scope: one-way (`li-quote-lane`'s `OneWayPair`; plain trader class)
Hyps: (a) throughout; (1) rests on the OPEN rewriters -/
theorem underdetermination_ledger (p : OneWayPair) (k : ℕ)
    (hfree : AtomFreeProcess (projAtomCode k) p.DPH) (c c' : ℚ) (hc0 : 0 < c) (hc1 : c < 1)
    (hc'0 : 0 < c') (hc'1 : c' < 1) :
    IsLogicalInductor (project p.H (projAtomCode k) (fun _ => c)) p.process ∧
    IsLogicalInductor (project p.H (projAtomCode k) (fun _ => c')) p.process ∧
    (∀ n φ, AtomFreeSentence (projAtomCode k) φ →
      project p.H (projAtomCode k) (fun _ => c) n φ =
        project p.H (projAtomCode k) (fun _ => c') n φ) ∧
    (∀ j m r n, project p.H (projAtomCode k) (fun _ => c) n ((ledgerLuv j m).gt r) =
      p.H n ((ledgerLuv j m).gt r)) ∧
    (∀ j m n, LUV.expect (project p.H (projAtomCode k) (fun _ => c)) n (ledgerLuv j m) =
      LUV.expect p.H n (ledgerLuv j m)) ∧
    limitingBelief (project p.H (projAtomCode k) (fun _ => c)) (projAtom k) = c ∧
    limitingBelief (project p.H (projAtomCode k) (fun _ => c')) (projAtom k) = c' := by
  haveI := p.H_inductor
  have hfree' : AtomFreeProcess (projAtomCode k) p.process := atomFreeProcess_ledgerProcess k hfree
  obtain ⟨h1, h2, hagree, hP, hl1, hl2⟩ := underdetermination_fresh_atom p.H p.process p.hworld
    (projAtomCode k) hfree' c c' hc0 hc1 hc'0 hc'1
  refine ⟨h1, h2, hagree, fun j m r n => hP n _ (atomFreeSentence_ledgerLuv_gt k j m r),
    fun j m n => ?_, hl1, hl2⟩
  simp only [LUV.expect, LUV.expectApprox]
  congr 1
  exact Finset.sum_congr rfl fun i _ => hP n _ (atomFreeSentence_ledgerLuv_gt k j m _)

/-! ## T2.5 The finite core and settlement-gated invariance, over FAF -/

/-- A feature's denotation depends only on the price coordinates it reads (`EF.priceQueries`).
Source: [[trust-lab-2-inventory]] 037 (the "finite core"); mandate T2.5(i)
Kind: P
Fidelity: exact -/
lemma EF.denoteWith_congr (e : EF) (P P' : History)
    (h : ∀ x ∈ e.priceQueries, P x.1 x.2 = P' x.1 x.2) :
    ∀ ρ : List ℝ, e.denoteWith ρ P = e.denoteWith ρ P' := by
  induction e with
  | price φ m =>
      intro ρ
      simp only [EF.denoteWith_price]
      exact h (m, φ) (by simp [EF.priceQueries])
  | const c => intro ρ; rfl
  | add a b iha ihb =>
      intro ρ
      simp only [EF.denoteWith_add]
      rw [iha (fun x hx => h x (by simp [EF.priceQueries, hx])) ρ,
        ihb (fun x hx => h x (by simp [EF.priceQueries, hx])) ρ]
  | mul a b iha ihb =>
      intro ρ
      simp only [EF.denoteWith_mul]
      rw [iha (fun x hx => h x (by simp [EF.priceQueries, hx])) ρ,
        ihb (fun x hx => h x (by simp [EF.priceQueries, hx])) ρ]
  | max a b iha ihb =>
      intro ρ
      simp only [EF.denoteWith_max]
      rw [iha (fun x hx => h x (by simp [EF.priceQueries, hx])) ρ,
        ihb (fun x hx => h x (by simp [EF.priceQueries, hx])) ρ]
  | safeRecip a iha =>
      intro ρ
      simp only [EF.denoteWith_safeRecip]
      rw [iha (fun x hx => h x (by simp [EF.priceQueries, hx])) ρ]
  | var i => intro ρ; rfl
  | letE x body ihx ihb =>
      intro ρ
      simp only [EF.denoteWith_letE]
      rw [ihx (fun y hy => h y (by simp [EF.priceQueries, hy])) ρ]
      exact ihb (fun y hy => h y (by simp [EF.priceQueries, hy])) _

/-- A day-`n` strategy **reads only** the coordinate set `K`: every coefficient's price leaves and
every traded sentence (at day `n`) lie in `K`.
Source: [[trust-lab-2-inventory]] 037; mandate T2.5
Kind: D
Fidelity: exact -/
def Strategy.ReadsOnly {n : ℕ} (S : Strategy n) (K : Set (ℕ × Sentence)) : Prop :=
  ∀ p ∈ S.trades, (∀ x ∈ p.1.priceQueries, x ∈ K) ∧ (n, p.2) ∈ K

/-- A trader reads only the coordinate set `K` on every day.
Source: [[trust-lab-2-inventory]] 037; mandate T2.5
Kind: D
Fidelity: exact -/
def Trader.ReadsOnly (T : Trader) (K : Set (ℕ × Sentence)) : Prop :=
  ∀ n, Strategy.ReadsOnly (T.strat n) K

/-- **Net-worth invariance (the finite core).** If two markets agree on every coordinate a trader
ever reads (price leaves) or trades, the trader's net worth is the same against both, in every
world on every day. Over FAF this is a lemma, not an EXEC target: `Exploits` already quantifies
over all days, so the source's finite trader class and eventual-periodicity extension are not needed.
Source: [[trust-lab-2-inventory]] 037–038 (the finite core and settlement-gated invariance), retired honestly (findings)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Trader.netWorth_congr (T : Trader) (K : Set (ℕ × Sentence)) (hT : Trader.ReadsOnly T K)
    (P P' : History) (hPP' : ∀ x ∈ K, P x.1 x.2 = P' x.1 x.2) (v : PCWorld) (n : ℕ) :
    T.netWorth P v n = T.netWorth P' v n := by
  unfold Trader.netWorth
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Strategy.value]
  refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
  obtain ⟨hleaves, htrade⟩ := hT m p hp
  rw [show p.1.denote P = p.1.denote P' from
    EF.denoteWith_congr p.1 P P' (fun x hx => hPP' x (hleaves x hx)) []]
  rw [hPP' (m, p.2) htrade]

/-- The `u`-free coordinates: every `(day, sentence)` with the sentence free of `u`.
Source: mandate T2.5(ii) ("invariance is co-extensive with the undecided fragment")
Kind: D
Fidelity: exact -/
def atomFreeCoords (u : ℕ) : Set (ℕ × Sentence) := {x | AtomFreeSentence u x.2}

/-- **Settlement-gated invariance, over FAF.** A trader whose price leaves and traded sentences are
all `u`-free has identical net worth against the two projections (any weights) — and against the
base inductor. Contrapositively, only a trader that *trades or reads* a `u`-sentence sees the
difference between the two inductors of T2.2: invariance is co-extensive with the undecided fragment.
Source: [[trust-lab-2-inventory]] 038; mandate T2.5(ii)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem netWorth_project_eq_of_readsOnly_atomFree (T : Trader) (u : ℕ)
    (hT : Trader.ReadsOnly T (atomFreeCoords u)) (P : History) (q q' : ℕ → ℚ) (v : PCWorld)
    (n : ℕ) :
    T.netWorth (project P u q) v n = T.netWorth (project P u q') v n ∧
    T.netWorth (project P u q) v n = T.netWorth P v n :=
  ⟨Trader.netWorth_congr T _ hT _ _ (fun x hx => by
      rw [project_restrict P u q x.1 hx, project_restrict P u q' x.1 hx]) v n,
   Trader.netWorth_congr T _ hT _ _ (fun x hx => project_restrict P u q x.1 hx) v n⟩

end Cleanroom.Li.LiProjection
