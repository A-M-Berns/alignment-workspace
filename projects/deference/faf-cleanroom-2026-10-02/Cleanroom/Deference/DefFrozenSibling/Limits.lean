import Cleanroom.Deference.DefFrozenSibling.Engine
import Cleanroom.Li.LiProjection.Underdetermination
import LogicalInduction.Properties.AffinePersistence

/-!
# `def-frozen-sibling` · Limits: T7, limit prices — exact on `G`, underdetermined off `G`

[[frozen-deliberation-deference-v6]] T7 (anson-023; root-deference-044; lean-deference-023):
"`|H^{[n]}_∞(P^{(n)}) − H⁺_∞(P^{(n)})| → 0` on `G`. Off `G` the limit is underdetermined."

**On `G`, exact per `n`** (`limit_agree_onG`; kind C, (a); *stronger* than the source's asymptotic
form): for every `n ∈ G`, the sibling's, the advised reasoner's and the predictor's limiting beliefs
on `P^{(n)}` all equal the decided value `truthAt S n`. From `DecidedBy` (stage membership in the
shared process, which each of the three processes contains stage-wise) and FAF's provability
induction at a constant family (`lic_provind_true`/`_false`), with `thm:con`'s limit identified by
uniqueness. The quantifier-order worry of anson-023 dissolves: no diagonal limit is needed, each
`n ∈ G` is exact; one-way per `n` (needs only the inductor fields). The limit lemmas are
`def-tracking-pin`'s `limitingBelief_eq_one_of_decided` / `_zero_of_refuted`, re-proved here
because that package keeps them in its heavy `Column` module (which imports the LIA compiler).
**Only the decided clause is used** (`limit_agree_of_decidedBy`, from which `limit_agree_onG` is
the `Timely` instance), and the same argument runs on the whole decided fragment: a contract decided
at *any* stage has its limiting belief pinned to one value in all three markets
(`limit_pinned_of_decidedAt`, repair round 2). So the source's dichotomy for limit prices is
**decided / undecidable**, not on-`G` / off-`G` — its T7(ii) ("off `G` the limit is
underdetermined") is false on the slow fragment (findings F16).

**Off `G`, by projection** (`projection_pair_offG_atom`; renamed and restated in repair round 1
after audit r1 adversarial B2 — formerly `underdetermination_offG`): two projections of the
advised reasoner onto a fresh atom, both logical inductors over `Hplus`'s process, that **agree
with `Hplus` itself on every contract at every day** (the contracts are free of the projection
atom, `contract_projFree`, so `li-projection`'s `project_restrict` makes each projection the
identity there — timely or not) and have limiting beliefs `c`, `c'` (any prescribed gap in
`(0,1)`) **on the projection atom**. What this shows: the record of a frozen-deliberation system
(every contract's price, at every day) does not determine the reasoner's limit on a sentence
outside the base language. What it does **not** show: anything about any off-`G` contract. The
source's T7(ii) — a nondegenerate interval of achievable `H⁺_∞(P)` for a fixed off-`G` `P` — splits
by fragment (repair round 2, audit r2 fidelity N1/N2): on the **slow** fragment it is false (the
limit is pinned, `limit_pinned_of_decidedAt`); on the **undecidable** fragment, for a contract that
is a bare atom the advised reasoner's process never mentions, it is rendered here by projecting
`Hplus` on the contract's own atom (`projection_pair_undecidable_contract`, §D: two inductors over
`processH`, agreeing with `Hplus` on every atom-free sentence, with limits `c`, `c'` on `P^{(n₀)}`
itself — modulo the same OPEN rewriters); for an undecidable contract *entangled* with the process
`li-projection`'s OPEN `multiplicity_entangled` remains the carrier. The mandate's
instantiation of `li-projection`'s `underdetermination_daySet` at `G = {n | Timely S ε n}` is kept
as the corollary `projection_pair_daySet`, with the disclosure that `Timely` does no work in it.
The inductor conjuncts rest on `li-projection`'s OPEN FP rewriters (`li-projection-open.txt`), so
both rows read `partial: over li-projection's OPEN rewriters` and are listed in
`def-frozen-sibling-open.txt`; the agreement and limit conjuncts are proved outright. Against
[[AUDIT]] §3.4's `underdetermination_off_G` ("two points in an interval"): the witnesses are
histories, inductors over the *same* process, and the agreement is exact at every day — but the
underdetermined sentence is a fresh atom, which the first-round name hid.
-/

namespace Cleanroom.Deference.DefFrozenSibling

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiProjection
open Filter Topology

/-! ## A. Limiting belief of a decided sentence (plumbing) -/

/-- A sentence lying in some stage has limiting belief `1` at any inductor over the process
(`def-tracking-pin`'s `limitingBelief_eq_one_of_decided`, re-proved to keep the import light).
Source: anson-043; FAF `thm:provind`, `thm:con`; `def-tracking-pin` `Column.lean`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem limitingBelief_eq_one_of_mem (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {φ : Sentence} (hφ : ∃ k, φ ∈ DP.D k) : limitingBelief P φ = 1 := by
  have h1 := lic_provind_true P DP (fun _ => φ) (MachineSentenceCodes.const φ)
    (fun _ v hv => hv.holds_of_mem_stage hφ) hworld
  have h2 := lic_limitingBelief_tendsto P DP hworld φ
  exact tendsto_nhds_unique h2 (convergesTo_iff_asympEq_const.2 h1)

/-- A sentence whose negation lies in some stage has limiting belief `0`
(`def-tracking-pin`'s `limitingBelief_eq_zero_of_refuted`, re-proved).
Source: anson-043; FAF `thm:provind`, `thm:con`; `def-tracking-pin` `Column.lean`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem limitingBelief_eq_zero_of_neg_mem (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {φ : Sentence} (hφ : ∃ k, ∼φ ∈ DP.D k) : limitingBelief P φ = 0 := by
  have h1 := lic_provind_false P DP (fun _ => φ) (MachineSentenceCodes.const φ)
    (fun _ v hv => hv.holds_of_mem_stage hφ) hworld
  have h2 := lic_limitingBelief_tendsto P DP hworld φ
  exact tendsto_nhds_unique h2 (convergesTo_iff_asympEq_const.2 h1)

/-- **The limiting belief of a decided contract is its decided value**, at any inductor over any
process containing the shared process stage-wise.
Source: mandate T7 (the per-`n` core)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem limitingBelief_contract_of_decidedBy {S : FrozenSystem} {n : ℕ} (h : DecidedBy S n)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ m, ∃ v : PCWorld, v.ConsistentWith (DP.D m))
    (hsub : ∀ m, S.base.D m ⊆ DP.D m) :
    limitingBelief P (S.contract n) = (truthAt S n : ℝ) := by
  unfold truthAt
  by_cases hmem : S.contract n ∈ S.base.D (S.F.f n)
  · rw [if_pos hmem]
    push_cast
    exact limitingBelief_eq_one_of_mem P DP hworld ⟨_, hsub _ hmem⟩
  · rw [if_neg hmem]
    push_cast
    exact limitingBelief_eq_zero_of_neg_mem P DP hworld ⟨_, hsub _ (h.resolve_left hmem)⟩

/-! ## B. T7 on `G`: exact per `n` -/

/-- **T7 on the decided fragment, exact per `n`**: for every `n` decided by the horizon
(`DecidedBy`, the first clause of `Timely`), the sibling's, the advised reasoner's and the
predictor's limiting beliefs on `P^{(n)}` are all the decided value. This is the fact
`limit_agree_onG` instantiates; the tolerance clause plays no role (audit r2 adversarial N5,
fidelity N8).
Source: [[frozen-deliberation-deference-v6]] T7 (lines 134–138); mandate T7
Kind: C
Fidelity: stronger: exact per decided `n`, three markets; "decided" as stage membership
Hyps: (a) none -/
theorem limit_agree_of_decidedBy (S : FrozenSystem) (n : ℕ) (h : DecidedBy S n) :
    limitingBelief (S.sib n) (S.contract n) = (truthAt S n : ℝ) ∧
      limitingBelief S.Hplus (S.contract n) = (truthAt S n : ℝ) ∧
      limitingBelief S.A (S.contract n) = (truthAt S n : ℝ) := by
  haveI := S.sib_inductor n
  haveI := S.Hplus_inductor
  haveI := S.A_inductor
  exact ⟨limitingBelief_contract_of_decidedBy h (S.sib n) (S.processSib n) (S.hworldSib n)
      (S.base_subset_processSib n),
    limitingBelief_contract_of_decidedBy h S.Hplus S.processH S.hworldH S.base_subset_processH,
    limitingBelief_contract_of_decidedBy h S.A S.processA S.hworldA S.base_subset_processA⟩

/-- **The limit of a contract decided at any stage is pinned** — in all three markets, to the same
value in `{0, 1}` (repair round 2, audit r2 fidelity N2). So the source's T7(ii), "off `G` the
limit is underdetermined … for a fixed off-`G` `P`", is **false on the slow fragment** (decided
after the horizon): T7's dichotomy for limit prices is decided / undecidable, not on-`G` / off-`G`
(findings F16). The source's own proof sketch ("no trader profits from a difference that never
settles") assumes undecidability.
Source: [[frozen-deliberation-deference-v6]] T7 (line 136, "off `G` the limit is underdetermined"); [[deference-in-logical-induction-v6]] §5.6 T7(ii) (root-deference-044 (ii)); audit r2 fidelity N2
Kind: C
Fidelity: n/a (a refutation of T7(ii)'s scope: the slow fragment is excluded)
Hyps: (a) none -/
theorem limit_pinned_of_decidedAt (S : FrozenSystem) (n : ℕ) (h : DecidedAt S n) :
    ∃ c : ℝ, (c = 0 ∨ c = 1) ∧ limitingBelief (S.sib n) (S.contract n) = c ∧
      limitingBelief S.Hplus (S.contract n) = c ∧ limitingBelief S.A (S.contract n) = c := by
  haveI := S.sib_inductor n
  haveI := S.Hplus_inductor
  haveI := S.A_inductor
  obtain ⟨m, hm | hm⟩ := h
  · exact ⟨1, Or.inr rfl,
      limitingBelief_eq_one_of_mem (S.sib n) (S.processSib n) (S.hworldSib n)
        ⟨m, S.base_subset_processSib n m hm⟩,
      limitingBelief_eq_one_of_mem S.Hplus S.processH S.hworldH ⟨m, S.base_subset_processH m hm⟩,
      limitingBelief_eq_one_of_mem S.A S.processA S.hworldA ⟨m, S.base_subset_processA m hm⟩⟩
  · exact ⟨0, Or.inl rfl,
      limitingBelief_eq_zero_of_neg_mem (S.sib n) (S.processSib n) (S.hworldSib n)
        ⟨m, S.base_subset_processSib n m hm⟩,
      limitingBelief_eq_zero_of_neg_mem S.Hplus S.processH S.hworldH
        ⟨m, S.base_subset_processH m hm⟩,
      limitingBelief_eq_zero_of_neg_mem S.A S.processA S.hworldA ⟨m, S.base_subset_processA m hm⟩⟩

/-- **T7 on `G` (headline; exact per `n`, kind C, (a)).** For every `n ∈ G`, the sibling's, the
advised reasoner's and the predictor's limiting beliefs on `P^{(n)}` are all the decided value:
`limitingBelief (sib n) (contract n) = truthAt n = limitingBelief Hplus (contract n) =
limitingBelief A (contract n)`. Only the decided clause of `Timely` is used (the tolerance clause
is idle here — the limits are exact whatever the sibling's day-`F n` verdict). Roles: `sib n` the
sealed sibling of index `n`, `Hplus` the advised reasoner, `A` the predictor. **One-way per `n`**
(each conjunct needs only that inductor's field and the stage containment); no `hz`.
Source: [[frozen-deliberation-deference-v6]] T7 (lines 134–138; anson-023, with its quantifier-order flag); [[deference-in-logical-induction-v6]] §5.6 T7(i) (root-deference-044); lean-deference-023 (`limit_agreement_on_G`, [[AUDIT]] §3.3 — the squeeze this replaces)
Kind: C
Fidelity: stronger: exact per `n ∈ G` (the source's `|…| → 0` along `G`) and for all three markets; "decided" as stage membership; the real domain is the decided fragment (`limit_agree_of_decidedBy`), of which `G` is the timely part
Hyps: (a) none -/
theorem limit_agree_onG (S : FrozenSystem) (ε : ℕ → ℚ) (n : ℕ) (h : Timely S ε n) :
    limitingBelief (S.sib n) (S.contract n) = (truthAt S n : ℝ) ∧
      limitingBelief S.Hplus (S.contract n) = (truthAt S n : ℝ) ∧
      limitingBelief S.A (S.contract n) = (truthAt S n : ℝ) :=
  limit_agree_of_decidedBy S n h.1

/-- **T7 on `G`, the source's form**: the sibling's and the advised reasoner's limits agree
exactly on every `n ∈ G` (hence their difference is `0`, a fortiori `→ 0` along `G`).
Source: [[frozen-deliberation-deference-v6]] T7 ("`|H^{[n]}_∞(P^{(n)}) − H⁺_∞(P^{(n)})| → 0` on `G`")
Kind: L
Fidelity: stronger: exact per `n`
Hyps: (a) none -/
theorem limit_agree_onG_sib_Hplus (S : FrozenSystem) (ε : ℕ → ℚ) (n : ℕ) (h : Timely S ε n) :
    limitingBelief (S.sib n) (S.contract n) = limitingBelief S.Hplus (S.contract n) := by
  obtain ⟨h1, h2, -⟩ := limit_agree_onG S ε n h
  rw [h1, h2]

/-! ## C. T7 off `G`: underdetermination by projection -/

/-- The off-`G` test family: the contract on `G`, the fresh projection atom off `G`.
Source: mandate T7 (off `G`)
Kind: D
Fidelity: n/a -/
noncomputable def offGFamily (S : FrozenSystem) (ε : ℕ → ℚ) (k : ℕ) (n : ℕ) : Sentence :=
  if Timely S ε n then S.contract n else projAtom k

/-- **T7 off `G` — a projection pair that agrees with the advised reasoner on every contract at
every day and differs on a fresh atom** (headline; `partial: over li-projection's OPEN
rewriters`; renamed from `underdetermination_offG` in repair round 1, audit r1 adversarial B2).
For a projection atom `projAtom k` fresh for the shared process and any two rationals
`c, c' ∈ (0,1)`: the two projections `project Hplus (projAtomCode k) (fun _ => c)` and `… c'` are
(1) both logical inductors over the advised reasoner's process `processH`; (2) **equal to `Hplus`
itself on every contract `P^{(n)}` at every day `m`** — timely or not, because the contracts are
free of the projection atom (`contract_projFree`) and the projection is the identity on atom-free
sentences (`li-projection`'s `project_restrict`); and (3) have limiting beliefs `c` and `c'` on the
projection atom `projAtom k`. **Nothing is shown about any off-`G` contract**: the underdetermined
sentence is the fresh atom, and the day-set `{n | Timely S ε n}` does no work (it only chooses on
which days the test family `offGFamily` displays the contract rather than the atom; see
`projection_pair_daySet`). The source's T7(ii) — a nondegenerate interval of achievable
`H⁺_∞(P)` for a fixed off-`G` contract `P` — is **not rendered by this theorem**; it is false on
the slow fragment (`limit_pinned_of_decidedAt`), rendered for an undecidable bare-atom contract by
`projection_pair_undecidable_contract` (§D), and left to `li-projection`'s OPEN
`multiplicity_entangled` for an entangled one. Conjuncts (1) rest on `li-projection`'s OPEN rewriters
(`project_const_isLogicalInductor`); (2)–(3) are proved outright (`project_restrict`,
`limitingBelief_project_const_atom`). Freshness for `Hplus`'s process is
`atomFreeProcess_ledgerProcess` (ledger atoms family `3`, projection atoms family `4`). Roles:
`Hplus` the advised reasoner (both projections are of it). One-way.
Source: [[frozen-deliberation-deference-v6]] T7 (lines 136–140, "off `G` the limit is underdetermined"; anson-023); [[deference-in-logical-induction-v6]] §5.6 T7(ii) (root-deference-044); lean-deference-023 (`underdetermination_off_G`, [[AUDIT]] §3.4 — the stub this replaces, with its own weakness named)
Kind: L (instance of `li-projection`'s Lemma A and marginal: three cited facts composed)
Fidelity: weaker: the underdetermined sentence is a fresh atom, not an off-`G` contract; the source's interval of achievable `H⁺_∞(P)` for an off-`G` contract is not rendered (`li-projection`'s OPEN `multiplicity_entangled` is the carrier); the agreement conjunct is stronger than the source's (every contract, every day)
Hyps: (a) throughout (`hbase`, freshness of the projection atom for the shared process, holds at every cleanroom-free base); conjuncts (1) rest on the OPEN rewriters -/
theorem projection_pair_offG_atom (S : FrozenSystem) (k : ℕ)
    (hbase : AtomFreeProcess (projAtomCode k) S.base) (c c' : ℚ) (hc0 : 0 < c) (hc1 : c < 1)
    (hc'0 : 0 < c') (hc'1 : c' < 1) :
    IsLogicalInductor (project S.Hplus (projAtomCode k) (fun _ => c)) S.processH ∧
    IsLogicalInductor (project S.Hplus (projAtomCode k) (fun _ => c')) S.processH ∧
    (∀ n m, project S.Hplus (projAtomCode k) (fun _ => c) m (S.contract n) = S.Hplus m (S.contract n) ∧
      project S.Hplus (projAtomCode k) (fun _ => c') m (S.contract n) = S.Hplus m (S.contract n)) ∧
    (limitingBelief (project S.Hplus (projAtomCode k) (fun _ => c)) (projAtom k) = c ∧
      limitingBelief (project S.Hplus (projAtomCode k) (fun _ => c')) (projAtom k) = c') := by
  haveI := S.Hplus_inductor
  have hfree : AtomFreeProcess (projAtomCode k) S.processH := atomFreeProcess_ledgerProcess k hbase
  refine ⟨project_const_isLogicalInductor S.Hplus S.processH _ hfree c hc0 hc1,
    project_const_isLogicalInductor S.Hplus S.processH _ hfree c' hc'0 hc'1, fun n m => ?_, ?_⟩
  · have hφ : AtomFreeSentence (projAtomCode k) (S.contract n) :=
      atomFreeSentence_of_tagFree (S.contract_projFree n) k
    exact ⟨project_restrict S.Hplus _ _ m hφ, project_restrict S.Hplus _ _ m hφ⟩
  · exact ⟨limitingBelief_project_const_atom S.Hplus S.processH S.hworldH _ c,
      limitingBelief_project_const_atom S.Hplus S.processH S.hworldH _ c'⟩

/-- **The mandate's day-set instantiation** of `li-projection`'s `underdetermination_daySet` at
`G = {n | Timely S ε n}` with the test family `offGFamily` (the contract on `G`, the projection
atom off `G`): the two projections agree on `P^{(n)}` at every day for `n ∈ G` and have limits
`c`, `c'` on `offGFamily … n` for `n ∉ G`. Kept for the record of the mandate's shape; **`Timely`
does no work** — the agreement conjunct holds on every contract at every day
(`projection_pair_offG_atom`), and off `G` the family is the single atom `projAtom k` at every
day, so the limits conjunct is one fact wrapped in a quantifier over off-`G` days. Not a
headline. `partial: over li-projection's OPEN rewriters`.
Source: mandate T7 (off `G`: "instantiate `underdetermination_daySet` at `Timely`"); audit r1 adversarial B2 (the disclosure)
Kind: L (instance of `li-projection`'s `underdetermination_daySet`)
Fidelity: weaker: as `projection_pair_offG_atom`; the day-set is inert
Hyps: (a) throughout; conjuncts (1) rest on the OPEN rewriters -/
theorem projection_pair_daySet (S : FrozenSystem) (ε : ℕ → ℚ) (k : ℕ)
    (hbase : AtomFreeProcess (projAtomCode k) S.base) (c c' : ℚ) (hc0 : 0 < c) (hc1 : c < 1)
    (hc'0 : 0 < c') (hc'1 : c' < 1) :
    IsLogicalInductor (project S.Hplus (projAtomCode k) (fun _ => c)) S.processH ∧
    IsLogicalInductor (project S.Hplus (projAtomCode k) (fun _ => c')) S.processH ∧
    (∀ n, Timely S ε n → ∀ m, project S.Hplus (projAtomCode k) (fun _ => c) m (S.contract n) =
      project S.Hplus (projAtomCode k) (fun _ => c') m (S.contract n)) ∧
    (∀ n, ¬ Timely S ε n →
      limitingBelief (project S.Hplus (projAtomCode k) (fun _ => c)) (offGFamily S ε k n) = c ∧
      limitingBelief (project S.Hplus (projAtomCode k) (fun _ => c')) (offGFamily S ε k n) = c') := by
  haveI := S.Hplus_inductor
  have hfree : AtomFreeProcess (projAtomCode k) S.processH := atomFreeProcess_ledgerProcess k hbase
  have hG : ∀ n ∈ {n | Timely S ε n}, AtomFreeSentence (projAtomCode k) (offGFamily S ε k n) := by
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    rw [offGFamily, if_pos hn]
    exact atomFreeSentence_of_tagFree (S.contract_projFree n) k
  have hG' : ∀ n ∉ {n | Timely S ε n}, offGFamily S ε k n = Formula.atom (projAtomCode k) := by
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    rw [offGFamily, if_neg hn]
    rfl
  obtain ⟨h1, h2, h3, h4⟩ := underdetermination_daySet S.Hplus S.processH S.hworldH
    (projAtomCode k) hfree {n | Timely S ε n} (offGFamily S ε k) hG hG' c c' hc0 hc1 hc'0 hc'1
  refine ⟨h1, h2, fun n hn m => ?_, fun n hn => h4 n hn⟩
  have := h3 n hn m
  rwa [offGFamily, if_pos hn] at this

/-! ## D. T7(ii) on the undecidable fragment: a bare-atom contract, projected on its own atom
(repair round 2, audit r2 fidelity N1) -/

/-- A contract that is a bare atom never mentioned by the advised reasoner's process (hence by the
shared process, which it contains stage-wise) is in the undecidable fragment.
Source: audit r2 fidelity N1 (probe `UndecidableContract.lean`); [[frozen-deliberation-deference-v6]] §6 ("Undecidable — never settles")
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem undecidable_of_atomFree (S : FrozenSystem) (n₀ u : ℕ) (hc : S.contract n₀ = Formula.atom u)
    (hfree : AtomFreeProcess u S.processH) : Undecidable S n₀ := by
  rintro ⟨m, h | h⟩
  · have := hfree m _ (S.base_subset_processH m h)
    rw [hc] at this
    exact this (by simp [sentenceAtomCodes_atom])
  · have := hfree m _ (S.base_subset_processH m h)
    rw [hc] at this
    exact this (by simp [sentenceAtomCodes_neg, sentenceAtomCodes_atom])

/-- **T7(ii) for an undecidable bare-atom contract, on this carrier** (headline companion of
`projection_pair_offG_atom`; `partial: over li-projection's OPEN rewriters`). For a contract
`P^{(n₀)}` that is a bare atom `u` the advised reasoner's process never mentions (so `n₀` is in the
undecidable fragment, `undecidable_of_atomFree`) and any `c, c' ∈ (0,1)`: projecting `Hplus` on
the contract's **own** atom gives two histories that are (1) both logical inductors over
`processH` (modulo `li-projection`'s OPEN rewriters, exactly as `projection_pair_offG_atom`);
(2) equal to `Hplus` itself on every sentence free of `u` — every ledger sentence and every other
contract free of `u`, at every day; (3) agree with each other on every such contract at every day;
and (4) have limiting beliefs `c` and `c'` **on `P^{(n₀)}` itself**: the source's nondegenerate
interval of achievable `H⁺_∞(P)` for a fixed undecidable `P`. What remains with `li-projection`'s
OPEN `multiplicity_entangled`: an undecidable contract that is not a bare atom (entangled with
the process). No inhabitant on disk has an undecidable contract (`offGSystem`, `onGSystem`,
`antiSystem` decide every day); the one-way instance is `offGSystem`'s construction with the
contract schedule dropped (the contract atoms are family `16`, which `paperDP` and the ledger never
mention) — not built (report §Next steps). Roles: `Hplus` the advised reasoner. One-way.
Source: [[frozen-deliberation-deference-v6]] T7 (line 136, "off `G` the limit is underdetermined"); [[deference-in-logical-induction-v6]] §5.6 T7(ii) (root-deference-044 (ii)); audit r2 fidelity N1 (probe `UndecidableContract.lean`)
Kind: L (`li-projection`'s three facts composed, as `projection_pair_offG_atom`)
Fidelity: exact for an undecidable bare-atom contract (the source's "fixed off-`G` `P`" restricted to the fragment where T7(ii) is true, findings F16); an entangled undecidable contract is not covered
Hyps: (a) throughout (`hc`, `hfree` are the contract's data); conjuncts (1) rest on the OPEN rewriters -/
theorem projection_pair_undecidable_contract (S : FrozenSystem) (n₀ u : ℕ)
    (hc : S.contract n₀ = Formula.atom u) (hfree : AtomFreeProcess u S.processH)
    (c c' : ℚ) (hc0 : 0 < c) (hc1 : c < 1) (hc'0 : 0 < c') (hc'1 : c' < 1) :
    IsLogicalInductor (project S.Hplus u (fun _ => c)) S.processH ∧
    IsLogicalInductor (project S.Hplus u (fun _ => c')) S.processH ∧
    (∀ φ, AtomFreeSentence u φ → ∀ m,
      project S.Hplus u (fun _ => c) m φ = S.Hplus m φ ∧
      project S.Hplus u (fun _ => c') m φ = S.Hplus m φ) ∧
    (∀ n, AtomFreeSentence u (S.contract n) → ∀ m,
      project S.Hplus u (fun _ => c) m (S.contract n) =
        project S.Hplus u (fun _ => c') m (S.contract n)) ∧
    (limitingBelief (project S.Hplus u (fun _ => c)) (S.contract n₀) = c ∧
      limitingBelief (project S.Hplus u (fun _ => c')) (S.contract n₀) = c') := by
  haveI := S.Hplus_inductor
  refine ⟨project_const_isLogicalInductor S.Hplus S.processH u hfree c hc0 hc1,
    project_const_isLogicalInductor S.Hplus S.processH u hfree c' hc'0 hc'1,
    fun φ hφ m => ⟨project_restrict S.Hplus u _ m hφ, project_restrict S.Hplus u _ m hφ⟩,
    fun n hn m => by rw [project_restrict S.Hplus u _ m hn, project_restrict S.Hplus u _ m hn],
    ?_⟩
  rw [hc]
  exact ⟨limitingBelief_project_const_atom S.Hplus S.processH S.hworldH u c,
    limitingBelief_project_const_atom S.Hplus S.processH S.hworldH u c'⟩

end Cleanroom.Deference.DefFrozenSibling
