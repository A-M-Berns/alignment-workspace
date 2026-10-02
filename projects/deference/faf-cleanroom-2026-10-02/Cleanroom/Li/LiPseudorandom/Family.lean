import Cleanroom.Li.LiPseudorandom.Fixed
import Cleanroom.Li.LiPseudorandom.AtomDP
import Cleanroom.Li.LiPseudorandom.Countable
import LogicalInduction.Properties.SelfTrust
import LogicalInduction.Construction.Statistics.HistoricalMaturity

/-!
# `li-pseudorandom` — T6.3: the family of record

`truthStar a g p := diagBuilder (fun x => liaHistory (atomDP a x g)) genWeighting (fun _ => p)`: the
diagonal sequence over the clamped denotations of every P-generable weighting on the LIA over the
process that decides the family itself. A `def` built from `diag`, not a `Classical.choose`;
noncomputable as written (T7, `Computable.lean`, is the computability certificate). Since repair
round 1 the enumeration `genWeighting` is the explicit, primitive recursive machine enumeration
(`Countable.lean`, `genWeighting_primrec`), not a chosen surjection, so the family is determined
by its definition and the only non-program ingredient is the LIA's quotes. The rules read the
market built from the truth *prefix* (`builderRule`), which is why the definition needs no
causality hypothesis; under `liaHistory_atomDP_causal` this equals the mandate's `truth⋆`
(`builderRule_w_eq`).

* `truthStar_pseudorandom_all` — the paper's `def:pseudorandom` with frequency `p` over all
  P-generable weightings divergent on the LIA over `atomDP a (truthStar a g p) g`;
* `truthStar_pseudorandom` — FAF's `PseudorandomFrequency (truthR (truthStar a g p)) p f
  (liaHistory (atomDP a (truthStar a g p) g))` for **every** `f`; hypotheses `0 ≤ p ≤ 1` and
  `∀ j, j < g j` only, all (a);
* the benford-ready bundle for this family: `truthStar_theoryTruth`, `truthStar_hworld`, and
  `MachineSentenceCodes (atomFamily a)` as a parameter (discharged for `a = id` by
  `machineSentenceCodes_atomFamily_id`);
* `truthStar_learned` — `liaHistory (atomDP …) n (atom (a n)) ≈ₙ p` by FAF's
  `lic_learning_pseudorandom_frequency` (`thm:benford`), **under the instance
  `IsLogicalInductor (liaHistory (atomDP …)) (atomDP …)`, which is T7's certificate** (OPEN if so
  listed in `li-pseudorandom-open.txt`): its row is `partial: over OPEN computability (T7)` until
  T7 lands, never `proved`.

Scope (verbatim, per the mandate): **the LIA over `atomDP`; `IsLogicalInductor` is T7's
certificate (OPEN if so listed).** "Pseudorandom" here means relative to `PGenerableWeighting` on
this market — not Martin-Löf random; the family is (by T7's intent) computable, hence not random in
any absolute sense. `LIACompiler` is not imported here.
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction Filter Topology

/-- **The family of record.** `diagBuilder` over the builder `x ↦ liaHistory (atomDP a x g)` and
the explicit enumeration `genWeighting` of FAF's P-generable weightings (`Countable.lean`,
primitive recursive), at constant target `p`. A `def` from `diag`; noncomputable as written — T7
is the computability certificate. Meaningful instances have `Function.Injective a` (otherwise a
stage may contain both a literal and its negation, no `hworld` exists, and `thm:benford` does not
apply); the pseudorandomness theorems below do not need it.
Source: mandate T6.3; [[anson-inventory]] anson-034; [[bli-program]] §3.2(b) (L3), §3.6(iii) (K3)
Kind: D
Fidelity: variant: the rules are evaluated on the market built from the truth prefix
(`builderRule` reads `B (restrict x n)`, not `B x`); equal to the mandate's `truth⋆` under
`CausalBuilder`, which `liaHistory_atomDP_causal` supplies (`builderRule_w_eq`) -/
noncomputable def truthStar (a g : ℕ → ℕ) (p : ℝ) : ℕ → Bool :=
  diagBuilder (fun x => liaHistory (atomDP a x g)) genWeighting (fun _ => p)

/-- **T6.3, paper form.** For every P-generable weighting `W` divergent on the LIA over
`atomDP a (truthStar a g p) g`, the `W`-weighted truth frequency of the family of record tends to
`p`: the LI paper's `def:pseudorandom` over all P-generable divergent weightings, relative to the
inductor of record. Hypotheses: `0 ≤ p ≤ 1`, `∀ j, j < g j`.
Scope: the LIA over `atomDP`; `IsLogicalInductor` is T7's certificate (OPEN if so listed) — not
needed for this statement, which is about the LIA's prices as a `History`.
Source: mandate T6.3; LI paper `def:pseudorandom` (`main.tex:1273`); [[anson-inventory]] anson-034
Kind: C
Fidelity: exact (paper's definition, relative to the LIA over `atomDP`)
Hyps: (a) -/
theorem truthStar_pseudorandom_all (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) :
    ∀ W : ℕ → EF, PGenerableWeighting W →
      DivergentWeighting W (liaHistory (atomDP a (truthStar a g p) g)) →
      weightedAverage (fun i => (W i).denote (liaHistory (atomDP a (truthStar a g p) g)))
        (truthR (truthStar a g p)) ≈ₙ (fun _ => p) :=
  diagBuilder_pseudorandom_of_causal (fun x => liaHistory (atomDP a x g)) g
    (liaHistory_atomDP_causal a g) hg genWeighting genWeighting_covers p hp

/-- **T6.3, the package's headline.** The family of record inhabits FAF's `PseudorandomFrequency`
at frequency `p` relative to the LIA over its own deciding process, for **every** deferral
function `f`. Hypotheses: `0 ≤ p ≤ 1`, `∀ j, j < g j` — all (a).
Scope: the LIA over `atomDP`; `IsLogicalInductor` is T7's certificate (OPEN if so listed) — not
needed here.
Source: mandate T6.3; FAF `PseudorandomFrequency` (`Properties/Pseudorandomness.lean`)
Kind: C
Fidelity: stronger: all `f` at once, relative to `def:pseudorandom`
Hyps: (a) -/
theorem truthStar_pseudorandom (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ∀ f : DeferralFunction, PseudorandomFrequency (truthR (truthStar a g p)) p f
      (liaHistory (atomDP a (truthStar a g p) g)) :=
  -- No `Injective a` is needed here (stronger than the mandate asked); the meaningful instances
  -- are injective `a`, for which `hworld` exists and `thm:benford` applies (`truthStar_learned`).
  pseudorandomFrequency_of_causal (fun x => liaHistory (atomDP a x g)) g
    (liaHistory_atomDP_causal a g) hg genWeighting genWeighting_covers p hp

/-- `TheoryTruth` for the family of record (derived from the stages).
Source: mandate T6.3 (benford-ready bundle)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem truthStar_theoryTruth (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (p : ℝ) :
    AffineCombination.TheoryTruth (atomFamily a) (atomDP a (truthStar a g p) g)
      (truthR (truthStar a g p)) :=
  atomDP_theoryTruth hg _

/-- `hworld` for the family of record: a side condition derived from the stages (the atom world
is consistent with every stage under `Injective a`); its non-vacuity role — no stage is
unsatisfiable, so `isLogicalInductor_of_stage_unsatisfiable` does not apply — is a remark, not a
witness.
Source: mandate T6.3 (benford-ready bundle)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem truthStar_hworld {a : ℕ → ℕ} (ha : Function.Injective a) (g : ℕ → ℕ) (p : ℝ) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((atomDP a (truthStar a g p) g).D n) :=
  atomDP_hworld ha _ g

/-- **`thm:benford` for the family of record**: the LIA's price of `atom (a n)` on day `n` tends
to `p`. By FAF's `lic_learning_pseudorandom_frequency` with every hypothesis discharged here
except two: `MachineSentenceCodes (atomFamily a)` (a parameter; (a) for `a = id` by
`machineSentenceCodes_atomFamily_id`, and (a) when a dependent's allocator certifies it) and the
instance **`IsLogicalInductor (liaHistory (atomDP …)) (atomDP …)`, which is T7's certificate**
(`OPEN T7` while `truthStar_isLogicalInductor` is listed open). The instance's field
`processComputable` is, at `a = id`, the open statement `starDP_computable` itself: this
hypothesis package is **not yet known to be inhabited** for `truthStar` as defined — it will be
exactly when T7 lands. Its ledger row is `partial: over OPEN computability (T7)` until then. For
a non-computable `a` the instance has no inhabitant at all (a computable stage encoder reads
`a n` off the stage difference), so the meaningful instances are injective **and computable**
`a` (round-2 adversarial audit, item 4).
Scope: the LIA over `atomDP`; `IsLogicalInductor` is T7's certificate (OPEN if so listed).
Source: mandate T6.3; FAF `lic_learning_pseudorandom_frequency` (`thm:benford`)
Kind: C
Fidelity: exact
Hyps: (a) except the `IsLogicalInductor` instance (OPEN T7; not known inhabited for the object of
record) and `hcodes` ((a)-when-discharged parameter) -/
theorem truthStar_learned (a g : ℕ → ℕ) (ha : Function.Injective a) (hg : ∀ j, j < g j)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hcodes : MachineSentenceCodes (atomFamily a))
    [IsLogicalInductor (liaHistory (atomDP a (truthStar a g p) g)) (atomDP a (truthStar a g p) g)] :
    (fun n => liaHistory (atomDP a (truthStar a g p) g) n (atomFamily a n)) ≈ₙ (fun _ => p) :=
  lic_learning_pseudorandom_frequency (liaHistory (atomDP a (truthStar a g p) g))
    (atomDP a (truthStar a g p) g) (atomFamily a) hcodes (truthR (truthStar a g p))
    (truthStar_theoryTruth a g hg p) p hp (truthStar_hworld ha g p) succDeferral
    (truthStar_pseudorandom a g hg p hp succDeferral)

/-- **Decided-with-delay for the family of record**: `atom (a n)` is in stage `m` iff its delay
day has arrived and the member is true; the negation likewise. What `bli-linkage` K3 (delay one,
`g := fun n => n + 1`) and `bli-leak` L3 (its own `g`) cite.
Source: mandate T6.1/T6.3; [[bli-program]] §3.2(b), §3.6(iii)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem truthStar_atom_mem_iff {a : ℕ → ℕ} (ha : Function.Injective a) {g : ℕ → ℕ}
    (hg : ∀ j, j < g j) (p : ℝ) {n m : ℕ} :
    (LO.Propositional.Formula.atom (a n) : Sentence) ∈ (atomDP a (truthStar a g p) g).D m ↔
      g n ≤ m ∧ truthStar a g p n = true :=
  atom_mem_atomDP_iff ha hg

end Cleanroom.Li.LiPseudorandom
