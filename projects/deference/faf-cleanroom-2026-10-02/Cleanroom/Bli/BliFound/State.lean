import Cleanroom.Bli.BliFound.Extend
import Cleanroom.Bli.BliFound.Size

/-!
# `bli-found` · State: state atoms, the state-learning process, policy atoms (F5's objects)

**D4 / T5** of the mandate.

* `stateAtom m q` is `⌜𝑸_m = Q̂⌝` for the written-out state with write-out *code* `q` (family
  `0`, day first). **(deviation)** The program types it over `bli-finite`'s `Table m`; this package
  has no edge to `bli-finite` (plan §0.4 rule 10), so the atom takes the code and the table
  instantiation is `bli-trajectory`'s. `policyPoint m q a` (`⌜π(Q̂) = a⌝`, family `1`) and
  `actionAt m a` (`A_m = a`, family `2`) likewise.
* **Largeness is a theorem about the write-out, not a stipulation**: `stateAtom_large` (a code
  with `Nat.log 4 q ≥ sizeBound m` is large on every day `≤ m`), `stateAtom_small` (the converse
  side), and `stateAtom_large_of_writeOut` — the honest form of bli-paper-032's "longer than every
  sentence it prices": any write-out with one digit block per listed element of `smallSet m` has
  `Nat.log 4 q ≥ (smallSet m).card > sizeBound m` (`Size.sizeBound_lt_card_smallSet`). Note
  (finding): with `sizeBound n = 2^{2^n}` such an atom is large on day `m` (the program's `∀ n < m`
  should read `∀ n ≤ m`) and becomes small only around day `log₂ log₂ q`, not `m + 1`.
* `stateProcess states actual` (bli-paper-038, bli-soto-a-003's "final detail"): at stage `s`,
  for every `m < s`, `stateAtom m (actual m)` and `∼stateAtom m q` for every other `q ∈ states m`
  (exclusivity) — an instance of `Extend.literalProcess` (family `0`), so monotone by
  construction and *functional without any hypothesis* (the positive entry is the actual state's,
  the negative ones are the others'). `bliDP DP states actual := extendBy DP (stateSchedule …)`.
* Everything about `bliDP` is derived from `Extend`: `bliDP_hworld` (from the base's `hworld` and
  its freeness for the state tag), `bliDP_exclusive`, `bliDP_conservative`, `bliDP_computable`.
  The instance at `paperDP 𝗜𝚺₁` — the guard against program §7.4 — is in `PaperInstances.lean`.
* `policyLinkProcess`: the stage family `stateAtom m q ⋏ policyPoint m q a 🡒 actionAt m a`,
  with its `hworld` and computability transports only; its use is `udt-bli-core`'s.

Index conventions: days go `m → m + 1`; no `Nat` subtraction in day arithmetic.

Sources: bli-paper-032, 038; bli-soto-a-003; [[bli-program]] §2.3; mandate D4/T5.
-/

namespace Cleanroom.Bli.BliFound

open LogicalInduction LO.Propositional

/-! ## The three atom families -/

/-- Family of the state atoms in the registry on `freshAtom`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev stateFamily : ℕ := 0
/-- Family of the policy points.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev policyFamily : ℕ := 1
/-- Family of the realized-action atoms.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev actionFamily : ℕ := 2

/-- The tag carried by every state atom: `cleanroomBaseTag + stateFamily`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev stateTag : ℕ := cleanroomBaseTag + stateFamily
/-- The tag carried by every policy point.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev policyTag : ℕ := cleanroomBaseTag + policyFamily
/-- The tag carried by every realized-action atom.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev actionTag : ℕ := cleanroomBaseTag + actionFamily

/-- **`⌜𝑸_m = Q̂⌝`** for the written-out state with write-out code `q`: family `0`, day first.
Source: bli-paper-032, bli-soto-a-003, [[bli-program]] §2.3; mandate D4
Kind: D
Fidelity: variant: takes the write-out *code* `q : ℕ` rather than `bli-finite`'s `Table m`
(deviation, see module docstring) -/
def stateAtom (m q : ℕ) : Sentence := freshAtom stateFamily (Nat.pair m q)

/-- **`⌜π(Q̂) = a⌝`**: the policy point at day `m`, state code `q`, action `a`; family `1`.
Source: [[bli-program]] §2.3; mandate D4
Kind: D
Fidelity: variant: codes for the state and the action -/
def policyPoint (m q a : ℕ) : Sentence := freshAtom policyFamily (Nat.pair m (Nat.pair q a))

/-- **`A_m = a`**: the realized-action atom at day `m`; family `2`.
Source: [[bli-program]] §2.3; mandate D4
Kind: D
Fidelity: variant: a fresh atom (the program calls it a computation-output claim; that
encoding is `bli-linkage`'s) -/
def actionAt (m a : ℕ) : Sentence := freshAtom actionFamily (Nat.pair m a)

/-- `stateAtom_inj`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateAtom_inj {m q m' q' : ℕ} : stateAtom m q = stateAtom m' q' ↔ m = m' ∧ q = q' := by
  unfold stateAtom
  rw [freshAtom_inj]
  simp [Nat.pair_eq_pair]

/-- State atoms are injective in `(m, q)`.
Source: mandate T5.1
Kind: L
Fidelity: exact -/
lemma stateAtom_injective : Function.Injective (fun p : ℕ × ℕ => stateAtom p.1 p.2) := by
  rintro ⟨m, q⟩ ⟨m', q'⟩ h
  obtain ⟨rfl, rfl⟩ := stateAtom_inj.mp h
  rfl

/-- `policyPoint_inj`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyPoint_inj {m q a m' q' a' : ℕ} :
    policyPoint m q a = policyPoint m' q' a' ↔ m = m' ∧ q = q' ∧ a = a' := by
  unfold policyPoint
  rw [freshAtom_inj]
  simp [Nat.pair_eq_pair]

/-- `actionAt_inj`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma actionAt_inj {m a m' a' : ℕ} : actionAt m a = actionAt m' a' ↔ m = m' ∧ a = a' := by
  unfold actionAt
  rw [freshAtom_inj]
  simp [Nat.pair_eq_pair]

/-- `stateAtom_ne_policyPoint`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateAtom_ne_policyPoint (m q m' q' a : ℕ) : stateAtom m q ≠ policyPoint m' q' a :=
  freshAtom_ne_of_family_ne (by decide)

/-- `stateAtom_ne_actionAt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateAtom_ne_actionAt (m q m' a : ℕ) : stateAtom m q ≠ actionAt m' a :=
  freshAtom_ne_of_family_ne (by decide)

/-- `policyPoint_ne_actionAt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyPoint_ne_actionAt (m q a m' a' : ℕ) : policyPoint m q a ≠ actionAt m' a' :=
  freshAtom_ne_of_family_ne (by decide)

/-- The one atom index of a state atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma sentenceAtomCodes_stateAtom (m q : ℕ) :
    sentenceAtomCodes (stateAtom m q) = {freshAtomCode stateFamily (Nat.pair m q)} := rfl

/-- `stateAtom_tag`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateAtom_tag (m q : ℕ) : ∀ a ∈ sentenceAtomCodes (stateAtom m q), a.unpair.1 = stateTag :=
  freshAtom_tag _ _

/-- `stateAtom_ne_faf`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateAtom_ne_faf (m q : ℕ) : ∀ a ∈ sentenceAtomCodes (stateAtom m q), 8 < a.unpair.1 :=
  freshAtom_ne_faf _ _

/-- `policyPoint_tag`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyPoint_tag (m q a : ℕ) :
    ∀ b ∈ sentenceAtomCodes (policyPoint m q a), b.unpair.1 = policyTag :=
  freshAtom_tag _ _

/-- `actionAt_tag`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma actionAt_tag (m a : ℕ) : ∀ b ∈ sentenceAtomCodes (actionAt m a), b.unpair.1 = actionTag :=
  freshAtom_tag _ _

/-- A state atom is tag-free for every tag but its own.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateAtom_tagFree_of_ne {m q t : ℕ} (h : t ≠ stateTag) : TagFreeSentence t (stateAtom m q) :=
  freshAtom_tagFree_of_ne h

/-- `policyPoint_tagFree_of_ne`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyPoint_tagFree_of_ne {m q a t : ℕ} (h : t ≠ policyTag) :
    TagFreeSentence t (policyPoint m q a) :=
  freshAtom_tagFree_of_ne h

/-- `actionAt_tagFree_of_ne`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma actionAt_tagFree_of_ne {m a t : ℕ} (h : t ≠ actionTag) : TagFreeSentence t (actionAt m a) :=
  freshAtom_tagFree_of_ne h

/-- The day a state atom refers to is `m`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomDay_stateAtom (m q : ℕ) : ∀ a ∈ sentenceAtomCodes (stateAtom m q), atomDay a = m := by
  intro a ha
  rw [sentenceAtomCodes_stateAtom, Finset.mem_singleton] at ha
  subst ha
  simp

/-- A day-`m` state atom is never in `Sminus n m` (it quotes day `m`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateAtom_notMem_Sminus (n m q : ℕ) : stateAtom m q ∉ Sminus n m := by
  rw [mem_Sminus]
  rintro ⟨-, h⟩
  have := h _ (Finset.mem_singleton_self _)
  rw [atomDay_stateAtom m q _ (Finset.mem_singleton_self _)] at this
  exact lt_irrefl _ this

/-! ## Size of a state atom: largeness as a theorem -/

/-- The exact size of a state atom (from `tokenSize_atom`).
Source: mandate T5.1
Kind: L
Fidelity: exact -/
lemma tokenSize_stateAtom (m q : ℕ) :
    tokenSize (stateAtom m q) =
      (natDigits4 (freshAtomCode stateFamily (Nat.pair m q) + 5)).length + 1 := by
  unfold stateAtom freshAtom
  rw [tokenSize_atom]

/-- `tokenSize_stateAtom_eq_log`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tokenSize_stateAtom_eq_log (m q : ℕ) :
    tokenSize (stateAtom m q) = Nat.log 4 (freshAtomCode stateFamily (Nat.pair m q) + 5) + 2 := by
  rw [tokenSize_stateAtom, length_natDigits4_eq_log (by omega)]

/-- The write-out code is dominated by the atom index.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma le_freshAtomCode_pair (f m q : ℕ) : q ≤ freshAtomCode f (Nat.pair m q) :=
  le_trans (Nat.right_le_pair m q) (Nat.right_le_pair _ _)

/-- **A state atom with a long write-out is large on every day up to its own.** If
`sizeBound m ≤ Nat.log 4 q` then `stateAtom m q` is not small on any day `n ≤ m`.
Source: bli-paper-032; [[bli-program]] §2.3 (corrected `< m` → `≤ m`, Known issue 6); mandate D4
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem stateAtom_large {m q : ℕ} (h : sizeBound m ≤ Nat.log 4 q) :
    ∀ n ≤ m, ¬ SmallOn n (stateAtom m q) := by
  intro n hn hsmall
  unfold SmallOn at hsmall
  rw [tokenSize_stateAtom_eq_log] at hsmall
  have h1 : Nat.log 4 q ≤ Nat.log 4 (freshAtomCode stateFamily (Nat.pair m q) + 5) :=
    Nat.log_mono_right (le_trans (le_freshAtomCode_pair _ _ _) (Nat.le_add_right _ 5))
  have h2 := sizeBound_mono hn
  omega

/-- **The converse side**: a state atom whose index fits in the day's digit budget is small.
Source: mandate D4
Kind: L
Fidelity: exact -/
theorem stateAtom_small {n m q : ℕ}
    (h : (natDigits4 (freshAtomCode stateFamily (Nat.pair m q) + 5)).length + 1 ≤ sizeBound n) :
    SmallOn n (stateAtom m q) := by
  unfold SmallOn
  rw [tokenSize_stateAtom]
  exact h

/-- Every sentence is small from day `tokenSize φ` on (`k ≤ 2^{2^k}`): largeness is always
temporary.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma smallOn_tokenSize (φ : Sentence) : SmallOn (tokenSize φ) φ := by
  unfold SmallOn sizeBound
  calc tokenSize φ ≤ 2 ^ tokenSize φ := Nat.lt_two_pow_self.le
    _ ≤ 2 ^ (2 ^ tokenSize φ) := Nat.pow_le_pow_right (by norm_num) Nat.lt_two_pow_self.le

/-- `exists_smallOn`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exists_smallOn (φ : Sentence) : ∃ n, SmallOn n φ := ⟨_, smallOn_tokenSize φ⟩

/-- **bli-paper-032's "longer than every sentence it prices", honestly.** Take any write-out
`writeOut : List ℕ → ℕ` that spends at least one base-4 digit per listed element
(`l.length ≤ Nat.log 4 (writeOut l)` — any injective `Nat.ofDigits`-style listing with one
digit block per element does). A list of length `≥ (smallSet m).card` — a table over the day-`m`
small sentences — then writes out to a code whose state atom is large on every day `≤ m`, from
day `m ≥ 1` on (`sizeBound_lt_card_smallSet`).
Source: bli-paper-032; mandate D4
Kind: C
Fidelity: exact (day `0` excluded: `smallSet 0 = {⊥}`)
Hyps: (a) the digit-budget property of `writeOut` is the hypothesis the table encoding
(`bli-trajectory`) discharges -/
theorem stateAtom_large_of_writeOut (writeOut : List ℕ → ℕ)
    (hw : ∀ l, l.length ≤ Nat.log 4 (writeOut l)) {m : ℕ} (hm : 1 ≤ m) (l : List ℕ)
    (hl : (smallSet m).card ≤ l.length) :
    ∀ n ≤ m, ¬ SmallOn n (stateAtom m (writeOut l)) := by
  apply stateAtom_large
  have := sizeBound_lt_card_smallSet hm
  have := hw l
  omega

/-- The digit-budget hypothesis of `stateAtom_large_of_writeOut` is satisfiable (N−: the
trivial write-out `4 ^ l.length`; an injective one is `bli-trajectory`'s). -/
example : ∀ l : List ℕ, l.length ≤ Nat.log 4 (4 ^ l.length) := fun l => by
  rw [Nat.log_pow (by norm_num)]

/-! ## The state schedule and `bliDP` -/

/-- The entries of the state schedule at stage `s`: for every day `m < s`, the positive entry
for the actual state and, for every `q ∈ states m`, the entry `(0, ⟨m, q⟩, decide (q = actual m))`
— positive exactly for the actual state (so the entry set is functional whether or not
`actual m ∈ states m`).
Source: bli-paper-038; bli-soto-a-003 ("final detail"); mandate D4
Kind: D
Fidelity: exact -/
def stateEntries (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) (s : ℕ) : Finset (ℕ × ℕ × Bool) :=
  (Finset.range s).biUnion fun m =>
    insert (stateFamily, Nat.pair m (actual m), true)
      ((states m).image fun q => (stateFamily, Nat.pair m q, decide (q = actual m)))

/-- `mem_stateEntries`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_stateEntries {states : ℕ → Finset ℕ} {actual : ℕ → ℕ} {s : ℕ} {x : ℕ × ℕ × Bool} :
    x ∈ stateEntries states actual s ↔
      ∃ m < s, x = (stateFamily, Nat.pair m (actual m), true) ∨
        ∃ q ∈ states m, x = (stateFamily, Nat.pair m q, decide (q = actual m)) := by
  simp only [stateEntries, Finset.mem_biUnion, Finset.mem_range, Finset.mem_insert,
    Finset.mem_image]
  constructor
  · rintro ⟨m, hm, h | ⟨q, hq, h⟩⟩
    · exact ⟨m, hm, Or.inl h⟩
    · exact ⟨m, hm, Or.inr ⟨q, hq, h.symm⟩⟩
  · rintro ⟨m, hm, h | ⟨q, hq, h⟩⟩
    · exact ⟨m, hm, Or.inl h⟩
    · exact ⟨m, hm, Or.inr ⟨q, hq, h.symm⟩⟩

/-- **The state schedule**: `stateEntries`, monotone in the stage.
Source: bli-paper-038; mandate D4
Kind: D
Fidelity: exact -/
def stateSchedule (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) : LiteralSchedule where
  lits := stateEntries states actual
  mono s := Finset.biUnion_subset_biUnion_of_subset_left _
    (fun _ hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.le_succ s)))

/-- The state schedule's stages are `stateEntries`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma stateSchedule_lits (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) (s : ℕ) :
    (stateSchedule states actual).lits s = stateEntries states actual s := rfl

/-- The state schedule is functional, with no hypothesis: a positive entry is the actual
state's, a negative entry is another state's.
Source: mandate T3 trap (i) / T5
Kind: L
Fidelity: exact -/
lemma stateSchedule_functional (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) :
    (stateSchedule states actual).Functional := by
  rintro s f p ⟨hpos, hneg⟩
  rw [stateSchedule_lits, mem_stateEntries] at hpos hneg
  obtain ⟨m, -, hm⟩ := hpos
  obtain ⟨m', -, hm'⟩ := hneg
  -- the positive entry has payload `⟨m, actual m⟩`
  have hp : p = Nat.pair m (actual m) := by
    rcases hm with h | ⟨q, -, h⟩
    · simp only [Prod.mk.injEq] at h; exact h.2.1
    · simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl, hb⟩ := h
      have : q = actual m := by simpa using hb.symm
      rw [this]
  -- the negative entry has payload `⟨m', q'⟩` with `q' ≠ actual m'`
  rcases hm' with h | ⟨q', -, h⟩
  · simp at h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨-, hp', hb⟩ := h
    have hq' : q' ≠ actual m' := by simpa using hb.symm
    rw [hp, Nat.pair_eq_pair] at hp'
    exact hq' (by rw [← hp'.1, hp'.2])

/-- The state schedule uses family `0` only.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateSchedule_families (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) :
    ∀ f ∈ (stateSchedule states actual).families, f = stateFamily := by
  rintro f ⟨s, _x, hx, rfl⟩
  rw [stateSchedule_lits, mem_stateEntries] at hx
  obtain ⟨m, -, h | ⟨q, -, h⟩⟩ := hx <;> (subst h; rfl)

/-- **The state-learning process** (bli-paper-038): the literal process of the state schedule.
Source: bli-paper-038; bli-soto-a-003; [[bli-program]] §2.3; mandate D4
Kind: D
Fidelity: exact -/
def stateProcess (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) : DeductiveProcess :=
  literalProcess (stateSchedule states actual)

/-- **`bliDP`**: the base process with the state-learning process adjoined.
Source: [[bli-program]] §2.3; mandate D4
Kind: D
Fidelity: exact -/
def bliDP (DP : DeductiveProcess) (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) : DeductiveProcess :=
  extendBy DP (stateSchedule states actual)

/-- `bliDP_eq_union`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma bliDP_eq_union (DP : DeductiveProcess) (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) :
    bliDP DP states actual = DP.union (stateProcess states actual) := rfl

/-- A stage of `bliDP`: the base stage plus the state literals.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma bliDP_D (DP : DeductiveProcess) (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) (s : ℕ) :
    (bliDP DP states actual).D s = DP.D s ∪ (stateEntries states actual s).image literalOf := rfl

/-- The actual state's atom is in every stage after its day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateAtom_actual_mem_bliDP (DP : DeductiveProcess) (states : ℕ → Finset ℕ)
    (actual : ℕ → ℕ) {m s : ℕ} (hm : m < s) :
    stateAtom m (actual m) ∈ (bliDP DP states actual).D s := by
  rw [bliDP_D, Finset.mem_union, Finset.mem_image]
  refine Or.inr ⟨(stateFamily, Nat.pair m (actual m), true), ?_, rfl⟩
  rw [mem_stateEntries]
  exact ⟨m, hm, Or.inl rfl⟩

/-- The negation of every other state's atom is in every stage after its day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma neg_stateAtom_mem_bliDP (DP : DeductiveProcess) (states : ℕ → Finset ℕ) (actual : ℕ → ℕ)
    {m s q : ℕ} (hm : m < s) (hq : q ∈ states m) (hne : q ≠ actual m) :
    (∼stateAtom m q) ∈ (bliDP DP states actual).D s := by
  rw [bliDP_D, Finset.mem_union, Finset.mem_image]
  refine Or.inr ⟨(stateFamily, Nat.pair m q, decide (q = actual m)), ?_, ?_⟩
  · rw [mem_stateEntries]
    exact ⟨m, hm, Or.inr ⟨q, hq, rfl⟩⟩
  · rw [decide_eq_false hne]
    rfl

/-- **Exclusivity.** In every world consistent with stage `s` of `bliDP`, for every day `m < s`
and every `q ∈ states m`, the state atom `⌜𝑸_m = q⌝` holds iff `q` is the actual state.
Source: bli-paper-038; bli-soto-a-003; mandate T5.3
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem bliDP_exclusive (DP : DeductiveProcess) (states : ℕ → Finset ℕ) (actual : ℕ → ℕ)
    {v : PCWorld} {s : ℕ} (hv : v.ConsistentWith ((bliDP DP states actual).D s)) :
    ∀ m < s, ∀ q ∈ states m, (v.Holds (stateAtom m q) ↔ q = actual m) := by
  intro m hm q hq
  constructor
  · intro h
    by_contra hne
    have := hv _ (neg_stateAtom_mem_bliDP DP states actual hm hq hne)
    exact (PCWorld.holds_neg v _).mp this h
  · rintro rfl
    exact hv _ (stateAtom_actual_mem_bliDP DP states actual hm)

/-- The actual state's atom holds in every world consistent with a stage after its day — the
positive literal `stateEntries` asserts unconditionally (deviation 2: even when
`actual m ∉ states m`, where `bliDP_exclusive` is silent), made visible in the API.
Source: bli-paper-038; audit r1 (fidelity §3.10)
Kind: L
Fidelity: exact -/
lemma stateAtom_actual_holds (DP : DeductiveProcess) (states : ℕ → Finset ℕ) (actual : ℕ → ℕ)
    {v : PCWorld} {s : ℕ} (hv : v.ConsistentWith ((bliDP DP states actual).D s)) {m : ℕ}
    (hm : m < s) : v.Holds (stateAtom m (actual m)) :=
  hv _ (stateAtom_actual_mem_bliDP DP states actual hm)

/-- The base is free of the state schedule as soon as it is tag-free for the state tag.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma processFreeOf_stateSchedule {DP : DeductiveProcess} (hDP : TagFreeProcess stateTag DP)
    (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) : ProcessFreeOf (stateSchedule states actual) DP :=
  ProcessFreeOf.of_tagFree fun f hf => by
    rw [stateSchedule_families states actual f hf]
    exact hDP

/-- **`bliDP_hworld`.** If every stage of a base process tag-free for the state tag has a
consistent world, so does every stage of `bliDP`. (The instance at `paperDP 𝗜𝚺₁` is
`PaperInstances.bliDP_paperDP_hworld`.)
Source: mandate T5.3 (guard against program §7.4)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem bliDP_hworld {DP : DeductiveProcess} (hDP : TagFreeProcess stateTag DP)
    (states : ℕ → Finset ℕ) (actual : ℕ → ℕ)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((bliDP DP states actual).D n) :=
  extendBy_hworld (stateSchedule_functional states actual)
    (processFreeOf_stateSchedule hDP states actual) h

/-- **`bliDP_conservative`** (theory form): `bliDP` decides nothing new about state-free
sentences.
Source: anson-012; mandate T5.3
Kind: C
Fidelity: variant: semantic "decided" (see `Extend.extendBy_decidesTheory_iff`)
Hyps: (a) -/
theorem bliDP_conservative {DP : DeductiveProcess} (hDP : TagFreeProcess stateTag DP)
    (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) {φ : Sentence} (hφ : TagFreeSentence stateTag φ) :
    (∀ v : PCWorld, v.ConsistentWithTheory (bliDP DP states actual) → v.Holds φ) ↔
      (∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds φ) :=
  extendBy_decidesTheory_iff (stateSchedule_functional states actual)
    (processFreeOf_stateSchedule hDP states actual)
    (FreeOf.of_tagFree fun f hf => by rw [stateSchedule_families states actual f hf]; exact hφ)

/-- `bliDP_conservative`, stage form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bliDP_conservative_stage {DP : DeductiveProcess} (hDP : TagFreeProcess stateTag DP)
    (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) {φ : Sentence} (hφ : TagFreeSentence stateTag φ)
    (n : ℕ) :
    (∀ v : PCWorld, v.ConsistentWith ((bliDP DP states actual).D n) → v.Holds φ) ↔
      (∀ v : PCWorld, v.ConsistentWith (DP.D n) → v.Holds φ) :=
  extendBy_decides_iff (stateSchedule_functional states actual)
    (processFreeOf_stateSchedule hDP states actual)
    (FreeOf.of_tagFree fun f hf => by rw [stateSchedule_families states actual f hf]; exact hφ) n

/-- `bliDP` adds only state-tag atoms: it stays tag-free for every other tag the base is
tag-free for.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma bliDP_tagFree {DP : DeductiveProcess} {t : ℕ} (hDP : TagFreeProcess t DP)
    (ht : t ≠ stateTag) (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) :
    TagFreeProcess t (bliDP DP states actual) := by
  intro k φ hφ
  rw [bliDP_D, Finset.mem_union, Finset.mem_image] at hφ
  rcases hφ with hφ | ⟨x, hx, rfl⟩
  · exact hDP k φ hφ
  · rw [mem_stateEntries] at hx
    obtain ⟨m, -, h | ⟨q, -, h⟩⟩ := hx
    · subst h
      exact stateAtom_tagFree_of_ne ht
    · subst h
      cases decide (q = actual m)
      · exact (stateAtom_tagFree_of_ne ht).neg
      · exact stateAtom_tagFree_of_ne ht

/-! ### Computability of `bliDP` -/

/-- A list enumeration of `stateEntries`, from a list enumeration of the state sets.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def stateEntriesList (enum : ℕ → List ℕ) (actual : ℕ → ℕ) (s : ℕ) : List (ℕ × ℕ × Bool) :=
  (List.range s).flatMap fun m =>
    (stateFamily, Nat.pair m (actual m), true) ::
      (enum m).map fun q => (stateFamily, Nat.pair m q, decide (q = actual m))

/-- `stateEntriesList_toFinset`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateEntriesList_toFinset (enum : ℕ → List ℕ) (states : ℕ → Finset ℕ)
    (henum : ∀ m, (enum m).toFinset = states m) (actual : ℕ → ℕ) (s : ℕ) :
    (stateEntriesList enum actual s).toFinset = stateEntries states actual s := by
  ext x
  rw [List.mem_toFinset, mem_stateEntries]
  simp only [stateEntriesList, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_map,
    ← henum, List.mem_toFinset]
  constructor
  · rintro ⟨m, hm, h | ⟨q, hq, h⟩⟩
    · exact ⟨m, hm, Or.inl h⟩
    · exact ⟨m, hm, Or.inr ⟨q, hq, h.symm⟩⟩
  · rintro ⟨m, hm, h | ⟨q, hq, h⟩⟩
    · exact ⟨m, hm, Or.inl h⟩
    · exact ⟨m, hm, Or.inr ⟨q, hq, h.symm⟩⟩

/-- `stateEntriesList_prim`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateEntriesList_prim {enum : ℕ → List ℕ} (henum : Primrec enum) {actual : ℕ → ℕ}
    (hact : Primrec actual) : Primrec (stateEntriesList enum actual) := by
  have hm : Primrec fun p : ℕ × ℕ => p.2 := Primrec.snd
  have hactm : Primrec fun p : ℕ × ℕ => actual p.2 := hact.comp hm
  have hhead : Primrec fun p : ℕ × ℕ => (stateFamily, Nat.pair p.2 (actual p.2), true) :=
    (Primrec.const stateFamily).pair ((Primrec₂.natPair.comp hm hactm).pair (Primrec.const true))
  have hq : Primrec fun r : (ℕ × ℕ) × ℕ => r.2 := Primrec.snd
  have hpm : Primrec fun r : (ℕ × ℕ) × ℕ => r.1.2 := Primrec.snd.comp Primrec.fst
  have hpa : Primrec fun r : (ℕ × ℕ) × ℕ => actual r.1.2 := hact.comp hpm
  have hdec : Primrec fun r : (ℕ × ℕ) × ℕ => decide (r.2 = actual r.1.2) := by
    obtain ⟨_, h⟩ := Primrec.eq.comp hq hpa
    exact h.of_eq fun r => by simp
  have hg : Primrec₂ fun (p : ℕ × ℕ) (q : ℕ) =>
      (stateFamily, Nat.pair p.2 q, decide (q = actual p.2)) :=
    ((Primrec.const stateFamily).pair ((Primrec₂.natPair.comp hpm hq).pair hdec)).to₂
  have htail : Primrec fun p : ℕ × ℕ =>
      (enum p.2).map fun q => (stateFamily, Nat.pair p.2 q, decide (q = actual p.2)) :=
    Primrec.list_map (henum.comp hm) hg
  have hinner : Primrec₂ fun (s m : ℕ) => (stateFamily, Nat.pair m (actual m), true) ::
      (enum m).map fun q => (stateFamily, Nat.pair m q, decide (q = actual m)) :=
    (Primrec.list_cons.comp hhead htail).to₂
  exact Primrec.list_flatMap Primrec.list_range hinner

/-- **`bliDP_computable`.** `bliDP` is computable when the base is, the state sets are
primitively recursively enumerated, and the actual state is primitive recursive.
Source: mandate T5.2
Kind: C
Fidelity: exact
Hyps: (a) the enumeration and `actual` certificates are the dependents' data -/
theorem bliDP_computable {DP : DeductiveProcess} (hDP : ComputableDeductiveProcess DP)
    (states : ℕ → Finset ℕ) (enum : ℕ → List ℕ) (henum : ∀ m, (enum m).toFinset = states m)
    (hprim : Primrec enum) {actual : ℕ → ℕ} (hact : Primrec actual) :
    ComputableDeductiveProcess (bliDP DP states actual) :=
  extendBy_computable hDP (stateSchedule states actual) (stateEntriesList enum actual)
    (stateEntriesList_toFinset enum states henum actual) (stateEntriesList_prim hprim hact)

/-! ## The policy-linkage process -/

/-- The linkage sentence `stateAtom m q ⋏ policyPoint m q a 🡒 actionAt m a`.
Source: [[bli-program]] §2.3; mandate D4
Kind: D
Fidelity: exact -/
def policyLink (m q a : ℕ) : Sentence := (stateAtom m q ⋏ policyPoint m q a) 🡒 actionAt m a

/-- **The policy-linkage process**: at stage `s`, for every `m < s`, `q ∈ states m`,
`a ∈ actions m`, the linkage sentence. Definition and transports only; its use is
`udt-bli-core`'s.
Source: [[bli-program]] §2.3; mandate D4
Kind: D
Fidelity: exact -/
def policyLinkProcess (states actions : ℕ → Finset ℕ) : DeductiveProcess where
  D s := (Finset.range s).biUnion fun m =>
    (states m).biUnion fun q => (actions m).image fun a => policyLink m q a
  mono s := Finset.biUnion_subset_biUnion_of_subset_left _
    (fun _ hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.le_succ s)))

/-- `mem_policyLinkProcess`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_policyLinkProcess {states actions : ℕ → Finset ℕ} {s : ℕ} {φ : Sentence} :
    φ ∈ (policyLinkProcess states actions).D s ↔
      ∃ m < s, ∃ q ∈ states m, ∃ a ∈ actions m, φ = policyLink m q a := by
  simp only [policyLinkProcess, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨m, hm, q, hq, a, ha, rfl⟩; exact ⟨m, hm, q, hq, a, ha, rfl⟩
  · rintro ⟨m, hm, q, hq, a, ha, rfl⟩; exact ⟨m, hm, q, hq, a, ha, rfl⟩

open Classical in
/-- The world that falsifies every policy point and agrees with `v` elsewhere.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def policyOverride (v : PCWorld) : PCWorld :=
  fun b => if b.unpair.1 = policyTag then False else v b

/-- `policyOverride_holds_iff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyOverride_holds_iff (v : PCWorld) {φ : Sentence} (hφ : TagFreeSentence policyTag φ) :
    (policyOverride v).Holds φ ↔ v.Holds φ :=
  PCWorld.holds_congr_atomCodes φ fun b hb => by
    simp [policyOverride, hφ b hb]

/-- `policyOverride_holds_policyLink`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyOverride_holds_policyLink (v : PCWorld) (m q a : ℕ) :
    (policyOverride v).Holds (policyLink m q a) := by
  intro h
  have := (PCWorld.holds_and _ _ _).mp h
  exfalso
  have hpp : (policyOverride v).Holds (policyPoint m q a) := this.2
  unfold policyPoint freshAtom at hpp
  rw [PCWorld.holds_atom] at hpp
  simp [policyOverride] at hpp

/-- **`hworld` transport for the policy linkage**: every world consistent with stage `n` of a
base process tag-free for the policy tag extends (falsifying every policy point) to a world
consistent with stage `n` of the base with the linkage adjoined.
Source: mandate D4
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem union_policyLink_consistentWith {DP : DeductiveProcess} (hDP : TagFreeProcess policyTag DP)
    (states actions : ℕ → Finset ℕ) {v : PCWorld} {n : ℕ} (hv : v.ConsistentWith (DP.D n)) :
    (policyOverride v).ConsistentWith ((DP.union (policyLinkProcess states actions)).D n) := by
  rw [PCWorld.consistentWith_union_iff]
  constructor
  · intro φ hφ
    exact (policyOverride_holds_iff v (hDP n φ hφ)).mpr (hv φ hφ)
  · intro φ hφ
    rw [mem_policyLinkProcess] at hφ
    obtain ⟨m, -, q, -, a, -, rfl⟩ := hφ
    exact policyOverride_holds_policyLink v m q a

/-- `union_policyLink_hworld`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem union_policyLink_hworld {DP : DeductiveProcess} (hDP : TagFreeProcess policyTag DP)
    (states actions : ℕ → Finset ℕ) (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (policyLinkProcess states actions)).D n) := by
  intro n
  obtain ⟨v, hv⟩ := h n
  exact ⟨policyOverride v, union_policyLink_consistentWith hDP states actions hv⟩

/-- A list enumeration of the linkage stages.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def policyLinkList (enumS enumA : ℕ → List ℕ) (s : ℕ) : List Sentence :=
  (List.range s).flatMap fun m =>
    (enumS m).flatMap fun q => (enumA m).map fun a => policyLink m q a

/-- `policyLinkList_toFinset`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyLinkList_toFinset {states actions : ℕ → Finset ℕ} {enumS enumA : ℕ → List ℕ}
    (hS : ∀ m, (enumS m).toFinset = states m) (hA : ∀ m, (enumA m).toFinset = actions m) (s : ℕ) :
    (policyLinkProcess states actions).D s = (policyLinkList enumS enumA s).toFinset := by
  ext φ
  rw [mem_policyLinkProcess]
  simp only [policyLinkList, List.mem_toFinset, List.mem_flatMap, List.mem_range, List.mem_map,
    ← hS, ← hA]
  constructor
  · rintro ⟨m, hm, q, hq, a, ha, rfl⟩
    exact ⟨m, hm, q, hq, a, ha, rfl⟩
  · rintro ⟨m, hm, q, hq, a, ha, rfl⟩
    exact ⟨m, hm, q, hq, a, ha, rfl⟩

/-- `sentenceAnd_prim`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sentenceAnd_prim : Primrec₂ fun φ ψ : Sentence => φ ⋏ ψ := by
  apply Primrec₂.encode_iff.mp
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 3)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd)))).to₂.of_eq fun _ _ => rfl

/-- `policyLink_prim`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyLink_prim : Primrec fun x : ℕ × ℕ × ℕ => policyLink x.1 x.2.1 x.2.2 := by
  have hm : Primrec fun x : ℕ × ℕ × ℕ => x.1 := Primrec.fst
  have hq : Primrec fun x : ℕ × ℕ × ℕ => x.2.1 := Primrec.fst.comp Primrec.snd
  have ha : Primrec fun x : ℕ × ℕ × ℕ => x.2.2 := Primrec.snd.comp Primrec.snd
  have hstate : Primrec fun x : ℕ × ℕ × ℕ => stateAtom x.1 x.2.1 :=
    sentenceAtom_prim.comp (Primrec₂.natPair.comp (Primrec.const stateTag)
      (Primrec₂.natPair.comp hm hq))
  have hpol : Primrec fun x : ℕ × ℕ × ℕ => policyPoint x.1 x.2.1 x.2.2 :=
    sentenceAtom_prim.comp (Primrec₂.natPair.comp (Primrec.const policyTag)
      (Primrec₂.natPair.comp hm (Primrec₂.natPair.comp hq ha)))
  have hact : Primrec fun x : ℕ × ℕ × ℕ => actionAt x.1 x.2.2 :=
    sentenceAtom_prim.comp (Primrec₂.natPair.comp (Primrec.const actionTag)
      (Primrec₂.natPair.comp hm ha))
  exact sentenceImp_prim.comp (sentenceAnd_prim.comp hstate hpol) hact

/-- `policyLinkList_prim`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyLinkList_prim {enumS enumA : ℕ → List ℕ} (hS : Primrec enumS) (hA : Primrec enumA) :
    Primrec (policyLinkList enumS enumA) := by
  have hm : Primrec fun p : ℕ × ℕ => p.2 := Primrec.snd
  have hm' : Primrec fun r : (ℕ × ℕ) × ℕ => r.1.2 := Primrec.snd.comp Primrec.fst
  have hq : Primrec fun r : (ℕ × ℕ) × ℕ => r.2 := Primrec.snd
  have hm'' : Primrec fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hq' : Primrec fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.1.2 := Primrec.snd.comp Primrec.fst
  have ha : Primrec fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.2 := Primrec.snd
  have h3 : Primrec₂ fun (r : (ℕ × ℕ) × ℕ) (a : ℕ) => policyLink r.1.2 r.2 a :=
    (policyLink_prim.comp (hm''.pair (hq'.pair ha))).to₂
  have h2 : Primrec₂ fun (p : ℕ × ℕ) (q : ℕ) => (enumA p.2).map fun a => policyLink p.2 q a :=
    (Primrec.list_map (hA.comp hm') h3).to₂
  have h1 : Primrec₂ fun (s m : ℕ) =>
      (enumS m).flatMap fun q => (enumA m).map fun a => policyLink m q a :=
    (Primrec.list_flatMap (hS.comp hm) h2).to₂
  exact Primrec.list_flatMap Primrec.list_range h1

/-- **Computability transport for the policy linkage.**
Source: mandate D4
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem policyLinkProcess_computable {states actions : ℕ → Finset ℕ} {enumS enumA : ℕ → List ℕ}
    (hS : ∀ m, (enumS m).toFinset = states m) (hA : ∀ m, (enumA m).toFinset = actions m)
    (hSp : Primrec enumS) (hAp : Primrec enumA) :
    ComputableDeductiveProcess (policyLinkProcess states actions) :=
  ComputableDeductiveProcess.ofEncodePrim
    (encode_stage_prim_of_list (policyLinkList_prim hSp hAp) (policyLinkList_toFinset hS hA))

/-- `union_policyLink_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem union_policyLink_computable {DP : DeductiveProcess} (hDP : ComputableDeductiveProcess DP)
    {states actions : ℕ → Finset ℕ} {enumS enumA : ℕ → List ℕ}
    (hS : ∀ m, (enumS m).toFinset = states m) (hA : ∀ m, (enumA m).toFinset = actions m)
    (hSp : Primrec enumS) (hAp : Primrec enumA) :
    ComputableDeductiveProcess (DP.union (policyLinkProcess states actions)) :=
  DeductiveProcessComputation.union_toComputable hDP.nonemptyComputation.some
    (policyLinkProcess_computable hS hA hSp hAp).nonemptyComputation.some

end Cleanroom.Bli.BliFound
