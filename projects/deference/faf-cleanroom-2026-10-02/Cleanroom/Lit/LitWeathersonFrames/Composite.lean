import Cleanroom.Lit.LitWeathersonFrames.Coin
import Cleanroom.Lit.LitWeathersonFrames.Bentham

/-!
# The composite (T11): what survives of "Theorem 2.2 fails on countably infinite frames"

Package `lit-weatherson-frames` (faf-cleanroom run, 2026-09-30). Weatherson's abstract (l. 29):
"The equivalence Dorst et al. establish between Total Trust and Value breaks down in both
directions on infinite frames: Total Trust can hold without Value (when utilities are unbounded),
and Value can hold without Total Trust (when the option set is finite but the state space is
countably infinite)." Under the product-form / positive-mass convention of record what survives is
**one direction, and only with both an infinite menu and non-uniformly-bounded options**:

* Coin: Total Trust holds and Value fails (`Coin.totalTrustInt`, `Coin.not_valueInt`) — but Coin
  is Valued on every finite menu of integrable options and on every uniformly bounded menu
  (`Coin.valueFinInt`, `Coin.valueBdd`), so each of Weatherson's two objections alone restores
  Value;
* Bentham: Valued *and* totally trusted (`Bentham.valueFinInt`, `Bentham.totalTrustC`); its
  Total Trust "failure" conditions on a null event (`Bentham.Y_event_null`);
* the Value ⟹ Total Trust direction holds on every countable frame (`value_imp_totalTrust`).

The OPEN of record is the other direction for finite menus of uniformly bounded options on an
arbitrary countable frame (`totalTrust_imp_valueFinBdd_open`, filed in
`lit-weatherson-frames-open.txt`): the paper does not settle it (its only Total-Trust-without-
Value frame uses an infinite menu of non-uniformly-bounded options), and DDB's finite proof
(Lemma 7.5 through the hull structure) does not obviously transfer.
-/

namespace Cleanroom.Lit.LitWeathersonFrames

noncomputable section

variable {W : Type}

/-- **Value, finite menus of uniformly bounded options**: the weakest of the Value predicates,
the one the OPEN of record asks Total Trust to imply.
Source: [[Deference and Infinite Frames]] abstract l. 29 ("when the option set is finite"), §3
l. 194
Kind: D
Fidelity: exact -/
def ValueFinBdd (π : W → ℝ) (F : CFrame W) : Prop :=
  ∀ (ι : Type) [Fintype ι] (o : ι → W → ℝ), BddFam o →
    ∀ S, RecommendedC F o S → ∀ i, Eℕ π (o i) ≤ stratValueC π o S

/-- `ValueFinInt` implies `ValueFinBdd` (bounded options are integrable).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ValueFinInt.valueFinBdd {π : W → ℝ} (hπ : IsDist π) {F : CFrame W} (h : ValueFinInt π F) :
    ValueFinBdd π F := fun ι _ o ho S hS i =>
  h ι o (fun i => (ho.bdd i).integrableW hπ) (fun i => (ho.bdd i).rowsIntegrable F) S hS i

/-- `ValueBdd` implies `ValueFinBdd`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ValueBdd.valueFinBdd {π : W → ℝ} {F : CFrame W} (h : ValueBdd π F) : ValueFinBdd π F :=
  fun ι _ o ho S hS i => h ι o ho S hS i

/-- **T11. The status of DDB's Theorem 2.2 on countably infinite frames** (positive-mass
convention). (i) On Coin, Total Trust holds and Value fails for an infinite menu of
non-uniformly-bounded integrable options; (ii) Coin is nonetheless Valued on every finite menu of
integrable options and on every uniformly bounded menu; (iii) Bentham is Valued and totally
trusted; (iv) Value ⟹ Total Trust on every countable frame. So: Total Trust ⇏ Value on countable
frames **only** with an infinite menu of non-uniformly-bounded options; Value ⟹ Total Trust never
fails. Named for what it proves, not "thm22_fails".
Source: [[Deference and Infinite Frames]] abstract l. 29, §3 l. 186; inventory 035
Kind: C
Fidelity: exact (positive-mass convention; the abstract's second direction is the null-event
artifact, finding F-T10)
Hyps: (a) only -/
theorem thm22_countable_status :
    (TotalTrustInt Coin.π Coin.frame ∧ ¬ ValueInt Coin.π Coin.frame) ∧
    (ValueFinInt Coin.π Coin.frame ∧ ValueBdd Coin.π Coin.frame) ∧
    (ValueFinInt Bentham.π Bentham.frame ∧ ValueBdd Bentham.π Bentham.frame ∧
      TotalTrustC Bentham.π Bentham.frame ∧ TotalTrustInt Bentham.π Bentham.frame) ∧
    (∀ (V : Type) (π : V → ℝ) (F : CFrame V), IsDist π → ValueBdd π F → TotalTrustC π F) :=
  ⟨⟨Coin.totalTrustInt, Coin.not_valueInt⟩, ⟨Coin.valueFinInt, Coin.valueBdd⟩,
    ⟨Bentham.valueFinInt, Bentham.valueBdd, Bentham.totalTrustC, Bentham.totalTrustInt_direct⟩,
    fun _ _ _ hπ hV => value_imp_totalTrust hπ hV⟩

/-- **OPEN (of record).** Total Trust ⟹ Value for finite menus of uniformly bounded options on
an arbitrary countable frame on `ℕ`. True on ray frames and on Bentham (through the finite
Geanakoplos theorem); not settled by the paper; DDB's finite proof (Lemma 7.5 via the hull
condition of `lit-ddb-frames`) uses the finiteness of the candidate set `C_π` and does not
obviously transfer — the obstruction is that on a countable frame the deferrer need not be a
finite convex combination of candidates. Listed in `lit-weatherson-frames-open.txt`.
Source: [[Deference and Infinite Frames]] §3 l. 186; [[Deference Done Better]] Thm 2.2; mandate
T11
Kind: OPEN
Fidelity: exact
Hyps: n/a (open) -/
theorem totalTrust_imp_valueFinBdd_open (π : ℕ → ℝ) (hπ : IsDist π) (F : CFrame ℕ)
    (h : TotalTrustC π F) : ValueFinBdd π F := by
  sorry

end

end Cleanroom.Lit.LitWeathersonFrames
