# Composition with the Logical Induction deference theorems

**Status:** `ci-only`.  The question is whether "ordinary LI Value on the activated
family" is available as stated, or whether a new conditional trust theorem is needed.
The answer is: **no new trust theorem; one new transfer lemma; one scope condition
identified with a process receipt.**

## 1. The inherited Value theorem, exactly

Two statements are on `main`, both in
`lean/Workspace/Deference/Contrib/InheritedAlgebra.lean` and both ported from the
June corpus:

**`value_iff_totalTrust`** (finite-exact, two-option witness menus `{X, const s}`):
the universal closure of the pointwise identity
`𝔼_π[Ŝ_wit] − s·𝔼_π[1] = Σ_w 1[s ≤ E*(X)(w)] π_w (X_w − s)`.  Linearity only.

**`value_asymptotic`** (tower ⟹ Value, asymptotic), hypotheses over real sequences:

| hypothesis | LI fact it stands for | reads the menu? |
|---|---|---|
| `hAdd1 : ES ≈ₙ Σ_j a j` | linearity of `𝔼ⁿ` over the soft followed strategy (`thm:loe`) | only as bounded sequences |
| `hCcee : a j ≈ₙ b j` | conditional tower `ccee(H→A)` on each option with the soft weight | as bounded LUVs |
| `hAdd2 : Σ_j b j ≈ₙ c` | linearity again | no |
| `hCee : Ee j ≈ₙ Eo j` | tower `cee(H→A)` on each option | as bounded LUVs |
| `hδ : δ → 0` | the softmax gap vanishes | no |
| `hSoft : Ee i n ≤ c n + δ n` eventually | the expert's soft self-endorsement: its estimate of the option it weights is within `δ` of the max | **yes** — this is the step the punishing menu kills |

Conclusion: `Eo i ≲ₙ ES` for each fixed `i` — the novice expects the followed strategy
to do at least as well as any fixed option.

The corpus reconciliation records (`RECONCILIATION.md` §1.2) that the *hard-selector*
route is refuted at full menu-quantifier strength: on a selection-referencing menu
the expert cannot endorse its own argmax, and Value is false, so a scope condition on
the menu is necessary.  The admissible domain is "not the quote-referencing diagonal"
— a provenance condition, not a syntactic fragment.

## 2. What composes unchanged

Instantiate the menu with `O_a := U_{n,a} = C_n · V_n(a)`.

- **Boundedness.**  `U_{n,a}` is a `[0,1]`-LUV: its thresholds are
  `C_n ∧ (V_n(a) > r)` (`AUTHORITY_ACTIVATED_VALUE.md` §5).  Every hypothesis of
  `value_asymptotic` is a relation between bounded real sequences; nothing in it
  inspects the menu's internal structure.
- **Efficient codeability.**  The threshold sentences of `U_{n,a}` are built from the
  fixed data `(o_n, a, r, verifier)` — an `RpnThresholdCodeSeq` in the dependency's
  sense when the family of occurrences is itself efficiently enumerated.  The
  activation conjunct adds one fixed sentence per `n`.
- **The tower hypotheses** (`hCee`, `hCcee`) are about the novice's deference to the
  advisor on these LUVs.  They are the epistemic-deference input and are neither
  easier nor harder for activated securities than for any other bounded LUV.
  **PAPER**, conditional.
- **Self-endorsement** (`hSoft`) is the advisor's coherence on its own quotes for the
  menu — available exactly when the menu is not selection-referencing (§3).

So: **ordinary Value runs on `{U_{n,a}}` without modification.**  The activated
securities are just bounded LUVs; the theorem does not know they are activated.

## 3. The scope condition is the no-preview receipt

The one place the construction touches Value's hypothesis package is `hSoft`.  The
punishing menu of the corpus is `O_j = 1[j ≠ j*(n)]`: the payoff of an option depends
on which option the advisor selects.  In the present setting the analogue is a
principal who reads the advisor's selection or quotes for `o_n` before committing
`V_n` and sets `V_n(â) = 0` (fixture **I**).  Then `U_{n,·}` references `𝔸ⁿ`'s
selection through `V_n`, no hard selection is consistent
(`TestI_SelfReference.test_preview_has_no_consistent_hard_selection`, **FIX**), and
Value fails for the same reason it fails on the corpus's menu.

The no-preview clause of `ProcessCert` (`AUTHORITY_ACTIVATED_VALUE.md` §4) is a
receipt that the commitment `ρ.key` to `V_n` was timestamped before the reveal of the
advisor's selection and quotes for `o_n`.  Under it `V_n` is fixed as a function of the
world independently of `j*(n)`, the menu is on the admissible domain, and `hSoft` is
available as for any exogenous menu.

**This is the identification the round adds:** the corpus's admissible-domain
condition, which it could state only as "a causal/provenance condition", is, for
evaluation occurrences, a *process receipt in the account*.  It is narrow — it seals
one object (the self-referential prediction for this occurrence) from one session
before one commitment — and it does not isolate `P⁺` from `A` otherwise.  Whether the
receipt is authentic is **EXT**.

## 4. What is new: the transfer lemma

Value on `{U_{n,a}}` bounds *activated* regret.  What the application wants is regret
against `V_n` — the actual future principal's evaluation, not the contract.  Nothing
in the inherited algebra relates the two: the void branch is where they differ, and
Value knows nothing about it.

`ActivatedValue.availability_transfer_strategy` (**LEAN**) is the missing lemma:

```
activated regret ≤ ε   ∧   𝔼ⁿ[1 − C_n] ≤ η   ⟹   unactivated regret ≤ ε + η
```

for any followed strategy (hard selector or soft mixture), with the constant `1`
sharp (`Sharp.transfer_sharp`).  `availability_transfer_asymptotic` is the same over
`≲ₙ`, with the pointwise facts `0 ≤ V − U ≤ 1 − C` as named hypotheses — in the LI
reading they are provability induction over provable inequalities plus linearity,
the same two inputs `value_asymptotic` already takes.

It is not a trust theorem.  It has no tower, no expert, no self-endorsement.  It is
the algebra of a common cancellation event.

## 5. Do we need a "Legitimate Total Trust" theorem?

No.  The check against the actual statements:

- `value_asymptotic`'s hypotheses are menu-agnostic relations between bounded
  sequences; instantiating with activated LUVs changes nothing in the proof.
- `value_iff_totalTrust`'s witness menu `{X, const s}` needs one adjustment that is
  a discipline, not a theorem: **the constant option must be activated too**, `C_n · s`,
  or the void branch favours the constant and reopens the certifiability channel
  (`TestWitnessMenuActivation`, **FIX**).  With the activated constant the identity is
  the conditional Total Trust `𝔼[V | C ∧ E*(U) ≥ s] ≥ s` by `argmax_iff`'s mass
  factorization.  This is the same linearity, applied to `C_n(X − s)`.
- The novelty is entirely in the semantics of `C_n` (the Normativity-side module) and
  the one transfer lemma.  There is no selected-trust or conditional-trust ingredient
  because activation is common to the menu; the moment it is per-candidate (fixture
  **D**) a genuinely conditional statement would be needed, and that is the reason
  common activation is a design constraint rather than a convenience.

## 6. Availability in the criterion's terms

`C_n` is a sentence settled by feedback at `m(n)`.  For `η_n = 𝔼ⁿ[1 − C_n] → 0`:

- If every `C_n` is true and reported by the deductive process, `lic_provind_true`
  (`AffineCoherence.lean:888`, **PAPER**; its `hthm` allows arbitrary settlement delay)
  gives `𝔼ⁿ[C_n] → 1` pointwise.  The verifier's output is a decidable computation,
  so its truth is reportable.
- If a fraction fails, the dependency supplies weighted-average unbiasedness
  (`lic_wub_ofComputation_unconditional`, **PAPER**) and the transfer theorem is read
  with `η_n` the novice's price, which is what it uses.

Neither is a claim that any ecosystem certifies; both say what the market does with
a certification stream it is given.

## 7. Composition with the selected-trust register (PR #90), briefly

`SelectedTrustNonPreemption.lean` takes the protected principal's value `W x m` as
data on cells.  The certified `V_n` can serve as `W` on the certified branch: `W x a
:= V_n(a)` on cells `x` where `C_n = 1`, and the activated security's price is a
candidate for the agent's operative value `EX x a` in the `(DV)` bridge
(`PRIORITIES.md` item 84), which asks for operative values that are prices of
*sealed-target* securities — and an activated security under the no-preview receipt
is sealed by construction.  That supplies the *object* item 84 asks for, not the
bridge: `(ST)` still relates the agent's operative values to `W` on the disagreement
region, and nothing here bounds `selectedGap`.  No incentive-corrigibility claim is
made; PR #90's Level II bound composes as stated with `r_P` the principal regret this
round bounds by `ε + η` when the principal's own selection is the followed strategy.
This is secondary and is not developed further.

## 8. What is not established

- The tower `Mart_{H→A}` on activated LUVs (**PAPER**, conditional).
- That the activated menu family is efficiently codeable in a concrete arithmetic
  instantiation; the shape is standard but no `RpnThresholdCodeSeq` witness is built
  here (**OPEN**, formalization work only).
- Any rate for `η_n → 0`; any pointwise statement in the mostly-certified regime.
- That the no-preview receipt is enforced by any mechanism (**EXT**).
