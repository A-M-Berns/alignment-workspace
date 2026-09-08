# Legitimate deference — the characterization theorem, conditional form

**Status:** `ci-only`; verification register for
`prompts/2026-09-08-legitimate-deference-consolidation/`.  Labels: **LEAN** kernel-checked
in this stack; **FIX** exact fixture; **PAPER** inherited (pinned Logical Induction
dependency, inherited deference algebra); **EXT** declared causal, semantic,
authentication or protocol meaning; **OPEN** not established.  Names are provisional.

## 1. Objects

| symbol | type | what it is | source |
|---|---|---|---|
| `o_n` | `Occ` | the anchored evaluation occurrence admitted at time `n`; anchor `EvalReq(ρ_P, α_n, Q_n, s_n, τ)` | `OccurrenceIntegrity` (PR #92) |
| `Q_n` | finite nonempty | the fixed candidate menu, by identity, at issuance | — |
| `W`, `π` | finite worlds, credence `π ≥ 0`, `Σπ = 1` | the novice's day-`n` view; in the LI reading, prices | — |
| `C_n : W → Bool` | the **common activation event** | §3 | `Program.activated` + derived predicates |
| `Ṽ_n : (w) → C_n w = true → Q_n → [0,1]` | the **partial** actual-future-principal evaluation, defined on certified worlds only | `PartialActivatedValue.Completion` |
| `U_{n,a} = C_n · V̄_a` | the activated securities, for any completion `V̄` of `Ṽ_n` | completion-invariant (`activated_completion_congr`, LEAN) |
| `α_n : W → Q_n → ℚ` | the advisor-following strategy: a world-dependent probability vector (hard selector or soft mixture) | `followed` |
| `R_U(α)` | `max_a 𝔼[U_a] − 𝔼[U^α]` | activated regret; **max outside 𝔼**: the best *fixed* candidate at issuance, not an ex-post oracle | `regretU` |
| `R_auth(α)` | `max_a 𝔼[Ṽ_a \| C] − 𝔼[Ṽ^α \| C]` | **conditional authoritative regret**, from `Ṽ_n` alone | `regretAuth` |
| `p_n = 𝔼[C_n]`, `η_n ≥ 𝔼[1 − C_n]` | activation mass, void-mass bound | `mass`, `voidMass` |

There is no counterfactual no-AI evaluator and no ideal-value oracle anywhere in the
table.  On worlds where `C_n = 0` there is no value vector, and none is invented.

## 2. The theorem

**Theorem (legitimate deference, conditional form).**  Suppose:

- **(A1) Sound activation.**  `C_n(w) = 1` only if, on `w`: the occurrence's propagated
  account is exactly one authenticated answer receipt (`activated`, LEAN); the event
  payload is authentic and `Bind`s exactly the vector `Ṽ_n(w)` (EXT); the binding
  endpoint is principal-exclusive — the receipt's warrant is the principal role's
  binding warrant and `Authorized` holds for it only on principal-produced events
  (existing field, meaning EXT); the occurrence has an occurrence-local Integrity trace
  with the evaluation's concern scope robustly open at every snapshot (`LocalLegit`,
  LEAN projection; openness semantics EXT); the issuance-rooted reason-mediated
  authorship holds — `ExclusiveBind ∧ ReasonMediated` over the audited continuation
  class, with the reason trace blind to the declared prohibited channels
  (`Authored`, `Blind R P`: predicates LEAN, receipts' meaning EXT); and the protected
  reason-coverage barrier holds — no live protected concern at commitment, with
  representation faithful into the trace (`NoBindLive`, `RepFaithful`, LEAN;
  declarations EXT).
- **(A2) Value-domain condition.**  The reason trace is blind to the selection-induced
  pair class `P_sel` of the advisor's whole continuation, so the activated menu is
  selection-blind (`selectionBlind_of_blind`, LEAN); this is the inherited Value
  theorem's scope condition (PAPER) and is *not* part of `C_n`.
- **(A3) Ordinary LI Value** on `{U_{n,a}}`: the inherited hypothesis package
  (`InheritedAlgebra.value_asymptotic`: tower and conditional tower on the activated
  LUVs, linearity, the advisor's soft self-endorsement) yields `R_U(α_n) ≤ ε_n` (PAPER,
  conditional; nothing here discharges the tower).
- **(A4) Availability.**  `𝔼_n[1 − C_n] ≤ η_n < 1` (OPEN as a realization; the theorem
  takes it as a hypothesis).

Then, with `0 ≤ ε_n`:

```
p_n ≥ 1 − η_n > 0     and     R_auth,n(α_n) = R_U(α_n) / p_n ≤ ε_n / (1 − η_n)
```

(`regretU_eq_mass_mul_regretAuth`, `regretAuth_le_div`, **LEAN**), and for every bounded
completion `V̄` of `Ṽ_n` with payoff diameter `D`,

```
|R_V̄(α_n) − R_U(α_n)| ≤ D · η_n
```

(`regretV_sub_regretU_abs_le`, **LEAN**; both constants sharp: `Sharp.transfer_sharp`,
`SharpLower.attained`).

**Corollary (asymptotic).**  `R_U ≲ₙ 0` and `η_n → 0` give `R_auth,n ≲ₙ 0`
(`regretAuth_asymptotic`, **LEAN**).  With Value's conclusion `R_U(α_n) ≲ₙ 0` (PAPER) and
availability `η_n → 0` (OPEN), the advisor-following strategy has asymptotically
nonpositive regret against every fixed candidate **by the actual authoritative future
principal's evaluation, conditional on the worlds where such an evaluation exists**.

**Corollary (reason suppression is void mass).**  Under (A1)'s coverage clause, the
credence of the event "some protected active concern is missing from the trace" is at
most `η_n` (`covFail_mass_le`, **LEAN**).  This bounds failures relative to the declared
scope; it does not say the scope was normatively complete.

## 3. The activation event, exactly

`C_n = 1` iff all of:

| # | clause | kind | where |
|---|---|---|---|
| 1 | exactly one authenticated answer receipt in the propagated account | LEAN structure | `Program.activated` |
| 2 | the event payload is authentic and binds the exact vector | EXT (event semantics) | `ACTIVATION_COMPOSITION.md` §2 of the authorship round |
| 3 | the binding endpoint is principal-exclusive | existing receipt field (`warrant`, `Authorized`); meaning EXT | same |
| 4 | occurrence-local Integrity trace | LEAN (`LocalTrace`, projected from `Evolution`) | `OccurrenceLocalIntegrity.lean` |
| 5 | the evaluation's concern scope robustly open at every snapshot | LEAN structure (`OpenAtFor` per snapshot); semantics EXT | same, `LocalLegit` |
| 6 | issuance-rooted reason-mediated authorship, trace blind to prohibited channels | LEAN predicates; receipts EXT | `ReasonMediatedAuthorship.lean` |
| 7 | protected reason-coverage barrier with faithful representation | LEAN predicates; declarations EXT | `ReasonCoverage.lean` |

Clauses 1, 4, 5 are the account/legitimacy layer.  Clauses 2, 3 are the authenticated
event layer.  Clauses 6, 7 are the authorship / reason-supply layer.  None of them is a
new conjunct of generic Legitimate Evolution, and `Protocol.AnswerOK` is unchanged.

**Selection blindness (A2) is not in `C_n`.**  It is a condition on the advisor's
continuation policy that the *Value theorem* needs; an evaluation can be fully
authoritative and still lie off Value's domain (the principal may legitimately
deliberate about the advisor's prediction).  Keeping semantic authority and theorem
admissibility apart is what lets `C_n` be a fact about the world and (A2) a fact about
the advisor.

## 4. What each conclusion means

- `R_auth ≤ ε/(1 − η)`: *by the actual AI-informed future principal, where that
  principal's evaluation has authority*, following the advisor is at most `ε/(1−η)` worse
  than the best fixed candidate of the issued menu.  This is the deference conclusion.
- `|R_V̄ − R_U| ≤ Dη`: *whatever story one tells about worlds with no evaluation*, the
  fixed-menu regret moves by at most `Dη`.  This is a robustness lemma about the
  arbitrariness of completions, not a claim about those worlds.
- Neither says the candidate is objectively good, that the declared scope `Γ_eval` was
  complete, that Robust Openness made the principal consider anything, or that
  authorship puts the menu on Value's domain.

## 5. Interpretation

The advisor can improve the principal by supplying reasons (fixtures A/E of the
authorship round: verdicts change radically under mediation).  It cannot win by
bypassing the reason interface (`blind_of_mediated`; fixtures B, C, F, G).  It cannot
obtain an authoritative evaluation while suppressing a protected live reason
(`void_of_omitted`; fixture F of this round).  Failure of authority is paid as
availability loss — `η_n` in the bound, `1 − p_n` in the mass — not by substituting a
counterfactual evaluator.

## 6. Hypothesis ledger

| hypothesis | class |
|---|---|
| `activated`, `LocalTrace`, `LocalLegit`, `ReasonMediated`, `Blind`, `Authored`, `NoBindLive`, `RepFaithful`, `Covered` as predicates; the identities and bounds of §2 | LEAN |
| fixtures A–L of `COUNTERMODELS.md` | FIX |
| Value on activated LUVs and its scope condition; `LUV`/`expectApprox`; provability induction for the all-certified availability case | PAPER, conditional |
| payload authenticity; `Authorized` for the binding warrant means principal-produced; the declared reason trace `R`, audited class `D`, prohibited class `P`, protected scope `Γ_eval`; the coverage semantics; that receipts mean what they say | EXT |
| `η_n → 0`; route exercise; the tower on activated LUVs for a concrete inductor; an `RpnThresholdCodeSeq` witness | OPEN |
