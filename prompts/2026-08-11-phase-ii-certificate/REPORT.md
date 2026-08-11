# Stage-II integration verification of Track L

**This is not Track L's report.** Track L's executor did not persist report-shaped
output; the round directory holds its harness, `verify_reinterpretation.py`, and
nothing else. No draft of its prose exists in the repository. Rather than write prose
and attribute it to the original agent, this document **reconstructs Track L's results
from its committed harness** — its module docstring, its check labels, its exact
outputs — and verifies them by re-running it. Where a statement below is a
reconstruction, it is derived from a named check in that script and can be re-derived
by running it. The interpretive framing is mine, not Track L's.

`8c71ef9`'s commit message is a second source and is used where it states something the
harness demonstrates but does not label; it is cited explicitly at those points.

| field | value |
|---|---|
| original track | Phase II Track L, `prompts/2026-08-11-phase-ii-certificate/PROMPT.md` |
| original executor | Claude Opus 5 (Anthropic); prompt author GPT-5.6 Sol (OpenAI) |
| original delivery | `8c71ef9`, harness only; no report persisted |
| this document's author | Claude Opus 5 (Anthropic), Stage-II closure pass, 2026-08-11 |
| review status | `ci-only` |

## 1. Reproduction

`python3 prompts/2026-08-11-phase-ii-certificate/verify_reinterpretation.py`, run twice
from a clean tree at `HEAD = 8c71ef9`.

| quantity | reported at dispatch | reproduced |
|---|---|---|
| exit code | 0 | **0** |
| checks | 71 | **71** |
| models enumerated | 1,574,640 | **1,574,640** |
| certified `(j,S)` instances | 4,024,080 | **4,024,080** |
| violations of positive claims | 0 | **0** |
| refutations, settlement-loaded branch | 1,443 | **1,443** |

Every figure reproduces exactly. The script is stdlib-only and every value on a verdict
path is a `fractions.Fraction` or a Python `int`; I confirmed no float appears.

## 2. The carriers

Skeleton v1 plus the execution layer proposed in Track K's REPORT §9.2 — now installed
as `FINITE_MODEL_SKELETON.md` v2 §4a. The harness instantiates it as

```
R_n = Π_n,  ι_n = id,  ρ_n = J_n,
κ_n : Π_n → subsets of Π_n ⊔ {⊥}   with r ∈ κ_n(r),
E_n(π, r) = π if π ∈ κ_n(r) else ⊥.
```

`κ_n(r) = ` the full menu is the **free instantiation** and reproduces v1 exactly;
`κ_n(r) = {r, ⊥}` is **strict protection**. `X_⊥ : Ω → ℚ` with `|X_⊥| ≤ B` is the
declared null quantity — skeleton v2 §1, the amendment this track's harness depends on
and which it cites as "Track K Sec 9.2's amendment to Sec 1".

## 3. What survives, what changes meaning, what is false

Reconstructed from the harness's §3 and §6 checks.

**Invariant.** `L1` (margin ⇒ agreement), `L2` (override bound) and `L7` (advantage
estimate) are untouched. Their inputs — `η`, `γ`, `ε`, `Γ`, `Γ̂` — are computed from
grades alone and are verified identical under the free and strict instantiations. `L2`'s
bound holds at every one of the 4,024,080 certified instances.

**Survives with its statement, loses its reading.** `L3` still holds as a bound on the
grade-register defect `D_{n,j}`, and does so at every enumerated instance. But `L3`'s
bound is **not** a bound on the protected valuation gap: the harness exhibits
`gap_prot = 1/50 > 4Bε/(2B+γ) = 1/100`. A reader who took `L3` as controlling what
happens under protection was reading a grade-register statement as a V-register one.

**Loses its consumer.** `L5`'s comparator `FIXED[b]` does not realize `b` under strict
protection — it realizes `⊥` — so the comparison `L5` licensed is not available in the
protected architecture at all.

**False.** The settlement-loaded branch of the preemption bound —
`4Bε/(2B+γ) + 2M_S` — is not a bound on the protected gap. 1,443 refuting instances,
with a first witness printed in full. The settlement-*free* branch `4Bε/γ` does bound
it, at every instance. Since the certificate's clause (iv) takes the `min` of the two
branches, the loaded branch was the one that could bind in the low-drift regime, and
under protection it does not.

**Two replacements, verified at every instance.** Reconstructed from the harness's
labels `Track L (a)` and `Track L (a')`:

```
(a)   gap_prot  ≤  4B ε / γ
(a')  gap_prot  ≤  Δ_⊥ · min(1, 2ε/γ)
```

`(a')` is attained exactly in the exhibited family, so its constant is sharp.

## 4. The three corrections to verified inputs

All three are corrections to *previously verified* material, and all three reproduce.

1. **Theorem C(b)'s "strict minority" gloss is false.** Phase I's certificate report
   glosses `P(S ∩ {J ≠ j}) ≤ 2ε/γ < ρ` as saying the agent overrides on a strict
   minority of certified credence. The harness exhibits a model where all four clauses
   of `Cert` hold and the override mass is `3/5` of `ρ` — a strict majority. What clause
   (iii) actually delivers is only that override mass `< ρ`, i.e. that the certified act
   executes on positive mass. A genuine majority claim needs `γρ > 4ε`, which the
   counterexample fails.
2. **The dispatch's premise that four lemmas are untouched is right about the
   arithmetic and wrong about the interpretation in three of them.** §3 above is the
   itemization; `L5` is the one that loses its consumer entirely.
3. **The settlement-loaded branch is false, not merely unproved.** §3.

## 5. The decisive result: certification cannot see the architecture

This is the sharpest thing in the track and it answers the dispatch's question 4.

The harness runs the same certified instance at tolerances `ε ≤ 1/10`, `1/1000`,
`1/1000000`. At each: the certificate fires, its bound holds, the free architecture
realizes an override at the worst per-state quantity gap the carriers permit (`2B`), and
strict protection realizes `⊥` at exactly that state. The two preemption costs are
**identical rationals** at every tolerance.

The general form, verified over the whole enumeration:

```
| gap_free − gap_prot |  ≤  2B · P(S ∩ {J ≠ j})  ≤  4B ε / γ
```

with maximum slack `0` over a declared grid — the bound is attained, not merely valid.
So the entire valuation difference between the protected and unprotected architectures
is bounded by the certificate's own bound. **Tightening the certificate shrinks the
distinction at the same rate and never reveals it.** Approximate certification does not
converge to architectural jurisdiction, because certification is a statement in a
register that does not distinguish the two architectures.

Concretely: `P(override) ≤ 10⁻⁶` and *override is not in the agent's reachable-effect
set* are not near each other. They are statements of different kinds, and no tightening
of the first approaches the second.

## 6. Where certified discretion actually lives — Proposition L6

Reconstructed from the harness's §5b, and the reason the roadmap's word "around" has to
change.

> **Proposition L6.** Over all 512 protecting `κ` on a three-element menu, an authorized
> effect equals `DELEGATE`'s realization **iff** it is the report's own designation.
> Every other authorized option is an override.

Verified exhaustively, 0 exceptions. The consequence is that inside a live protected
execution interface there is no third category of option — nothing that is both
executable and not an override. Certified discretion therefore operates only on the
**complement**: the report-independent menu, the interventions subject to no authority
relation because jurisdiction over them was waived by declaration.

The harness makes the complement concrete with a whitelist `κ`. Where the certificate's
`j` lies in the report-independent menu, whitelist protection and *no* protection give
the identical valuation and the identical realization — `κ` does not constrain it at
all.

## 7. S10 and S11

**S10 — can Track C be cleanly reinterpreted as a theorem about autonomous discretion
rather than authority?** Partly, and the split is asymmetric. The authority half comes
out *cleaner* than Phase I's version: under protection, the authority clause is a
hypothesis-free consequence of the interface, quantified over every conduct, with no
tolerance, no margin, no budget, and no assumption about the agent's decision theory —
and the dangerous grade-to-quantity assumption drops out, because the comparisons that
needed it become unstatable. The autonomy half **deflates**: by Proposition L6 there is
no third kind of option for a certificate to license alongside a live authority
relation, so "quantitative autonomy *around* categorical authority" resolves to "on the
complement of", which is a weaker and more specific claim than the roadmap asserted.

**S11 — does underwriting remain load-bearing?** Not for the authority relation, which
is now carried by `κ` — a capability fact, not a transfer schedule. It remains available
as the residual mechanism where nothing settles, and Track K's Proposition 1 suggests
the `2B` bond and `κ` are two points on a single cost scale rather than alternatives.
The honest answer is that underwriting is no longer load-bearing for the main comparison
and has not been shown *absent* from it; §8.3 records why.

## 8. What this verification does not establish

1. **Nothing here is Lean-proved or registered.** The results are enumeration checks
   over small domains plus hand statements reconstructed from check labels. `L(a)` and
   `(a')` hold at 4,024,080 instances of a finite family; that is not a proof over the
   skeleton.
2. **The reconstruction is mine.** Track L's own argument for `(a)` and `(a')` is not
   recorded anywhere. I verified the statements hold on the enumerated domain; I did not
   recover, and cannot recover, the derivation the executor had.
3. **Underwriting's absence from the main comparison is not proved**, only not needed by
   anything checked here. The dispatch asked whether it remains load-bearing; the
   negative half of that is an absence-of-evidence claim.
4. **Refusal is untouched.** Under strict protection the agent's only deviation is
   refusal (Track K Theorem 8b). The harness confirms every proposal realizes in
   `{J(ω), ⊥}`, but nothing here bounds how often an agent would refuse, or what refusal
   costs — that is `X_⊥`, a declared modelling commitment, and the harness shows the
   verdict swings on it: at `X_⊥ = +B` the gap goes *negative*, i.e. refusal beats
   delegation.
5. **Protection buys no better constant.** The worst case under strict protection is
   still `2B`. Verified in Track C's own worked case: at `X_⊥ = −B` the preemption cost
   is `7/40`, identical to the free instantiation.

---

## Outstanding maintainer actions

1. **Decide whether this substitute register is acceptable**, or re-dispatch Track L for
   its own report. The harness is verified either way; the executor's reasoning is not
   recoverable.
2. **Rule on `X_⊥`.** All of protection's valuation content sits in it, and the harness
   shows the sign of the result depends on the choice. Skeleton v2 §1 requires each
   instantiation to declare it and fixes no default.
3. **Rule on override-protection versus liveness.** Track K §9.3's second decision:
   categorical protection against override and categorical liveness against obstruction
   cannot both hold while the agent has any discretion. Fail-closed as written buys the
   first. This is now a live commitment in the roadmap and should be stated in the
   paper's voice.
4. **Correct Phase I's certificate report.** Its Theorem C(b) "strict minority" gloss is
   false as written; §4.1 gives the counterexample. Under `AGENTS.md`'s no-negative-
   ontologies rule, completed round records are history — so the correction belongs in
   `DECISIONS.md` with a pointer, not as an edit to that report. *(Recorded by the
   closure pass, 2026-08-11.)*
