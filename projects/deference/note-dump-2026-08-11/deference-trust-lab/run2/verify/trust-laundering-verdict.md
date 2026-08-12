# Faithfulness-gate verdict: TODO `trust-laundering`

**Verdict: SHADOW** (the validation uses a strict shadow of DDB/Lean Total Trust; the
headline non-vacuity witness is a **vacuous chain** under the genuine property — both short
links actually fail). The *underlying claim* (genuine non-transitivity) is nonetheless TRUE
and I located honest witnesses for it — see "Salvage" — but the executor's reported artifact
does NOT establish it, so the work as submitted is a shadow, not a real result.

Modality: EXEC. Attacker = independent skeptic; success metric = finding fakeness. Found it.

---

## 1. What the executor claimed

"Total Trust / endorsement is NOT transitive over DDB-style finite frames. Exhaustive-grid +
randomized search using the EXACT inequality `value_witness_iff_totalTrust_mass`. Explicit
verified witness: both short links (H→A, A→B) hold over **all 32 (X,s) pairs**, yet H→B fails
at X=1[world1], s=1/2, gap 1/8. Recovery conjecture refuted; obstruction is prior mismatch."

Faithfulness rests entirely on: (i) the inequality computed is the real DDB/Lean one, and
(ii) "both short links HOLD" is a faithful instance of `pi Total-Trusts P`.

## 2. The inequality IS faithful — but the quantifier is NOT

The Lean keystone `DeferenceConverse.value_witness_iff_totalTrust_mass` (LeanDeference.lean
L426–431) states, for the conditioning event `{w : s ≤ ∑_v P w v · X v}`:

```
s · (∑_{Ew≥s} π w)  ≤  ∑_{Ew≥s} π w · X w
```

The Python `TT_holds` (trust-laundering.py L73–82) computes exactly this with exact
`Fraction`s. **The per-(X,s) inequality is a faithful match** — genuine conditional-mass form,
not "equal means". Shadow-test (d) does NOT fire.

BUT the DDB/Lean *property* `π Total-Trusts P` quantifies over **all** random variables:
- v2 §0.2 L77: *"Total Trust. For **every** random variable X and threshold t: E_π(X | E(X)≥t) ≥ t."*
- Lean `value_iff_totalTrust` (L446–454): `∀ (X : W → ℝ) (s : ℝ) …` — **all real-valued X**.

The script tests only `X ∈ {0,1}^W` and `s ∈ {1/3,1/2,2/3,1}` — **32 points** for |W|=3.
The script's `link_holds` (L92–99) calls this set "Total Trust over the WHOLE grid." It is not
the whole anything: it is a 32-point coarse shadow of an infinite quantifier. **The object
validated ("link HOLDS over the full grid") is a strictly weaker predicate than the DDB/Lean
Total Trust it claims to test.** That is the laundering: not in a Lean hypothesis (there is no
Lean), but in silently replacing `∀X:W→ℝ` with `∀X∈{0,1}^W ∧ s∈{4 values}`.

## 3. The headline witness is a VACUOUS CHAIN (shadow-test case (c))

Re-running the executor's own `WITNESS` against the faithful property (rich grid
`x∈{k/8}`, `s∈{k/24}` ∪ breakpoints — a close proxy for "all X, all s"):

| link | coarse 32-pt grid (script) | faithful (all-X) grid | explicit faithful failure |
|------|---------------------------|------------------------|---------------------------|
| **L1 H→A** | HOLDS | **FAILS** | X=(0, 7/8, 5/8), s=2/3, lhs 1/6 > rhs 5/32, gap **1/96** |
| **L2 A→B** | HOLDS | **FAILS** | X=(3/4, 0, 1/4), s=1/3, lhs 1/12 > rhs 1/16, gap **1/48** |
| LONG H→B | FAILS | FAILS | (as claimed) |

So under the genuine DDB/Lean Total Trust definition, **NEITHER short link holds.** The chain
"H Total-Trusts A, A Total-Trusts B" is false at both edges. This is precisely the
pre-registered SHADOW case **(c): "credences where one link actually FAILS (a vacuous chain)."**
The reported headline — "both short links hold over all 32 (X,s) … yet H→B fails" — is true of
the 32-point grid and FALSE of the property the claim is about. The 1/8 long-edge gap is real,
but a chain whose premises are both false is not a non-transitivity witness; it is a vacuous
implication.

The `NESTED_WITNESS` (Part 3) inherits the same defect (its short links were certified on the
same 32-point grid). The Part-2 genericity stat (41% break) and Part-4 recovery sweep are all
computed with the coarse-grid `link_holds`, so every quantitative claim is about the shadow
predicate, not DDB Total Trust.

## 4. Why the {0,1} grid is not a defensible test class

One might argue indicators suffice (biconvex sets ↔ cuts). They do not:
- For the executor's `(π_A, P_B)`, Total Trust holds on **all** {0,1}-indicators and **all**
  thresholds (0 failures) yet FAILS at the real-valued `X=(3/4,0,1/4)`. Indicators are blind to
  it. So even "all indicators, all s" ≠ DDB Total Trust; the executor's "4 thresholds, 8
  indicators" is doubly coarse.
- Symmetric blindness in the other direction: my salvage witness (§5) has all three links
  holding on every {0,1}-indicator; its long-edge failure is only visible on non-indicator X.

The shadow cuts both ways: the coarse grid spuriously passes failing short links AND would
spuriously pass failing long edges. It is not a conservative proxy in either direction.

## 5. Salvage — the CLAIM is true; honest witnesses exist (this is what makes it SHADOW not BROKEN)

Searching with the faithful (rich-grid) predicate on BOTH short links and the long edge: of 418
chains the script's coarse grid would accept, only 24 survive the faithful test on both short
links, and **6 are genuine faithful non-transitivity witnesses**. Verified one on a very fine
grid (`x∈{k/8}`, `s∈{k/24}` ∪ breakpoints):

```
pi_H = (1/4, 1/2, 1/4)        pi_A = (1/4, 1/4, 1/2)     (priors differ)
P_A  = [[1/2,1/4,1/4],[0,3/4,1/4],[0,1/2,1/2]]    fibers {0},{1},{2}
P_B  = [[1/4,1/4,1/2],[0,3/4,1/4],[0,1/4,3/4]]    fibers {0},{1},{2}
  L1 H->A : 0 faithful failures (genuinely Total-Trusts)
  L2 A->B : 0 faithful failures (genuinely Total-Trusts)
  LONG H->B: 213 faithful failures (genuinely does NOT Total-Trust); first fail X=(0,1/8,1/4), s=5/32
```

Notably the long-edge failure here needs a **non-indicator** X — confirming again that the
executor's indicator-only search could never have found a clean witness, only false ones.

So: **non-transitivity of genuine DDB/Lean Total Trust is REAL.** The executor's *conclusion* is
correct; the executor's *validation* (artifact, witness, every statistic) is a shadow that does
not establish it. Under the gate's rules ("compiles/runs ≠ real; faithful + non-vacuous"), an
EXEC artifact whose printed non-vacuity witness is a vacuous chain under the real property is a
SHADOW.

## 6. On the recovery sub-claim

The "recovery = prior identity π_H=π_A" finding is, as the writeup honestly flags, an identity
(long edge ≡ L2 when π_H=π_A) — content-free as a composition law, and correctly labelled so.
But it too is computed on the shadow predicate, so its quantitative support (343/0, etc.) does
not transfer. The qualitative point (delegation through a *different* standpoint doesn't compose;
nesting doesn't rescue) is plausible and survives morally, but is not validated as reported.

## 7. Scope / PROOF-ONLY dodge — honest

"No Lean" is correct and not a dodge: a Lean file hard-coding three distributions checking one
inequality would be the named SHADOW (b), and the all-X quantifier is not finitely checkable by
the grid the executor used. The LI/asymptotic D3 layer is correctly left PROOF-ONLY; no
hypothesis-laundering of LI theorems occurs (there is no LI content in the artifact at all).

## 8. Verdict

**SHADOW.** Settling attack: re-ran the executor's own `WITNESS` against the faithful all-X
Total-Trust property (rich rational grid) — **both** short links fail (L1 at X=(0,7/8,5/8) s=2/3
gap 1/96; L2 at X=(3/4,0,1/4) s=1/3 gap 1/48), so the printed non-vacuity witness is a vacuous
chain, exactly the pre-registered shadow case (c). The "both links hold over all 32 (X,s)" is
true only of a 32-point shadow of `∀X:W→ℝ`. The real claim is TRUE (I found 6 genuine
faithful witnesses, one fine-grid-verified), so this is SHADOW (laundered/trivialized
validation of a true claim) rather than BROKEN — but the submitted artifact does not establish
the result it reports.
