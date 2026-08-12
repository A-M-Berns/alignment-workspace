# Extraction: new Total Trust ⟹ Value proof (Claude Code session b9e8341b, 2026-07-20)

*Provenance: extracted 2026-07-21 from the session transcript (uuid `b9e8341b`). The proof exists ONLY in that conversation — no file was written by that session. A curated copy of the full conversation now ships alongside this folder's other transcripts (`2026-07-20__…__b9e8341b.md`). This extraction is the source for the wiki page [[total-trust-implies-value-telescoping]].*

## Session context

Q&A about `deference-in-logical-induction-v6.md`. Four user turns: (1) elaborate the Mart ⟹ Value argument of §1.1; (2) provide a label→paper-theorem dictionary with verbatim quotes from the Logical Induction paper; (3) the converse direction; (4) "Can you prove total-trust -> value similarly to how you proved mart->value?" — the fourth turn produced the new result. The assistant explicitly checked: "This argument is **not in v6** — §1.2 stops at witness menus, and the §1.3 table routes 'Total Trust ⟹ Value' through the tower."

## The new theorem: full-menu Total Trust ⟹ Value by telescoping (menu induction)

### Setup

Total Trust used only at threshold 0, in the unnormalized form §1.2 shows equivalent to the conditional one:

> **TT(D, 0):** for every e.c. bounded LUV-combination $D$ built from menu options and observable expert-estimates: $E^H_n\big(D\cdot w(E^\ast(D))\big)\gtrsim_n 0$, where $w = \operatorname{Ind}_\delta(E^\ast(D)>0)$ (soft threshold weight; in the finite-exact setting, the hard indicator).

Expert $E^\ast$: observable, coherent, introspective (as in v6 §1.1). Menu $\{O^1,\dots,O^K\}$, $m^j = E^\ast(O^j)$, $M_k = \max_{j\le k} m^j$.

### Construction — follow-the-expert as a chain of keep-or-switch decisions

Relabel so the comparison option $O^i$ is first. Define recursively:

$$\widehat S^{(1)} := O^1 = O^i, \qquad D_k := O^k - \widehat S^{(k-1)}, \qquad \widehat S^{(k)} := \widehat S^{(k-1)} + D_k\cdot\mathbb{1}[E^\ast(D_k)>0].$$

At each stage the expert compares incumbent to the next option and switches iff it rates the newcomer strictly higher. Each $\widehat S^{(k)}$ and $D_k$ is an e.c. LUV (its formula references only menu options and the expert's observable estimates).

**Claim A (F1, generalized): $\Gamma\vdash E^\ast(\widehat S^{(k)}) = M_k$.** By induction, using introspection (the weight is a function of the expert's own known estimates) and coherence:
$$E^\ast(\widehat S^{(k)}) = E^\ast(\widehat S^{(k-1)}) + E^\ast(D_k)\cdot\mathbb{1}[E^\ast(D_k)>0] = M_{k-1} + \max(0,\,m^k - M_{k-1}) = M_k,$$
using $E^\ast(D_k) = m^k - M_{k-1}$ (expert linearity + inductive hypothesis).

**Claim B:** $\widehat S^{(K)}$ *is* the argmax strategy $\widehat S$ under the "first max wins" tie-break (computable, hence legal; and F1 is tie-break-independent anyway).

### The chain / theorem

For each $k = 2,\dots,K$:
$$
\begin{aligned}
E^H_n(\widehat S^{(k)})
&\approx_n\ E^H_n(\widehat S^{(k-1)}) + E^H_n\big(D_k\cdot\mathbb{1}[E^\ast(D_k)>0]\big)
&&[\text{Linearity of Expectation, Thm 4.8.4}]\\
&\gtrsim_n\ E^H_n(\widehat S^{(k-1)})
&&[\textbf{TT}(D_k, 0)].
\end{aligned}
$$
Telescoping from $K$ down to $1$:
$$E^H_n(\widehat S) = E^H_n(\widehat S^{(K)}) \;\gtrsim_n\; E^H_n(\widehat S^{(1)}) = E^H_n(O^i). \qquad\blacksquare$$

**Structural reading (punchline):** by the §1.2 boxed witness identity, TT($D_k$, 0) *is* Value on the two-option menu $\{D_k, \text{const }0\}$. So: *"follow the expert on a K-menu" decomposes into K−1 pairwise keep-or-switch deferrals, and two-option Value telescopes to full Value.* The convex-geometry squeeze of §1.6 is bypassed because Value never needed $g=\mathrm{id}$ (the tower equality) — Value is "one rung below the tower."

### Assumptions used

Only the novice's own theorems — **Linearity of Expectation (Thm 4.8.4)** and **Expectation Provability Induction (Thm 4.8.10)** carrying the Γ-provable decomposition identity through $E^H_n$; expert-side facts only coherence + introspection (Claim A). No tower/self-trust theorem used.

### Three caveats (flagged in the session)

1. **No contradiction with DDB's "excruciating" direction:** the induction applies TT to *derived* bets $D_k = O^k - \widehat S^{(k-1)}$ that mention the expert's estimates. In LI these are honest e.c. LUVs because observability puts the expert's estimates into the novice's world as decided facts (the "thin channel"). In DDB the frame $P$ is not world-measurable, so $D_k$ is not a legal bet and the induction is unavailable — §2.1's moral relocated: the DDB-hard direction is cheap *because of* observability.
2. **No contradiction with the §1.6 amplifier:** the amplifier shows single-bet *parallel cuts* cannot pin the tower *equality*; here TT is used over *all* derived bets and only the *inequality* (Value) is concluded, never the equality (Mart). An amplifier-like novice can survive these hypotheses and still fail the tower, but cannot fail Value.
3. **Soft/hard — where the LI continuum bites:** with genuine soft weights $\operatorname{Ind}_\delta$, the honest theorem is about the **δ-hedged** strategy $\widehat S^{(k)}_\delta := \widehat S^{(k-1)}_\delta + D_k\cdot\operatorname{Ind}_\delta(E^\ast(D_k)>0)$; telescoping goes through verbatim and Claim A softens to $E^\ast(\widehat S^{(K)}_\delta) \ge M_K - \delta$. Total Trust alone does **not** give Value for the *hard*-argmax strategy: threshold cuts only lower-bound high-region integrals and upper-bound low-region ones, so nothing lower-bounds $E^H_n(D\cdot\mathbb{1}[0<E^\ast(D)\le\delta])$ — that missing bound is exactly the amplifier's surviving degree of freedom. Hard-argmax Value therefore remains a Mart-only deliverable. In the finite-exact/DDB-style setting, hard indicators are legal and the induction gives full hard Value exactly.

## Supporting material re-derived in the session (existing v6 content)

- **Forward Mart ⟹ Value (§1.1)** four-line chain with paper names:
$$E^H_n(\widehat S_n)\;\underset{\text{Mart}}{\approx_n}\;E^H_n(\ulcorner E^\ast(\widehat S_n)\urcorner)\;\underset{\text{4.8.10}}{\approx_n}\;E^H_n(\ulcorner M_n\urcorner)\;\underset{\text{4.8.10}}{\gtrsim_n}\;E^H_n(\ulcorner m^i_n\urcorner)\;\underset{\text{Mart}}{\approx_n}\;E^H_n(O^i_n)$$
using F1 ($E^\ast(\widehat S_n)=M_n$) and F2 ($M_n\ge m^i_n$).
- **Label→paper-theorem dictionary** (verified against `references/logical-induction/main.tex`, Garrabrant et al., arXiv:1609.03543): `loe` = Linearity of Expectation (Thm 4.8.4); `expprovind` = Expectation Provability Induction (Thm 4.8.10); `epr` = Expectations of Probabilities (4.11.4); `er` = Iterated Expectations (4.11.5); `cee` = Expected Future Expectations (4.12.1); `ccee` = No Expected Net Update under Conditionals (4.12.3); `st` = Self-Trust (4.12.4). `Mart` is NOT a paper theorem (it is the deference hypothesis; its self-trust instance is 4.12.1).
- **Converse Value ⟹ Mart** exposition: Leg 1 (§1.2) Value ⟹ Total Trust via the exact witness identity $E_\pi(\widehat S_{\mathrm{wit}}) - s\,E_\pi(1) = E_\pi\big((X-s)\,\mathbb{1}[E^\ast(X)\ge s]\big)$ (linearity only); Leg 2 (§1.6) Total Trust ⟹ tower, the hard convex-geometry squeeze left as prose, obstructed by the **amplifier** counterexample $g(e_0)=(1+2c)e_0-c$, $c>0$ (passes all parallel cuts, killed only by boundedness at endpoints $g(0)=-c<0$, $g(1)=1+c>1$).

## Corrections to v6 discussed (not applied)

1. **§5.9-area gloss** ("Value ⟺ Total Trust, pinned by §1.2") is stronger than what §1.2 proves (witness-menu Value ⟺ TT). Full-menu Value from TT isn't otherwise derivable in v6 without the §1.6 squeeze to Mart. The new proof closes this gap (modulo the soft-hedging caveat) and "would slot naturally between §1.2 and §1.4 as a lemma."
2. **Theorem-numbering precision:** v6 cites arXiv theorem numbers but `main.tex` uses symbolic labels; cite by name if edition numbering differs. v6 uses 4.8.4/4.8.10 in bounded form for [a,b]-LUVs while the paper proves [0,1] (affine rescaling taken as trivial); v6 §0.3 identifies 4.8.10's semantic hypothesis "W(A_n) ≥ b in every consistent world" with "Γ ⊢ A_n ≥ 0".
