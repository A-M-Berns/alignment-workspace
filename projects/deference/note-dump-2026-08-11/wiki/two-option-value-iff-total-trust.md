# Value ⟺ Total Trust on two-option menus (the exact identity)

*On the two-option menu $\{X, \text{const } s\}$, "Value on this menu" and "Total Trust at $(X,s)$" are the **same statement** — an exact linear identity, both arrows, per $(X,s)$, with no tower. What this page does **not** prove: full-menu Value ⟺ Total Trust. It delivers Value ⟹ Total Trust in full (full-menu Value contains the two-option case), and the converse only on two-option menus; the full-menu converse is the subject of [[total-trust-implies-value-telescoping]].*

**Naming.** Until 2026-07-23 this page was called `value-iff-total-trust-witness`, borrowing DDB's usage: in their Lemma 7.1 the two-option menu is the *witness* exhibiting a given Total-Trust instance as a Value instance — sound terminology for the direction Value ⟹ Total Trust, where the menu witnesses each cut. But extended to name the page and the identity, "witness" read as advertising a proof of the full equivalence, which this page is not. Renamed accordingly; "witness identity/menus" in legacy documents and extractions (deference-v6, `session-b9e8341b-proof.md`) means what this page calls the **two-option identity** and **two-option menus**.

## Setting

**Abstract single-expert setting** ([[setting-and-notation]]): novice $H \dashv \mathcal{C}_H$ a logical inductor; expert $E^\ast$ **observable** and **coherent**. Introspection is **not** used, and no deference hypothesis (no Mart, no self-trust theorem) is assumed — this is DDB's *easy* direction (their Lemma 7.1), ported with only the novice's linearity (`loe`, 4.8.4) and enough expert coherence to read the two-option argmax. Source: deference-v6 §1.2 (`deference-in-logical-induction-v6.md`).

What each condition buys here:
- **Observability** makes the followed strategy below an e.d. LUV (its formula case-splits on the expert's readable estimate) — the hard indicator appears only *inside the LUV*, never as a trade weight, so the discontinuity obstruction of [[setting-and-notation]] does not arise.
- **Coherence** is used only through $E^\ast(\text{const } s) = s$, so that "the expert takes $X$ iff $E^\ast(X) \ge s$" *is* the argmax rule on this menu (tie broken toward $X$; any ledger-decided tie-break works — [[ledger-decided-tie-breaks]]).

## Statement

Fix a bet $X$ (bounded $[a,b]$-LUV) and a threshold $s$; offer the menu $\{X, \text{const } s\}$. The followed strategy ([[deference-notions]]) is

$$ \widehat S_{\{X,s\}} = X\cdot\mathbb{1}[E^\ast(X)\ge s] + s\cdot\mathbb{1}[E^\ast(X)<s]. $$

**Two-option identity** (exact, linearity alone; read $E_\pi$ as $E^H_n$, finite-exact):

$$ \boxed{\ E_\pi(\widehat S_{\{X,s\}}) - s\,E_\pi(1) \;=\; E_\pi\big((X-s)\,\mathbb{1}[E^\ast(X)\ge s]\big)\ } $$

Hence **Value against the constant option** ($E_\pi(\widehat S_{\{X,s\}}) \ge s\,E_\pi(1)$) holds **iff** the boxed right side is $\ge 0$, i.e. iff the unnormalized **upper cut** of Total Trust holds at $(X,s)$; dividing by the conditioning mass gives $E_\pi(X \mid E^\ast(X) \ge s) \ge s$. Symmetrically (same decomposition, other baseline):

$$ E_\pi(\widehat S_{\{X,s\}}) - E_\pi(X) \;=\; E_\pi\big((s-X)\,\mathbb{1}[E^\ast(X)< s]\big), $$

so **Value against the fixed option $X$** holds iff the **lower cut** $E_\pi(X \mid E^\ast(X) < s) \le s$ holds. Quantifying over all $(X, s)$:

$$ \textbf{Value (all two-option menus } \{X, \text{const } s\}\textbf{)} \iff \textbf{Total Trust (all } X, s, \text{ both cuts)}. $$

Because both identities are *equalities*, each arrow is exact and lossless, **per $(X,s)$**: "Value on the menu $\{X, \text{const } s\}$" and "Total Trust at $s$" are literally the same number being nonnegative.

## Proof

Pointwise, on every world: $\widehat S_{\{X,s\}} - s = (X-s)\cdot\mathbb{1}[E^\ast(X)\ge s]$ (the low-region terms $s - s$ cancel), and $\widehat S_{\{X,s\}} - X = (s-X)\cdot\mathbb{1}[E^\ast(X)<s]$. Both are $\Gamma$-provable LUV identities. Apply $E_\pi$ and use linearity. $\blacksquare$

In LI dress: the identities are provable identities of bounded e.d. LUV-combinations, carried through $E^H_n$ by `loe` (4.8.4) — and that is the *entire* proof. No tower step, no `expprovind` inequality, no expert-side fact beyond $E^\ast(\text{const }s)=s$.

**Soft/LI form.** Total Trust in LI is soft ([[deference-notions]]), so the honest LI form concerns the **$\delta$-hedged** strategy $\widehat S_{\{X,s\},\delta} := X\cdot w_{s,\delta} + s\,(1 - w_{s,\delta})$ with $w_{s,\delta} = \operatorname{Ind}_\delta(E^\ast(X) > s)$. `loe` gives $E^H_n(\widehat S_{\{X,s\},\delta}) \approx_n E^H_n(X\,w_{s,\delta}) + s\,E^H_n(1) - s\,E^H_n(w_{s,\delta})$, and the equivalence becomes: $E^H_n(\widehat S_{\{X,s\},\delta}) \gtrsim_n s\,E^H_n(1)$ **iff** $E^H_n(X\,w_{s,\delta}) \gtrsim_n s\,E^H_n(w_{s,\delta})$ — soft Total Trust at $(s,\delta)$ — again both arrows, at each fixed width $\delta$. Recovering the conditional form divides by the mass $E^H_n(w_{s,\delta})$ (meaningful when the mass is bounded away from $0$) and sends $\delta \to 0$.

## Critical precision: two-option menus only (flagged)

What is proved is **Value restricted to two-option menus $\{X, \text{const } s\}$ $\iff$ Total Trust**. The forward direction of the full equivalence is unaffected — *full*-menu Value trivially implies two-option Value, hence Total Trust. But the reverse arrow here recovers only two-option Value; **Total Trust ⟹ full-menu Value is *not* delivered by this page**, and within deference-v6 it was only reachable by the long way round — squeezing Total Trust up to Mart and then applying [[mart-implies-value]]. Direct routes now exist: the cluster at [[total-trust-implies-value-telescoping]] (no gap-closure needed) and, for gap-closed bet classes, the gap-bet route [[total-trust-implies-mart]] + [[mart-implies-value]].

deference-v6's later gloss overstates this: the §5.9-area citation ("classwise Value via §1.2", and §5.11's "Value$_D$ ⟺ TT$_D$ pinned by §1.2") reads §1.2 as a full Value ⟺ Total Trust equivalence, which §1.2 does not prove (see the session extraction `imported-chats/analysis/session-b9e8341b-proof.md`, §"Corrections"). The gap is real but now closed: the routes assembled at [[total-trust-implies-value-telescoping]] prove Total Trust ⟹ full-menu Value directly (telescoping over pairwise keep-or-switch rungs, or in one step — with a $\delta$-hedging caveat at threshold $0$, removed under full TT by [[provable-bound-respect]]), without the squeeze. With that lemma in place, the corpus-level claims that convert forced Total Trust into Value ([[faithful-acceleration-result]]) are repaired; on the *hard*-argmax strategy the residue is exactly the near-threshold term flagged on both of those pages.

⚠ **Scope flag (2026-08-02).** The forward gloss above — full-menu Value contains the two-option case, hence Value ⟹ Total Trust in full — silently weakened when Value's quantifier was restricted to conditional-stable menus ([[total-trust-implies-value]] §Necessity): not every menu $\{X, \text{const } s\}$ is conditional-stable. At bets whose quote hovers on the threshold, the menu can fail the condition with Value genuinely false on it — while the *hard* above-threshold inequality this page's identity computes is itself false there, though soft Total Trust holds. Under the honest Value hypothesis, the right-to-left direction of this page therefore serves only the stable pairs; full-strength entry into soft Total Trust runs through the fold instead ([[tower-implies-total-trust]]). The certificate (the liar probe) and the loop-level consequences: [[loop-direction]].

## Status

**KERNEL-CHECKED** — two Lean statements in `LeanDeference.lean` (deference-v6 §1 Lean block):

- `DeferenceConverse.value_iff_totalTrust` — the finite-exact identity, **stated as an iff** (both arrows), quantified over all $(X,s)$, hard indicators legal in the finite setting;
- `DeferenceConverseAsymp.value_iff_totalTrust_asymptotic` — the soft/asymptotic form at fixed $s$: given the `loe` decomposition as the hypothesis `hLoe`, the iff $\;s\,E^H_n(1) \lesssim_n E^H_n(\widehat S_{\{X,s\},\delta}) \iff s\,E^H_n(w) \lesssim_n E^H_n(Xw)$.

deference-v6 Appendix B (abstract-theory block, "the most solid tier"): "`Value ⟺ Total Trust` (two-option witness, both arrows) — status `P`, §1.2" (Appendix B's "witness" = this page's two-option menu; see the Naming note).

**The Lean honesty caveat** ([[conventions-and-status-labels]]) applies: the finite-exact theorem checks the worlds-sum algebra of the identity; the asymptotic form takes the `loe` carry as a named hypothesis (`hLoe`) over real sequences. `loe` itself and the market are unmodeled (status `LI` — black-boxed). Given 4.8.4, the prose proof above is complete; nothing else is assumed.

## Related

- [[deference-notions]] — Total Trust (soft form), Value, the menus/followed-strategy apparatus
- [[mart-implies-value]] — the forward arrow of the full equivalence (spends the tower; this page spends none)
- [[total-trust-implies-value-telescoping]] — closes the two-option→full-menu gap flagged above
- [[total-trust-implies-mart]] — the other leg of the reverse direction (Total Trust ⟹ Mart), now a gap-bet two-liner for gap-closed classes; [[amplifier-counterexample]] — why parallel cuts alone were never enough
- [[value-iff-mart]] — the assembled lattice with per-arrow status
- [[reversal-of-difficulty-vs-ddb]] — this is DDB's easy direction (Lemma 7.1); LI keeps it easy and makes their hard one easy too
- [[faithful-acceleration-result]] — the downstream consumer of the reverse arrow (forced Total Trust → Value)
- [[loop-direction]] — the right-to-left direction under honest scope-restricted Value serves only stable pairs (the liar probe)

*Source: deference-v6 §1.2 (`deference-in-logical-induction-v6.md` L198–211); precision flag from `imported-chats/analysis/session-b9e8341b-proof.md` §"Corrections to v6". Renamed from `value-iff-total-trust-witness` 2026-07-23.*
