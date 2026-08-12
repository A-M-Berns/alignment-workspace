# Conventions and status labels

*Wiki for the deference-in-logical-induction project. Each page covers one result or one concept, stating its own setting and hypotheses at the top, so it is always clear which assumptions carry which results. Pages link via `[[page-name]]` (Obsidian). Master map: [[index]].*

## Notation (shared across pages; pages restate what they use)

- $H \dashv \mathcal{C}_H$ — the human/novice logical inductor over trader class $\mathcal{C}_H$ (canonically P). $A \dashv \mathcal{C}_A$ — the AI/expert inductor (canonically EXP), $\mathcal{C}_H \subseteq \mathcal{C}_A$.
- $E^H_n(X)$ — $H$'s day-$n$ expectation of LUV $X$; $\mathbb{P}^H_n(\varphi)$ its day-$n$ price of sentence $\varphi$.
- $a_n := E^A_n(\ulcorner Y_n \urcorner)$ — the AI's quote on the day-$n$ target $Y_n$.
- $\mathbb E^\ast_n(X) := E^A_n\big(\ulcorner E^H_{f(n)}(X)\urcorner\big)$ — the **lookahead expectation** (li-deference §Formalism). **Abram (2026-08-11): abbreviate as $\mathbb E^\ast_n$, not $B_n$/$B_t$** — it should keep looking like an expectation. Pages predating this line use $B_n$; read them accordingly. Context: [[eisenstat-conjecture-attribution]] §1.
- Lookahead $F(n)$ / $f(n) \sim 2^n$; schedules $e(n) < F(n) < \sigma(n)$.
- $X \approx_n Y$: the difference $\to 0$. $X \gtrsim_n Y$: $\liminf (X - Y) \ge 0$.
- $\operatorname{Ind}_\delta(\cdot)$ — soft (continuous ramp) indicator with width $\delta$.
- Violation weight (faithful acceleration): $w_n = \operatorname{Ind}_\delta(a_n > t)\cdot \operatorname{Ind}_\delta(E^H_n(X) < t - \varepsilon)$.
- $\Gamma$ — the deductive process's theory. "e.c." = efficiently computable — reserved for what traders must *evaluate* (weights, features, tie-break rules).
- **"e.d."** (efficiently *describable*) — this wiki's preferred term for the LI paper's "e.c." as applied to LUVs/bets: the *description* (formula) is produced efficiently; the described value may be uncomputable (halting-bit LUVs). Deliberate break with the paper's vocabulary; rationale at [[setting-and-notation]] §LUV, consequences at [[ledger-decided-tie-breaks]].
- **"delay", not "staleness"** (Abram, 2026-07-29) — for the case where two inductors do not clear as one fixed point. Shorter, neutral, and the non-shared-fixed-point case is the **default**, not a specially-named pathology; what deserves a name is the extra assumption (joint clearing), not its absence. Delay is one axis among several — see [[delay-and-visibility]] §1.
- **deference-v6** — `deference-in-logical-induction-v6.md`, the legacy monograph (retained as history; supersession table in [[index]]). Cite it as "deference-v6 §x.y"; never abbreviate to a bare "v6" — bare version tags go ambiguous the moment another document reaches a v6 of its own.

## Deference notions (defined in [[deference-notions]])

**Mart / the tower** (pointwise equality) · **conditional tower / the fold** · **Total Trust** (soft-conditioned inequality) · **Value** (menu/instrumental) · **Reflection** (too strong).

## Label → paper-theorem dictionary

References are to Garrabrant et al., *Logical Induction* (arXiv:1609.03543v5); source of truth is `references/logical-induction/main.tex`, which uses symbolic labels — cite by *name* if edition numbering differs.

| label | name | arXiv v5 # |
|---|---|---|
| `loe` | Linearity of Expectation | 4.8.4 |
| `expprovind` | Expectation Provability Induction | 4.8.10 |
| `epr` | Expectations of Probabilities | 4.11.3 |
| `er` | Iterated Expectations | 4.11.4 |
| `cee` | Expected Future Expectations | 4.12.1 |
| `ccee` | No Expected Net Update under Conditionals | 4.12.3 |
| `st` | Self-Trust | 4.12.4 |
| — | Recurring Unbiasedness (propositional / affine / expectation) | 4.3.6 / 4.5.9 / 4.8.15 |
| — | Unbiasedness From Feedback (propositional / affine / expectation) | 4.3.8 / 4.5.10 / 4.8.16 |
| — | Paradox Resistance | 4.11.2 |
| — | Expectations Converge | 4.8.3 |
| — | Learning Varied Pseudorandom Frequencies (affine / LUV) | 4.4.5 / 4.8.17 |
| — | Continuous Threshold Indicator ($\operatorname{Ind}_\delta$) | 4.3.2 |
| — | Generable From $\overline{\mathbb{P}}$ | 4.3.5 |

`Mart` is **not** a paper theorem — it is the deference *hypothesis*; its self-trust instance is `cee` (4.12.1).

⚠ **Numbering corrected 2026-07-29** by walking the paper's shared theorem counter: `epr`/`er` are **4.11.3/4.11.4** (this table previously said 4.11.4/4.11.5 — there is no Theorem 4.11.5), and propositional Recurring Unbiasedness is **4.3.6** (4.3.7 is Definition *Deferral Function*). Three errata in the printed text, including a previously unnoticed one in Definition 4.4.4: see [[li-paper-erratum]].

## Exposition style (Abram's feedback, 2026-07-28)

- **No shadow variables.** Never introduce a second name for the decided *value* of a formula that already has a name (e.g. "$c_n :=$ the value of $w_n$") — a decided LUV and its rational value can share one symbol, with the identification stated once. Introduce an abbreviation only when the long form genuinely obstructs reading; prefer spelling out $E^A_n(V_n)$ over coining a fresh letter for it.
- **Don't use "cut" as a noun for the Total-Trust inequalities**, or lean on bare jargon like "the threshold bound." Say which inequality is meant in words: conditioning on the quote being above (or below) the threshold — the two *halves* of the condition.
- **State a fact at its natural grain.** If an argument's content is one sentence ("the ramp is positive only where the quote exceeds $v$"), do not expand it into a case analysis.

## Status labels

Every stated result carries one of:

- **KERNEL-CHECKED** — a Lean statement in `lean-deference/` covers the arithmetic/algebraic chain (see the honesty caveat below).
- **PROVED (prose)** — a complete written proof, not machine-checked.
- **PROVED modulo named hypotheses** — proof complete given explicitly named unproved inputs (each listed on the page).
- **CONJECTURED (~p)** — with the working credence carried over from the source chat/session where one was given.
- **REFUTED** — with the counterexample.
- **INTERPRETATION** — a reading/moral, not a mathematical claim.

## The Lean honesty caveat (applies wherever KERNEL-CHECKED appears)

**The Lean proves the deference algebra, not the forcing.** In several modules the "theorem" is a squeeze over hypotheses that restate the conclusion (e.g. T1/T3 of the frozen construction, and the faithful-acceleration trader chain given `hbias`/`hbdd`); the market and trader dynamics are entirely unmodeled. Machine-checking here certifies the arithmetic skeleton, never that logical induction *forces* the premises. Per-claim details: deference-v6 §7 and Appendix B (`deference-in-logical-induction-v6.md` L794, L905), and `lean-deference/AUDIT.md`.

## Provenance conventions

- Legacy documents (`deference-in-logical-induction-v6.md`, the original FA notes, the `fa-positive-*-corrected` files) are **retained unmodified as history**; the wiki supersedes them where pages say so. The supersession table lives in [[index]].
- Warning: `fa-positive-result-corrected.md` (v1) and `fa-positive-results-corrected-v2.md` contain claims **retracted later in the source chat** (see [[new-chats-2026-07]]); `fa-positive-results-corrected-v3.md` is the best file-form statement but predates the chat's final results.
- Source chats live in `imported-chats/`; planning briefings in `imported-chats/analysis/`. The FA chat's seven intermediate working documents could not be recovered from the export (tool-call bodies elided) — see the recovery note in [[new-chats-2026-07]] and `imported-chats/fa-chat-artifacts/README.md`.
