# Mart ⟹ Value

*If the novice Marts an observable, coherent (introspective) expert, it Values it: the four-step chain — two tower steps, two `expprovind` carries — with no conditional martingale, no softmax, no bound on the menu size.*

## Setting

**Abstract single-expert setting** ([[setting-and-notation]]): novice $H \dashv \mathcal{C}_H$ a logical inductor; expert $E^\ast$ **observable** and **coherent**, with **introspection** entering only through F1 (see the remark below). Menus, the followed strategy $\widehat S_n$, and the facts F1/F2 as in [[deference-notions]]: an e.d. sequence of finite menus $\mathcal{O}_n = \{O^1_n, \dots, O^k_n\}$ of bounded $[a,b]$-LUVs, $m^j_n := E^\ast(O^j_n)$, $M_n := \max_j m^j_n$, $\widehat S_n := O^{\,j^\ast(n)}_n$ (least-index argmax; any ledger-decided tie-break — [[ledger-decided-tie-breaks]]). Source: deference-v6 §1.1.

**Hypotheses used — exactly these, nothing more:**

- **Mart**$(H \to E^\ast)$, but only on the two relevant LUV sequences: $(\widehat S_n)_n$ and $(O^i_n)_n$. Not the universal tower — two instances of it.
- The **novice's own** `loe` (4.8.4) and `expprovind` (4.8.10) — free LI theorems of $H$ ([[setting-and-notation]]).
- Expert-side: **(F1)** $\Gamma \vdash E^\ast(\widehat S_n) = M_n$ (tie-break-independent) and **(F2)** $\Gamma \vdash M_n \ge m^i_n$.

Observability makes $\widehat S_n$ an e.d. LUV (its formula references the menu, the readable estimates, the tie-break), so `argmax` never appears as a discontinuous trade *weight* — the obstruction does not arise.

## Statement

For every e.d. sequence of finite menus and every fixed index $i$:

$$ E^H_n(\widehat S_n) \;\gtrsim_n\; E^H_n(O^i_n). $$

That is: by the novice's own current lights, "let the expert decide" is asymptotically weakly preferred to committing to any fixed option — **Value**$(H \to E^\ast)$ ([[deference-notions]]).

## Proof

The four-step chain, each step annotated with its justification (paper-theorem names per the dictionary in [[conventions-and-status-labels]]):

$$ E^H_n(\widehat S_n) \;\underset{\textbf{Mart}}{\approx_n}\; E^H_n\big(\ulcorner E^\ast(\widehat S_n)\urcorner\big) \;\underset{\texttt{expprovind } 4.8.10}{\approx_n}\; E^H_n\big(\ulcorner M_n\urcorner\big) \;\underset{\texttt{expprovind } 4.8.10}{\gtrsim_n}\; E^H_n\big(\ulcorner m^i_n\urcorner\big) \;\underset{\textbf{Mart}}{\approx_n}\; E^H_n(O^i_n). $$

- **Step 1** (tower on $\widehat S_n$): the deference hypothesis **Mart** applied to the e.d. LUV sequence $(\widehat S_n)$.
- **Step 2** (F1 carried through $E^H_n$): $\Gamma \vdash E^\ast(\widehat S_n) = M_n$, so the difference $\ulcorner E^\ast(\widehat S_n)\urcorner - \ulcorner M_n\urcorner$ is a bounded e.d. LUV-combination provably $= 0$; `expprovind` (equality form, with `loe` splitting the difference) gives $\approx_n$.
- **Step 3** (F2 carried through $E^H_n$): $\Gamma \vdash M_n \ge m^i_n$ (a max dominates each entry); `expprovind` (inequality form) gives $\gtrsim_n$.
- **Step 4** (tower on $O^i_n$): **Mart** again, reading $\ulcorner m^i_n \urcorner = \ulcorner E^\ast(O^i_n) \urcorner$.

Chaining $\approx_n,\ \approx_n,\ \gtrsim_n,\ \approx_n$ yields $\gtrsim_n$. $\blacksquare$

Note what is *absent*: no conditional martingale, no softmax, no $\delta\log k$ penalty, no bound on the menu size $k$, no tie-breaking analysis (F1 is tie-break-free). Steps 2–3 each do two things: the (in)equality is *provable* (it holds in every consistent world), but it sits *inside* $E^H_n(\ulcorner\cdot\urcorner)$, and carrying a provable identity through $E^H_n$ is exactly what `expprovind` is for. This is the law of total expectation in LI dress, across two processes: the expert knows what it chose, so its estimate of its choice is the max; the tower carries the max back to the present, where it dominates each fixed option; the tower carries that back out to the option.

### Remark: what F1 actually costs (flagged)

deference-v6 §1.1 credits F1 to "**coherence** of $E^\ast$ in action" alone. That undersells the ingredient slightly: $\widehat S_n$ is a formula that *case-splits on the expert's own estimates*, so for $E^\ast$ to provably assign it the value $M_n$, the expert must correctly resolve that case-split — it must **know its own estimates**. This is exactly the introspection hypothesis (`hknow` in the fold, [[deference-notions]] §fold; the session extraction's Claim A makes the same point for the generalized F1 of the telescoping proof). The cost is nil for both canonical instances — the future self has `epr`/`er` (4.11.4/4.11.5), and the AI's estimates are published decided facts which any coherent operator respecting $\Gamma$ inherits — but in the abstract setting F1 is honestly **coherence + introspection**, not coherence alone. See [[expert-conditions]]. A third hidden line item: the tie-break must be **ledger-decided** ($\Gamma$-decided given the published estimates — equivalently, computable from them), or F1 fails outright by correlation: [[ledger-decided-tie-breaks]]. **⚠ (2026-07-25) — and a fourth, decisive one.** For the case under study — an inductor-expert, expectations the paper's price-integrals — "$\Gamma \vdash E^\ast(\widehat S_n) = M_n$" is exact only in the *surrogate* reading (linear extension of published quotes); the expert's actual expectation of the argmax expression tracks the max only asymptotically, only modulo introspection, and only on menus satisfying a **decision-theoretic scope condition**: on selection-referencing menus (the punishing-menu counterexample, [[total-trust-implies-value]] §Lemma 2) it fails outright and Value itself is false — so this theorem is hypothesis-conditional exactly there (the kernel-checked form already takes the F1 carry as a named hypothesis). F1 is where the entire expert-side bill lands: coherence + introspection + ledger-decided tie-break + conditional-stability.

## Status

**KERNEL-CHECKED** — `DeferenceArgmax.value_argmax_asymptotic` (in `LeanDeference.lean`), plus the finite-exact route `Deference.value_of_CM`. deference-v6 Appendix B (abstract-theory block): "Deference is the tower; `Value ⟺ Mart`" — status `P/C`, §1.1 — the most solid tier of the corpus.

**The Lean honesty caveat** ([[conventions-and-status-labels]]) in concrete form: the kernel-checked statement is

```lean
theorem DeferenceArgmax.value_argmax_asymptotic (ES Em Emi Eoi : ℕ → ℝ)
    (hUM_S : Approx ES Em) (hMon : AsympLE Emi Em) (hCee : Approx Eoi Emi) : AsympLE Eoi ES
```

— the four chain steps enter as **three named real-sequence hypotheses** (`hUM_S` folds steps 1–2, tower-on-$\widehat S$ plus the F1 carry, into a single `Approx`; `hMon` is step 3; `hCee` is step 4). What the kernel certifies is the *composition* of the asymptotic calculus; the tower steps, `expprovind`, the market, and the traders are unmodeled. Per deference-v6 §7: the Lean proves the deference algebra, not the forcing.

The prose proof above is complete given the LI paper's 4.8.4/4.8.10 (status `LI` — black-boxed) and the Mart hypothesis; nothing else is assumed.

## Related

- [[deference-notions]] — Mart, Value, the menus/F1/F2 apparatus, the implication diagram
- [[two-option-value-iff-total-trust]] — the converse direction's first leg (exact, per $(X,s)$)
- [[total-trust-implies-value-telescoping]] — Value from Total Trust *without* the tower (one rung below)
- [[total-trust-implies-mart]] — the reverse route back up to the tower (gap-bets); [[amplifier-counterexample]] — why it once looked hard
- [[value-iff-mart]] — the assembled equivalence and its per-arrow status
- [[expert-conditions]] — what observable/coherent/introspective buy
- [[ledger-decided-tie-breaks]] — F1's third hidden ingredient
- [[reversal-of-difficulty-vs-ddb]] — this direction is DDB's hard one, made free by the single-state expert

*Source: deference-v6 §1.1 (`deference-in-logical-induction-v6.md` L180–196); paper-name annotations from the session extraction `imported-chats/analysis/session-b9e8341b-proof.md`.*
