# Research directory map (planning-phase briefing)

*Provenance: produced 2026-07-21 by an exploration subagent during planning of the li-deference wiki. A structured map of the project folder for the reorganization. Line numbers refer to files as of 2026-07-20.*

## v6 (`deference-in-logical-induction-v6.md`, 152KB) — current integrated spine

Two-part structure: §0–§2 abstract single-process/general-expert theory (novice LI H deferring to any observable, coherent expert E*); §3 the hinge (when is the tower forced — arbitrage + complexity gap C_H ⊊ C_A); §4–§5 cross-process setting (distinct stronger inductor A): negative backbone (§4) + two positive constructions (§5): frozen/sealed-sibling (§5.1–5.8) and faithful acceleration (§5.9–5.11). §6 alignment reading; §7 Lean status; §8 open problems. Notation: H⊣C_H (canonically P), A⊣C_A (canonically EXP); a_n := E^A_n(⌜Y_n⌝); lookahead F(n)/f(n) ~ 2^n; schedules e(n) < F(n) < σ(n); ≈_n (difference → 0), ≳_n (liminf ≥ 0).

### Heading outline (line numbers)

- L24 Summary (12 headline claims)
- L45 §0 Setting: 0.1 motivation L47; 0.2 shared world L55; 0.3 the human + free tools L66; 0.4 the AI, schedules, deference relation L86; 0.5 DDB in a page L121; 0.6 dictionary/Savage framing L131
- L155 §1 Deference between processes is the tower property: 1.1 Mart⟹Value L180; 1.2 Value⟹Total Trust (witness, exact) L198; 1.3 reversal of difficulty L213; 1.4 what remains: the tower L222; 1.5 universal tower contains conditional form (the fold) L226; 1.6 Total Trust and the soft⇒hard squeeze L232 (amplifier at L245)
- L293 §2 What the expert must be: 2.1 coherent single state cheap, frame dear L295; 2.2 modest but coherent ⟹ infinite process L312; 2.3 Weatherson ↔ LI scope conditions L320; 2.4 realizability payoff L331
- L361 §3 When is the tower forced: 3.1 direct trader / Value gap = arbitrage L365; 3.2 self-case free L374; 3.3 hinge: complexity gap L389; 3.4 governing question L397
- L425 §4 Across processes, negatively: 4.1 No-Forced-Trust L427; 4.2 natural model: self-trust through a mirror L437; 4.3 it dies twice L449 (2a anti-inductive settlement L451; 2b cost-circularity L461); 4.4 dichotomy: predictable iff uninfluenced L477; 4.5 what survives anyway L485 (externalized self-trust, Non-Dogmatism, refuted sub-attempt L498); 4.6 substrate L500; 4.7 structural findings L504; 4.8 the tower itself is dead L540
- L548 §5 Across processes, positively: 5.1 sealed sibling L554; 5.2 construction L560; 5.3 three fragments L573; 5.4 faithfulness forced L580; 5.5 soundness on G only L586; 5.6 dichotomy and ceiling L598; 5.7 Target-Soundness and the seam L604; 5.8 two-channel refinement / safety L620; 5.9 faithful acceleration L683 (theorem L693); 5.10 admissible domain, not syntactic L697; 5.11 where Value sits: trichotomy L714 (table L720)
- L732 §6 Meaning: 6.1–6.7 (manipulation boundary 6.3 L753; corrigibility 6.4 L762; legitimacy program 6.5 L768; idealization/scope 6.6 L772; averaged-form caveats 6.7 L781)
- L794 §7 Machine-check; L818 §8 open problems; L838 v4→v5 map; L861 v5→v6 changes; L875 Provenance/References (FA notes cited L883–886; Anson chats credited L877–888); L901 Appendix A Lean ledger; L905 Appendix B vetting ledger (status codes P/C/S/T/Pr/LI/O — ready-made per-claim status source)

### Result inventory (with status)

Deference notions (§0.5, §1): **Mart/tower** E^H_n(X) ≈_n E^H_n(⌜E*(X)⌝); **fold/conditional tower** (same with observable weight, §1.5); **Total Trust** E^H_n(X | E*(X) ≥ t) ≳_n t; **Value** (weakly prefer letting E* pick from any menu); **Reflection** (condition on [P=ρ]; too strong, incompatible with modesty).

Abstract tier: Mart⟹Value (§1.1, proved, Lean `value_argmax_asymptotic`; uses only novice loe/expprovind + tower hyp). Value⟺Total Trust per (X,s) (§1.2 witness identity, exact, Lean `value_iff_totalTrust`; NOTE: witness-menu Value). Reversal of difficulty (§1.3, interpretation). Value⟺Mart (§1.4: forward proved; reverse squeeze prose). Fold (§1.5, proved, introspective expert). Soft⇒hard squeeze fails as one-liner (§1.6): **amplifier** g(e) = (1+2c)e − c passes every threshold cut, killed only by boundedness at endpoints; general squeeze remains prose. §2.1 coherent state cheap/frame dear (sympy + Lean fiber core). §2.2 modest+coherent ⟹ infinite frame (hard tail `CM_implies_immodest` proved; soft⇒hard reduction prose). §2.3 Weatherson ↔ scope conditions (interpretation).

Forcing (§3): Value gap = pure arbitrage (proved arithmetically; needs novice able to trade in expert's market). Self-case free (§3.2: every hypothesis an LI theorem — cee/ccee/epr/er). Hinge (§3.3): novice can't arbitrage A (a_n is C_A-hard); A can arbitrage novice ⟹ forcing means A predicts the novice; satisfiable only because P ⊊ EXP and target blind to A's output. Lean: `blind_cost_realizable` vs `cost_circularity`.

Negative backbone (§4): No-Forced-Trust (§4.1, prose meta-theorem). 2a anti-inductive settlement (§4.3): ρ(a) = 1[a ≤ ½] gives inf_a |a − ρ(a)| = ½; on diagonal g_n ↔ (R_n ≤ ½), liminf ‖a_n − Y_n‖ ≥ ½ — kills universal pointwise tracking, compute-independent (Lean `no_exact_quote`, `tracking_fails`). 2b cost-circularity (§4.3): timely tracking needs C_A ∋ R∘F: regress arithmetic proved; timely-cost step a "soft joint" (~75–80%). Dichotomy predictable-iff-uninfluenced (§4.4, propositional only, never instantiated). Externalized self-trust (§4.5, proved modulo named Tracking hyp). Non-Dogmatism confines manipulation (§4.5, proved). Refuted sub-attempt at L498 (flagged wrong: monotonicity reversal/category error). §4.8 tower death: Mart(H→A) reduces to tracking (read-off + cee) so inherits 2a/2b (Lean `tower_imp_tracking`); "both faces die together" on the diagonal is prose — **and is FALSE on the diagonal per the FA chat (see delta-report.md D16)**.

Positive construction 1 — frozen/sealed sibling (§5.1–5.8): target Y_n := H^[n]_{F(n)}(P^(n)) (novice's own deliberation with A's current quote held out; blindness forces a family). T1 Faithful Tracking a_n − Y_n ≈_n 0 (every fragment; Lean is a squeeze over hyps ≡ conclusion). T2 earned meta-trust (composition via expprovind). T3 conditional tower ccee(H⁺→A) on timely fragment G, provable in H⁺'s own logic. T4 Value on G (converse forces T3). T5 object-level ceiling (pointwise deference false; = tracking_fails). T6 calibration curve on G. T7 limit prices: on-G proved; off-G "nondegenerate interval" is a two-points stub (oversold name). Target-Soundness: theorem on G, provably fails off G (the seam). Safety/silence (§5.8): stub (0·ε=0)/Archimedean.

Positive construction 2 — faithful acceleration (§5.9–5.11): target Y_n := E^H_{f(n)}(X) (unfrozen coupled human's future credence); "defer to credences, not truth." Ingredients: (I) self-trust cee; (II) calibration = Expectation Unbiasedness From Feedback 4.8.16. Theorem (L693): violation weight w_n = Ind_δ(a_n>t)·Ind_δ(E^H_n(X)<t−ε) has ∑ w_n < ∞ ⟹ gate-weighted average ≥ t−ε−δ and classwise Value via §1.2 witness. Lean `FaithfulAcceleration.lean` (arithmetic chain; hbias/hbdd named not proved). §5.10 admissible domain (benign price-liar χ vs fatal quote-diagonal g_n; can't be syntactic — PA rebuilds g_n; three causal/provenance framings; deepest open item). §5.11 domain-relative Value; trichotomy L720: unfrozen+pointwise impossible; unfrozen+averaged forced on admissible domain; sealed+pointwise forced on G. **All of §5.9–5.11 is superseded in part by the FA chat corrections — see delta-report.md.**

§6: faithfulness forced everywhere, soundness only on G; manipulation boundary §6.3 (whispering earring — steering and faithful prediction produce the same vanishing a_n − Y_n); corrigibility §6.4 (no fully-updated-deference problem); legitimacy program §6.5 (not formalized); §6.6 fixed-option idealization, outer-alignment/asymptotic only; §6.7 single-round "one big lie" + good-feedback-only reach.

§7 honesty caveat (propagate everywhere): **the Lean proves the deference algebra, not the forcing** — T1/T3 squeezes over hypotheses that restate the conclusion; market/traders unmodeled. Five modules + check.py, ≈129 results, sorry-free. Appendix B (L905) per-claim vetting ledger.

## The FA cluster (see delta-report.md for corrections)

Generation A (Jul 13, superseded, absorbed into v6 §5.9–5.11): `faithful-acceleration.md` (261 L; the boxed all-days ∑w_n < ∞ over ALL sentences — over-claims; §5 ladder wrong per D10; L138 tolerance example false per D11; L171 false). `faithful-acceleration-scope.md` (124 L; admissible-domain adjudication; its §4 gate argument has the step-3 hole; source of v6 §5.10). `pointwise-tower-and-faithful-acceleration.md` (210 L; trichotomy synthesis; §0 still says "all sentences").

Generation B (chat products, mtime Jul 20): `fa-positive-result-corrected.md` (v1), `fa-positive-results-corrected-v2.md`, `fa-positive-results-corrected-v3.md`. v1/v2 contain retracted architecture (D6); v3 is current-best but pre-msgs-42-43. v3: Thm 1 (window-disjoint schedules d_{k+1} ≥ 2^{d_k}, ~0.85), Thm 2 (adaptive one-position trader, w_n → 0 all days, ~0.75), Cor 2 per-day dominance, Cor 3 all-days sum; assumptions A1 joint clearing (load-bearing), A4 expressibility; §6 self-referential family (per-X true-and-empty; family quotes pin to ½).

`li-deference.md` (311 L, Abram's own hand, motivation + formalism + "Translating Total Trust" drafting section L137–309; several stub sections). Cited as source by v6, legitimacy-theory-v1, FA notes.

## Other files

- `legitimacy-theory-v1.md` (169 L, Fable 5, 2026-07-05): legitimacy = endpoint-preservation ("catalyst not reagent"); influence defect d_n; legitimacy cannot be a trace condition (run-3 trace-nonrecoverability), mirroring §5.10's "not syntactic." Built on v6 as spine.
- `anson-notes/`: four source notes v6 integrates (`no-timely-pointwise-tower.md` → §4.8; `self-referential-settlement-target.md` → §4.2–4.5; `frozen-deliberation-deference-v6.md` → §5.1–5.8; `trust-between-inductors-summary-v2.md`) + `INDEX.md` cataloguing the 11 Anson chats (2026-05-20 → 06-20) with claude.ai URLs — **already integrated**.
- `lean-deference/`: five modules + `AUDIT.md` (statement-level adversarial audit driving v6 §7's honesty caveat).
- `deference-trust-lab/`: exploration lab (v6 §6.7/§8 cite for red-team caveats). NOTE `run3/questions/scout-acceleration.md` (2026-07-01) independently found the gate-hole and ladder defects but proposed the "patient hard gates are legal" repair that the FA chat later overturned (msg 18).
- `internal-fixpoint/`: unrelated (reflective oracles). `udt-representation-theorem/`: separate project. `references/`: DDB, Weatherson, LI paper sources (`references/logical-induction/main.tex`).
- the task queue L208–216: "Characterize inter-inductor Total Trust" — the open problem behind v6 §3.4.

## Reconciliation flags for the wiki

1. The scope question has two answers in the corpus: v6 §5.10/scope-note "admissible domain (exclude diagonal; not syntactic)" vs the FA chat/corrected files "no domain restriction; the diagonal is a degenerate stratum (quote pinned at ½, Paradox-Resistance regime)." Compatible in spirit, framed oppositely; the chat's resolution is current-best, with the (II) citation-vs-posit fork (delta D17) explicitly reserved for Abram.
2. v6 Appendix B + lean-deference/AUDIT.md are the ready-made per-claim status sources; propagate the "Lean proves the algebra, not the forcing" caveat everywhere.
