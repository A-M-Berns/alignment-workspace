# FA-chat intermediate working documents — recovery needed

**Status note (2026-07-29):** two *other* documents from this same chat have since arrived, by hand-copying the rendered artifact panel in the claude.ai UI — `../fa-positive-results-corrected-v3.md` (msg 41) and `../fa-block-staleness-impossibility.md` (msg 47). That route works and is the recommended one for the seven below; it does not discharge the task, since these are different documents. See `../index.md` § "Chat-authored documents".

During the faithful-acceleration adjudication chat (`../2026-07-01__checking-faithful-acceleration-result__a6632d0f.md`), Claude authored seven working documents via file-creation tool calls:

| file | created | revised | contents |
|---|---|---|---|
| `fa-scope-adjudication-plan.md` | msg 6 | msgs 12, 19, 21, 23 | 6-step adjudication plan, Q1–Q5, verdict criteria A1/A2/B/C |
| `fa-claim-counterclaim-explainer.md` | msg 8 | msg 12 | claim/counterclaim anatomy (L1/L2/L3), χ-vs-g_n |
| `fa-ladder-check.md` | msg 16 | — | Prop A, Prop B, witnesses W1–W7, strength-ladder correction |
| `fa-step2-verbatim.md` | msg 18 | — | verbatim LI theorem families, the 4.8.15/4.8.16 erratum, tower-sparse legality |
| `fa-step3-construction.md` | msg 21 | — | g_n construction, C4 (wrong-χ-comparator), C6 (pre-decision timing) |
| `fa-step4-resolution.md` | msg 23 | — | reductio, Forcing Theorem A, Lemma B, Theorem C, v6 consequences, citation-vs-posit fork |
| `fa-catchup.md` | msg 25 | — | self-contained consolidation of the adjudication |

**They are not here because they could not be extracted**: the markdown chat export renders every `create_file` / `str_replace` call as a parameterless placeholder (`*[tool call: create_file]*`) with no document body — verified at all seven creation sites and all revision sites. The bodies appear nowhere else in this collection.

**To recover them** (human action needed):
1. Easiest: open the chat in the claude.ai UI and download the seven artifacts from the conversation's file outputs, placing them in this directory; or
2. re-render the raw claude.ai export with tool-input rendering enabled, if the export format preserves tool inputs at all.

Until then: their **substance** is preserved in the chat's visible prose/discussion and is summarized (with a carry-over map of what did and didn't reach the `fa-positive-*-corrected` files) in `../analysis/delta-report.md` §3. The wiki pages under `wiki/` were written from the transcript's visible content.
