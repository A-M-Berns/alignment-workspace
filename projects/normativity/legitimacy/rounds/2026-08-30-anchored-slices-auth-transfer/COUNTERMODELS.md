# Hostile finite cases

The executable witness for every row is in \`tests/test_slice_models.py\`.
\(a,b\) are exact semantic tokens; joins are finite set union unless the row
uses the nondistributive \(M_3\) fixture.

| # | Case | Accounting | Authentication / slice result |
| --- | --- | --- | --- |
| 1 | matter gets criticism \(b\) at time 20 | old \(a\) invariant unchanged | admit fresh slice \(b@20\) |
| 2 | new \(a\vee b\) called translation of \(a\) | claimed equation can pass after relabeling | fails anchored denotation; \(b\) needs a birth |
| 3 | \(a\vee b\) weakened to \(a\) | fails unless \(b\) is a terminal term | valid only with authorized disposition of \(b\) |
| 4 | \(a\) strengthened to \(a\vee b\) | successor join can be stated | valid only when \(b\) is a fresh authenticated slice |
| 5 | \(x:a\) renamed \(y:a\) | passes | exact authenticated translation |
| 6 | \(a\vee b\) split into children \(a,b\) | collective join passes | joint authentication passes |
| 7 | parents \(a,b\) merged into child \(a\vee b\) | parent-indexed join passes | each inherited denotation preserved |
| 8 | first checker reads intermediate \(y=a\), second \(y=b\) | both local equations look valid | composition rejected: no common interpretation |
| 9 | successor labeled \(a\) but actually means \(b\) | passes supplied-label accounting | semantic authentication fails |
| 10 | Coverage target unchanged, applicability \(A+B\) reduced to \(A\) | old label can be copied | fails; dropped applicability needs disposition |
| 11 | Coverage applicability unchanged, target \(T\) changed to \(U\) | old label can be copied | fails target authentication |
| 12 | reason content retained, answer mode changed to ignore | token accounting can pass | fails answer-mode authentication |
| 13 | reason answerability preserved but comparison margin lost | Transfer passes | insufficient for Progress comparability |
| 14 | red/rouge ontologies both map to anchored risk | local labels differ | commuting transport authenticates |
| 15 | new ontology maps rouge to reward | local rename looks plausible | no commuting transport; rejected |
| 16 | external fact satisfies anchored obsolescence rule | removed content is explicit terminal term | authorized disposition passes |
| 17 | evaluator calls unchanged facts obsolete | removed content is unaccounted | rejected as neither fact nor disposition |
| 18 | slice \(b\) accrues on an already split frontier | prior split still accounts for \(a\) | independent \(b@20\) invariant starts |
| 19 | one issue merges matters \(m_1,m_2\), then \(m_1\) accrues \(c\) | loads share occurrence | matter-and-slice indices keep anchors distinct |
| 20 | early-\(b\) and late-\(b\) histories have same final growing anchor | final \(a\vee b\) values coincide | birth indices distinguish inherited histories |

## Additional algebraic discriminator

The \(M_3\) fixture demonstrates that the accounting consumer uses finite join
without distributivity. A relational obligation is represented as the single
element \`answer-a-in-light-of-b\`; the theorem does not force an atomic
decomposition.

The cases collectively show that slice indexing adds provenance, while
authentication adds meaning. Neither can be recovered from accounting alone.
