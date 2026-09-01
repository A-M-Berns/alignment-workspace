# Hostile finite cases

All rows have executable witnesses in tests/test_refinement_models.py.

| # | Case | Result |
| --- | --- | --- |
| 1 | persistent live issue silently drops \(a\to0\) | rejected by identity frame / affected-batch coverage |
| 2 | persistent issue silently changes \(a\to b\) | rejected |
| 3 | in-place exact authenticated translation | accepted as identity-valued generalized Transfer |
| 4 | in-place \(a\vee b\to a\) with disposition of \(b\) | accepted |
| 5 | in-place strengthening plus fresh grounded slice | accepted; old slice remains \(a\) |
| 6 | join-preserving map sends \(b\) to zero | hides strengthening; adequacy fails |
| 7 | same lossy map hides weakening | order reflection fails |
| 8 | map collapses only cosmetic distinctions | globally noninjective, slice-faithful |
| 9 | constant-bottom observation | join-sound and vacuous; equality reflection fails |
| 10 | order-preserving map not order-reflecting | inadequate |
| 11 | faithful map on relevance quotient | accepted |
| 12 | two faithful, quotient-compatible bridges | composition accepted |
| 13 | locally plausible bridges with quotient mismatch | composition rejected |
| 14 | many-era erosion eventually maps relevant \(b\) to zero | caught at first inadequate era |
| 15 | semantic meaning valid, no grounded origin | admission rejected |
| 16 | grounded authorizer, malformed meaning | admission rejected |
| 17 | new fact activates conditional Due under standing rule | admission accepted |
| 18 | evaluator invents convenient slice | admission rejected |
| 19 | Coverage map forgets applicability | adequacy fails |
| 20 | reason map preserves proposition but forgets answer mode | adequacy fails |
| 21 | irrelevant distinctions collapse | demonstrates full injectivity is too strong |
| 22 | lossy order map enables hidden revision | demonstrates order reflection is necessary |

The fixtures use exact finite sets and exhaustive finite powersets. They support
unregistered paper claims and do not register a checker verdict.
