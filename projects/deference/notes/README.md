# Notes — deference

The deference line's living documents. Specification layer: maintainer-owned, and
a proof-layer pull request may not touch them.

| document | what it is authoritative for |
|---|---|
| `CORRIGIBILITY_ROADMAP.md` | current architecture and execution planning |
| `CORRIGIBILITY_PAPER_LEDGER.md` | human-readable research status |
| `DISPATCH_QUEUE.md` | what is dispatched, waiting, or not yet dispatchable |
| `FINITE_MODEL_SKELETON.md` | the frozen finite specification object a round's finite tracks bind to |
| `TERMS.md` | what the line's vocabulary currently means, and which document owns each meaning |

**Precedence.** If the roadmap and the ledger disagree about whether something has
been established, the ledger wins. If any prose here and `../CLAIMS.md` disagree
about what has been established inside this repository, the registry wins. Prose is
documentation of the record; the registry entry is what a claim is. `TERMS.md`
records meanings and never sets them: where it and an owning document disagree,
the owning document wins.

The skeleton is frozen per round and versioned. A revision is a new version number
recorded in the document, with every track that consumed the previous version rerun
or explicitly reconciled — otherwise results that appear to compose do not.

The note dumps recording this line's starting point sit beside this directory, each
with its own `ORIGIN.md`. Reference them by path; they are not copied here.
