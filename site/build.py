"""`python3 site/build.py [--out DIR] [--check]`: the static site from the map and the repository (rulings S2–S4).

(The prompt's `python3 -m site.build` cannot run: `site` is the name of a standard-library module Python imports at
startup, so a package of that name is shadowed; the generator is a script in the `site/` directory instead.)

Reads graph/index.json (writing it with the plain checker run if absent), graph/derived.json, state/*.json, the registries,
DECISIONS.md, wiki/, graph/policy.yaml, graph/events/*.jsonl, site/lede.md and site/walks/*.md; writes `_site/`. Fails on
an unresolved reference, two ids mapping to one path, a walk step naming no id, or a binding in the lede or a walk that
disagrees with the state. `--check` builds into a temporary directory and prints the counts; it is what the gate runs.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import shutil
import sys
import tempfile
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))   # the generator's own modules; `site` is the standard library's name, so this is a script, not a package
import md, pages
from load import ROOT, BuildError, Repo

SITE = ROOT / "site"
BIND = re.compile(r"<!--bind:([a-z_]+)-->(.*?)<!--/bind-->", re.S)
STEP = re.compile(r"^## (\S+)\s*$", re.M)


def counts(repo: Repo) -> dict:
    results = [x for x, N in repo.nodes.items() if N.get("formal_result") and not N["fields"].get("superseded_by")]
    connected = [x for x in results if any(k == "part" for _, k in repo.parents.get(x, []))]
    prog = repo.nodes.get("the-program")
    return {"nodes": len(repo.nodes), "lines": len(prog["frame"]["roots"]) if prog else 0, "items": len(repo.items),
            "results": len(results), "connected": len(connected), "held": sum(len(N["frame"].get("holds") or []) for N in repo.nodes.values() if N.get("frame")),
            "decisions": len(repo.decisions), "rounds": len(repo.rounds), "wiki_pages": len(repo.wiki),
            "registered": len(repo.registry)}


def check_bindings(text: str, C: dict, where: str) -> str:
    """Every `<!--bind:key-->value<!--/bind-->` must agree with the computed count; returns the text with the markers removed."""
    problems = []

    def sub(m):
        key, val = m.group(1), m.group(2).strip()
        if key not in C:
            problems.append(f"{where}: binding {key!r} names no count the build knows ({', '.join(sorted(C))})")
            return val
        if str(C[key]) != val:
            problems.append(f"{where}: binding {key!r} says {val!r}; the state says {C[key]!r}")
        return str(C[key])
    out = BIND.sub(sub, text)
    if problems:
        raise BuildError("\n".join(problems))
    return out


def parse_walk(text: str) -> dict:
    """A walk: a `# Title` line, an intro up to the first `## <id>` heading, then steps, each `## <id>` with its prose."""
    m = re.search(r"^# (.+)$", text, re.M)
    if not m:
        raise BuildError("a walk begins with a `# Title` line")
    title = m.group(1).strip()
    parts = STEP.split(text)
    intro = parts[0][m.end():].strip()
    steps = [(parts[i].strip(), parts[i + 1].strip()) for i in range(1, len(parts), 2)]
    if not steps:
        raise BuildError(f"walk {title!r} has no `## <id>` step")
    return {"title": title, "intro": intro, "steps": steps}


def walk_page(site: pages.Site, slug: str, walk: dict) -> str:
    r = site.repo
    body = [f"<p class=\"draft-note\">The prose of this walk is the round's draft, marked as such for the maintainers to rewrite; each step shows the live node beside it.</p>",
            f"<div class=\"walk-intro\">{md.render(walk['intro'], pages.wiki_link_resolver(site))}</div>"]
    for i, (ident, prose) in enumerate(walk["steps"], 1):
        if ident not in r.nodes:
            raise BuildError(f"walk {slug!r}, step {i}: {ident!r} names no node")
        N = r.nodes[ident]
        meta = [pages.kind_label(N), "drafted" if r.drafted(ident) else f"{len(r.human_events(ident))} human event(s)"]
        held = r.held_by.get(ident, [])
        roots = r.root_of.get(ident, [])
        side = [f"<p class=\"statement\">{pages.esc(N['statement'].strip())}</p>", f"<p class=\"muted\">{' · '.join(pages.esc(m) for m in meta)}</p>"]
        if roots:
            side.append("<p class=\"muted\">root of " + ", ".join((site.link("n", f) if f != "top" else "the top frame") + f" ({pages.esc(str(role))})" for f, role in roots) + "</p>")
        if held:
            side.append("<p class=\"muted\">held by " + ", ".join(site.link("n", f) for f in held) + "</p>")
        if N.get("frame"):
            Fr = N["frame"]
            side.append(f"<p class=\"muted\">holds {len(Fr.get('holds') or [])} node(s); {len(Fr.get('roots') or [])} root(s)</p>")
        if N.get("formal_result"):
            F = N["formal_result"]
            side.append(f"<p class=\"muted\">formal result; hypotheses {'unread' if F.get('hypotheses') == 'unread' else str(len(F.get('hypotheses') or [])) + ' read'}; registry id <code>{pages.esc(str(F.get('registry_id')))}</code></p>")
        if ident in r.item_of_node:
            side.append(f"<p class=\"muted\">item {site.link('items', r.item_of_node[ident])}, {pages.esc(str(N['fields'].get('item_status', 'open')))}</p>")
        body.append(f"<section class=\"step\"><div class=\"step-prose\"><span class=\"step-no\">{i}</span>{md.render(prose, pages.wiki_link_resolver(site))}</div>"
                    f"<aside class=\"step-node{' drafted' if r.drafted(ident) else ''}\"><h3>{site.link('n', ident)}</h3>{''.join(side)}</aside></section>")
    return pages.layout(site, walk["title"], "\n".join(body), [("walks", "/walks/")], "a guided walk")


def build(out: pathlib.Path, verbose: bool = True) -> dict:
    t0 = time.perf_counter()
    repo = Repo()
    site = pages.Site(repo)
    C = counts(repo)
    written: dict[str, int] = {}

    def put(path: str, content: str, kind: str) -> None:
        p = out / path.lstrip("/")
        if path.endswith("/"):
            p = p / "index.html"
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content)
        written[kind] = written.get(kind, 0) + 1

    # the lede and the walks (the only hand-written prose), binding-checked
    lede_src = (SITE / "lede.md").read_text() if (SITE / "lede.md").is_file() else ""
    if not lede_src.strip():
        raise BuildError("site/lede.md is missing or empty: the front page's one paragraph is required")
    lede_html = md.render(check_bindings(lede_src, C, "site/lede.md"), pages.wiki_link_resolver(site))
    walks = []
    for wp in sorted((SITE / "walks").glob("*.md")):
        w = parse_walk(check_bindings(wp.read_text(), C, wp.name))
        walks.append((wp.stem, w))
    if not walks:
        raise BuildError("site/walks/ holds no walk; the build needs at least one")
    for slug, w in walks:
        put(site.url("walks", slug, must_exist=False), walk_page(site, slug, w), "walk")
    put("/walks/", pages.index_list_page(site, "Walks", [f"<li><a href=\"/walks/{pages.esc(s)}/\">{pages.esc(w['title'])}</a></li>" for s, w in walks]), "listing")
    # nodes
    for x in repo.nodes:
        put(site.url("n", x), pages.node_page(site, x), "node")
    # items
    for num in sorted(repo.items, key=lambda s: (not s.isdigit(), int(s) if s.isdigit() else 0, s)):
        put(site.url("items", num), pages.item_page(site, num), "item")
    put("/items/", pages.index_list_page(site, "Items", [f"<li>{site.link('items', n, f'{n}. ' + str(repo.nodes[rec['node']]['fields'].get('title', '')))} <span class=\"muted\">{pages.esc(str(repo.nodes[rec['node']]['fields'].get('item_status', '')))}</span></li>"
                                                        for n, rec in sorted(repo.items.items(), key=lambda kv: (not kv[0].isdigit(), int(kv[0]) if kv[0].isdigit() else 0, kv[0]))],
                                           "The priority items, each a node of the map; PRIORITIES.md is rendered from them."), "listing")
    # decisions
    for a in repo.decisions:
        put(site.url("decisions", a), pages.decision_page(site, a), "decision")
    put("/decisions/", pages.index_list_page(site, "Decisions", [f"<li><span class=\"date\">{pages.esc(d['date'] or 'queued')}</span> {site.link('decisions', a, d['title'])} <span class=\"muted\">{pages.esc(d['status'])}</span></li>"
                                                               for a, d in sorted(repo.decisions.items(), key=lambda kv: (kv[1]['date'] or '9999', kv[0]), reverse=True)],
                                               "Every entry of DECISIONS.md by its anchor; the prose is the file's, verbatim."), "listing")
    # rounds
    for rid in repo.rounds:
        put(site.url("rounds", rid), pages.round_page(site, rid), "round")
    put("/rounds/", pages.index_list_page(site, "Rounds", [f"<li><span class=\"date\">{pages.esc(str(R.get('date')))}</span> {site.link('rounds', rid)} <span class=\"muted\">{pages.esc(str(R.get('project') or 'workspace'))}</span></li>"
                                                         for rid, R in sorted(repo.rounds.items(), key=lambda kv: str(kv[1].get('date')), reverse=True)]), "listing")
    # wiki
    for name in repo.wiki:
        put(site.url("wiki", name), pages.wiki_page(site, name), "wiki")
    put("/wiki/", pages.index_list_page(site, "Wiki", [f"<li>{site.link('wiki', n, n.replace('-', ' '))}</li>" for n in repo.wiki]), "listing")
    # handles
    for h in repo.handles:
        put(site.url("by", h.lstrip("@")), pages.handle_page(site, h.lstrip("@")), "handle")
    put("/by/", pages.index_list_page(site, "Handles", [f"<li>{site.link('by', h.lstrip('@'), h)} <span class=\"muted\">{pages.esc((spec or {}).get('kind', ''))}</span></li>" for h, spec in repo.handles.items()]), "listing")
    # claims: a redirect to the node the record belongs to
    for cid, e in repo.registry.items():
        target = repo.claims.get(cid)
        if target is None:
            # a superseded entry resolves to its alias node where one exists
            alias = [x for x, N in repo.nodes.items() if (N.get("formal_result") or {}).get("registry_id") == cid]
            target = alias[0] if alias else None
        if target is None:
            site.unresolved.append(f"claim:{cid} (no node carries its record)")
            continue
        u = site.url("n", target)
        put(site.url("claims", cid), f"<!doctype html><meta charset=\"utf-8\"><meta http-equiv=\"refresh\" content=\"0; url={u}\"><title>{pages.esc(cid)}</title><p>{pages.esc(cid)} → <a href=\"{u}\">{pages.esc(target)}</a></p>", "claim-redirect")
    # feed, spine, ranking, search, front
    rows = pages.feed_rows(site)
    put("/feed/", pages.feed_page(site, rows), "feed")
    put("/spine/", pages.spine_page(site), "spine")
    put("/ranking/", pages.ranking_page(site), "ranking")
    put("/search/", pages.search_page(site), "search")
    put("/search/index.json", json.dumps(pages.search_index(site), ensure_ascii=False), "search-index")
    put("/", pages.front_page(site, lede_html, [(s, w["title"]) for s, w in walks], rows), "front")
    # assets
    (out / "assets").mkdir(parents=True, exist_ok=True)
    for asset in (SITE / "assets").glob("*"):
        shutil.copy(asset, out / "assets" / asset.name)
    if (SITE / "CNAME").is_file():
        shutil.copy(SITE / "CNAME", out / "CNAME")
    (out / ".nojekyll").write_text("")
    if site.unresolved:
        raise BuildError("unresolved reference(s):\n  " + "\n  ".join(sorted(set(site.unresolved))))
    elapsed = time.perf_counter() - t0
    summary = {"pages": written, "counts": C, "paths": len(site.paths), "unresolved": 0, "seconds": round(elapsed, 2), "commit": repo.commit}
    if verbose:
        print("SITE BUILD:", json.dumps(summary, sort_keys=True))
    return summary


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(prog="python3 -m site.build")
    ap.add_argument("--out", default=str(ROOT / "_site"))
    ap.add_argument("--check", action="store_true", help="build into a temporary directory and report; write nothing under the repository")
    a = ap.parse_args(argv)
    try:
        if a.check:
            with tempfile.TemporaryDirectory() as d:
                build(pathlib.Path(d))
        else:
            out = pathlib.Path(a.out)
            if out.exists():
                shutil.rmtree(out)
            build(out)
    except BuildError as e:
        print(f"SITE BUILD FAILED: {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
