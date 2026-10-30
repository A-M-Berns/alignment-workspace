"""The pages, each a function from the repository to HTML. Structure and human events only; the ranking's numbers
appear on `/ranking/` and in a collapsed section of a node page, nowhere else."""
from __future__ import annotations

import html
import json
import re

import md
from load import Repo, BuildError, last_changed

esc = md.esc
REF = re.compile(r"<!--ref:(claim|item|item-open|round|node):([^<>\s]+)-->")
STATE = re.compile(r"<!--state:[^>]*-->(.*?)<!--/state-->", re.S)
WIKI_MD_LINK = re.compile(r"\]\(([A-Za-z0-9][A-Za-z0-9-]*)\)")


class Site:
    """The path registry: one id, one URL (ruling S4). `url` registers and returns; `check` refuses collisions."""

    def __init__(self, repo: Repo):
        self.repo = repo
        self.paths: dict[str, tuple[str, str]] = {}       # path -> (kind, id)
        self.unresolved: list[str] = []

    @staticmethod
    def seg(s: str) -> str:
        return str(s).replace("/", "--")

    def url(self, kind: str, ident: str, must_exist: bool = True) -> str:
        r = self.repo
        ok = {"n": ident in r.nodes, "items": ident in r.items, "decisions": ident in r.decisions, "rounds": ident in r.rounds,
              "claims": ident in r.registry, "wiki": ident in r.wiki, "by": ("@" + ident) in r.handles, "prs": ident in r.prs,
              "concepts": ident in r.concepts}[kind]
        if not ok and must_exist:
            self.unresolved.append(f"{kind}:{ident}")
        path = f"/{kind}/{self.seg(ident)}/"
        prev = self.paths.get(path)
        if prev and prev != (kind, ident):
            raise BuildError(f"two ids map to one path {path}: {prev[1]!r} and {ident!r}")
        self.paths[path] = (kind, ident)
        return path

    def repo_root(self):
        from load import ROOT
        return ROOT

    def link(self, kind: str, ident: str, label: str | None = None, cls: str = "") -> str:
        u = self.url(kind, ident)
        c = f' class="{cls}"' if cls else ""
        return f'<a href="{u}"{c}>{esc(label if label is not None else ident)}</a>'


def layout(site: Site, title: str, body: str, crumbs: list[tuple[str, str]] | None = None, subtitle: str = "") -> str:
    r = site.repo
    nav = '<a href="/">map</a>'
    crumb_html = ""
    if crumbs:
        crumb_html = '<nav class="crumbs">' + " › ".join(f'<a href="{u}">{esc(t)}</a>' for t, u in crumbs) + "</nav>"
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(title)}</title><link rel="stylesheet" href="/assets/style.css"><script defer src="/assets/app.js"></script></head>
<body><header class="top"><a class="home" href="/">alignment-workspace</a><nav class="main">{nav}</nav>
<form class="search" action="/search/" method="get"><input type="search" name="q" placeholder="search ids, statements, titles" aria-label="search"></form></header>
<main>{crumb_html}<h1>{esc(title)}</h1>{f'<p class="subtitle">{subtitle}</p>' if subtitle else ''}
{body}
</main><footer>Built from commit <code>{esc(r.commit[:12])}</code> ({esc(r.commit_date)}) by <code>python3 -m site.build</code>; a render of the repository, never a second source. Structure and human events only; the ranking is a lens, shown on <a href="/ranking/">/ranking/</a>.</footer>
</body></html>"""


def owners_html(site: Site, owners: list[str]) -> str:
    out = []
    for h in owners:
        spec = site.repo.handles.get(h) or {}
        gh = spec.get("github")
        label = f"{h} (GitHub {gh})" if gh else h
        out.append(site.link("by", h.lstrip("@"), label))
    return ", ".join(out) or "—"


def kind_label(N: dict) -> str:
    return N["kind"] + (f"/{N['leaf_kind']}" if N.get("leaf_kind") else "")


def node_card(site: Site, x: str, note: str = "") -> str:
    r = site.repo
    N = r.nodes[x]
    cls = "card drafted" if r.drafted(x) else "card"
    tag = '<span class="tag">drafted</span>' if r.drafted(x) else '<span class="tag human">human-touched</span>'
    st = esc(N["statement"].strip().replace("\n", " "))
    return (f'<div class="{cls}"><div class="card-head">{site.link("n", x)} <span class="kind">{esc(kind_label(N))}</span> {tag}'
            + (f' <span class="note">{esc(note)}</span>' if note else "") + f'</div><p>{st}</p></div>')


def wiki_link_resolver(site: Site):
    def resolve(page: str):
        p = page.replace(" ", "-")
        return site.url("wiki", p) if p in site.repo.wiki else None
    return resolve


def render_wiki(site: Site, name: str) -> str:
    """The wiki source with its references resolved to links carrying the target's live class or status."""
    r = site.repo
    text = r.wiki[name]
    text = STATE.sub(lambda m: m.group(1), text)

    def ref(m):
        kind, ident = m.group(1), m.group(2)
        if kind == "claim":
            e = r.registry.get(ident)
            if not e:
                site.unresolved.append(f"wiki:{name}:claim:{ident}")
                return ""
            return f' <a class="ref claim" href="{site.url("claims", ident)}">[{esc(e.get("class", "?"))}, {esc(e.get("status", "?"))}]</a>'
        if kind in ("item", "item-open"):
            if ident not in r.items:
                site.unresolved.append(f"wiki:{name}:item:{ident}")
                return ""
            st = r.nodes[r.items[ident]["node"]]["fields"].get("item_status", "open")
            return f' <a class="ref item" href="{site.url("items", ident)}">[item {esc(ident)}, {esc(st)}]</a>'
        if kind == "round":
            if ident not in r.rounds:
                site.unresolved.append(f"wiki:{name}:round:{ident}")
                return ""
            return f' <a class="ref round" href="{site.url("rounds", ident)}">[round]</a>'
        if kind == "node":
            if ident not in r.nodes:
                site.unresolved.append(f"wiki:{name}:node:{ident}")
                return ""
            return f' <a class="ref node" href="{site.url("n", ident)}">[node]</a>'
        return ""
    text = REF.sub(ref, text)
    # relative wiki links `[Text](Page)` become site links where the page exists
    text = WIKI_MD_LINK.sub(lambda m: f"]({site.url('wiki', m.group(1))})" if m.group(1) in r.wiki else m.group(0), text)
    return md.render(text, wiki_link_resolver(site), heading_shift=1)


def events_html(site: Site, events: list) -> str:
    if not events:
        return "<p class=\"muted\">No human event has touched this node.</p>"
    rows = []
    for e in sorted(events, key=lambda e: (str(e.get("date")), str(e.get("id")))):
        rows.append(f"<li><code>{esc(str(e.get('id')))}</code> {esc(str(e.get('kind')))} by {site.link('by', str(e.get('by')).lstrip('@'), str(e.get('by')))} on {esc(str(e.get('date')))}"
                    + (f": {esc(str(e.get('gloss') or e.get('reason') or ''))}" if (e.get('gloss') or e.get('reason')) else "") + "</li>")
    return "<ul class=\"events\">" + "".join(rows) + "</ul>"


def work_html(site: Site, work: list) -> str:
    r = site.repo
    out = []
    for w in work or []:
        k, ref = w.get("kind"), str(w.get("ref"))
        if k == "priorities":
            out.append(f"item {site.link('items', ref)}" if ref in r.items else f"item {esc(ref)} (no node)")
        elif k == "round":
            rid = ref.rstrip("/").split("/")[-1] if ref.rstrip("/").split("/")[-1] in r.rounds else None
            if rid is None:
                for cand in r.rounds.values():
                    if cand.get("path") == ref.rstrip("/"):
                        rid = cand["id"]
            out.append(f"round {site.link('rounds', rid)}" if rid else f"round <code>{esc(ref)}</code>")
        elif k == "decision":
            out.append(f"decision {site.link('decisions', ref, r.decisions[ref]['title'] if ref in r.decisions else ref)}")
        elif k == "foundation":
            f = r.foundations.get(ref)
            out.append(f"foundation <code>{esc(ref)}</code>" + (f" ({esc(f.get('path', ''))})" if f else ""))
        elif k == "open":
            out.append(f"open declaration <code>{esc(ref)}</code>")
        else:
            out.append(f"{esc(str(k))} <code>{esc(ref)}</code>")
    return ("<ul>" + "".join(f"<li>{o}</li>" for o in out) + "</ul>") if out else ""


def bridge_card(site: Site, x: str) -> str:
    """The formal result's card: the informal claim it is a conjunct of, the declaration, the bridge, the hypotheses, the
    registry class and status, and the improvement claim's routes beneath as what remains."""
    r = site.repo
    N = r.nodes[x]
    F = N["formal_result"]
    rec = r.nodes[F["record"]]
    entry = r.record_entry(x)
    claims = [p for p, kind in r.parents.get(x, []) if kind == "part" and r.nodes[p]["kind"] == "and" and not r.nodes[p].get("formal_result")]
    parts = ['<section class="bridge-card">', "<h2>Bridge card</h2>"]
    if claims:
        parts.append("<p class=\"claim-top\">A conjunct of the informal claim " + ", ".join(site.link("n", c) + f": <em>{esc(r.nodes[c]['statement'].strip())}</em>" for c in claims) + "</p>")
    else:
        parts.append("<p class=\"claim-top muted\">Connected to no informal claim yet: held by " + (", ".join(site.link("n", f) for f in r.held_by.get(x, [])) or "no frame") + ".</p>")
    decl = rec["fields"].get("statement_of_record")
    lp = r.lean_path(decl) if decl else None
    gh = f"https://github.com/A-M-Berns/alignment-workspace/blob/{r.commit}/{lp}" if lp and r.commit != "uncommitted" else None
    parts.append(f"<p><strong>Declaration</strong> <code>{esc(str(decl))}</code>" + (f' in <a href="{gh}">{esc(lp)}</a>' if gh else (f" in <code>{esc(lp)}</code>" if lp else "")) + f" (record {site.link('n', F['record'])})</p>")
    if entry:
        parts.append(f"<p><strong>Registry</strong> {site.link('claims', entry['id'])}: class <code>{esc(entry.get('class', ''))}</code>, status <code>{esc(entry.get('status', ''))}</code>, "
                     f"review {esc((entry.get('provenance') or {}).get('review_status', '?'))}, origin round {site.link('rounds', entry['origin_round']) if entry.get('origin_round') in r.rounds else esc(str(entry.get('origin_round')))}"
                     + (f"; bears on item {site.link('items', str(entry['answers_item']))}" if str(entry.get('answers_item')) in r.items else "") + "</p>")
    bridges = [c for c in N["children"] if r.nodes[c].get("leaf_kind") == "bridge"]
    for b in bridges:
        B = r.nodes[b]
        parts.append(f"<div class=\"bridge\"><strong>Bridge</strong> ({esc(B['fields'].get('attribution', ''))}; {site.link('n', b)}"
                     + (", drafted" if r.drafted(b) else ", human-touched") + f"):<p>{esc(B['statement'].strip())}</p></div>")
    hyps = F.get("hypotheses")
    if hyps == "unread":
        parts.append("<p><strong>Hypotheses</strong>: <em>unread</em> (the record's Source carries the signature; a reader files them).</p>")
    else:
        items = []
        for h in hyps or []:
            H = r.nodes[h]
            items.append(f"<li>{site.link('n', h)} <span class=\"tag\">{esc(H['fields'].get('discharge', ''))}</span>: {esc(H['statement'].strip())}"
                         + (f"<br><span class=\"muted\">{esc(H['notes'].strip())}</span>" if H.get("notes") else "") + "</li>")
        parts.append("<p><strong>Hypotheses</strong>, read:</p><ul class=\"hyps\">" + "".join(items) + "</ul>")
    comp = [c for c in N["children"] if r.nodes[c].get("leaf_kind") == "completeness"]
    for c in comp:
        parts.append(f"<p><strong>Completeness</strong> ({site.link('n', c)}): {esc(r.nodes[c]['statement'].strip())}</p>")
    # what remains: the improvement claims on the informal claim(s)
    for c in claims:
        imps = [y for y, M in r.nodes.items() if M["fields"].get("improves") == c]
        for imp in imps:
            routes = r.nodes[imp]["children"]
            parts.append(f"<h3>What remains ({site.link('n', imp)})</h3><p class=\"muted\">{esc(r.nodes[imp]['statement'].strip())}</p><ul class=\"routes\">")
            for rt in routes:
                RT = r.nodes[rt]
                item = r.item_of_node.get(rt)
                refs = [str(w.get("ref")) for w in RT.get("work") or [] if w.get("kind") == "priorities"]
                tail = ""
                if item:
                    tail = f" — this is item {site.link('items', item)}"
                elif refs:
                    tail = " — item " + ", ".join(site.link("items", i) for i in refs if i in r.items)
                res = " (residual)" if RT["fields"].get("residual") else ""
                parts.append(f"<li>{site.link('n', rt)}{res}: {esc(RT['statement'].strip())}{tail}</li>")
            parts.append("</ul>")
    parts.append("</section>")
    return "\n".join(parts)


INTAKE = (("comment", "What you want to say about this node. A maintainer round files what lands as the event it is."),
          ("challenge", "The picture: what you believe is wrong with this node's Statement, and what would settle it."),
          ("estimate", "Your number on this node and the reasoning it rests on; it enters a ledger as your event."),
          ("want", "What you want, in research terms; it is filed as a want under your handle where your words place it."))


def intake_html(site: Site, x: str) -> str:
    """The intake verbs: each opens a prefilled GitHub issue carrying the node id and a protocol-shaped body; a
    maintainer round sweeps issues into ledger events (`graph/PROTOCOL.md`). The site itself accepts no write."""
    from urllib.parse import quote
    links = []
    for verb, hint in INTAKE:
        title = quote(f"[node] {x}: {verb}")
        body = quote(f"node: {x}\nurl: /n/{Site.seg(x)}/\nverb: {verb}\n\n## {hint}\n\n")
        links.append(f'<a class="verb" href="https://github.com/A-M-Berns/alignment-workspace/issues/new?title={title}&amp;body={body}">{verb}</a>')
    return '<section class="intake"><h2>Say something about it</h2><p class="muted">Each verb opens a prefilled issue; a round files what lands as the ledger event it is.</p><p>' + " · ".join(links) + "</p></section>"


def node_body(site: Site, x: str) -> tuple[str, list[tuple[str, str]], str]:
    r = site.repo
    N = r.nodes[x]
    is_frame = bool(N.get("frame"))
    sub = esc(kind_label(N)) + (" · <span class=\"tag\">drafted</span>" if r.drafted(x) else " · <span class=\"tag human\">human-touched</span>")
    chain = r.frame_chain(x) if is_frame else []
    crumbs = [("top", "/")] + [(f, site.url("n", f)) for f in chain[:-1]]
    body = []
    if is_frame:
        Fr = N["frame"]
        body.append(f"<section><h2>Question</h2><p class=\"question\">{esc(Fr['question'] or '')}</p>"
                    f"<p>Owners: {owners_html(site, Fr.get('owners') or [])}" + (" · <em>owner has not confirmed (drafted from the wiki)</em>" if Fr.get("filed_from") == "wiki" else "")
                    + (" · <em>not opened</em>" if Fr.get("opened") is False else "") + "</p></section>")
        if chain:
            body.append("<p class=\"muted\">Path: " + " › ".join(site.link("n", f) for f in chain) + "</p>")
        roots = Fr.get("roots") or []
        if not roots:
            body.append("<section><h2>Roots</h2><p><strong>No goal yet.</strong> This frame holds what it is about (below) and names no goal of the ranking; naming one is its owner's spelling-out.</p></section>")
        else:
            by_role: dict[str, list[str]] = {}
            for rt in roots:
                by_role.setdefault(rt.get("role") or "?", []).append(rt["id"])
            body.append("<section><h2>Roots (the frame's goals)</h2>")
            for role in ("plan", "risk-story", "shared-claim", "want"):
                if role in by_role:
                    body.append(f"<h3>{esc(role)}</h3>" + "".join(node_card(site, rid, "sub-frame" if r.nodes[rid].get("frame") else "") for rid in by_role[role]))
            body.append("</section>")
        held = Fr.get("holds") or []
        if held:
            groups = {"formal results": [], "items": [], "other": []}
            for h in held:
                H = r.nodes[h]
                (groups["formal results"] if H.get("formal_result") else groups["items"] if h in r.item_of_node else groups["other"]).append(h)
            body.append("<section><h2>What it holds</h2><p class=\"muted\">Nodes this frame is about that are not goals of the ranking: no status, value or rank here.</p>")
            for g_name, ids in groups.items():
                if ids:
                    body.append(f"<h3>{esc(g_name)} ({len(ids)})</h3><ul class=\"held\">" + "".join(
                        f"<li>{site.link('n', h)}: {esc(r.nodes[h]['statement'].strip()[:200])}" + (f" — item {site.link('items', r.item_of_node[h])}" if h in r.item_of_node else "") + "</li>" for h in ids) + "</ul>")
            body.append("</section>")
        subs = [rt["id"] for rt in roots if r.nodes[rt["id"]].get("frame")]
        if subs:
            body.append("<section><h2>Sub-frames</h2><ul>" + "".join(f"<li>{site.link('n', s)}: {esc(r.nodes[s]['frame']['question'] or '')}</li>" for s in subs) + "</ul></section>")
        for page in N.get("narrative") or []:
            name = page.split("/")[-1][:-3]
            if name in r.wiki:
                body.append(f"<section><h2>Narrative: {site.link('wiki', name)}</h2><div class=\"wiki\">{render_wiki(site, name)}</div></section>")
    body.append(f"<section><h2>Statement</h2><p class=\"statement\">{esc(N['statement'].strip())}</p></section>")
    if N.get("source"):
        body.append(f"<section><h2>Source</h2>{md.render(N['source'], wiki_link_resolver(site))}</section>")
    if N.get("notes"):
        body.append(f"<section><h2>Notes</h2>{md.render(N['notes'], wiki_link_resolver(site))}</section>")
    if N.get("formal_result"):
        body.append(bridge_card(site, x))
    if x in r.item_of_node:
        body.append(f"<p>This node is item {site.link('items', r.item_of_node[x])}.</p>")
    # author, events
    body.append(f"<section><h2>Author and human events</h2><p>Author {esc(str(N.get('author')))}; version {esc(str(N.get('version')))}; size {esc(str(N.get('size')))}.</p>{events_html(site, r.human_events(x))}</section>")
    # edges
    edges = []
    for p, kind in r.parents.get(x, []):
        edges.append(f"<li>{esc(kind)} of {site.link('n', p)}</li>")
    for f, role in r.root_of.get(x, []):
        edges.append(f"<li>root ({esc(str(role))}) of {site.link('n', f) if f != 'top' else 'the top frame'}</li>")
    for f in r.held_by.get(x, []):
        edges.append(f"<li>held by {site.link('n', f) if f != 'top' else 'the top frame'}</li>")
    if N.get("given"):
        edges.append(f"<li>given {site.link('n', str(N['given']).split('@')[0])}{' (as valid)' if '@valid' in str(N['given']) else ''}</li>")
    kids = [f"<li>{esc(k)}: {site.link('n', c)} <span class=\"kind\">{esc(kind_label(r.nodes[c]))}</span></li>" for c in N["children"] for k in ["part"]]
    body.append("<section><h2>Edges</h2>" + ("<h3>Above</h3><ul>" + "".join(edges) + "</ul>" if edges else "") + ("<h3>Children</h3><ul>" + "".join(kids) + "</ul>" if kids else "") + "</section>")
    if N.get("work"):
        body.append("<section><h2>Work pointers</h2>" + work_html(site, N["work"]) + "</section>")
    # the ranking lens, collapsed
    D = r.derived["nodes"].get(x)
    if D:
        lens = {k: D.get(k) for k in ("status", "diagnosis", "flags", "V", "belief", "draft")}
        if x in r.derived.get("roots", {}):
            R = r.derived["roots"][x]
            lens["root"] = {k: R.get(k) for k in ("status", "Pr", "value", "cost", "margin")}
        body.append(f"<details class=\"ranking\"><summary>Ranking (the lens, not the structure)</summary><pre>{esc(json.dumps(lens, indent=1, ensure_ascii=False))}</pre></details>")
    body.append(intake_html(site, x))
    return "\n".join(body), crumbs, sub


def node_page(site: Site, x: str) -> str:
    body, crumbs, sub = node_body(site, x)
    return layout(site, x, body, crumbs, sub)


def node_frag(site: Site, x: str) -> str:
    """The node's detail without the layout: what the map's panel shows when a node is opened in place."""
    body, _, sub = node_body(site, x)
    return f'<div class="frag"><p class="frag-head">{site.link("n", x)} <span class="kind">{sub}</span></p>{body}</div>'


def item_page(site: Site, num: str) -> str:
    r = site.repo
    rec = r.items[num]
    x = rec["node"]
    N = r.nodes[x]
    f = N["fields"]
    body = [f"<p class=\"subtitle\">{esc(str(f.get('section', '')))} · difficulty {esc(str(f.get('difficulty') or '—'))} · project {esc(str(f.get('project') or 'none'))} · <strong>{esc(str(f.get('item_status', 'open')))}</strong> · node {site.link('n', x)}</p>"]
    if f.get("heading_notes"):
        body.append(f"<p class=\"muted\">{md.inline(str(f['heading_notes']))}</p>")
    if N.get("item_body"):
        body.append(f"<section class=\"item-body\">{md.render(N['item_body'], wiki_link_resolver(site))}</section>")
    for k, label in (("deliverable", "Deliverable shape"), ("acceptance", "Acceptance check")):
        if f.get(k):
            body.append(f"<p><strong>{label}:</strong> {md.inline(str(f[k]))}</p>")
    if f.get("context"):
        ctx = f["context"] if isinstance(f["context"], list) else [f["context"]]
        body.append("<p><strong>Context:</strong> " + "; ".join(f"<code>{esc(str(c))}</code>" for c in ctx) + "</p>")
    bearing = rec.get("bearing") or []
    body.append("<section><h2>Registered results bearing on this item</h2>" + ("<ul>" + "".join(f"<li>{site.link('n', b)}: {esc(r.nodes[b]['statement'].strip()[:200])}</li>" for b in bearing) + "</ul>" if bearing else "<p class=\"muted\">None registered.</p>") + "</section>")
    where = []
    for fr in r.held_by.get(x, []):
        where.append(f"held by {site.link('n', fr)}")
    for p, kind in r.parents.get(x, []):
        where.append(f"{kind} of {site.link('n', p)}")
    if N.get("given"):
        where.append(f"a route conditioned on {site.link('n', str(N['given']).split('@')[0])}")
    body.append("<section><h2>Where it hangs</h2>" + ("<ul>" + "".join(f"<li>{w}</li>" for w in where) + "</ul>" if where else "<p class=\"muted\">Attached nowhere.</p>") + "</section>")
    # claim_changes lists registry ids; a round touched the item when one of them bears on it
    rounds = [rid for rid, R in r.rounds.items() if any(str((r.registry.get(c) or {}).get("answers_item")) == num for c in R.get("claim_changes") or [])]
    touching = [a for a, d in r.decisions.items() if any(t["kind"] == "item" and t["ref"] == num for t in d["touches"])]
    body.append("<section><h2>Rounds and decisions that touch it</h2>" + ("<ul>" + "".join(f"<li>round {site.link('rounds', rid)}</li>" for rid in rounds) + "".join(f"<li>decision {site.link('decisions', a, r.decisions[a]['title'])}</li>" for a in touching) + "</ul>" if rounds or touching else "<p class=\"muted\">None recorded.</p>") + "</section>")
    return layout(site, f"Item {num}: {f.get('title', '')}", "\n".join(body), [("items", "/items/")])


def decision_page(site: Site, anchor: str) -> str:
    r = site.repo
    d = r.decisions[anchor]
    body = [f"<p class=\"subtitle\">{esc(d['date'] or 'queued')} · <strong>{esc(d['status'])}</strong> · DECISIONS.md line {d['line']}</p>",
            f"<section class=\"decision-body\">{md.render(d['body'], wiki_link_resolver(site))}</section>"]
    touches = []
    for t in d["touches"]:
        if t["kind"] == "node" and t["ref"] in r.nodes:
            touches.append(site.link("n", t["ref"]))
        elif t["kind"] == "item" and t["ref"] in r.items:
            touches.append("item " + site.link("items", t["ref"]))
        elif t["kind"] == "claim" and t["ref"] in r.registry:
            touches.append("claim " + site.link("claims", t["ref"]))
        else:
            touches.append(f"<code>{esc(t['kind'])}:{esc(t['ref'])}</code> (unresolved)")
    body.append("<section><h2>Touches</h2>" + ("<ul>" + "".join(f"<li>{t}</li>" for t in touches) + "</ul>" if touches else "<p class=\"muted\">Nothing named.</p>") + "</section>")
    pb = d.get("pointed_by") or []
    body.append("<section><h2>Nodes pointing at it</h2>" + ("<ul>" + "".join(f"<li>{site.link('n', x)}</li>" for x in pb) + "</ul>" if pb else "<p class=\"muted\">None.</p>") + "</section>")
    return layout(site, d["title"], "\n".join(body), [("decisions", "/decisions/")])


def round_page(site: Site, rid: str) -> str:
    r = site.repo
    R = r.rounds[rid]
    body = [f"<p class=\"subtitle\">{esc(str(R.get('date')))} · project {esc(str(R.get('project') or 'workspace'))} · path <code>{esc(str(R.get('path')))}</code></p>"]
    if R.get("verdict"):
        body.append(f"<p><strong>Verdict</strong> <code>{esc(str(R['verdict']))}</code></p>")
    docs = []
    for label, rel in (("Prompt", R.get("prompt")), ("Report", (R.get("path") or "") + "/REPORT.md" if R.get("path") else None), ("README", (R.get("path") or "") + "/README.md" if R.get("path") else None)):
        if rel and (md_path := (site.repo_root() / rel)).is_file():
            docs.append(f"<details><summary>{label} <code>{esc(rel)}</code></summary><div class=\"doc\">{md.render(md_path.read_text(), wiki_link_resolver(site), heading_shift=2)}</div></details>")
    if not docs and R.get("path"):
        p = site.repo_root() / "prompts" / rid / "REPORT.md"
        if p.is_file():
            docs.append(f"<details><summary>Report <code>prompts/{esc(rid)}/REPORT.md</code></summary><div class=\"doc\">{md.render(p.read_text(), wiki_link_resolver(site), heading_shift=2)}</div></details>")
    body += docs
    claims = [cid for cid, e in r.registry.items() if e.get("origin_round") == rid]
    body.append("<section><h2>Claims it registered</h2>" + ("<ul>" + "".join(f"<li>{site.link('claims', c)}: {esc(r.registry[c].get('short_name', ''))}</li>" for c in claims) + "</ul>" if claims else "<p class=\"muted\">None.</p>") + "</section>")
    items = sorted({str((r.registry.get(c) or {}).get("answers_item")) for c in R.get("claim_changes") or []})
    items = [i for i in items if i in r.items]
    body.append("<section><h2>Items it filed or answered</h2>" + ("<ul>" + "".join(f"<li>{site.link('items', i)}</li>" for i in items) + "</ul>" if items else "<p class=\"muted\">None recorded in the index.</p>") + "</section>")
    pb = r.round_pointed.get(rid) or []
    body.append("<section><h2>Nodes pointing at it</h2>" + ("<ul>" + "".join(f"<li>{site.link('n', x)}</li>" for x in pb) + "</ul>" if pb else "<p class=\"muted\">None.</p>") + "</section>")
    deps = R.get("depends_on") or []
    if deps:
        body.append("<section><h2>Depends on</h2><ul>" + "".join(f"<li>{site.link('rounds', d) if d in r.rounds else esc(d)}</li>" for d in deps) + "</ul></section>")
    return layout(site, rid, "\n".join(body), [("rounds", "/rounds/")])


def wiki_page(site: Site, name: str) -> str:
    r = site.repo
    text = r.wiki[name]
    refs = REF.findall(text)
    srcs = []
    for kind, ident in refs:
        if kind == "claim" and ident in r.registry:
            srcs.append(r.registry[ident]["registry"])
        elif kind in ("item", "item-open") and ident in r.items:
            srcs.append(f"graph/nodes/{r.items[ident]['node']}.md")
        elif kind == "node" and ident in r.nodes:
            srcs.append(f"graph/nodes/{ident}.md")
    own = last_changed([f"wiki/{name}.md"])
    src = last_changed(sorted(set(srcs))) if srcs else None
    narr = [x for x in r.narratives.get(f"wiki/{name}.md", [])]
    body = [f"<p class=\"subtitle\">page last changed {esc(own or '—')} · its sources last changed {esc(src or '—')}" + (" · narrates " + ", ".join(site.link('n', x) if x != 'top' else 'the top frame' for x in narr) if narr else "") + "</p>",
            f"<div class=\"wiki\">{render_wiki(site, name)}</div>"]
    return layout(site, name.replace("-", " "), "\n".join(body), [("wiki", "/wiki/")])


def concept_side(site: Site, cid: str) -> str:
    """The side pane every concept's full view carries: its connections split between core theory
    (goals and philosophical concepts), core formalism (constructions and mathematical objects) and
    sources (prior work), each with the link's why; then the merged work tagged to it, newest first."""
    r = site.repo
    e = r.concepts[cid]
    groups: dict[str, list[str]] = {"Core theory": [], "Core formalism": [], "Sources": []}
    bucket = {"goal": "Core theory", "philosophy": "Core theory", "construction": "Core formalism",
              "object": "Core formalism", "work": "Sources"}
    for L in r.concept_links:
        other = L["to"] if L["from"] == cid else L["from"] if L["to"] == cid else None
        if not other or other not in r.concepts:
            continue
        o = r.concepts[other]
        target = site.url("wiki", o["wiki"]) if o.get("wiki") else site.url("concepts", other)
        arrow = "↔" if L.get("undirected") else ("←" if L["to"] == cid else "→")
        groups[bucket.get(o.get("kind", ""), "Core theory")].append(
            f'<li><span class="dirmark">{arrow}</span> <a href="{target}">{esc(o.get("title", other))}</a>'
            f'<br><span class="muted whyline">{esc(str(L.get("why") or ""))}</span></li>')
    out = []
    for gname in ("Core theory", "Core formalism", "Sources"):
        if groups[gname]:
            out.append(f"<section class=\"side-group\"><h2>{gname}</h2><ul class=\"listing\">" + "".join(groups[gname]) + "</ul></section>")
    refs = set(e.get("refs") or [])
    related = [(num, P) for num, P in sorted(r.prs.items(), key=lambda kv: (str(kv[1].get("merged") or ""), int(kv[0])), reverse=True)
               if (e.get("wiki") and e["wiki"] in ((P.get("topics") or {}).get("wiki") or []))
               or (refs & set((P.get("topics") or {}).get("frames") or []))]
    if related:
        out.append("<section class=\"side-group\"><h2>Merged work</h2>" + "".join(pr_digest_details(site, num) for num, _ in related) + "</section>")
    return "\n".join(out)


def concept_body(site: Site, cid: str) -> str:
    """A registry concept's full view: the content pane (blurb, source, map refs — or the wiki page where
    one backs it) beside the connections-and-merged-work pane of concept_side."""
    r = site.repo
    e = r.concepts[cid]
    kind_label_ = r.concept_kinds.get(e.get("kind", ""), e.get("kind", ""))
    main = [f'<p class="subtitle">{esc(kind_label_)}</p>', f'<div class="pr-summary"><p>{esc(str(e.get("blurb") or ""))}</p></div>']
    if e.get("url"):
        main.append(f'<p><a href="{esc(e["url"])}">{esc(e["url"])}</a></p>')
    refs = [x for x in e.get("refs") or [] if x in r.nodes]
    if refs:
        main.append("<section><h2>On the map</h2><ul class=\"listing\">" + "".join(f"<li>{site.link('n', x)}: {esc(r.nodes[x]['statement'].strip()[:160])}</li>" for x in refs) + "</ul></section>")
    return f'<div class="pane2"><div class="pane-main">{"".join(main)}</div><aside class="pane-side">{concept_side(site, cid)}</aside></div>'


def concept_page(site: Site, cid: str) -> str:
    return layout(site, site.repo.concepts[cid].get("title", cid), concept_body(site, cid), [("map", "/")])


def concept_frag(site: Site, cid: str) -> str:
    e = site.repo.concepts[cid]
    return f'<div class="frag"><p class="frag-head">{site.link("concepts", cid, e.get("title", cid))} <span class="kind">concept</span></p>{concept_body(site, cid)}</div>'


def wiki_frag(site: Site, name: str) -> str:
    """The wiki page's full view for the map: the rendered page beside the concept's side pane —
    connections split into core theory, core formalism and sources, then the tagged merged work."""
    r = site.repo
    cid = next((c for c, e in r.concepts.items() if e.get("wiki") == name), None)
    head = f'<p class="frag-head">{site.link("wiki", name, name.replace("-", " "))} <span class="kind">concept</span></p>'
    main = f"<div class=\"wiki\">{render_wiki(site, name)}</div>"
    if cid:
        return f'{head}<div class="pane2"><div class="pane-main">{main}</div><aside class="pane-side">{concept_side(site, cid)}</aside></div>'
    related = [(num, P) for num, P in sorted(r.prs.items(), key=lambda kv: (str(kv[1].get("merged") or ""), int(kv[0])), reverse=True)
               if name in ((P.get("topics") or {}).get("wiki") or [])]
    tail = ("<section><h2>Merged work on this concept</h2>" + "".join(pr_digest_details(site, num) for num, _ in related) + "</section>") if related else ""
    return head + main + tail


def pr_digest_details(site: Site, num: str) -> str:
    """One merged pull request as an expandable row: the digest inside, the full page a click further."""
    r = site.repo
    P = r.prs[num]
    head = (f'<span class="date">{esc(str(P.get("merged") or ""))}</span> #{esc(num)} {esc(str(P.get("title", "")))}'
            + (' <span class="tag">superseded in part</span>' if P.get("superseded") else ""))
    inner = []
    if P.get("superseded"):
        inner.append(f'<p class="superseded"><strong>Superseded in part:</strong> {md.inline(str(P["superseded"]))}</p>')
    inner.append("".join(f"<p>{md.inline(para.strip())}</p>" for para in str(P.get("summary") or "").split("\n\n") if para.strip()))
    inner.append(f'<p class="muted">{site.link("prs", num, "Full detail →")}</p>')
    return f'<details class="pr-digest"><summary>{head}</summary><div class="pr-digest-body">{"".join(inner)}</div></details>'


def pr_body(site: Site, num: str) -> str:
    """A merged pull request's digest: the key points, its supersessions with references, its rounds and topics.
    The digests are a round deliverable in state/prs.json, provenance-marked there; the site renders them."""
    r = site.repo
    P = r.prs[num]
    gh = f"https://github.com/A-M-Berns/alignment-workspace/pull/{esc(num)}"
    body = [f'<p class="subtitle">merged {esc(str(P.get("merged") or "—"))} · <a href="{gh}">pull request #{esc(num)} on GitHub</a></p>']
    if P.get("superseded"):
        body.append(f'<p class="superseded"><strong>Superseded in part:</strong> {md.inline(str(P["superseded"]))}</p>')
    body.append("<div class=\"pr-summary\">" + "".join(f"<p>{md.inline(para.strip())}</p>" for para in str(P.get("summary") or "").split("\n\n") if para.strip()) + "</div>")
    rds = [rid for rid in P.get("rounds") or [] if rid in r.rounds]
    if rds:
        body.append("<p><strong>Rounds:</strong> " + ", ".join(site.link("rounds", rid) for rid in rds) + "</p>")
    topics = P.get("topics") or {}
    tlinks = [site.link("wiki", w, w.replace("-", " ")) for w in topics.get("wiki") or [] if w in r.wiki] \
        + [site.link("n", f) for f in topics.get("frames") or [] if f in r.nodes]
    if tlinks:
        body.append("<p><strong>Topics:</strong> " + ", ".join(tlinks) + "</p>")
    return "\n".join(body)


def pr_page(site: Site, num: str) -> str:
    return layout(site, f"#{num} {site.repo.prs[num].get('title', '')}", pr_body(site, num), [("merged work", "/prs/")])


def pr_frag(site: Site, num: str) -> str:
    P = site.repo.prs[num]
    return f'<div class="frag"><p class="frag-head">{site.link("prs", num, f"#{num} " + str(P.get("title", "")))} <span class="kind">merged pull request</span></p>{pr_body(site, num)}</div>'


def handle_page(site: Site, handle: str) -> str:
    r = site.repo
    h = "@" + handle
    spec = r.handles.get(h) or {}
    frames = [x for x, N in r.nodes.items() if N.get("frame") and h in (N["frame"].get("owners") or [])]
    wants = [x for x, N in r.nodes.items() if N["fields"].get("want") and N["fields"].get("owner") == h]
    evs = [e for e in r.events if e.get("by") == h]
    body = [f"<p class=\"subtitle\">{esc(spec.get('kind', '?'))}" + (f" · GitHub <a href=\"https://github.com/{esc(spec['github'])}\">{esc(spec['github'])}</a>" if spec.get("github") else "") + (f" · model {esc(spec['model'])}" if spec.get("model") else "")
            + (" · <em>a legacy name, minted before an AI handle was its model's slug</em>" if spec.get("legacy") else "") + "</p>"]
    body.append("<section><h2>Frames owned</h2>" + ("<ul>" + "".join(f"<li>{site.link('n', x)}: {esc(r.nodes[x]['frame']['question'] or '')}</li>" for x in frames) + "</ul>" if frames else "<p class=\"muted\">None.</p>") + "</section>")
    wl = []
    for x in wants:
        pri = [e for e in r.events_by_node.get(x, []) if e.get("kind") == "priority" and e.get("by") == h]
        word = pri[-1].get("estimate") if pri else None
        state = f"priority {esc(str(word))}" if word else ("no word yet: filed from quoted words, weighs nothing until the owner speaks" if r.nodes[x]["fields"].get("filed_from") == "quote" else "no word yet (reads as medium)")
        wl.append(f"<li>{site.link('n', x)}: {esc(r.nodes[x]['statement'].strip())} — <em>{state}</em></li>")
    body.append("<section><h2>Wants</h2>" + ("<ul>" + "".join(wl) + "</ul>" if wl else "<p class=\"muted\">None.</p>") + "</section>")
    body.append("<section><h2>Events</h2>" + events_html(site, evs) + "</section>")
    return layout(site, h, "\n".join(body), [("by", "/by/")])


def front_page(site: Site, lede_html: str, feed_rows: list[str]) -> str:
    """The map, zoomed out: /assets/map.js lays /assets/map.json out as nested regions and zooms; a node opened on the
    canvas shows its /n/<id>/frag.html in the panel. Without JavaScript the lines render as links below the lede."""
    r = site.repo
    top = r.index["frame"]
    prog = r.nodes.get("the-program")
    lines = [rt["id"] for rt in (prog["frame"]["roots"] if prog else [])]
    noscript = ("<noscript><section><h2>The lines</h2><ul>" + "".join(
        f"<li>{site.link('n', line)}: {esc(r.nodes[line]['frame']['question'] or '')}</li>" for line in lines)
        + "</ul></section></noscript>")
    body = ['<div class="map-full"><div class="map-stage">'
            '<svg id="map" role="application" aria-label="the argument map"></svg>'
            '<div class="map-side overlay">'
            '<span id="map-legend"></span>'
            '<label class="edges-toggle"><input type="checkbox" id="map-edges" checked> edges</label></div>'
            f'<details class="map-about overlay"><summary>about this map</summary><p class="question">{esc(top["question"])}</p>{lede_html}</details>'
            '<span class="map-hint overlay muted">drag to pan · scroll to zoom · click a node · esc backs out</span>'
            '<div id="map-card" hidden></div>'
            '<div id="map-modal"><div id="map-panel"><button id="map-panel-close" aria-label="close">×</button><div id="map-panel-body"></div></div></div>'
            '</div></div>',
            noscript,
            "<div class=\"below-map\"><details class=\"front-feed\"><summary>Recent in the feed</summary><ul class=\"feed\">" + "".join(feed_rows[:12]) + "</ul><p><a href=\"/feed/\">The whole feed</a>.</p></details></div>"]
    return layout(site, "The map of the program", "\n".join(body)).replace("</head>", '<script defer src="/assets/map.js"></script></head>')


def map_data(site: Site) -> dict:
    """What the canvas draws: the concept network of state/concepts.json — ids, per-concept metadata
    (kind, wiki page, title, blurb, tagged merged work, and the goal-distance layer that orders the
    canvas left to right), and the directed links, each with its relation labels and why."""
    r = site.repo
    REL = {"part": "is part of", "substrate": "is the substrate of", "uses": "is used by", "shapes": "shaped",
           "defines": "sets out", "adjacent": "is adjacent to", "contrast": "is contrasted with", "formalizes": "is formalized by"}
    links: list[list] = []
    succ: dict[str, list[str]] = {}
    for L in r.concept_links:
        a, b = L.get("from"), L.get("to")
        if a not in r.concepts or b not in r.concepts:
            site.unresolved.append(f"concepts:link:{a}--{b}")
            continue
        rels = [REL.get(x, x) for x in L.get("rel") or []]
        und = 1 if L.get("undirected") else 0
        links.append([a, b, 2 + len(rels), rels, str(L.get("why") or ""), und])
        if not und:
            succ.setdefault(a, []).append(b)
    # the goal-distance layer: longest directed path toward the-program (goals as sinks on the right)
    memo: dict[str, int | None] = {}
    seen: set[str] = set()

    def depth(x: str) -> int | None:
        if x in memo:
            return memo[x]
        if x == "the-program":
            memo[x] = 0
            return 0
        if x in seen:
            return None
        seen.add(x)
        outs = [d for d in (depth(y) for y in succ.get(x, [])) if d is not None]
        seen.discard(x)
        memo[x] = 1 + max(outs) if outs else None
        return memo[x]
    ds = {cid: depth(cid) for cid in r.concepts}
    dmax = max([v for v in ds.values() if v is not None] or [1])
    # a node with no directed path to the program sits deep left; what feeds only such nodes sits deeper
    for _ in range(3):
        for cid in r.concepts:
            if ds[cid] is None:
                outs = [ds[y] for y in succ.get(cid, []) if ds.get(y) is not None]
                ds[cid] = 1 + max(outs) if outs else dmax
    ds = {cid: (v if v is not None else dmax) for cid, v in ds.items()}
    prs_of: dict[str, int] = {}
    for num, P in r.prs.items():
        for w in (P.get("topics") or {}).get("wiki") or []:
            prs_of[w] = prs_of.get(w, 0) + 1
    meta = {}
    for cid, e in r.concepts.items():
        if e.get("wiki") and e["wiki"] not in r.wiki:
            site.unresolved.append(f"concepts:{cid}:wiki:{e['wiki']}")
        for x in e.get("refs") or []:
            if x not in r.nodes:
                site.unresolved.append(f"concepts:{cid}:ref:{x}")
        meta[cid] = {"k": e.get("kind", ""), "w": e.get("wiki") or "", "t": e.get("title", cid),
                     "s": str(e.get("blurb") or ""), "prs": prs_of.get(e.get("wiki") or "", 0), "d": ds[cid]}
    return {"items": list(r.concepts), "concepts": meta, "kinds": r.concept_kinds, "links": links}


def feed_rows(site: Site) -> list[str]:
    r = site.repo
    rows = []
    for rid, R in r.rounds.items():
        rows.append((str(R.get("date") or ""), f"round {site.link('rounds', rid)}" + (f" ({esc(str(R.get('project')))})" if R.get("project") else "")))
    for cid, e in r.registry.items():
        rd = r.rounds.get(e.get("origin_round") or "")
        rows.append((str(rd.get("date")) if rd else "", f"claim {site.link('claims', cid)} registered ({esc(e.get('class', ''))}), {esc(e.get('short_name', ''))}"))
    for a, d in r.decisions.items():
        if d.get("date"):
            rows.append((d["date"], f"decision {site.link('decisions', a, d['title'])}"))
    rows.sort(key=lambda t: t[0], reverse=True)
    return [f"<li><span class=\"date\">{esc(d or '—')}</span> {h}</li>" for d, h in rows]


def feed_page(site: Site, rows: list[str]) -> str:
    return layout(site, "Feed", "<p class=\"muted\">Rounds, claims registered and decisions landed, by date, from state/rounds.json, the registries' origin rounds and the decision anchors.</p><ul class=\"feed\">" + "".join(rows) + "</ul>")


def spine_page(site: Site) -> str:
    """The formal results as a DAG by the part/given edges between their claims; held-only results below."""
    r = site.repo
    results = [x for x, N in r.nodes.items() if N.get("formal_result") and not N["fields"].get("superseded_by")]
    connected, held_only = [], []
    for x in results:
        claims = [p for p, k in r.parents.get(x, []) if k == "part"]
        (connected if claims else held_only).append(x)
    cls_of = lambda x: (r.record_entry(x) or {}).get("class", "unregistered")
    body = ["<p class=\"muted\">Formal results connected to the informal claims they establish, by the part edges of the map; class-coloured. Held-only results are listed below as unconnected. Small this round: the five connected claims are what it shows.</p>"]
    body.append("<section><h2>Connected</h2><ul class=\"spine\">")
    for x in sorted(connected):
        claims = [p for p, k in r.parents.get(x, []) if k == "part"]
        ups = []
        for c in claims:
            up = [(p, k) for p, k in r.parents.get(c, []) if k in ("part", "given")]
            imps = [y for y, M in r.nodes.items() if M["fields"].get("improves") == c]
            ups.append(f"{site.link('n', c)}" + (" ← " + ", ".join(f"{site.link('n', p)} ({k})" for p, k in up) if up else "") + (f" → {len(imps)} improvement claim(s)" if imps else ""))
        body.append(f"<li class=\"cls-{esc(cls_of(x))}\"><span class=\"cls\">{esc(cls_of(x))}</span> {site.link('n', x)} is a conjunct of " + "; ".join(ups) + "</li>")
    body.append("</ul></section><section><h2>Held only (unconnected)</h2><ul class=\"spine small\">")
    for x in sorted(held_only):
        body.append(f"<li class=\"cls-{esc(cls_of(x))}\"><span class=\"cls\">{esc(cls_of(x))}</span> {site.link('n', x)} — held by " + (", ".join(site.link('n', f) for f in r.held_by.get(x, [])) or "no frame") + "</li>")
    body.append("</ul></section>")
    return layout(site, "Theorem spine", "\n".join(body))


def ranking_page(site: Site) -> str:
    r = site.repo
    tasks = (site.repo_root() / "graph" / "tasks.md")
    text = tasks.read_text() if tasks.is_file() else "graph/tasks.md is not in this tree."
    dg = r.derived.get("digest") or {}
    body = ["<p class=\"lens\"><strong>This page is the lens, not the structure.</strong> The numbers here are derived from the human ledgers by the checker and say what to read next; nothing on any other page carries them.</p>",
            f"<section><h2>Digest</h2><pre>{esc(json.dumps(dg, indent=1, ensure_ascii=False))}</pre></section>",
            f"<section><h2>graph/tasks.md</h2><div class=\"doc\">{md.render(text, wiki_link_resolver(site), heading_shift=1)}</div></section>"]
    return layout(site, "Ranking", "\n".join(body))


def index_list_page(site: Site, title: str, rows: list[str], note: str = "") -> str:
    return layout(site, title, (f"<p class=\"muted\">{note}</p>" if note else "") + "<ul class=\"listing\">" + "".join(rows) + "</ul>")


def search_page(site: Site) -> str:
    return layout(site, "Search", "<p class=\"muted\">A client-side index over ids, Statements, titles and registry short names.</p><div id=\"results\">Loading the index…</div>")


def search_index(site: Site) -> list[dict]:
    r = site.repo
    out = []
    for x, N in r.nodes.items():
        out.append({"u": site.url("n", x), "t": x, "k": kind_label(N), "s": N["statement"].strip()[:300]})
    for num, rec in r.items.items():
        out.append({"u": site.url("items", num), "t": f"item {num}: {r.nodes[rec['node']]['fields'].get('title', '')}", "k": "item", "s": ""})
    for cid, e in r.registry.items():
        out.append({"u": site.url("claims", cid), "t": cid, "k": f"claim/{e.get('class', '')}", "s": e.get("short_name", "")})
    for a, d in r.decisions.items():
        out.append({"u": site.url("decisions", a), "t": d["title"], "k": "decision", "s": a})
    for rid in r.rounds:
        out.append({"u": site.url("rounds", rid), "t": rid, "k": "round", "s": ""})
    for name in r.wiki:
        out.append({"u": site.url("wiki", name), "t": name.replace("-", " "), "k": "wiki", "s": ""})
    return out
