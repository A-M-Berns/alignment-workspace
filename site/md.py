"""A small Markdown renderer for the site (standard library only).

Supported: ATX headings (`#` to `######`), paragraphs, unordered lists (`-`, `*`) and ordered lists (`1.`),
nested one level by indentation, fenced code blocks (```), block quotes (`>`), tables in the pipe form, horizontal
rules, inline code, emphasis (`*x*`, `_x_`), strong (`**x**`), links (`[t](u)`), wiki links (`[[Page]]`) and HTML
comments (dropped, except `<!--ref:…-->` markers, which the caller resolves before rendering).

Not supported, by design: nested lists deeper than one level, setext headings, footnotes, definition lists, raw
inline HTML (it is escaped), images (rendered as links), reference-style links, task lists, and math. A document that
uses them renders legibly but plainly.
"""
from __future__ import annotations

import html
import re

INLINE_CODE = re.compile(r"`([^`\n]+)`")
STRONG = re.compile(r"\*\*([^*\n]+)\*\*")
EM = re.compile(r"(?<![\w*])\*([^*\n]+)\*(?![\w*])|(?<![\w_])_([^_\n]+)_(?![\w_])")
LINK = re.compile(r"!?\[([^\]\n]*)\]\(([^)\s]+)(?:\s+\"[^\"]*\")?\)")
WIKILINK = re.compile(r"\[\[([^\]|\n]+)(?:\|([^\]\n]+))?\]\]")
COMMENT = re.compile(r"<!--.*?-->", re.S)
AUTOLINK = re.compile(r"(?<![\"'(>\w])(https?://[^\s<)\]]+)")


def esc(s: str) -> str:
    return html.escape(s, quote=True)


def inline(text: str, link_wiki=None) -> str:
    """Inline markup to HTML. `link_wiki(page) -> url or None` resolves `[[Page]]` links."""
    text = COMMENT.sub("", text)
    out, pos = [], 0
    # protect code spans first: split on them, render the rest
    parts = INLINE_CODE.split(text)
    for i, part in enumerate(parts):
        if i % 2 == 1:
            out.append(f"<code>{esc(part)}</code>")
            continue
        s = esc(part)

        def wl(m):
            page, label = m.group(1).strip(), (m.group(2) or m.group(1)).strip()
            url = link_wiki(page) if link_wiki else None
            return f'<a href="{esc(url)}">{esc(label)}</a>' if url else f"<span class=\"dead-link\">{esc(label)}</span>"
        s = WIKILINK.sub(wl, s)
        s = LINK.sub(lambda m: f'<a href="{m.group(2)}">{m.group(1) or m.group(2)}</a>', s)
        s = AUTOLINK.sub(lambda m: f'<a href="{m.group(1)}">{m.group(1)}</a>', s)
        s = STRONG.sub(r"<strong>\1</strong>", s)
        s = EM.sub(lambda m: f"<em>{m.group(1) or m.group(2)}</em>", s)
        out.append(s)
    return "".join(out)


def render(text: str, link_wiki=None, heading_shift: int = 0) -> str:
    lines = text.split("\n")
    out: list[str] = []
    i = 0
    n = len(lines)
    para: list[str] = []

    def flush_para():
        if para:
            out.append(f"<p>{inline(' '.join(l.strip() for l in para), link_wiki)}</p>")
            para.clear()

    while i < n:
        line = lines[i]
        stripped = line.strip()
        if stripped.startswith("```"):
            flush_para()
            lang = stripped[3:].strip()
            buf = []
            i += 1
            while i < n and not lines[i].strip().startswith("```"):
                buf.append(lines[i])
                i += 1
            i += 1
            cls = f' class="lang-{esc(lang)}"' if lang else ""
            out.append(f"<pre><code{cls}>{esc(chr(10).join(buf))}</code></pre>")
            continue
        if not stripped:
            flush_para()
            i += 1
            continue
        m = re.match(r"^(#{1,6})\s+(.*?)\s*#*\s*$", stripped)
        if m:
            flush_para()
            level = min(6, len(m.group(1)) + heading_shift)
            out.append(f"<h{level}>{inline(m.group(2), link_wiki)}</h{level}>")
            i += 1
            continue
        if re.match(r"^(-{3,}|\*{3,}|_{3,})$", stripped):
            flush_para()
            out.append("<hr>")
            i += 1
            continue
        if stripped.startswith(">"):
            flush_para()
            buf = []
            while i < n and lines[i].strip().startswith(">"):
                buf.append(re.sub(r"^\s*>\s?", "", lines[i]))
                i += 1
            out.append(f"<blockquote>{render(chr(10).join(buf), link_wiki, heading_shift)}</blockquote>")
            continue
        if "|" in stripped and i + 1 < n and re.match(r"^\s*\|?\s*:?-{2,}", lines[i + 1]):
            flush_para()
            rows = []
            while i < n and "|" in lines[i].strip() and lines[i].strip():
                rows.append(lines[i].strip())
                i += 1
            cells = lambda r: [c.strip() for c in r.strip().strip("|").split("|")]
            head = cells(rows[0])
            body = [cells(r) for r in rows[2:]]
            out.append("<table><thead><tr>" + "".join(f"<th>{inline(c, link_wiki)}</th>" for c in head) + "</tr></thead><tbody>"
                       + "".join("<tr>" + "".join(f"<td>{inline(c, link_wiki)}</td>" for c in r) + "</tr>" for r in body) + "</tbody></table>")
            continue
        m = re.match(r"^(\s*)([-*]|\d+\.)\s+(.*)$", line)
        if m:
            flush_para()
            ordered = m.group(2)[0].isdigit()
            tag = "ol" if ordered else "ul"
            items: list[tuple[int, str, list[str]]] = []
            while i < n:
                mm = re.match(r"^(\s*)([-*]|\d+\.)\s+(.*)$", lines[i])
                if mm:
                    items.append((len(mm.group(1)), mm.group(3), []))
                    i += 1
                    continue
                if lines[i].strip() and lines[i].startswith(" ") and items:
                    items[-1][2].append(lines[i].strip())
                    i += 1
                    continue
                break
            # one level of nesting by indentation
            base = items[0][0] if items else 0
            html_items, j = [], 0
            while j < len(items):
                ind, txt, cont = items[j]
                sub = []
                k = j + 1
                while k < len(items) and items[k][0] > base:
                    sub.append(items[k])
                    k += 1
                body_txt = inline(" ".join([txt] + cont), link_wiki)
                if sub:
                    subtag = "ol" if False else "ul"
                    body_txt += f"<{subtag}>" + "".join(f"<li>{inline(' '.join([t] + c), link_wiki)}</li>" for _, t, c in sub) + f"</{subtag}>"
                html_items.append(f"<li>{body_txt}</li>")
                j = k
            out.append(f"<{tag}>{''.join(html_items)}</{tag}>")
            continue
        para.append(line)
        i += 1
    flush_para()
    return "\n".join(out)


def first_paragraph(text: str) -> str:
    """The first paragraph of a Markdown document, as plain text (headings, comments and blank lines skipped)."""
    buf = []
    for line in text.split("\n"):
        s = COMMENT.sub("", line).strip()
        if not s:
            if buf:
                break
            continue
        if s.startswith("#") or s.startswith("```") or s.startswith("|") or s.startswith("---"):
            if buf:
                break
            continue
        buf.append(s)
    plain = " ".join(buf)
    plain = WIKILINK.sub(lambda m: (m.group(2) or m.group(1)), plain)
    plain = LINK.sub(lambda m: m.group(1) or m.group(2), plain)
    plain = re.sub(r"[*_`]", "", plain)
    return plain
