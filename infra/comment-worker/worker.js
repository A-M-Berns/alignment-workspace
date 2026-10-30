// The comment intake worker. The site POSTs a comment here; the worker files it as a GitHub issue
// in the repository (title `[comment] <concept id>`), so the whole flow happens on the site and the
// issue creation is the parallel record. It publishes and adjudicates nothing; its only credential
// is a fine-grained token scoped to issues:write on this one repository, held as a Worker secret —
// never in the repository or its CI. Reviewed comments reach the site through state/comments.json.
const ALLOWED_ORIGINS = ["https://alignmentworkspace.com", "https://www.alignmentworkspace.com", "http://localhost:8137"];
const REPO = "A-M-Berns/alignment-workspace";

function cors(origin) {
  const o = ALLOWED_ORIGINS.includes(origin) ? origin : ALLOWED_ORIGINS[0];
  return {
    "Access-Control-Allow-Origin": o,
    "Access-Control-Allow-Methods": "POST, OPTIONS",
    "Access-Control-Allow-Headers": "content-type",
  };
}

export default {
  async fetch(request, env) {
    const origin = request.headers.get("Origin") || "";
    if (request.method === "OPTIONS") return new Response(null, { headers: cors(origin) });
    if (request.method !== "POST") return new Response("POST only", { status: 405, headers: cors(origin) });
    let p;
    try { p = await request.json(); } catch { return json({ ok: false, error: "bad json" }, 400, origin); }
    const concept = String(p.concept || "").slice(0, 120).trim();
    const body = String(p.body || "").slice(0, 5000).trim();
    const name = String(p.name || "").slice(0, 80).trim();
    if (!concept || !/^[A-Za-z0-9._-]+$/.test(concept)) return json({ ok: false, error: "bad concept id" }, 400, origin);
    if (body.length < 3) return json({ ok: false, error: "empty comment" }, 400, origin);
    const issue = {
      title: `[comment] ${concept}`,
      body: `concept: ${concept}\nfrom: ${name || "anonymous"} (via alignmentworkspace.com)\nmap: https://alignmentworkspace.com/#c=${concept}\n\n---\n\n${body}`,
    };
    const r = await fetch(`https://api.github.com/repos/${REPO}/issues`, {
      method: "POST",
      headers: {
        "Authorization": `Bearer ${env.GITHUB_TOKEN}`,
        "Accept": "application/vnd.github+json",
        "User-Agent": "alignmentworkspace-comments",
        "Content-Type": "application/json",
      },
      body: JSON.stringify(issue),
    });
    if (!r.ok) return json({ ok: false, error: `github ${r.status}` }, 502, origin);
    const out = await r.json();
    return json({ ok: true, url: out.html_url }, 200, origin);
  },
};

function json(obj, status, origin) {
  return new Response(JSON.stringify(obj), { status, headers: { "Content-Type": "application/json", ...cors(origin) } });
}
