// Navigation and client-side search. Vanilla JavaScript; the search index is /search/index.json, written by the build.
(function () {
  "use strict";
  function q(sel, root) { return (root || document).querySelector(sel); }
  function esc(s) { return String(s).replace(/[&<>"']/g, function (c) { return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]; }); }

  // the header's search box submits to /search/?q=…; on the search page we filter the index
  var results = q("#results");
  if (results) {
    var params = new URLSearchParams(location.search);
    var query = (params.get("q") || "").trim();
    var box = q("header.top input[type=search]");
    if (box) box.value = query;
    fetch("/search/index.json").then(function (r) { return r.json(); }).then(function (index) {
      function run(text) {
        var terms = text.toLowerCase().split(/\s+/).filter(Boolean);
        if (!terms.length) { results.innerHTML = '<p class="muted">Type to search ' + index.length + ' entries: node ids and Statements, items, registry ids and short names, decisions, rounds, wiki pages.</p>'; return; }
        var hits = [];
        for (var i = 0; i < index.length; i++) {
          var e = index[i];
          var hay = (e.t + " " + e.k + " " + e.s).toLowerCase();
          var score = 0;
          for (var j = 0; j < terms.length; j++) {
            if (hay.indexOf(terms[j]) < 0) { score = -1; break; }
            if (e.t.toLowerCase().indexOf(terms[j]) >= 0) score += 2; else score += 1;
          }
          if (score > 0) hits.push([score, e]);
        }
        hits.sort(function (a, b) { return b[0] - a[0] || a[1].t.localeCompare(b[1].t); });
        var out = hits.slice(0, 200).map(function (h) {
          var e = h[1];
          return '<div class="hit"><a href="' + esc(e.u) + '">' + esc(e.t) + '</a><span class="k">' + esc(e.k) + '</span>' + (e.s ? '<br><span class="muted">' + esc(e.s.slice(0, 220)) + '</span>' : '') + '</div>';
        }).join("");
        results.innerHTML = (hits.length ? '<p class="muted">' + hits.length + ' hit' + (hits.length === 1 ? '' : 's') + (hits.length > 200 ? ', first 200 shown' : '') + '</p>' : '<p class="muted">Nothing matches.</p>') + out;
      }
      run(query);
      if (box) {
        box.addEventListener("input", function () { run(box.value); history.replaceState(null, "", "/search/?q=" + encodeURIComponent(box.value)); });
      }
    }).catch(function () { results.textContent = "The search index could not be loaded."; });
  }

  // keyboard: "/" focuses the search box
  document.addEventListener("keydown", function (ev) {
    if (ev.key === "/" && !/input|textarea/i.test(document.activeElement && document.activeElement.tagName)) {
      var b = q("header.top input[type=search]");
      if (b) { ev.preventDefault(); b.focus(); }
    }
  });

  // Record my assessment: compose the exact ledger event and hand it to GitHub's editor
  // on the author's own ledger. The site accepts no write. Exposed so the map can wire a
  // composer it injects into the read-more modal.
  window.wireAssess = function (root) {
    var as2 = q("section.assess", root);
    if (!as2 || as2.getAttribute("data-wired")) return;
    as2.setAttribute("data-wired", "1");
    var cfg = JSON.parse(as2.getAttribute("data-assess"));
    var fill = function (sel, opts) { opts.forEach(function (o) { var e = document.createElement("option"); e.value = o; e.textContent = o; sel.appendChild(e); }); };
    fill(q(".as-handle", as2), cfg.handles);
    fill(q(".as-stance", as2), cfg.stances);
    fill(q(".as-aspect", as2), cfg.aspects);
    q(".as-make", as2).addEventListener("click", function () {
      var handle = q(".as-handle", as2).value, stance = q(".as-stance", as2).value, aspect = q(".as-aspect", as2).value;
      var verbatim = q(".as-verbatim", as2).value.trim();
      var out = q(".as-out", as2), links = q(".as-links", as2);
      if (!verbatim) { out.hidden = false; out.textContent = "The rationale is required: the event carries your own words in verbatim."; return; }
      var today = new Date().toISOString().slice(0, 10);
      var ev = {
        id: handle.slice(1) + "-a-" + today.replace(/-/g, "") + "-" + cfg.node,
        by: handle, date: today, rule: cfg.rule, via: "site", version: cfg.version,
        kind: "assessment", target: { node: cfg.node }, stance: stance, aspect: aspect, verbatim: verbatim
      };
      if (cfg.active[handle]) ev.supersedes = cfg.active[handle];
      var line = JSON.stringify(ev);
      out.hidden = false; out.textContent = line;
      links.hidden = false;
      q(".as-edit", as2).href = "https://github.com/A-M-Berns/alignment-workspace/edit/main/graph/events/" + handle.slice(1) + ".jsonl";
      q(".as-copy", as2).onclick = function () {
        navigator.clipboard.writeText(line).then(function () { q(".as-copy", as2).textContent = "Copied"; });
      };
    });
  };
  window.wireAssess(document);
})();
