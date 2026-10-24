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
})();
