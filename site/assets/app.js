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

  // Scoring is a move: pick a number in the hero, give one sentence, sign and copy the
  // exact ledger event into your own GitHub ledger. Vouch or challenge is derived from
  // the picked number against the standing score. The site accepts no write. Exposed so
  // the map can wire the block it injects into the read-more modal.
  window.wireAssess = function (root) {
    var ed = q(".assess-editor[data-assess]", root);
    if (!ed || ed.getAttribute("data-wired")) return;
    ed.setAttribute("data-wired", "1");
    var cfg = JSON.parse(ed.getAttribute("data-assess"));
    var scope = root && root.querySelectorAll ? root : document;
    var rc = ed.nextElementSibling; // .assess-receipt
    var handleSel = q(".as-handle", ed);
    cfg.handles.forEach(function (o) { var e = document.createElement("option"); e.value = o; e.textContent = o; handleSel.appendChild(e); });
    try {
      var saved = localStorage.getItem("aw-handle");
      if (saved && cfg.handles.indexOf(saved) >= 0) handleSel.value = saved;
      handleSel.addEventListener("change", function () { localStorage.setItem("aw-handle", handleSel.value); });
    } catch (e) { /* storage may be unavailable */ }
    // a signed-in reader's handle takes the select
    function adoptAccount() {
      var a = window.AWAccount && window.AWAccount.get();
      if (a && a.handle && cfg.handles.indexOf(a.handle) >= 0) handleSel.value = a.handle;
    }
    adoptAccount();
    document.addEventListener("aw-account-ready", adoptAccount);
    var picked = null; // {axis, score}
    function headline(axis, n) {
      var st = cfg.standing[axis];
      if (st.contested) return "Your " + axis + " score: " + n;
      if (st.d === "–") return "The first " + axis + " score: " + n;
      if (st.ai) return "The first human " + axis + " score: " + n + ' <span class="stands-at">AI score stands at ' + st.d + "*</span>";
      if (String(n) === st.d) return "Support " + axis + " " + st.d;
      return "Challenge " + axis + " " + st.d + " with " + n;
    }
    function openEditor(axis, score) {
      picked = { axis: axis, score: score };
      scope.querySelectorAll(".seg.sel").forEach(function (s) { s.classList.remove("sel"); });
      var seg = scope.querySelector('.seg[data-axis="' + axis + '"][data-score="' + score + '"]');
      if (seg) seg.classList.add("sel");
      q(".ed-head", ed).innerHTML = headline(axis, score); // built from fixed strings and the build's own numbers
      var prev = cfg.active[handleSel.value + "|" + axis];
      q(".ed-note", ed).textContent = prev ? "This replaces your earlier " + axis + " score; everyone else's stays." : "";
      ed.hidden = false; rc.hidden = true;
      q(".as-verbatim", ed).focus();
      ed.scrollIntoView({ block: "nearest", behavior: "smooth" });
    }
    scope.querySelectorAll(".seg, button.hx-num").forEach(function (b) {
      b.addEventListener("click", function () {
        openEditor(b.getAttribute("data-axis"), parseInt(b.getAttribute("data-score"), 10));
      });
    });
    q(".as-make", ed).addEventListener("click", function () {
      if (!picked) return;
      var handle = handleSel.value;
      var verbatim = q(".as-verbatim", ed).value.trim();
      if (!verbatim) { q(".ed-note", ed).textContent = "The rationale is required: the event carries your own words. One clear sentence is enough."; return; }
      var today = new Date().toISOString().slice(0, 10);
      var tid = cfg.target.node || cfg.target.concept;
      var ev = {
        id: handle.slice(1) + "-a-" + today.replace(/-/g, "") + "-" + picked.axis + "-" + tid,
        by: handle, date: today, rule: cfg.rule, via: "site", version: cfg.version,
        kind: "assessment", target: cfg.target, axis: picked.axis, score: picked.score, verbatim: verbatim
      };
      if (cfg.active[handle + "|" + picked.axis]) ev.supersedes = cfg.active[handle + "|" + picked.axis];
      var line = JSON.stringify(ev);
      q(".rc-line", rc).textContent = handle + " · " + picked.axis + " " + picked.score + " — “" + verbatim + "”";
      q(".as-out", rc).textContent = line;
      q(".as-edit", rc).href = "https://github.com/A-M-Berns/alignment-workspace/edit/main/graph/events/" + handle.slice(1) + ".jsonl";
      q(".rc-status", rc).textContent = "Prepared locally — not yet submitted.";
      q(".as-copy", rc).textContent = "Copy event";
      // signed in as this handle: the receipt submits itself as a pull request
      var old = q(".as-pr", rc);
      if (old) old.remove();
      var a = window.AWAccount && window.AWAccount.get();
      if (a && a.token && a.handle === handle) {
        var pr = document.createElement("button");
        pr.type = "button"; pr.className = "as-pr"; pr.textContent = "Open the pull request";
        q(".as-copy", rc).parentNode.insertBefore(pr, q(".as-copy", rc));
        pr.onclick = function () {
          pr.disabled = true;
          window.AWAccount.submit(line, handle, function (t) { q(".rc-status", rc).textContent = t; })
            .then(function (url) {
              q(".rc-status", rc).innerHTML = 'Submitted — <a href="' + esc(url) + '" target="_blank" rel="noopener">the pull request</a> publishes on merge.';
            })
            .catch(function (e) {
              pr.disabled = false;
              q(".rc-status", rc).textContent = "Submission failed (" + String(e.message || e) + ") — the copy flow below still works.";
            });
        };
      }
      ed.hidden = true; rc.hidden = false;
      q(".as-copy", rc).onclick = function () {
        navigator.clipboard.writeText(line).then(function () {
          q(".as-copy", rc).textContent = "Copied ✓";
          q(".rc-status", rc).textContent = "Copied — paste the line at the end of your ledger on GitHub and commit; it publishes on the next build.";
        });
      };
    });
  };
  window.wireAssess(document);
})();
