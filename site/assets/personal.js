// The personal lens: relative dates, "new since your last visit" on the activity panel,
// the owner's workbench on their own profile, and the priorities page's "unscored by
// you" filter. Everything here reads public JSON and this browser's storage; the pages
// render identically for every signed-out reader.
(function () {
  "use strict";
  function esc(s) { return String(s).replace(/[&<>"']/g, function (c) { return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]; }); }

  // ISO dates become relative, the exact date on hover and focus
  function rel(iso) {
    var days = Math.floor((Date.now() - new Date(iso + "T00:00:00Z")) / 86400000);
    if (days <= 0) return "today";
    if (days === 1) return "1d ago";
    if (days < 30) return days + "d ago";
    if (days < 365) return Math.floor(days / 30) + "mo ago";
    return Math.floor(days / 365) + "y ago";
  }
  document.querySelectorAll("span.date").forEach(function (s) {
    var t = s.textContent.trim();
    if (/^\d{4}-\d{2}-\d{2}$/.test(t)) { s.title = t; s.setAttribute("tabindex", "0"); s.textContent = rel(t); }
  });

  // the activity panel marks rows published since this browser's last visit; the
  // boundary is captured once per visit, before the marks render
  if (location.pathname === "/activity/") {
    var KEY = "aw-activity-last";
    var last = null;
    try { last = localStorage.getItem(KEY); } catch (e) { /* unavailable */ }
    var maxd = "";
    var marked = 0;
    document.querySelectorAll(".panel ul.dense li").forEach(function (li) {
      var d = li.querySelector(".date");
      var iso = d && (d.title || d.textContent.trim());
      if (!iso || !/^\d{4}-\d{2}-\d{2}$/.test(iso)) return;
      if (iso > maxd) maxd = iso;
      if (last && iso > last) {
        var n = document.createElement("span");
        n.className = "new";
        n.textContent = "new";
        li.insertBefore(n, li.firstChild);
        marked++;
      }
    });
    if (marked) {
      var note = document.createElement("p");
      note.className = "muted";
      note.textContent = "new — published since your last visit here, on this browser.";
      var grid = document.querySelector(".panel-grid");
      if (grid) grid.parentNode.insertBefore(note, grid);
    }
    if (maxd) try { localStorage.setItem(KEY, maxd); } catch (e) { /* unavailable */ }
  }

  function account() { return window.AWAccount && window.AWAccount.get(); }
  function fetchJSON(u) { return fetch(u).then(function (r) { return r.json(); }); }

  // the owner's workbench, only on their own profile: pending submissions and what to
  // score next, drawn from the priorities ordering minus what they have scored
  var wb = document.getElementById("workbench");
  function workbench() {
    var a = account();
    if (!wb || !a || !a.handle || a.handle !== wb.getAttribute("data-handle")) return;
    Promise.all([fetchJSON("/assets/next.json"), fetchJSON("/assets/scores.json")]).then(function (res) {
      var mine = res[1][a.handle] || {};
      var recs = (window.AWAccount.receipts() || []);
      var pend = recs.map(function (r) {
        var t = r.target || {};
        return '<li>' + esc(String(t.concept || t.node || "")) + ' · ' + esc(String(r.axis)) + ' ' + esc(String(r.score)) +
          ' — <a href="' + esc(r.pr) + '" target="_blank" rel="noopener">awaiting merge</a></li>';
      });
      var sug = [];
      res[0].some(function (c) {
        var scored = mine["concepts:" + c.id] || {};
        c.axes.forEach(function (ax) {
          if (sug.length >= 3 || scored[ax] != null) return;
          if (recs.some(function (r) { return (r.target || {}).concept === c.id && r.axis === ax; })) return;
          sug.push('<li><a href="/concepts/' + esc(c.id) + '/">' + esc(c.t) + '</a> · ' + esc(ax) + '</li>');
        });
        return sug.length >= 3;
      });
      wb.innerHTML = '<section class="panel"><h2>Your workbench</h2>'
        + '<h3>Pending submissions</h3>'
        + (pend.length ? '<ul class="dense">' + pend.join("") + '</ul><p class="muted">Remembered on this browser; the pull requests are on GitHub.</p>'
                       : '<p class="muted">No submissions remembered on this browser.</p>')
        + '<h3>What to score next</h3>'
        + (sug.length ? '<ul class="dense">' + sug.join("") + '</ul>' : '<p class="muted">Every axis the ordering ranks carries your score.</p>')
        + '<p class="muted"><a href="/priorities/?mine=1">Everything unscored by you</a>.</p></section>';
      wb.hidden = false;
    }).catch(function () { /* the public page stands on its own */ });
  }
  workbench();
  document.addEventListener("aw-account-ready", workbench);

  // /priorities/: filter to the concepts with an axis you have not scored
  var mineBtn = document.getElementById("prio-mine");
  if (mineBtn) {
    var on = false;
    function apply(scores) {
      var a = account();
      var mine = (a && a.handle && scores[a.handle]) || {};
      var recs = (window.AWAccount && window.AWAccount.receipts()) || [];
      var kept = 0;
      document.querySelectorAll("li.prio").forEach(function (li) {
        var cid = li.getAttribute("data-cid");
        var axes = (li.getAttribute("data-axes") || "").split(",").filter(Boolean);
        var scored = mine["concepts:" + cid] || {};
        var open = axes.filter(function (ax) {
          return scored[ax] == null && !recs.some(function (r) { return (r.target || {}).concept === cid && r.axis === ax; });
        });
        var chip = li.querySelector(".prio-unscored");
        if (chip) chip.remove();
        if (!on) { li.hidden = false; return; }
        li.hidden = !open.length;
        if (open.length) {
          kept++;
          chip = document.createElement("p");
          chip.className = "prio-unscored muted";
          chip.textContent = "you haven’t scored: " + open.join(", ");
          li.appendChild(chip);
        }
      });
      mineBtn.classList.toggle("on", on);
      document.querySelector(".prio-mine-note").textContent = on ? kept + " concepts carry an axis you haven’t scored." : "";
    }
    function arm() {
      var a = account();
      if (!a || !a.handle) return;
      mineBtn.hidden = false;
      fetchJSON("/assets/scores.json").then(function (scores) {
        mineBtn.onclick = function () { on = !on; apply(scores); };
        if (new URLSearchParams(location.search).get("mine") === "1") { on = true; apply(scores); }
      }).catch(function () { /* the filter just stays off */ });
    }
    arm();
    document.addEventListener("aw-account-ready", arm);
  }
})();
