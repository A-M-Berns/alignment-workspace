// The map: one pannable, zoomable network — the concept registry of state/concepts.json. Small circles
// colour-coded by kind, force-laid and normalized into a world a bit larger than the stage; edges carry
// their relation and why on hover; clicking a node opens its popup (the entry's wiki page fragment where
// one exists, else /concepts/<id>/frag.html). /#c=<id> deep-links a concept. Vanilla JavaScript, SVG.
(function () {
  "use strict";
  var svg = document.getElementById("map");
  if (!svg) return;
  var NS = "http://www.w3.org/2000/svg";
  var seg = function (id) { return String(id).replace(/\//g, "--"); };
  var modal = document.getElementById("map-modal"), panelBody = document.getElementById("map-panel-body");
  var tip = document.getElementById("map-tip");
  var KIND_TONE = { goal: "bone", construction: "emerald", object: "sapphire", work: "amber", philosophy: "amethyst" };

  var DATA = null, tf = { k: 1, x: 0, y: 0 }, home = { k: 1, x: 0, y: 0 };
  var cam = document.createElementNS(NS, "g");
  svg.appendChild(cam);

  function el(tag, attrs, parent) {
    var e = document.createElementNS(NS, tag);
    for (var k in attrs) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }
  function esc(s) { return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;"); }
  function box() { var b = svg.getBoundingClientRect(); return { w: b.width, h: b.height, left: b.left, top: b.top }; }
  function applyTf() { cam.setAttribute("transform", "translate(" + tf.x + "," + tf.y + ") scale(" + tf.k + ")"); }
  function wrap(text, x, y, width, size, lines, anchor) {
    var t = el("text", { x: x, y: y, "font-size": size, "text-anchor": anchor || "start" });
    var per = Math.max(Math.floor(width / (size * 0.56)), 4), words = String(text).split(/\s+/), line = "", used = 0;
    for (var i = 0; i < words.length && used < lines; i++) {
      var cand = line ? line + " " + words[i] : words[i];
      if (cand.length > per && line) {
        el("tspan", { x: x, dy: used ? size * 1.15 : 0 }, t).textContent = used + 1 === lines ? line + "…" : line;
        used++; line = words[i];
      } else line = cand;
    }
    if (used < lines && line) el("tspan", { x: x, dy: used ? size * 1.15 : 0 }, t).textContent = line.length > per ? line.slice(0, per - 1) + "…" : line;
    return t;
  }

  // deterministic force layout, normalized into a world a bit larger than the stage
  function layout(items, links, w0, h0) {
    var n = items.length, pos = [], i, j;
    var spread = Math.max(1, Math.min(Math.sqrt(n) / 4.6, 1.6));
    var w = w0 * spread, h = h0 * spread;
    var R = Math.min(w, h) * 0.36;
    for (i = 0; i < n; i++) {
      var a = (i / n) * 2 * Math.PI + (i % 2) * 0.35;
      pos.push({ x: w / 2 + Math.cos(a) * R * (0.6 + 0.4 * ((i * 7919) % 97) / 97), y: h / 2 + Math.sin(a) * R * (0.6 + 0.4 * ((i * 104729) % 89) / 89), vx: 0, vy: 0 });
    }
    var idx = {};
    for (i = 0; i < n; i++) idx[items[i]] = i;
    var ls = [];
    for (i = 0; i < links.length; i++) {
      var ia = idx[links[i][0]], ib = idx[links[i][1]];
      if (ia !== undefined && ib !== undefined && ia !== ib) ls.push([ia, ib, Math.min(links[i][2], 8)]);
    }
    var rep = (w * h) / Math.max(n, 1) * 1.25;
    for (var it = 0; it < 260; it++) {
      for (i = 0; i < n; i++) for (j = i + 1; j < n; j++) {
        var dx = pos[j].x - pos[i].x, dy = pos[j].y - pos[i].y, d2 = dx * dx + dy * dy + 60;
        var f = Math.min(rep / d2, 5) * 0.016;
        pos[i].vx -= dx * f; pos[i].vy -= dy * f; pos[j].vx += dx * f; pos[j].vy += dy * f;
      }
      for (i = 0; i < ls.length; i++) {
        var p = pos[ls[i][0]], q = pos[ls[i][1]], k = (0.0012 + ls[i][2] * 0.0011);
        p.vx += (q.x - p.x) * k; p.vy += (q.y - p.y) * k; q.vx += (p.x - q.x) * k; q.vy += (p.y - q.y) * k;
      }
      for (i = 0; i < n; i++) {
        pos[i].vx += (w / 2 - pos[i].x) * 0.0022; pos[i].vy += (h / 2 - pos[i].y) * 0.0022;
        pos[i].x += Math.max(-10, Math.min(10, pos[i].vx)); pos[i].y += Math.max(-10, Math.min(10, pos[i].vy));
        pos[i].vx *= 0.8; pos[i].vy *= 0.8;
      }
    }
    var mx = 90, my = 80, minx = 1e9, miny = 1e9, maxx = -1e9, maxy = -1e9;
    for (i = 0; i < n; i++) {
      minx = Math.min(minx, pos[i].x); maxx = Math.max(maxx, pos[i].x);
      miny = Math.min(miny, pos[i].y); maxy = Math.max(maxy, pos[i].y);
    }
    var s = Math.min((w - 2 * mx) / Math.max(maxx - minx, 1), (h - 2 * my) / Math.max(maxy - miny, 1), 1.8);
    for (i = 0; i < n; i++) {
      pos[i].x = w / 2 + (pos[i].x - (minx + maxx) / 2) * s;
      pos[i].y = h / 2 + (pos[i].y - (miny + maxy) / 2) * s;
    }
    return { pos: pos, w: w, h: h };
  }

  function showTip(html, ev) {
    tip.innerHTML = html;
    tip.hidden = false;
    var b = box();
    var x = ev.clientX - b.left + 14, y = ev.clientY - b.top + 10;
    if (x > b.w - 280) x = Math.max(8, x - 300);
    if (y > b.h - 90) y -= 80;
    tip.style.left = x + "px";
    tip.style.top = y + "px";
  }
  function hideTip() { tip.hidden = true; }

  var at = {};
  function render() {
    cam.textContent = "";
    var b = box();
    var g = el("g", { "class": "scene" }, cam);
    el("rect", { x: -4 * b.w, y: -4 * b.h, width: 9 * b.w, height: 9 * b.h, "class": "backdrop" }, g);
    var items = DATA.items, links = DATA.links;
    var lay = layout(items, links, b.w, b.h);
    home = { k: 1, x: (b.w - lay.w) / 2, y: (b.h - lay.h) / 2 };
    tf = { k: home.k, x: home.x, y: home.y };
    applyTf();
    at = {};
    for (var i = 0; i < items.length; i++) at[items[i]] = lay.pos[i];
    var eg = el("g", { "class": "net-edges" }, g);
    links.forEach(function (L) {
      var a = at[L[0]], c = at[L[1]];
      if (!a || !c) return;
      var grp = el("g", { "class": "net-edge" }, eg);
      el("line", { x1: a.x, y1: a.y, x2: c.x, y2: c.y, "class": "wire", "stroke-width": Math.min(0.7 + L[2] * 0.25, 2.6) }, grp);
      el("line", { x1: a.x, y1: a.y, x2: c.x, y2: c.y, "class": "hit", "stroke-width": 11 }, grp);
      grp.addEventListener("mousemove", function (ev) {
        var ta = (DATA.concepts[L[0]] || {}).t || L[0], tb = (DATA.concepts[L[1]] || {}).t || L[1];
        showTip("<b>" + esc(ta) + " ↔ " + esc(tb) + "</b><br>" + esc(L[3] || ""), ev);
      });
      grp.addEventListener("mouseleave", hideTip);
    });
    var deg = {};
    links.forEach(function (L) { deg[L[0]] = (deg[L[0]] || 0) + 1; deg[L[1]] = (deg[L[1]] || 0) + 1; });
    items.forEach(function (id) {
      var m = DATA.concepts[id] || {}, p = at[id];
      var r = Math.min(6 + Math.sqrt((deg[id] || 0) + 1) * 1.6, 13);
      var cg = el("g", { "class": "dot tone-" + (KIND_TONE[m.k] || "amethyst") }, g);
      el("circle", { cx: p.x, cy: p.y, r: r + 5, "class": "halo" }, cg);
      el("circle", { cx: p.x, cy: p.y, r: r, "class": "core" }, cg);
      var t = el("text", { x: p.x, y: p.y + r + 13, "text-anchor": "middle", "font-size": 11 }, cg);
      t.textContent = (m.t || id).length > 34 ? (m.t || id).slice(0, 33) + "…" : (m.t || id);
      if (m.s) {
        var st = wrap(m.s, p.x, p.y + r + 25, 165, 8.5, 2, "middle");
        st.setAttribute("class", "nsub");
        cg.appendChild(st);
      }
      cg.addEventListener("mousemove", function (ev) {
        var kind = (DATA.kinds || {})[m.k] || m.k || "";
        showTip("<b>" + esc(m.t || id) + "</b>" + (kind ? ' <span class="muted">· ' + esc(kind) + "</span>" : "")
          + (m.s ? "<br>" + esc(m.s) : "") + (m.prs ? "<br><i>" + m.prs + " merged PR(s)</i>" : ""), ev);
      });
      cg.addEventListener("mouseleave", hideTip);
      cg.addEventListener("click", function (ev) { ev.stopPropagation(); hideTip(); openPanel(id); });
    });
  }

  function base(id) {
    var w = (DATA.concepts[id] || {}).w;
    return w ? "/wiki/" + seg(w) + "/" : "/concepts/" + seg(id) + "/";
  }
  function openPanel(id) {
    modal.classList.add("open");
    var m = DATA.concepts[id] || {};
    panelBody.innerHTML = '<p class="muted">Loading ' + esc(m.t || id) + "…</p>";
    fetch(base(id) + "frag.html").then(function (r) { if (!r.ok) throw 0; return r.text(); }).then(function (h) {
      panelBody.innerHTML = h + '<p class="muted popup-foot"><a href="' + base(id) + '">Open the full page →</a></p>';
    }).catch(function () { panelBody.innerHTML = '<p>Could not load; <a href="' + base(id) + '">open the page</a>.</p>'; });
    if (history.replaceState) history.replaceState(null, "", "/#c=" + seg(id));
  }
  function closePanel() {
    modal.classList.remove("open");
    panelBody.innerHTML = "";
    if (history.replaceState) history.replaceState(null, "", "/");
  }
  document.getElementById("map-panel-close").addEventListener("click", closePanel);
  modal.addEventListener("click", function (ev) { if (ev.target === modal) closePanel(); });

  function legend() {
    var lg = document.getElementById("map-legend");
    if (!lg) return;
    var K = DATA.kinds || {};
    var rows = [["bone", K.goal || "goal"], ["emerald", K.construction || "construction"], ["sapphire", K.object || "object"], ["amber", K.work || "work"], ["amethyst", K.philosophy || "philosophy"]];
    lg.innerHTML = rows.map(function (r) { return '<span class="lg tone-' + r[0] + '"><span class="dotc"></span>' + esc(r[1]) + "</span>"; }).join("");
  }

  // pan and zoom
  var drag = null;
  svg.addEventListener("pointerdown", function (ev) { drag = { x: ev.clientX, y: ev.clientY, tx: tf.x, ty: tf.y, moved: false }; svg.setPointerCapture(ev.pointerId); });
  svg.addEventListener("pointermove", function (ev) {
    if (!drag) return;
    if (Math.abs(ev.clientX - drag.x) + Math.abs(ev.clientY - drag.y) > 3) drag.moved = true;
    tf.x = drag.tx + ev.clientX - drag.x;
    tf.y = drag.ty + ev.clientY - drag.y;
    applyTf();
  });
  svg.addEventListener("pointerup", function () { setTimeout(function () { drag = null; }, 0); });
  svg.addEventListener("click", function (ev) { if (drag && drag.moved) ev.stopPropagation(); }, true);
  svg.addEventListener("wheel", function (ev) {
    ev.preventDefault();
    var b = box(), mx = ev.clientX - b.left, my = ev.clientY - b.top;
    var kNew = Math.max(0.3, Math.min(tf.k * Math.exp(-ev.deltaY * 0.0016), 9));
    tf.x = mx - (mx - tf.x) * (kNew / tf.k);
    tf.y = my - (my - tf.y) * (kNew / tf.k);
    tf.k = kNew;
    applyTf();
  }, { passive: false });
  document.addEventListener("keydown", function (ev) { if (ev.key === "Escape" && modal.classList.contains("open")) closePanel(); });
  document.getElementById("map-edges").addEventListener("change", function () {
    svg.classList.toggle("no-edges", !document.getElementById("map-edges").checked);
  });
  window.addEventListener("resize", render);

  fetch("/assets/map.json").then(function (r) { return r.json(); }).then(function (d) {
    DATA = d;
    legend();
    render();
    cam.style.opacity = 0;
    var t0 = null;
    (function fade(ts) {
      if (!t0) t0 = ts;
      var t = Math.min((ts - t0) / 400, 1);
      cam.style.opacity = t;
      if (t < 1) requestAnimationFrame(fade);
    })(performance.now());
    var m = location.hash.match(/#c=(.+)/);
    if (m) {
      var id = decodeURIComponent(m[1]).replace(/--/g, "/");
      if (DATA.concepts[id]) openPanel(id);
      else if (DATA.concepts[decodeURIComponent(m[1])]) openPanel(decodeURIComponent(m[1]));
    }
  }).catch(function () {
    svg.outerHTML = '<p>The map data could not be loaded; the <noscript>lines</noscript> listing below and the <a href="/search/">search</a> still work.</p>';
  });
})();
