// The map: one full-viewport network of the concept registry, organized by what feeds the goals.
// Nodes sit in layers by their distance to the program (prior work and mathematical objects left,
// constructions mid, the lines and the program right); directed edges carry small arrows toward what
// they feed. Clicking a node or an edge opens a small card; "Read more" opens the fullscreen view
// (the entry's wiki fragment or /concepts/<id>/frag.html) with an ×. /#c=<id> deep-links a concept.
(function () {
  "use strict";
  var svg = document.getElementById("map");
  if (!svg) return;
  var NS = "http://www.w3.org/2000/svg";
  var seg = function (id) { return String(id).replace(/\//g, "--"); };
  var modal = document.getElementById("map-modal"), panelBody = document.getElementById("map-panel-body");
  var card = document.getElementById("map-card");
  var KIND_TONE = { goal: "bone", construction: "emerald", object: "sapphire", work: "amber", philosophy: "amethyst" };

  var DATA = null, tf = { k: 1, x: 0, y: 0 }, home = { k: 1, x: 0, y: 0 };
  var defs = document.createElementNS(NS, "defs");
  svg.appendChild(defs);
  var cam = document.createElementNS(NS, "g");
  svg.appendChild(cam);
  var mk = document.createElementNS(NS, "marker");
  mk.setAttribute("id", "arrow");
  mk.setAttribute("viewBox", "0 0 8 8");
  mk.setAttribute("refX", "7"); mk.setAttribute("refY", "4");
  mk.setAttribute("markerWidth", "7"); mk.setAttribute("markerHeight", "7");
  mk.setAttribute("orient", "auto-start-reverse");
  var mkp = document.createElementNS(NS, "path");
  mkp.setAttribute("d", "M0,0.6 L7.4,4 L0,7.4 z");
  mkp.setAttribute("class", "arrowhead");
  mk.appendChild(mkp);
  defs.appendChild(mk);

  function el(tag, attrs, parent) {
    var e = document.createElementNS(NS, tag);
    for (var k in attrs) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }
  function esc(s) { return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;"); }
  function box() { var b = svg.getBoundingClientRect(); return { w: b.width, h: b.height, left: b.left, top: b.top }; }
  var zoomed = false;
  function applyTf() {
    cam.setAttribute("transform", "translate(" + tf.x + "," + tf.y + ") scale(" + tf.k + ")");
    if (!zoomed && tf.k >= 1.5) { zoomed = true; svg.classList.add("zoomed"); }
    else if (zoomed && tf.k <= 1.35) { zoomed = false; svg.classList.remove("zoomed"); }
  }
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

  // layered layout: x anchored by goal distance (goals right), y settled by forces
  function layout(items, links, w0, h0) {
    var n = items.length, i, j;
    var w = w0 * 1.5, h = h0 * 1.25;
    var dmax = 1;
    items.forEach(function (id) { dmax = Math.max(dmax, (DATA.concepts[id] || {}).d || 0); });
    var xm = 120, pos = [], idx = {};
    for (i = 0; i < n; i++) {
      var m = DATA.concepts[items[i]] || {}, dd = m.d || 0;
      var xT = xm + (1 - dd / dmax) * (w - 2 * xm);
      pos.push({ x: xT, xT: xT, y: h * (0.15 + 0.7 * (((i * 7919) % 97) / 97)), vx: 0, vy: 0 });
      idx[items[i]] = i;
    }
    var ls = [];
    for (i = 0; i < links.length; i++) {
      var ia = idx[links[i][0]], ib = idx[links[i][1]];
      if (ia !== undefined && ib !== undefined && ia !== ib) ls.push([ia, ib]);
    }
    var rep = (w * h) / Math.max(n, 1) * 1.1;
    for (var it = 0; it < 300; it++) {
      for (i = 0; i < n; i++) for (j = i + 1; j < n; j++) {
        var dx = pos[j].x - pos[i].x, dy = pos[j].y - pos[i].y, d2 = dx * dx + dy * dy + 60;
        var f = Math.min(rep / d2, 5) * 0.016;
        pos[i].vx -= dx * f * 0.35; pos[i].vy -= dy * f; pos[j].vx += dx * f * 0.35; pos[j].vy += dy * f;
      }
      for (i = 0; i < ls.length; i++) {
        var p = pos[ls[i][0]], q = pos[ls[i][1]];
        p.vy += (q.y - p.y) * 0.004; q.vy += (p.y - q.y) * 0.004;
      }
      for (i = 0; i < n; i++) {
        pos[i].vx += (pos[i].xT - pos[i].x) * 0.06;
        pos[i].vy += (h / 2 - pos[i].y) * 0.0024;
        pos[i].x += Math.max(-9, Math.min(9, pos[i].vx)); pos[i].y += Math.max(-9, Math.min(9, pos[i].vy));
        pos[i].vx *= 0.78; pos[i].vy *= 0.78;
      }
    }
    var ym = 70, miny = 1e9, maxy = -1e9;
    for (i = 0; i < n; i++) { miny = Math.min(miny, pos[i].y); maxy = Math.max(maxy, pos[i].y); }
    var s = Math.min((h - 2 * ym) / Math.max(maxy - miny, 1), 1.6);
    for (i = 0; i < n; i++) pos[i].y = h / 2 + (pos[i].y - (miny + maxy) / 2) * s;
    return { pos: pos, w: w, h: h };
  }

  var at = {}, radius = {};
  function render() {
    cam.textContent = "";
    hideCard();
    var b = box();
    var g = el("g", { "class": "scene" }, cam);
    el("rect", { x: -4 * b.w, y: -4 * b.h, width: 9 * b.w, height: 9 * b.h, "class": "backdrop" }, g);
    var items = DATA.items, links = DATA.links;
    var lay = layout(items, links, b.w, b.h);
    home = { k: 1, x: (b.w - lay.w) / 2, y: (b.h - lay.h) / 2 };
    tf = { k: home.k, x: home.x, y: home.y };
    applyTf();
    at = {}; radius = {};
    var deg = {};
    links.forEach(function (L) { deg[L[0]] = (deg[L[0]] || 0) + 1; deg[L[1]] = (deg[L[1]] || 0) + 1; });
    for (var i = 0; i < items.length; i++) {
      at[items[i]] = lay.pos[i];
      radius[items[i]] = Math.min(6 + Math.sqrt((deg[items[i]] || 0) + 1) * 1.6, 13);
    }
    var eg = el("g", { "class": "net-edges" }, g);
    var incident = {};
    links.forEach(function (L) {
      var a = at[L[0]], c = at[L[1]];
      if (!a || !c) return;
      var dx = c.x - a.x, dy = c.y - a.y, len = Math.sqrt(dx * dx + dy * dy) || 1;
      var ra = radius[L[0]] + 3, rc = radius[L[1]] + (L[5] ? 3 : 8);
      var x1 = a.x + dx / len * ra, y1 = a.y + dy / len * ra;
      var x2 = c.x - dx / len * rc, y2 = c.y - dy / len * rc;
      var grp = el("g", { "class": "net-edge" }, eg);
      var wire = el("line", { x1: x1, y1: y1, x2: x2, y2: y2, "class": "wire", "stroke-width": Math.min(0.75 + L[2] * 0.08, 1.3) }, grp);
      if (!L[5]) wire.setAttribute("marker-end", "url(#arrow)");
      el("line", { x1: a.x, y1: a.y, x2: c.x, y2: c.y, "class": "hit", "stroke-width": 12 }, grp);
      grp.addEventListener("click", function (ev) { ev.stopPropagation(); edgeCard(L, ev); });
      (incident[L[0]] = incident[L[0]] || []).push(grp);
      (incident[L[1]] = incident[L[1]] || []).push(grp);
    });
    items.forEach(function (id) {
      var m = DATA.concepts[id] || {}, p = at[id], r = radius[id];
      var cg = el("g", { "class": "dot tone-" + (KIND_TONE[m.k] || "amethyst") }, g);
      el("circle", { cx: p.x, cy: p.y, r: Math.max(r * 1.8, 16), "class": "hitc" }, cg);
      el("circle", { cx: p.x, cy: p.y, r: r * 1.8, "class": "halo" }, cg);
      el("circle", { cx: p.x, cy: p.y, r: r, "class": "core" }, cg);
      if (m.k === "goal") el("circle", { cx: p.x, cy: p.y, r: r + 3, "class": "ring" }, cg);
      var t = el("text", { x: p.x, y: p.y + r + 14, "text-anchor": "middle", "font-size": 11 }, cg);
      t.textContent = (m.t || id).length > 34 ? (m.t || id).slice(0, 33) + "…" : (m.t || id);
      if (m.s) {
        var st = wrap(m.s, p.x, p.y + r + 27, 190, 10.5, 2, "middle");
        st.setAttribute("class", "nsub");
        cg.appendChild(st);
      }
      cg.addEventListener("mouseenter", function () { (incident[id] || []).forEach(function (e2) { e2.classList.add("lit"); }); });
      cg.addEventListener("mouseleave", function () { (incident[id] || []).forEach(function (e2) { e2.classList.remove("lit"); }); });
      cg.addEventListener("click", function (ev) { ev.stopPropagation(); nodeCard(id, ev); });
    });
  }

  // the small card: a node's or an edge's summary in place; "Read more" opens the fullscreen view
  function placeCard(ev) {
    var b = box();
    card.hidden = false;
    var x = ev.clientX - b.left + 14, y = ev.clientY - b.top + 10;
    var cw = Math.min(340, b.w - 24), ch = card.offsetHeight || 220;
    if (x + cw > b.w - 12) x = Math.max(10, ev.clientX - b.left - cw - 14);
    if (y + ch > b.h - 12) y = Math.max(10, b.h - ch - 14);
    card.style.left = x + "px";
    card.style.top = y + "px";
  }
  function hideCard() { card.hidden = true; card.innerHTML = ""; }
  function kindLabel(k) { return (DATA.kinds || {})[k] || k || ""; }
  function nodeCard(id, ev) {
    var m = DATA.concepts[id] || {};
    card.innerHTML = '<p class="card-head">' + esc(m.t || id) + ' <span class="kind">' + esc(kindLabel(m.k)) + "</span></p>"
      + (m.s ? "<p class=\"card-blurb\">" + esc(m.s) + "</p>" : "")
      + '<p class="card-meta muted">' + (m.prs ? m.prs + " merged PR(s) · " : "") + (m.w ? "wiki page" : "registry entry") + "</p>"
      + '<p class="card-actions"><button data-act="more">Read more</button><a href="' + base(id) + '">Open page →</a></p>';
    card.querySelector("[data-act=more]").addEventListener("click", function () { hideCard(); openFull(id); });
    placeCard(ev);
  }
  function edgeCard(L, ev) {
    var a = DATA.concepts[L[0]] || {}, c = DATA.concepts[L[1]] || {};
    var arrow = L[5] ? " ↔ " : " → ";
    card.innerHTML = '<p class="card-head">' + esc(a.t || L[0]) + '<span class="muted">' + arrow + "</span>" + esc(c.t || L[1]) + "</p>"
      + '<p class="card-rels">' + (L[3] || []).map(function (r) { return '<span class="tag">' + esc(r) + "</span>"; }).join(" ") + "</p>"
      + (L[4] ? "<p class=\"card-blurb\">" + esc(L[4]) + "</p>" : "")
      + '<p class="card-actions"><button data-n="0">' + esc(a.t || L[0]) + '</button><button data-n="1">' + esc(c.t || L[1]) + "</button></p>";
    card.querySelector("[data-n='0']").addEventListener("click", function (e2) { nodeCard(L[0], e2); });
    card.querySelector("[data-n='1']").addEventListener("click", function (e2) { nodeCard(L[1], e2); });
    placeCard(ev);
  }

  function base(id) {
    var w = (DATA.concepts[id] || {}).w;
    return w ? "/wiki/" + seg(w) + "/" : "/concepts/" + seg(id) + "/";
  }
  function openFull(id) {
    modal.classList.add("open");
    var m = DATA.concepts[id] || {};
    panelBody.innerHTML = '<p class="muted">Loading ' + esc(m.t || id) + "…</p>";
    fetch(base(id) + "frag.html").then(function (r) { if (!r.ok) throw 0; return r.text(); }).then(function (h) {
      panelBody.innerHTML = h + '<p class="muted popup-foot"><a href="' + base(id) + '">Open the full page →</a></p>';
    }).catch(function () { panelBody.innerHTML = '<p>Could not load; <a href="' + base(id) + '">open the page</a>.</p>'; });
    if (history.replaceState) history.replaceState(null, "", "/#c=" + seg(id));
  }
  function closeFull() {
    modal.classList.remove("open");
    panelBody.innerHTML = "";
    if (history.replaceState) history.replaceState(null, "", "/");
  }
  document.getElementById("map-panel-close").addEventListener("click", closeFull);
  modal.addEventListener("click", function (ev) { if (ev.target === modal) closeFull(); });

  function legend() {
    var lg = document.getElementById("map-legend");
    if (!lg) return;
    var K = DATA.kinds || {};
    var rows = [["bone", K.goal || "goal"], ["emerald", K.construction || "construction"], ["sapphire", K.object || "object"], ["amber", K.work || "work"], ["amethyst", K.philosophy || "philosophy"]];
    lg.innerHTML = rows.map(function (r) { return '<span class="lg tone-' + r[0] + '"><span class="dotc"></span>' + esc(r[1]) + "</span>"; }).join("");
  }

  // pan and zoom; a plain click on the backdrop closes the card
  // capture the pointer only once a drag has actually started: a captured pointer retargets the
  // click to the svg itself, which would swallow every node and edge click
  var drag = null;
  svg.addEventListener("pointerdown", function (ev) { drag = { id: ev.pointerId, x: ev.clientX, y: ev.clientY, tx: tf.x, ty: tf.y, moved: false }; });
  svg.addEventListener("pointermove", function (ev) {
    if (!drag) return;
    if (!drag.moved && Math.abs(ev.clientX - drag.x) + Math.abs(ev.clientY - drag.y) > 4) {
      drag.moved = true;
      try { svg.setPointerCapture(drag.id); } catch (e) { }
    }
    if (!drag.moved) return;
    tf.x = drag.tx + ev.clientX - drag.x;
    tf.y = drag.ty + ev.clientY - drag.y;
    applyTf();
  });
  svg.addEventListener("pointerup", function () { setTimeout(function () { drag = null; }, 0); });
  svg.addEventListener("click", function (ev) {
    if (drag && drag.moved) { ev.stopPropagation(); return; }
    hideCard();
  }, true);
  svg.addEventListener("wheel", function (ev) {
    ev.preventDefault();
    var b = box(), mx = ev.clientX - b.left, my = ev.clientY - b.top;
    var kNew = Math.max(0.3, Math.min(tf.k * Math.exp(-ev.deltaY * 0.0016), 9));
    tf.x = mx - (mx - tf.x) * (kNew / tf.k);
    tf.y = my - (my - tf.y) * (kNew / tf.k);
    tf.k = kNew;
    applyTf();
  }, { passive: false });
  document.addEventListener("keydown", function (ev) {
    if (ev.key !== "Escape") return;
    if (modal.classList.contains("open")) closeFull();
    else hideCard();
  });
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
      if (DATA.concepts[id]) openFull(id);
      else if (DATA.concepts[decodeURIComponent(m[1])]) openFull(decodeURIComponent(m[1]));
    }
  }).catch(function () {
    svg.outerHTML = '<p>The map data could not be loaded; the <noscript>lines</noscript> listing below and the <a href="/search/">search</a> still work.</p>';
  });
})();
