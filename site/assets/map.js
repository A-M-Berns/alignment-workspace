// The map canvas: each level is a pannable, zoomable network graph — small circular nodes, force-laid,
// edges hoverable for a summary of the relationship. The concepts view (the default) is the wiki as one
// network; clicking any node opens its popup (/wiki/<Page>/frag.html, /n/<id>/frag.html or
// /prs/<n>/frag.html). In the containment views a node with contents descends one level with an animated
// zoom; esc, ctrl-click, wheel-out past the minimum zoom, or the breadcrumb backs out.
(function () {
  "use strict";
  var svg = document.getElementById("map");
  if (!svg) return;
  var NS = "http://www.w3.org/2000/svg";
  var seg = function (id) { return String(id).replace(/\//g, "--"); };
  var modal = document.getElementById("map-modal"), panelBody = document.getElementById("map-panel-body");
  var tip = document.getElementById("map-tip");
  var crumbsEl = document.getElementById("map-crumbs"), viewsEl = document.getElementById("map-views");
  var VIEW_LABEL = { concepts: "concepts", concept: "goals", rounds: "rounds", prs: "merged work" };
  var KIND_TONE = { goal: "bone", construction: "emerald", object: "sapphire", work: "amber", philosophy: "amethyst" };

  var DATA = null, view = "concepts", root = null, path = [], animating = false;
  var home = { k: 1, x: 0, y: 0, o: 1 };
  var cam = document.createElementNS(NS, "g");
  svg.appendChild(cam);
  var tf = { k: 1, x: 0, y: 0 };

  function el(tag, attrs, parent) {
    var e = document.createElementNS(NS, tag);
    for (var k in attrs) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }
  function ease(t) { return t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2; }
  function esc(s) { return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;"); }
  function box() { var b = svg.getBoundingClientRect(); return { w: b.width, h: b.height, left: b.left, top: b.top }; }
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
  function applyTf() { cam.setAttribute("transform", "translate(" + tf.x + "," + tf.y + ") scale(" + tf.k + ")"); }

  function build(viewName) {
    root = JSON.parse(JSON.stringify(DATA.views[viewName]));
    (function link(t, p) { t.parent = p; t.wt = t.ch.length ? 0 : 1; for (var i = 0; i < t.ch.length; i++) { link(t.ch[i], t); t.wt += t.ch[i].wt; } t.wt += t.ch.length ? 1 : 0; })(root, null);
  }
  function label(t) {
    if (t.kind === "pr") { var m = DATA.prmeta[t.id.slice(1)] || {}; return "#" + t.id.slice(1) + " " + (m.t || ""); }
    if (t.kind === "concept") return (DATA.concepts[t.id] || {}).t || t.id;
    if (t.kind === "topic") return t.id.replace(/-/g, " ");
    return t.id;
  }
  function tone(t) {
    var n = DATA.nodes[t.id];
    if (t.kind === "concept") return KIND_TONE[(DATA.concepts[t.id] || {}).k] || "amethyst";
    if (t.kind === "pr") return "pr";
    if (t.kind === "topic") return "amethyst";
    if (!n) return "group";
    if (n.c === "lean-proved") return "emerald";
    if (n.c === "enumeration-verified" || n.c === "witness-checked") return "sapphire";
    if (n.c === "test-supported" || n.c === "contributor-checked") return "amber";
    if (n.c) return "slate";
    if (n.i) return "garnet";
    if (n.f) return "bone";
    return "plain";
  }

  // deterministic force layout; the world grows with the node count, so a level needn't fit the stage.
  // No walls: the sim runs free and the finished layout is normalized into the world box, so nothing piles
  // at a border.
  function network(items, links, w0, h0) {
    var n = items.length, pos = [], i, j;
    var spread = Math.max(1, Math.min(Math.sqrt(n) / 4.6, 1.6));
    var w = w0 * spread, h = h0 * spread;
    var R = Math.min(w, h) * (n > 20 ? 0.4 : 0.3);
    for (i = 0; i < n; i++) {
      var a = (i / n) * 2 * Math.PI + (i % 2) * 0.35;
      pos.push({ x: w / 2 + Math.cos(a) * R * (0.6 + 0.4 * ((i * 7919) % 97) / 97), y: h / 2 + Math.sin(a) * R * (0.6 + 0.4 * ((i * 104729) % 89) / 89), vx: 0, vy: 0 });
    }
    var idx = {};
    for (i = 0; i < n; i++) idx[items[i].id] = i;
    var ls = [];
    for (i = 0; i < links.length; i++) {
      var ia = idx[links[i].a], ib = idx[links[i].b];
      if (ia !== undefined && ib !== undefined && ia !== ib) ls.push([ia, ib, Math.min(links[i].w || 1, 8)]);
    }
    var rep = (w * h) / Math.max(n, 1) * 1.25;
    var iters = n > 160 ? 120 : 260;
    for (var it = 0; it < iters; it++) {
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
    // normalize: uniform-scale the finished layout into the world box, centred, margins clear of the chrome
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

  // ancestor of `id` among focus.ch
  function childAncestor(focus, id) {
    var map = focus._desc;
    if (!map) {
      map = focus._desc = {};
      for (var i = 0; i < focus.ch.length; i++) {
        (function mark(t, top) { if (!(t.id in map)) map[t.id] = top; for (var j = 0; j < t.ch.length; j++) mark(t.ch[j], top); })(focus.ch[i], focus.ch[i]);
      }
    }
    return map[id] || null;
  }

  function levelLinks(focus) {
    if (focus === root && view === "concepts") {
      return (DATA.clinks || []).map(function (L) { return { a: L[0], b: L[1], w: L[2], tip: L[3] }; });
    }
    var pairs = {}, i;
    for (i = 0; i < DATA.edges.length; i++) {
      var e = DATA.edges[i], a = childAncestor(focus, e[0]), b = childAncestor(focus, e[1]);
      if (!a || !b || a === b) continue;
      var key = a.id < b.id ? a.id + "\u0000" + b.id : b.id + "\u0000" + a.id;
      var p = pairs[key] = pairs[key] || { a: a.id, b: b.id, w: 0, kinds: {}, ex: [] };
      p.w++;
      p.kinds[e[2] || "part"] = (p.kinds[e[2] || "part"] || 0) + 1;
      if (p.ex.length < 3) p.ex.push(e[0] + " → " + e[1]);
    }
    var out = [];
    for (var k in pairs) {
      var q = pairs[k], kb = [];
      for (var kk in q.kinds) kb.push(q.kinds[kk] + " " + kk);
      out.push({ a: q.a, b: q.b, w: q.w, tip: kb.join(", ") + (q.ex.length ? " — e.g. " + q.ex.join("; ") : "") });
    }
    return out;
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

  function render(focus) {
    cam.textContent = "";
    var b = box();
    var g = el("g", { "class": "scene" }, cam);
    el("rect", { x: -4 * b.w, y: -4 * b.h, width: 9 * b.w, height: 9 * b.h, "class": "backdrop" }, g);
    var items = focus.ch, links = levelLinks(focus);
    var lay = network(items, links, b.w, b.h);
    var pos = lay.pos;
    home = { k: 1, x: (b.w - lay.w) / 2, y: (b.h - lay.h) / 2, o: 1 };
    tf = { k: home.k, x: home.x, y: home.y };
    applyTf();
    var at = {};
    for (var i = 0; i < items.length; i++) { items[i].x = pos[i].x; items[i].y = pos[i].y; at[items[i].id] = pos[i]; }
    var eg = el("g", { "class": "net-edges" }, g);
    links.forEach(function (L) {
      var a = at[L.a], c = at[L.b];
      if (!a || !c) return;
      var grp = el("g", { "class": "net-edge" }, eg);
      el("line", { x1: a.x, y1: a.y, x2: c.x, y2: c.y, "class": "wire", "stroke-width": Math.min(0.7 + L.w * 0.3, 3) }, grp);
      el("line", { x1: a.x, y1: a.y, x2: c.x, y2: c.y, "class": "hit", "stroke-width": 11 }, grp);
      grp.addEventListener("mousemove", function (ev) {
        showTip("<b>" + esc(label({ id: L.a, kind: items[0].kind })) + " ↔ " + esc(label({ id: L.b, kind: items[0].kind })) + "</b><br>" + esc(L.tip || (L.w + " connection(s)")), ev);
      });
      grp.addEventListener("mouseleave", hideTip);
    });
    var showLabels = items.length <= 90;
    items.forEach(function (c) {
      var deg = 0;
      links.forEach(function (L) { if (L.a === c.id || L.b === c.id) deg++; });
      var r = Math.min(6 + Math.sqrt(deg + 1) * 1.6, 13);
      var cg = el("g", { "class": "dot tone-" + tone(c) + ((DATA.nodes[c.id] || {}).d ? " drafted" : "") }, g);
      el("circle", { cx: c.x, cy: c.y, r: r + 5, "class": "halo" }, cg);
      el("circle", { cx: c.x, cy: c.y, r: r, "class": "core" }, cg);
      if (showLabels) {
        var t = el("text", { x: c.x, y: c.y + r + 13, "text-anchor": "middle", "font-size": 11 }, cg);
        var s = label(c);
        t.textContent = s.length > 34 ? s.slice(0, 33) + "…" : s;
        var n2 = DATA.nodes[c.id] || {}, cm2 = DATA.concepts[c.id] || {};
        var sum = c.kind === "concept" ? (cm2.s || "") : c.kind === "pr" ? ((DATA.prmeta[c.id.slice(1)] || {}).d || "") : (n2.q || n2.s || "");
        if (sum) {
          var st = wrap(sum, c.x, c.y + r + 25, 165, 8.5, 2, "middle");
          st.setAttribute("class", "nsub");
          cg.appendChild(st);
        }
      }
      cg.addEventListener("mousemove", function (ev) {
        var n = DATA.nodes[c.id] || {};
        var cm = DATA.concepts[c.id] || {};
        var sub = c.kind === "pr" ? ((DATA.prmeta[c.id.slice(1)] || {}).d || "") : c.kind === "concept" ? (cm.s || "") : (n.q || n.s || "");
        var kindLine = c.kind === "concept" ? ((DATA.kinds || {})[cm.k] || cm.k || "") : "";
        showTip("<b>" + esc(label(c)) + "</b>" + (kindLine ? ' <span class="muted">· ' + esc(kindLine) + "</span>" : "") + (sub ? "<br>" + esc(sub.slice(0, 180)) : "") + (view !== "concepts" && c.ch.length ? "<br><i>click to enter · " + (c.wt - 1) + " inside</i>" : ""), ev);
      });
      cg.addEventListener("mouseleave", hideTip);
      cg.addEventListener("click", function (ev) {
        ev.stopPropagation();
        hideTip();
        if (animating) return;
        if (ev.ctrlKey || ev.metaKey) { ascend(); return; }
        if (view !== "concepts" && c.ch.length) descend(c);
        else openPanel(c);
      });
    });
    crumbs();
    return g;
  }

  function crumbs() {
    var parts = ['<a data-i="-1">' + esc(view === "concept" ? "the program" : (VIEW_LABEL[view] || view)) + "</a>"];
    for (var i = 0; i < path.length; i++) parts.push('<a data-i="' + i + '">' + esc(label(path[i])) + "</a>");
    crumbsEl.innerHTML = parts.join(' <span class="sep">›</span> ') + (path.length ? ' <button id="map-up" title="back out (esc)">↑ up</button>' : "");
    var links = crumbsEl.querySelectorAll("a");
    for (var j = 0; j < links.length; j++) links[j].addEventListener("click", function () { jump(parseInt(this.getAttribute("data-i"), 10)); });
    var up = document.getElementById("map-up");
    if (up) up.addEventListener("click", ascend);
  }

  function focusNode() { return path.length ? path[path.length - 1] : root; }

  function animate(from, to, ms, done) {
    animating = true;
    var t0 = null;
    function step(ts) {
      if (!t0) t0 = ts;
      var t = Math.min((ts - t0) / ms, 1), e2 = ease(t);
      tf = { k: from.k + (to.k - from.k) * e2, x: from.x + (to.x - from.x) * e2, y: from.y + (to.y - from.y) * e2 };
      applyTf();
      cam.style.opacity = from.o + (to.o - from.o) * e2;
      if (t < 1) requestAnimationFrame(step);
      else { animating = false; done && done(); }
    }
    requestAnimationFrame(step);
  }

  function descend(c) {
    var b = box(), k = 6;
    hideTip();
    animate({ k: tf.k, x: tf.x, y: tf.y, o: 1 }, { k: k, x: b.w / 2 - c.x * k, y: b.h / 2 - c.y * k, o: 0.05 }, 320, function () {
      path.push(c);
      render(c);
      animate({ k: 0.8, x: home.x + 0.1 * b.w, y: home.y + 0.1 * b.h, o: 0 }, home, 260);
    });
  }

  function ascend() {
    if (!path.length || animating) return;
    hideTip();
    var child = path.pop();
    var b = box();
    animate({ k: tf.k, x: tf.x, y: tf.y, o: 1 }, { k: 0.55, x: 0.22 * b.w, y: 0.22 * b.h, o: 0 }, 220, function () {
      render(focusNode());
      var c = child, k = 5;
      animate({ k: k, x: b.w / 2 - (c.x || b.w / 2) * k, y: b.h / 2 - (c.y || b.h / 2) * k, o: 0.1 }, home, 320);
    });
  }

  function jump(i) {
    if (animating) return;
    path = i < 0 ? [] : path.slice(0, i + 1);
    render(focusNode());
    animate({ k: 0.9, x: home.x + 0.05 * box().w, y: home.y + 0.05 * box().h, o: 0 }, home, 220);
  }

  function conceptBase(t) {
    var w = (DATA.concepts[t.id] || {}).w;
    return w ? "/wiki/" + seg(w) + "/" : "/concepts/" + seg(t.id) + "/";
  }
  function fragUrl(t) {
    if (t.kind === "pr") return "/prs/" + t.id.slice(1) + "/frag.html";
    if (t.kind === "concept") return conceptBase(t) + "frag.html";
    if (t.kind === "topic") return t.tref && t.tref.slice(0, 2) === "n:" ? "/n/" + seg(t.tref.slice(2)) + "/frag.html" : "/wiki/" + seg(t.id) + "/frag.html";
    return "/n/" + seg(t.id) + "/frag.html";
  }
  function pageUrl(t) {
    if (t.kind === "pr") return "/prs/" + t.id.slice(1) + "/";
    if (t.kind === "concept") return conceptBase(t);
    return "/n/" + seg(t.id) + "/";
  }

  function openPanel(t) {
    modal.classList.add("open");
    panelBody.innerHTML = '<p class="muted">Loading ' + esc(label(t)) + "…</p>";
    fetch(fragUrl(t)).then(function (r) { if (!r.ok) throw 0; return r.text(); }).then(function (h) {
      panelBody.innerHTML = h + '<p class="muted popup-foot"><a href="' + pageUrl(t) + '">Open the full page →</a></p>';
    }).catch(function () { panelBody.innerHTML = '<p>Could not load; <a href="' + pageUrl(t) + '">open the page</a>.</p>'; });
    if (history.replaceState && !t.kind) history.replaceState(null, "", "/#n=" + seg(t.id));
  }
  function closePanel() {
    modal.classList.remove("open");
    panelBody.innerHTML = "";
    if (history.replaceState) history.replaceState(null, "", "/");
  }
  document.getElementById("map-panel-close").addEventListener("click", closePanel);
  modal.addEventListener("click", function (ev) { if (ev.target === modal) closePanel(); });

  function legend(v) {
    var lg = document.getElementById("map-legend");
    if (!lg) return;
    var K = DATA.kinds || {};
    var rows = v === "concepts"
      ? [["bone", K.goal || "goal"], ["emerald", K.construction || "construction"], ["sapphire", K.object || "object"], ["amber", K.work || "work"], ["amethyst", K.philosophy || "philosophy"]]
      : [["emerald", "lean-proved"], ["sapphire", "enumeration / witness"], ["amber", "test / contributor"], ["garnet", "item"], ["bone", "frame"], ["pr", "merged PR"], ["slate", "other"]];
    lg.innerHTML = rows.map(function (r) { return '<span class="lg tone-' + r[0] + '"><span class="dotc"></span>' + esc(r[1]) + "</span>"; }).join("");
  }

  function show(v) {
    view = v;
    path = [];
    build(v);
    legend(v);
    render(root);
    cam.style.opacity = 0;
    animate({ k: 0.92, x: home.x + 0.04 * box().w, y: home.y + 0.04 * box().h, o: 0 }, home, 240);
    var btns = viewsEl.querySelectorAll("button");
    for (var b = 0; b < btns.length; b++) btns[b].classList.toggle("on", btns[b].getAttribute("data-view") === v);
  }

  // pan and free zoom within a level; wheel-out past minimum backs out a level
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
  svg.addEventListener("click", function (ev) { if (drag && drag.moved) { ev.stopPropagation(); } }, true);
  var outAcc = 0, outLock = 0;
  svg.addEventListener("wheel", function (ev) {
    ev.preventDefault();
    if (animating) return;
    var b = box(), mx = ev.clientX - b.left, my = ev.clientY - b.top;
    var f = Math.exp(-ev.deltaY * 0.0016);
    var kNew = tf.k * f;
    if (kNew < 0.82 && path.length) {
      var now = Date.now();
      if (now > outLock) { outAcc += ev.deltaY; if (outAcc > 120) { outAcc = 0; outLock = now + 500; ascend(); return; } }
    } else outAcc = 0;
    kNew = Math.max(0.3, Math.min(kNew, 9));
    tf.x = mx - (mx - tf.x) * (kNew / tf.k);
    tf.y = my - (my - tf.y) * (kNew / tf.k);
    tf.k = kNew;
    applyTf();
  }, { passive: false });
  document.addEventListener("keydown", function (ev) {
    if (ev.key === "Escape") { if (modal.classList.contains("open")) closePanel(); else ascend(); }
  });
  window.addEventListener("resize", function () { render(focusNode()); });

  function findPath(t, id, acc) {
    if (t.id === id) return acc.concat([t]);
    for (var i = 0; i < t.ch.length; i++) {
      var r = findPath(t.ch[i], id, acc.concat([t]));
      if (r) return r;
    }
    return null;
  }

  fetch("/assets/map.json").then(function (r) { return r.json(); }).then(function (d) {
    DATA = d;
    var order = ["concepts", "concept", "prs", "rounds"];
    order.forEach(function (v) {
      if (!d.views[v]) return;
      var btn = document.createElement("button");
      btn.setAttribute("data-view", v);
      btn.textContent = VIEW_LABEL[v] || v;
      btn.addEventListener("click", function () { show(this.getAttribute("data-view")); });
      viewsEl.appendChild(btn);
    });
    var m = location.hash.match(/#n=(.+)/);
    if (m) {
      var id = decodeURIComponent(m[1]).replace(/--/g, "/");
      show("concept");
      var p = findPath(root, id, []) || findPath(root, decodeURIComponent(m[1]), []);
      if (p && p.length > 1) {
        var target = p[p.length - 1];
        path = p.slice(1, p.length - (target.ch.length ? 0 : 1));
        render(focusNode());
        if (!target.ch.length) openPanel(target);
      }
    } else show("concepts");
  }).catch(function () {
    svg.outerHTML = '<p>The map data could not be loaded; the <noscript>lines</noscript> listing below and the <a href="/search/">search</a> still work.</p>';
  });
})();
