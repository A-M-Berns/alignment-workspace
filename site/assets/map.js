// The map canvas, in discrete levels. One level renders at a time: the focus's children as rounded regions
// (with a faint preview of their own contents), entered by click with an animated zoom and left by esc,
// ctrl-click, wheel-out or the breadcrumb. The concepts view lays its top level out as a constellation —
// linked circles — instead of regions. A leaf opens its fragment in the panel: /n/<id>/frag.html for a map
// node, /wiki/<Page>/frag.html for a concept, /prs/<n>/frag.html for a merged pull request.
(function () {
  "use strict";
  var svg = document.getElementById("map");
  if (!svg) return;
  var NS = "http://www.w3.org/2000/svg";
  var seg = function (id) { return String(id).replace(/\//g, "--"); };
  var panel = document.getElementById("map-panel"), panelBody = document.getElementById("map-panel-body");
  var crumbsEl = document.getElementById("map-crumbs"), viewsEl = document.getElementById("map-views");
  var VIEW_LABEL = { concept: "goals", concepts: "concepts", rounds: "rounds", class: "class", prs: "merged work" };

  var DATA = null, view = "concept", root = null, path = [], animating = false;
  var cam = document.createElementNS(NS, "g");
  svg.appendChild(cam);

  function el(tag, attrs, parent) {
    var e = document.createElementNS(NS, tag);
    for (var k in attrs) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }
  function ease(t) { return t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2; }

  function build(viewName) {
    root = JSON.parse(JSON.stringify(DATA.views[viewName]));
    (function link(t, p) { t.parent = p; t.wt = t.ch.length ? 0 : 1; for (var i = 0; i < t.ch.length; i++) { link(t.ch[i], t); t.wt += t.ch[i].wt; } t.wt += t.ch.length ? 1 : 0; })(root, null);
  }
  function kindOf(t) {
    if (t.kind) return t.kind;
    var n = DATA.nodes[t.id];
    if (!n) return "group";
    return t.ch.length ? "node region" : "node";
  }
  function label(t) {
    if (t.kind === "pr") { var m = DATA.prmeta[t.id.slice(1)] || {}; return "#" + t.id.slice(1) + " " + (m.t || ""); }
    if (t.kind === "concept" || t.kind === "topic") return t.id.replace(/-/g, " ");
    return t.id;
  }
  function classesOf(t) {
    var c = "lvl " + kindOf(t);
    var n = DATA.nodes[t.id];
    if (n) {
      if (n.d) c += " drafted";
      if (n.f) c += " frame";
      if (n.c) c += " cls-" + n.c;
    }
    if (t.kind === "pr" && (DATA.prmeta[t.id.slice(1)] || {}).sup) c += " sup";
    return c;
  }

  // squarified treemap of items (by wt) into a rect
  function squarify(items, x, y, w, h) {
    items = items.slice().sort(function (a, b) { return b.wt - a.wt; });
    var total = 0, i;
    for (i = 0; i < items.length; i++) total += items[i].wt;
    var scale = (w * h) / total, out = [], row = [], rowSum = 0, rest = items;
    function worst(row, sumWt, side) {
      var sum = sumWt * scale, mx = 0;
      for (var j = 0; j < row.length; j++) {
        var a = row[j].wt * scale, r = Math.max((side * side * a) / (sum * sum), (sum * sum) / (side * side * a));
        if (r > mx) mx = r;
      }
      return mx;
    }
    function layRow(row, sumWt) {
      var area = sumWt * scale, horiz = w >= h, thick = horiz ? area / h : area / w, off = 0;
      for (var j = 0; j < row.length; j++) {
        var len = (row[j].wt * scale) / thick;
        out.push(horiz ? [row[j], x, y + off, thick, len] : [row[j], x + off, y, len, thick]);
        off += len;
      }
      if (horiz) { x += thick; w -= thick; } else { y += thick; h -= thick; }
    }
    while (rest.length) {
      var side = Math.min(w, h), it = rest[0];
      if (!row.length || worst(row.concat([it]), rowSum + it.wt, side) <= worst(row, rowSum, side)) {
        row.push(it); rowSum += it.wt; rest = rest.slice(1);
      } else { layRow(row, rowSum); row = []; rowSum = 0; }
    }
    if (row.length) layRow(row, rowSum);
    return out;
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

  function box() { var b = svg.getBoundingClientRect(); return { w: b.width, h: b.height }; }

  // ancestor of `id` that is a direct child of focus, via the current tree
  function childAncestor(focus, id) {
    var map = focus._desc;
    if (!map) {
      map = focus._desc = {};
      for (var i = 0; i < focus.ch.length; i++) {
        (function mark(t, top) { map[t.id] = top; for (var j = 0; j < t.ch.length; j++) mark(t.ch[j], top); })(focus.ch[i], focus.ch[i]);
      }
    }
    return map[id] || null;
  }

  function drawEdges(g, focus) {
    if (!document.getElementById("map-edges").checked) return;
    var pairs = {}, i;
    for (i = 0; i < DATA.edges.length; i++) {
      var e = DATA.edges[i], a = childAncestor(focus, e[0]), b = childAncestor(focus, e[1]);
      if (!a || !b || a === b || a.x === undefined || b.x === undefined) continue;
      var key = a.id < b.id ? a.id + "\u0000" + b.id : b.id + "\u0000" + a.id;
      pairs[key] = pairs[key] || { a: a, b: b, n: 0, given: false };
      pairs[key].n++;
      if (e[2] === "given") pairs[key].given = true;
    }
    var eg = el("g", { "class": "edges" }, g);
    for (var k in pairs) {
      var p = pairs[k];
      var x1 = p.a.x + p.a.w / 2, y1 = p.a.y + p.a.h / 2, x2 = p.b.x + p.b.w / 2, y2 = p.b.y + p.b.h / 2;
      var path2 = el("path", { d: "M" + x1 + "," + y1 + " Q" + ((x1 + x2) / 2 + (y2 - y1) * 0.12) + "," + ((y1 + y2) / 2 + (x1 - x2) * 0.12) + " " + x2 + "," + y2,
                               "class": "edge" + (p.given ? " edge-given" : ""), "stroke-width": Math.min(1 + Math.log(p.n), 3.5) }, eg);
      el("title", {}, path2).textContent = p.n + " connection(s)";
    }
  }

  function constellation(items, w, h) {
    var i, j, n = items.length, pos = [];
    for (i = 0; i < n; i++) {
      var a = (i / n) * 2 * Math.PI;
      pos.push({ x: w / 2 + Math.cos(a) * w * 0.33, y: h / 2 + Math.sin(a) * h * 0.33, vx: 0, vy: 0 });
    }
    var links = [];
    for (i = 0; i < (DATA.clinks || []).length; i++) {
      var L = DATA.clinks[i], ia = -1, ib = -1;
      for (j = 0; j < n; j++) { if (items[j].id === L[0]) ia = j; if (items[j].id === L[1]) ib = j; }
      if (ia >= 0 && ib >= 0) links.push([ia, ib, L[2]]);
    }
    for (var it = 0; it < 220; it++) {
      for (i = 0; i < n; i++) for (j = i + 1; j < n; j++) {
        var dx = pos[j].x - pos[i].x, dy = pos[j].y - pos[i].y, d2 = dx * dx + dy * dy + 40, f = Math.min((w * h) / 220 / d2, 4);
        pos[i].vx -= dx * f * 0.02; pos[i].vy -= dy * f * 0.02; pos[j].vx += dx * f * 0.02; pos[j].vy += dy * f * 0.02;
      }
      for (i = 0; i < links.length; i++) {
        var a2 = pos[links[i][0]], b2 = pos[links[i][1]], k = Math.min(links[i][2], 8) * 0.0022;
        var ddx = b2.x - a2.x, ddy = b2.y - a2.y;
        a2.vx += ddx * k; a2.vy += ddy * k; b2.vx -= ddx * k; b2.vy -= ddy * k;
      }
      for (i = 0; i < n; i++) {
        pos[i].x += Math.max(-9, Math.min(9, pos[i].vx)); pos[i].y += Math.max(-9, Math.min(9, pos[i].vy));
        pos[i].vx *= 0.82; pos[i].vy *= 0.82;
        pos[i].x = Math.max(70, Math.min(w - 70, pos[i].x)); pos[i].y = Math.max(50, Math.min(h - 60, pos[i].y));
      }
    }
    return { pos: pos, links: links };
  }

  function renderConstellation(g, focus, w, h) {
    var lay = constellation(focus.ch, w, h), i;
    var lg = el("g", { "class": "clinks" }, g);
    for (i = 0; i < lay.links.length; i++) {
      var L = lay.links[i], a = lay.pos[L[0]], b = lay.pos[L[1]];
      el("line", { x1: a.x, y1: a.y, x2: b.x, y2: b.y, "class": "clink", opacity: Math.min(0.12 + L[2] * 0.06, 0.55), "stroke-width": Math.min(0.6 + L[2] * 0.25, 3) }, lg);
    }
    for (i = 0; i < focus.ch.length; i++) {
      var c = focus.ch[i], p = lay.pos[i], meta = (DATA.concepts || {})[c.id] || {};
      var r = 9 + Math.sqrt((meta.n || 0) + 1) * 2.4;
      c.x = p.x - r; c.y = p.y - r; c.w = 2 * r; c.h = 2 * r;
      var cg = el("g", { "class": "lvl concept-dot" + (meta.prs ? " has-prs" : "") }, g);
      el("circle", { cx: p.x, cy: p.y, r: r }, cg);
      cg.appendChild(wrap(label(c), p.x, p.y + r + 13, 150, 11, 2, "middle"));
      el("title", {}, cg).textContent = label(c) + " — " + (meta.n || 0) + " node(s), " + (meta.prs || 0) + " merged PR(s)";
      attach(cg, c);
    }
  }

  function attach(g, t) {
    g.addEventListener("click", function (ev) {
      ev.stopPropagation();
      if (animating) return;
      if (ev.ctrlKey || ev.metaKey) { ascend(); return; }
      if (t.ch.length) descend(t);
      else openPanel(t);
    });
  }

  function render(focus) {
    cam.textContent = "";
    cam.setAttribute("transform", "");
    var b = box(), pad = 10;
    var g = el("g", { "class": "scene" }, cam);
    el("rect", { x: 0, y: 0, width: b.w, height: b.h, "class": "backdrop" }, g);
    if (focus.layout === "constellation") {
      renderConstellation(g, focus, b.w, b.h);
    } else {
      var placed = squarify(focus.ch, pad, pad, b.w - 2 * pad, b.h - 2 * pad), i;
      for (i = 0; i < placed.length; i++) {
        var p = placed[i], c = p[0], gap = 5;
        c.x = p[1] + gap; c.y = p[2] + gap; c.w = Math.max(p[3] - 2 * gap, 8); c.h = Math.max(p[4] - 2 * gap, 8);
        var cg = el("g", { "class": classesOf(c) }, g);
        el("rect", { x: c.x, y: c.y, width: c.w, height: c.h, rx: Math.min(10, c.w / 6, c.h / 6) }, cg);
        var n = DATA.nodes[c.id] || {}, tx = c.x + 10, ty = c.y + 20;
        if (c.w > 56 && c.h > 30) {
          var sz = c.ch.length ? Math.max(Math.min(c.w / 16, 15), 12) : Math.max(Math.min(c.w / 18, 12.5), 10.5);
          cg.appendChild(wrap(label(c), tx, ty, c.w - 20, sz, 2));
          if (n.q && c.h > 76) {
            var qt = wrap(n.q, tx, ty + sz * 2.5, c.w - 20, 10.5, 2);
            qt.setAttribute("class", "q");
            cg.appendChild(qt);
          }
        }
        if (c.ch.length) {
          var bt = el("text", { x: c.x + c.w - 8, y: c.y + c.h - 8, "class": "badge", "text-anchor": "end", "font-size": 10 }, cg);
          bt.textContent = (c.wt - 1) + " inside";
          preview(cg, c);
        }
        el("title", {}, cg).textContent = label(c) + ((DATA.nodes[c.id] || {}).s ? " — " + DATA.nodes[c.id].s : "");
        attach(cg, c);
      }
      drawEdges(g, focus);
    }
    crumbs();
    return g;
  }

  function preview(cg, c) {
    // a faint grid of the region's own contents, so depth shows before you enter
    var innerY = c.y + Math.min(c.h * 0.42, 54), ih = c.y + c.h - 16 - innerY;
    if (ih < 14 || c.w < 70) return;
    var kids = c.ch.slice(0, 24);
    var cols = Math.ceil(Math.sqrt(kids.length * (c.w - 20) / ih)) || 1, rows = Math.ceil(kids.length / cols);
    var cw = (c.w - 20) / cols, chh = ih / rows;
    var pg = el("g", { "class": "preview" }, cg);
    for (var i = 0; i < kids.length; i++) {
      var kx = c.x + 10 + (i % cols) * cw, ky = innerY + Math.floor(i / cols) * chh;
      var kc = DATA.nodes[kids[i].id] || {};
      el("rect", { x: kx + 1.5, y: ky + 1.5, width: Math.max(cw - 3, 2), height: Math.max(chh - 3, 2), rx: 2,
                   "class": "pv" + (kc.c ? " cls-" + kc.c : "") + (kids[i].ch.length ? " pv-deep" : "") }, pg);
    }
  }

  function crumbs() {
    var parts = ['<a data-i="-1">' + (view === "concept" ? "the program" : (VIEW_LABEL[view] || view)) + "</a>"];
    for (var i = 0; i < path.length; i++) parts.push('<a data-i="' + i + '">' + label(path[i]).replace(/&/g, "&amp;").replace(/</g, "&lt;") + "</a>");
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
      var t = Math.min((ts - t0) / ms, 1), e = ease(t);
      var k = from.k + (to.k - from.k) * e;
      cam.setAttribute("transform", "translate(" + (from.x + (to.x - from.x) * e) + "," + (from.y + (to.y - from.y) * e) + ") scale(" + k + ")");
      cam.style.opacity = from.o + (to.o - from.o) * e;
      if (t < 1) requestAnimationFrame(step);
      else { animating = false; done && done(); }
    }
    requestAnimationFrame(step);
  }

  function rectTransform(c) {
    // the transform that blows rect c up to fill the stage
    var b = box(), k = Math.min(b.w / c.w, b.h / c.h) * 0.96;
    return { k: k, x: b.w / 2 - (c.x + c.w / 2) * k, y: b.h / 2 - (c.y + c.h / 2) * k, o: 0.08 };
  }

  function descend(c) {
    var into = rectTransform(c);
    animate({ k: 1, x: 0, y: 0, o: 1 }, into, 300, function () {
      path.push(c);
      render(c);
      cam.style.opacity = 0;
      animate({ k: 1.06, x: -0.03 * box().w, y: -0.03 * box().h, o: 0 }, { k: 1, x: 0, y: 0, o: 1 }, 220);
    });
  }

  function ascend() {
    if (!path.length || animating) return;
    var child = path.pop();
    var parent = focusNode();
    render(parent);
    var from = rectTransform(child);
    from.o = 0.25;
    animate(from, { k: 1, x: 0, y: 0, o: 1 }, 300);
  }

  function jump(i) {
    if (animating) return;
    if (i < 0) { path = []; render(root); cam.style.opacity = 0; animate({ k: 0.94, x: 0.03 * box().w, y: 0.03 * box().h, o: 0 }, { k: 1, x: 0, y: 0, o: 1 }, 220); return; }
    path = path.slice(0, i + 1);
    render(focusNode());
    animate({ k: 0.94, x: 0.03 * box().w, y: 0.03 * box().h, o: 0.2 }, { k: 1, x: 0, y: 0, o: 1 }, 220);
  }

  function fragUrl(t) {
    if (t.kind === "pr") return "/prs/" + t.id.slice(1) + "/frag.html";
    if (t.kind === "concept") return "/wiki/" + seg(t.id) + "/frag.html";
    if (t.kind === "topic") return t.tref && t.tref.slice(0, 2) === "n:" ? "/n/" + seg(t.tref.slice(2)) + "/frag.html" : "/wiki/" + seg(t.id) + "/frag.html";
    return "/n/" + seg(t.id) + "/frag.html";
  }
  function pageUrl(t) {
    if (t.kind === "pr") return "/prs/" + t.id.slice(1) + "/";
    if (t.kind === "concept") return "/wiki/" + seg(t.id) + "/";
    return "/n/" + seg(t.id) + "/";
  }

  function openPanel(t) {
    panel.classList.add("open");
    panelBody.innerHTML = '<p class="muted">Loading ' + label(t).replace(/</g, "&lt;") + "…</p>";
    fetch(fragUrl(t)).then(function (r) { if (!r.ok) throw 0; return r.text(); }).then(function (h) { panelBody.innerHTML = h; })
      .catch(function () { panelBody.innerHTML = '<p>Could not load; <a href="' + pageUrl(t) + '">open the page</a>.</p>'; });
    if (history.replaceState && t.kind !== "pr" && t.kind !== "concept") history.replaceState(null, "", "/#n=" + seg(t.id));
  }
  document.getElementById("map-panel-close").addEventListener("click", function () {
    panel.classList.remove("open");
    panelBody.innerHTML = "";
    if (history.replaceState) history.replaceState(null, "", "/");
  });

  function show(v) {
    view = v;
    path = [];
    build(v);
    render(root);
    cam.style.opacity = 0;
    animate({ k: 0.96, x: 0.02 * box().w, y: 0.02 * box().h, o: 0 }, { k: 1, x: 0, y: 0, o: 1 }, 240);
    var btns = viewsEl.querySelectorAll("button");
    for (var b = 0; b < btns.length; b++) btns[b].classList.toggle("on", btns[b].getAttribute("data-view") === v);
  }

  // back out: esc, wheel-out, double-click the backdrop
  document.addEventListener("keydown", function (ev) { if (ev.key === "Escape") { if (panel.classList.contains("open")) { panel.classList.remove("open"); panelBody.innerHTML = ""; } else ascend(); } });
  var wheelAcc = 0, wheelLock = 0;
  svg.addEventListener("wheel", function (ev) {
    ev.preventDefault();
    var now = Date.now();
    if (now < wheelLock) return;
    wheelAcc += ev.deltaY;
    if (wheelAcc > 140) { wheelAcc = 0; wheelLock = now + 450; ascend(); }
    if (wheelAcc < -200) wheelAcc = -200;
  }, { passive: false });
  svg.addEventListener("dblclick", function (ev) { if (ev.target.classList && ev.target.classList.contains("backdrop")) ascend(); });
  document.getElementById("map-edges").addEventListener("change", function () { render(focusNode()); });
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
    for (var v in d.views) {
      var btn = document.createElement("button");
      btn.setAttribute("data-view", v);
      btn.textContent = VIEW_LABEL[v] || v;
      btn.addEventListener("click", function () { show(this.getAttribute("data-view")); });
      viewsEl.appendChild(btn);
    }
    show("concept");
    var m = location.hash.match(/#n=(.+)/);
    if (m) {
      var id = decodeURIComponent(m[1]).replace(/--/g, "/");
      var p = findPath(root, id, []) || findPath(root, decodeURIComponent(m[1]), []);
      if (p && p.length > 1) {
        var target = p[p.length - 1];
        path = p.slice(1, p.length - (target.ch.length ? 0 : 1));
        render(focusNode());
        if (!target.ch.length) openPanel(target);
      }
    }
  }).catch(function () {
    svg.outerHTML = '<p>The map data could not be loaded; the <noscript>lines</noscript> listing below and the <a href="/search/">search</a> still work.</p>';
  });
})();
