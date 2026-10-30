// The map canvas: /assets/map.json laid out as nested regions with semantic zoom. Vanilla JavaScript, SVG.
// Containment carries the hierarchy (a frame or claim opens into its contents once it is wide enough on screen);
// the part/given/held cross-edges draw only between nodes currently visible. Clicking a node loads its
// /n/<id>/frag.html into the panel. The hash #n=<id> (ids with "/" as "--") deep-links a node.
(function () {
  "use strict";
  var svg = document.getElementById("map");
  if (!svg) return;
  var NS = "http://www.w3.org/2000/svg";
  var W = 1600, H = 1000;               // world units
  var OPEN = 150, LABEL = 70;           // screen px at which a region opens / a leaf shows its label
  var seg = function (id) { return id.replace(/\//g, "--"); };
  var panel = document.getElementById("map-panel"), panelBody = document.getElementById("map-panel-body");

  var DATA = null, view = "concept", k = 1, tx = 0, ty = 0;
  var root = null;                       // layout tree: {id, ch, x, y, w, h, el, chEl, open}
  var byId = {}, containers = [], leaves = [];
  var world = document.createElementNS(NS, "g");
  var edgesG = document.createElementNS(NS, "g");
  edgesG.setAttribute("class", "edges");
  svg.appendChild(world);

  function weight(t) {
    if (!t.ch.length) { t.wt = 1; return 1; }
    var s = 1;
    for (var i = 0; i < t.ch.length; i++) s += weight(t.ch[i]);
    t.wt = s;
    return s;
  }

  // squarified treemap of t.ch into (x,y,w,h)
  function squarify(items, x, y, w, h) {
    items = items.slice().sort(function (a, b) { return b.wt - a.wt; });
    var total = 0;
    for (var i = 0; i < items.length; i++) total += items[i].wt;
    var scale = (w * h) / total;
    var row = [], rowSum = 0, rest = items, out = [];
    function worst(row, sumWt, side) {
      var sum = sumWt * scale, mx = 0;
      for (var i = 0; i < row.length; i++) {
        var a = row[i].wt * scale;
        var r = Math.max((side * side * a) / (sum * sum), (sum * sum) / (side * side * a));
        if (r > mx) mx = r;
      }
      return mx;
    }
    while (rest.length) {
      var side = Math.min(w, h);
      var it = rest[0];
      if (!row.length || worst(row.concat([it]), rowSum + it.wt, side) <= worst(row, rowSum, side)) {
        row.push(it); rowSum += it.wt; rest = rest.slice(1);
      } else {
        layRow(row, rowSum); row = []; rowSum = 0;
      }
    }
    if (row.length) layRow(row, rowSum);
    function layRow(row, sum) {
      var area = sum * scale, horiz = w >= h;
      var thick = horiz ? area / h : area / w;
      var off = 0;
      for (var i = 0; i < row.length; i++) {
        var len = (row[i].wt * scale) / thick;
        if (horiz) out.push([row[i], x, y + off, thick, len]);
        else out.push([row[i], x + off, y, len, thick]);
        off += len;
      }
      if (horiz) { x += thick; w -= thick; } else { y += thick; h -= thick; }
    }
    return out;
  }

  function layout(t, x, y, w, h, depth) {
    t.x = x; t.y = y; t.w = w; t.h = h; t.depth = depth;
    byId[t.id] = t;
    if (!t.ch.length) { leaves.push(t); return; }
    containers.push(t);
    var band = Math.min(h * 0.14, Math.max(w, h) * 0.035 + 4);
    var pad = Math.min(w, h) * 0.015 + 0.5;
    var placed = squarify(t.ch, x + pad, y + band, Math.max(w - 2 * pad, 1), Math.max(h - band - pad, 1));
    for (var i = 0; i < placed.length; i++) {
      var p = placed[i];
      layout(p[0], p[1] + pad * 0.2, p[2] + pad * 0.2, Math.max(p[3] - pad * 0.4, 0.5), Math.max(p[4] - pad * 0.4, 0.5), depth + 1);
    }
  }

  function cls(t) {
    var n = DATA.nodes[t.id] || {};
    var c = t.ch.length ? "region" : "leaf";
    if (n.f) c += " frame";
    if (n.d) c += " drafted";
    if (n.c) c += " cls-" + n.c;
    if (n.i) c += " item item-" + n.i;
    c += " depth-" + Math.min(t.depth, 6);
    return c;
  }

  function title(t) {
    var n = DATA.nodes[t.id] || {};
    return n.q || n.s || t.id;
  }

  function render(t) {
    var g = document.createElementNS(NS, "g");
    g.setAttribute("class", cls(t));
    var r = document.createElementNS(NS, "rect");
    r.setAttribute("x", t.x); r.setAttribute("y", t.y); r.setAttribute("width", t.w); r.setAttribute("height", t.h);
    g.appendChild(r);
    var label = document.createElementNS(NS, "text");
    label.setAttribute("x", t.x + t.w / 2); label.setAttribute("y", t.y + Math.min(t.h / 2, t.h * 0.07 + 3));
    label.textContent = t.id === "top" ? "" : t.id;
    g.appendChild(label);
    t.el = g; t.rectEl = r; t.labelEl = label;
    if (t.ch.length) {
      var chG = document.createElementNS(NS, "g");
      chG.setAttribute("class", "ch");
      for (var i = 0; i < t.ch.length; i++) chG.appendChild(render(t.ch[i]));
      g.appendChild(chG);
      t.chEl = chG;
    }
    g.addEventListener("click", function (ev) {
      if (ev.target !== r && ev.target !== label) return;
      ev.stopPropagation();
      if (t.ch.length && !t.open) zoomTo(t);
      else if (!t.ch.length && DATA.nodes[t.id]) openPanel(t.id);
      else if (t.ch.length) zoomTo(t);
    });
    var tip = document.createElementNS(NS, "title");
    tip.textContent = t.id + (title(t) !== t.id ? " — " + title(t) : "");
    g.insertBefore(tip, r);
    return g;
  }

  function apply() {
    world.setAttribute("transform", "translate(" + tx + "," + ty + ") scale(" + k + ")");
    var i, t, sw;
    for (i = 0; i < containers.length; i++) {
      t = containers[i]; sw = t.w * k;
      var open = sw > OPEN;
      if (open !== t.open) {
        t.open = open;
        t.el.classList.toggle("closed", !open);
      }
      t.labelEl.style.fontSize = Math.max(Math.min(t.w / Math.max(t.id.length, 8) * 1.6, t.h * 0.1 + 2, 26 / k), 8 / k) + "px";
    }
    for (i = 0; i < leaves.length; i++) {
      t = leaves[i]; sw = t.w * k;
      var lab = sw > LABEL;
      if (lab !== t.lab) { t.lab = lab; t.el.classList.toggle("unlabeled", !lab); }
      if (lab) t.labelEl.style.fontSize = Math.max(Math.min(t.w / Math.max(t.id.length, 6) * 1.5, t.h * 0.3), 6 / k) + "px";
    }
    drawEdges();
  }
  var raf = null;
  function schedule() { if (!raf) raf = requestAnimationFrame(function () { raf = null; apply(); }); }

  function visible(t) {
    for (var p = t.parent; p; p = p.parent) if (p.open === false) return false;
    return true;
  }

  function drawEdges() {
    edgesG.textContent = "";
    if (!document.getElementById("map-edges").checked) return;
    var box = svg.getBoundingClientRect(), drawn = 0;
    for (var i = 0; i < DATA.edges.length && drawn < 500; i++) {
      var e = DATA.edges[i], a = byId[e[0]], b = byId[e[1]];
      if (!a || !b || !visible(a) || !visible(b)) continue;
      var x1 = a.x + a.w / 2, y1 = a.y + a.h / 2, x2 = b.x + b.w / 2, y2 = b.y + b.h / 2;
      var sx1 = x1 * k + tx, sy1 = y1 * k + ty, sx2 = x2 * k + tx, sy2 = y2 * k + ty;
      if ((sx1 < 0 && sx2 < 0) || (sx1 > box.width && sx2 > box.width) || (sy1 < 0 && sy2 < 0) || (sy1 > box.height && sy2 > box.height)) continue;
      var p = document.createElementNS(NS, "path");
      p.setAttribute("d", "M" + x1 + "," + y1 + " Q" + ((x1 + x2) / 2 + (y2 - y1) * 0.15) + "," + ((y1 + y2) / 2 + (x1 - x2) * 0.15) + " " + x2 + "," + y2);
      p.setAttribute("class", "edge edge-" + (e[2] || "part"));
      edgesG.appendChild(p);
      drawn++;
    }
  }

  function zoomTo(t) {
    var box = svg.getBoundingClientRect();
    var kNew = Math.min(box.width / t.w, box.height / t.h) * 0.9;
    k = kNew;
    tx = box.width / 2 - (t.x + t.w / 2) * k;
    ty = box.height / 2 - (t.y + t.h / 2) * k;
    schedule();
  }

  function openPanel(id) {
    panel.classList.add("open");
    panelBody.innerHTML = '<p class="muted">Loading ' + id + "…</p>";
    fetch("/n/" + seg(id) + "/frag.html").then(function (r) { return r.text(); }).then(function (h) {
      panelBody.innerHTML = h;
    }).catch(function () { panelBody.innerHTML = '<p>Could not load; <a href="/n/' + seg(id) + '/">open the page</a>.</p>'; });
    if (history.replaceState) history.replaceState(null, "", "/#n=" + seg(id));
  }
  document.getElementById("map-panel-close").addEventListener("click", function () {
    panel.classList.remove("open");
    panelBody.innerHTML = "";
    if (history.replaceState) history.replaceState(null, "", "/");
  });

  function link(t, parent) {
    t.parent = parent;
    for (var i = 0; i < t.ch.length; i++) link(t.ch[i], t);
  }

  function show(v) {
    view = v;
    byId = {}; containers = []; leaves = [];
    world.textContent = "";
    root = JSON.parse(JSON.stringify(DATA.views[v]));
    link(root, null);
    weight(root);
    layout(root, 0, 0, W, H, 0);
    world.appendChild(render(root));
    world.appendChild(edgesG);
    var box = svg.getBoundingClientRect();
    k = Math.min(box.width / W, box.height / H);
    tx = (box.width - W * k) / 2; ty = (box.height - H * k) / 2;
    for (var i = 0; i < containers.length; i++) containers[i].open = null;
    for (var j = 0; j < leaves.length; j++) leaves[j].lab = null;
    apply();
    var btns = document.querySelectorAll(".map-bar button[data-view]");
    for (var b = 0; b < btns.length; b++) btns[b].classList.toggle("on", btns[b].getAttribute("data-view") === v);
  }

  // pan and zoom
  var drag = null, dragged = false;
  svg.addEventListener("pointerdown", function (ev) { drag = { x: ev.clientX, y: ev.clientY, tx: tx, ty: ty }; dragged = false; svg.setPointerCapture(ev.pointerId); });
  svg.addEventListener("pointermove", function (ev) {
    if (!drag) return;
    var dx = ev.clientX - drag.x, dy = ev.clientY - drag.y;
    if (Math.abs(dx) + Math.abs(dy) > 3) dragged = true;
    tx = drag.tx + dx; ty = drag.ty + dy;
    schedule();
  });
  svg.addEventListener("pointerup", function () { drag = null; });
  svg.addEventListener("click", function (ev) { if (dragged) { ev.stopPropagation(); dragged = false; } }, true);
  svg.addEventListener("wheel", function (ev) {
    ev.preventDefault();
    var box = svg.getBoundingClientRect();
    var mx = ev.clientX - box.left, my = ev.clientY - box.top;
    var f = Math.exp(-ev.deltaY * 0.0015);
    var kNew = Math.min(Math.max(k * f, 0.2), 4000);
    tx = mx - (mx - tx) * (kNew / k);
    ty = my - (my - ty) * (kNew / k);
    k = kNew;
    schedule();
  }, { passive: false });
  document.getElementById("map-edges").addEventListener("change", schedule);
  var btns = document.querySelectorAll(".map-bar button[data-view]");
  for (var b = 0; b < btns.length; b++) btns[b].addEventListener("click", function () { show(this.getAttribute("data-view")); });
  window.addEventListener("resize", schedule);

  fetch("/assets/map.json").then(function (r) { return r.json(); }).then(function (d) {
    DATA = d;
    show("concept");
    var m = location.hash.match(/#n=(.+)/);
    if (m) {
      var id = decodeURIComponent(m[1]).replace(/--/g, "/");
      var t = byId[id] || byId[decodeURIComponent(m[1])];
      if (t) { zoomTo(t); if (!t.ch.length) openPanel(t.id); }
    }
  }).catch(function () {
    svg.outerHTML = '<p>The map data could not be loaded; the <noscript>lines</noscript> listing below and the <a href="/search/">search</a> still work.</p>';
  });
})();
