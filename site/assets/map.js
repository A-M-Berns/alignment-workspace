// The map: the concept registry as a goal-ward flow. Nodes are text capsules placed in columns by
// distance to the program (foundations left, goals right), ordered within a column to sit near their
// neighbours; directed edges are flow curves with arrowheads, the few undirected relations dashed and
// faint. Clicking a capsule or an edge opens a small card; "Read more" opens the fullscreen view.
// /#c=<id> deep-links a concept. Vanilla JavaScript, SVG.
(function () {
  "use strict";
  var svg = document.getElementById("map");
  if (!svg) return;
  var NS = "http://www.w3.org/2000/svg";
  var seg = function (id) { return String(id).replace(/\//g, "--"); };
  var modal = document.getElementById("map-modal"), panelBody = document.getElementById("map-panel-body");
  var card = document.getElementById("map-card");
  var KIND_TONE = { goal: "bone", construction: "emerald", object: "sapphire", work: "amber", philosophy: "amethyst", companion: "garnet" };

  var DATA = null, tf = { k: 1, x: 0, y: 0 }, home = { k: 1, x: 0, y: 0 }, fitAll = null;
  var defs = document.createElementNS(NS, "defs");
  svg.appendChild(defs);
  var cam = document.createElementNS(NS, "g");
  svg.appendChild(cam);
  var mk = document.createElementNS(NS, "marker");
  mk.setAttribute("id", "arrow");
  mk.setAttribute("viewBox", "0 0 8 8");
  mk.setAttribute("refX", "7"); mk.setAttribute("refY", "4");
  mk.setAttribute("markerWidth", "6.5"); mk.setAttribute("markerHeight", "6.5");
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
    if (!zoomed && tf.k >= 1.4) { zoomed = true; svg.classList.add("zoomed"); }
    else if (zoomed && tf.k <= 1.25) { zoomed = false; svg.classList.remove("zoomed"); }
  }

  // split a title into at most two capsule lines
  function titleLines(s, perLine) {
    var words = String(s).split(/\s+/), lines = [""], li = 0;
    for (var i = 0; i < words.length; i++) {
      var cand = lines[li] ? lines[li] + " " + words[i] : words[i];
      if (cand.length > perLine && lines[li] && li < 1) { li++; lines.push(words[i]); }
      else lines[li] = cand.length > perLine && li === 1 ? lines[li] : cand;
    }
    if (lines[1] && lines[1].length > perLine) lines[1] = lines[1].slice(0, perLine - 1) + "…";
    return lines;
  }

  // compact layered graph with soft goal affinity (GPT Astra consult, 2026-10-31): x is
  // dependency rank with measured column widths and clean 80px gaps; y places each node at
  // the weighted middle of the goals it feeds, refined by neighbour sweeps and a constrained
  // compaction, so shared foundations sit between the lines they support. Importance shows
  // mostly as capsule area over a readable type floor. Long edges route through free slots
  // in the columns they cross rather than arcing over the map.
  var GOALS = ["corrigibility-line", "normative-induction", "normativity-line", "legitimacy-line", "deference-line", "openness-line"];
  function layout(items, links) {
    var meta = DATA.concepts, i;
    var succ = {}, nbAll = {};
    links.forEach(function (L) {
      if (!L[5]) (succ[L[0]] = succ[L[0]] || []).push(L[1]);
      (nbAll[L[0]] = nbAll[L[0]] || []).push(L[1]);
      (nbAll[L[1]] = nbAll[L[1]] || []).push(L[0]);
    });
    // geometry: type sits near a floor (12-16px); importance is carried by capsule area
    var geo = {};
    items.forEach(function (id) {
      var m = meta[id] || {};
      var imp = m.imp || 0;
      var curve = Math.pow(imp, 1.35);
      var fs = 12 + 4 * curve;
      var disp = String(m.t || id).replace(/\s*\([^)]*\)$/, "") || String(m.t || id);
      var lines = titleLines(disp, 18);
      var wch = Math.max.apply(null, lines.map(function (L) { return L.length; }));
      var cw = wch * fs * 0.626 + 26 + 96 * curve;
      var chh = Math.round((lines.length > 1 ? 2 * (fs + 3) + 12 : fs + 16) + 42 * curve);
      if (id === "the-program") { cw += 12; chh += 6; fs = Math.max(fs, 16); }
      geo[id] = { w: cw, h: chh, lines: lines, fs: fs };
    });
    // x: rank by goal distance; column centres from measured widths with a constant clear gap
    var dmax = 1;
    items.forEach(function (id) { dmax = Math.max(dmax, (meta[id] || {}).d || 0); });
    var colOf = {};
    items.forEach(function (id) { colOf[id] = id === "the-program" ? dmax : dmax - ((meta[id] || {}).d || 0); });
    var colW = [];
    items.forEach(function (id) { var c = colOf[id]; colW[c] = Math.max(colW[c] || 0, geo[id].w); });
    var colX = [], xcur = 150;
    for (i = 0; i <= dmax; i++) {
      colX[i] = xcur + (colW[i] || 0) / 2;
      xcur += colW[i] ? colW[i] + 80 : 0;
    }
    var w = xcur + 70;
    // the set of goals each node feeds, along directed edges
    var reach = {};
    function goalsOf(id, trail) {
      if (reach[id]) return reach[id];
      if (trail[id]) return [];
      trail[id] = 1;
      var out = {};
      if (GOALS.indexOf(id) >= 0) out[id] = 1;
      (succ[id] || []).forEach(function (s) { goalsOf(s, trail).forEach(function (gg) { out[gg] = 1; }); });
      delete trail[id];
      reach[id] = Object.keys(out).sort();
      return reach[id];
    }
    items.forEach(function (id) { goalsOf(id, {}); });
    // goal order: the permutation keeping goals with shared upstream support adjacent
    var shared = {};
    items.forEach(function (id) {
      if (GOALS.indexOf(id) >= 0 || id === "the-program") return;
      var gs = reach[id] || [];
      var aw = gs.length ? 1 / gs.length : 0;
      for (var a2 = 0; a2 < gs.length; a2++) for (var b2 = a2 + 1; b2 < gs.length; b2++) {
        var key = gs[a2] + "|" + gs[b2];
        shared[key] = (shared[key] || 0) + aw * aw;
      }
    });
    function permCost(order) {
      var at2 = {};
      order.forEach(function (gid, idx) { at2[gid] = idx; });
      var cost = 0;
      Object.keys(shared).forEach(function (key) {
        var pq = key.split("|");
        cost += shared[key] * Math.abs(at2[pq[0]] - at2[pq[1]]);
      });
      return cost;
    }
    var goalOrder = GOALS.slice(), bestCost = permCost(goalOrder);
    (function permute(arr, k) {
      if (k === arr.length) {
        var c2 = permCost(arr);
        if (c2 < bestCost - 1e-9 || (Math.abs(c2 - bestCost) < 1e-9 && arr.join() < goalOrder.join())) {
          bestCost = c2; goalOrder = arr.slice();
        }
        return;
      }
      for (var j = k; j < arr.length; j++) {
        var t = arr[k]; arr[k] = arr[j]; arr[j] = t;
        permute(arr, k + 1);
        t = arr[k]; arr[k] = arr[j]; arr[j] = t;
      }
    })(GOALS.slice(), 0);
    // anchors, and each node's preferred y: the mean anchor of the goals it feeds
    var PITCH = 300;
    var anchor = {};
    goalOrder.forEach(function (gid, idx) { anchor[gid] = 90 + idx * PITCH; });
    var mid = 90 + (goalOrder.length - 1) * PITCH / 2;
    var pref = {};
    items.forEach(function (id) {
      var gs = reach[id] || [];
      pref[id] = gs.length ? gs.reduce(function (s, gg) { return s + anchor[gg]; }, 0) / gs.length : mid;
    });
    var y = {};
    items.forEach(function (id) { y[id] = pref[id]; });
    var cols = [];
    items.forEach(function (id) { (cols[colOf[id]] = cols[colOf[id]] || []).push(id); });
    function lam(id) { return GOALS.indexOf(id) >= 0 ? 8 : (id === "the-program" ? 0 : 0.5); }
    function orderCol(col) {
      col.sort(function (a, bb) {
        var ga2 = GOALS.indexOf(a), gb2 = GOALS.indexOf(bb);
        if (ga2 >= 0 && gb2 >= 0) return goalOrder.indexOf(a) - goalOrder.indexOf(bb);
        return (y[a] - y[bb]) || a.localeCompare(bb);
      });
    }
    // sweeps plus compaction: target y from neighbours and the affinity anchor, then a
    // weighted no-overlap projection (pool adjacent violators) within each column
    var SEP = 80;
    for (var pass = 0; pass < 24; pass++) {
      cols.forEach(function (col) {
        if (!col || !col.length) return;
        var target = {}, wgt = {};
        col.forEach(function (id) {
          var nb = nbAll[id] || [];
          var s = 0;
          nb.forEach(function (n2) { s += y[n2]; });
          var l2 = lam(id);
          target[id] = (nb.length + l2) > 0 ? (s + l2 * pref[id]) / (nb.length + l2) : pref[id];
          wgt[id] = nb.length + l2 + 0.01;
        });
        var hold = {};
        col.forEach(function (id) { hold[id] = target[id]; });
        var keep = y; y = target; orderCol(col); y = keep;
        // cumulative required separations, then PAV on the shifted targets
        var sep = [0];
        for (var i2 = 1; i2 < col.length; i2++) {
          sep[i2] = sep[i2 - 1] + (geo[col[i2 - 1]].h + geo[col[i2]].h) / 2 + SEP;
        }
        var blocks = [];
        for (var i3 = 0; i3 < col.length; i3++) {
          var b2 = { v: hold[col[i3]] - sep[i3], w: wgt[col[i3]], n: 1 };
          while (blocks.length && blocks[blocks.length - 1].v >= b2.v) {
            var pb = blocks.pop();
            b2 = { v: (pb.v * pb.w + b2.v * b2.w) / (pb.w + b2.w), w: pb.w + b2.w, n: pb.n + b2.n };
          }
          blocks.push(b2);
        }
        var k2 = 0;
        blocks.forEach(function (bl) {
          for (var i4 = 0; i4 < bl.n; i4++) { y[col[k2]] = bl.v + sep[k2]; k2++; }
        });
      });
    }
    // normalise to the frame and take final positions
    var yMin = 1e9, yMax = -1e9;
    items.forEach(function (id) {
      yMin = Math.min(yMin, y[id] - geo[id].h / 2);
      yMax = Math.max(yMax, y[id] + geo[id].h / 2);
    });
    var pos = {};
    items.forEach(function (id) { pos[id] = { x: colX[colOf[id]], y: y[id] - yMin + 90 }; });
    var h = yMax - yMin + 180;
    // personal space, guaranteed: push apart any residual overlapping capsules
    for (var iter = 0; iter < 40; iter++) {
      var moved = false;
      for (var ii = 0; ii < items.length; ii++) for (var jj = ii + 1; jj < items.length; jj++) {
        var A = pos[items[ii]], Bq = pos[items[jj]], ga = geo[items[ii]], gb = geo[items[jj]];
        var ox = (ga.w + gb.w) / 2 + 18 - Math.abs(A.x - Bq.x);
        var oy = (ga.h + gb.h) / 2 + 76 - Math.abs(A.y - Bq.y);
        if (ox > 0 && oy > 0) {
          var push = oy / 2 + 1;
          if (A.y <= Bq.y) { A.y -= push; Bq.y += push; } else { A.y += push; Bq.y -= push; }
          moved = true;
        }
      }
      if (!moved) break;
    }
    // free vertical slots per column, for routing long edges around capsules
    var occupied = [];
    items.forEach(function (id) {
      var c = colOf[id];
      (occupied[c] = occupied[c] || []).push([pos[id].y - geo[id].h / 2 - 10, pos[id].y + geo[id].h / 2 + 10]);
    });
    (occupied || []).forEach(function (iv) { if (iv) iv.sort(function (a, bb) { return a[0] - bb[0]; }); });
    function freeYNear(c, want) {
      var iv = occupied[c];
      if (!iv || !iv.length) return want;
      var inside = null;
      for (var i5 = 0; i5 < iv.length; i5++) if (want > iv[i5][0] && want < iv[i5][1]) { inside = iv[i5]; break; }
      if (!inside) return want;
      var up = inside[0], down = inside[1];
      for (var i6 = 0; i6 < iv.length; i6++) {
        if (iv[i6][1] <= up && Math.abs(iv[i6][1] - up) < 1) up = iv[i6][0];
        if (iv[i6][0] >= down && Math.abs(iv[i6][0] - down) < 1) down = iv[i6][1];
      }
      return (want - up) <= (down - want) ? up : down;
    }
    return { pos: pos, geo: geo, w: w, h: h, colOf: colOf, colX: colX, freeYNear: freeYNear };
  }

  var at = {}, geo = {}, capEl = {};
  var pinned = null, focusOn = null, focusOff = null;
  function render() {
    cam.textContent = "";
    hideCard();
    var b = box();
    var g = el("g", { "class": "scene" }, cam);
    el("rect", { x: -4 * b.w, y: -4 * b.h, width: 9 * b.w, height: 9 * b.h, "class": "backdrop" }, g);
    var items = DATA.items, links = DATA.links;
    var lay = layout(items, links);
    at = lay.pos; geo = lay.geo;
    var colOf = lay.colOf;
    svg.__layout = { at: at, geo: geo };
    var ax = el("g", { "class": "axis" }, g);

    // boot at twice the fit-to-width zoom, centred, so capsules open at reading size;
    // the map overflows the viewport and the user pans
    home = { k: Math.min((b.w / lay.w) * 2, 1.2), x: 0, y: 0 };
    home.x = (b.w - lay.w * home.k) / 2;
    home.y = (b.h - lay.h * home.k) / 2;
    fitAll = { k: Math.min(b.w / lay.w, (b.h - 40) / lay.h) };
    fitAll.x = (b.w - lay.w * fitAll.k) / 2;
    fitAll.y = (b.h - lay.h * fitAll.k) / 2;
    tf = { k: home.k, x: home.x, y: home.y };
    applyTf();
    var incident = {}, neighbors = {}, dotEl = {};
    capEl = {};
    var eg = el("g", { "class": "net-edges" }, g);
    // ports: each capsule's edges leave and enter spread along the middle 70% of its side,
    // ordered by the other endpoint's y, so parallel relations stay separately traceable
    var outPort = {}, inPort = {};
    (function assignPorts() {
      var outs = {}, ins = {};
      links.forEach(function (L, li) {
        if (!at[L[0]] || !at[L[1]]) return;
        (outs[L[0]] = outs[L[0]] || []).push(li);
        (ins[L[1]] = ins[L[1]] || []).push(li);
      });
      function spread(byNode, port, otherOf) {
        Object.keys(byNode).forEach(function (id) {
          var es = byNode[id];
          es.sort(function (p2, q2) { return (at[otherOf(p2)].y - at[otherOf(q2)].y) || (p2 - q2); });
          var span2 = geo[id].h * 0.7;
          es.forEach(function (li, idx) {
            port[li] = at[id].y + (es.length < 2 ? 0 : (idx / (es.length - 1) - 0.5) * span2);
          });
        });
      }
      spread(outs, outPort, function (li) { return links[li][1]; });
      spread(ins, inPort, function (li) { return links[li][0]; });
    })();
    links.forEach(function (L, li) {
      var a = at[L[0]], c = at[L[1]];
      if (!a || !c) return;
      var ga = geo[L[0]], gc = geo[L[1]];
      var leftToRight = a.x <= c.x;
      var y1 = outPort[li] !== undefined ? outPort[li] : a.y;
      var y2 = inPort[li] !== undefined ? inPort[li] : c.y;
      var x1 = a.x + (leftToRight ? ga.w / 2 + 2 : -ga.w / 2 - 2);
      var x2 = c.x + (leftToRight ? -gc.w / 2 - (L[5] ? 2 : 7) : gc.w / 2 + (L[5] ? 2 : 7));
      var span = Math.abs((colOf[L[1]] || 0) - (colOf[L[0]] || 0));
      var d;
      if (!L[5] && span >= 2 && leftToRight) {
        // thread through a free slot in each column crossed, instead of arcing over the map
        var pts = [[x1, y1]];
        for (var cc = colOf[L[0]] + 1; cc < colOf[L[1]]; cc++) {
          var yw = y1 + (y2 - y1) * ((lay.colX[cc] - x1) / Math.max(x2 - x1, 1));
          pts.push([lay.colX[cc], lay.freeYNear(cc, yw)]);
        }
        pts.push([x2, y2]);
        d = "M" + pts[0][0] + "," + pts[0][1];
        for (var pi = 1; pi < pts.length; pi++) {
          var dx = (pts[pi][0] - pts[pi - 1][0]) * 0.5;
          d += " C" + (pts[pi - 1][0] + dx) + "," + pts[pi - 1][1] + " " + (pts[pi][0] - dx) + "," + pts[pi][1] + " " + pts[pi][0] + "," + pts[pi][1];
        }
      } else {
        var bow = Math.max(Math.abs(x2 - x1) * 0.45, 40) * (leftToRight ? 1 : -1);
        d = "M" + x1 + "," + y1 + " C" + (x1 + bow) + "," + y1 + " " + (x2 - bow) + "," + y2 + " " + x2 + "," + y2;
      }
      var grp = el("g", { "class": "net-edge" + (L[5] ? " undirected" : "") }, eg);
      var wire = el("path", { d: d, "class": "wire", "stroke-width": Math.min(0.75 + L[2] * 0.08, 1.3) }, grp);
      if (!L[5]) wire.setAttribute("marker-end", "url(#arrow)");
      el("path", { d: d, "class": "hit", "stroke-width": 13 }, grp);
      grp.addEventListener("click", function (ev) { ev.stopPropagation(); edgeCard(L, ev); });
      (incident[L[0]] = incident[L[0]] || []).push(grp);
      (incident[L[1]] = incident[L[1]] || []).push(grp);
      (neighbors[L[0]] = neighbors[L[0]] || []).push(L[1]);
      (neighbors[L[1]] = neighbors[L[1]] || []).push(L[0]);
    });
    focusOn = function (id) {
      g.classList.add("focus");
      if (dotEl[id]) dotEl[id].classList.add("nb");
      (incident[id] || []).forEach(function (e2) { e2.classList.add("lit"); });
      (neighbors[id] || []).forEach(function (nid) { var ng = dotEl[nid]; if (ng) ng.classList.add("nb"); });
    };
    focusOff = function (id) {
      g.classList.remove("focus");
      if (dotEl[id]) dotEl[id].classList.remove("nb");
      (incident[id] || []).forEach(function (e2) { e2.classList.remove("lit"); });
      (neighbors[id] || []).forEach(function (nid) { var ng = dotEl[nid]; if (ng) ng.classList.remove("nb"); });
    };
    items.forEach(function (id) {
      var m = DATA.concepts[id] || {}, p = at[id], ge = geo[id];
      var cg = el("g", { "class": "cap tone-" + (KIND_TONE[m.k] || "amethyst") + (id === "the-program" ? " program" : "") }, g);
      dotEl[id] = cg;
      capEl[id] = cg;
      el("rect", { x: p.x - ge.w / 2, y: p.y - ge.h / 2, width: ge.w, height: ge.h, rx: 10, "class": "pill" }, cg);
      var fs = ge.fs || 11.5;
      var t = el("text", { x: p.x, y: p.y + (ge.lines.length > 1 ? 4 - (fs + 2) / 2 : 4), "text-anchor": "middle", "font-size": fs, "class": "cap-title" }, cg);
      ge.lines.forEach(function (ln, li) {
        el("tspan", { x: p.x, dy: li ? fs + 2 : 0 }, t).textContent = ln;
      });
      if (m.s) {
        var st = el("text", { x: p.x, y: p.y + ge.h / 2 + 14, "text-anchor": "middle", "font-size": 10.5, "class": "nsub" }, cg);
        var words = String(m.s).split(/\s+/), line = "", used = 0, per = Math.max(Math.floor((ge.w + 70) / 5.9), 18);
        for (var i2 = 0; i2 < words.length && used < 2; i2++) {
          var cand = line ? line + " " + words[i2] : words[i2];
          if (cand.length > per && line) {
            el("tspan", { x: p.x, dy: used ? 12 : 0 }, st).textContent = used === 1 ? line + "…" : line;
            used++; line = words[i2];
          } else line = cand;
        }
        if (used < 2 && line) el("tspan", { x: p.x, dy: used ? 12 : 0 }, st).textContent = line;
      }
      cg.addEventListener("mouseenter", function () { if (!pinned) focusOn(id); });
      cg.addEventListener("mouseleave", function () { if (!pinned) focusOff(id); });
      cg.addEventListener("click", function (ev) { ev.stopPropagation(); nodeCard(id, ev); });
    });
  }

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
  function hideCard() {
    card.hidden = true;
    card.innerHTML = "";
    if (pinned && focusOff) focusOff(pinned);
    pinned = null;
  }
  function kindLabel(k) { return (DATA.kinds || {})[k] || k || ""; }
  function nodeCard(id, ev) {
    if (pinned && focusOff) focusOff(pinned);
    pinned = id;
    if (focusOn) focusOn(id);
    var m = DATA.concepts[id] || {};
    card.innerHTML = '<p class="card-head">' + esc(m.t || id) + ' <span class="kind">' + esc(kindLabel(m.k)) + "</span></p>"
      + (m.s ? "<p class=\"card-blurb\">" + esc(m.s) + "</p>" : "")
      + '<p class="card-meta muted">' + (m.prs ? m.prs + " merged PR(s) · " : "") + (m.w ? "wiki page" : "registry entry") + "</p>"
      + '<p class="card-actions"><button data-act="more">Read more</button><button data-act="cmt" class="quiet">Comment</button></p>';
    card.querySelector("[data-act=more]").addEventListener("click", function () { hideCard(); openFull(id); });
    card.querySelector("[data-act=cmt]").addEventListener("click", function (e2) { commentForm(id); placeCard(e2); });
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

  var COMMENT_API = "https://comments.alignmentworkspace.com";
  function commentForm(id) {
    var m = DATA.concepts[id] || {};
    card.innerHTML = '<p class="card-head">Comment on ' + esc(m.t || id) + "</p>"
      + '<input class="cmt-name" type="text" maxlength="80" placeholder="name (optional)">'
      + '<textarea class="cmt-body" maxlength="5000" rows="5" placeholder="What you want to say. It appears after review; it is filed publicly the moment you send it."></textarea>'
      + '<p class="card-actions"><button data-act="send">Send</button><button data-act="back" class="quiet">Back</button></p>'
      + '<p class="cmt-status muted"></p>';
    card.querySelector("[data-act=back]").addEventListener("click", function (e2) { nodeCard(id, e2); });
    card.querySelector("[data-act=send]").addEventListener("click", function () {
      var body = card.querySelector(".cmt-body").value.trim();
      var name = card.querySelector(".cmt-name").value.trim();
      var st = card.querySelector(".cmt-status");
      if (body.length < 3) { st.textContent = "Write something first."; return; }
      st.textContent = "Sending…";
      fetch(COMMENT_API, { method: "POST", headers: { "content-type": "application/json" },
        body: JSON.stringify({ concept: id, name: name, body: body }) })
        .then(function (r) { return r.json(); })
        .then(function (d2) {
          if (d2.ok) { st.innerHTML = 'Sent — it appears after review. <a href="' + d2.url + '">Filed record</a>.'; }
          else { throw new Error(d2.error || "failed"); }
        })
        .catch(function () {
          st.innerHTML = 'Could not send. <a href="https://github.com/A-M-Berns/alignment-workspace/issues/new?title='
            + encodeURIComponent("[comment] " + id) + "&body=" + encodeURIComponent(body)
            + '">File it directly</a> instead.';
        });
    });
  }
  function base(id) {
    return "/concepts/" + seg(id) + "/";
  }
  function openFull(id) {
    modal.classList.add("open");
    var m = DATA.concepts[id] || {};
    panelBody.innerHTML = '<p class="muted">Loading ' + esc(m.t || id) + "…</p>";
    fetch(base(id) + "frag.html").then(function (r) { if (!r.ok) throw 0; return r.text(); }).then(function (h) {
      panelBody.innerHTML = h + '<p class="muted popup-foot"><a href="' + base(id) + '">Open the full page →</a> · <a href="#" data-cmt>Comment on this concept</a></p>';
      var cl = panelBody.querySelector("[data-cmt]");
      if (cl) cl.addEventListener("click", function (e2) { e2.preventDefault(); closeFull(); commentForm(id); placeCard(e2); });
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
    var rows = [["bone", K.goal || "goal"], ["emerald", K.construction || "construction"], ["sapphire", K.object || "object"], ["amber", K.work || "work"], ["amethyst", K.philosophy || "philosophy"], ["garnet", K.companion || "companion"]];
    lg.innerHTML = rows.map(function (r) { return '<span class="lg tone-' + r[0] + '"><span class="dotc"></span>' + esc(r[1]) + "</span>"; }).join("");
  }

  // pan and zoom; capture the pointer only once a drag has started, or clicks retarget to the svg
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
    var kNew = Math.max(0.25, Math.min(tf.k * Math.exp(-ev.deltaY * 0.0016), 9));
    tf.x = mx - (mx - tf.x) * (kNew / tf.k);
    tf.y = my - (my - tf.y) * (kNew / tf.k);
    tf.k = kNew;
    applyTf();
  }, { passive: false });
  document.addEventListener("keydown", function (ev) {
    if ((ev.metaKey || ev.ctrlKey) && ev.key.toLowerCase() === "f" && !ev.shiftKey && !ev.altKey) {
      var inp = document.querySelector("header.top input[type=search]");
      if (inp) { ev.preventDefault(); inp.focus(); inp.select(); }
      return;
    }
    if (ev.key !== "Escape") return;
    if (modal.classList.contains("open")) closeFull();
    else hideCard();
  });
  window.addEventListener("resize", render);

  // map search: the header box jumps the canvas to matches; enter cycles when there are several
  (function () {
    var input = document.querySelector("header.top input[type=search]");
    var form = input && input.closest("form");
    if (!input) return;
    input.setAttribute("placeholder", "search the map");
    var chip = document.createElement("span");
    chip.className = "search-chip";
    input.insertAdjacentElement("afterend", chip);
    var matches = [], idx = -1, lastQ = "";
    function find(q) {
      q = q.trim().toLowerCase();
      matches = [];
      if (q.length < 2) return;
      DATA.items.forEach(function (id) {
        var m = DATA.concepts[id] || {};
        if ((m.t || id).toLowerCase().indexOf(q) >= 0 || (m.s || "").toLowerCase().indexOf(q) >= 0) matches.push(id);
      });
    }
    var tween = null;
    function jumpTo(id) {
      var p = at[id];
      if (!p) return;
      var b = box(), kT = Math.max(tf.k, 1.5), from = { k: tf.k, x: tf.x, y: tf.y };
      var to = { k: kT, x: b.w / 2 - p.x * kT, y: b.h / 2 - p.y * kT };
      var t0 = null;
      if (tween) cancelAnimationFrame(tween);
      (function step(ts) {
        if (!t0) t0 = ts;
        var u = Math.min((ts - t0) / 360, 1), e2 = u < 0.5 ? 4 * u * u * u : 1 - Math.pow(-2 * u + 2, 3) / 2;
        tf = { k: from.k + (to.k - from.k) * e2, x: from.x + (to.x - from.x) * e2, y: from.y + (to.y - from.y) * e2 };
        applyTf();
        if (u < 1) tween = requestAnimationFrame(step);
      })(performance.now());
      svg.querySelectorAll("g.cap.hit-mark").forEach(function (e2) { e2.classList.remove("hit-mark"); });
      var cg = capEl[id];
      if (cg) {
        cg.classList.add("hit-mark");
        setTimeout(function () { cg.classList.remove("hit-mark"); }, 1600);
      }
    }
    function go(step) {
      if (input.value !== lastQ) { lastQ = input.value; find(lastQ); idx = -1; }
      if (!matches.length) { chip.textContent = input.value.trim().length >= 2 ? "no match" : ""; return; }
      idx = (idx + step + matches.length) % matches.length;
      chip.textContent = (idx + 1) + " / " + matches.length;
      jumpTo(matches[idx]);
    }
    input.addEventListener("input", function () {
      lastQ = input.value;
      find(lastQ);
      idx = -1;
      chip.textContent = matches.length ? matches.length + " match" + (matches.length === 1 ? "" : "es") : (lastQ.trim().length >= 2 ? "no match" : "");
    });
    if (form) form.addEventListener("submit", function (ev) { ev.preventDefault(); go(1); });
    input.addEventListener("keydown", function (ev) { if (ev.key === "Enter") { ev.preventDefault(); go(ev.shiftKey ? -1 : 1); } });
  })();

  fetch("/assets/map.json").then(function (r) { return r.json(); }).then(function (d) {
    DATA = d;
    legend();
    var fitBtn = document.getElementById("map-fit");
    if (fitBtn) fitBtn.addEventListener("click", function () { var t2 = fitAll || home; tf = { k: t2.k, x: t2.x, y: t2.y }; applyTf(); });
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
