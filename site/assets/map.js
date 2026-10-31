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

  var DATA = null, tf = { k: 1, x: 0, y: 0 }, home = { k: 1, x: 0, y: 0 }, fitAll = null, far = false;
  var defs = document.createElementNS(NS, "defs");
  svg.appendChild(defs);
  var cam = document.createElementNS(NS, "g");
  svg.appendChild(cam);
  var mk = document.createElementNS(NS, "marker");
  mk.setAttribute("id", "arrow");
  mk.setAttribute("viewBox", "0 0 8 8");
  mk.setAttribute("refX", "7.4"); mk.setAttribute("refY", "4");
  mk.setAttribute("markerUnits", "userSpaceOnUse");
  mk.setAttribute("markerWidth", "9"); mk.setAttribute("markerHeight", "9");
  mk.setAttribute("orient", "auto");
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
    if (!far && tf.k <= 0.7) { far = true; svg.classList.add("far"); }
    else if (far && tf.k >= 0.8) { far = false; svg.classList.remove("far"); }
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

  // radial (maintainer directive, 2026-10-31): the overall program is the one node at the
  // centre; the six lines take angular sectors around it, ordered so lines with shared
  // upstream support sit adjacent; every other concept sits at the circular mean of the
  // lines it feeds, at a radius given by its dependency depth, so shared foundations fall
  // between the sectors they serve. Rings are elliptical (wide) because capsules are
  // horizontal text. Importance shows as capsule area over a readable type floor.
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
    // rings: dependency depth, the program at zero
    var dmax = 1;
    items.forEach(function (id) { dmax = Math.max(dmax, (meta[id] || {}).d || 0); });
    var ring = {};
    items.forEach(function (id) { ring[id] = id === "the-program" ? 0 : ((meta[id] || {}).d || dmax); });
    // the set of lines each node feeds
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
    // order the lines around the circle so pairs with shared support sit adjacent
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
    function ringDist(p2, q2, n2) { var d2 = Math.abs(p2 - q2); return Math.min(d2, n2 - d2); }
    function permCost(order) {
      var at2 = {};
      order.forEach(function (gid, idx) { at2[gid] = idx; });
      var cost = 0;
      Object.keys(shared).forEach(function (key) {
        var pq = key.split("|");
        cost += shared[key] * ringDist(at2[pq[0]], at2[pq[1]], order.length);
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
    var gAngle = {};
    goalOrder.forEach(function (gid, idx) { gAngle[gid] = -Math.PI / 2 + idx * (2 * Math.PI / goalOrder.length); });
    // each node's angle: the circular mean of the lines it feeds; those feeding nothing
    // named take the mean of their neighbours, settled over a few passes
    var ang = {};
    items.forEach(function (id) {
      if (id === "the-program") { ang[id] = 0; return; }
      var gs = reach[id] || [];
      if (gs.length) {
        var vx = 0, vy = 0;
        gs.forEach(function (gg) { vx += Math.cos(gAngle[gg]); vy += Math.sin(gAngle[gg]); });
        ang[id] = Math.atan2(vy, vx);
      }
    });
    for (var pass = 0; pass < 4; pass++) {
      items.forEach(function (id) {
        if (ang[id] !== undefined) return;
        var vx = 0, vy = 0, n2 = 0;
        (nbAll[id] || []).forEach(function (nb) {
          if (ang[nb] !== undefined && nb !== "the-program") { vx += Math.cos(ang[nb]); vy += Math.sin(ang[nb]); n2++; }
        });
        if (n2) ang[id] = Math.atan2(vy, vx);
      });
    }
    var spare = 0;
    items.forEach(function (id) { if (ang[id] === undefined) { ang[id] = spare * 2.399963; spare++; } });
    // homogeneous density (maintainer directive, 2026-10-31): rings are filled to their
    // capacity — each holds as many capsules as its circumference carries at one constant
    // gap — taken in dependency-depth order, so depth still reads outward but no ring is
    // crowded or bare. Within a ring, capsules sit around the whole circle in affinity
    // order with width-proportional arcs, rotated to best match where their lines live.
    function norm2(a2) { while (a2 > Math.PI) a2 -= 2 * Math.PI; while (a2 < -Math.PI) a2 += 2 * Math.PI; return a2; }
    // a mild blend toward even occupancy rounds the disc without smearing the sectors
    var evened = items.filter(function (id) { return id !== "the-program"; })
      .sort(function (a2, b2) { return ang[a2] - ang[b2] || a2.localeCompare(b2); });
    evened.forEach(function (id, idx) {
      var even = -Math.PI + (idx + 0.5) * 2 * Math.PI / evened.length;
      ang[id] = norm2(ang[id] + norm2(even - ang[id]) * 0.45);
    });
    var EX = 1.22, PITCH = 265, R0 = 330, GAP = 78;
    var order = items.filter(function (id) { return id !== "the-program"; })
      .sort(function (a2, b2) { return (ring[a2] - ring[b2]) || (ang[a2] - ang[b2]) || a2.localeCompare(b2); });
    var pos = { "the-program": { x: 0, y: 0 } };
    var rk = 0, cursor = 0;
    while (cursor < order.length) {
      var r2 = R0 + rk * PITCH;
      var a4 = EX * r2, b4 = r2;
      var circ = Math.PI * (3 * (a4 + b4) - Math.sqrt((3 * a4 + b4) * (a4 + 3 * b4)));
      var members = [], used = 0;
      while (cursor < order.length) {
        var nid = order[cursor];
        var need = geo[nid].w + GAP;
        if (members.length && used + need > circ) break;
        members.push(nid); used += need; cursor++;
      }
      members.sort(function (a2, b2) { return ang[a2] - ang[b2] || a2.localeCompare(b2); });
      // each capsule starts at its affinity angle and moves only as far as the constant
      // gap demands, so sectors stay where their lines live and sparse arcs stay sparse
      var theta = {};
      members.forEach(function (id) { theta[id] = ang[id]; });
      var rMean = (a4 + b4) / 2;
      for (var it2 = 0; it2 < 80; it2++) {
        var moved2 = false;
        for (var i2 = 0; i2 < members.length; i2++) {
          var m1 = members[i2], m2 = members[(i2 + 1) % members.length];
          if (m1 === m2) continue;
          var need2 = ((geo[m1].w + geo[m2].w) / 2 + GAP) / rMean;
          var gap2 = norm2(theta[m2] - theta[m1]);
          if (gap2 < 0) gap2 += 2 * Math.PI;
          if (gap2 < need2) {
            var push2 = (need2 - gap2) / 2;
            theta[m1] = norm2(theta[m1] - push2);
            theta[m2] = norm2(theta[m2] + push2);
            moved2 = true;
          }
        }
        if (!moved2) break;
      }
      members.forEach(function (id) {
        pos[id] = { x: a4 * Math.cos(theta[id]), y: b4 * Math.sin(theta[id]) };
      });
      rk++;
    }
    for (var iter = 0; iter < 60; iter++) {
      var bumped = false;
      for (var ii = 0; ii < items.length; ii++) for (var jj = ii + 1; jj < items.length; jj++) {
        var A = pos[items[ii]], Bq = pos[items[jj]], ga = geo[items[ii]], gb = geo[items[jj]];
        var ox = (ga.w + gb.w) / 2 + 20 - Math.abs(A.x - Bq.x);
        var oy = (ga.h + gb.h) / 2 + 20 - Math.abs(A.y - Bq.y);
        if (ox > 0 && oy > 0) {
          var dx = A.x - Bq.x, dy = A.y - Bq.y;
          var len = Math.sqrt(dx * dx + dy * dy) || 1;
          var push = (Math.min(ox, oy) / 2 + 1);
          A.x += (dx / len) * push; A.y += (dy / len) * push;
          Bq.x -= (dx / len) * push; Bq.y -= (dy / len) * push;
          bumped = true;
        }
      }
      if (!bumped) break;
    }
    pos["the-program"] = { x: 0, y: 0 };
    // frame: shift to positive coordinates
    var xMin = 1e9, xMax = -1e9, yMin = 1e9, yMax = -1e9;
    items.forEach(function (id) {
      xMin = Math.min(xMin, pos[id].x - geo[id].w / 2); xMax = Math.max(xMax, pos[id].x + geo[id].w / 2);
      yMin = Math.min(yMin, pos[id].y - geo[id].h / 2); yMax = Math.max(yMax, pos[id].y + geo[id].h / 2);
    });
    var pad = 110;
    items.forEach(function (id) { pos[id].x += pad - xMin; pos[id].y += pad - yMin; });
    return { pos: pos, geo: geo, w: xMax - xMin + 2 * pad, h: yMax - yMin + 2 * pad,
             cx: pad - xMin, cy: pad - yMin, ring: ring };
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

    svg.__layout = { at: at, geo: geo };
    var ax = el("g", { "class": "axis" }, g);

    // boot at twice the whole-map fit, centred on the program, so capsules open at
    // reading size; the map overflows the viewport and the user pans
    home = { k: Math.min(Math.min(b.w / lay.w, (b.h - 40) / lay.h) * 2, 1.1), x: 0, y: 0 };
    home.x = b.w / 2 - lay.cx * home.k;
    home.y = b.h / 2 - lay.cy * home.k;
    fitAll = { k: Math.min(b.w / lay.w, (b.h - 40) / lay.h) };
    fitAll.x = (b.w - lay.w * fitAll.k) / 2;
    fitAll.y = (b.h - lay.h * fitAll.k) / 2;
    tf = { k: home.k, x: home.x, y: home.y };
    applyTf();
    var incident = {}, neighbors = {}, dotEl = {};
    capEl = {};
    var eg = el("g", { "class": "net-edges" }, g);
    // edges attach where the capsule faces the other endpoint, and bow gently toward the
    // centre, so the flow reads as an inward spiral to the program
    function boundaryPoint(id, tx, ty, inset) {
      var p = at[id], g2 = geo[id];
      var dx = tx - p.x, dy = ty - p.y;
      var sx = dx !== 0 ? (g2.w / 2 + inset) / Math.abs(dx) : 1e9;
      var sy = dy !== 0 ? (g2.h / 2 + inset) / Math.abs(dy) : 1e9;
      var s = Math.min(sx, sy);
      return [p.x + dx * s, p.y + dy * s];
    }
    links.forEach(function (L) {
      var a = at[L[0]], c = at[L[1]];
      if (!a || !c) return;
      var p1 = boundaryPoint(L[0], c.x, c.y, 2);
      var p2 = boundaryPoint(L[1], a.x, a.y, L[5] ? 2 : 4);
      var mx = (p1[0] + p2[0]) / 2, my = (p1[1] + p2[1]) / 2;
      var qx = mx + (lay.cx - mx) * 0.16, qy = my + (lay.cy - my) * 0.16;
      var d = "M" + p1[0] + "," + p1[1] + " Q" + qx + "," + qy + " " + p2[0] + "," + p2[1];
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
    var tween = null, searchLit = null;
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
        if (searchLit && focusOff && pinned !== searchLit) focusOff(searchLit);
        searchLit = id;
        if (!pinned && focusOn) focusOn(id);
        setTimeout(function () {
          cg.classList.remove("hit-mark");
          if (!pinned && focusOff && searchLit === id) { focusOff(id); searchLit = null; }
        }, 1600);
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

  fetch("/assets/map.json", { cache: "no-cache" }).then(function (r) { return r.json(); }).then(function (d) {
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
