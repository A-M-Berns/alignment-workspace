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

  var DATA = null, tf = { k: 1, x: 0, y: 0 }, home = { k: 1, x: 0, y: 0 };
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

  // layered flow with goal bands (GPT Astra consult, 2026-10-30): ranks from goal distance with
  // variable column pitch from real capsule widths; rows are bands by the first goal a node reaches,
  // staircase-ordered; within a band, median-ordered. The program sits alone at the far right, centred.
  var GOALS = ["corrigibility-line", "normative-induction", "normativity-line", "legitimacy-line", "deference-line", "openness-line"];
  function layout(items, links) {
    var meta = DATA.concepts, i;
    var succ = {}, nbAll = {};
    links.forEach(function (L) {
      if (!L[5]) (succ[L[0]] = succ[L[0]] || []).push(L[1]);
      (nbAll[L[0]] = nbAll[L[0]] || []).push(L[1]);
      (nbAll[L[1]] = nbAll[L[1]] || []).push(L[0]);
    });
    // band: the first goal reached along directed edges (breadth first, ties by the staircase order)
    var band = {};
    GOALS.forEach(function (gid) { band[gid] = gid; });
    items.forEach(function (id) {
      if (band[id] || id === "the-program") return;
      var seen = {}, q = [id];
      seen[id] = 1;
      while (q.length) {
        var nxt = [], found = null;
        for (var qi = 0; qi < q.length; qi++) {
          (succ[q[qi]] || []).forEach(function (s) {
            if (GOALS.indexOf(s) >= 0 && (found === null || GOALS.indexOf(s) < GOALS.indexOf(found))) found = s;
            if (!seen[s]) { seen[s] = 1; nxt.push(s); }
          });
        }
        if (found) { band[id] = found; break; }
        q = nxt;
      }
    });
    for (var pass = 0; pass < 4; pass++) {
      items.forEach(function (id) {
        if (band[id] || id === "the-program") return;
        var nb = (nbAll[id] || []).filter(function (n) { return band[n]; });
        if (nb.length) band[id] = band[nb[0]];
      });
    }
    items.forEach(function (id) { if (!band[id] && id !== "the-program") band[id] = "context"; });
    // capsule geometry
    var geo = {};
    items.forEach(function (id) {
      var tt = (meta[id] || {}).t || id;
      var lines = titleLines(tt, 20);
      var wch = Math.max.apply(null, lines.map(function (L) { return L.length; }));
      var cw = Math.max(Math.min(wch * 7.2 + 30, 196), 96);
      var chh = lines.length > 1 ? 48 : 34;
      if (id === "the-program") { cw += 14; chh += 6; }
      geo[id] = { w: cw, h: chh, lines: lines };
    });
    // columns: rank by goal distance, pitch from the widest capsule per rank
    var dmax = 1;
    items.forEach(function (id) { dmax = Math.max(dmax, (meta[id] || {}).d || 0); });
    var colOf = {};
    items.forEach(function (id) { colOf[id] = id === "the-program" ? dmax : dmax - ((meta[id] || {}).d || 0); });
    var colW = [];
    items.forEach(function (id) { var c = colOf[id]; colW[c] = Math.max(colW[c] || 0, geo[id].w); });
    var colX = [], xcur = 150;
    for (i = 0; i <= dmax; i++) {
      var cwid = colW[i] || 0;
      colX[i] = xcur + cwid / 2;
      xcur += cwid ? Math.max(cwid + 70, 216) : 0;
    }
    var w = xcur + 150;
    // rows: the bands in staircase order. Within a band, only capsules in the same column stack;
    // different columns share the band's vertical extent, so the map stays wide, not tall.
    var bandOrder = GOALS.concat(["context"]);
    var rows = {};
    items.forEach(function (id) { if (id !== "the-program") (rows[band[id]] = rows[band[id]] || []).push(id); });
    var y = {}, gap = 30, bandGap = 84, ycur = 90, bandSpan = {};
    function stackBand(b) {
      var byCol = {};
      (rows[b] || []).forEach(function (id) { (byCol[colOf[id]] = byCol[colOf[id]] || []).push(id); });
      var bandH = 0;
      Object.keys(byCol).forEach(function (c) {
        var hh = byCol[c].reduce(function (s, id) { return s + geo[id].h; }, 0) + gap * (byCol[c].length - 1);
        bandH = Math.max(bandH, hh);
      });
      return { byCol: byCol, bandH: bandH };
    }
    bandOrder.forEach(function (b) {
      if (!(rows[b] || []).length) return;
      var st = stackBand(b);
      bandSpan[b] = [ycur, ycur + st.bandH];
      Object.keys(st.byCol).forEach(function (c) {
        var col = st.byCol[c];
        var step = st.bandH / col.length;
        col.forEach(function (id, i2) { y[id] = ycur + (i2 + 0.5) * step; });
      });
      ycur += st.bandH + bandGap;
    });
    var h = Math.max(ycur + 40, 640);
    // median sweeps: reorder each band-column stack toward its neighbours, keeping the stack centred
    for (var sweep = 0; sweep < 6; sweep++) {
      bandOrder.forEach(function (b) {
        if (!bandSpan[b]) return;
        var st = stackBand(b);
        Object.keys(st.byCol).forEach(function (c) {
          var col = st.byCol[c];
          if (col.length < 2) return;
          col.sort(function (a, bb) {
            var ma = (nbAll[a] || []).reduce(function (s, n) { return s + (y[n] || 0); }, 0) / Math.max((nbAll[a] || []).length, 1);
            var mb = (nbAll[bb] || []).reduce(function (s, n) { return s + (y[n] || 0); }, 0) / Math.max((nbAll[bb] || []).length, 1);
            return (ma || 0) - (mb || 0) || a.localeCompare(bb);
          });
          var step = (bandSpan[b][1] - bandSpan[b][0]) / col.length;
          col.forEach(function (id, i2) { y[id] = bandSpan[b][0] + (i2 + 0.5) * step; });
        });
      });
    }
    // interleave: members of a stack step alternately left and right of their column line
    var stackIndex = {};
    bandOrder.forEach(function (b) {
      if (!bandSpan[b]) return;
      var st = stackBand(b);
      Object.keys(st.byCol).forEach(function (c) {
        st.byCol[c].slice().sort(function (a, bb) { return y[a] - y[bb]; }).forEach(function (id, i2) { stackIndex[id] = i2; });
      });
    });
    var pos = {};
    items.forEach(function (id) {
      var sx = (((stackIndex[id] || 0) % 2) * 2 - 1) * Math.min((colW[colOf[id]] || 120) * 0.2 + 14, 46);
      pos[id] = { x: colX[colOf[id]] + (id === "the-program" ? 0 : sx), y: y[id] };
    });
    if (pos["the-program"]) pos["the-program"].y = h / 2;
    var bands = bandOrder.filter(function (b) { return rows[b] && rows[b].length && b !== "context"; })
      .map(function (b) { return { label: ((meta[b] || {}).t || b), y0: bandSpan[b][0], y1: bandSpan[b][1] }; });
    if (rows.context && rows.context.length) bands.push({ label: "context", y0: bandSpan.context[0], y1: bandSpan.context[1] });
    return { pos: pos, geo: geo, w: w, h: h, bands: bands };
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
    var ax = el("g", { "class": "axis" }, g);

    home = { k: Math.min(b.w / lay.w, 1), x: 0, y: 0 };
    home.x = (b.w - lay.w * home.k) / 2;
    home.y = (b.h - lay.h * home.k) / 2;
    tf = { k: home.k, x: home.x, y: home.y };
    applyTf();
    var incident = {}, neighbors = {}, dotEl = {};
    capEl = {};
    var eg = el("g", { "class": "net-edges" }, g);
    links.forEach(function (L) {
      var a = at[L[0]], c = at[L[1]];
      if (!a || !c) return;
      var ga = geo[L[0]], gc = geo[L[1]];
      var leftToRight = a.x <= c.x;
      var x1 = a.x + (leftToRight ? ga.w / 2 + 2 : -ga.w / 2 - 2), y1 = a.y;
      var x2 = c.x + (leftToRight ? -gc.w / 2 - (L[5] ? 2 : 7) : gc.w / 2 + (L[5] ? 2 : 7)), y2 = c.y;
      var bow = Math.max(Math.abs(x2 - x1) * 0.45, 40) * (leftToRight ? 1 : -1);
      var d = "M" + x1 + "," + y1 + " C" + (x1 + bow) + "," + y1 + " " + (x2 - bow) + "," + y2 + " " + x2 + "," + y2;
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
      var t = el("text", { x: p.x, y: p.y + (ge.lines.length > 1 ? -2.5 : 4), "text-anchor": "middle", "font-size": id === "the-program" ? 13 : 11.5, "class": "cap-title" }, cg);
      ge.lines.forEach(function (ln, li) {
        el("tspan", { x: p.x, dy: li ? 13.5 : 0 }, t).textContent = ln;
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
      + '<p class="card-actions"><button data-act="more">Read more</button><a class="comment-link" href="' + commentUrl(id) + '">Comment</a></p>';
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

  function commentUrl(id) {
    var m = DATA.concepts[id] || {};
    var title = encodeURIComponent("[concept] " + id + ": comment");
    var body = encodeURIComponent("concept: " + id + "\nmap: /#c=" + seg(id) + "\n\n## What you want to say\n\n");
    return "https://github.com/A-M-Berns/alignment-workspace/issues/new?title=" + title + "&body=" + body;
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
      panelBody.innerHTML = h + '<p class="muted popup-foot"><a href="' + base(id) + '">Open the full page →</a> · <a href="' + commentUrl(id) + '">Comment on this concept</a></p>';
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
