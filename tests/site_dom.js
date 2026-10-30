// The map's behaviour gate, run by tests/site_build.py against a finished build directory:
//   node tests/site_dom.js <build dir>
// It executes site/assets/map.js in a stub DOM against the build's map.json and fails when the app
// crashes into its could-not-load fallback, renders the wrong number of capsules or edges, a node or
// edge click produces no card, a sampled fragment is missing, or any two capsules overlap. Silence is
// not success: every terminal state below exits loudly.
"use strict";
const fs = require("fs");
const path = require("path");

const dir = process.argv[2];
if (!dir) { console.error("usage: node tests/site_dom.js <build dir>"); process.exit(2); }
const data = JSON.parse(fs.readFileSync(path.join(dir, "assets", "map.json"), "utf8"));

let created = [], cardHtml = null, crashed = false;
function el(tag) {
  const e = {
    _tag: tag, _cls: "", _ls: {}, children: [], style: {},
    classList: { toggle() {}, add() {}, remove() {}, contains: () => false },
    setAttribute(k, v) { if (k === "class") this._cls = v; }, getAttribute() { return null; },
    appendChild(c) { this.children.push(c); return c; },
    insertBefore(c) { this.children.unshift(c); return c; },
    addEventListener(t, f) { (this._ls[t] = this._ls[t] || []).push(f); },
    querySelector() { return { addEventListener() {} }; },
    querySelectorAll() { return []; },
    getBoundingClientRect() { return { width: 1280, height: 800, left: 0, top: 0 }; },
    checked: true, offsetHeight: 200,
  };
  Object.defineProperty(e, "textContent", { get() { return ""; }, set() {} });
  Object.defineProperty(e, "innerHTML", { get() { return e.__html || ""; }, set(v) { e.__html = v; if (e === ids["map-card"]) cardHtml = v; } });
  Object.defineProperty(e, "hidden", { get() { return e.__hid; }, set(v) { e.__hid = v; } });
  Object.defineProperty(e, "outerHTML", { set() { crashed = true; } });
  created.push(e);
  return e;
}
const ids = {};
global.document = {
  getElementById(id) { return ids[id] || (ids[id] = el("div")); },
  createElementNS(ns, tag) { return el(tag); },
  createElement() { return el("div"); },
  querySelector() { return null; },
  querySelectorAll() { return []; },
  addEventListener() {},
};
global.window = { addEventListener() {} };
global.location = { hash: "", search: "" };
global.history = { replaceState() {} };
global.requestAnimationFrame = (f) => { setImmediate(() => f(Date.now())); return 1; };
global.fetch = (u) => {
  const rel = String(u).replace(/^\//, "").replace(/\/$/, "/index.html");
  const file = path.join(dir, rel);
  if (!fs.existsSync(file)) return Promise.resolve({ ok: false, text: () => Promise.resolve(""), json: () => Promise.reject(new Error("404")) });
  const body = fs.readFileSync(file, "utf8");
  return Promise.resolve({ ok: true, text: () => Promise.resolve(body), json: () => Promise.resolve(JSON.parse(body)) });
};

const src = fs.readFileSync(path.join(dir, "assets", "map.js"), "utf8");
eval(src);

setTimeout(() => {
  const fail = (msg) => { console.error("SITE DOM GATE FAILED:", msg); process.exit(1); };
  if (crashed) fail("the app fell into its could-not-load fallback");
  const caps = created.filter((e) => (e._cls || "").indexOf("cap tone") === 0);
  const edges = created.filter((e) => e._cls === "net-edge" || e._cls === "net-edge undirected");
  if (caps.length !== data.items.length) fail(`capsules ${caps.length} != concepts ${data.items.length}`);
  if (edges.length !== data.links.length) fail(`edge groups ${edges.length} != links ${data.links.length}`);
  const ev = { stopPropagation() {}, clientX: 300, clientY: 300, preventDefault() {} };
  cardHtml = null;
  (caps[3]._ls.click || []).forEach((f) => f(ev));
  if (!cardHtml || cardHtml.indexOf("card-head") < 0) fail("a node click produced no card");
  cardHtml = null;
  (edges[0]._ls.click || []).forEach((f) => f(ev));
  if (!cardHtml || cardHtml.indexOf("card-head") < 0) fail("an edge click produced no card");
  const sample = data.items[0];
  const frag = path.join(dir, "concepts", sample.replace(/\//g, "--"), "frag.html");
  if (!fs.existsSync(frag)) fail(`missing fragment for ${sample}`);
  const L = ids["map"].__layout;
  if (!L) fail("the layout was not exposed");
  const names = Object.keys(L.at);
  for (let i = 0; i < names.length; i++) for (let j = i + 1; j < names.length; j++) {
    const a = L.at[names[i]], b = L.at[names[j]], ga = L.geo[names[i]], gb = L.geo[names[j]];
    if (Math.abs(a.x - b.x) < (ga.w + gb.w) / 2 + 10 && Math.abs(a.y - b.y) < (ga.h + gb.h) / 2 + 12) {
      fail(`capsules overlap: ${names[i]} / ${names[j]}`);
    }
  }
  console.log(`SITE DOM GATE: app boots, ${caps.length} capsules, ${edges.length} edges, cards open, fragments present, no overlaps`);
  process.exit(0);
}, 1200);
