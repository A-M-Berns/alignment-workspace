// The landing's highlight follows the tiling: sample the canvas, take the most
// frequent colour that is not the near-black ground, lift it to a readable
// luminance, and set it as --accent (the tile hover border reads it).
(function () {
  "use strict";
  var cv = document.getElementById("wang-tiles");
  if (!cv) return;
  var off = document.createElement("canvas");
  var W = 48;
  function tick() {
    if (!cv.width || !cv.height) return;
    var H = Math.max(1, Math.round(W * cv.height / cv.width));
    off.width = W; off.height = H;
    var ctx = off.getContext("2d", { willReadFrequently: true });
    ctx.drawImage(cv, 0, 0, W, H);
    var d;
    try { d = ctx.getImageData(0, 0, W, H).data; } catch (e) { return; }
    var counts = {}, best = null, bestN = 0;
    for (var i = 0; i < d.length; i += 4) {
      var r = d[i], g = d[i + 1], b = d[i + 2];
      var lum = 0.299 * r + 0.587 * g + 0.114 * b;
      if (lum < 26) continue; // the ground
      var key = ((r >> 4) << 8) | ((g >> 4) << 4) | (b >> 4);
      var c = (counts[key] = (counts[key] || 0) + 1);
      if (c > bestN) { bestN = c; best = [r, g, b]; }
    }
    if (!best) return;
    var lum2 = 0.299 * best[0] + 0.587 * best[1] + 0.114 * best[2];
    if (lum2 < 96) { // lift a dark dominant so the highlight stays visible
      var f = 96 / Math.max(lum2, 1);
      best = best.map(function (v) { return Math.min(255, Math.round(v * f)); });
    }
    document.documentElement.style.setProperty("--accent", "rgb(" + best[0] + " " + best[1] + " " + best[2] + ")");
  }
  setInterval(tick, 1200);
  setTimeout(tick, 400);
})();
