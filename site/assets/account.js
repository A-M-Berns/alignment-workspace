// GitHub sign-in. Identity is the reader's own GitHub account, matched to a handle
// through graph/policy.yaml's mapping (shipped in /assets/account.json). Sign-in is the
// device flow through a secretless relay, or a pasted fine-grained token; the token
// lives only in this browser's storage. Submission stays a pull request from the
// reader's own fork, assembled here against api.github.com — the site accepts no write.
(function () {
  "use strict";
  var API = "https://api.github.com";
  var cfg = null;       // {repo, relay, handles: {github login -> handle}}
  var auth = null;      // {token, login, handle}
  try { auth = JSON.parse(localStorage.getItem("aw-auth") || "null"); } catch (e) { /* unavailable */ }

  function gh(path, opts) {
    opts = opts || {};
    opts.headers = Object.assign({
      Accept: "application/vnd.github+json",
      Authorization: "Bearer " + auth.token,
    }, opts.headers || {});
    if (opts.body && typeof opts.body !== "string") { opts.body = JSON.stringify(opts.body); }
    return fetch(API + path, opts).then(function (r) {
      if (r.status === 404) return null;
      if (!r.ok) return r.json().catch(function () { return {}; }).then(function (j) {
        throw new Error("GitHub said " + r.status + (j.message ? ": " + j.message : ""));
      });
      return r.status === 204 ? {} : r.json();
    });
  }
  function b64(s) { return btoa(unescape(encodeURIComponent(s))); }
  function unb64(s) { return decodeURIComponent(escape(atob(s.replace(/\n/g, "")))); }
  function save() { try { localStorage.setItem("aw-auth", JSON.stringify(auth)); } catch (e) { /* unavailable */ } }

  function chip() {
    var m = document.getElementById("account");
    if (!m || !cfg) return;
    if (auth && auth.login) {
      m.innerHTML = '<span class="acct">' + (auth.handle ? auth.handle : "@" + auth.login) +
        ' <button type="button" class="acct-out">sign out</button></span>';
      m.querySelector(".acct-out").onclick = function () {
        auth = null; try { localStorage.removeItem("aw-auth"); } catch (e) { /* unavailable */ }
        chip();
      };
    } else {
      m.innerHTML = '<button type="button" class="acct-in">sign in</button>';
      m.querySelector(".acct-in").onclick = openDialog;
    }
  }

  function finishLogin(token, status) {
    auth = { token: token };
    return gh("/user").then(function (u) {
      auth.login = u.login;
      auth.handle = cfg.handles[u.login] || null;
      save(); chip();
      status(auth.handle
        ? "Signed in as " + auth.handle + "."
        : "Signed in as @" + u.login + " — no handle in graph/policy.yaml maps to this account yet, so scores can be prepared but not submitted; propose a handle from any score's receipt.");
    });
  }

  function openDialog() {
    var old = document.getElementById("acct-dialog");
    if (old) old.remove();
    var d = document.createElement("dialog");
    d.id = "acct-dialog";
    d.innerHTML =
      '<h3>Sign in with GitHub</h3>' +
      (cfg.relay
        ? '<p><button type="button" class="dev-start">Get a device code</button></p><p class="dev-note muted"></p>'
        : '<p class="muted">The device-flow relay is not configured on this deployment.</p>') +
      '<p class="muted">Or paste a fine-grained token (public repositories, contents read/write on your fork):</p>' +
      '<p><input type="password" class="pat" placeholder="github_pat_…" size="28"> ' +
      '<button type="button" class="pat-go">Use it</button></p>' +
      '<p class="acct-status muted"></p>' +
      '<p><button type="button" class="acct-close">Close</button></p>';
    document.body.appendChild(d);
    d.showModal();
    var status = function (t) { d.querySelector(".acct-status").textContent = t; };
    d.querySelector(".acct-close").onclick = function () { d.close(); d.remove(); };
    d.querySelector(".pat-go").onclick = function () {
      var t = d.querySelector(".pat").value.trim();
      if (!t) return;
      finishLogin(t, status).catch(function (e) { auth = null; status(String(e.message || e)); });
    };
    var dev = d.querySelector(".dev-start");
    if (dev) dev.onclick = function () {
      dev.disabled = true;
      fetch(cfg.relay + "/device/code", { method: "POST", headers: { "Content-Type": "application/json" }, body: "{}" })
        .then(function (r) { return r.json(); })
        .then(function (c) {
          d.querySelector(".dev-note").innerHTML =
            'Enter <strong>' + c.user_code + '</strong> at <a href="' + c.verification_uri + '" target="_blank" rel="noopener">' +
            c.verification_uri + "</a> — waiting…";
          var every = Math.max(c.interval || 5, 5) * 1000;
          var until = Date.now() + (c.expires_in || 900) * 1000;
          (function poll() {
            if (Date.now() > until) { status("The code expired; start again."); dev.disabled = false; return; }
            setTimeout(function () {
              fetch(cfg.relay + "/oauth/access_token", {
                method: "POST", headers: { "Content-Type": "application/json" },
                body: JSON.stringify({ device_code: c.device_code }),
              }).then(function (r) { return r.json(); }).then(function (t) {
                if (t.access_token) {
                  finishLogin(t.access_token, status).then(function () {
                    d.querySelector(".dev-note").textContent = "Done.";
                  }).catch(function (e) { status(String(e.message || e)); });
                } else if (t.error === "authorization_pending" || t.error === "slow_down") {
                  if (t.error === "slow_down") every += 5000;
                  poll();
                } else { status("GitHub said: " + (t.error_description || t.error)); dev.disabled = false; }
              }).catch(function () { poll(); });
            }, every);
          })();
        }).catch(function () { status("The relay did not answer."); dev.disabled = false; });
    };
  }

  // Append one ledger line on a fresh branch of the reader's fork and open the pull
  // request. Returns a promise of the pull request's URL.
  function submit(line, handle, progress) {
    if (!auth || !auth.token) return Promise.reject(new Error("not signed in"));
    var owner = cfg.repo.split("/")[0], name = cfg.repo.split("/")[1];
    var me = auth.login, def, path = "graph/events/" + handle.replace(/^@/, "") + ".jsonl";
    progress("Checking your fork…");
    return gh("/repos/" + me + "/" + name).then(function (fork) {
      if (fork) return fork;
      progress("Forking " + cfg.repo + "…");
      return gh("/repos/" + owner + "/" + name + "/forks", { method: "POST", body: {} }).then(function () {
        return new Promise(function (res, rej) {
          var tries = 0;
          (function wait() {
            gh("/repos/" + me + "/" + name).then(function (f) {
              if (f) return res(f);
              if (++tries > 15) return rej(new Error("the fork did not appear"));
              setTimeout(wait, 2000);
            }).catch(rej);
          })();
        });
      });
    }).then(function (fork) {
      def = fork.default_branch;
      progress("Syncing the fork…");
      return gh("/repos/" + me + "/" + name + "/merge-upstream", { method: "POST", body: { branch: def } })
        .catch(function () { /* a fresh fork is already current */ });
    }).then(function () {
      return gh("/repos/" + me + "/" + name + "/git/ref/heads/" + def);
    }).then(function (ref) {
      var branch = "score-" + Date.now();
      progress("Writing the event…");
      return gh("/repos/" + me + "/" + name + "/git/refs", {
        method: "POST", body: { ref: "refs/heads/" + branch, sha: ref.object.sha },
      }).then(function () {
        return gh("/repos/" + me + "/" + name + "/contents/" + path + "?ref=" + def);
      }).then(function (f) {
        var text = f ? unb64(f.content) : "";
        if (text && !/\n$/.test(text)) text += "\n";
        return gh("/repos/" + me + "/" + name + "/contents/" + path, {
          method: "PUT",
          body: Object.assign({
            message: "assessment by " + handle + " via the site\n\nSigned-off-by: " + handle + " <" + me + "@users.noreply.github.com>",
            content: b64(text + line + "\n"),
            branch: branch,
          }, f ? { sha: f.sha } : {}),
        }).then(function () { return branch; });
      });
    }).then(function (branch) {
      progress("Opening the pull request…");
      return gh("/repos/" + owner + "/" + name + "/pulls", {
        method: "POST",
        body: {
          title: "Assessment by " + handle,
          head: me + ":" + branch,
          base: def,
          body: "One `assessment` ledger event, composed on the site and submitted from the author's own account.\n\n```json\n" + line + "\n```",
        },
      });
    }).then(function (pr) { return pr.html_url; });
  }

  window.AWAccount = {
    get: function () { return auth; },
    submit: submit,
  };

  fetch("/assets/account.json").then(function (r) { return r.json(); }).then(function (c) {
    cfg = c; chip();
    document.dispatchEvent(new CustomEvent("aw-account-ready"));
  }).catch(function () { /* the chip stays empty; the copy flow needs none of this */ });
})();
