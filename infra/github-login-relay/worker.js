// The GitHub sign-in relay. The device-flow endpoints on github.com send no CORS
// headers, so the static site cannot call them from the browser; this worker forwards
// exactly those two endpoints and nothing else. It holds no secret — device flow has
// none; the client id is public and pinned here so the relay serves only this site's
// OAuth app. Tokens pass through on their way to the reader's own browser and are
// never stored.

const GITHUB = "https://github.com/login";
const ORIGINS = [
  "https://alignmentworkspace.com",
  "https://www.alignmentworkspace.com",
  "http://localhost:8787",
  "http://localhost:8000",
];

function cors(origin) {
  return {
    "Access-Control-Allow-Origin": ORIGINS.includes(origin) ? origin : ORIGINS[0],
    "Access-Control-Allow-Methods": "POST, OPTIONS",
    "Access-Control-Allow-Headers": "Content-Type, Accept",
  };
}

export default {
  async fetch(request, env) {
    const origin = request.headers.get("Origin") || "";
    if (request.method === "OPTIONS") return new Response(null, { headers: cors(origin) });
    if (request.method !== "POST") return new Response("POST only", { status: 405, headers: cors(origin) });
    const url = new URL(request.url);
    const body = await request.json().catch(() => ({}));
    let upstream, payload;
    if (url.pathname === "/device/code") {
      upstream = GITHUB + "/device/code";
      payload = { client_id: env.CLIENT_ID, scope: "public_repo" };
    } else if (url.pathname === "/oauth/access_token") {
      upstream = GITHUB + "/oauth/access_token";
      payload = {
        client_id: env.CLIENT_ID,
        device_code: String(body.device_code || ""),
        grant_type: "urn:ietf:params:oauth:grant-type:device_code",
      };
    } else {
      return new Response("not an endpoint this relay forwards", { status: 404, headers: cors(origin) });
    }
    const r = await fetch(upstream, {
      method: "POST",
      headers: { "Content-Type": "application/json", Accept: "application/json" },
      body: JSON.stringify(payload),
    });
    return new Response(await r.text(), {
      status: r.status,
      headers: { "Content-Type": "application/json", ...cors(origin) },
    });
  },
};
