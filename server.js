'use strict';

require('dotenv').config();
const http = require('http');
const fs = require('fs');
const path = require('path');
const os = require('os');
const { WebSocketServer } = require('ws');
const chokidar = require('chokidar');

// ─── Config ───────────────────────────────────────────────────────────────────

const PORT = parseInt(process.env.PORT || '3131', 10);
const CLAUDE_PROJECTS_DIR = path.join(os.homedir(), '.claude', 'projects');
const GITHUB_TOKEN = process.env.GITHUB_TOKEN || '';
const GITHUB_ORG = process.env.GITHUB_ORG || '';
const COPILOT_POLL_INTERVAL_MS = 5 * 60 * 1000; // 5 minutes

// Pricing per 1M tokens (USD) — update as Anthropic changes rates
const PRICING = {
  // Claude Fable Family (most capable; above Opus tier)
  'claude-fable-5':             { input: 10.00, output: 50.00, cache_write: 12.50, cache_read: 1.00 },
  'claude-mythos-5':            { input: 10.00, output: 50.00, cache_write: 12.50, cache_read: 1.00 },

  // Claude Opus Family — 4.5/4.6/4.7/4.8 share the standard $5/$25 tier.
  // NOTE: longer keys must precede shorter ones so prefix-matching prefers the specific tier.
  'claude-opus-4-8':            { input: 5.00,  output: 25.00, cache_write: 6.25,  cache_read: 0.50 },
  'claude-opus-4-7':            { input: 5.00,  output: 25.00, cache_write: 6.25,  cache_read: 0.50 },
  'claude-opus-4-6':            { input: 5.00,  output: 25.00, cache_write: 6.25,  cache_read: 0.50 },
  'claude-opus-4-5':            { input: 5.00,  output: 25.00, cache_write: 6.25,  cache_read: 0.50 },
  'claude-opus-4':              { input: 15.00, output: 75.00, cache_write: 18.75, cache_read: 1.50 }, // Pinned legacy Opus 4.0/4.1 pricing

  // Claude Sonnet Family (All standard models are normalized to $3/$15)
  'claude-sonnet-4-5':          { input: 3.00,  output: 15.00, cache_write: 3.75,  cache_read: 0.30 },  
  'claude-sonnet-4-6':          { input: 3.00,  output: 15.00, cache_write: 3.75,  cache_read: 0.30 },
  'claude-sonnet-4':            { input: 3.00,  output: 15.00, cache_write: 3.75,  cache_read: 0.30 }, // Pinned legacy/cloud tier
  'claude-3-7-sonnet-20250219': { input: 3.00,  output: 15.00, cache_write: 3.75,  cache_read: 0.30 }, 
  'claude-3-5-sonnet-20241022': { input: 3.00,  output: 15.00, cache_write: 3.75,  cache_read: 0.30 },
  'claude-3-5-sonnet-20240620': { input: 3.00,  output: 15.00, cache_write: 3.75,  cache_read: 0.30 },

  // Claude Haiku Family
  'claude-haiku-4':             { input: 1.00,  output: 5.00,  cache_write: 1.25,  cache_read: 0.10 }, // Updated to Haiku 4.5/4 standard tier
  'claude-3-5-haiku-20241022':  { input: 0.80,  output: 4.00,  cache_write: 1.00,  cache_read: 0.08 }, // Maintained legacy 3.5 price
  'claude-3-haiku-20240307':    { input: 0.25,  output: 1.25,  cache_write: 0.3125,cache_read: 0.025 }, // Exact 1.25x/0.10x math on base $0.25
};

function getPricing(model) {
  if (!model) return null;
  const lower = model.toLowerCase();
  // Exact match first
  if (PRICING[lower]) return PRICING[lower];
  // Prefix match
  for (const key of Object.keys(PRICING)) {
    if (lower.startsWith(key) || key.startsWith(lower)) return PRICING[key];
  }
  // Fuzzy: find by family (point at current standard tiers, not legacy)
  if (lower.includes('fable') || lower.includes('mythos')) return PRICING['claude-fable-5'];
  if (lower.includes('opus'))   return PRICING['claude-opus-4-8'];
  if (lower.includes('sonnet')) return PRICING['claude-sonnet-4-6'];
  if (lower.includes('haiku'))  return PRICING['claude-haiku-4'];
  return null;
}

function calcCost(usage, model) {
  const p = getPricing(model);
  if (!p) return 0;
  const M = 1_000_000;
  return (
    ((usage.input_tokens || 0) * p.input) / M +
    ((usage.output_tokens || 0) * p.output) / M +
    ((usage.cache_creation_input_tokens || 0) * p.cache_write) / M +
    ((usage.cache_read_input_tokens || 0) * p.cache_read) / M
  );
}

// ─── State ────────────────────────────────────────────────────────────────────

/**
 * claudeTurns: array of turn objects
 * {
 *   source: 'claude',
 *   timestamp: ISO string,
 *   sessionId: string,
 *   projectName: string,
 *   model: string,
 *   input_tokens: number,
 *   output_tokens: number,
 *   cache_creation_input_tokens: number,
 *   cache_read_input_tokens: number,
 *   cost: number
 * }
 */
const claudeTurns = [];

/**
 * copilotDays: array from GitHub API
 * { source: 'copilot', date: 'YYYY-MM-DD', model: string, total_suggestions_count, total_acceptances_count,
 *   total_lines_suggested, total_lines_accepted, total_active_users }
 */
const copilotDays = [];

// Track byte offsets per file to avoid re-parsing old lines
const fileOffsets = new Map(); // filePath → bytes read so far

// Claude Code writes one JSONL line per content block, and every line for a
// turn repeats the same message.id + identical message.usage. Counting each
// line double-counts a turn's tokens. Track seen message ids so each assistant
// message's usage is counted exactly once.
const seenMessageIds = new Set();

// ─── Claude Code Parser ───────────────────────────────────────────────────────

function projectNameFromPath(filePath) {
  // ~/.claude/projects/<projectSlug>/[subagents/]<sessionId>.jsonl
  const parts = filePath.split(path.sep);
  const idx = parts.indexOf('projects');
  if (idx !== -1 && parts[idx + 1]) {
    // Convert slug back to a readable path (leading dashes → slashes)
    const slug = parts[idx + 1];
    return slug.replace(/^-/, '').replace(/-/g, '/') || slug;
  }
  return 'unknown';
}

function parseJSONLFile(filePath) {
  console.log(`[claude] Parsing ${filePath}`);
  const projectName = projectNameFromPath(filePath);
  // For subagent files the UUID is the parent dir; for top-level it's the filename
  const parts = filePath.split(path.sep);
  const subIdx = parts.indexOf('subagents');
  const sessionId = subIdx !== -1
    ? (parts[subIdx - 1] || path.basename(filePath, '.jsonl')) + '/' + path.basename(filePath, '.jsonl')
    : path.basename(filePath, '.jsonl');
  const startOffset = fileOffsets.get(filePath) || 0;

  let fd;
  try {
    fd = fs.openSync(filePath, 'r');
    const stat = fs.fstatSync(fd);
    const fileSize = stat.size;

    if (fileSize <= startOffset) return; // nothing new

    const bufLen = fileSize - startOffset;
    const buf = Buffer.allocUnsafe(bufLen);
    const bytesRead = fs.readSync(fd, buf, 0, bufLen, startOffset);
    fs.closeSync(fd);
    fd = null;

    const chunk = buf.slice(0, bytesRead).toString('utf8');
    const lines = chunk.split('\n');

    let newOffset = startOffset;
    for (const line of lines) {
      const trimmed = line.trim();
      if (!trimmed) continue;
      newOffset += Buffer.byteLength(line, 'utf8') + 1; // +1 for \n

      let obj;
      try { obj = JSON.parse(trimmed); } catch { continue; }

      // We want assistant messages that carry usage
      const usage = obj.usage || (obj.message && obj.message.usage);
      if (!usage) continue;
      if (!usage.input_tokens && !usage.output_tokens) continue;

      // Dedupe: skip content-block lines that repeat an already-counted turn
      const msgId = (obj.message && obj.message.id) || obj.id;
      if (msgId) {
        if (seenMessageIds.has(msgId)) continue;
        seenMessageIds.add(msgId);
      }

      const actualModel = obj.model || (obj.message && obj.message.model) || '';
      const ts = obj.timestamp || obj.ts || new Date().toISOString();

      claudeTurns.push({
        source: 'claude',
        timestamp: ts,
        sessionId,
        projectName,
        model: actualModel,
        input_tokens: usage.input_tokens || 0,
        output_tokens: usage.output_tokens || 0,
        cache_creation_input_tokens: usage.cache_creation_input_tokens || 0,
        cache_read_input_tokens: usage.cache_read_input_tokens || 0,
        cost: calcCost(usage, actualModel),
      });
    }

    fileOffsets.set(filePath, startOffset + bytesRead);
  } catch (err) {
    if (fd != null) try { fs.closeSync(fd); } catch {}
    // File may be locked or missing — skip silently
  }
}

function scanAllClaudeFiles() {
  if (!fs.existsSync(CLAUDE_PROJECTS_DIR)) return;
  const projectDirs = fs.readdirSync(CLAUDE_PROJECTS_DIR, { withFileTypes: true })
    .filter(d => d.isDirectory())
    .map(d => path.join(CLAUDE_PROJECTS_DIR, d.name));

  for (const dir of projectDirs) {
    const files = fs.readdirSync(dir)
      .filter(f => f.endsWith('.jsonl'))
      .map(f => path.join(dir, f));
    for (const f of files) parseJSONLFile(f);
  }
}

// ─── File Watcher ─────────────────────────────────────────────────────────────

function startClaudeWatcher(broadcast) {
  if (!fs.existsSync(CLAUDE_PROJECTS_DIR)) {
    console.log(`[claude] Directory not found: ${CLAUDE_PROJECTS_DIR} — watcher skipped`);
    return;
  }

  const watcher = chokidar.watch(path.join(CLAUDE_PROJECTS_DIR, '**', '*.jsonl'), {
    persistent: true,
    ignoreInitial: true,
    awaitWriteFinish: { stabilityThreshold: 300, pollInterval: 100 },
  });

  watcher.on('add', fp => {
    const before = claudeTurns.length;
    parseJSONLFile(fp);
    broadcast(claudeTurns.slice(before));
  });
  watcher.on('change', fp => {
    const before = claudeTurns.length;
    parseJSONLFile(fp);
    broadcast(claudeTurns.slice(before));
  });
  console.log(`[claude] Watching ${CLAUDE_PROJECTS_DIR}`);
}

// ─── GitHub Copilot API ───────────────────────────────────────────────────────

async function fetchCopilotUsage() {
  if (!GITHUB_TOKEN) return;

  const endpoint = GITHUB_ORG
    ? `https://api.github.com/orgs/${encodeURIComponent(GITHUB_ORG)}/copilot/usage`
    : 'https://api.github.com/copilot/usage';

  try {
    const res = await fetch(endpoint, {
      headers: {
        Authorization: `Bearer ${GITHUB_TOKEN}`,
        Accept: 'application/vnd.github+json',
        'X-GitHub-Api-Version': '2022-11-28',
        'User-Agent': 'claude-viz/1.0',
      },
    });
    if (!res.ok) {
      console.warn(`[copilot] API ${res.status}: ${await res.text()}`);
      return;
    }
    const data = await res.json();
    const days = Array.isArray(data) ? data : (data.breakdown ? [data] : []);
    copilotDays.length = 0;
    for (const day of days) {
      copilotDays.push({
        source: 'copilot',
        date: day.day || day.date || '',
        total_suggestions_count: day.total_suggestions_count || 0,
        total_acceptances_count: day.total_acceptances_count || 0,
        total_lines_suggested: day.total_lines_suggested || 0,
        total_lines_accepted: day.total_lines_accepted || 0,
        total_active_users: day.total_active_users || 0,
        breakdown: day.breakdown || [],
      });
    }
    console.log(`[copilot] Fetched ${copilotDays.length} days`);
  } catch (err) {
    console.warn(`[copilot] Fetch error: ${err.message}`);
  }
}

// ─── Data Aggregation ─────────────────────────────────────────────────────────

function buildSnapshot() {
  // --- Claude aggregations ---

  // Sort turns by timestamp
  const sorted = [...claudeTurns].sort((a, b) => a.timestamp.localeCompare(b.timestamp));

  // Daily totals
  const dailyMap = new Map();
  for (const t of sorted) {
    const day = t.timestamp.slice(0, 10);
    if (!dailyMap.has(day)) {
      dailyMap.set(day, { day, input: 0, output: 0, cache_write: 0, cache_read: 0, cost: 0, turns: 0 });
    }
    const d = dailyMap.get(day);
    d.input += t.input_tokens;
    d.output += t.output_tokens;
    d.cache_write += t.cache_creation_input_tokens;
    d.cache_read += t.cache_read_input_tokens;
    d.cost += t.cost;
    d.turns++;
  }
  const daily = Array.from(dailyMap.values()).sort((a, b) => a.day.localeCompare(b.day));

  // Cumulative cost
  let cum = 0;
  const cumulativeCost = daily.map(d => { cum += d.cost; return { day: d.day, cost: cum }; });

  // Per-session totals
  const sessionMap = new Map();
  for (const t of sorted) {
    if (!sessionMap.has(t.sessionId)) {
      sessionMap.set(t.sessionId, {
        sessionId: t.sessionId,
        projectName: t.projectName,
        firstTs: t.timestamp,
        lastTs: t.timestamp,
        turns: 0,
        input: 0, output: 0, cache_write: 0, cache_read: 0, cost: 0,
        models: new Set(),
      });
    }
    const s = sessionMap.get(t.sessionId);
    s.turns++;
    s.input += t.input_tokens;
    s.output += t.output_tokens;
    s.cache_write += t.cache_creation_input_tokens;
    s.cache_read += t.cache_read_input_tokens;
    s.cost += t.cost;
    if (t.model) s.models.add(t.model);
    if (t.timestamp > s.lastTs) s.lastTs = t.timestamp;
  }
  const sessions = Array.from(sessionMap.values())
    .map(s => ({ ...s, models: Array.from(s.models) }))
    .sort((a, b) => b.lastTs.localeCompare(a.lastTs))
    .slice(0, 100); // cap at 100 most recent

  // Per-model totals
  const modelMap = new Map();
  for (const t of sorted) {
    const m = t.model || 'unknown';
    if (!modelMap.has(m)) modelMap.set(m, { model: m, input: 0, output: 0, cache_write: 0, cache_read: 0, cost: 0 });
    const r = modelMap.get(m);
    r.input += t.input_tokens;
    r.output += t.output_tokens;
    r.cache_write += t.cache_creation_input_tokens;
    r.cache_read += t.cache_read_input_tokens;
    r.cost += t.cost;
  }
  const byModel = Array.from(modelMap.values()).sort((a, b) => b.cost - a.cost);

  // Today's hourly totals (local time) — 24 buckets, hour 0..23
  const now = new Date();
  const pad = n => String(n).padStart(2, '0');
  const localDayKey = d => `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())}`;
  const todayKey = localDayKey(now);
  const todayHourly = Array.from({ length: 24 }, (_, hour) => ({
    hour, input: 0, output: 0, cache_write: 0, cache_read: 0, tokens: 0, cost: 0, turns: 0,
  }));
  let todayTokens = 0, todayCost = 0, todayTurns = 0;
  for (const t of sorted) {
    const d = new Date(t.timestamp);
    if (localDayKey(d) !== todayKey) continue;
    const b = todayHourly[d.getHours()];
    const tk = t.input_tokens + t.output_tokens + t.cache_creation_input_tokens + t.cache_read_input_tokens;
    b.input += t.input_tokens;
    b.output += t.output_tokens;
    b.cache_write += t.cache_creation_input_tokens;
    b.cache_read += t.cache_read_input_tokens;
    b.tokens += tk;
    b.cost += t.cost;
    b.turns++;
    todayTokens += tk;
    todayCost += t.cost;
    todayTurns++;
  }
  const today = { date: todayKey, hourly: todayHourly, tokens: todayTokens, cost: todayCost, turns: todayTurns };

  // Overall totals
  const totals = sorted.reduce((acc, t) => {
    acc.input += t.input_tokens;
    acc.output += t.output_tokens;
    acc.cache_write += t.cache_creation_input_tokens;
    acc.cache_read += t.cache_read_input_tokens;
    acc.cost += t.cost;
    acc.turns++;
    return acc;
  }, { input: 0, output: 0, cache_write: 0, cache_read: 0, cost: 0, turns: 0 });

  return {
    claude: { daily, cumulativeCost, sessions, byModel, totals, today },
    copilot: { days: copilotDays },
    updatedAt: new Date().toISOString(),
  };
}

// ─── HTTP + WebSocket Server ──────────────────────────────────────────────────

const server = http.createServer((req, res) => {
  if (req.method !== 'GET') { res.writeHead(405); res.end(); return; }

  const url = new URL(req.url, `http://localhost:${PORT}`);

  if (url.pathname === '/data') {
    const body = JSON.stringify(buildSnapshot());
    res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
    res.end(body);
    return;
  }

  if (url.pathname === '/' || url.pathname === '/index.html') {
    const fp = path.join(__dirname, 'index.html');
    fs.readFile(fp, (err, data) => {
      if (err) { res.writeHead(404); res.end('Not found'); return; }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
      res.end(data);
    });
    return;
  }

  res.writeHead(404); res.end('Not found');
});

const wss = new WebSocketServer({ server });
const clients = new Set();

wss.on('connection', ws => {
  clients.add(ws);
  // Send full snapshot on connect
  ws.send(JSON.stringify({ type: 'snapshot', data: buildSnapshot() }));
  ws.on('close', () => clients.delete(ws));
  ws.on('error', () => clients.delete(ws));
});

function broadcast(newTurns = []) {
  if (clients.size === 0) return;
  const msg = JSON.stringify({ type: 'update', data: buildSnapshot(), newTurns });
  for (const ws of clients) {
    if (ws.readyState === ws.OPEN) ws.send(msg);
  }
}

// ─── Boot ─────────────────────────────────────────────────────────────────────

console.log('[boot] Scanning existing Claude Code sessions…');
scanAllClaudeFiles();
console.log(`[boot] Loaded ${claudeTurns.length} turns from ${fileOffsets.size} files`);

startClaudeWatcher(broadcast);

if (GITHUB_TOKEN) {
  fetchCopilotUsage().then(broadcast);
  setInterval(() => fetchCopilotUsage().then(broadcast), COPILOT_POLL_INTERVAL_MS);
} else {
  console.log('[copilot] GITHUB_TOKEN not set — Copilot data disabled');
}

server.listen(PORT, '127.0.0.1', () => {
  console.log(`\n✓ Token Visualizer running → http://localhost:${PORT}\n`);
});
