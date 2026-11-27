// A fast drop-in for makefun-diff 1.0.0 (make.fun's own line diff), written from its rule as stated in the
// house baseline's index.js header: the same patch, byte for byte, for less CPU.
//
// How it works, in brief. Lines are cut after every "\n" (a "\r" stays part of its line; a last line with no
// "\n" is a line too) and interned once per case to small integer ids (id = base id shifted by one bit plus a
// newline-presence bit), so the hot loops compare integers, never strings. The common line prefix, then the
// common suffix of what is left, are trimmed. Between them runs Myers's greedy search: for each edit count d
// and each diagonal k it keeps, in a flat Int32Array per d, the furthest point into the old text a path of d
// edits reaches, taking the deletion when a deletion and an insertion reach the same point, never moving past
// either text's end, pruning no edge diagonal, and following every run of equal lines as far as it goes; the
// first path to reach both ends is the script. The V rows are kept so the script is recovered by walking the
// same choices backwards, with no per-cell object ever allocated. The patch is then formatted in one pass,
// hunks holding every change run with up to 3 kept lines before and after it, two runs at most 6 kept lines
// apart sharing a hunk, deletions listed before insertions in each run, a line with no trailing newline
// written with one and followed by a line "%". No network, no caching between cases, deterministic.

const KEEP = 0;
const DEL = 1;
const INS = 2;

/** makefun-diff 1.0.0's answer for one case's input: its patch of { old, new }, as one JSON string. */
export function run(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }
  const oldText = input.old;
  const newText = input.new;

  // Lines, cut after every "\n". parts[i] is a line without its "\n"; a line has its "\n" unless it is the
  // last part of its text and that part is not the empty tail of a text ending in "\n".
  const op = oldText.split('\n');
  const np = newText.split('\n');
  const oLast = op.length - 1;
  const nLast = np.length - 1;
  const n = op.length - (op[oLast] === '' ? 1 : 0);
  const m = np.length - (np[nLast] === '' ? 1 : 0);

  // The common prefix, then the common suffix of what is left, compared on the line parts: two lines are
  // equal exactly when their parts are equal and their newline presence agrees (a line has its "\n" unless
  // it is its text's last part). Trimming first means only the lines between them are ever interned, so a
  // near-identical pair costs almost nothing.
  let prefix = 0;
  while (prefix < n && prefix < m && op[prefix] === np[prefix] && (prefix < oLast) === (prefix < nLast)) prefix++;
  let suffix = 0;
  while (
    suffix < n - prefix && suffix < m - prefix &&
    op[n - 1 - suffix] === np[m - 1 - suffix] &&
    (n - 1 - suffix < oLast) === (m - 1 - suffix < nLast)
  ) suffix++;
  const Np = n - prefix - suffix;
  const Mp = m - prefix - suffix;

  // Intern each distinct line part of the middle once per case; a line's id carries its newline presence
  // in the low bit, so two lines share an id exactly when they are the same code units, newline or its
  // absence included, and the hot loops compare integers, never strings.
  const ids = new Map();
  const a = new Int32Array(Np);
  const b = new Int32Array(Mp);
  let next = 0;
  for (let i = 0; i < Np; i++) {
    const s = op[prefix + i];
    let id = ids.get(s);
    if (id === undefined) {
      id = next++;
      ids.set(s, id);
    }
    a[i] = (id << 1) | (prefix + i < oLast ? 1 : 0);
  }
  for (let j = 0; j < Mp; j++) {
    const s = np[prefix + j];
    let id = ids.get(s);
    if (id === undefined) {
      id = next++;
      ids.set(s, id);
    }
    b[j] = (id << 1) | (prefix + j < nLast ? 1 : 0);
  }

  // Myers's greedy search. Vs[d] is an Int32Array of d + 1 entries: Vs[d][j] is one more than the furthest
  // old-lines consumed on diagonal k = 2j - d by a path of d edits, after following equal lines as far as
  // they go, or 0 when no path reaches that diagonal (so a fresh zero-filled row needs no sentinel pass).
  // Row d - 1 is all the choice at row d ever reads, and a cell's deletion parent is the previous cell's
  // insertion parent, so one carried value serves both reads.
  const Vs = [];
  let x = 0;
  {
    const lim = Np < Mp ? Np : Mp;
    while (x < lim && a[x] === b[x]) x++;
  }
  const v0 = new Int32Array(1);
  v0[0] = x + 1;
  Vs.push(v0);
  let D = -1;
  let KD = 0;
  let jD = 0;
  if (x >= Np && x >= Mp) {
    D = 0;
  } else {
    outer: for (let d = 1; d <= Np + Mp; d++) {
      const prev = Vs[d - 1];
      const cur = new Int32Array(d + 1);
      Vs.push(cur);
      let carry = 0; // prev[j - 1], the deletion parent's stored reach; 0 is no path (j = 0 has none)
      for (let j = 0; j < d; j++) {
        const k = 2 * j - d;
        const sDel = carry; // stored xDel + 1, the deletion's parent
        const sIns = prev[j]; // stored xIns + 1, the insertion's parent
        carry = sIns;
        // A move past the end of either text is no candidate: the deletion needs sDel - 1 < Np, the
        // insertion needs its new-lines consumed, sIns - 1 - (k + 1), to stay below Mp.
        const canDel = sDel !== 0 && sDel <= Np;
        const canIns = sIns !== 0 && sIns - k - 2 < Mp;
        if (!canDel && !canIns) continue;
        // The candidate further into the old text, and the deletion when both reach the same point: the
        // deletion reaches sDel old lines, the insertion sIns - 1.
        let xx;
        if (canDel && (!canIns || sDel >= sIns - 1)) xx = sDel;
        else xx = sIns - 1;
        const lim = Mp + k < Np ? Mp + k : Np;
        while (xx < lim && a[xx] === b[xx - k]) xx++;
        cur[j] = xx + 1;
        if (xx >= Np && xx - k >= Mp) {
          D = d;
          KD = k;
          jD = j;
          break outer;
        }
      }
      // j = d (k = d): no insertion parent, the deletion's parent is the carried prev[d - 1].
      {
        const k = d;
        const sDel = carry;
        const canDel = sDel !== 0 && sDel <= Np;
        if (canDel) {
          let xx = sDel;
          const lim = Mp + k < Np ? Mp + k : Np;
          while (xx < lim && a[xx] === b[xx - k]) xx++;
          cur[d] = xx + 1;
          if (xx >= Np && xx - k >= Mp) {
            D = d;
            KD = k;
            jD = d;
            break outer;
          }
        }
      }
    }
  }
  if (D < 0) throw new Error('makefun-diff: the search ended without reaching both ends');

  // Walk the same choices backwards from (D, KD) to recover the edit script, as runs built in reverse:
  // each step contributes its run of equal lines, then the one edit that led into it.
  const rk = [];
  const rc = [];
  {
    let k = KD;
    let j = jD;
    for (let d = D; d >= 1; d--) {
      const row = Vs[d - 1];
      const sDel = j >= 1 ? row[j - 1] : 0;
      const sIns = j <= d - 1 ? row[j] : 0;
      const canDel = sDel !== 0 && sDel <= Np;
      const canIns = sIns !== 0 && sIns - k - 2 < Mp;
      let xEdit;
      let isDel;
      if (canDel && (!canIns || sDel >= sIns - 1)) {
        isDel = true;
        xEdit = sDel;
      } else if (canIns) {
        isDel = false;
        xEdit = sIns - 1;
      } else {
        throw new Error('makefun-diff: backtrack lost the path');
      }
      const snake = Vs[d][j] - 1 - xEdit;
      if (snake > 0) {
        rk.push(KEEP);
        rc.push(snake);
      }
      rk.push(isDel ? DEL : INS);
      rc.push(1);
      if (isDel) {
        k -= 1;
        j -= 1;
      } else {
        k += 1;
      }
    }
    const x0 = Vs[0][0] - 1;
    if (x0 > 0) {
      rk.push(KEEP);
      rc.push(x0);
    }
  }

  // The runs in order, the common prefix and suffix folded in as kept runs, adjacent runs of one kind merged.
  const fk = [];
  const fc = [];
  const pushRun = (kind, count) => {
    if (count <= 0) return;
    const last = fk.length - 1;
    if (last >= 0 && fk[last] === kind) fc[last] += count;
    else {
      fk.push(kind);
      fc.push(count);
    }
  };
  pushRun(KEEP, prefix);
  for (let i = rk.length - 1; i >= 0; i--) pushRun(rk[i], rc[i]);
  pushRun(KEEP, suffix);

  // The change runs: each a stretch of deletions and insertions between two kept lines, at old line o and new p.
  const changes = [];
  let o = 0;
  let p = 0;
  let deleted = 0;
  let inserted = 0;
  for (let i = 0; i < fk.length; i++) {
    const kind = fk[i];
    const count = fc[i];
    if (kind === KEEP) {
      o += count;
      p += count;
      continue;
    }
    let c = changes.length !== 0 ? changes[changes.length - 1] : undefined;
    if (c === undefined || c.o + c.dels !== o || c.p + c.ins !== p) {
      c = { o, p, dels: 0, ins: 0 };
      changes.push(c);
    }
    if (kind === DEL) {
      c.dels += count;
      o += count;
      deleted += count;
    } else {
      c.ins += count;
      p += count;
      inserted += count;
    }
  }

  // The hunks: change runs at most 6 kept lines apart share one.
  const hunks = [];
  for (const c of changes) {
    const h = hunks.length !== 0 ? hunks[hunks.length - 1] : undefined;
    const prev = h !== undefined ? h[h.length - 1] : undefined;
    if (prev !== undefined && c.o - (prev.o + prev.dels) <= 6) h.push(c);
    else hunks.push([c]);
  }

  // The patch, built as pieces and joined once.
  const out = [`makefun-diff/1 old=${n} new=${m} hunks=${hunks.length} deleted=${deleted} inserted=${inserted}\n`];
  for (const h of hunks) {
    const first = h[0];
    const last = h[h.length - 1];
    const oldStart = first.o - 3 > 0 ? first.o - 3 : 0;
    const newStart = first.p - (first.o - oldStart);
    const after = n - (last.o + last.dels) < 3 ? n - (last.o + last.dels) : 3;
    const oldEnd = last.o + last.dels + after;
    const newEnd = last.p + last.ins + after;
    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);
    let at = oldStart;
    for (const c of h) {
      for (; at < c.o; at++) {
        out.push('=', op[at], at < oLast ? '\n' : '\n%\n');
      }
      for (let i = 0; i < c.dels; i++) {
        const idx = c.o + i;
        out.push('-', op[idx], idx < oLast ? '\n' : '\n%\n');
      }
      for (let i = 0; i < c.ins; i++) {
        const idx = c.p + i;
        out.push('+', np[idx], idx < nLast ? '\n' : '\n%\n');
      }
      at = c.o + c.dels;
    }
    for (; at < oldEnd; at++) {
      out.push('=', op[at], at < oLast ? '\n' : '\n%\n');
    }
  }
  return out.join('');
}
