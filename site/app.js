// Replays stream.json on a shared clock, so every viewer sees the same thing.
//
// Position p = (now - epoch) / 1000 * rate, in typing units. The chapters are
// replayed in passes; each pass uses its own shuffled order (perm), and the
// chapter number keeps counting up: number = base + pass * K + index in pass.
// The chapter and species numbers in the text are the placeholders @N (digits)
// and @S (subscript digits), filled in at display time.
//
// The clock functions (mulberry32, perm, locate) must match tools/build_site.py.
(async function () {
  const main = document.getElementById("stream");
  const foot = document.getElementById("foot");
  const leanDialog = document.getElementById("lean-source");
  const leanTitle = document.getElementById("lean-title");
  const leanCode = document.getElementById("lean-code");
  const langBtn = document.getElementById("lang");
  const params = new URLSearchParams(location.search);
  const live = params.has("live");
  document.getElementById("live-status").hidden = !live;
  const bundle = live ? "live.json" : "stream.json";
  async function loadBundle() {
    const response = await fetch(bundle, { cache: "no-store" });
    if (!response.ok) throw new Error(`Could not load ${bundle}`);
    return response.json();
  }
  let data;
  try {
    data = await loadBundle();
  } catch (error) {
    main.textContent = live ? "Waiting for a generated chapter…" : error.message;
    if (live) setTimeout(() => location.reload(), 5000);
    return;
  }

  const TEXT = {
    en: { foot: "Formal proofs in Lean.", src: "Source and proofs" },
    fr: { foot: "Démonstrations formelles en Lean.", src: "Sources et démonstrations" },
  };

  // --- language -------------------------------------------------------------
  const langs = data.langs || ["en"];
  let lang = null;
  try { lang = localStorage.getItem("bourbaki-lang"); } catch (e) {}
  if (!langs.includes(lang)) {
    lang = (navigator.language || "").toLowerCase().startsWith("fr") && langs.includes("fr") ? "fr" : langs[0];
  }

  function applyLangChrome() {
    document.documentElement.lang = lang;
    const t = TEXT[lang] || TEXT.en;
    foot.textContent = t.foot;
    if (data.repo) {
      const link = document.createElement("a");
      link.href = data.repo;
      if (link.protocol === "https:") {
        link.textContent = t.src;
        foot.append(" ", link, ".");
      }
    }
    const other = langs[(langs.indexOf(lang) + 1) % langs.length];
    langBtn.textContent = other.toUpperCase();
    langBtn.setAttribute("aria-label", other === "fr" ? "Lire en français" : "Read in English");
    langBtn.hidden = langs.length < 2;
  }

  langBtn.addEventListener("click", () => {
    lang = langs[(langs.indexOf(lang) + 1) % langs.length];
    try { localStorage.setItem("bourbaki-lang", lang); } catch (e) {}
    applyLangChrome();
    current = null;  // force a full redraw in the new language
    tick();
  });

  // --- shared clock ---------------------------------------------------------
  const chapters = data.chapters.map((ch) => {
    let start = 0;
    const blocks = ch.blocks.map((b) => {
      const bb = { ...b, start, chapterId: ch.id, lean: ch.lean };
      start += b.c;
      return bb;
    });
    return { id: ch.id, blocks, cost: start };
  });
  const K = chapters.length;
  const total = chapters.reduce((s, c) => s + c.cost, 0);

  function mulberry32(a) {
    return function () {
      a |= 0;
      a = (a + 0x6d2b79f5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }
  function rawPerm(pass) {
    const rnd = mulberry32((Math.imul(pass, 0x9e3779b1) + 12345) >>> 0);
    const arr = [...Array(K).keys()];
    for (let i = K - 1; i > 0; i--) {
      const j = Math.floor(rnd() * (i + 1));
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
  }
  const permCache = new Map();
  function perm(pass) {
    if (!permCache.has(pass)) {
      const arr = rawPerm(pass);
      if (pass > 0 && K > 2 && arr[0] === rawPerm(pass - 1)[K - 1]) [arr[0], arr[1]] = [arr[1], arr[0]];
      permCache.set(pass, arr);
    }
    return permCache.get(pass);
  }

  // ?at=N starts this viewer at unit N (for previews and testing).
  const at = params.get("at");
  if (at?.trim() && Number.isSafeInteger(Number(at)) && Number(at) >= 0) {
    data.epoch = Date.now() - (Number(at) / data.rate) * 1000;
  }

  // The chapter being typed at position p: {pass, idx, ch, number, offset}.
  function locate(p) {
    const pass = Math.floor(p / total);
    let q = p - pass * total;
    const order = perm(pass);
    for (let idx = 0; idx < K; idx++) {
      const ch = chapters[order[idx]];
      if (q < ch.cost) return { pass, idx, ch, number: data.base + pass * K + idx, offset: q };
      q -= ch.cost;
    }
  }
  function previous(loc) {
    const pass = loc.idx > 0 ? loc.pass : loc.pass - 1;
    if (pass < 0) return null;
    const idx = loc.idx > 0 ? loc.idx - 1 : K - 1;
    return { pass, idx, ch: chapters[perm(pass)[idx]], number: data.base + pass * K + idx };
  }

  // --- rendering --------------------------------------------------------------
  const esc = (s) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
  const SUB = "₀₁₂₃₄₅₆₇₈₉";
  const fill = (s, n) => s.replace(/@N/g, String(n)).replace(/@S/g, String(n).replace(/\d/g, (d) => SUB[d]));
  const mathCache = new Map();
  function tex(src, display) {
    const key = (display ? "D" : "I") + src;
    if (!mathCache.has(key)) {
      let html;
      try {
        html = katex.renderToString(src, { displayMode: display, throwOnError: false });
      } catch (e) {
        html = esc(src);
      }
      if (mathCache.size > 2000) mathCache.clear();
      mathCache.set(key, html);
    }
    return mathCache.get(key);
  }

  // HTML for block b of chapter number n, typed up to `elapsed` units.
  function blockHTML(b, n, elapsed) {
    const units = b.u[lang] || b.u[langs[0]];
    const own = units.reduce((s, u) => s + u.c, 0);
    let left = elapsed === Infinity ? Infinity : Math.floor((elapsed / b.c) * own);
    let html = "";
    for (const u of units) {
      if (left <= 0) break;
      if (u.t === "text") {
        const s = esc(fill(u.s, n)).slice(0, Math.max(0, left));
        html += u.it ? "<em>" + s + "</em>" : s;
      } else if (left >= u.c) {
        if (u.t === "math") html += tex(fill(u.tex, n), false);
        else if (u.t === "display") html += '<span class="display">' + tex(fill(u.tex, n), true) + "</span>";
        else if (u.t === "lean" && Number.isInteger(b.lean?.lines[u.name])) {
          const name = esc(u.name);
          html += `<button type="button" class="lean-link" data-chapter="${esc(b.chapterId)}" data-declaration="${name}" aria-label="Lean: ${name}" title="${name}">L∃∀N</button>`;
        }
      }
      left -= u.c;
    }
    return html;
  }

  main.addEventListener("click", (event) => {
    const button = event.target.closest("button[data-declaration]");
    if (!button) return;
    const { chapter, declaration } = button.dataset;
    const source = data.chapters.find((item) => item.id === chapter)?.lean;
    const line = source?.lines[declaration];
    if (!Number.isInteger(line)) return;

    const lines = source.source.split("\n");
    const selected = document.createElement("mark");
    selected.textContent = lines[line - 1];
    leanTitle.textContent = `theories/${chapter}.lean:${line} · ${declaration}`;
    leanCode.replaceChildren(lines.slice(0, line - 1).join("\n") + "\n",
      selected, "\n" + lines.slice(line).join("\n"));
    leanDialog.showModal();
    selected.scrollIntoView({ block: "center" });
  });

  function addBlockEl(b) {
    const el = document.createElement(b.k === "p" ? "p" : b.k);
    main.appendChild(el);
    return el;
  }
  function addSep() {
    const sep = document.createElement("div");
    sep.className = "sep";
    sep.textContent = "* * *";
    main.appendChild(sep);
  }
  function renderWhole(loc) {
    for (const b of loc.ch.blocks) addBlockEl(b).innerHTML = blockHTML(b, loc.number, Infinity);
  }

  let current = null;   // {pass, idx, ch, number}
  let shown = [];       // elements of the current chapter's blocks
  let lastPos = -1;
  const cursor = '<span class="cursor"></span>';

  function nearBottom() {
    return window.innerHeight + window.scrollY >= document.body.scrollHeight - 200;
  }

  function startChapter(loc, fresh) {
    if (fresh) {
      main.innerHTML = "";
      const prev = previous(loc);
      if (prev) {
        renderWhole(prev);
        addSep();
      }
    } else {
      // Complete the chapter just finished, keep only it above the new one.
      const b = current.ch.blocks;
      shown.forEach((el, i) => (el.innerHTML = blockHTML(b[i], current.number, Infinity)));
      for (let i = shown.length; i < b.length; i++) addBlockEl(b[i]).innerHTML = blockHTML(b[i], current.number, Infinity);
      const keep = main.querySelectorAll(".sep");
      if (keep.length) {
        const last = keep[keep.length - 1];
        while (main.firstChild !== last) main.removeChild(main.firstChild);
        main.removeChild(last);
      }
      addSep();
    }
    current = loc;
    shown = [];
  }

  function tick() {
    const pos = Math.max(0, Math.floor(((Date.now() - data.epoch) / 1000) * data.rate));
    const p = live ? Math.min(pos, total - 1) : pos;
    if ((live ? Math.min(pos, total) : p) === lastPos && current) return;
    const stick = nearBottom() || !current;
    const loc = locate(p);
    if (!current || loc.number !== current.number) {
      const consecutive = current && loc.number === current.number + 1 && p > lastPos;
      startChapter(loc, !consecutive);
    }
    lastPos = live ? Math.min(pos, total) : p;
    const blocks = current.ch.blocks;
    let cur = 0;
    while (cur + 1 < blocks.length && blocks[cur + 1].start <= loc.offset) cur++;
    for (let i = 0; i <= cur; i++) {
      if (i >= shown.length) shown.push(addBlockEl(blocks[i]));
      if (i < cur) {
        if (!shown[i].dataset.done) {
          shown[i].innerHTML = blockHTML(blocks[i], current.number, Infinity);
          shown[i].dataset.done = "1";
        }
      }
    }
    const b = blocks[cur];
    shown[cur].innerHTML = blockHTML(b, current.number, live && pos >= total ? Infinity : loc.offset - b.start) + (live && pos >= total ? "" : cursor);
    if (stick) window.scrollTo(0, document.body.scrollHeight);
  }

  applyLangChrome();
  tick();
  setInterval(tick, 60);
  if (live) {
    async function watch() {
      try {
        const latest = await loadBundle();
        if (latest.epoch !== data.epoch) {
          location.reload();
          return;
        }
      } catch {
        // Keep the current chapter visible during a transient fetch failure.
      }
      setTimeout(watch, 5000);
    }
    setTimeout(watch, 5000);
  }
})();
