/* Venn Engine: Interactive Set & Venn Diagram Engine
 * Sets A, B, C live in a universe U. Every element falls in one of 8 regions
 * (a 3-bit mask: bit0 = in A, bit1 = in B, bit2 = in C). An expression is
 * parsed once, then evaluated per region. That gives both the highlighted
 * area and the resulting set, and it makes identity checking exact.
 */
(function () {
  "use strict";

  const $ = (s, r = document) => r.querySelector(s);
  const NS = "http://www.w3.org/2000/svg";

  const NAMES = ["A", "B", "C"];
  const COLORS = ["#22d3ee", "#ff4d8d", "#fbbf24"];
  const CIRCLES = [
    { cx: 250, cy: 230, r: 135 },
    { cx: 390, cy: 230, r: 135 },
    { cx: 320, cy: 350, r: 135 },
  ];
  const BOX = { x: 20, y: 20, w: 600, h: 480 };
  const VIEW = { w: 640, h: 520 };
  // Items shown inside each region of the diagram, by mask
  const CAPACITY = [6, 9, 9, 6, 9, 6, 6, 4];
  const PER_ROW = [2, 3, 3, 2, 3, 2, 2, 2];

  const EXAMPLE = {
    A: "1, 2, 3, 4, 5",
    B: "4, 5, 6, 7",
    C: "5, 7, 8, 9",
    extras: "10, 11",
  };

  const EXPR_EXAMPLES = [
    "A ∪ B",
    "A ∩ B",
    "A − B",
    "A Δ B",
    "A′",
    "(A ∪ B) ∩ C′",
    "A ∩ B ∩ C",
    "A ∪ B ∪ C",
  ];
  const ID_EXAMPLES = [
    { name: "De Morgan", l: "(A ∪ B)′", r: "A′ ∩ B′" },
    { name: "Distributive", l: "A ∩ (B ∪ C)", r: "(A ∩ B) ∪ (A ∩ C)" },
    { name: "Absorption", l: "A ∪ (A ∩ B)", r: "A" },
    { name: "Difference", l: "A − B", r: "A ∩ B′" },
    { name: "Idempotent", l: "A ∪ A", r: "A" },
    { name: "Symmetric diff", l: "A Δ B", r: "(A ∪ B) − (A ∩ B)" },
    { name: "Not an identity", l: "A − B", r: "B − A" },
  ];

  /* ---------- helpers ---------- */

  function esc(s) {
    return String(s).replace(
      /[&<>"']/g,
      (ch) =>
        ({
          "&": "&amp;",
          "<": "&lt;",
          ">": "&gt;",
          '"': "&quot;",
          "'": "&#39;",
        })[ch],
    );
  }

  function parseList(str) {
    const parts = str
      .split(/[\s,;{}]+/)
      .map((s) => s.trim())
      .filter(Boolean);
    return [...new Set(parts)];
  }

  function sortEls(arr) {
    return arr.slice().sort((a, b) => {
      const na = Number(a),
        nb = Number(b);
      if (!isNaN(na) && !isNaN(nb)) return na - nb;
      return a.localeCompare(b);
    });
  }

  function fmtSet(arr) {
    return arr.length ? "{" + arr.map(esc).join(", ") + "}" : "∅";
  }

  function popcount(m) {
    return (m & 1) + ((m >> 1) & 1) + ((m >> 2) & 1);
  }

  function regionName(m) {
    const ins = NAMES.filter((_, i) => (m >> i) & 1);
    if (m === 0) return "Outside all sets";
    if (ins.length === 1) return "Only " + ins[0];
    if (ins.length === 3) return "A, B and C";
    return ins.join(" and ") + " only";
  }

  /* ---------- expression parser ---------- */

  const SYMBOLS = {
    "∪": "OR",
    "|": "OR",
    "+": "OR",
    "∩": "AND",
    "&": "AND",
    "*": "AND",
    "−": "DIFF",
    "–": "DIFF",
    "-": "DIFF",
    "\\": "DIFF",
    Δ: "XOR",
    "△": "XOR",
    "^": "XOR",
    "(": "LP",
    ")": "RP",
    "'": "POST",
    "′": "POST",
    ᶜ: "POST",
    "!": "NOT",
    "~": "NOT",
    "¬": "NOT",
    "∅": "EMPTY",
  };
  const WORDS = {
    UNION: "OR",
    INTERSECTION: "AND",
    INTERSECT: "AND",
    MINUS: "DIFF",
    XOR: "XOR",
    NOT: "NOT",
    COMP: "NOT",
    EMPTY: "EMPTY",
  };

  function tokenize(src) {
    const out = [];
    let i = 0;
    while (i < src.length) {
      const ch = src[i];
      if (/\s/.test(ch)) {
        i++;
        continue;
      }
      if (/[A-Za-z]/.test(ch)) {
        let j = i;
        while (j < src.length && /[A-Za-z]/.test(src[j])) j++;
        const word = src.slice(i, j).toUpperCase();
        if (["A", "B", "C"].includes(word))
          out.push({ t: "SET", v: NAMES.indexOf(word) });
        else if (word === "U") out.push({ t: "UNIV" });
        else if (WORDS[word]) out.push({ t: WORDS[word] });
        else
          throw new Error(
            'Unknown name "' +
              src.slice(i, j) +
              '". Use A, B, C or U, and put ∪, ∩, −, Δ between them.',
          );
        i = j;
        continue;
      }
      if (SYMBOLS[ch]) {
        out.push({ t: SYMBOLS[ch] });
        i++;
        continue;
      }
      throw new Error('Unexpected character "' + ch + '".');
    }
    return out;
  }

  function parse(src) {
    if (!src.trim()) throw new Error("Type an expression, for example A ∪ B.");
    const toks = tokenize(src);
    let p = 0;
    const peek = () => (p < toks.length ? toks[p].t : null);

    function expr() {
      let left = term();
      while (["OR", "DIFF", "XOR"].includes(peek())) {
        const op = toks[p++].t;
        left = { k: "bin", op, l: left, r: term() };
      }
      return left;
    }
    function term() {
      let left = factor();
      while (peek() === "AND") {
        p++;
        left = { k: "bin", op: "AND", l: left, r: factor() };
      }
      return left;
    }
    function factor() {
      if (peek() === "NOT") {
        p++;
        return { k: "not", a: factor() };
      }
      let node = atom();
      while (peek() === "POST") {
        p++;
        node = { k: "not", a: node };
      }
      return node;
    }
    function atom() {
      const t = toks[p];
      if (!t)
        throw new Error(
          "The expression ends too early. Add a set after the last operator.",
        );
      if (t.t === "SET") {
        p++;
        return { k: "set", i: t.v };
      }
      if (t.t === "UNIV") {
        p++;
        return { k: "univ" };
      }
      if (t.t === "EMPTY") {
        p++;
        return { k: "empty" };
      }
      if (t.t === "LP") {
        p++;
        const inner = expr();
        if (peek() !== "RP") throw new Error("Missing closing bracket ).");
        p++;
        return inner;
      }
      if (t.t === "RP") throw new Error("Extra closing bracket ).");
      throw new Error(
        "Expected a set (A, B, C, U or ∅) but found an operator.",
      );
    }

    const tree = expr();
    if (p < toks.length) {
      throw new Error(
        toks[p].t === "RP"
          ? "Extra closing bracket )."
          : "Two sets in a row. Put an operator between them.",
      );
    }
    return tree;
  }

  // Truth value of the expression for a region mask
  function ev(n, m) {
    switch (n.k) {
      case "set":
        return (m >> n.i) & 1;
      case "univ":
        return 1;
      case "empty":
        return 0;
      case "not":
        return ev(n.a, m) ? 0 : 1;
      case "bin": {
        const l = ev(n.l, m),
          r = ev(n.r, m);
        if (n.op === "OR") return l | r;
        if (n.op === "AND") return l & r;
        if (n.op === "DIFF") return l & (r ? 0 : 1);
        return l ^ r;
      }
    }
    return 0;
  }

  /* ---------- state from the inputs ---------- */

  function readSets() {
    const lists = NAMES.map((n) => parseList($("#set" + n).value));
    const extras = parseList($("#extras").value);
    const universe = sortEls([...new Set([...lists.flat(), ...extras])]);
    const lookups = lists.map((l) => new Set(l));
    const byMask = Array.from({ length: 8 }, () => []);
    universe.forEach((e) => {
      let m = 0;
      lookups.forEach((s, i) => {
        if (s.has(e)) m |= 1 << i;
      });
      byMask[m].push(e);
    });
    const sets = lists.map((l) => sortEls(l));
    return { sets, universe, byMask };
  }

  const elementsOf = (data, masks) =>
    sortEls(masks.flatMap((m) => data.byMask[m]));
  const selectedMasks = (ast) =>
    [0, 1, 2, 3, 4, 5, 6, 7].filter((m) => ev(ast, m));

  /* ---------- diagram (built once, updated on input) ---------- */

  const svg = $("#venn");
  const regionG = [];
  const regionTitle = [];
  const regionText = [];
  const setCountText = [];
  let anchors = [];
  let universeLabel;

  function el(tag, attrs, parent) {
    const e = document.createElementNS(NS, tag);
    for (const k in attrs) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }

  function computeAnchors() {
    const sums = Array.from({ length: 8 }, () => ({ x: 0, y: 0, n: 0 }));
    for (let x = BOX.x; x < BOX.x + BOX.w; x += 4) {
      for (let y = BOX.y; y < BOX.y + BOX.h; y += 4) {
        let m = 0;
        CIRCLES.forEach((c, i) => {
          if ((x - c.cx) ** 2 + (y - c.cy) ** 2 <= c.r * c.r) m |= 1 << i;
        });
        const s = sums[m];
        s.x += x;
        s.y += y;
        s.n++;
      }
    }
    const a = sums.map((s) => ({ x: s.x / s.n, y: s.y / s.n }));
    a[0] = { x: 535, y: 440 }; // outside region: bottom-right corner
    return a;
  }

  function buildDiagram() {
    svg.setAttribute("viewBox", "0 0 " + VIEW.w + " " + VIEW.h);
    anchors = computeAnchors();

    const defs = el("defs", {}, svg);
    CIRCLES.forEach((c, i) => {
      const cp = el("clipPath", { id: "clip" + i }, defs);
      el("circle", { cx: c.cx, cy: c.cy, r: c.r }, cp);
    });
    for (let m = 0; m < 8; m++) {
      const mk = el(
        "mask",
        {
          id: "mask" + m,
          maskUnits: "userSpaceOnUse",
          x: 0,
          y: 0,
          width: VIEW.w,
          height: VIEW.h,
        },
        defs,
      );
      el(
        "rect",
        { x: 0, y: 0, width: VIEW.w, height: VIEW.h, fill: "#fff" },
        mk,
      );
      CIRCLES.forEach((c, i) => {
        if (!((m >> i) & 1))
          el("circle", { cx: c.cx, cy: c.cy, r: c.r, fill: "#000" }, mk);
      });
    }

    el(
      "rect",
      {
        class: "universe",
        x: BOX.x,
        y: BOX.y,
        width: BOX.w,
        height: BOX.h,
        rx: 14,
      },
      svg,
    );
    CIRCLES.forEach((c, i) => {
      el(
        "circle",
        { class: "tint-" + NAMES[i].toLowerCase(), cx: c.cx, cy: c.cy, r: c.r },
        svg,
      );
    });

    // One clickable-looking region per mask: an exact intersection/exclusion of circles
    for (let m = 0; m < 8; m++) {
      const g = el(
        "g",
        { class: "region", "data-mask": m, mask: "url(#mask" + m + ")" },
        svg,
      );
      regionTitle[m] = el("title", {}, g);
      let parent = g;
      CIRCLES.forEach((c, i) => {
        if ((m >> i) & 1)
          parent = el("g", { "clip-path": "url(#clip" + i + ")" }, parent);
      });
      el("rect", { x: BOX.x, y: BOX.y, width: BOX.w, height: BOX.h }, parent);
      regionG[m] = g;
      g.setAttribute("tabindex", "0");
      g.addEventListener("click", () => toggleRegion(m));
      g.addEventListener("keydown", (e) => {
        if (e.key === "Enter" || e.key === " ") {
          e.preventDefault();
          toggleRegion(m);
        }
      });
    }

    CIRCLES.forEach((c, i) => {
      el(
        "circle",
        { class: "outline", cx: c.cx, cy: c.cy, r: c.r, stroke: COLORS[i] },
        svg,
      );
    });

    for (let m = 0; m < 8; m++) {
      regionText[m] = el(
        "text",
        { class: "els", "text-anchor": "middle" },
        svg,
      );
    }

    const labelPos = [
      { x: 120, y: 92 },
      { x: 520, y: 92 },
      { x: 120, y: 472 },
    ];
    NAMES.forEach((n, i) => {
      const t = el(
        "text",
        {
          class: "set-label",
          x: labelPos[i].x,
          y: labelPos[i].y,
          "text-anchor": "middle",
          fill: COLORS[i],
        },
        svg,
      );
      t.textContent = n;
      setCountText[i] = el(
        "text",
        {
          class: "set-count",
          x: labelPos[i].x,
          y: labelPos[i].y + 18,
          "text-anchor": "middle",
        },
        svg,
      );
    });
    universeLabel = el(
      "text",
      { class: "u-label", x: BOX.x + 14, y: BOX.y + 22 },
      svg,
    );
  }

  function shorten(s) {
    return s.length > 9 ? s.slice(0, 8) + "…" : s;
  }

  function layoutText(m, items) {
    const t = regionText[m];
    t.textContent = "";
    const cap = CAPACITY[m],
      per = PER_ROW[m];
    let shown = items,
      more = 0;
    if (items.length > cap) {
      shown = items.slice(0, cap - 1);
      more = items.length - shown.length;
    }
    const rows = [];
    for (let i = 0; i < shown.length; i += per)
      rows.push(
        shown
          .slice(i, i + per)
          .map(shorten)
          .join(", "),
      );
    if (more) rows.push("+" + more + " more");
    const a = anchors[m],
      lh = 17;
    const y0 = a.y - ((rows.length - 1) * lh) / 2 + 5;
    rows.forEach((r, i) => {
      const ts = document.createElementNS(NS, "tspan");
      ts.setAttribute("x", a.x);
      ts.setAttribute("y", y0 + i * lh);
      const comma = i < rows.length - 1 && !(more && i === rows.length - 2);
      ts.textContent = r + (comma ? "," : "");
      t.appendChild(ts);
    });
  }

  function paintDiagram(data, sel) {
    for (let m = 0; m < 8; m++) {
      const on = sel.includes(m);
      regionG[m].classList.toggle("sel", on);
      regionText[m].classList.toggle("sel", on);
      layoutText(m, data.byMask[m]);
      const n = data.byMask[m].length;
      regionTitle[m].textContent =
        regionName(m) + ": " + n + (n === 1 ? " element" : " elements");
    }
    data.sets.forEach((s, i) => {
      setCountText[i].textContent = "|" + NAMES[i] + "| = " + s.length;
    });
    universeLabel.textContent =
      "U, " +
      data.universe.length +
      (data.universe.length === 1 ? " element" : " elements");
  }

  /* ---------- results panel ---------- */

  function powerSet(arr) {
    let out = [[]];
    arr.forEach((x) => {
      out = out.concat(out.map((s) => s.concat([x])));
    });
    return out;
  }

  const OPS = { OR: "∪", AND: "∩", DIFF: "−", XOR: "Δ" };
  function show(n, inner) {
    switch (n.k) {
      case "set":
        return NAMES[n.i];
      case "univ":
        return "U";
      case "empty":
        return "∅";
      case "not":
        return show(n.a, true) + "′";
      default: {
        const t = show(n.l, true) + " " + OPS[n.op] + " " + show(n.r, true);
        return inner ? "(" + t + ")" : t;
      }
    }
  }
  function collectSteps(n, out, seen) {
    if (n.k === "not") collectSteps(n.a, out, seen);
    if (n.k === "bin") {
      collectSteps(n.l, out, seen);
      collectSteps(n.r, out, seen);
    }
    if (n.k === "not" || n.k === "bin") {
      const txt = show(n, false);
      if (!seen.has(txt)) {
        seen.add(txt);
        out.push({ txt, masks: selectedMasks(n) });
      }
    }
    return out;
  }

  let stepsCache = [];
  function renderResult(data, ast, err) {
    const R = $("#tab-result"),
      S = $("#tab-steps"),
      G = $("#tab-regions");
    $("#tab-analysis").innerHTML = sizesHtml(data);

    const max = Math.max(1, ...data.byMask.map((a) => a.length));
    G.innerHTML =
      '<p class="muted">How many elements sit in each of the 8 regions.</p><ul class="reg">' +
      [0, 1, 2, 3, 4, 5, 6, 7]
        .map(
          (m) =>
            '<li><span class="rn">' +
            esc(regionName(m)) +
            '</span><span class="rc">' +
            data.byMask[m].length +
            '</span><span class="bar"><i style="width:' +
            (data.byMask[m].length / max) * 100 +
            '%"></i></span><span class="re">' +
            fmtSet(data.byMask[m]) +
            "</span></li>",
        )
        .join("") +
      "</ul>";

    if (err) {
      R.innerHTML =
        '<p class="muted">Fix the expression to see the result.</p>';
      S.innerHTML =
        '<p class="muted">Steps appear once the expression is valid.</p>';
      stepsCache = [];
      return;
    }
    const sel = selectedMasks(ast);
    const res = elementsOf(data, sel);
    const n = res.length;

    let html = n
      ? '<div class="rchips">' +
        res.map((e) => '<span class="rchip">' + esc(e) + "</span>").join("") +
        "</div>"
      : '<p class="empty">∅</p>';
    html += '<p class="size">|result| = ' + n + "</p>";
    html +=
      '<p class="muted">Regions selected: ' +
      (sel.length ? sel.map(regionName).join("; ") : "none (the empty set)") +
      ".</p>";
    html +=
      '<div class="row"><button type="button" class="btn ghost" id="copy">Copy result</button></div>';
    html += "<h3>Power set</h3>";
    if (n <= 4)
      html +=
        "<p>2<sup>" +
        n +
        "</sup> = " +
        Math.pow(2, n) +
        " subsets: " +
        powerSet(res).map(fmtSet).join(", ") +
        "</p>";
    else
      html +=
        "<p>2<sup>" +
        n +
        "</sup> = " +
        Math.pow(2, n).toLocaleString() +
        " subsets.</p>";
    R.innerHTML = html;
    R.dataset.text = n ? "{" + res.join(", ") + "}" : "∅";

    stepsCache = collectSteps(ast, [], new Set());
    S.innerHTML = stepsCache.length
      ? '<p class="muted">Evaluated inside-out. Hover or focus a step to preview its region on the diagram.</p><ol class="steps">' +
        stepsCache
          .map(
            (st, i) =>
              '<li tabindex="0" data-i="' +
              i +
              '"><code>' +
              esc(st.txt) +
              "</code><span>" +
              fmtSet(elementsOf(data, st.masks)) +
              "</span></li>",
          )
          .join("") +
        "</ol>"
      : '<p class="muted">Add an operator (∪, ∩, −, Δ or ′) to see the evaluation steps.</p>';
  }

  function sizesHtml(data) {
    const [A, B, C] = data.sets;
    const sa = new Set(A),
      sb = new Set(B),
      sc = new Set(C);
    const inter = (x, y) => x.filter((e) => y.has(e));
    const ab = inter(A, sb).length,
      ac = inter(A, sc).length,
      bc = inter(B, sc).length;
    const abc = data.byMask[7].length;
    const direct = A.length + B.length + C.length - ab - ac - bc + abc;
    const unionSize = new Set([...A, ...B, ...C]).size;

    let html =
      '<h3>Set sizes</h3><div class="sizes">' +
      "<span>|A| = " +
      A.length +
      "</span><span>|B| = " +
      B.length +
      "</span>" +
      "<span>|C| = " +
      C.length +
      "</span><span>|U| = " +
      data.universe.length +
      "</span></div>";

    // Relations between sets
    const rel = [];
    const pairs = [
      [0, 1],
      [0, 2],
      [1, 2],
    ];
    const subset = (x, y) => x.length > 0 && x.every((e) => y.has(e));
    const sets = [A, B, C],
      look = [sa, sb, sc];
    pairs.forEach(([i, j]) => {
      const iSubJ = subset(sets[i], look[j]),
        jSubI = subset(sets[j], look[i]);
      if (iSubJ && jSubI) rel.push(NAMES[i] + " = " + NAMES[j]);
      else if (iSubJ)
        rel.push(NAMES[i] + " ⊂ " + NAMES[j] + " (proper subset)");
      else if (jSubI)
        rel.push(NAMES[j] + " ⊂ " + NAMES[i] + " (proper subset)");
      if (
        sets[i].length &&
        sets[j].length &&
        inter(sets[i], look[j]).length === 0
      ) {
        rel.push(NAMES[i] + " ∩ " + NAMES[j] + " = ∅ (disjoint)");
      }
    });
    html += "<h3>Relations</h3>";
    html += rel.length
      ? "<ul>" + rel.map((r) => "<li>" + esc(r) + "</li>").join("") + "</ul>"
      : '<p class="muted">No subset or disjoint relations between A, B and C.</p>';

    html += "<h3>Inclusion–exclusion</h3>";
    html +=
      '<p class="mathline">|A ∪ B ∪ C| = |A| + |B| + |C| − |A∩B| − |A∩C| − |B∩C| + |A∩B∩C|<br>= ' +
      [A.length, B.length, C.length].join(" + ") +
      " − " +
      ab +
      " − " +
      ac +
      " − " +
      bc +
      " + " +
      abc +
      " = <strong>" +
      direct +
      "</strong>" +
      (direct === unionSize ? ", which matches the count of A ∪ B ∪ C." : ".") +
      "</p>";
    return html;
  }

  /* ---------- identity checker ---------- */

  function renderIdentity(data) {
    const out = $("#identity-out");
    let l, r;
    try {
      l = parse($("#lhs").value);
      r = parse($("#rhs").value);
    } catch (e) {
      out.innerHTML = '<p class="error">' + esc(e.message) + "</p>";
      return;
    }
    const masks = [0, 1, 2, 3, 4, 5, 6, 7];
    const lv = masks.map((m) => ev(l, m)),
      rv = masks.map((m) => ev(r, m));
    const bad = masks.filter((m) => lv[m] !== rv[m]);

    let html;
    if (!bad.length) {
      html =
        '<p class="verdict ok">Identity holds. Both sides select exactly the same regions, so they are equal for any sets.</p>';
    } else {
      html =
        '<p class="verdict bad">Not an identity. The sides differ in: ' +
        bad.map(regionName).map(esc).join("; ") +
        ".</p>";
    }

    const lres = elementsOf(
      data,
      masks.filter((m) => lv[m]),
    );
    const rres = elementsOf(
      data,
      masks.filter((m) => rv[m]),
    );
    html +=
      '<p class="muted">With your current sets: left = ' +
      fmtSet(lres) +
      ", right = " +
      fmtSet(rres) +
      ".</p>";

    html +=
      '<div class="table-wrap"><table class="truth"><thead><tr><th>Region</th><th>A</th><th>B</th><th>C</th><th>Left</th><th>Right</th></tr></thead><tbody>';
    masks.forEach((m) => {
      html +=
        "<tr" +
        (lv[m] !== rv[m] ? ' class="diff"' : "") +
        "><td>" +
        esc(regionName(m)) +
        "</td>" +
        [0, 1, 2].map((i) => "<td>" + ((m >> i) & 1) + "</td>").join("") +
        '<td class="' +
        (lv[m] ? "one" : "") +
        '">' +
        lv[m] +
        "</td>" +
        '<td class="' +
        (rv[m] ? "one" : "") +
        '">' +
        rv[m] +
        "</td></tr>";
    });
    html += "</tbody></table></div>";
    out.innerHTML = html;
  }

  /* ---------- main update ---------- */

  function update() {
    const data = readSets();
    let ast = null,
      err = "";
    try {
      ast = parse($("#expr").value);
    } catch (e) {
      err = e.message;
    }
    $("#expr-error").textContent = err;
    $("#expr").setAttribute("aria-invalid", err ? "true" : "false");

    const sel = ast ? selectedMasks(ast) : [];
    cur = { data, sel };
    paintDiagram(data, sel);
    renderChips(data);
    renderResult(data, ast, err);
    save();
    renderIdentity(data);
    syncChips();
  }

  /* ---------- controls ---------- */

  function insertAtCursor(input, text) {
    const s =
      input.selectionStart == null ? input.value.length : input.selectionStart;
    const e = input.selectionEnd == null ? s : input.selectionEnd;
    input.value = input.value.slice(0, s) + text + input.value.slice(e);
    const pos = s + text.length;
    input.focus();
    input.setSelectionRange(pos, pos);
    input.dispatchEvent(new Event("input", { bubbles: true }));
  }

  function makeKeys(container, getTarget) {
    const keys = [
      ["A", "Set A", "name"],
      ["B", "Set B", "name"],
      ["C", "Set C", "name"],
      ["U", "Universe U", "name"],
      ["∅", "Empty set"],
      null,
      ["∪", "Union"],
      ["∩", "Intersection"],
      ["−", "Difference"],
      ["Δ", "Symmetric difference"],
      ["′", "Complement"],
      null,
      ["(", "Open bracket"],
      [")", "Close bracket"],
    ];
    keys.forEach((k) => {
      if (!k) {
        const g = document.createElement("span");
        g.className = "gap";
        container.appendChild(g);
        return;
      }
      const b = document.createElement("button");
      b.type = "button";
      b.textContent = k[0];
      b.title = k[1];
      b.setAttribute("aria-label", k[1]);
      if (k[2]) b.className = k[2];
      b.addEventListener("click", () => insertAtCursor(getTarget(), k[0]));
      container.appendChild(b);
    });
  }

  let lastIdInput = $("#lhs");
  $("#lhs").addEventListener("focus", () => {
    lastIdInput = $("#lhs");
  });
  $("#rhs").addEventListener("focus", () => {
    lastIdInput = $("#rhs");
  });
  makeKeys($("#keys-main"), () => $("#expr"));
  makeKeys($("#keys-id"), () => lastIdInput);

  EXPR_EXAMPLES.forEach((x) => {
    const b = document.createElement("button");
    b.type = "button";
    b.className = "chip";
    b.textContent = x;
    b.dataset.expr = x;
    b.addEventListener("click", () => {
      $("#expr").value = x;
      update();
    });
    $("#expr-chips").appendChild(b);
  });

  ID_EXAMPLES.forEach((x) => {
    const b = document.createElement("button");
    b.type = "button";
    b.className = "chip";
    b.textContent = x.name;
    b.dataset.l = x.l;
    b.dataset.r = x.r;
    b.addEventListener("click", () => {
      $("#lhs").value = x.l;
      $("#rhs").value = x.r;
      update();
    });
    $("#id-chips").appendChild(b);
  });

  function syncChips() {
    const cur = $("#expr").value.trim();
    document.querySelectorAll("#expr-chips .chip").forEach((c) => {
      c.setAttribute("aria-pressed", c.dataset.expr === cur ? "true" : "false");
    });
    const l = $("#lhs").value.trim(),
      r = $("#rhs").value.trim();
    document.querySelectorAll("#id-chips .chip").forEach((c) => {
      c.setAttribute(
        "aria-pressed",
        c.dataset.l === l && c.dataset.r === r ? "true" : "false",
      );
    });
  }

  function setValues(v) {
    $("#setA").value = v.A;
    $("#setB").value = v.B;
    $("#setC").value = v.C;
    $("#extras").value = v.extras;
    update();
  }

  $("#btn-clear").addEventListener("click", () =>
    setValues({ A: "", B: "", C: "", extras: "" }),
  );
  $("#btn-random").addEventListener("click", () => {
    const pick = () =>
      Array.from({ length: 12 }, (_, i) => i + 1)
        .filter(() => Math.random() < 0.45)
        .join(", ");
    setValues({ A: pick(), B: pick(), C: pick(), extras: "" });
  });

  ["#setA", "#setB", "#setC", "#extras", "#expr", "#lhs", "#rhs"].forEach(
    (s) => {
      $(s).addEventListener("input", update);
    },
  );

  /* ---------- chip inputs, tabs, steps, region picking, export, theme ---------- */

  let cur = { data: null, sel: [] };
  const FIELDS = ["A", "B", "C", "extras"];
  const fid = (n) => (n === "extras" ? "#extras" : "#set" + n);

  function expandTokens(str) {
    return str
      .split(/[\s,;{}]+/)
      .filter(Boolean)
      .flatMap((t) => {
        const m = t.match(/^(\d+)(?:-|\.\.)(\d+)$/);
        if (m && Math.abs(+m[2] - +m[1]) <= 200) {
          const lo = Math.min(+m[1], +m[2]),
            hi = Math.max(+m[1], +m[2]);
          return Array.from({ length: hi - lo + 1 }, (_, i) => String(lo + i));
        }
        return [t];
      });
  }
  function commit(n, input) {
    const toks = expandTokens(input.value);
    input.value = "";
    if (!toks.length) return;
    $(fid(n)).value = [
      ...new Set([...parseList($(fid(n)).value), ...toks]),
    ].join(", ");
    update();
  }
  function renderChips() {
    FIELDS.forEach((n) => {
      const box = $("#chips-" + n),
        input = box.querySelector("input");
      box.querySelectorAll(".tok").forEach((t) => t.remove());
      const list = parseList($(fid(n)).value);
      $("#cnt-" + n).textContent = list.length;
      list.forEach((v) => {
        const t = document.createElement("span");
        t.className = "tok";
        t.innerHTML =
          esc(v) +
          '<button type="button" aria-label="Remove ' +
          esc(v) +
          '">×</button>';
        t.querySelector("button").addEventListener("click", () => {
          $(fid(n)).value = parseList($(fid(n)).value)
            .filter((x) => x !== v)
            .join(", ");
          update();
        });
        box.insertBefore(t, input);
      });
    });
  }
  FIELDS.forEach((n) => {
    const box = $("#chips-" + n),
      input = box.querySelector("input");
    box.addEventListener("click", () => input.focus());
    input.addEventListener("keydown", (e) => {
      if (e.key === "Enter" || e.key === "," || e.key === " ") {
        e.preventDefault();
        commit(n, input);
      } else if (e.key === "Backspace" && !input.value) {
        const l = parseList($(fid(n)).value);
        if (l.length) {
          l.pop();
          $(fid(n)).value = l.join(", ");
          update();
        }
      }
    });
    input.addEventListener("input", () => {
      if (/[,;\s]/.test(input.value)) commit(n, input);
    });
    input.addEventListener("blur", () => commit(n, input));
  });

  // Tabs
  document.querySelectorAll(".tab").forEach((tb) =>
    tb.addEventListener("click", () => {
      document
        .querySelectorAll(".tab")
        .forEach((x) => x.classList.toggle("on", x === tb));
      document.querySelectorAll(".pane").forEach((p) => {
        p.hidden = p.id !== "tab-" + tb.dataset.tab;
      });
    }),
  );

  // Step preview on the diagram
  const stepsBox = $("#tab-steps");
  const preview = (e) => {
    const li = e.target.closest && e.target.closest("li[data-i]");
    if (li && cur.data) paintDiagram(cur.data, stepsCache[+li.dataset.i].masks);
  };
  const unpreview = () => {
    if (cur.data) paintDiagram(cur.data, cur.sel);
  };
  stepsBox.addEventListener("pointerover", preview);
  stepsBox.addEventListener("focusin", preview);
  stepsBox.addEventListener("pointerleave", unpreview);
  stepsBox.addEventListener("focusout", unpreview);

  // Copy result
  $("#tab-result").addEventListener("click", (e) => {
    if (e.target.id !== "copy") return;
    const txt = $("#tab-result").dataset.text || "";
    const done = () => {
      e.target.textContent = "Copied!";
      setTimeout(() => {
        e.target.textContent = "Copy result";
      }, 1200);
    };
    if (navigator.clipboard)
      navigator.clipboard.writeText(txt).then(done, () => {});
    else done();
  });

  // Click a region: toggle it and rewrite the expression as a union of region terms
  function toggleRegion(m) {
    const set = new Set(cur.sel);
    if (set.has(m)) set.delete(m);
    else set.add(m);
    const masks = [...set].sort((a, b) => a - b);
    $("#expr").value =
      masks.length === 0
        ? "∅"
        : masks.length === 8
          ? "U"
          : masks
              .map((k) =>
                NAMES.map((nm, i) => ((k >> i) & 1 ? nm : nm + "′")).join(
                  " ∩ ",
                ),
              )
              .join(" ∪ ");
    update();
  }

  // Export the diagram as a standalone SVG
  $("#btn-svg").addEventListener("click", () => {
    const v = (n) =>
      getComputedStyle(document.documentElement).getPropertyValue(n).trim();
    const css =
      ".universe{fill:" +
      v("--solid") +
      ";stroke:" +
      v("--line") +
      ";stroke-width:1.5}.region rect{fill:transparent}.region.sel rect{fill:" +
      v("--sel") +
      "}.tint-a{fill:" +
      COLORS[0] +
      ";fill-opacity:.16}.tint-b{fill:" +
      COLORS[1] +
      ";fill-opacity:.16}.tint-c{fill:" +
      COLORS[2] +
      ";fill-opacity:.16}.outline{fill:none;stroke-width:3.5}" +
      ".els{font:600 14px sans-serif;fill:" +
      v("--ink") +
      "}.els.sel{fill:#fff}.set-label{font:800 24px sans-serif}.set-count,.u-label{font:13px sans-serif;fill:" +
      v("--muted") +
      "}";
    const c = svg.cloneNode(true);
    c.setAttribute("xmlns", NS);
    c.insertBefore(
      Object.assign(document.createElementNS(NS, "style"), {
        textContent: css,
      }),
      c.firstChild,
    );
    const bgRect = el("rect", {
      x: 0,
      y: 0,
      width: VIEW.w,
      height: VIEW.h,
      fill: v("--bg"),
    });
    c.insertBefore(bgRect, c.firstChild);
    const a = document.createElement("a");
    a.href = URL.createObjectURL(
      new Blob([new XMLSerializer().serializeToString(c)], {
        type: "image/svg+xml",
      }),
    );
    a.download = "venn-diagram.svg";
    a.click();
    URL.revokeObjectURL(a.href);
  });

  // Presets
  const PRESETS = {
    Numbers: EXAMPLE,
    Fruits: {
      A: "apple, mango, banana, grape",
      B: "mango, grape, kiwi, orange",
      C: "banana, kiwi, lemon, grape",
      extras: "pear, plum",
    },
    Languages: {
      A: "C, Java, Python, JS",
      B: "Python, JS, Go, Rust",
      C: "C, Rust, Go, Swift",
      extras: "Ruby",
    },
    Multiples: {
      A: "2, 4, 6, 8, 10, 12",
      B: "3, 6, 9, 12",
      C: "5, 10",
      extras: "1, 7, 11",
    },
  };
  Object.keys(PRESETS).forEach((k) => {
    const b = document.createElement("button");
    b.type = "button";
    b.className = "chip";
    b.textContent = k;
    b.addEventListener("click", () => setValues(PRESETS[k]));
    $("#presets").appendChild(b);
  });

  // Theme and saved state (storage can be blocked, so every access is guarded)
  const root = document.documentElement;
  function setTheme(t) {
    root.dataset.theme = t;
    $("#theme").textContent = t === "dark" ? "Light mode" : "Dark mode";
    if (cur.data) update();
  }
  $("#theme").addEventListener("click", () =>
    setTheme(root.dataset.theme === "dark" ? "light" : "dark"),
  );
  function save() {
    try {
      localStorage.setItem(
        "venn-engine",
        JSON.stringify({
          A: $("#setA").value,
          B: $("#setB").value,
          C: $("#setC").value,
          extras: $("#extras").value,
          expr: $("#expr").value,
          lhs: $("#lhs").value,
          rhs: $("#rhs").value,
          theme: root.dataset.theme,
        }),
      );
    } catch (e) {
      /* ignore */
    }
  }
  function load() {
    try {
      return JSON.parse(localStorage.getItem("venn-engine"));
    } catch (e) {
      return null;
    }
  }

  /* ---------- start ---------- */

  buildDiagram();
  const saved = load();
  if (saved) {
    $("#expr").value = saved.expr || $("#expr").value;
    $("#lhs").value = saved.lhs || $("#lhs").value;
    $("#rhs").value = saved.rhs || $("#rhs").value;
    if (saved.theme) setTheme(saved.theme);
    setValues(saved);
  } else {
    setValues(EXAMPLE);
  }
})();
