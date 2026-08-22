/* IronKernel site: reveal animations + Kernel/shell syntax highlighting. */

const IKR_OPERATIVE = new Set([
  // Primitive operatives (Runtime.fs)
  "vau",
  "ϝ",
  "define",
  "if",
  ".",
  "new",
  ".get",
  ".set",
  "clr-open",
  "clr-alias",
  "clr-type",
  "reset",
  "prompt",
  "contract",
  // Library operatives (kernel.ikr / promises.ikr)
  "quote",
  "sequence",
  "lambda",
  "λ",
  "let",
  "let*",
  "letrec",
  "letrec*",
  "defn",
  "cond",
  "and?",
  "or?",
  "lazy",
  "import!",
  "provide!",
  "set!",
  "remote-eval",
  "bindings->environment",
  "get-current-environment",
  "time",
]);

const IKR_APPLICATIVE = new Set([
  // Primitive applicatives (Runtime.fs)
  "eval",
  "wrap",
  "unwrap",
  "load",
  "call/cc",
  "+",
  "-",
  "*",
  "/",
  "<",
  "<=",
  ">",
  "car",
  "cdr",
  "cons",
  "eq?",
  "eqv?",
  "null?",
  "pair?",
  "zero?",
  "environment?",
  "make-environment",
  "environment-symbols",
  "environment-local-symbols",
  "environment-capabilities",
  "print",
  "printf",
  "show",
  "contract-of",
  "shift",
  "make-prompt-tag",
  "perform",
  "resume",
  "await-task",
  "task-delay",
  "vector",
  "vector?",
  "make-vector",
  "vector-ref",
  "vector-set!",
  "make-encapsulation-type",
  "clr-opens",
  "open-input-file",
  "open-output-file",
  "close-input-port",
  "close-output-port",
  "read",
  "write",
  "read-contents",
  "read-all",
  // Common library applicatives
  "list",
  "list*",
  "length",
  "map",
  "apply",
  "begin",
  "caar",
  "cadr",
  "cdar",
  "cddr",
  "any?",
  "zip",
  "for-each",
  "compose",
  "not?",
  "force",
  "memoize",
  "promise?",
  "let/cc",
]);

const IKR_CONSTANT = new Set(["#t", "#f", "#inert"]);
const IKR_NUMBER =
  /^-?(?:0[xX][0-9a-fA-F]+|(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?)L?$/;
const IKR_SYMBOL = /^[^\s()[\]";]+/;

const SHELL_BUILTINS =
  /^(?:git|dotnet|cd|tar|npm|ik|cat|ls|mkdir|curl|wget|export|source)\b/;

function escapeHtml(value) {
  return value
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

function span(kind, value) {
  return '<span class="tok-' + kind + '">' + escapeHtml(value) + "</span>";
}

function detectLanguage(code, source) {
  const fromClass = [...code.classList]
    .map((name) => name.match(/^language-(.+)$/))
    .find(Boolean);
  if (fromClass) {
    const lang = fromClass[1];
    if (lang === "text" || lang === "plain" || lang === "none") return null;
    if (lang === "bash" || lang === "sh" || lang === "console") return "shell";
    if (lang === "scheme" || lang === "lisp" || lang === "kernel") return "ikr";
    return lang;
  }

  const trimmed = source.trim();
  if (!trimmed) return null;
  if (/^[A-Za-z0-9_./-]+:\d+:\d+:/.test(trimmed)) return null;
  if (
    /^(?:git|dotnet|cd|tar|npm|ik|\.\/IronKernel|IronKernel\.exe)\b/m.test(trimmed) ||
    /^# (?:Release|Equivalent|Install|local)/m.test(trimmed)
  ) {
    return "shell";
  }
  if (
    /[();λϝ]/.test(trimmed) ||
    /(?:^|\s)(?:#t|#f|#inert)/.test(trimmed) ||
    /(?:^|\s)'[^\s]/.test(trimmed)
  ) {
    return "ikr";
  }
  return null;
}

function highlightIronKernel(source) {
  let out = "";
  let i = 0;
  while (i < source.length) {
    const ch = source[i];

    if (ch === ";") {
      const end = source.indexOf("\n", i);
      const comment = end === -1 ? source.slice(i) : source.slice(i, end);
      out += span("comment", comment);
      i += comment.length;
      continue;
    }

    if (ch === '"') {
      let j = i + 1;
      while (j < source.length) {
        if (source[j] === "\\") {
          j += 2;
          continue;
        }
        if (source[j] === '"') {
          j += 1;
          break;
        }
        j += 1;
      }
      out += span("string", source.slice(i, j));
      i = j;
      continue;
    }

    if (/\s/.test(ch)) {
      const m = source.slice(i).match(/^\s+/);
      out += escapeHtml(m[0]);
      i += m[0].length;
      continue;
    }

    if (ch === "'") {
      out += span("quote", "'");
      i += 1;
      continue;
    }

    if ("()[]".includes(ch)) {
      out += span("punct", ch);
      i += 1;
      continue;
    }

    if (ch === "&") {
      out += span("improper", "&");
      i += 1;
      continue;
    }

    const rest = source.slice(i);
    const m = rest.match(IKR_SYMBOL);
    if (!m) {
      out += escapeHtml(ch);
      i += 1;
      continue;
    }

    const token = m[0];
    if (IKR_CONSTANT.has(token)) out += span("constant", token);
    else if (IKR_NUMBER.test(token)) out += span("number", token);
    else if (IKR_OPERATIVE.has(token)) out += span("operative", token);
    else if (IKR_APPLICATIVE.has(token)) out += span("applicative", token);
    else if (token.startsWith(":")) out += span("keyword", token);
    else out += span("sym", token);
    i += token.length;
  }
  return out;
}

function highlightShellLine(line) {
  if (/^\s*#/.test(line)) return span("comment", line);

  let out = "";
  let i = 0;
  let firstToken = true;
  while (i < line.length) {
    const ch = line[i];

    if (/\s/.test(ch)) {
      const m = line.slice(i).match(/^\s+/);
      out += escapeHtml(m[0]);
      i += m[0].length;
      continue;
    }

    if (ch === '"' || ch === "'") {
      const quote = ch;
      let j = i + 1;
      while (j < line.length && line[j] !== quote) {
        if (line[j] === "\\" && quote === '"') j += 2;
        else j += 1;
      }
      if (j < line.length) j += 1;
      out += span("string", line.slice(i, j));
      i = j;
      firstToken = false;
      continue;
    }

    if (ch === "\\" && i + 1 < line.length && line[i + 1] === "\n") {
      out += span("improper", "\\");
      i += 1;
      continue;
    }

    const m = line.slice(i).match(/^[^\s"'\\]+/);
    if (!m) {
      out += escapeHtml(ch);
      i += 1;
      continue;
    }

    const token = m[0];
    if (firstToken && (SHELL_BUILTINS.test(token) || token.startsWith("./") || /\.exe$/.test(token))) {
      out += span("operative", token);
    } else if (token.startsWith("-")) {
      out += span("keyword", token);
    } else {
      out += span("sym", token);
    }
    i += token.length;
    firstToken = false;
  }
  return out;
}

function highlightShell(source) {
  return source
    .split(/(\n)/)
    .map((piece) => (piece === "\n" ? "\n" : highlightShellLine(piece)))
    .join("");
}

function highlightCodeBlocks() {
  document.querySelectorAll("pre > code").forEach((code) => {
    if (code.dataset.highlighted === "1") return;
    const source = code.textContent;
    const lang = detectLanguage(code, source);
    if (!lang) return;
    try {
      code.classList.add("language-" + lang);
      code.innerHTML = lang === "shell" ? highlightShell(source) : highlightIronKernel(source);
      code.dataset.highlighted = "1";
    } catch (err) {
      console.error("IronKernel highlight failed:", err);
    }
  });
}

function initReveal() {
  const prefersReduced = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  if (prefersReduced) {
    document.querySelectorAll(".reveal").forEach((el) => el.classList.add("in"));
    return;
  }

  const io = new IntersectionObserver(
    (entries) => {
      for (const entry of entries) {
        if (entry.isIntersecting) {
          entry.target.classList.add("in");
          io.unobserve(entry.target);
        }
      }
    },
    { threshold: 0.12, rootMargin: "0px 0px -8% 0px" }
  );
  document.querySelectorAll(".reveal").forEach((el) => io.observe(el));
}

initReveal();
highlightCodeBlocks();
