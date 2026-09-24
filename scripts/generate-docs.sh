#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD="$ROOT/_build/default"
OUT="$ROOT/docs/coqdoc-noproofs"
STYLE_SRC="$ROOT/docs/coqdoc-assets"
DIRS=(Common CPSA Original)

# The order of the directories on the landing page; others follow in alphabetical order.
ORDER=(Common CPSA CPSA/Instances Original/Instances Original/Examples/simple_auth
       Original/Examples/nsl Original/Examples/ns_original Original/Examples/kmp)

group_of() {
  case "$1" in
    Common) echo "Framework" ;;
    CPSA|CPSA/*) echo "Partial order and operational semantics" ;;
    Original/*) echo "The CSF 2025 development" ;;
    *) echo "Other modules" ;;
  esac
}

describe() {
  case "$1" in
    Common) echo "Strands, bundles and their inductive characterization, and the tactics shared by the whole development." ;;
    CPSA) echo "CPSA-style protocol syntax, the operational semantics, and its correspondence with bundles." ;;
    CPSA/Instances) echo "Terms, penetrator, and default instances for the CPSA development." ;;
    Original/Instances) echo "Terms, penetrator, and default instances for the case studies." ;;
    Original/Examples/simple_auth) echo "A simple unilateral authentication protocol and its variants." ;;
    Original/Examples/nsl) echo "The Needham-Schroeder-Lowe protocol: authentication and secrecy." ;;
    Original/Examples/ns_original) echo "The original Needham-Schroeder protocol." ;;
    Original/Examples/kmp) echo "Key management policies." ;;
    *) echo "" ;;
  esac
}

# The links come from the .glob files, which must match the sources.
(cd "$ROOT" && dune build)

if [[ ! -f "$BUILD/Common/Strands.glob" ]]; then
  echo "No build found in $BUILD: run 'dune build' first." >&2
  exit 1
fi

mkdir -p "$OUT"
rm -f "$OUT"/strandsrocq.*.html

cp "$STYLE_SRC/header.html" "$OUT/header.html"
cp "$STYLE_SRC/footer.html" "$OUT/footer.html"
cp "$STYLE_SRC/style.css" "$OUT/style.css"

# The sources, listed from the repository and grouped by directory.
FILES=()
for top in "${DIRS[@]}"; do
  while IFS= read -r f; do FILES+=("$f"); done < <(
    cd "$ROOT" && find "$top" -name '*.v' |
      awk '{ d = $0; sub(/\/[^\/]*$/, "", d); print d "\t" $0 }' | LC_ALL=C sort | cut -f2)
done

# coqdoc reads each source next to its .glob file, which dune leaves in the build.  Work on a
# copy of both, where the comments inside proofs become ordinary comments and so are hidden
# with the proofs.  The replacement keeps every byte offset, which the .glob files refer to,
# and the digest at the top of each .glob is updated, since coqdoc ignores a stale one.
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
for f in "${FILES[@]}"; do
  mkdir -p "$WORK/$(dirname "$f")"
  cp "$ROOT/$f" "$WORK/$f"
  if [[ -f "$BUILD/${f%.v}.glob" ]]; then cp "$BUILD/${f%.v}.glob" "$WORK/${f%.v}.glob"; fi
done
chmod -R u+w "$WORK"
python3 - "$WORK" "${FILES[@]}" <<'PY'
import hashlib, os, re, sys

work, files = sys.argv[1], sys.argv[2:]
proof = re.compile(r"(?m)^[ \t]*Proof[ \t]*(?:\.|with\b|using\b).*?\b(?:Qed|Defined|Admitted|Abort)\s*\.", re.S)
# coqdoc reads $, # and % in comments as escapes to LaTeX and HTML; in ordinary comments they
# are replaced by placeholders of the same length, put back once the pages are written.
PLACEHOLDERS = str.maketrans({"$": "\x01", "#": "\x02", "%": "\x03"})

def ordinary_comments(s):
    i, n = 0, len(s)
    while i < n:
        if s[i] == '"':
            j = i + 1
            while j < n and not (s[j] == '"' and not s.startswith('""', j)):
                j += 2 if s.startswith('""', j) else 1
            i = j + 1
        elif s.startswith("(*", i):
            doc = s.startswith("(**", i) and not s.startswith("(**)", i)
            depth, j = 1, i + 2
            while j < n and depth:
                if s.startswith("(*", j):
                    depth, j = depth + 1, j + 2
                elif s.startswith("*)", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            if not doc:
                yield i, j
            i = j
        else:
            i += 1

for f in files:
    v = os.path.join(work, f)
    old = open(v, "rb").read()
    s = proof.sub(lambda m: re.sub(r"\(\*\*(?!\))", "(* ", m.group(0)), old.decode("utf-8"))
    parts, last = [], 0
    for a, b in list(ordinary_comments(s)):
        parts += [s[last:a], s[a:b].translate(PLACEHOLDERS)]
        last = b
    new = ("".join(parts) + s[last:]).encode("utf-8")
    g = v[:-2] + ".glob"
    first, _, rest = open(g, encoding="utf-8").read().partition("\n") if os.path.exists(g) else ("", "", "")
    if first != "DIGEST " + hashlib.md5(old).hexdigest():
        print(f"warning: {f} changed since the last build, its page has no links: run 'dune build'",
              file=sys.stderr)
        first = ""
    if new == old:
        continue
    assert len(new) == len(old)
    open(v, "wb").write(new)
    if first:
        open(g, "w", encoding="utf-8").write("DIGEST " + hashlib.md5(new).hexdigest() + "\n" + rest)
PY

(cd "$WORK" && coqdoc \
  --html \
  --gallina \
  --utf8 \
  --parse-comments \
  --toc \
  --index identifiers \
  --with-header "$OUT/header.html" \
  --with-footer "$OUT/footer.html" \
  -R . strandsrocq \
  -d "$OUT" \
  "${FILES[@]}")

# Keep only the ordinary comments that follow code on the same line, such as those on the
# edges of a bundle: drop the ones on a line of their own, with their line.
python3 - "$OUT" <<'PY'
import glob, os, re, sys

BLANK = re.compile(r"(?:\s|&nbsp;)*")
OPEN = '<span class="comment">'
CODE = '<div class="code">'

def span_end(s, i):
    depth, j = 0, i
    while True:
        o, c = s.find("<span", j), s.find("</span>", j)
        if o != -1 and o < c:
            depth, j = depth + 1, o + 5
        else:
            depth, j = depth - 1, c + 7
            if depth == 0:
                return j

for p in glob.glob(os.path.join(sys.argv[1], "strandsrocq.*.html")):
    s = open(p, encoding="utf-8").read()
    out, i = [], 0
    while (a := s.find(OPEN, i)) >= 0:
        b = span_end(s, a)
        br, code = s.rfind("<br/>", 0, a), s.rfind(CODE, 0, a)
        start = max(br + len("<br/>") if br >= 0 else 0, code + len(CODE) if code >= 0 else 0)
        if not BLANK.fullmatch(s, start, a):
            # keep the spaces before the comment, which align it with its neighbours
            out.append(re.sub(r" +$", lambda m: "&nbsp;" * len(m.group(0)), s[i:a]) + s[a:b])
        else:
            nb = s.find("<br/>", b)
            if nb >= 0 and BLANK.fullmatch(s, b, nb):
                out.append(s[i:start])
                b = nb + len("<br/>")
            else:
                out.append(s[i:a])
        i = b
    out.append(s[i:])
    s = "".join(out).translate({1: "$", 2: "#", 3: "%"})
    open(p, "w", encoding="utf-8").write(s)
PY

# Drop the code blocks that hold only blank lines, which coqdoc emits between two comments.
perl -0pi -e 's{<div class="code">(?:\s|<br/>|&nbsp;)*</div>\n?}{}g' "$OUT"/strandsrocq.*.html

# A name that comes from a functor application, or from a parameter of a functor, is linked to
# the module that instantiates it, where no definition is shown.  Point such links to the
# definition, found by name among the framework pages, and drop those that remain ambiguous.
python3 - "$OUT" <<'PY'
import collections, glob, os, re, sys

out = sys.argv[1]
text = {os.path.basename(p): open(p, encoding="utf-8").read()
        for p in glob.glob(os.path.join(out, "strandsrocq.*.html"))}
ids = {p: set(re.findall(r'\bid="([^"]+)"', s)) for p, s in text.items()}

def area(page):
    return page.split(".")[1]

def framework(page):
    return area(page) in ("Common", "CPSA") or page.startswith("strandsrocq.Original.Instances.")

defs = collections.defaultdict(list)
for page, names in ids.items():
    if framework(page):
        for i in names:
            if ":" not in i and not i.startswith("lab"):
                defs[i.split(".")[-1]].append((page, i))

def resolve(page, anchor):
    if ":" in anchor:
        # A local binder, as in a recursive reference: link to the definition on the same page.
        name = anchor.split(":")[0]
        own = [i for i in ids.get(page, ()) if ":" not in i and i.split(".")[-1] == name]
        return (page, own[0]) if len(own) == 1 else None
    path = anchor.split(".")
    cands = [c for c in defs.get(path[-1], []) if area(c[0]) in (area(page), "Common")]
    def score(c):
        cp, k = c[1].split("."), 0
        while k < min(len(cp), len(path)) and cp[-1 - k] == path[-1 - k]:
            k += 1
        return k, area(c[0]) == area(page)
    if not cands:
        return None
    best = max(score(c) for c in cands)
    top = [c for c in cands if score(c) == best]
    return top[0] if len(top) == 1 else None

fixed = dropped = 0
link = re.compile(r'<a class="(idref|modref)" href="((?:strandsrocq\.[^"#]*\.html)?)#([^"]+)">(.*?)</a>', re.S)
for page, s in text.items():
    def repl(m):
        global fixed, dropped
        target = m.group(2) or page
        if m.group(3) in ids.get(target, ()):
            return m.group(0)
        r = resolve(target, m.group(3))
        if r is None:
            dropped += 1
            return m.group(4)
        fixed += 1
        href = ("" if r[0] == page else r[0]) + "#" + r[1]
        return f'<a class="{m.group(1)}" href="{href}">{m.group(4)}</a>'
    new = link.sub(repl, s)
    if new != s:
        with open(os.path.join(out, page), "w", encoding="utf-8") as f:
            f.write(new)
print(f"links redirected to their definition: {fixed}, links dropped: {dropped}")
PY

# Give the table of contents and the index of identifiers a title.
add_title() {
  awk -v t="$2" '{ print } /<main class="coqdoc-page">/ && !done { print "<h1 class=\"libtitle\">" t "</h1>"; done = 1 }' \
    "$OUT/$1" > "$OUT/$1.tmp" && mv "$OUT/$1.tmp" "$OUT/$1"
}
add_title toc.html "Contents"
add_title identifiers.html "Index"

# The directories that hold the sources, in the order of ORDER.
FOUND=()
for f in "${FILES[@]}"; do
  d="$(dirname "$f")"
  case " ${FOUND[*]:-} " in *" $d "*) ;; *) FOUND+=("$d") ;; esac
done
DIRS_ORDERED=()
for d in "${ORDER[@]}"; do
  case " ${FOUND[*]} " in *" $d "*) DIRS_ORDERED+=("$d") ;; esac
done
for d in "${FOUND[@]}"; do
  case " ${ORDER[*]} " in *" $d "*) ;; *) DIRS_ORDERED+=("$d") ;; esac
done

{
  sed '/<main class="coqdoc-page">/d' "$STYLE_SRC/header.html"
  cat <<'HTML'
<main class="coqdoc-page doc-index">
<h1 class="libtitle">StrandsRocq</h1>
<p class="lead">A Rocq mechanization of strand spaces, with a CPSA-style operational semantics and the case studies of the CSF 2025 paper. The pages show statements and comments, without proof bodies.</p>
HTML
  group=""
  for d in "${DIRS_ORDERED[@]}"; do
    g="$(group_of "$d")"
    if [[ "$g" != "$group" ]]; then
      if [[ -n "$group" ]]; then printf '</dl>\n'; fi
      printf '\n<h2>%s</h2>\n<dl>\n' "$g"
      group="$g"
    fi
    desc="$(describe "$d")"
    printf '<dt><b>%s</b>%s</dt>\n<dd>' "$d" "${desc:+: $desc}"
    for f in "${FILES[@]}"; do
      if [[ "$(dirname "$f")" == "$d" ]]; then
        printf '<a href="strandsrocq.%s.html">%s</a> ' "$(echo "${f%.v}" | tr / .)" "$(basename "$f" .v)"
      fi
    done
    printf '</dd>\n'
  done
  printf '</dl>\n'
  cat "$STYLE_SRC/footer.html"
} > "$OUT/index.html"

echo "Documentation written to:"
echo "  $OUT/index.html"
