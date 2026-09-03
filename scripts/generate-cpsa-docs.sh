#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="$ROOT/docs/coqdoc-noproofs"
STYLE_SRC="$ROOT/docs/coqdoc-assets"

mkdir -p "$OUT"

cp "$STYLE_SRC/header.html" "$OUT/header.html"
cp "$STYLE_SRC/footer.html" "$OUT/footer.html"
cp "$STYLE_SRC/style.css" "$OUT/style.css"

coqdoc \
  --html \
  --gallina \
  --utf8 \
  --toc \
  --interpolate \
  --no-glob \
  --with-header "$OUT/header.html" \
  --with-footer "$OUT/footer.html" \
  -R "$ROOT" strandsrocq \
  -d "$OUT" \
  "$ROOT/Common/Enumerate.v" \
  "$ROOT/Common/BundleSizeInduction.v" \
  "$ROOT/Common/BundleSizeInductionFixed.v" \
  "$ROOT/CPSA/ChoiceRoles.v" \
  "$ROOT/CPSA/ComputableSemantics.v" \
  "$ROOT/CPSA/ProtocolExamples.v" \
  "$ROOT/CPSA/PaperExamples.v" \
  "$ROOT/CPSA/RoleSyntax.v" \
  "$ROOT/CPSA/Semantics.v" \
  "$ROOT/CPSA/LabelledSemantics.v" \
  "$ROOT/CPSA/EnumerationSemantics.v" \
  "$ROOT/CPSA/Instances/DefaultInstances.v" \
  "$ROOT/CPSA/Instances/EmbeddedTraceStrands.v" \
  "$ROOT/CPSA/Instances/Penetrator.v" \
  "$ROOT/CPSA/Instances/UTermTacticsTests.v" \
  "$ROOT/CPSA/Instances/UTerms.v" \
  "$ROOT/CPSA/Instances/UTermsTactics.v"

cat > "$OUT/index.html" <<'HTML'
<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>CPSA Documentation</title>
  <link rel="stylesheet" href="style.css">
</head>
<body>
<main class="coqdoc-page doc-index">
  <header class="page-header">
    <p class="eyebrow">strandsrocq / CPSA</p>
    <h1>CPSA Documentation</h1>
    <p class="subtitle">
      Coqdoc pages for the strand-space infrastructure and CPSA syntax,
      semantics, examples, and concrete term instances. Generated without
      proof bodies.
    </p>
  </header>

  <section>
    <h2>Common: enumeration and bundle induction</h2>
    <ul class="file-tree">
      <li><a href="strandsrocq.Common.Enumerate.html">Enumerate.v</a></li>
      <li><a href="strandsrocq.Common.BundleSizeInduction.html">BundleSizeInduction.v</a></li>
      <li><a href="strandsrocq.Common.BundleSizeInductionFixed.html">BundleSizeInductionFixed.v</a></li>
    </ul>
  </section>

  <section>
    <h2>CPSA</h2>
    <ul class="file-tree">
      <li><a href="strandsrocq.CPSA.RoleSyntax.html">RoleSyntax.v</a></li>
      <li><a href="strandsrocq.CPSA.ChoiceRoles.html">ChoiceRoles.v</a></li>
      <li><a href="strandsrocq.CPSA.Semantics.html">Semantics.v</a></li>
      <li><a href="strandsrocq.CPSA.ComputableSemantics.html">ComputableSemantics.v</a></li>
      <li><a href="strandsrocq.CPSA.LabelledSemantics.html">LabelledSemantics.v</a></li>
      <li><a href="strandsrocq.CPSA.EnumerationSemantics.html">EnumerationSemantics.v</a></li>
      <li><a href="strandsrocq.CPSA.PaperExamples.html">PaperExamples.v</a></li>
      <li><a href="strandsrocq.CPSA.ProtocolExamples.html">ProtocolExamples.v</a></li>
    </ul>
  </section>

  <section>
    <h2>CPSA/Instances</h2>
    <ul class="file-tree">
      <li><a href="strandsrocq.CPSA.Instances.UTerms.html">UTerms.v</a></li>
      <li><a href="strandsrocq.CPSA.Instances.UTermsTactics.html">UTermsTactics.v</a></li>
      <li><a href="strandsrocq.CPSA.Instances.UTermTacticsTests.html">UTermTacticsTests.v</a></li>
      <li><a href="strandsrocq.CPSA.Instances.EmbeddedTraceStrands.html">EmbeddedTraceStrands.v</a></li>
      <li><a href="strandsrocq.CPSA.Instances.DefaultInstances.html">DefaultInstances.v</a></li>
      <li><a href="strandsrocq.CPSA.Instances.Penetrator.html">Penetrator.v</a></li>
    </ul>
  </section>

  <section>
    <h2>Generated Indexes</h2>
    <ul class="file-tree">
      <li><a href="toc.html">Coqdoc table of contents</a></li>
    </ul>
  </section>
</main>
</body>
</html>
HTML

echo "CPSA documentation written to:"
echo "  $OUT/index.html"
