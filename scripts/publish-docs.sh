#!/usr/bin/env bash
# Put the generated documentation on the gh-pages branch, which GitHub Pages serves.
# Usage: bash scripts/publish-docs.sh [--push]   (the remote is $REMOTE, origin by default)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="$ROOT/docs/coqdoc-noproofs"
BRANCH=gh-pages
REMOTE="${REMOTE:-origin}"
PUSH=no
if [[ "${1:-}" == "--push" ]]; then PUSH=yes; fi

if [[ -n "$(git -C "$ROOT" status --porcelain --untracked-files=no)" ]]; then
  echo "The working tree has uncommitted changes: commit them first, so that the pages match a commit." >&2
  exit 1
fi

# Document only published code: HEAD must already be on a branch of the remote.
git -C "$ROOT" fetch -q "$REMOTE"
if [[ -z "$(git -C "$ROOT" branch -r --contains HEAD --list "$REMOTE/*" | grep -v "$REMOTE/$BRANCH\$" || true)" ]]; then
  echo "HEAD is not on $REMOTE yet: push it first, so that the pages describe published code." >&2
  exit 1
fi

bash "$ROOT/scripts/generate-docs.sh"

# The site is the generated pages, without the templates coqdoc read, plus .nojekyll so that
# GitHub Pages serves the files as they are.
SITE="$(mktemp -d)"
INDEX="$(mktemp)"
trap 'rm -rf "$SITE" "$INDEX"' EXIT
cp -R "$OUT"/. "$SITE"
rm -f "$SITE/header.html" "$SITE/footer.html"
touch "$SITE/.nojekyll"

# Build the commit without touching the working tree: a temporary index over the site directory.
git -C "$ROOT" fetch -q "$REMOTE" "$BRANCH" 2>/dev/null || true
PARENT="$(git -C "$ROOT" rev-parse -q --verify "refs/remotes/$REMOTE/$BRANCH" \
  || git -C "$ROOT" rev-parse -q --verify "refs/heads/$BRANCH" || true)"
rm -f "$INDEX"
export GIT_INDEX_FILE="$INDEX"
git -C "$ROOT" --work-tree="$SITE" add -A -f .
TREE="$(git -C "$ROOT" write-tree)"
unset GIT_INDEX_FILE

if [[ -n "$PARENT" && "$TREE" == "$(git -C "$ROOT" rev-parse "$PARENT^{tree}")" ]]; then
  echo "The documentation on $BRANCH is already up to date."
else
  SOURCE="$(git -C "$ROOT" rev-parse --abbrev-ref HEAD)@$(git -C "$ROOT" rev-parse --short HEAD)"
  COMMIT="$(git -C "$ROOT" commit-tree "$TREE" ${PARENT:+-p "$PARENT"} -m "Update the documentation to $SOURCE")"
  git -C "$ROOT" update-ref "refs/heads/$BRANCH" "$COMMIT"
  echo "Committed the documentation of $SOURCE on the local branch $BRANCH."
fi

if [[ "$PUSH" == yes ]]; then
  git -C "$ROOT" push "$REMOTE" "$BRANCH"
else
  echo "Nothing pushed. To publish: git push $REMOTE $BRANCH, or run this script with --push."
fi
