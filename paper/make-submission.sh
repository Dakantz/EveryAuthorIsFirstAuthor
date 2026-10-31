#!/usr/bin/env bash
# Package the paper source into an arXiv-uploadable zip, containing only the
# files LaTeX actually read (per main.fls) plus the precompiled bibliography.
# arXiv runs neither shell escape nor biber, so the minted and typst caches
# ship along (both are in main.fls) and minted is switched to frozencache.
set -euo pipefail
cd "$(dirname "$0")"

[ main.fls -nt main.tex ] || echo "warning: main.fls is older than main.tex, run latexmk first" >&2

out=arxiv-submission.zip
rm -f "$out"
stage=$(mktemp -d)
trap 'rm -rf "$stage"' EXIT

{
  # INPUT lines from latexmk's file list, restricted to files inside the project
  grep '^INPUT ' main.fls | cut -d' ' -f2- | grep -v '^/' | sed 's|^\./||'
  echo main.bbl
  echo sources.bib
} | grep -vE '^main\.(aux|out|run\.xml|tex)$' | sort -u | while read -r f; do
  [ -f "$f" ] || continue  # temporaries such as minted's *.config.minted
  dest=$stage/src/${f#../}  # ../lib/equalauthors.sty -> lib/, found via \input@path
  mkdir -p "$(dirname "$dest")"
  cp "$f" "$dest"
done

sed 's/\\usepackage{minted}/\\usepackage[frozencache]{minted}/' main.tex > "$stage/src/main.tex"
grep -q frozencache "$stage/src/main.tex" || { echo "error: \\usepackage{minted} not found in main.tex" >&2; exit 1; }

(cd "$stage/src" && zip -qr "$OLDPWD/$out" .)

# Test build of the zip as arXiv does it: no shell escape, no biber.
mkdir "$stage/test"
unzip -q "$out" -d "$stage/test"
for _ in 1 2; do
  (cd "$stage/test" && pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex >/dev/null) || {
    cp "$stage/test/main.log" arxiv-test.log
    echo "error: test build failed, see arxiv-test.log" >&2
    exit 1
  }
done
if grep -E 'Warning: .*(undefined|Rerun)' "$stage/test/main.log"; then
  echo "warning: test build has unresolved references (above)" >&2
fi

unzip -l "$out"
echo "ok: $out builds without shell escape ($(pdfinfo "$stage/test/main.pdf" | awk '/^Pages/ {print $2}') pages)"
echo "note: main.bbl must match arXiv's biblatex version (built here with biber $(biber --version | awk '{print $3}'))"
