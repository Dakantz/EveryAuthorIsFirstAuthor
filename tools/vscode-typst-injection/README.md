# Typst inside LaTeX (VS Code injection grammar)

Highlights the body of `\begin{typst} ... \end{typst}` (see `paper/typst.sty`)
using Typst's own grammar.

## Install

A workspace `.vscode/` cannot contribute grammars, so this has to be linked
into the per-user extensions directory:

    ln -s "$PWD/tools/vscode-typst-injection" ~/.vscode/extensions/latex-typst-injection

Use `~/.vscode-server/extensions` for VS Code Remote, or
`~/.vscode-oss/extensions` for VSCodium. Then reload the window
(`Developer: Reload Window`).

## Requires

[Tinymist](https://marketplace.visualstudio.com/items?itemName=myriad-dreamin.tinymist)
(or any extension providing the `source.typst` scope). Without it the
injection matches but has no grammar to apply.

## What it does not do

Formatting. VS Code formats per document language, so `typstfmt` will not run
inside a `.tex` buffer. `.vscode/settings.json` keeps latexindent from
reindenting these blocks instead.
