
# Compositional Secure Compilation

This repository contains all files related to work "Compositional Secure Compilation".

## Building

This repository uses `latexmk`, so there is no need to re-run your latex compiler, `makeglossaries`, or `bibtex`/`biber`.
To build, simply run `latexmk -pdf`.
Any files emitted by the compilation process are put into a `build/` directory, including the final `pdf`.

## Structure

- `main.tex` is, as the name might imply, the main development file.
- `glossary.tex` is a collection of various definitions; especially (hyper-)security properties, found among existing work.
- `acronyms.tex` list of acronyms
- `library.bib` contains any reference whatsoever.

