<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# rocq-candy

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/ku-sldg/rocq-candy/actions/workflows/docker-action.yml/badge.svg?branch=main
[docker-action-link]: https://github.com/ku-sldg/rocq-candy/actions/workflows/docker-action.yml




<Project Description>

## Meta

- Author(s):
  - Will Thomas
- License: [Creative Commons Attribution Share Alike 4.0 International](LICENSE)
- Compatible Coq versions: 8.20 later
- Compatible OCaml versions: 4.12 or later
- Additional dependencies:
  - [ExtLib](https://github.com/coq-community/coq-ext-lib)
  - [Dune](https://dune.build) 3.17 or later
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of rocq-candy
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install rocq-candy
```

To instead build and install manually, do:

``` shell
git clone https://github.com/ku-sldg/rocq-candy.git
cd rocq-candy
dune build
dune install
```



