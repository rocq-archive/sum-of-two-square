<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# SumOfTwoSquare

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/SumOfTwoSquare/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/SumOfTwoSquare/actions/workflows/docker-action.yml





This directory contains the proof that a number n can be written as the 
sum of two square numbers if and only if each prime factor $p$ of $n$ 
that is equal to 3 modulo 4 has its exponent in the decomposition of n
that is even.

A note on the development is available at [here](https://inria.hal.science/hal-05025371)


To build the directory, type

  make all

Laurent Thery thery@sophia.inria.fr

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Additional dependencies: none
- Rocq/Coq namespace: `SumOfTwoSquare`
- Related publication(s): none

## Building and installation instructions

To build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/thery/SumOfTwoSquare.git
cd SumOfTwoSquare
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



