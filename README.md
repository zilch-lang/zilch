# Zilch

[![stars](https://img.shields.io/github/stars/zilch-lang/gzc?color=%23fdaa33&style=for-the-badge)](https://github.com/zilch-lang/gzc/stargazers) [![forks](https://img.shields.io/github/forks/zilch-lang/gzc?color=%23654321&label=Forks&style=for-the-badge)](https://github.com/zilch-lang/gzc/network/members)

## Table of Contents

- [TL;DR](#tldr)
- [Getting started](#getting-started)
  - [Prerequisites](#prerequisites)
    - [Stack and/or cabal](#stack-andor-cabal)
    - [Cloning this repository](#cloning-this-repository)
  - [Building the compiler](#building-the-compiler)
- [Code examples](#code-examples)
- [Contributing](#contributing)
- [Q&A](#qa)
- [License](#license)

## TL;DR

Zilch is a statically and strongly-typed, low-level functional programming language.
The goal is to provide a fully-fledged functional programming language with focus on performance and easiness of use, despite its low-level aspect.

The end-goal (the evolutionary step) is to rewrite the entire project in Zilch once the language is mature enough.

## Getting started

As of now, no release has been built (yet), so you'll need to compile the project yourself if you want to use it.

<!--
### Prerequisites

:warning: If you also are using Nix, then you don't need to look at the various steps involving installing stack/cabal.
You can directly skip to building the project, after firing up a new `nix-shell`.

#### Stack and/or cabal

You will firstly need [`stack`](https://docs.haskellstack.org/en/stable/README/) is your path, in order to build the code. 
Stack is a haskell package & dependency manager as well as a build tool for haskell projects.
It is used here, but [`cabal`](https://www.haskell.org/cabal/) should work as well because we provide cabal files.

#### Cloning this repository

The next step is to clone this repository (how do you expect to build it otherwise? :wink:) to somewhere you feel confortable with.
Using `git`, you can just type `git clone https://github.com/zilch-lang/gzc <target-directory>` (where `<target-directory>` may be left blank, in which case the repository will be cloned in your current directory under the name `gzc`).

### Building the compiler

:warning: DISCLAIMER: It may take a long time, depending on your machine specs.

<details><summary>Stack users</summary>

All you need to do is to type `stack build`, and everything will be built for you.

</details>

<details><summary>Cabal users</summary>

To be honest, I don't work with cabal.
All I know is that you can type `cabal v2-build` to build the project.

</details>
-->

## Code examples

There aren't many examples, because of the non-stability of the project yet.
However, you can expect some to come later in the [examples](./examples) directory, as the project evolves into something more concrete.

## Contributing

Obviously, this project is open-source, which means that *you* may be involved in the development!
If you wish to have some features to be implemented, or even want to report a bug in the compile feel free to check out the [issues](https://github.com/zilch-lang/gzc/issues) to see if nobody already requested/reported it.
If someone was faster than you, don't worry, you can also drop a :thumbsup: on their issue to show that you may also be interested in this feature/want to see this bug resolved.

You may also fork this project and add your own code/features! 
However, the pull requests made may not always be accepted, depending on how relevant they are to the project.

## Q&A

Some of you, who are interested in programming language implementation, or even casual developers in search of their Graal programming language, may have some questions about Zilch.
Some of them are already listed below, but if you have some other, feel free to put them in the issues section, I'd be happy to answer them.

<details><summary><b>What does this project bring, compared to other functional/low-level programming languages?</b></summary>

I'd be enclined to say “Nothing”.
Most of the already in-use programming languages have not been made in 2 days, and are still actively maintained.
Some of them (e.g. Rust) are incredibly powerful (see how linear types can prevent some bugs for examples).

Zilch is not meant to be such a big programming language, and is mainly a research project that I'm making on my own, to explore type-system components, low-level functional programming and also because I like doing this kind of stuff.

</details>

<details><summary><b>Any current real-world use of this programming language?</b></summary>

No, at least not as far as I'm aware.
However, I plan on rewriting the compiler for Zilch and [N\*](https://github.com/zilch-lang/nsc) in Zilch at some point, when the language reaches some level of stability/usability.

</details>

## License

This work is licensed under the [BSD-3 license](./LICENSE).
