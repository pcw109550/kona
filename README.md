<h1 align="center">
<img src="./assets/banner.png" alt="Kona" width="100%" align="center">
</h1>

<h4 align="center">
    The Monorepo for <a href="https://specs.optimism.io/">OP Stack</a> Types, Components, and Services built in Rust.
</h4>

<p align="center">
  <a href="https://github.com/op-rs/kona/releases"><img src="https://img.shields.io/github/v/release/op-rs/kona?style=flat&labelColor=1C2C2E&color=C96329&logo=GitHub&logoColor=white"></a>
  <a href="https://docs.rs/kona-derive/"><img src="https://img.shields.io/docsrs/kona-derive?style=flat&labelColor=1C2C2E&color=C96329&logo=Rust&logoColor=white"></a>
  <a href="https://github.com/op-rs/kona/actions/workflows/rust_ci.yaml"><img src="https://img.shields.io/github/actions/workflow/status/op-rs/kona/rust_ci.yaml?style=flat&labelColor=1C2C2E&label=ci&color=BEC5C9&logo=GitHub%20Actions&logoColor=BEC5C9" alt="CI"></a>
  <a href="https://codecov.io/gh/op-rs/kona"><img src="https://img.shields.io/codecov/c/gh/op-rs/kona?style=flat&labelColor=1C2C2E&logo=Codecov&color=BEC5C9&logoColor=BEC5C9" alt="Codecov"></a>
  <a href="https://github.com/op-rs/kona/blob/main/LICENSE.md"><img src="https://img.shields.io/badge/License-MIT-d1d1f6.svg?style=flat&labelColor=1C2C2E&color=BEC5C9&logo=googledocs&label=license&logoColor=BEC5C9" alt="License"></a>
  <a href="https://op-rs.github.io/kona"><img src="https://img.shields.io/badge/Book-854a15?style=flat&labelColor=1C2C2E&color=BEC5C9&logo=mdBook&logoColor=BEC5C9" alt="Book"></a>
</p>

<p align="center">
  <a href="#whats-kona">What's Kona?</a> •
  <a href="#overview">Overview</a> •
  <a href="#overview">MSRV</a> •
  <a href="https://op-rs.github.io/kona/CONTRIBUTING.html">Contributing</a> •
  <a href="#credits">Credits</a> •
  <a href="#license">License</a>
</p>


## What's Kona?

Originally a suite of portable implementations of the OP Stack rollup state transition,
Kona has been extended to be _the monorepo_ for <a href="https://specs.optimism.io/">OP Stack</a>
types, components, and services built in Rust. Kona provides an ecosystem of extensible, low-level
crates that compose into components and services required for the OP Stack.

Kona contains many foundational crates including:
- The [derivation pipeline][g-derivation-pipeline].
- A stateless block executor.

Built on top of these libraries, this repository also features a [fault proof program][fpp-specs]
designed to deterministically execute the rollup state transition in order to verify an
[L2 output root][g-output-root] from the L1 inputs it was [derived from][g-derivation-pipeline].

The [book][book] contains a more in-depth overview of the project, contributor guidelines, tutorials for
getting started with building your own programs, and a reference for the libraries and tools provided by Kona.


> [!IMPORTANT]
>
> Ethereum (Alloy) types modified for the OP Stack live in [op-alloy](https://github.com/alloy-rs/op-alloy).


### Alternative Backends

Kona's libraries were built with alternative backend support and extensibility in mind - it is not just a fault proof
program! Kona is also used by:

- [`op-succinct`][op-succinct]
- [`kailua`][kailua]

To build your own backend for kona, or build a new application on top of its libraries,
see the [SDK section of the book](https://op-rs.github.io/kona/sdk/intro.html).

### Development Status

> [!WARNING]
>
> `kona` is currently in active development, and is not yet ready for use in production.

## Overview

**Binaries**

- [`client`](./bin/client): The bare-metal program that runs on top of a [fault proof VM][g-fault-proof-vm].
- [`host`](./bin/host): The host program that runs natively alongside the FPVM, serving as the [Preimage Oracle][g-preimage-oracle] server.

**Protocol**

- [`genesis`](./crates/protocol/genesis): Genesis types for OP Stack chains.
- [`protocol`](./crates/protocol/protocol): Core protocol types used across OP Stack rust crates.
- [`derive`](./crates/protocol/derive): `no_std` compatible implementation of the [derivation pipeline][g-derivation-pipeline].
- [`driver`](./crates/protocol/driver): Stateful derivation pipeline driver.
- [`interop`](./crates/protocol/interop): Core functionality and primitives for the [Interop feature](https://specs.optimism.io/interop/overview.html) of the OP Stack.
- [`registry`](./crates/protocol/registry): Rust bindings for the [superchain-registry][superchain-registry].

**Proof**

- [`mpt`](./crates/proof/mpt): Utilities for interacting with the Merkle Patricia Trie in the client program.
- [`executor`](./crates/proof/executor): `no_std` stateless block executor for the [OP Stack][op-stack].
- [`kona-proof`](./crates/proof/proof): High level OP Stack state transition proof SDK.
- [`kona-proof-interop`](./crates/proof/proof-interop): Extension of `kona-proof` with interop support.
- [`preimage`](./crates/proof/preimage): High level interfaces to the [`PreimageOracle`][fpp-specs] ABI.
- [`std-fpvm`](./crates/proof/std-fpvm): Platform specific [Fault Proof VM][g-fault-proof-vm] kernel APIs.
- [`std-fpvm-proc`](./crates/proof/std-fpvm-proc): Proc macro for [Fault Proof Program][fpp-specs] entrypoints.

**External**

- [`rpc`](./crates/external/rpc): OP Stack RPC types and extensions.
- [`net`](./crates/external/net): OP Stack Networking including P2P and Discovery.

**Providers**

- [`providers-alloy`](./crates/providers/providers-alloy): Provider implementations for `kona-derive` backed by [Alloy][alloy].
- [`providers-local`](./crates/providers/providers-local): Local provider implementations for `kona-derive`.

**Utilities**

- [`serde`](./crates/utilities/serde): Serialization helpers.


## MSRV

The current MSRV (minimum supported rust version) is 1.81.

The MSRV is not increased automatically, and will be updated
only as part of a patch (pre-1.0) or minor (post-1.0) release.


## Contributing

`kona` is built by open source contributors like you, thank you for improving the project!

A [contributing guide][contributing] is available that sets guidelines for contributing.

Pull requests will not be merged unless CI passes, so please ensure that your contribution
follows the linting rules and passes clippy.


## Credits

`kona` is inspired by the work of several teams, namely [OP Labs][op-labs] and other contributors' work on the
[`op-program`][op-program] and [BadBoiLabs][bad-boi-labs]'s work on [Cannon-rs][badboi-cannon-rs].

`kona` is also built on rust types in [alloy][alloy], [op-alloy][op-alloy], and [maili][maili].


## License

Licensed under the <a href="LICENSE-MIT">MIT license</a>.

> [!NOTE]
>
> Contributions intentionally submitted for inclusion in these crates by you
> shall be licensed as above, without any additional terms or conditions.


<!-- Links -->

[alloy]: https://github.com/alloy-rs/alloy
[maili]: https://github.com/op-rs/maili
[op-alloy]: https://github.com/alloy-rs/op-alloy
[contributing]: https://op-rs.github.io/kona/CONTRIBUTING.html
[op-stack]: https://github.com/ethereum-optimism/optimism
[superchain-registry]: https://github.com/ethereum-optimism/superchain-registry
[op-program]: https://github.com/ethereum-optimism/optimism/tree/develop/op-program
[cannon]: https://github.com/ethereum-optimism/optimism/tree/develop/cannon
[cannon-rs]: https://github.com/op-rs/cannon-rs
[badboi-cannon-rs]: https://github.com/BadBoiLabs/cannon-rs
[asterisc]: https://github.com/etheruem-optimism/asterisc
[fpp-specs]: https://specs.optimism.io/fault-proof/index.html
[book]: https://op-rs.github.io/kona/
[op-succinct]: https://github.com/succinctlabs/op-succinct
[kailua]: https://github.com/risc0/kailua
[op-labs]: https://github.com/ethereum-optimism
[bad-boi-labs]: https://github.com/BadBoiLabs
[g-output-root]: https://specs.optimism.io/glossary.html#l2-output-root
[g-derivation-pipeline]: https://specs.optimism.io/protocol/derivation.html#l2-chain-derivation-pipeline
[g-fault-proof-vm]: https://specs.optimism.io/experimental/fault-proof/index.html#fault-proof-vm
[g-preimage-oracle]: https://specs.optimism.io/fault-proof/index.html#pre-image-oracle
