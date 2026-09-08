# Vyper-HOL
Formal semantics for the [Vyper](https://vyperlang.org) programming language for [Ethereum](https://ethereum.org) in the [HOL4 theorem prover](https://hol-theorem-prover.org).

This work is part of the ongoing [Verifereum](https://verifereum.org) project building formal specifications and infrastructure for formal verification of Ethereum applications. Vyper is a compelling choice of programming language for secure smart contracts because of its clean design and focus on simplicity and readability. Formal semantics for Vyper, as pursued here, serves as a rigorous precise mathematical specification of the language and as an essential requirement for building a formally verified compiler from Vyper to EVM (Ethereum virtual machine) bytecode (and/or formally verifying the official Vyper compiler).

Initial development for the subset of Vyper covered here was supported by Grant ID FY25-1892 from the Ethereum Foundation's [Ecosystem Support Program](https://esp.ethereum.foundation). The project is active and evolving, with ongoing work to expand coverage and improve the toolchain.

## Contents

This repository contains a _formal_ and _executable_ definition of a subset of the semantics of Vyper, expressed as a _definitional interpreter_ in higher-order logic. This means we have defined an interpreter for Vyper programs as a mathematical function in logic, which can be executed and about which we can also prove theorems.

The work is presented as HOL4 theories: each theory, e.g. `vyperAST`, is implemented in a script file, e.g. `vyperASTScript.sml`.
These script files are intended to be read as a formal specification of Vyper (or at least the subset we have formalised so far), in addition to being executable by the HOL4 theorem prover to build the logical definitions and theories described.

The main function for executing Vyper statements is `eval_stmts` defined in `vyperInterpreter` (specifically `evaluate_def`). Top-level entry points are `load_contract` and `call_external`, defined in the same theory. Examples of calling these functions and executing the interpreter can be found in `vyperTestRunner`, which defines functions such as `run_call` used in evaluating the formal semantics on the Vyper language test suite.

The interpreter operates on abstract syntax (defined in `vyperAST`) and an evaluation state (`evaluation_state`, defined in `vyperState`) representing the mutable EVM state. Top-level entry-points use an `abstract_machine` wrapper (defined in `vyperInterpreter`) that packages the evaluation state with contract source code and other static data.

## Repository Structure

The repository is organised into the following directories:

- **`syntax/`** — Vyper abstract syntax tree definitions
- **`frontend/`** — JSON import and translation into the core AST
- **`semantics/`** — Vyper semantics, organised across several theories covering values and types, value-level operations, storage encoding, ABI encoding, evaluation context and builtins, interpreter state and monad, the definitional interpreter itself, and a CPS/small-step version for efficient execution
  - **`semantics/prop/`** — Properties of the semantics (scope preservation, state preservation, etc.)
- **`tests/`** — Test infrastructure and generated test scripts from the Vyper test suite
- **`lowering/`** — Vyper-to-Venom IR compiler definition and correctness proofs
- **`venom/`** — Venom IR semantics and compiler pass proofs
  - **`venom/passes/`** — Individual compiler passes

We describe the main contents and notable features below.

### Syntax (`syntax/`)

The abstract syntax tree (AST) for Vyper is defined in `vyperAST`. The main datatypes are `expr` for expressions, `stmt` for statements, and `toplevel` for top-level declarations. This definition of Vyper's syntax is intended for use _after_ parsing, type-checking, constant and module inlining, and any other front-end elaboration done to user-written sources. As such, the syntax includes hints used by the interpreter, e.g., the `concat()` builtin is represented syntactically as `Concat n` where `n` is the type-inferrable maximum length of the result.

We syntactically restrict the targets for assignment statements/expressions, using the `assignment_target` type which can be seen as a restriction of the expression syntax to only variables (`x`), subscripting (`x[3]`), and attribute selection (`x.y`) with arbitrary nesting. This in particular also applies to the `append` and `pop` builtin functions on arrays, which are stateful (mutating) operations that we treat as assignments.

Interface declarations (`InterfaceDecl`) are included in the AST, with interface function signatures parsed from JSON and stored in the interpreter's type environment. This enables resolution of external calls to interface-typed targets. Full type-checking of interfaces remains future work (see [#47](https://github.com/verifereum/vyper-hol/issues/47)). Module imports and exports are handled by the JSON frontend/translation layer, and expressions carry `source_id` information to identify which module they belong to.

### Semantics (`semantics/`)

The formal semantics for Vyper is defined across several theories in `semantics/`. The top-level entry-points are `load_contract` (for running a contract-deployment transaction given the Vyper source code of the contract), and `call_external` (for calling an external function of an already-deployed contract). These entry-points use the `eval_stmts` function defined in `evaluate_def` for interpreting Vyper code. These functions operate on Vyper values; see the test infrastructure below for how to wrap these calls with encoding/decoding to ABI-encoded bytes.

`load_contract` is a Vyper-level deployment abstraction rather than a model of the EVM `CREATE` or `CREATE2` instructions. Its transaction supplies the target address directly, and successful deployment installs Vyper sources and exports. In contrast, Verifereum's EVM creation semantics derives the created address, updates creator and created-account nonces, executes init code, and installs runtime bytecode. Relating these two boundaries is an obligation of the Vyper-to-EVM compiler-correctness development. Vyper-level constructor value transfer is not omitted: it uses the ordinary external-function call path, retaining the updated accounts on success and rolling back to the input abstract machine on failure.

The semantics is organised into layers:
- **Values and types** — runtime values (`value`), type representations (`type_value`), and operations on values such as arithmetic, comparisons, conversions, and array manipulation.
- **Storage** — encoding and decoding of Vyper values to/from EVM storage slots, and hashmap slot computation using Keccak256.
- **ABI** — conversions between Vyper types and the standard [Contract ABI](https://docs.soliditylang.org/en/latest/abi-spec.html) encoding, used for encoding/decoding call data and return values. This defers to the ABI encoder/decoder in Verifereum for conversions to/from raw bytes.
- **Evaluation context** — the non-stateful environment for the interpreter, containing the transaction information, source code of existing contracts, and semantics for builtins that depend on this context (e.g., `msg.sender`, `block.number`, `ecrecover`).
- **Interpreter state** — the stateful machinery for the interpreter, including a state-exception monad, the mutable state (EVM accounts, variable scopes, immutables, logs, transient storage), and operations for reading/writing storage, variables, and globals. Assignment to nested targets (e.g., `x[3].n = 9`) is also handled at this level.
- **Interpreter** — the main definitional interpreter (`evaluate_def`), function lookup and calling conventions, the termination proof, and the top-level entry-points.
- **Type checking** — partial type-checking definitions (`vyperTypeCheck`), including `satisfies_type`, `well_typed_expr`, and related predicates.

The interpreter is written in a state-exception monad. Exceptions are used for semantic errors (e.g., looking up a variable that was not bound), legitimate runtime exceptions (e.g., failed assertions), and control flow for internal function calls and loops (`return`, `break`, `continue`).

Termination is proved for the interpreter, validating Vyper's design as a total language (this does not rely on gas consumption, which is invisible at the Vyper source level). The termination argument uses the facts that internal function calls cannot recurse (even indirectly) and that all loops have an explicit (syntactic) bound.

External calls (`staticcall` and `extcall`) are implemented by deferring to the low-level EVM execution defined in Verifereum. This makes termination straightforward since the interpreter is not recursive for external calls; termination depends on gas consumption (and this being sufficient has already been proven in Verifereum). The interpreter also supports module imports, with internal function calls across modules tracked via `source_id`, and `@deploy` functions callable during contract deployment.

A continuation-passing (small-step) version of the interpreter is also defined and proved equivalent to the big-step version. Its main purpose is to facilitate efficient execution via HOL4's `cv_compute` mechanism.

Properties of the semantics — such as scope preservation and state preservation — are proved in `semantics/prop/`.

### Tests (`tests/`)

The test infrastructure defines functions for re-running execution traces from the Vyper test suite using the definitional interpreter. The main entry-point is the `run_test` function defined in `vyperTestRunner`. Machinery for decoding exported JSON test files is defined in the `vyperTestLib` library; the generated test scripts are in `tests/generated/`.

The decoding of JSON into our AST type is somewhat ad-hoc, in part because the JSON format is not fully specified. In future work, we might formalise more of the front-end or elaboration process, including parsing and type-checking, so that we can run source code directly. For now, we rely on an external front-end (e.g., as used in Vyper's test export process) and decode its output to construct terms in our formal syntax.

## Current Limitations

The formal semantics covers the core Vyper language including external calls (`staticcall`, `extcall`), reentrancy protection (`@nonreentrant`), `raw_call`, contract creation builtins, transient storage, and module imports. The main limitation is the **front-end**: there is no formal parser (we operate on abstract syntax exported as JSON, [#46](https://github.com/verifereum/vyper-hol/issues/46)) and type-checking is partial ([#47](https://github.com/verifereum/vyper-hol/issues/47)). A small number of minor features remain unimplemented, including `print` and gas modelling for `msg.gas`/`msg.mana` and external call gas limits ([#98](https://github.com/verifereum/vyper-hol/issues/98)).

## Outcomes and Next Steps

The main outcomes of this work so far are:
- We have defined a formal executable specification of a subset of Vyper in higher-order logic,
- which passes the `functional/codegen` section of the Vyper language test suite, modulo the minor exclusions listed above.

Passing a substantial portion of the official test suite means our formal semantics is a solid foundation for future work on formal verification for Vyper including both proving properties about the language and producing a verified compiler and other verified tools. In addition to the test executions, we have proved a number of properties about the semantics, including totality of the language (the interpreter always terminates), scope and state preservation properties for the evaluator (in `semantics/prop/`), and correctness proofs for several Venom IR compiler passes (in `venom/passes/`). The `lowering/` directory contains a Vyper-to-Venom IR compiler definition with end-to-end correctness proofs in progress.

It should also be noted that the export of the test suite in a format consumable by others was motivated in part by this project.

Next steps include formalising the front-end (parsing and full type-checking), proving safety properties about the language ([#90](https://github.com/verifereum/vyper-hol/issues/90)), and continuing work on verifying the Vyper compiler. For a live roadmap and current tasks, see the [issue tracker](https://github.com/verifereum/vyper-hol/issues).

## Dependencies and How to Run

This work is developed in the [HOL4 theorem prover](https://hol-theorem-prover.org), and makes use of the Ethereum Virtual Machine (EVM) formalisation in the [Verifereum](https://verifereum.org) project, and the test suite for the [Vyper language](https://vyperlang.org) from [its repository](https://github.com/vyperlang/vyper).

The project is built with [`holbuild`](https://github.com/charles-cooper/holbuild). The repository's `holproject.toml` is the source of truth for the project configuration and pinned HOL dependencies, including the compatible [Verifereum](https://github.com/verifereum/verifereum) revision. Vyper functional tests are generated from the upstream commit pinned in [`VYPER_PIN`](VYPER_PIN). The CI workflow (`.github/workflows/holbuild.yml`) is the recommended reference for the exact automated build.

For a local build, install `holbuild` v0.10.0 or newer and run:

```bash
holbuild buildhol
holbuild -j"$(nproc)" build
```

`holbuild buildhol` builds and caches the HOL toolchain and project dependencies specified by `holproject.toml`.

Release instructions, including the prebuilt holbuild archive artefact, are in [docs/release.md](docs/release.md).

### Running the Vyper test suite

The test runner expects exported JSON fixtures to be available at `tests/vyper-test-exports`. To generate them locally, clone and install Vyper, then export the functional tests:

```bash
git clone --depth 1 https://github.com/vyperlang/vyper.git vyper-src
cd vyper-src
git fetch --unshallow --tags
git checkout --detach "$(tr -d '[:space:]' < ../VYPER_PIN)"
pip install . --group test
pytest -s -n0 --export ../tests/vyper-test-exports -m "not fuzzing" tests/functional
```

The checkout command reads the repository's authoritative `VYPER_PIN`; keep it
before installation and export so the installed compiler and generated fixtures
come from the pinned revision.

Then run individual generated test theories with `holbuild`, for example:

```bash
holbuild -j"$(nproc)" build vyperTest_functional_builtins_codegen_test_abi_decodeTheory
```

The CI workflow runs the generated tests in parallel groups; see `.github/workflows/holbuild.yml` for that full setup.
