# O1 bytecode fixtures

This directory contains the independent Python oracle. No HOL-generated
expected bytecode is retained alongside it.

## Independent oracle

`python-o1-no-asm-opt-sources/` contains 23 Vyper source counterparts to the
HOL AST programs in `../evalCompilerScript.sml`. `python-o1-no-asm-opt/`
contains bytecode produced from those sources by pinned Python Vyper commit
`cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`, read from `../../../VYPER_PIN`.
These files are the independent parity oracle. Its generated `provenance.json`
records the full compiler revision, relevant tool/runtime/dependency versions,
settings, SHA-256 hashes of
every source and bytecode payload, and an audit-anchor hash of the HOL program
definitions. The HOL file is hashed only to detect correspondence drift; it is
not an input to Python compilation.

The oracle profile exactly matches the current HOL fixture boundary:

```text
experimental codegen:       enabled
Venom IR pipeline:           O1 lowering-only passes
final assembly optimization: disabled (matching HOL finalizer K SOME)
EVM version:                 prague
bytecode metadata:           disabled
outputs:                     bytecode, bytecode_runtime
```

At the pinned revision, Python Vyper's `OptimizationLevel.NONE` and
`OptimizationLevel.O1` are explicitly mapped to the same `PASSES_O1` Venom
pipeline; `NONE` alone disables the final assembly optimizer. The generator
checks that those pass lists are equal before compiling. Thus differences from
HOL are not caused merely by comparing HOL's identity finalizer with Python's
assembly optimizer.

No HOL definition, evaluator, or `.hex` output participates in oracle bytecode
generation. The generator checks the Vyper checkout's full Git revision,
requires a clean checkout, clones only its committed objects into a temporary
directory, and installs that clone into an isolated uv-managed Python 3.11.11
environment using the dependency versions in
`../python-o1-oracle-constraints.txt`. A fixed setuptools-scm version string
makes package construction independent of local Git tags. Python isolated mode
and a cleared Python environment prevent module-path shadowing; the helper also
checks the imported compiler's location and reported commit before invoking it.
Generation requires `uv 0.10.11`, the version pinned in CI.

Given a clean Vyper checkout, reproduce the committed oracle without modifying
it:

```sh
sh lowering/defs/python-o1-bytecode-fixtures --check \
  --vyper-repo /path/to/vyper
```

Update the oracle only from that independently verified compiler:

```sh
sh lowering/defs/python-o1-bytecode-fixtures --update \
  --vyper-repo /path/to/vyper
```

The underlying compiler settings are implemented explicitly in
`../python_o1_bytecode_oracle.py` and correspond to this pinned CLI invocation:

```sh
vyper -f bytecode,bytecode_runtime \
  --experimental-codegen --disable-optimize --evm-version prague \
  --disable-bytecode-metadata <source.vy>
```

## HOL comparison

No HOL-generated `.hex` files are committed. `evalCompilerBytecodeLib.sml`
reads the independent Python oracle directly, and every theorem in
`evalCompilerBytecodeScript.sml` requires fresh evaluation of

```sml
compile_vyper (K SOME) (o1_policy prague_capabilities) <program>
```

to equal the corresponding Python deploy/runtime pair. `K SOME` is an identity
finalizer. The independent Python profile uses the same O1 Venom pass list while
disabling final assembly optimization, so the comparison is like-for-like at
this compiler boundary.

Run the complete comparison with:

```sh
sh lowering/defs/python-o1-bytecode-fixtures --compare-hol \
  --vyper-repo /path/to/vyper
```

This first reproduces the Python oracle from `VYPER_PIN`, then runs `holbuild`
with `evalCompilerBytecodeScript.sml` enabled by the `bytecode-parity` root group
in `holproject.toml`. Any bytecode difference or HOL `NONE` result fails the
command. There is no implementation-derived fallback expected output.

The parity test currently fails: 17 HOL bytecode pairs differ from Python, and
four loop plus two internal-call programs return `NONE` while Python emits
bytecode. The theory comments identify the precise checked guards responsible
for the six `NONE` results. These failures must be fixed in the implementation,
not accepted by regenerating expected output from HOL.

## Fixture format

Oracle files use canonical lowercase, even-length hexadecimal:

```text
deploy=<hex bytes>
runtime=<hex bytes>
```

There is no `0x` prefix. Blank lines and `#` comments are accepted by the HOL
oracle fixture reader.
