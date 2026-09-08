# Eval Compiler Bytecode Fixtures

Each `.hex` file contains the exact deploy and runtime bytecode expected from
`compile_vyper` for one evaluator test program.

The fixture format is:

```text
deploy=<hex bytes>
runtime=<hex bytes>
```

Blank lines and `#` comments are ignored by `evalCompilerBytecodeLib`.
