# Contract checker evaluator

The contract checker evaluator computes the logical `check_contract` function
on closed inputs and returns a theorem produced by the HOL kernel. It is useful
for validating translated Vyper contracts without adding a new theorem or
proof script for each contract.

The implementation is split into three libraries:

- `semantics/vyperCheckContractLib` is the JSON-independent core.
- `frontend/vyperCheckContractFrontendLib` translates compiler JSON or already
  decoded frontend terms before invoking the core.
- `tests/vyperCheckContractTraceLib` adapts a `deployment_trace` from the Vyper
  test runner. It is under `tests/` because it depends on test infrastructure.

## Result and failure behavior

A successful call returns a hypothesis-free theorem of the form

```text
check_contract in_deploy layouts address modules = SOME artifact
```

The library verifies that the theorem has the expected left-hand side, no
assumptions, a concrete `SOME` result, and a closed artifact. The theorem, not
an unchecked ML value, is the evidence for the result.

The API fails closed. It raises an ML exception if an input contains free
variables, computation is partial, the logical checker returns `NONE`, the
conversion produces assumptions or an unexpected theorem shape, or the
artifact is open. `check_contract_conv` can be used directly when a caller
needs to inspect a computed rejection theorem ending in `NONE`.

`in_deploy` is an ML `bool`; the library constructs the corresponding HOL
Boolean internally. Use `true` when checking the deployment context and
`false` for the runtime context.

## Direct logical-term API

Load `vyperCheckContractLib` and supply closed HOL terms of the types expected
by `vyperTypeContractTheory.check_contract`:

```sml
Theory checkerExample
Ancestors
  vyperTypeContract
Libs
  vyperCheckContractLib

val layouts =
  ``([] : (address # (storage_layout # storage_layout)) list)``;
val modules =
  ``([(NONE, [])] : (num option # toplevel list) list)``;
val address = ``(0w : address)``;

val checked = vyperCheckContractLib.check_contract
  {in_deploy = false,
   layouts = layouts,
   address = address,
   modules = modules};
```

The lower-level operations are:

- `mk_check_contract`: construct and validate the closed application term;
- `check_contract_conv`: compute an application, including a result of `NONE`;
- `check_contract_with`: use a caller-supplied conversion while retaining all
  success-result validation;
- `check_contract`: use the standard static checker conversion.

## Static compset and extension

`check_contract_compset` is an eager, sealed, explicitly curated compset. It
does not inherit the ambient `"compute"` theorem set or simplifier state. Its
behavior therefore does not depend on unrelated theories loaded by a caller.

Callers can functionally copy and extend it without changing the shared value:

```sml
val extended_compset =
  vyperCheckContractLib.check_contract_compset
  |> computeLib.copy
  |> computeLib.add_thms [my_checker_computation_rule];

val extended_conv = computeLib.CBV_CONV extended_compset;
val checked = vyperCheckContractLib.check_contract_with extended_conv input;
```

Rules added this way must be trusted kernel theorems. A local extension is
preferable to changing the shared compset for contract-specific definitions;
the shared compset should contain only dependencies of the general checker.

## Compiler frontend API

`vyperCheckContractFrontendLib` accepts the compiler's annotated AST and
storage layout as already decoded HOL terms:

```sml
val input =
  {in_deploy = false,
   address = ``(0w : address)``,
   annotated_ast = annotated_ast_term,
   storage_layout = storage_layout_term};

val checked = vyperCheckContractFrontendLib.check_contract input;
```

For a JSON file containing both objects, use:

```sml
val checked = vyperCheckContractFrontendLib.check_contract_file
  {in_deploy = false,
   address = ``(0w : address)``,
   path = "contract.json"};
```

The frontend uses the shared canonical AST translation and storage-layout
extraction. Interface (`.vyi`) units remain available during translation for
nominal types and signatures but are excluded from the runtime module list.

Call `check_contract_result` when the caller also needs the prepared terms:

```sml
val result = vyperCheckContractFrontendLib.check_contract_result input;
val theorem = #theorem result;
val artifact = #artifact result;
val modules = #modules result;
val layouts = #layouts result;
```

The artifact and projections in `checked_result` are extracted only after the
same theorem validation performed by the convenience API.

`prepare_check_input` performs translation without checking.
`prepare_translated_input` accepts the already translated `sources` and
`import_map` terms and is useful to adapters that do not start with raw JSON.

## Deployment traces

Given a closed HOL `deployment_trace` record produced by the test runner:

```sml
val checked =
  vyperCheckContractTraceLib.check_deployment_trace deployment_trace_term;
```

The adapter extracts `deployedAddress`, `sourceAst`, `importMap`, and
`storageLayout`, prepares a frontend input with `in_deploy = true`, and invokes
the core checker. `prepare_deployment_trace` returns the prepared core input
without evaluating it.

This adapter is intentionally not a dependency of the core or frontend
libraries.

## Compiler JSON fixtures

A committed compiler fixture should be reproducible with the exact Vyper
revision in `VYPER_PIN`. Keep the corresponding source and a provenance note.
Compiler invocations that emit `annotated_ast` and `layout` produce two JSON
objects; merge them into one object with the top-level keys expected by the
frontend.

Before committing generated JSON, replace compiler `resolved_path` values with
stable fixture-relative paths. For imports, preserve relative directory
structure and rewrite every occurrence consistently so canonical source
identity is unchanged. Reject generated output that still contains the local
checkout root, `/home/`, `/tmp/`, or the generating username.

The Flex Daddy example and its exact provenance are in
`tests/fixtures/check_contract/third_party/flex/`. It is checked in both
runtime and deployment modes by
`frontend/vyperCheckContractFrontendLibTestScript.sml`.
