# Compiler definition parity

This document tracks whether the HOL compiler definitions correspond to the Python compiler pinned for the whole repository.

## Authoritative upstream revision

The sole source of truth is [`../VYPER_PIN`](../VYPER_PIN). Read the live revision from that file; it must not be duplicated here.

The same pin is to be used for:

- compiler-definition parity;
- Vyper language-test exports;
- generated AST JSON and compiler metadata;
- bytecode and other compiler fixtures;
- downstream tools which consume Python Vyper output.

Do not introduce independent component pins. Source-file annotations may identify a historical port commit for provenance, but parity claims must always be made against `VYPER_PIN`. New or updated annotations should normally name the relevant Python source path and symbol instead of repeating a commit hash.

## Formal compiler boundary

The current expected boundary is an elaborated HOL AST plus metadata ordinarily produced by Python frontend and semantic-analysis phases. Parsing raw source is not part of the first compiler-correctness theorem.

The parity audit must determine, for every item of metadata, whether it is:

1. formally computed in HOL;
2. supplied under a proved relation to elaborated frontend output; or
3. trusted as an explicit theorem input.

Important boundary items include module/import resolution, type information, storage and immutable layouts, selectors, entry-point information, function IDs and reachability, dispatch metadata, compiler settings, and EVM version.

See [`compiler-correctness-specification.md`](compiler-correctness-specification.md) for the intended theorem boundary.

## Status vocabulary

- **unknown** — not yet audited against `VYPER_PIN`.
- **matches** — audited and behaviorally matches the pinned Python definition.
- **representation-equivalent** — differs structurally but has a stated correspondence preserving relevant behavior.
- **intentional abstraction** — intentionally differs; the abstraction and its proof boundary are documented.
- **needs update** — HOL behavior differs and should be changed.
- **missing in HOL** — pinned compiler functionality has no formal counterpart on the selected path.
- **HOL-only proof adaptation** — formal-only machinery with no direct Python counterpart.
- **out of theorem scope** — deliberately outside the stated compiler theorem boundary.
- **blocked** — cannot classify until a boundary or semantic decision is made.

## Historical anchors currently recorded

These are provenance notes, not target revisions.

| HOL area/file | Recorded historical anchor | Parity status |
|---|---|---|
| `lowering/defs/exprLoweringScript.sml` | `6a3248028` | unknown |
| `lowering/defs/contextScript.sml` | `e1dead045` | unknown |
| `lowering/defs/vyperCompilerScript.sml` | `a7f7bf133` | unknown |
| `lowering/defs/selectorDispatchScript.sml` | `a7f7bf133` | unknown |
| `lowering/vyperLoweringCorrectScript.sml` | `a7f7bf133` | unknown |
| `venom/compiler/venomPipelineScript.sml` | `a7f7bf133` | unknown |
| `venom/codegen/defs/*` | mostly `e1dead045` | unknown |

The pinned compiler has evolved materially since these anchors. In particular, the pinned O2 pipeline includes additional or changed memory/FMP passes and pass ordering. No historical anchor should be treated as evidence of current parity.

## Correspondence matrix

The matrix should eventually identify exact Python modules, classes, and functions rather than broad source areas. All entries on the first end-to-end path must be classified before the parity milestone closes.

### Frontend/compiler boundary

| Input or phase | HOL representation | Status | Audit question |
|---|---|---|---|
| Parsed and elaborated AST | `vyperAST` and JSON frontend | unknown | Which elaboration facts are assumed? |
| Type metadata | AST/type-related fields and environments | unknown | Is Python semantic-analysis output represented completely? |
| Module/import resolution | module/source-id structures | unknown | Formal computation or trusted input? |
| Storage layout | compile environment/module inputs | unknown | How is it related to Python layout generation? |
| Immutable layout | compile environment/module inputs | unknown | Formal computation or supplied metadata? |
| Function IDs/reachability | module-lowering inputs | unknown | Python computes these from analysed module metadata. |
| Selectors/entry metadata | selector and entry inputs | unknown | Current HOL top-level lowering accepts pre-extracted data. |
| Compiler settings/EVM version | pipeline/codegen parameters | unknown | Must be fixed explicitly in theorem inputs. |

### Lowering definitions

| HOL file/area | Pinned Python source area | Status | Notes |
|---|---|---|---|
| `lowering/defs/compileEnvScript.sml` | `vyper/codegen_venom/context.py`, related compiler metadata | unknown | Environment/state fields and layout inputs. |
| `lowering/defs/contextScript.sml` | `vyper/codegen_venom/context.py`, `buffer.py`, `value.py` | unknown | Memory/storage/context and pointer behavior. |
| `lowering/defs/emitHelperScript.sml` | Venom builder/emission APIs | unknown | Fresh IDs, labels, blocks, and emission conventions. |
| `lowering/defs/exprLoweringScript.sml` | `vyper/codegen_venom/expr.py`, `arithmetic.py` | unknown | High priority; includes evaluation and calling conventions. |
| `lowering/defs/stmtLoweringScript.sml` | `vyper/codegen_venom/stmt.py` | unknown | Assignment order, control flow, return/assert/loop behavior. |
| `lowering/defs/abiEncoderScript.sml` | `vyper/codegen_venom/abi/*` | unknown | Static/dynamic encode/decode and buffer management. |
| `lowering/defs/builtin*.sml` | `vyper/codegen_venom/builtins/*` | unknown | Calls, create, conversion, ABI, bytes, math, and system builtins. |
| `lowering/defs/selectorDispatchScript.sml` | `vyper/codegen_venom/module.py`, jump-table helpers | unknown | Linear/sparse dispatch and default arguments. |
| `lowering/defs/moduleLoweringScript.sml` | `vyper/codegen_venom/module.py` | unknown | Reachability, runtime/deploy generation, metadata, and data sections. |
| `lowering/defs/vyperCompilerScript.sml` | public Venom compiler entry path | blocked | HOL currently accepts metadata rather than deriving it from a module. Boundary decision required. |

### Venom IR and semantics

| HOL file/area | Pinned Python source area | Status | Notes |
|---|---|---|---|
| Venom instructions/operands | `vyper/venom/basicblock.py` | unknown | Check opcodes, operand order, outputs, labels, and effects. |
| Functions and contexts | `vyper/venom/function.py`, `context.py` | unknown | Entry, parameters, internal calls, and data. |
| Builder conventions | `vyper/venom/builder.py` | unknown | Freshness and block construction. |
| Memory/allocation model | `vyper/venom/memory_allocator.py`, `memory_location.py` | unknown | Relate Python compile-time locations to HOL runtime allocation semantics. |
| CFG analysis | `vyper/venom/analysis/cfg.py` | partially reviewed | See [`cfg_analysis_parity.md`](cfg_analysis_parity.md); revalidate against pin. |
| Other analyses | `vyper/venom/analysis/*` | unknown | Audit those used by the mandatory pipeline first. |
| Conservative FMP reclaim analysis (`venom/analysis/fmp/defs/fmpReclaimDefsScript.sml`, `venom/analysis/fmp/proofs/fmpReclaimPropsScript.sml`) | `vyper/venom/passes/fmp_lowering.py:FmpLoweringPass` reclaim behavior | intentional abstraction | HOL recomputes from the current context and structurally checks every emitted restore target, but conservatively vetoes alias, provenance, capture, and escape cases represented by richer Python analysis objects. Empty or no-target plans are conservative outcomes, not evidence of parity. |

### Pipeline and pass definitions

| HOL file/area | Pinned Python source area | Status | Notes |
|---|---|---|---|
| `venom/compiler/venomPipelineScript.sml` | `vyper/venom/optimization_levels/*`, compiler pipeline entry | needs update | Existing comments explicitly omit `mem_merge`; pinned pipelines include additional memory/FMP passes and changed ordering. |
| Minimal mandatory pipeline | compiler/codegen entry path | missing in HOL | Must be identified and named independently of O2/O3/Os. |
| Individual pass definitions | `vyper/venom/passes/*` | unknown | Audit mandatory passes first. |
| O2 configuration | `vyper/venom/optimization_levels/O2.py` | needs update | Current pinned pass list differs from existing HOL O2 definition. |
| O3 configuration | `vyper/venom/optimization_levels/O3.py` | unknown | Optional for first e2e theorem. |
| Os configuration | `vyper/venom/optimization_levels/Os.py` | unknown | Optional for first e2e theorem. |
| Pass-order constraints | pass classes and `pass_order.py` | missing/unknown | Determine whether constraints need formal counterparts or only pipeline evidence. |

### Codegen definitions

| HOL file | Pinned Python source area | Status | Notes |
|---|---|---|---|
| `venom/codegen/defs/stackModelScript.sml` | Venom stack model/code generation | unknown | Stack order and value conventions. |
| `venom/codegen/defs/stackPlanTypesScript.sml` | stack-plan state/types | unknown | Spill allocator, function frames, labels. |
| `venom/codegen/defs/stackPlanOpsScript.sml` | reorder/spill/dup/swap logic | unknown | Recheck historical operand-order issue. |
| `venom/codegen/defs/stackPlanGenScript.sml` | Venom-to-assembly generation | unknown | Parameters, PHIs, calls, returns, stack depth. |
| `venom/codegen/defs/planExecScript.sml` | stack operation to assembly emission | unknown | Opcode emission and pseudo-operations. |
| `venom/codegen/defs/asmIRScript.sml` | Python assembly representation | unknown | Labels, data sections, calls, and metadata. |
| `venom/codegen/defs/asmSemScript.sml` | no necessarily exact Python counterpart | blocked | Decide intended abstraction, especially for nested calls. |
| `venom/codegen/defs/symbolResolveScript.sml` | assembly/symbol resolution | unknown | Label sizes, offsets, data addressing. |
| `venom/codegen/defs/codegenScript.sml` | top-level assembly/bytecode path | unknown | Runtime/deploy data and metadata behavior. |

### Fixtures

| HOL file/area | Purpose | Status | Notes |
|---|---|---|---|
| `lowering/defs/evalCompilerScript.sml` | compiler smoke fixtures | unknown | Regenerate only after parity updates are understood. |
| `lowering/defs/evalCompilerBytecodeScript.sml` | fresh HOL-to-Python bytecode parity test | failing: 17 bytecode mismatches, 6 checked-guard rejections | Every EVAL theorem requires exact equality with the independent Python oracle. No HOL-generated `.hex` outputs are committed. The four loops fail the current PHI-dominance guard, and two internal calls fail FMP input arity because their return PC is still lowered as `PARAM`. |
| `lowering/defs/python-o1-bytecode-fixtures`, `python_o1_bytecode_oracle.py`, and `bytecode/python-o1-no-asm-opt*/` | independently generated pinned-Python O1 bytecode oracle and comparison entrypoint | reproducible from pin | The generator verifies the clean checkout against `VYPER_PIN` and compiles tracked sources in a locked, isolated environment with the pinned `PASSES_O1` lowering pipeline, Prague, metadata disabled, and final assembly optimization disabled to match HOL's identity finalizer. CI reproduces the Python oracle with `--check`; `--compare-hol` performs fresh HOL evaluation against it and exits nonzero on the current discrepancies. |
| `tests/vyper-test-exports` and generators | language-test AST/metadata export | uses repository pin by policy | Keep aligned with `VYPER_PIN`. |

## Audit workflow

1. Read the target revision from `VYPER_PIN` and verify the comparison checkout corresponds to it.
2. Fix the formal boundary and compiler settings for the first theorem.
3. For each matrix entry, compare the HOL definition with the exact pinned Python symbol.
4. Record representational correspondences and intentional abstractions explicitly.
5. Mark behavioral differences as definition updates rather than attempting to prove stale definitions correct.
6. Identify theorem statements invalidated by each update.
7. Determine the minimal mandatory pre-codegen pipeline.
8. Update executable fixtures after definition changes, without treating fixture agreement as a proof.
9. Close all entries on the first e2e path before declaring parity complete.

## Open parity decisions

- What precise elaborated metadata belongs to the trusted compiler-input boundary?
- Should HOL compute module reachability, selectors, and dispatch data or relate supplied values to frontend output?
- What pinned compiler setting gives the smallest valid pre-codegen pipeline?
- Which passes are mandatory even when optional optimization is disabled?
- How should assembly semantics represent or abstract nested EVM calls?
- What bytecode metadata policy is part of the first deployment theorem?
- Which HOL simplifications are intentional abstractions rather than missing compiler functionality?
