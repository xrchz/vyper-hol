(*
 * Conservative syntactic FMP reclaim analysis.
 *
 * Pinned-upstream comparison boundary: the reclaim logic in the pinned
 * Vyper Venom FMP-lowering pass (vyper/venom/passes/*; see VYPER_PIN) uses
 * Python analysis/provenance objects which are not represented by the HOL
 * instruction record.  This theory therefore exposes an intentional
 * abstraction, not an exact-parity claim, and accepts no cached external
 * liveness, DFG, or reclaim map.
 *
 * Syntactic use classification frozen for this abstraction:
 *   - a well-shaped DALLOCA with exactly one output creates a LIFO mark;
 *   - an exact base variable used only in an explicitly recognized memory
 *     address position is a direct admissible use;
 *   - PHI, ASSIGN, arithmetic/derived-pointer, or any otherwise unclassified
 *     use pins the mark;
 *   - storing the base as a value or passing it to call-like code captures it;
 *   - returning, invoking, or otherwise publishing the base escapes it.
 * Unknown or overlapping cases take the strongest conservative veto.  The
 * executable definitions below make each category explicit so fixtures can
 * test the boundary independently.
 *)

Theory fmpReclaimDefs
Ancestors
  fmpAnalysisDefs
  livenessDefs
  cfgDefs
  arithmetic
  finite_map

val _ = export_theory();
