(*
 * Stack Plan Operations
 *
 * Upstream: vyperlang/vyper@e1dead045 (sunset GEP, #4895)
 * Swap/dup with spilling, reorder, popmany.
 * Port of StackSpiller + _stack_reorder from venom_to_assembly.py.
 *
 * TOP-LEVEL:
 *   do_swap, do_dup           — swap/dup with deep-stack spill handling
 *   do_spill_at, do_restore   — explicit spill/restore
 *   reorder_plan              — arrange operands on stack
 *   popmany_plan              — pop a set of variables
 *)

Theory stackPlanOps
Ancestors
  stackPlanTypes dfgDefs sorting

(* ===== Basic Spill/Restore Operations ===== *)

(* Spill TOS to a fresh memory slot *)
Definition do_spill_tos_def:
  do_spill_tos ps =
    let (off, alloc') = alloc_spill_slot ps.ps_alloc in
    let op = stack_peek 0 ps.ps_stack in
    ([SOSpill off],
     ps with <| ps_stack := stack_pop 1 ps.ps_stack;
                ps_spilled := ps.ps_spilled |+ (op, off);
                ps_alloc := alloc' |>)
End

(* Spill operand at distance dist from TOS *)
Definition do_spill_at_def:
  do_spill_at dist ps =
    if dist = 0 then do_spill_tos ps
    else
      let ps' = ps with ps_stack := stack_swap dist ps.ps_stack in
      let (spill_ops, ps'') = do_spill_tos ps' in
      ([SOSwap dist] ++ spill_ops, ps'')
End

(* Restore a spilled operand from memory *)
Definition do_restore_def:
  do_restore op ps =
    case FLOOKUP ps.ps_spilled op of
      NONE => ([] : stack_op list, ps)
    | SOME off =>
        let alloc' = free_spill_slot off ps.ps_alloc in
        ([SORestore off],
         ps with <| ps_stack := stack_push op ps.ps_stack;
                    ps_spilled := ps.ps_spilled \\ op;
                    ps_alloc := alloc' |>)
End

(* ===== Swap/Dup with Deep Stack Support ===== *)

(* Get top N items from stack (TOS first) *)
Definition top_n_def:
  top_n n stk = REVERSE (TAKE n (REVERSE stk))
End

(* Swap at distance from TOS (0-based). Returns (ops, updated state).
   dist=0: noop. dist 1..16: SWAP{dist}. dist>16: bulk spill/restore.
   EVM SWAPn swaps position 0 with position n. *)
Definition do_swap_def:
  do_swap dist ps =
    if dist = 0 then ([] : stack_op list, ps)
    else if dist ≤ 16 then
      ([SOSwap dist],
       ps with ps_stack := stack_swap dist ps.ps_stack)
    else
      let chunk = dist + 1 in
      let items = top_n chunk ps.ps_stack in
      (* Spill chunk items *)
      let (spill_ops, offsets, alloc') =
        FOLDL (λ(ops, offs, al) item.
          let (off, al') = alloc_spill_slot al in
          (ops ++ [SOSpill off], SNOC off offs, al'))
        ([], [] : num list, ps.ps_alloc) items in
      let base_stack = TAKE (LENGTH ps.ps_stack - chunk) ps.ps_stack in
      (* Desired order (bottom→top): swap first and last, keep middle *)
      let desired = [chunk - 1] ++
        GENLIST (λi. i + 1) (chunk - 2) ++ [0] in
      (* Restore in reverse desired order: last pushed = TOS *)
      let restore_ops =
        MAP (λidx. SORestore (EL idx offsets)) (REVERSE desired) in
      let alloc'' =
        FOLDL (λal off. free_spill_slot off al) alloc' offsets in
      let restored = MAP (λidx. EL idx items) desired in
      (spill_ops ++ restore_ops,
       ps with <| ps_stack := base_stack ++ restored;
                  ps_alloc := alloc'' |>)
End

(* Dup at distance from TOS (0-based). Returns (ops, updated state).
   dist≤15: DUP{dist+1}. dist>15: bulk spill/restore with dup. *)
Definition do_dup_def:
  do_dup dist ps =
    if dist ≤ 15 then
      ([SODup (dist + 1)],
       ps with ps_stack := stack_dup dist ps.ps_stack)
    else
      let chunk = dist + 1 in
      let items = top_n chunk ps.ps_stack in
      let (spill_ops, offsets, alloc') =
        FOLDL (λ(ops, offs, al) item.
          let (off, al') = alloc_spill_slot al in
          (ops ++ [SOSpill off], SNOC off offs, al'))
        ([], [] : num list, ps.ps_alloc) items in
      let base_stack = TAKE (LENGTH ps.ps_stack - chunk) ps.ps_stack in
      (* Desired order (bottom→top): all original ++ [first] (duplicates deepest) *)
      let desired = GENLIST I chunk ++ [0] in
      (* Restore in reverse desired order: last pushed = TOS *)
      let restore_ops =
        MAP (λidx. SORestore (EL idx offsets)) (REVERSE desired) in
      (* Free all offsets once — dup has repeated index, don't double-free *)
      let alloc'' =
        FOLDL (λal off. free_spill_slot off al) alloc' offsets in
      let restored = MAP (λidx. EL idx items) desired in
      (spill_ops ++ restore_ops,
       ps with <| ps_stack := base_stack ++ restored;
                  ps_alloc := alloc'' |>)
End

(* ===== Reduce Depth via Selective Spilling ===== *)

Definition select_spill_candidate_def:
  select_spill_candidate stk forbidden target_dist target_len =
    (* max_offset excludes the target position itself; target_len keeps every
       spill below the already-finalized target window. *)
    let max_offset = MIN 16 (MIN (target_dist - 1) (LENGTH stk - 1)) in
    FIND (λoffset.
      target_len ≤ offset ∧
      let item = stack_peek offset stk in
      ¬ MEM item forbidden ∧ is_var_operand item)
    (GENLIST I (max_offset + 1))
End

(* fuel = stack height, guarantees termination *)
Definition reduce_depth_plan_def:
  reduce_depth_plan 0 target_ops target_op f target_len ps =
    ([] : stack_op list, ps) ∧
  reduce_depth_plan (SUC fuel) target_ops target_op f target_len ps =
    if f + 1 < target_len then ([], ps)
    else
      case stack_get_unfixed_depth target_op f target_len ps.ps_stack of
        NONE => ([], ps)
      | SOME dist =>
          if dist ≤ 16 then ([], ps)
          else
            case select_spill_candidate ps.ps_stack target_ops dist target_len of
              NONE => ([], ps)
            | SOME cand_dist =>
                let (spill_ops, ps') = do_spill_at cand_dist ps in
                let (rest_ops, ps'') =
                  reduce_depth_plan fuel target_ops target_op f target_len ps' in
                (spill_ops ++ rest_ops, ps'')
End

(* ===== Stack Reorder ===== *)

(* Reorder one operand to its target position *)
Definition reorder_one_def:
  reorder_one dfg target_ops target_idx op ps =
    let num_ops = LENGTH target_ops in
    let final_dist = num_ops - 1 - target_idx in
    (* Find an unfixed occurrence, or restore a spilled copy at unprotected TOS. *)
    let (restore_ops, ps1) =
      case stack_get_unfixed_depth op final_dist num_ops ps.ps_stack of
        SOME _ => ([] : stack_op list, ps)
      | NONE =>
          (case FLOOKUP ps.ps_spilled op of
            SOME _ => do_restore op ps
          | NONE => ([], ps)) in
    case stack_get_unfixed_depth op final_dist num_ops ps1.ps_stack of
      NONE => (restore_ops, ps1)
    | SOME dist =>
        let (reduce_ops, ps2) =
          if dist > 16
          then reduce_depth_plan (LENGTH ps1.ps_stack) target_ops op
                 final_dist num_ops ps1
          else ([] : stack_op list, ps1) in
        case stack_get_unfixed_depth op final_dist num_ops ps2.ps_stack of
          NONE => (restore_ops ++ reduce_ops, ps2)
        | SOME dist' =>
            if dist' = final_dist then
              (restore_ops ++ reduce_ops, ps2)
            else if final_dist < LENGTH ps2.ps_stack then
              let at_target = stack_peek final_dist ps2.ps_stack in
              if operand_equiv dfg op at_target then
                let ps3 = ps2 with ps_stack :=
                  stack_poke final_dist op
                    (stack_poke dist' at_target ps2.ps_stack) in
                (restore_ops ++ reduce_ops, ps3)
              else
                let (swap1_ops, ps3) = do_swap dist' ps2 in
                let (swap2_ops, ps4) = do_swap final_dist ps3 in
                (restore_ops ++ reduce_ops ++ swap1_ops ++ swap2_ops, ps4)
            else
              let (swap1_ops, ps3) = do_swap dist' ps2 in
              let (swap2_ops, ps4) = do_swap final_dist ps3 in
              (restore_ops ++ reduce_ops ++ swap1_ops ++ swap2_ops, ps4)
End

(* Reorder stack to match target_ops layout *)
Definition reorder_plan_def:
  reorder_plan dfg target_ops ps =
    FOLDL (λ(ops, ps) (idx, op).
      let (step_ops, ps') = reorder_one dfg target_ops idx op ps in
      (ops ++ step_ops, ps'))
    ([] : stack_op list, ps) (MAPi (λi op. (i, op)) target_ops)
End

(* Cost metric for dry-run comparison *)
Definition reorder_cost_def:
  reorder_cost ops =
    LENGTH (FILTER (λop. case op of
      SOSwap _ => T | SOSpill _ => T | SORestore _ => T | _ => F) ops)
End

(* ===== Popmany ===== *)

(* Check if depths form {1, 2, ..., n} (not including TOS=0) *)
Definition is_contiguous_top_def:
  is_contiguous_top (depths : num list) =
    let n = LENGTH depths in
    let sorted = QSORT (λa b. a ≤ b) depths in
    (sorted = GENLIST SUC n) ∧ n ≤ 16
End

(* Individual swap+pop per item, shallowest first *)
Definition popmany_individual_def:
  popmany_individual to_pop ps =
    let sorted = QSORT (λa b.
      case (stack_get_depth a ps.ps_stack,
            stack_get_depth b ps.ps_stack) of
        (SOME da, SOME db) => da ≤ db
      | _ => T) to_pop in
    FOLDL (λ(ops, ps) v.
      case stack_get_depth v ps.ps_stack of
        NONE => (ops, ps)
      | SOME dist =>
          let (swap_ops, ps') =
            if dist = 0 then ([] : stack_op list, ps)
            else do_swap dist ps in
          (ops ++ swap_ops ++ [SOPop 1],
           ps' with ps_stack := stack_pop 1 ps'.ps_stack))
    ([] : stack_op list, ps) sorted
End

Definition popmany_plan_def:
  popmany_plan ([] : operand list) ps = ([] : stack_op list, ps) ∧
  popmany_plan to_pop ps =
    let depths_opt = MAP (λv. stack_get_depth v ps.ps_stack) to_pop in
    if EVERY IS_SOME depths_opt then
      let depths = MAP THE depths_opt in
      if is_contiguous_top depths then
        (* Contiguous: swap deepest to TOS, then bulk pop *)
        let n = LENGTH to_pop in
        let (swap_ops, ps') = do_swap n ps in
        (swap_ops ++ [SOPop n],
         ps' with ps_stack := stack_pop n ps'.ps_stack)
      else popmany_individual to_pop ps
    else popmany_individual to_pop ps
End

(* ===== Release Dead Spills ===== *)

Definition release_dead_spills_def:
  release_dead_spills next_liveness ps =
    let dead = FILTER (λ(op, off).
      case op of Var v => ¬ MEM v next_liveness | _ => T)
      (fmap_to_alist ps.ps_spilled) in
    FOLDL (λps' (op, off).
      ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                  ps_alloc := free_spill_slot off ps'.ps_alloc |>)
    ps dead
End
