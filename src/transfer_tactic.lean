import complements.filter_product
import tactic
import tactic.interactive
import data.real.hyperreal

open tactic expr

namespace tactic

meta def transfer_step_one_aux (tgt : expr) (new_vars : list expr) : tactic (list expr) :=
do  `(%%lhs ↔ %%rhs) ← (return tgt) | fail "Goal is not an equivalence (step 1)",
    match rhs with
    | `(∀ _ : (filter.germ %%l %%α), _) := 
      do  `(filter %%ι) ← infer_type l,
          e ← to_expr ``(filter.germ.forall_iff_forall_lift_pred %%l),
          rewrite_target e,
          return new_vars
    | `(∃ _ : (filter.germ %%l %%α), _) := 
      do  `(filter %%ι) ← infer_type l,
          e ← to_expr ``(filter.germ.exists_iff_exists_lift_pred %%l),
          rewrite_target e,
          return new_vars
    | _ := fail "No known pattern applicable (step 1)"
    end

meta def transfer_step_two_aux (tgt : expr) (new_vars : list expr) : tactic (list expr) :=
do  `(%%lhs ↔ %%rhs) ← (return tgt) | fail "Goal is not an equivalence (step 2)",
    match lhs with
    | `(∀ _, _) := 
      do  some (name, _, _) ← get_binder none tt lhs,
          name ← get_unused_name name,
          refine ``(forall_congr _),
          new_var ← intro name,
          return (new_var :: new_vars)
    | _ := fail "No known pattern applicable (step 2)"
    end

meta def transfer_step_three_aux (tgt : expr) (new_vars : list expr) : tactic (list expr) :=
do  `(filter.germ.lift_pred %%p %%x ↔ %%rhs) ← (return tgt) | fail "Goal is not an equivalence (step 3)",
    match p with
    | `(λ _, ∀ y, %%q) := 
      do  e ← to_expr ``(filter.germ.lift_pred_forall_iff_forall_lift_pred'),
          rewrite_target e,
          return new_vars
    | _ := fail "No known pattern applicable (step 3)"
    end

meta def transfer_step_four_aux (tgt : expr) (new_vars : list expr) : tactic unit :=
do  new_vars.mmap' (λ x, do { refine ``((%%x).induction_on _), name ← get_unused_name, intro name }),
    reflexivity

namespace interactive

setup_tactic_parser

meta def transfer_step_one : tactic unit :=
do  tgt ← target,
    transfer_step_one_aux tgt [],
    skip

meta def transfer_step_two : tactic unit :=
do  tgt ← target,
    transfer_step_two_aux tgt [],
    skip

meta def transfer_step_three : tactic unit :=
do  tgt ← target,
    transfer_step_three_aux tgt [],
    skip

meta def transfer_step_four : tactic unit :=
do  tgt ← target,
    transfer_step_four_aux tgt []

end interactive

#check `[rw filter.germ.forall_iff_forall_lift_pred]

example (α ι : Type*) [preorder α] (l : ultrafilter ι) (a : α) : 
  (∀ x, a ≤ x) ↔ (∀ x : (l : filter ι).germ α, ↑a ≤ x) :=
begin
  transfer_step_one,
  transfer_step_two,
  transfer_step_four,
end

example (α ι : Type*) [preorder α] (l : ultrafilter ι) (a : α) : 
  (∀ x y : α, x = y) ↔ (∀ x y : (l : filter ι).germ α, x = y) :=
begin
  transfer_step_one,
  transfer_step_two,
  transfer_step_three,
  transfer_step_two,
  transfer_step_four,
end

end tactic