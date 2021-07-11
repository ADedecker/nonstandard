import complements.filter_product
import tactic
import tactic.interactive
import data.real.hyperreal

open tactic expr

namespace tactic

section step_one

private meta def forall_rule (l : expr) (α : expr) : tactic unit :=
do  `(filter %%ι) ← infer_type l,
    e ← to_expr ``(filter.germ.forall_iff_forall_lift_pred %%l),
    rewrite_target e

private meta def exists_rule (l : expr) (α : expr) : tactic unit :=
do  `(filter %%ι) ← infer_type l,
    e ← to_expr ``(filter.germ.exists_iff_exists_lift_pred %%l),
    rewrite_target e

meta def transfer_step_one_aux (tgt : expr) : tactic unit :=
do  `(%%lhs ↔ %%rhs) ← (return tgt) | fail "Goal is not an equivalence (step 1)",
    match rhs with
    | `(∀ _ : (filter.germ %%l %%α), _) := forall_rule l α
    | `(∀ _ : ℝ*, _) := forall_rule `(filter.hyperfilter ℕ : filter ℕ) `(ℝ)
    | `(∃ _ : (filter.germ %%l %%α), _) := exists_rule l α
    | `(∃ _ : ℝ*, _) := exists_rule `(filter.hyperfilter ℕ : filter ℕ) `(ℝ)
    | _ := fail "No known pattern applicable (step 1)"
    end

end step_one

section step_two

meta def transfer_step_two_aux (tgt : expr) : tactic unit :=
do  `(%%lhs ↔ %%rhs) ← (return tgt) | fail "Goal is not an equivalence (step 2)",
    match lhs with
    | `(∀ _ : %%t, _) := 
      (do t' ← infer_type t,
          unify t' `(Prop),
          refine ``(imp_congr _ _)) <|>
      (do some (name, _, _) ← get_binder none tt lhs,
          name ← get_unused_name name,
          refine ``(forall_congr _),
          intro name,
          skip)
    | `(∃ _ : %%t, _) := 
      do  --some (name, _, _) ← get_binder none tt lhs, TODO
          name ← get_unused_name,
          refine ``(exists_congr _),
          intro name,
          skip
    | `(_ ∧ _) := 
      do  name ← get_unused_name,
          refine ``(and_congr _ _)
    | _ := fail "No known pattern applicable (step 2)"
    end

end step_two

section step_three

meta def transfer_step_three_aux (tgt : expr) : tactic unit :=
do  `(filter.germ.lift_pred %%p %%x ↔ %%rhs) ← (return tgt) | fail "Goal is not an equivalence (step 3)",
    match p with
    | `(λ _, ∀ y, %%q) := 
      (do e ← to_expr ``(filter.germ.lift_pred_forall_iff_forall_lift_pred'),
          rewrite_target e) <|>
      (do e ← to_expr ``(filter.germ.lift_pred_imp_iff_imp_lift_pred),
          rewrite_target e)
    | `(λ _, ∃ y, %%q) := 
      (do e ← to_expr ``(filter.germ.lift_pred_exists_iff_exists_lift_pred'),
          rewrite_target e) <|>
      (do e ← to_expr ``(filter.germ.lift_pred_exists_prop_iff_and_lift_pred),
          e' ← to_expr ``(exists_prop),
          rewrite_target e,
          rewrite_target e')
    | `(λ _, _ < _) := 
      do  e ← to_expr ``(filter.germ.lift_pred_lt_iff_lt_map),
          rewrite_target e
    | `(λ _, _ > _) := 
      do  e ← to_expr ``(filter.germ.lift_pred_lt_iff_lt_map),
          rewrite_target e
    | _ := fail "No known pattern applicable (step 3)"
    end

end step_three

meta def transfer_step_four_aux (tgt : expr) : tactic unit :=
do  hyps ← local_context,
    hyps.mmap' (λ x, try $ 
      do  `(filter.germ _ _) ← infer_type x,
          refine ``((%%x).induction_on _), 
          name ← get_unused_name, 
          intro name ),
    try (reflexivity)

namespace interactive

setup_tactic_parser

meta def transfer_step_one : tactic unit :=
target >>= transfer_step_one_aux

meta def transfer_step_two : tactic unit :=
target >>= transfer_step_two_aux

meta def transfer_step_three : tactic unit :=
target >>= transfer_step_three_aux

meta def transfer_step_four : tactic unit :=
target >>= transfer_step_four_aux

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
  rw filter.germ.coe_eq,
  refl
end

open filter

example (l : ℝ) (u : ℕ → ℝ) :
  (∀ ε > 0, ∃ N ≥ (1 : ℕ), ∀ n ≥ N, abs (u n - l) < ε) ↔
  (∀ ε > 0, ∃ N ≥ (1 : (hyperfilter ℕ : filter ℕ).germ ℕ), ∀ n ≥ N, germ.map abs (germ.map u n - ↑l) < ε) :=
begin
  transfer_step_one,
  transfer_step_two,
  transfer_step_three,
  transfer_step_two,
  { transfer_step_three, 
    transfer_step_four },
  { transfer_step_three,
    transfer_step_two,
    transfer_step_three,
    transfer_step_two,
    { transfer_step_four },
    { transfer_step_three,
      transfer_step_two,
      transfer_step_three,
      transfer_step_two,
      { transfer_step_four },
      { transfer_step_three,
        transfer_step_four } } }
end

end tactic