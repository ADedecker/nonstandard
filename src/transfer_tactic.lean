import complements.filter_product
import tactic
import tactic.interactive
import data.real.hyperreal

open tactic expr

namespace tactic

section lift_lhs

private meta def forall_rule (l : expr) (α : expr) : tactic unit :=
do  `(filter %%ι) ← infer_type l,
    e ← to_expr ``(filter.germ.forall_iff_forall_lift_pred %%l),
    rewrite_target e

private meta def exists_rule (l : expr) (α : expr) : tactic unit :=
do  `(filter %%ι) ← infer_type l,
    e ← to_expr ``(filter.germ.exists_iff_exists_lift_pred %%l),
    rewrite_target e

meta def transfer.lift_lhs (tgt : expr) : tactic unit :=
do  `(%%lhs ↔ %%rhs) ← (return tgt) | fail "Goal is not an equivalence (step 1)",
    match rhs with
    | `(∀ _ : (filter.germ %%l %%α), _) := forall_rule l α
    | `(∀ _ : ℝ*, _) := forall_rule `(filter.hyperfilter ℕ : filter ℕ) `(ℝ)
    | `(∃ _ : (filter.germ %%l %%α), _) := exists_rule l α
    | `(∃ _ : ℝ*, _) := exists_rule `(filter.hyperfilter ℕ : filter ℕ) `(ℝ)
    | _ := fail "No known pattern applicable (step 1)"
    end

end lift_lhs

section congr

meta def transfer.congr (tgt : expr) : tactic unit :=
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

end congr

section push_lift

meta def transfer.push_lift (tgt : expr) : tactic unit :=
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

end push_lift

section induction

meta def transfer.induction (tgt : expr) : tactic unit :=
local_context >>= list.mmap' (λ x, try $ 
  do  `(filter.germ _ _) ← infer_type x,
      refine ``((%%x).induction_on _), 
      name ← get_unused_name, 
      intro name )

meta def transfer.close (tgt : expr) : tactic unit :=
transfer.induction tgt >> reflexivity

meta def transfer.simp (tgt : expr) : tactic unit :=
transfer.induction tgt >> `[simp]

end induction

namespace interactive

setup_tactic_parser

meta def transfer.lift_lhs : tactic unit :=
target >>= tactic.transfer.lift_lhs

meta def transfer.congr : tactic unit :=
target >>= tactic.transfer.congr

meta def transfer.push_lift : tactic unit :=
target >>= tactic.transfer.push_lift

meta def transfer.induction : tactic unit :=
target >>= tactic.transfer.induction

meta def transfer.simp : tactic unit :=
target >>= tactic.transfer.simp

meta def transfer.close : tactic unit :=
target >>= tactic.transfer.close

meta def transfer.step : tactic unit :=
transfer.close <|>
transfer.congr <|>
(transfer.push_lift >> try transfer.congr) <|>
(transfer.lift_lhs >> try transfer.congr) <|>
transfer.simp -- WARNING

end interactive

example (α ι : Type*) [preorder α] (l : ultrafilter ι) (a : α) : 
  (∀ x, a ≤ x) ↔ (∀ x : (l : filter ι).germ α, ↑a ≤ x) :=
begin
  transfer.step,
  transfer.step
end

example (α ι : Type*) [preorder α] (l : ultrafilter ι) (a : α) : 
  (∀ x y : α, x = y) ↔ (∀ x y : (l : filter ι).germ α, x = y) :=
begin
  transfer.step,
  transfer.step,
  transfer.step,
  transfer.step
end

open filter

example (l : ℝ) (u : ℕ → ℝ) :
  (∀ ε > 0, ∃ N ≥ (1 : ℕ), ∀ n ≥ N, abs (u n - l) < ε) ↔
  (∀ ε > 0, ∃ N ≥ (1 : (hyperfilter ℕ : filter ℕ).germ ℕ), ∀ n ≥ N, germ.map abs (germ.map u n - ↑l) < ε) :=
begin
  transfer.step,
  transfer.step,
  { transfer.step, 
    transfer.step },
  { transfer.step, 
    transfer.step, 
    { transfer.step },
    { transfer.step, 
      transfer.step,
      { transfer.step },
      { transfer.step, 
        transfer.step } } }
end

end tactic