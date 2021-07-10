import order.filter.filter_product
import complements.germ

/-! # Complements on filter products -/

open ultrafilter filter function

namespace filter.germ

variables {ι α β : Type*} (l : ultrafilter ι)

local notation `∀*` binders `, ` r:(scoped p, filter.eventually p l) := r
local notation `α*` := (l : filter ι).germ α
local notation `β*` := (l : filter ι).germ β
local notation `⋈` := (prod_equiv (l : filter ι) : α* × β* → (l : filter ι).germ (α × β))

/-! ## Transfer lemmas -/

/-! ### Not rules -/

lemma lift_pred_not_iff_not_lift_pred (p : α → Prop) (x : α*) : 
  lift_pred (λ x, ¬ p x) x ↔ ¬ lift_pred p x :=
begin
  refine x.induction_on (λ f, _),
  rw [lift_pred_coe, lift_pred_coe, eventually_not]
end

lemma lift_rel_not_iff_not_lift_rel (r : α → β → Prop) (x : α*) (y : β*) : 
  lift_rel (λ x y, ¬ r x y) x y ↔ ¬ lift_rel r x y :=
begin
  refine x.induction_on₂ y (λ f g, _),
  rw [lift_rel_coe, lift_rel_coe, eventually_not]
end

/-! ### Forall rules -/

lemma lift_pred_forall_iff_forall_lift_rel (r : α → β → Prop) (x : α*) : 
  lift_pred (λ x, ∀ (y : β), r x y) x ↔ ∀ (y : β*), lift_rel r x y :=
begin
  rw [← not_iff_not, ← lift_pred_not_iff_not_lift_pred],
  push_neg,
  simp_rw [← lift_rel_not_iff_not_lift_rel],
  exact lift_pred_exists_iff_exists_lift_rel ↑l _ x,
end

lemma lift_pred_forall_iff_forall_lift_pred (r : α → β → Prop) (x : α*) : 
  lift_pred (λ x, ∀ (y : β), r x y) x ↔ ∀ (y : β*), lift_pred (uncurry r) (⋈ (x, y)) :=
begin
  convert lift_pred_forall_iff_forall_lift_rel l r x,
  ext,
  exact forall_congr (λ y, by rw ← lift_rel_iff_lift_pred_uncurry)
end

lemma lift_pred_forall_iff_forall_lift_pred' (r : α → β → Prop) (x : α*) : 
  lift_pred (λ x, ∀ (y : β), r x y) x ↔ ∀ (y : β*), lift_pred (λ u : α × β, r u.1 u.2) (⋈ (x, y)) :=
lift_pred_forall_iff_forall_lift_pred l r x

end filter.germ