import data.real.hyperreal
import complements.filter_product

open filter function

namespace filter.germ

section examples

local notation `𝓗` := hyperfilter ℕ

example : (∀ (x : ℝ), ∃ y, y ≤ x) ↔ (∀ (x : ℝ*), ∃ y, y ≤ x) :=
begin
  rw forall_iff_forall_lift_pred (𝓗 : filter ℕ),
  refine forall_congr (λ x, _),
  rw lift_pred_exists_iff_exists_lift_rel,
  refine exists_congr (λ y, _),
  rw ← uncurry_apply_pair (≤) y x,
  rw lift_rel_symm,
  refl
end

example : (∃ (x : ℝ), ∀ y, y ≤ x) ↔ (∃ (x : ℝ*), ∀ y, y ≤ x) :=
begin
  rw exists_iff_exists_lift_pred (𝓗 : filter ℕ),
  refine exists_congr (λ x, _),
  rw lift_pred_forall_iff_forall_lift_rel,
  refine forall_congr (λ y, _),
  rw lift_rel_symm,
  refl
end

example : (∀ (x y : ℝ), ∃ z, (x ≤ z ∧ z ≤ y)) ↔ 
  (∀ (x y : ℝ*), ∃ z, (x ≤ z ∧ z ≤ y)) :=
begin
  rw forall_iff_forall_lift_pred (𝓗 : filter ℕ),
  refine forall_congr (λ x, _),
  rw lift_pred_forall_iff_forall_lift_pred',
  refine forall_congr (λ y, _),
  rw lift_pred_exists_iff_exists_lift_pred',
  refine exists_congr (λ z, _),
  rw lift_pred_and_iff_and_lift_pred,
  refine and_congr _ _;
  { refine x.induction_on (λ f, _),
    refine y.induction_on (λ g, _),
    refine z.induction_on (λ h, _),
    refl }
end

end examples

end filter.germ