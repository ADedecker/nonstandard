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

example (f : ℝ → ℝ) : 
  (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, abs x < δ → abs (f x) < ε) ↔ 
  (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ*, germ.map abs x < δ → germ.map abs (germ.map f x) < ε) :=
begin
  rw forall_iff_forall_lift_pred (𝓗 : filter ℕ),
  refine forall_congr (λ ε, _),
  rw lift_pred_imp_iff_imp_lift_pred,
  refine imp_congr _ _,
  { rw lift_pred_lt_iff_lt_map,
    refine ε.induction_on (λ f, _),
    refl },
  { rw lift_pred_exists_iff_exists_lift_pred',
    refine exists_congr (λ δ, _),
    rw [lift_pred_exists_prop_iff_and_lift_pred, exists_prop],
    refine and_congr _ _,
    { rw lift_pred_lt_iff_lt_map,
      refine ε.induction_on (λ f, _),
      refine δ.induction_on (λ g, _),
      refl },
    { rw lift_pred_forall_iff_forall_lift_pred',
      refine forall_congr (λ x, _),
      rw lift_pred_imp_iff_imp_lift_pred,
      refine imp_congr _ _,
      { rw lift_pred_lt_iff_lt_map,
        refine ε.induction_on (λ f, _),
        refine δ.induction_on (λ g, _),
        refine x.induction_on (λ h, _),
        refl },
      { rw lift_pred_lt_iff_lt_map,
        refine ε.induction_on (λ f, _),
        refine δ.induction_on (λ g, _),
        refine x.induction_on (λ h, _),
        refl } } }
end

example (l : ℝ) (u : ℕ → ℝ) :
  (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, abs (u n - l) < ε) ↔
  (∀ ε > 0, ∃ N : (𝓗 : filter ℕ).germ ℕ, ∀ n ≥ N, germ.map abs (germ.map u n - ↑l) < ε) :=
begin
  rw forall_iff_forall_lift_pred (𝓗 : filter ℕ),
  refine forall_congr (λ ε, _),
  rw lift_pred_imp_iff_imp_lift_pred,
  refine imp_congr _ _,
  { rw lift_pred_lt_iff_lt_map,
    refine ε.induction_on (λ f, _),
    refl },
  { rw lift_pred_exists_iff_exists_lift_pred',
    refine exists_congr (λ N, _),
    rw lift_pred_forall_iff_forall_lift_pred',
    refine forall_congr (λ n, _),
    rw lift_pred_imp_iff_imp_lift_pred,
    refine imp_congr _ _,
    { refine ε.induction_on (λ f, _),
      refine N.induction_on (λ g, _),
      refine n.induction_on (λ h, _),
      refl },
    { refine ε.induction_on (λ f, _),
      refine N.induction_on (λ g, _),
      refine n.induction_on (λ h, _),
      rw [lt_def],
      refl } }
end

end examples

end filter.germ