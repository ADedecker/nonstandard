import data.real.hyperreal
import complements.filter_product
import transfer_tactic

open filter function

namespace filter.germ

section examples

local notation `𝓗` := hyperfilter ℕ

example : (∀ (x : ℝ), ∃ y, y ≤ x) ↔ (∀ (x : ℝ*), ∃ y, y ≤ x) :=
by transfer

example : (∃ (x : ℝ), ∀ y, y ≤ x) ↔ (∃ (x : ℝ*), ∀ y, y ≤ x) :=
by transfer

example : (∀ (x y : ℝ), ∃ z, (x ≤ z ∧ z ≤ y)) ↔ 
  (∀ (x y : ℝ*), ∃ z, (x ≤ z ∧ z ≤ y)) :=
by transfer

example : (∀ (x y : ℝ), (x ≠ y) → ∃ z, (x < z ∧ z < y) ∨ (x > z ∧ z > y)) ↔ 
  (∀ (x y : ℝ*), (x ≠ y) → ∃ z, (x < z ∧ z < y) ∨ (x > z ∧ z > y)) :=
by transfer

example (f : ℝ → ℝ) : 
  (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, abs x < δ → abs (f x) < ε) ↔ 
  (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ*, germ.map abs x < δ → germ.map abs (germ.map f x) < ε) :=
by transfer

example (l : ℝ) (u : ℕ → ℝ) :
  (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, abs (u n - l) < ε) ↔
  (∀ ε > 0, ∃ N : (𝓗 : filter ℕ).germ ℕ, ∀ n ≥ N, germ.map abs (germ.map u n - ↑l) < ε) :=
by transfer

-----------------

noncomputable def omega' {α : Type*} [ordered_semiring α] : 
  (𝓗 : filter ℕ).germ α := ↑(coe : ℕ → α) 

local notation `ω` := omega'

open_locale topological_space
open hyperreal

lemma abs_eq_map_abs : (abs : ℝ* → ℝ*) = germ.map abs :=
begin
  ext x,
  rw [abs, max_def],
  refine x.induction_on (λ f, _),
  refl
end

lemma goal (u : ℕ → ℝ) (l : ℝ) (h : tendsto u at_top (𝓝 l)) : is_st (germ.map u ω) l :=
begin
  rw metric.tendsto_at_top at h,
  intros ε hε,
  rcases h ε hε with ⟨N, hN⟩,
  simp_rw [dist_eq_norm, real.norm_eq_abs] at hN,
  have : (∀ n : ℕ, n ≥ N → abs (u n - l) < ε) ↔ 
    (∀ n : (𝓗 : filter ℕ).germ ℕ, n ≥ ↑N → germ.map abs (germ.map u n - ↑l) < ↑ε),
  by transfer,
  rw this at hN,
  specialize hN ω sorry,
  rw ← abs_eq_map_abs at hN,
  rw abs_lt at hN,
  sorry
end

end examples

end filter.germ