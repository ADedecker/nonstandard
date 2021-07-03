import data.real.hyperreal

open filter

namespace filter

lemma eventually.choice {α β : Type*} {r : α → β → Prop} {l : filter α} 
  [l.ne_bot] (h : ∀ᶠ x in l, ∃ y, r x y) : ∃ f : α → β, ∀ᶠ x in l, r x (f x) :=
begin
  classical,
  use (λ x, if hx : ∃ y, r x y then classical.some hx 
            else classical.some (classical.some_spec h.exists)),
  filter_upwards [h],
  intros x hx,
  rw dif_pos hx,
  exact classical.some_spec hx
end

end filter

namespace filter.germ

variables {ι α β : Type*} (l : filter ι)

local notation `∀*` binders `, ` r:(scoped p, filter.eventually p l) := r
local notation `α*` := l.germ α
local notation `β*` := l.germ β

lemma lift_rel_symm (r : α → β → Prop) (x : α*) (y : β*) : 
  lift_rel r x y ↔ lift_rel (λ a b, r b a) y x :=
begin
  refine x.induction_on₂ y (λ f g, _), 
  rw [lift_rel_coe, lift_rel_coe]
end

lemma forall_iff_forall_lift_pred [l.ne_bot] (p : α → Prop) : 
  (∀ x, p x) ↔ (∀ x : α*, lift_pred p x) :=
begin
  split,
  { refine λ h x, x.induction_on (λ f, _),
    rw lift_pred_coe,
    exact eventually_of_forall (λ x, h (f x)) },
  { exact λ h x, lift_pred_const_iff.mp (h ↑x) }
end

lemma exists_iff_exists_lift_pred [l.ne_bot] (p : α → Prop) : 
  (∃ x, p x) ↔ (∃ x : α*, lift_pred p x) :=
begin
  split,
  { exact λ ⟨x, hx⟩, ⟨↑x, lift_pred_const hx⟩ },
  { rintros ⟨x, hx⟩,
    revert hx,
    refine x.induction_on (λ f, _),
    intro hf,
    rw lift_pred_coe at hf,
    rcases hf.exists with ⟨i, hi⟩,
    exact ⟨f i, hi⟩ }
end

lemma lift_pred_exists_eq_exists_lift_rel [l.ne_bot] (r : α → β → Prop) : 
  lift_pred (λ x, ∃ (y : β), r x y) = (λ x, ∃ (y : β*), lift_rel r x y) :=
begin
  ext x,
  refine x.induction_on (λ f, _),
  rw lift_pred_coe,
  split, 
  { intro h,
    rcases h.choice with ⟨g, hg⟩,
    use g,
    rw lift_rel_coe,
    exact hg },
  { rintro ⟨y, hy⟩,
    revert hy,
    refine y.induction_on (λ g, _),
    intro hg,
    rw lift_rel_coe at hg,
    filter_upwards [hg],
    exact λ i hi, ⟨g i, hi⟩ }
end

example : (∀ (x : ℝ), ∃ y, y ≤ x) ↔ (∀ (x : ℝ*), ∃ y, y ≤ x) :=
begin
  rw forall_iff_forall_lift_pred (hyperfilter ℕ : filter ℕ),
  refine forall_congr (λ x, _),
  rw lift_pred_exists_eq_exists_lift_rel,
  refine exists_congr (λ y, _),
  rw lift_rel_symm,
  refl
end

end filter.germ