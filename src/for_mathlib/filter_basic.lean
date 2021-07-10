import order.filter.basic

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