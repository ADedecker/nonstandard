import order.filter.germ
import for_mathlib.filter_basic

/-! # Complements on filter germs -/

open filter function

namespace filter.germ

variables {ι α β : Type*} (l : filter ι)

local notation `∀*` binders `, ` r:(scoped p, filter.eventually p l) := r
local notation `α*` := l.germ α
local notation `β*` := l.germ β

/-! ## Product of germs -/

def prod_equiv : α* × β* ≃ l.germ (α × β) :=
{ to_fun := uncurry (quotient.map₂' (λ f g i, ⟨f i, g i⟩)
    begin
      intros f f' hff' g g' hgg',
      filter_upwards [hff', hgg'],
      intros i hfi hgi,
      simp [hfi, hgi]
    end),
  inv_fun := λ i, 
    ⟨quotient.map' (λ f, prod.fst ∘ f) 
      begin
        intros f f' hff',
        filter_upwards [hff'],
        intros i hfi,
        simp [hfi]
      end i, 
    quotient.map' (λ f, prod.snd ∘ f) 
      begin
        intros g g' hgg',
        filter_upwards [hgg'],
        intros i hgi,
        simp [hgi]
      end i⟩,
  left_inv := by {rintros ⟨⟨f⟩, ⟨g⟩⟩, refl},
  right_inv := by {rintro ⟨f⟩, convert rfl, ext x; refl} }

local notation `⋈` := (prod_equiv l : α* × β* → l.germ (α × β))

@[simp] lemma prod_equiv_coe (f : ι → α) (g : ι → β) : 
  ⋈ ((f : α*), (g : β*)) = ↑(λ (i : ι), (f i, g i)) :=
rfl

lemma lift_rel_iff_lift_pred_uncurry (r : α → β → Prop) (x : α*) (y : β*) : 
  lift_rel r x y ↔ lift_pred (uncurry r) (⋈ (x, y)) :=
begin
  refine x.induction_on₂ y (λ f g, _),
  refl
end

lemma lift_rel_iff_lift_pred_uncurry' (r : α → β → Prop) (x : α*) (y : β*) : 
  lift_rel r x y ↔ lift_pred (λ u : α × β, r u.1 u.2) (⋈ (x, y)) :=
lift_rel_iff_lift_pred_uncurry l r x y

lemma lift_rel_symm (r : α → β → Prop) (x : α*) (y : β*) : 
  lift_rel r x y ↔ lift_rel (λ a b, r b a) y x :=
begin
  refine x.induction_on₂ y (λ f g, _), 
  refl
end

/-! ## Transfer lemmas -/

/-! ### Forall rules -/

lemma forall_iff_forall_lift_pred [l.ne_bot] (p : α → Prop) : 
  (∀ x, p x) ↔ (∀ x : α*, lift_pred p x) :=
begin
  split,
  { refine λ h x, x.induction_on (λ f, _),
    exact eventually_of_forall (λ x, h (f x)) },
  { exact λ h x, lift_pred_const_iff.mp (h ↑x) }
end

/-! ### Exists rules -/

lemma exists_iff_exists_lift_pred [l.ne_bot] (p : α → Prop) : 
  (∃ x, p x) ↔ (∃ x : α*, lift_pred p x) :=
begin
  split,
  { exact λ ⟨x, hx⟩, ⟨↑x, lift_pred_const hx⟩ },
  { rintros ⟨x, hx⟩,
    revert hx,
    refine x.induction_on (λ f, _),
    exact λ hf, let ⟨i, hi⟩ := hf.exists in ⟨f i, hi⟩ }
end

lemma lift_pred_exists_iff_exists_lift_rel [l.ne_bot] (r : α → β → Prop) (x : α*) : 
  lift_pred (λ x, ∃ (y : β), r x y) x ↔ ∃ (y : β*), lift_rel r x y :=
begin
  refine x.induction_on (λ f, _),
  rw lift_pred_coe,
  split, 
  { exact λ h, let ⟨g, hg⟩ := h.choice in ⟨g, hg⟩ },
  { rintro ⟨y, hy⟩,
    revert hy,
    refine y.induction_on (λ g, _),
    intro hg,
    filter_upwards [hg],
    exact λ i hi, ⟨g i, hi⟩ }
end

lemma lift_pred_exists_iff_exists_lift_pred [l.ne_bot] (r : α → β → Prop) (x : α*) : 
  lift_pred (λ x, ∃ (y : β), r x y) x ↔ ∃ (y : β*), lift_pred (uncurry r) (⋈ (x, y)) :=
begin
  conv_rhs {congr, funext, rw ← lift_rel_iff_lift_pred_uncurry},
  exact lift_pred_exists_iff_exists_lift_rel l r x
end

lemma lift_pred_exists_iff_exists_lift_pred' [l.ne_bot] (r : α → β → Prop) (x : α*) : 
  lift_pred (λ x, ∃ (y : β), r x y) x ↔ ∃ (y : β*), lift_pred (λ u : α × β, r u.1 u.2) (⋈ (x, y)) :=
lift_pred_exists_iff_exists_lift_pred l r x

/-! ### And rules -/

lemma lift_pred_and_iff_and_lift_pred [l.ne_bot] (p q : α → Prop) (x : α*) :
  lift_pred (λ x, p x ∧ q x) x ↔ lift_pred p x ∧ lift_pred q x :=
begin
  refine x.induction_on (λ f, _),
  exact eventually_and
end

/-! ### Exists rules for Props -/

lemma lift_pred_exists_prop_iff_and_lift_pred [l.ne_bot] (p q : α → Prop) (x : α*) :
  lift_pred (λ x, ∃ (h : p x), q x) x ↔ lift_pred p x ∧ lift_pred q x :=
begin
  conv in (Exists _) {rw exists_prop},
  exact lift_pred_and_iff_and_lift_pred l p q x
end

end filter.germ