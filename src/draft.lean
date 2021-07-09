import data.real.hyperreal

open filter function

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

section filter

variables {ι α β : Type*} (l : filter ι)

local notation `∀*` binders `, ` r:(scoped p, filter.eventually p l) := r
local notation `α*` := l.germ α
local notation `β*` := l.germ β

--private def myfun : (ι → α) → (ι → β) → ι → α × β := λ f g i, ⟨f i, g i⟩
--private def myfun_inv_fst : (ι → α × β) → ι → α := λ f, prod.fst ∘ f
--private def myfun_inv_snd : (ι → α × β) → ι → β := λ f, prod.snd ∘ f

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

lemma forall_iff_forall_lift_pred [l.ne_bot] (p : α → Prop) : 
  (∀ x, p x) ↔ (∀ x : α*, lift_pred p x) :=
begin
  split,
  { refine λ h x, x.induction_on (λ f, _),
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

example : (∀ (x : ℝ), ∃ y, y ≤ x) ↔ (∀ (x : ℝ*), ∃ y, y ≤ x) :=
begin
  rw forall_iff_forall_lift_pred (hyperfilter ℕ : filter ℕ),
  refine forall_congr (λ x, _),
  rw lift_pred_exists_iff_exists_lift_rel,
  refine exists_congr (λ y, _),
  rw ← uncurry_apply_pair (≤) y x,
  rw lift_rel_symm,
  refl
end

end filter

section ultrafilter

open ultrafilter

variables {ι α β : Type*} (l : ultrafilter ι)

local notation `∀*` binders `, ` r:(scoped p, filter.eventually p l) := r
local notation `α*` := (l : filter ι).germ α
local notation `β*` := (l : filter ι).germ β
local notation `⋈` := (prod_equiv (l : filter ι) : α* × β* → (l : filter ι).germ (α × β))

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

end ultrafilter

example : (∃ (x : ℝ), ∀ y, y ≤ x) ↔ (∃ (x : ℝ*), ∀ y, y ≤ x) :=
begin
  rw exists_iff_exists_lift_pred (hyperfilter ℕ : filter ℕ),
  refine exists_congr (λ x, _),
  rw lift_pred_forall_iff_forall_lift_rel,
  refine forall_congr (λ y, _),
  rw lift_rel_symm,
  refl
end

example : (∀ (x y : ℝ), ∃ z, x ≤ z) ↔ 
  (∀ (x y : ℝ*), ∃ z, x ≤ z) :=
begin
  rw forall_iff_forall_lift_pred (hyperfilter ℕ : filter ℕ),
  refine forall_congr (λ x, _),
  rw lift_pred_forall_iff_forall_lift_pred',
  refine forall_congr (λ y, _),
  rw lift_pred_exists_iff_exists_lift_pred',
  refine exists_congr (λ z, _),
  refine x.induction_on (λ f, _),
  refine y.induction_on (λ g, _),
  refine z.induction_on (λ h, _),
  simp,
  refl,
end

end filter.germ