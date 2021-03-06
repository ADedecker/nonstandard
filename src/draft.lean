import data.real.hyperreal
import complements.filter_product
import transfer_tactic

open filter function

namespace filter.germ

section examples

local notation `ð` := hyperfilter â

example : (â (x : â), â y, y â¤ x) â (â (x : â*), â y, y â¤ x) :=
by transfer

example : (â (x : â), â y, y â¤ x) â (â (x : â*), â y, y â¤ x) :=
by transfer

example : (â (x y : â), â z, (x â¤ z â§ z â¤ y)) â 
  (â (x y : â*), â z, (x â¤ z â§ z â¤ y)) :=
by transfer

example : (â (x y : â), (x â  y) â â z, (x < z â§ z < y) â¨ (x > z â§ z > y)) â 
  (â (x y : â*), (x â  y) â â z, (x < z â§ z < y) â¨ (x > z â§ z > y)) :=
by transfer

example (f : â â â) : 
  (â Îµ > 0, â Î´ > 0, â x : â, abs x < Î´ â abs (f x) < Îµ) â 
  (â Îµ > 0, â Î´ > 0, â x : â*, germ.map abs x < Î´ â germ.map abs (germ.map f x) < Îµ) :=
by transfer

example (l : â) (u : â â â) :
  (â Îµ > 0, â N : â, â n â¥ N, abs (u n - l) < Îµ) â
  (â Îµ > 0, â N : (ð : filter â).germ â, â n â¥ N, germ.map abs (germ.map u n - âl) < Îµ) :=
by transfer

-----------------

noncomputable def omega' {Î± : Type*} [ordered_semiring Î±] : 
  (ð : filter â).germ Î± := â(coe : â â Î±) 

local notation `Ï` := omega'

open_locale topological_space
open hyperreal

lemma abs_eq_map_abs : (abs : â* â â*) = germ.map abs :=
begin
  ext x,
  rw [abs, max_def],
  refine x.induction_on (Î» f, _),
  refl
end

lemma goal (u : â â â) (l : â) (h : tendsto u at_top (ð l)) : is_st (germ.map u Ï) l :=
begin
  rw metric.tendsto_at_top at h,
  intros Îµ hÎµ,
  rcases h Îµ hÎµ with â¨N, hNâ©,
  simp_rw [dist_eq_norm, real.norm_eq_abs] at hN,
  have : (â n : â, n â¥ N â abs (u n - l) < Îµ) â 
    (â n : (ð : filter â).germ â, n â¥ âN â germ.map abs (germ.map u n - âl) < âÎµ),
  by transfer,
  rw this at hN,
  specialize hN Ï sorry,
  rw â abs_eq_map_abs at hN,
  rw abs_lt at hN,
  sorry
end

end examples

end filter.germ