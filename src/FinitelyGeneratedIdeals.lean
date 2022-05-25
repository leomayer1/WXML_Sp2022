import ideal
import data.finset.basic
import tactic
import group_theory.group_action.basic


open_locale big_operators

variables {R : Type} [comm_ring R]
variable S : finset R
   
 

def ideal_gen_by  : ideal R := {
  carrier := {x : R | ∃ I : S → R, x = ∑ a : S, ((I a) * a : R)  }, 

  zero_mem' := 
  begin 
    simp only [finset.univ_eq_attach, set.mem_set_of_eq],
    use 0,
    simp only [pi.zero_apply, zero_mul, finset.sum_const_zero],
  end,
  add_mem' :=
    begin
      simp,
      intros x y f hx g hy,
      use f + g,
      simp [hx, hy],
      ring,
      rw finset.sum_add_distrib,
    end,
  smul_mem' :=
    begin
      intros r x h,
      cases h with f hx,
      let rf : S → R := λ s, r*f(s),
      use rf,
      rw hx,
      rw [←smul_eq_mul, finset.smul_sum],
      apply finset.sum_congr rfl,
      intros a ha,
      rw [smul_eq_mul, mul_assoc],    
    end
}

def fingen (I : ideal R) : Prop := ∃ S : finset R, I = ideal_gen_by S

--- See Brendan Note in ideal.lean
def add_subgroup_of_ideal (I : ideal R) : add_subgroup R := {
  carrier := I.carrier,
  zero_mem' := I.zero_mem',
  add_mem' := I.add_mem',
  neg_mem' := λ x h, by { have := I.smul_mem' (-1) h, simp at this, assumption }
}
---

lemma linear_combinations_in_ideal (I : ideal R) (S : finset R) (f: S → R): (∀ x, x ∈ S → x ∈ I) → ∑ a : S, (f a) * a ∈ I :=
begin
  intro h,
  apply add_subgroup.sum_mem (add_subgroup_of_ideal I),
  simp,
  intro,
  apply I.smul_mem',
  apply h,
  cases c,
  exact c_property,
end

lemma gen_by_subset_is_subset (I : ideal R) (S : finset R) :(∀ x, x ∈ S → x ∈ I) → ideal_gen_by S ⊆ I :=
begin
  intros h x g,
  simp [ideal_gen_by] at g,
  cases g with coeffs g,
  subst g,
  apply linear_combinations_in_ideal,
  assumption,
end

def indicator_of (P : set R) [decidable_pred P] : R → R :=
  λ x, if P x then 1 else 0

theorem sum_over_subtype_is_sum_in {α G : Type} [decidable_eq α] [add_comm_monoid  G] (S : finset α) (f : α → G) (g : S → G) 
  : (∀ x (h : x ∈ S), g ⟨x, h⟩ = f x) → ∑ x : S, g x = ∑ x : α in S, f x :=
begin
  revert f g,
  apply finset.induction_on S,
  { simp },
  { intros a s h ih f g hfeqg, 
    dsimp [coe_sort], 
    rw finset.attach_insert,
    rw finset.sum_insert, 
    { rw finset.sum_insert h,
      rw hfeqg,
      rw ← ih f (λ x : s, g ⟨x.val, finset.mem_insert_of_mem x.property⟩),
      { dsimp [finset.sum], apply congr_arg, apply congr_arg,
        rw @finset.image_val_of_inj_on {x // x ∈ s} {x // x ∈ insert a s},
        { simp, congr },
        { intros x hx y hy heq, cases x, cases y,
          simp at heq ⊢, assumption } },
      { intros, simp, apply_assumption } },
    { rw @finset.mem_image {x // x ∈ s} {x // x ∈ insert a s},
      intro h', cases h' with w h', cases h' with w' h', cases w,
      simp at h', rw h' at w_property, contradiction }, 
  }
end

lemma finset_subset_of_ideal_gen_by [decidable_eq R] (S : finset R) : ∀ x : R, x ∈ S → x ∈ ideal_gen_by S :=
begin
  intros x h,
  existsi (λ y : S, indicator_of (λ z, z = x) y.val),
  rewrite sum_over_subtype_is_sum_in S (λ y, indicator_of (λ z, z = x) y * y),
  { rw [← finset.insert_erase h, finset.sum_insert (finset.not_mem_erase x S)],
    rw finset.sum_eq_zero,
    { simp [indicator_of] },
    { intros, simp [indicator_of], intro, simp at H, cases H, contradiction } },
  { simp }
end 

lemma gen_by_of_subset_is_subset [decidable_eq R] (S S' : finset R) : S ⊆ S' → ideal_gen_by S ⊆ ideal_gen_by S' :=
begin
  intro,
  apply gen_by_subset_is_subset (ideal_gen_by S') S,
  intros y hy, apply finset_subset_of_ideal_gen_by, apply_assumption, assumption
end