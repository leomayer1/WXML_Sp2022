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