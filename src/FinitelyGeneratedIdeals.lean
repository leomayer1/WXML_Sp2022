import ideal
import data.finset.basic
import tactic
import group_theory.group_action.big_operators


--open_locale big_operators

variables {R : Type} [comm_ring R]
variable S : finset R
--variable f : S → R
--#check ∑ a : S, ((f a) * a : R)
   
instance tada : distrib_mul_action R R :=
{ smul_add := mul_add,
  smul_zero := mul_zero }  

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
      --ring,
      rw [←smul_eq_mul, finset.smul_sum],

      
      
    end
}


example (f : S → R) (r : R) : r * ∑ a : S, f a = ∑ a : S, (r * f a) :=
begin
  suggest,
end
#check finset.smul_sum