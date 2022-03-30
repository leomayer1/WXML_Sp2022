import tactic
import algebra.ring

section defs
/- Let R be an arbitrary commutative ring -/
variables (R : Type*) [comm_ring R]

/- Definition of an ideal -/
@[ext] structure ideal :=
(carrier : set R)
(zero_mem' : (0 : R) ∈ carrier)
(add_mem' {x y : R} : x ∈ carrier → y ∈ carrier → x + y ∈ carrier)
(smul_mem' (r : R) {x : R} : x ∈ carrier → r*x ∈ carrier)

/- The set {0} is an ideal -/
instance : has_zero (ideal R) := ⟨{
  carrier := {0}, --the singleton set containing 0
  zero_mem' := rfl,
  add_mem' := λ x y hx hy, by simp * at *,
  smul_mem' := λ r x hx, by simp * at *
}⟩

/- R itself is an ideal-/
def univ : ideal R := {
  carrier := set.univ, --set.univ is the set of all elements of R
  zero_mem' := by simp,
  add_mem' := by simp,
  smul_mem' := by simp
}

/- Definition of a principal ideal -/
def prin {R : Type*} [comm_ring R] (x : R) : ideal R := {
  carrier := {r : R | ∃ s : R, r = s*x},
  zero_mem' := ⟨0, (zero_mul x).symm⟩,
  add_mem' :=
    begin
      rintros _ _ ⟨a, rfl⟩ ⟨b, rfl⟩,
      exact ⟨a + b, (add_mul _ _ _).symm⟩
    end,
  smul_mem' :=
    begin
      rintros r _ ⟨a, rfl⟩,
      exact ⟨r * a, (mul_assoc _ _ _).symm⟩
    end
}

end defs

/- Here we define the membership relation, as well as any
  operations on ideals: intersection, sum, etc.
-/
section operations
variables {R : Type*} [comm_ring R]

/- This lets us write r ∈ I for r : R and I : ideal R -/
instance : has_mem R (ideal R) := ⟨λ x I, x ∈ I.carrier⟩
/- This lets us write I ⊆ J for I J : ideal R -/
instance : has_subset (ideal R) := ⟨λ I J, I.carrier ⊆ J.carrier⟩
/- This lets us write I ⊂ J for I J : ideal R -/
instance : has_ssubset (ideal R) := ⟨λ I J, I.carrier ⊂ J.carrier⟩
/- This lets us write I ∩ J for I J : ideal R -/
instance : has_inter (ideal R) := ⟨λ I J,
  {
    carrier := I.carrier ∩ J.carrier,
    zero_mem' := ⟨I.zero_mem', J.zero_mem'⟩,
    add_mem' := λ x y hx hy, ⟨I.add_mem' hx.1 hy.1, J.add_mem' hx.2 hy.2⟩,
    smul_mem' := λ r x hx, ⟨I.smul_mem' r hx.1, J.smul_mem' r hx.2⟩,
  }⟩

/- This lets us write I + J for I J : ideal R -/
instance : has_add (ideal R) := ⟨λ I J,
  {
    carrier := {x | ∃ i j : R, i ∈ I ∧ j ∈ J ∧ x = i + j},
    zero_mem' := ⟨0,0, I.zero_mem', J.zero_mem', by simp⟩,
    add_mem' :=
      begin
        rintros _ _ ⟨ix, jx, hix, hjx, rfl⟩ ⟨iy, jy, hiy, hjy, rfl⟩,
        exact ⟨ix + iy, jx + jy, I.add_mem' hix hiy, J.add_mem' hjx hjy, by ring⟩,
      end,
    smul_mem' :=
      begin
        rintros r _ ⟨i, j, hi, hj, rfl⟩,
        exact ⟨r*i, r*j, I.smul_mem' r hi, J.smul_mem' r hj, by ring⟩
      end
  }⟩

/- Easy lemmas -/
@[simp] lemma zero_mem (I : ideal R) : (0 : R) ∈ I := I.zero_mem'
@[simp] lemma sub_add_left (I J : ideal R) : I ⊆ I + J := λ i hi, ⟨i, 0, hi, by simp⟩
@[simp] lemma sub_add_right (I J : ideal R) : J ⊆ I + J := λ j hj, ⟨0, j, by simp, hj, by simp⟩

end operations

lemma mem_prin {R : Type*} [comm_ring R] (x : R) : x ∈ prin x := ⟨1, by ring⟩


/- Definitions and facts about prime and maximal ideals -/
variables {R : Type*} [comm_ring R]
def prime (I : ideal R) := ∀ x y : R, x*y ∈ I → x ∈ I ∨ y ∈ I
def maximal (I : ideal R) := ∀ J : ideal R, I ⊂ J → J = univ R

/- Pretty messy, definitely could use more outside lemmas -/
theorem maximal_implies_prime {I : ideal R} (hI : maximal I) : prime I :=
begin
  intros x y hxy,
  by_cases h : x ∈ I,
  { left,
    exact h
  },
  { right,
    have h2 := sub_add_left I (prin x),
    have h3 : I ⊂ I + (prin x),
    {
      unfold has_ssubset.ssubset,
      simp,
      rw set.ssubset_iff_of_subset,
      use x,
      exact ⟨(sub_add_right I (prin x)) (mem_prin x), h⟩,
      exact h2,
    },
    have h4 := hI (I + prin x) h3,
    have h5 : (1 : R) ∈ univ R := by simp [univ],
    rw ← h4 at h5,
    rcases h5 with ⟨i, _, hi, ⟨s, rfl⟩, hh⟩,
    rw ← (one_mul y),
    rw hh,
    rw add_mul,
    apply I.add_mem',
    { rw mul_comm,
      exact I.smul_mem' y hi,
    },
    { rw mul_assoc,
      exact I.smul_mem' s hxy,
    }
  }
end