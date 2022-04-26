import tactic
import algebra.ring

section defs
/- Let R be an arbitrary commutative ring -/
variables (R : Type*) [comm_ring R]

/- Definition of an ideal.
  In order to define an ideal, one needs to specify its
  underlying set (carrier), as well as three proofs
-/
@[ext] structure ideal :=
(carrier : set R)
(zero_mem' : (0 : R) ∈ carrier)
(add_mem' {x y : R} : x ∈ carrier → y ∈ carrier → x + y ∈ carrier)
(smul_mem' (r : R) {x : R} : x ∈ carrier → r*x ∈ carrier)

/- The set {0} is an ideal -/
instance : has_zero (ideal R) := ⟨{
  carrier := {0}, --the singleton set containing 0
  zero_mem' := rfl, --proof that 0 ∈ {0}
  add_mem' := λ x y hx hy, by simp * at *, --proof that if x ∈ {0} and y ∈ {0}, then
                                          -- x + y ∈ {0}. "simp" is a tactic that is
                                          -- able to perform basic simplifications,
                                          -- so it can replace the hypothesis x ∈ {0}
                                          -- with x = 0, and it knows 0 + 0 = 0.
  smul_mem' := λ r x hx, by simp * at *   --simp also knows r*0 = 0
}⟩

/- R itself is an ideal-/
def univ : ideal R := {
  carrier := set.univ, --set.univ is the set of all elements of R
  zero_mem' := by triv,
  add_mem' := by simp,
  smul_mem' := by simp
}

/- Definition of a principal ideal -/
def prin {R : Type*} [comm_ring R] (x : R) : ideal R := {
  carrier := {r : R | ∃ s : R, r = s*x},
  zero_mem' := ⟨0, (zero_mul x).symm⟩,
  add_mem' :=
    begin
      rintros _ _ ⟨a, rfl⟩ ⟨b, rfl⟩, --if a*x, b*x ∈ prin x...
      exact ⟨a + b, by rw ← add_mul⟩, --then a*x + b*x = (a + b)*x ∈ prin x
    end,
  smul_mem' :=
    begin
      rintros r _ ⟨a, rfl⟩, -- if a*x ∈ prin x...
      exact ⟨r * a, (mul_assoc _ _ _).symm⟩ -- then r*(a*x) = (r*a)*x ∈ prin x
    end
}

lemma univ_eq_prin_one : univ R = prin (1 : R) :=
begin
  ext,
  split,
  { intro h,
    simp [prin],}, --what is going on here??
  { intro h,
    triv,
  },
end

end defs

/- Here we define the membership relation, as well as any
  operations on ideals: intersection, sum, etc.
  We could also add a lot from e.g. Atiyah MacDonald ch 1:
  ideal quotients, radical ideals, the radical operation,
  and facts about these objects.
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

lemma mem_prin {R : Type*} [comm_ring R] (x : R) : x ∈ prin x := ⟨1, by simp⟩


/- Definitions and facts about prime and maximal ideals -/
variables {R : Type*} [comm_ring R]
def is_prin (I : ideal R) := ∃ (x : R), I = prin x
def radical (I : ideal R) := ∀ (x : R) (n : ℕ), x^(n + 1) ∈ I → x ∈ I
def prime (I : ideal R) := ((1 : R) ∉ I) ∧ (∀ x y : R, x*y ∈ I → x ∈ I ∨ y ∈ I)
def maximal (I : ideal R) := (1 : R) ∉ I ∧ ∀ J : ideal R, I ⊂ J → J = univ R
lemma is_unit_iff (x : R) : is_unit x ↔ ∃ y : R, x*y = 1 :=
  begin
    split,
    { intro h,
      rcases h with ⟨x,rfl⟩,
      cases x with x y h1 h2,
      use y,
      exact h1,
    },
    { rintros ⟨y,hy⟩,
      unfold is_unit,
      use x,
      exact y,
      exact hy,
      rw mul_comm,
      exact hy,
      refl,
    }
  end
def irreducible (x : R) := ∀ y z : R, y*z = x → is_unit y ∨ is_unit z
def preimage {S : Type*} [comm_ring S] (f: S →+* R) (I : ideal R) : ideal S :=
  { carrier := f ⁻¹' (I.carrier),
    zero_mem' := by simp[map_zero f, ideal.zero_mem'],
    add_mem' := λ x y hx hy, by simp [ideal.add_mem' I hx hy],
    smul_mem' := λ r x hx, by simp [ideal.smul_mem' I (f r) hx],
  }
@[simp] lemma mem_preimage_iff {S : Type*} [comm_ring S] (f: S →+* R) (I : ideal R) (x : S) :
    x ∈ preimage f I ↔ f x ∈ I := iff.rfl

/- Pretty messy, definitely could use more outside lemmas
  This is what formalizing proofs "usually" looks like,
  with the entire thing written in tactic mode
-/
theorem prime_of_maximal {I : ideal R} (hI : maximal I) : prime I :=
begin
  split,
  exact hI.1,
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
    have h4 := hI.2 (I + prin x) h3,
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

theorem prime_of_preimage {S : Type*} [comm_ring S] (f : R →+* S) {I : ideal S}
  (hI : prime I) : prime (preimage f I) :=
begin
  split,
  { intros h1,
    simp * at *,
    exact hI.1 h1,
  },
  { intros x y hxy,
    simp at hxy,
    cases hI.2 (f x) (f y) hxy with hx hy,
    { left,
      exact hx,},
    { right,
      exact hy,},
    },
end

theorem radical_of_prime {I : ideal R} (hI : prime I) : radical I :=
begin
  intros x n h,
  induction n with m hm,
  { simp at h,
    exact h,
  },
  {
    have h2 : x*x^(m+1) ∈ I,
    {
      convert h,
      rw nat.succ_eq_add_one,
      repeat {rw pow_add},
      ring,
    },
    cases (hI.2 x (x^(m+1)) h2) with hx hbig,
    {
      exact hx,
    },
    {
      exact hm hbig,
    }
  }
end