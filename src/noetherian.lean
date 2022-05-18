import ideal

section generation

variables {R : Type} [comm_ring R]

/- Inductively define the (underlying set of) the ideal
  generated by a set
-/
inductive gen_by' (A : set R) : set R
| mem_self : ∀ a ∈ A, gen_by' a
| zero_mem : gen_by' 0
| add_mem : ∀ x y : R, gen_by' x → gen_by' y → gen_by' (x + y)
| smul_mem : ∀ r x : R, gen_by' x → gen_by' (r*x)

def gen_by (A : set R) : ideal R :=
{ carrier := gen_by' A,
  zero_mem' :=  gen_by'.zero_mem,
  add_mem' := gen_by'.add_mem,
  smul_mem' := gen_by'.smul_mem
}

/- TODO : a million helper lemmas
  gen_by A ⊆ I ↔ A ⊆ I.carrier
  gen_by A = intersection of ideals I st A ⊆ I.carrier,
  etc.
-/

end generation

/- An ideal is finitely generated if it is the ideal defined by a
  finite set.
  Lean defines a set X to be finite if there is a list L (built-in inductive type)
  of elements of the set, such that ∀ x ∈ X, x ∈ X → x ∈ L
-/

section fingen

variables {R : Type} [comm_ring R]

def fin_gen (I : ideal R) := ∃ A : set R, set.finite A ∧ gen_by A = I

end fingen


section noeth

variables (R : Type) [comm_ring R]

def noetherian := ∀ I : ideal R, fin_gen I

end noeth

section ascending_chain

variables (R : Type) [comm_ring R]

def asc_chain {R : Type} [comm_ring R] (I : ℕ → ideal R) := ∀ n : ℕ, I n ⊆ I (n + 1)

def asc_ch_cond (R : Type) [comm_ring R] :=
  ∀ (f : ℕ → ideal R), asc_chain f → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → f n = f N


end ascending_chain

variables {R : Type} [comm_ring R]

lemma noetherian_of_acc (h : asc_ch_cond R) : noetherian R := sorry
lemma acc_of_noetherian (h : noetherian R) : asc_ch_cond R := sorry

-- need facts about polynomials, degrees?