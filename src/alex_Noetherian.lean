import data.finset.basic
import tactic
import group_theory.group_action.basic
import FinitelyGeneratedIdeals

def is_ascending {R} [comm_ring R] (f : ℕ → ideal R) :=
  ∀ n, f n ⊆ f (n + 1)

lemma arbitrary_indices_ascending {R} [comm_ring R] (f : ℕ → ideal R)
  : is_ascending f → ∀ i j, i ≤ j → f i ⊆ f j :=
begin
  intros h i j hij,
  cases (nat.le.dest hij) with k hk,
  revert i j,
  induction k with k ih; intros; subst hk,
  { refl },
  { transitivity (f (i + k)).carrier,
    apply ih; linarith,
    apply h }
end

def ascending_chain_is_directed {R} [comm_ring R] (f : ℕ → ideal R)
  : is_ascending f → directed (⊆) f :=
  λ hAsc i j, ⟨max i j, arbitrary_indices_ascending f hAsc i (max i j) (le_max_iff.mpr (or.inl (le_refl i))),
                        arbitrary_indices_ascending f hAsc j (max i j) (le_max_iff.mpr (or.inr (le_refl j)))⟩

def stabilizes {R} [comm_ring R] (f : ℕ → ideal R) := ∃ N, ∀ n ≥ N, f n = f N

def ACC (R) [comm_ring R] : Prop :=  
  ∀ f : ℕ → ideal R, is_ascending f → stabilizes f

def all_ideals_fg (R) [comm_ring R] : Prop :=
  ∀ I : ideal R, fingen I

lemma exists_outside_of_not_fingen {R} [comm_ring R] (I : ideal R) (S : finset R)
  : ¬ fingen I → (∀ x, x ∈ S → x ∈ I) → ∃ y, y ∈ I ∧ y ∉ ideal_gen_by S :=
begin
  intros h g,
  by_contra h',
  apply h,
  existsi S,
  ext,
  constructor,
  { simp at h', apply_assumption },
  { apply gen_by_subset_is_subset, assumption }
end

local attribute [instance] classical.prop_decidable

noncomputable
def ascending_chain_of_generators_in_not_fg_ideal {R} [comm_ring R] (I : ideal R) (h : ¬ fingen I)
  : ℕ → { S : finset R | ∀ x, x ∈ S → x ∈ I }
| 0 := ⟨∅, by simp⟩
| (n+1) :=
  match ascending_chain_of_generators_in_not_fg_ideal n with 
  | ⟨S, hS⟩ := match classical.indefinite_description _ (exists_outside_of_not_fingen I S h hS) with
              | ⟨y, hy⟩ := ⟨S.cons y (λ hIn, hy.right (finset_subset_of_ideal_gen_by S y hIn)),
                           λ x h', or.elim (finset.mem_cons.mp h')
                                           (λ hxy, eq.substr hxy hy.left)
                                           (hS x)⟩
              end
  end

lemma ascending_chain_of_generators_in_not_fg_ideal_is_ascending {R} [comm_ring R] (I : ideal R) (h : ¬ fingen I) 
  : ∀ n, (ascending_chain_of_generators_in_not_fg_ideal I h n).val ⊆ (ascending_chain_of_generators_in_not_fg_ideal I h (n + 1)).val :=
begin
  intros n x h',
  destruct (ascending_chain_of_generators_in_not_fg_ideal I h n), intros S hS heq1,
  destruct (classical.indefinite_description _ (exists_outside_of_not_fingen I S h hS)), intros y hy heq2,
  rw [ascending_chain_of_generators_in_not_fg_ideal, heq1,
      ascending_chain_of_generators_in_not_fg_ideal._match_1, heq2,
      ascending_chain_of_generators_in_not_fg_ideal._match_2, finset.mem_cons],
  right, rw heq1 at h', exact h'
end

noncomputable
def ascending_chain_of_ideals_in_not_fg_ideal {R} [comm_ring R] (I : ideal R) (h : ¬ fingen I)
  : ℕ → ideal R := λ n, ideal_gen_by (ascending_chain_of_generators_in_not_fg_ideal I h n).val

lemma ascending_chain_of_ideals_in_not_fg_ideal_is_ascending {R} [comm_ring R] (I : ideal R) (h : ¬ fingen I) 
  : is_ascending (ascending_chain_of_ideals_in_not_fg_ideal I h) :=
λ n x hx, gen_by_of_subset_is_subset _ _ (ascending_chain_of_generators_in_not_fg_ideal_is_ascending I h n) hx

theorem ACC_iff_all_ideals_fg (R) [comm_ring R] : ACC R ↔ all_ideals_fg R :=
begin
  constructor,
  { intros h I,
    by_contra h',
    have asc := ascending_chain_of_generators_in_not_fg_ideal I h',
    have := h (ascending_chain_of_ideals_in_not_fg_ideal I h') _,
    { cases this with N H, 
      specialize H (N + 1) (by linarith), 
      dsimp [ascending_chain_of_ideals_in_not_fg_ideal] at H,
      destruct ascending_chain_of_generators_in_not_fg_ideal I h' N, intros S hS h1,
      destruct (classical.indefinite_description _ (exists_outside_of_not_fingen I S h' hS)), intros y hy h2,
      rw [ascending_chain_of_generators_in_not_fg_ideal, h1,
          ascending_chain_of_generators_in_not_fg_ideal._match_1, h2,
          ascending_chain_of_generators_in_not_fg_ideal._match_2] at H,
      apply hy.right, dsimp at H, rw ← H, apply finset_subset_of_ideal_gen_by,
      apply finset.mem_cons_self },
    { apply ascending_chain_of_ideals_in_not_fg_ideal_is_ascending } },
  { intros h f hAsc,
    have : directed (⊆) f := ascending_chain_is_directed f hAsc,
    specialize h (union_of_directed_family f this),
    cases h with S hS,
    have in_S_implies_in_fn : ∀ y : R, y ∈ S → ∃ n, y ∈ f n,
    { intros y hy,
      have : y ∈ union_of_directed_family f this,
      { rw hS, apply finset_subset_of_ideal_gen_by, assumption },
      { cases this with S' hy', cases hy' with w hy', cases w with i hi, subst hi,
        existsi i, assumption } },
    let min_index_containing : S → ℕ := λ x, @nat.find (λ n, x.val ∈ f n) _ (in_S_implies_in_fn x.val x.property),
    let S' := multiset.map min_index_containing S.attach.val,
    suffices stable : ∀ n, (∀ k, k ∈ S' → k ≤ n) → f n = union_of_directed_family f this,
    { existsi (multiset.sum S'),
      intros n hn,
      transitivity union_of_directed_family f this;
      rw stable; intros k hk; transitivity S'.sum,
      { apply multiset.single_le_sum (λ _ _, nat.zero_le _) k hk },
      { assumption },
      { apply multiset.single_le_sum (λ _ _, nat.zero_le _) k hk },
      { refl } },
    intros n hn,
    ext, constructor; intro h,
    { existsi (f n).carrier, existsi _, assumption, existsi n, refl },
    { rw hS at h, cases h with coeffs h, rw h,
      apply linear_combinations_in_ideal,
      intros y hy,
      let k := min_index_containing ⟨y, hy⟩,
      apply arbitrary_indices_ascending f hAsc k n,
      { apply hn, rw multiset.mem_map, existsi (subtype.mk y hy), simp },
      { exact nat.find_spec (in_S_implies_in_fn y hy) } } }
end