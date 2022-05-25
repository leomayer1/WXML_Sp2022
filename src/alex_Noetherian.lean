import data.finset.basic
import tactic
import group_theory.group_action.basic
import FinitelyGeneratedIdeals

variables (R : Type) [comm_ring R]

def is_ascending (f : ℕ → ideal R) := ∀ n, f n ⊆ f (n + 1)

lemma arbitrary_indices_ascending (f : ℕ → ideal R) : is_ascending R f → ∀ i j, i ≤ j → f i ⊆ f j :=
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

def stabilizes (f : ℕ → ideal R) := ∃ N, ∀ n > N, f n = f N

def ACC : Prop :=  
  ∀ f : ℕ → ideal R, is_ascending R f → stabilizes R f

def Noetherian : Prop :=
  ∀ I : ideal R, fingen I

lemma not_fingen_exists_outside (I : ideal R) (S: finset R) : ¬fingen I → (∀ x, x ∈ S → x ∈ I) → ∃ y, y ∈ I ∧ y ∉ ideal_gen_by S :=
begin
  intros h g,
  by_contra h',
  have := forall_not_of_not_exists h',
  simp at this,
  apply h,
  existsi S,
  ext,
  constructor,
  {
    apply this,
  },
  {
    apply gen_by_subset_is_subset,
    assumption,
  },
end

local attribute [instance] classical.prop_decidable

noncomputable
def ascending_chain_of_not_fingen (I : ideal R) (h : ¬ fingen I) : ℕ → { S : finset R | ∀ x, x ∈ S → x ∈ I }
| 0 := ⟨∅, by simp⟩
| (n+1) :=
  match ascending_chain_of_not_fingen n with 
  | ⟨S, hS⟩ := match classical.indefinite_description _ (not_fingen_exists_outside R I S h hS) with
              | ⟨y, hy⟩ := ⟨S.cons y (by { intro, cases hy, apply hy_right, apply finset_subset_of_ideal_gen_by S, assumption}),
                           by {intros x h, simp at h, cases h, rw h_1, cases hy, assumption, apply hS, assumption,}⟩
              end
  end

lemma ascending_chain_of_not_fingen_is_ascending (I : ideal R) (h : ¬ fingen I) 
  : ∀ n, (ascending_chain_of_not_fingen R I h n).val ⊆ (ascending_chain_of_not_fingen R I h (n + 1)).val :=
begin
  intro,
  { intros x h', destruct (ascending_chain_of_not_fingen R I h n),
    intros S hS heq1,
    destruct (classical.indefinite_description _ (not_fingen_exists_outside R I S h hS)),
    intros y hy heq2, 
    dsimp [ascending_chain_of_not_fingen],
    rw heq1 at *, 
    dsimp [ascending_chain_of_not_fingen._match_1],
    rw heq2 at *,
    dsimp [ascending_chain_of_not_fingen._match_2],
    dunfold finset.cons, simp, simp at h', apply or.inr, assumption }
end

lemma ideals_gen_by_ascending_chain_of_not_fingen_are_ascending (I : ideal R) (h : ¬ fingen I) 
  : is_ascending R (λ n, ideal_gen_by (ascending_chain_of_not_fingen R I h n).val) :=
begin
  intro, simp, apply gen_by_of_subset_is_subset, apply ascending_chain_of_not_fingen_is_ascending
end

theorem Noetherian_iff_ACC : ACC R ↔ Noetherian R := 
begin
constructor,
{
  intros h I,
  by_contra h',
  have asc := ascending_chain_of_not_fingen R I h',
  have := h (λ n, ideal_gen_by (ascending_chain_of_not_fingen R I h' n).val) _,
  { cases this with N H, 
    specialize H (N + 1) (by linarith), 
    simp at H, 
    generalize h1 : ascending_chain_of_not_fingen R I h' N = S,
    cases S with S hS,
    generalize h2 : (classical.indefinite_description _ (not_fingen_exists_outside R I S h' hS)) = y,
    cases y with y hy,
    dsimp [ascending_chain_of_not_fingen] at H, rw h1 at H,
    dsimp [ascending_chain_of_not_fingen._match_1] at H, rw h2 at H,
    dsimp [ascending_chain_of_not_fingen._match_2] at H, rw ← H at hy,
    cases hy, apply hy_right, apply finset_subset_of_ideal_gen_by,
    apply finset.mem_cons_self },
  { apply ideals_gen_by_ascending_chain_of_not_fingen_are_ascending }
},
{
  intros h f hAsc,
  have : directed (⊆) f,
  { intros i j, existsi max i j, constructor;
    apply arbitrary_indices_ascending R f hAsc,
    { apply le_max_left }, { apply le_max_right } },
  specialize h (union_of_directed_family f this),
  cases h with S hS,
  have in_S_implies_in_fn : ∀ y : R, y ∈ S → ∃ n, y ∈ f n,
  { intros y hy,
    have : y ∈ union_of_directed_family f this,
    { rw hS, apply finset_subset_of_ideal_gen_by, assumption },
    { cases this with S' hy', cases hy' with w hy', cases w with i hi, subst hi,
      existsi i, assumption } },
  let S' := multiset.map (λ x : {y // y ∈ S}, @nat.find (λ n, x.val ∈ f n) _ (in_S_implies_in_fn x.1 x.2)) S.attach.val,
  suffices stable : ∀ n, (∀ k, k ∈ S' → k ≤ n) → f n = union_of_directed_family f this,
  { existsi (multiset.sum S'),
    intros n hn, transitivity union_of_directed_family f this;
    rw stable; intros k hk; transitivity S'.sum; try { linarith };
    apply multiset.single_le_sum (λ _ _, nat.zero_le _) k hk, },
  intros n hn,
  ext, constructor; intro h,
  { existsi (f n).carrier, existsi _, assumption, existsi n, refl },
  { rw hS at h, cases h with coeffs h, rw h,
    apply linear_combinations_in_ideal,
    intros y hy,
    let k := @nat.find (λ k', y ∈ f k') _ (in_S_implies_in_fn y hy),
    apply arbitrary_indices_ascending R f hAsc k n,
    { apply hn, rw multiset.mem_map, existsi (subtype.mk y hy), simp },
    { exact nat.find_spec (in_S_implies_in_fn y hy) } },
},
end

