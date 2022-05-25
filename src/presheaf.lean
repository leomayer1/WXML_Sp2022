import topology.basic

structure presheaf (X : Type) [topological_space X] :=
(sections_on : {V : set X | is_open V} → Type)
(restrict : ∀ U V : {V : set X | is_open V}, U.val ⊆ V.val → sections_on V → sections_on U)
(functorality : ∀ (U V W : {V : set X | is_open V}) (h1 : U.val ⊆ V.val) (h2 : V.val ⊆ W.val)
                (s : sections_on W), restrict U V h1 (restrict V W h2 s) = restrict U W (λ x h, h2 (h1 h)) s)

class abelian_presheaf {X : Type} [topological_space X] (F : presheaf X) :=
(ab_group_structure : ∀ U : {V : set X | is_open V}, add_comm_group (F.sections_on U))

-- instance sections_abelian {X : Type} [topological_space X] (F : presheaf X) (U : {V : set X | is_open V}) 
--         [C : abelian_presheaf F] : add_comm_group (F.sections_on U) := abelian_presheaf.ab_group_structure U

local attribute [instance] abelian_presheaf.ab_group_structure

def zero_sections { X : Type } [topological_space X] (F : presheaf X) [abelian_presheaf F] : F.sections_on ⟨set.univ, is_open_univ⟩ :=
0

-- structure morphism (X : Type) [topological_space X] (F G : presheaf X) : Type :=
-- (morphism_on : ∀ U : {V : set X | is_open V}, F.sections_on U → G.sections_on U)
-- (naturality : ∀ (U V : {V : set X | is_open V}) (h : U.val ⊆ V.val) (s : F.sections_on V), 
--               morphism_on V (F.restrict U V h s) = G.restrict U V h (morphism_on U s))

-- def kernel (X : Type) [topological_space X] (F : presheaf X) [abelian_presheaf F] : presheaf X := {
--   sections_on := λ V, add_monoid.kernel
-- }