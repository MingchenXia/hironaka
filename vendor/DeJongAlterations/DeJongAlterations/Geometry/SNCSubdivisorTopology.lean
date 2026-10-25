import DeJongAlterations.Geometry.SNCSubdivisorComponent

/-!
# Actual components of finite reduced subunions

The selected reduced closed subscheme and its component embedding are
constructed from the original native irreducible components.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.SNCSubdivisorTopology

open Scheme.IdealSheafData SNCSubdivisorComponent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}}

/-- The actual finite closed union of selected native components. -/
def selectedSupport (D : X.IdealSheafData) (F : Finset (DivisorComponent D)) : Closeds X :=
  F.sup Subtype.val

theorem mem_selectedSupport (D : X.IdealSheafData) (F : Finset (DivisorComponent D)) (x : X) :
    x ∈ selectedSupport D F ↔ ∃ C ∈ F, x ∈ C.val := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    change False ↔ ∃ C ∈ (∅ : Finset (DivisorComponent D)), x ∈ C.val
    simp
  | @insert C F hC ih =>
    rw [selectedSupport, Finset.sup_insert]
    change (x ∈ (C.val : Set X) ∨ x ∈ selectedSupport D F) ↔ _
    constructor
    · rintro (hxC | hxF)
      · exact ⟨C, Finset.mem_insert_self _ _, hxC⟩
      · obtain ⟨C₀, hC₀, hxC₀⟩ := ih.mp hxF
        exact ⟨C₀, Finset.mem_insert_of_mem hC₀, hxC₀⟩
    · rintro ⟨C₀, hC₀, hxC₀⟩
      rcases Finset.mem_insert.mp hC₀ with rfl | hC₀
      · exact Or.inl hxC₀
      · exact Or.inr (ih.mpr ⟨C₀, hC₀, hxC₀⟩)

/-- The full actual reduced ideal of the chosen component union. -/
def selectedDivisor (D : X.IdealSheafData) (F : Finset (DivisorComponent D)) :
    X.IdealSheafData := vanishingIdeal (selectedSupport D F)

theorem selectedDivisor_support (D : X.IdealSheafData) (F : Finset (DivisorComponent D)) :
    (selectedDivisor D F).support = selectedSupport D F := rfl

theorem selectedSupport_le (D : X.IdealSheafData) (F : Finset (DivisorComponent D)) :
    selectedSupport D F ≤ D.support := by
  intro x hx
  obtain ⟨C, _, hxC⟩ := (mem_selectedSupport D F x).mp hx
  exact component_le_support D C hxC

theorem selectedDivisor_isReduced (D : X.IdealSheafData) (F : Finset (DivisorComponent D)) :
    IsReduced (selectedDivisor D F).subscheme :=
  ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme _

/-- Native component maximality holds for actual ambient irreducible subsets. -/
theorem component_maximal (D : X.IdealSheafData) (C : DivisorComponent D)
    (T : Set X) (hT : IsIrreducible T)
    (hCT : (C.val : Set X) ⊆ T) (hTD : T ⊆ D.support) :
    T ⊆ (C.val : Set X) := by
  obtain ⟨S, hS, hSC⟩ := C.property
  let : IrreducibleSpace T := Subtype.irreducibleSpace hT
  let g : T → D.support := fun t ↦ ⟨t.val, hTD t.property⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk _
  have hgi : IsIrreducible (g '' Set.univ) :=
    (IrreducibleSpace.isIrreducible_univ T).image g hg.continuousOn
  have hSg : S ⊆ g '' Set.univ := by
    intro z hz
    have hzC : z.val ∈ (C.val : Set X) := hSC ▸ Set.mem_image_of_mem Subtype.val hz
    exact ⟨⟨z.val, hCT hzC⟩, Set.mem_univ _, Subtype.ext rfl⟩
  have hgS := hS.2 hgi hSg
  intro x hx
  rw [← hSC]
  let t : T := ⟨x, hx⟩
  exact ⟨g t, hgS ⟨t, Set.mem_univ t, rfl⟩, rfl⟩

/-- Every new actual component equals an actually selected original component. -/
theorem component_eq_selected (D : X.IdealSheafData) (F : Finset (DivisorComponent D))
    (C : DivisorComponent (selectedDivisor D F)) :
    ∃ C₀ ∈ F, C.val = C₀.val := by
  classical
  have hirr := SNCLocality.divisorComponent_isIrreducible (selectedDivisor D F) C
  let G : Finset (Set X) := F.image (fun C₀ ↦ (C₀.val : Set X))
  have hcover : (C.val : Set X) ⊆ ⋃₀ (G : Set (Set X)) := by
    intro x hx
    have hxE := component_le_support (selectedDivisor D F) C hx
    obtain ⟨C₀, hC₀, hxC₀⟩ := (mem_selectedSupport D F x).mp hxE
    exact Set.mem_sUnion.mpr ⟨C₀.val, Finset.mem_image.mpr ⟨C₀, hC₀, rfl⟩, hxC₀⟩
  obtain ⟨T, hTG, hCT⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp hirr G (by
      intro T hT
      obtain ⟨C₀, _, rfl⟩ := Finset.mem_image.mp hT
      exact C₀.val.isClosed) hcover
  obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hTG
  have hCE : (C₀.val : Set X) ⊆ (selectedDivisor D F).support := by
    intro x hx
    exact (mem_selectedSupport D F x).mpr ⟨C₀, hC₀, hx⟩
  have heq : (C.val : Set X) = C₀.val :=
    Set.Subset.antisymm hCT
      (component_maximal (selectedDivisor D F) C (C₀.val : Set X)
        (SNCLocality.divisorComponent_isIrreducible D C₀) hCT hCE)
  exact ⟨C₀, hC₀, Closeds.ext heq⟩

/-- Every selected original component is an actual component of the reduced selected union. -/
theorem selected_eq_component (D : X.IdealSheafData) (F : Finset (DivisorComponent D))
    (C : DivisorComponent D) (hCF : C ∈ F) :
    ∃ C' : DivisorComponent (selectedDivisor D F), C'.val = C.val := by
  let E := selectedDivisor D F
  have hCE : (C.val : Set X) ⊆ E.support := by
    intro x hx
    exact (mem_selectedSupport D F x).mpr ⟨C, hCF, hx⟩
  let : IrreducibleSpace C.val :=
    Subtype.irreducibleSpace (SNCLocality.divisorComponent_isIrreducible D C)
  let g : C.val → E.support := fun x ↦ ⟨x.val, hCE x.property⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk _
  have hgi : IsIrreducible (g '' Set.univ) :=
    (IrreducibleSpace.isIrreducible_univ C.val).image g hg.continuousOn
  obtain ⟨S, hS, hgS⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (g '' Set.univ) hgi
  let C' := divisorComponentOf E S hS
  have hCC' : (C.val : Set X) ⊆ (C'.val : Set X) := by
    intro x hx
    let t : C.val := ⟨x, hx⟩
    exact ⟨g t, hgS ⟨t, Set.mem_univ t, rfl⟩, rfl⟩
  have hC'C : (C'.val : Set X) ⊆ (C.val : Set X) :=
    component_maximal D C (C'.val : Set X) (SNCLocality.divisorComponent_isIrreducible E C')
      hCC' (fun _ hx ↦ selectedSupport_le D F (component_le_support E C' hx))
  exact ⟨C', Closeds.ext (Set.Subset.antisymm hC'C hCC')⟩

/-- Embed the actual new component set into the actual original component set. -/
def componentEmbedding (D : X.IdealSheafData) (F : Finset (DivisorComponent D)) :
    DivisorComponent (selectedDivisor D F) ↪ DivisorComponent D where
  toFun C := (component_eq_selected D F C).choose
  inj' C C' h := by
    apply Subtype.ext
    have hC := (component_eq_selected D F C).choose_spec.2
    have hC' := (component_eq_selected D F C').choose_spec.2
    exact hC.trans ((congrArg Subtype.val h).trans hC'.symm)

theorem componentEmbedding_mem (D : X.IdealSheafData) (F : Finset (DivisorComponent D))
    (C : DivisorComponent (selectedDivisor D F)) : componentEmbedding D F C ∈ F :=
  (component_eq_selected D F C).choose_spec.1

theorem componentEmbedding_val (D : X.IdealSheafData) (F : Finset (DivisorComponent D))
    (C : DivisorComponent (selectedDivisor D F)) :
    (componentEmbedding D F C).val = C.val :=
  (component_eq_selected D F C).choose_spec.2.symm

/-- All new scheme-theoretic intersections are literally original intersections. -/
theorem componentIntersection_eq (D : X.IdealSheafData) (F : Finset (DivisorComponent D))
    (J : Finset (DivisorComponent (selectedDivisor D F))) :
    componentIntersection (selectedDivisor D F) J =
      componentIntersection D (J.map (componentEmbedding D F)) := by
  classical
  simp only [componentIntersection, Finset.map_eq_image, Finset.iSup_finset_image,
    componentEmbedding_val]

end DeJongAlterations.Geometry.SNCSubdivisorTopology
