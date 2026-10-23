import DeJongAlterations.Geometry.SNCSubdivisor

/-!
# Actual component selection in the boundary enlargement reduction

A closed pure codimension-one subset of the native SNC support is
identified with an internally selected finite family of actual components.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.BoundaryEnlargement

open Scheme.IdealSheafData SNCSubdivisorTopology SNCSubdivisorComponent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}}

/-- Every actual ambient irreducible subset of a native support lies in an actual component. -/
theorem exists_component_containing
    (D : X.IdealSheafData) (T : Set X) (hT : IsIrreducible T)
    (hTD : T ⊆ D.support) :
    ∃ C : DivisorComponent D, T ⊆ (C.val : Set X) := by
  let : IrreducibleSpace T := Subtype.irreducibleSpace hT
  let g : T → D.support := fun t ↦ ⟨t.val, hTD t.property⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk _
  have hgi : IsIrreducible (g '' Set.univ) :=
    (IrreducibleSpace.isIrreducible_univ T).image g hg.continuousOn
  obtain ⟨S, hS, hgS⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (g '' Set.univ) hgi
  refine ⟨divisorComponentOf D S hS, ?_⟩
  intro x hx
  let t : T := ⟨x, hx⟩
  exact ⟨g t, hgS ⟨t, Set.mem_univ t, rfl⟩, rfl⟩

/-- Pure codimension one computes coheight one at an actual component's actual generic point. -/
theorem component_genericPoint_coheight
    (E : X.IdealSheafData) (hE : HasPureCodimension E.support 1) (C : DivisorComponent E) :
    Order.coheight (SNCLocality.divisorComponent_isIrreducible E C).genericPoint = 1 := by
  let hC := SNCLocality.divisorComponent_isIrreducible E C
  have hgeneric := hC.isGenericPoint_genericPoint C.val.isClosed
  obtain ⟨S, hS, hSC⟩ := C.property
  have hdim := hE S hS hC.genericPoint (by rw [hSC]; exact hgeneric)
  rw [ringKrullDim_stalk_eq_coheight] at hdim
  exact_mod_cast hdim

/-- Native singleton SNC codimension computes the actual component generic point's coheight. -/
theorem snc_component_genericPoint_coheight
    (D : X.IdealSheafData) (hD : IsStrictNormalCrossings D) (C : DivisorComponent D) :
    Order.coheight (SNCLocality.divisorComponent_isIrreducible D C).genericPoint = 1 := by
  classical
  let hC := SNCLocality.divisorComponent_isIrreducible D C
  have hgeneric := hC.isGenericPoint_genericPoint C.val.isClosed
  have hcodim : HasPureCodimension C.val 1 := by
    simpa only [componentIntersection, Finset.mem_singleton, iSup_iSup_eq_left,
      ReducedClosedSubscheme.support_vanishingIdeal, Finset.card_singleton] using
      hD.intersectionsCodimension {C} (Finset.singleton_nonempty C)
  let : IrreducibleSpace C.val := Subtype.irreducibleSpace hC
  have hcomp : (Set.univ : Set C.val) ∈ irreducibleComponents C.val := by
    simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff]
  have hg : IsGenericPoint hC.genericPoint ((Subtype.val : C.val → X) '' Set.univ) := by
    have hi : (Subtype.val : C.val → X) '' Set.univ = (C.val : Set X) := by
      ext x
      simp
    rw [hi]
    exact hgeneric
  have hdim := hcodim Set.univ hcomp hC.genericPoint hg
  rw [ringKrullDim_stalk_eq_coheight] at hdim
  exact_mod_cast hdim

/-- Containment of actual codimension-one components in an SNC component forces equality. -/
theorem component_eq_of_subset
    (E : X.IdealSheafData) (hE : HasPureCodimension E.support 1)
    (D : X.IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C : DivisorComponent E) (C' : DivisorComponent D)
    (hCC' : (C.val : Set X) ⊆ (C'.val : Set X)) : C.val = C'.val := by
  let hC := SNCLocality.divisorComponent_isIrreducible E C
  let hC' := SNCLocality.divisorComponent_isIrreducible D C'
  have hg := hC.isGenericPoint_genericPoint C.val.isClosed
  have hg' := hC'.isGenericPoint_genericPoint C'.val.isClosed
  have hco : Order.coheight hC.genericPoint = 1 := component_genericPoint_coheight E hE C
  have hco' : Order.coheight hC'.genericPoint = 1 := snc_component_genericPoint_coheight D hD C'
  have hle : hC.genericPoint ≤ hC'.genericPoint := hg'.specializes (hCC' hg.mem)
  have heq : hC.genericPoint = hC'.genericPoint := by
    by_contra hne
    have hlt : hC.genericPoint < hC'.genericPoint := by
      refine lt_iff_le_not_ge.mpr ⟨hle, ?_⟩
      intro hge
      exact hne (((show hC.genericPoint ⤳ hC'.genericPoint from hge).antisymm
        (show hC'.genericPoint ⤳ hC.genericPoint from hle)).eq)
    have h := Order.coheight_add_one_le hlt
    rw [hco, hco'] at h
    norm_num at h
  apply Closeds.ext
  rw [← hg.def, ← hg'.def, heq]

/-- The internally selected actual SNC components contained in the smaller closed subset. -/
def containedFamily [NoetherianSpace X] (D : X.IdealSheafData) (T : Closeds X) :
    Finset (DivisorComponent D) := by
  classical
  let : Fintype (DivisorComponent D) := Fintype.ofFinite _
  exact Finset.univ.filter (fun C ↦ C.val ≤ T)

theorem mem_containedFamily [NoetherianSpace X] (D : X.IdealSheafData) (T : Closeds X)
    (C : DivisorComponent D) : C ∈ containedFamily D T ↔ C.val ≤ T := by
  classical
  simp only [containedFamily, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The pure codimension-one subset is exactly the actual internally selected component union. -/
theorem selectedSupport_containedFamily_eq [NoetherianSpace X]
    (D : X.IdealSheafData) (hD : IsStrictNormalCrossings D)
    (T : Closeds X) (hT : HasPureCodimension T 1) (hTD : T ≤ D.support) :
    selectedSupport D (containedFamily D T) = T := by
  apply le_antisymm
  · intro x hx
    obtain ⟨C, hC, hxC⟩ := (mem_selectedSupport D (containedFamily D T) x).mp hx
    exact (mem_containedFamily D T C).mp hC hxC
  · intro x hx
    let E := vanishingIdeal T
    let z : E.support := ⟨x, hx⟩
    let C := divisorComponentOf E (irreducibleComponent z)
      (irreducibleComponent_mem_irreducibleComponents z)
    have hxC : x ∈ (C.val : Set X) := ⟨z, mem_irreducibleComponent, rfl⟩
    obtain ⟨C', hCC'⟩ := exists_component_containing D (C.val : Set X)
      (SNCLocality.divisorComponent_isIrreducible E C)
      (fun _ hy ↦ hTD (component_le_support E C hy))
    have heq : C.val = C'.val := component_eq_of_subset E hT D hD C C' hCC'
    have hC'T : C'.val ≤ T := by
      rw [← heq]
      exact component_le_support E C
    apply (mem_selectedSupport D (containedFamily D T) x).mpr
    exact ⟨C', (mem_containedFamily D T C').mpr hC'T, by rw [← heq]; exact hxC⟩

/-- The native vanishing ideal of any actual pure codimension-one subset of SNC is SNC. -/
theorem isStrictNormalCrossings_of_pureCodimension_subset
    [IsLocallyNoetherian X] [NoetherianSpace X]
    (D : X.IdealSheafData) (hD : IsStrictNormalCrossings D)
    (T : Closeds X) (hT : HasPureCodimension T 1) (hTD : T ≤ D.support) :
    IsStrictNormalCrossings (vanishingIdeal T) := by
  have h := SNCSubdivisor.isStrictNormalCrossings_selected D hD (containedFamily D T)
  simpa only [selectedDivisor, selectedSupport_containedFamily_eq D hD T hT hTD] using h

end DeJongAlterations.Geometry.BoundaryEnlargement
