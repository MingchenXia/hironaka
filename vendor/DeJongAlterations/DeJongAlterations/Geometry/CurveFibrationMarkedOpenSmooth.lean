import DeJongAlterations.Geometry.GenericFiberIntegral
import DeJongAlterations.Geometry.GenericSmoothness

/-! # Actual generic-fibre smoothness spreads to a dense base open under properness. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace DeJongAlterations.Geometry.CurveFibrationMarkedOpen
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- EVERY original point over the native generic point lies in the ORIGINAL relative smooth locus. -/
theorem genericFiber_le_smoothLocus {X S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    (x : X) (hx : f x = genericPoint S) : x ∈ f.smoothLocus := by
  let e := S.fromSpecResidueField (genericPoint S)
  let i := f.fiberι (genericPoint S)
  let q := f.fiberToSpecResidueField (genericPoint S)
  let z := (f.fiberHomeo (genericPoint S)).symm ⟨x, hx⟩
  have hiz : i z = x := f.fiberι_fiberHomeo_symm _ _
  suffices i z ∈ f.smoothLocus by simpa only [hiz] using this
  rw [Scheme.Hom.mem_smoothLocus]
  let : Flat e := GenericFiberIntegral.fromSpecResidueField_flat S
  let : Flat i := by change Flat (pullback.fst f e); infer_instance
  let : IsIso (i.stalkMap z) := GenericFiberIntegral.stalkMap_isIso_of_flat_preimmersion i z
  let : IsIso (e.stalkMap (q z)) :=
    GenericFiberIntegral.stalkMap_isIso_of_flat_preimmersion e (q z)
  have hq : (q.stalkMap z).hom.FormallySmooth := by
    apply Scheme.Hom.mem_smoothLocus.mp
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  have H : ((i ≫ f).stalkMap z).hom.FormallySmooth := by
    have ht : i ≫ f = q ≫ e := pullback.condition
    rw [ht, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso
      (e.stalkMap (q z)) (q.stalkMap z)).mpr hq
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at H
  exact (RingHom.FormallySmooth.respectsIso.cancel_right_isIso
    (f.stalkMap (i z)) (i.stalkMap z)).mp H

/-- Actual target restriction is smooth when its ORIGINAL source preimage lies in the ORIGINAL smooth locus. -/
theorem smooth_morphismRestrict_of_preimage_le_smoothLocus {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (V : S.Opens)
    (hV : f ⁻¹ᵁ V ≤ f.smoothLocus) : Smooth (f ∣_ V) := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro z _
  rw [Scheme.Hom.mem_smoothLocus]
  let i := (f ⁻¹ᵁ V).ι
  have hf : (f.stalkMap (i z)).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (hV z.property)
  have H : ((i ≫ f).stalkMap z).hom.FormallySmooth := by
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_right_isIso
      (f.stalkMap (i z)) (i.stalkMap z)).mpr hf
  change (((f ⁻¹ᵁ V).ι ≫ f).stalkMap z).hom.FormallySmooth at H
  rw [← morphismRestrict_ι, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at H
  exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    (V.ι.stalkMap ((f ∣_ V) z)) ((f ∣_ V).stalkMap z)).mp H

/-- Properness and ORIGINAL smooth generic fibre internally produce an actual dense smooth BASE open. -/
theorem exists_nonempty_dense_smooth_base_open {X S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [IsProper f]
    [Smooth (f.fiberToSpecResidueField (genericPoint S))] :
    ∃ V : S.Opens, Nonempty V ∧ Dense (V : Set S) ∧
      f ⁻¹ᵁ V ≤ f.smoothLocus ∧ Smooth (f ∣_ V) := by
  let B : Set X := (f.smoothLocus : Set X)ᶜ
  let V : S.Opens := ⟨(f '' B)ᶜ, (f.isClosedMap B f.smoothLocus.isOpen.isClosed_compl).isOpen_compl⟩
  have hη : genericPoint S ∈ V := by
    rintro ⟨x, hxB, hxη⟩
    exact hxB (genericFiber_le_smoothLocus f x hxη)
  have hV : f ⁻¹ᵁ V ≤ f.smoothLocus := by
    intro x hx
    by_contra hbad
    exact hx ⟨x, hbad, rfl⟩
  exact ⟨V, ⟨⟨genericPoint S, hη⟩⟩, V.isOpen.dense ⟨genericPoint S, hη⟩, hV,
    smooth_morphismRestrict_of_preimage_le_smoothLocus f V hV⟩

end DeJongAlterations.Geometry.CurveFibrationMarkedOpen
