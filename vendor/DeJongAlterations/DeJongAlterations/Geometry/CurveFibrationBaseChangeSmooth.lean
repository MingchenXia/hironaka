import DeJongAlterations.Geometry.CurveFibrationBaseChangeReduction
import DeJongAlterations.Geometry.ImperfectFieldExample

/-!
# The actual whole reduction preserves the original smooth locus

The actual smooth pullback is reduced over an integral base. The
original reduction restricts to a surjective closed immersion into this
reduced open and therefore is an actual scheme isomorphism there.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S Y T W : Scheme.{u}}

/-- Actual smooth affine charts over a field are reduced. -/
theorem isReduced_of_smooth_field {K : Type u} [Field K]
    (p : T ⟶ Spec (.of K)) [Smooth p] : IsReduced T := by
  let : ∀ i, IsReduced (T.affineCover.X i) := by
    intro i
    let U := T.affineCover.X i
    let a := U.isoSpec.inv ≫ T.affineCover.f i ≫ p
    obtain ⟨φ, hφ⟩ := Spec.map_surjective a
    let : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
    let : Algebra K Γ(U, ⊤) := φ.hom.toAlgebra
    let : Algebra.Smooth K Γ(U, ⊤) := RingHom.smooth_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp inferInstance)
    let : _root_.IsReduced Γ(U, ⊤) := ImperfectFieldExample.isReduced_of_smooth K Γ(U, ⊤)
    let : IsReduced (Spec Γ(U, ⊤)) := inferInstance
    exact isReduced_of_isOpenImmersion U.isoSpec.hom
  exact IsReduced.of_openCover T T.affineCover

/-- Native geometric reducedness is derived from actual arbitrary smooth field fibres. -/
theorem smooth_geometricallyReduced (p : T ⟶ W) [Smooth p] : GeometricallyReduced p where
  geometrically_isReduced := by
    intro K _ y Q a b h
    let : Smooth b := MorphismProperty.of_isPullback h inferInstance
    exact isReduced_of_smooth_field b

/-- Smoothness over an integral base gives actual reducedness without Noetherianity. -/
theorem isReduced_of_smooth_integral_base [IsIntegral W] (p : T ⟶ W) [Smooth p] :
    IsReduced T := by
  let : GeometricallyReduced p := smooth_geometricallyReduced p
  let : Finite (irreducibleComponents W) := Set.finite_coe_iff.mpr (by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _)
  exact GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents p

/-- The original whole reduction is an actual isomorphism above the original smooth locus. -/
theorem reductionι_smoothOpen_isIso [IsIntegral Y]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (g : Y ⟶ S) :
    IsIso (reductionι f g ∣_ ((pullback.fst f g) ⁻¹ᵁ f.smoothLocus)) := by
  let U := (pullback.fst f g) ⁻¹ᵁ f.smoothLocus
  let : Smooth (U.ι ≫ pullback.snd f g) := smooth_originalLocus f g
  let : IsReduced U.toScheme := isReduced_of_smooth_integral_base (U.ι ≫ pullback.snd f g)
  let : Surjective (reductionι f g ∣_ U) := ⟨by
    intro y
    obtain ⟨x, hx⟩ := (reductionι f g).surjective y.val
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change reductionι f g x ∈ U
      rw [hx]
      exact y.property
    · apply Subtype.ext
      simpa only [morphismRestrict_base_coe] using hx⟩
  exact isIso_of_isClosedImmersion_of_surjective _

/-- The restriction of the original reduced projection above the original smooth locus is smooth. -/
theorem smooth_reduced_originalLocus [IsIntegral Y]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (g : Y ⟶ S) :
    Smooth (((reductionι f g) ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ f.smoothLocus)).ι ≫
      (reductionι f g ≫ pullback.snd f g)) := by
  let U := (pullback.fst f g) ⁻¹ᵁ f.smoothLocus
  let : IsIso (reductionι f g ∣_ U) := reductionι_smoothOpen_isIso f g
  let : Smooth (U.ι ≫ pullback.snd f g) := smooth_originalLocus f g
  have h : Smooth ((reductionι f g ∣_ U) ≫ (U.ι ≫ pullback.snd f g)) := inferInstance
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at h
  exact h

/-- The same ORIGINAL pulled-back smooth locus lies in the actual reduced projection's smooth locus. -/
theorem originalLocus_le_reduced_smoothLocus [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (g : Y ⟶ S) :
    (reductionι f g) ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ f.smoothLocus) ≤
      (reductionι f g ≫ pullback.snd f g).smoothLocus := by
  let V := (reductionι f g) ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ f.smoothLocus)
  let : Smooth (V.ι ≫ (reductionι f g ≫ pullback.snd f g)) := smooth_reduced_originalLocus f g
  have H : V.ι ⁻¹ᵁ (reductionι f g ≫ pullback.snd f g).smoothLocus = ⊤ := by
    rw [Scheme.Hom.preimage_smoothLocus_eq]
    exact Scheme.Hom.smoothLocus_eq_top _
  intro x hx
  have h : (⟨x, hx⟩ : V) ∈
      V.ι ⁻¹ᵁ (reductionι f g ≫ pullback.snd f g).smoothLocus := by rw [H]; trivial
  exact h


/-- Original fibrewise smooth density transports to the actual reduced projection on every field fibre. -/
theorem reducedSecond_smoothLocus_fieldFiber_dense [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (hsm : ∀ (K : Type u) [Field K] (e : Spec (.of K) ⟶ S),
      Dense ((pullback.fst f e) ⁻¹' (f.smoothLocus : Set X)))
    (g : Y ⟶ S) {K : Type u} [Field K] (e : Spec (.of K) ⟶ Y) :
    Dense ((pullback.fst (reductionι f g ≫ pullback.snd f g) e) ⁻¹'
      ((reductionι f g ≫ pullback.snd f g).smoothLocus : Set (reducedPullback f g))) := by
  let p := pullback.snd f g
  let q := reductionι f g ≫ p
  let b := reductionBaseChangeMap f g e
  have hraw : Dense ((pullback.fst p e ≫ pullback.fst f g) ⁻¹'
      (f.smoothLocus : Set X)) :=
    dense_originalLocus_of_isPullback f (e ≫ g) (hsm _ (e ≫ g))
      (pullback.fst p e ≫ pullback.fst f g) (pullback.snd p e)
      ((IsPullback.of_hasPullback p e).paste_horiz (IsPullback.of_hasPullback f g))
  have hd := hraw.preimage ((reductionBaseChangeMap_isHomeomorph f g e).homeomorph b).isOpenMap
  have hred : Dense ((pullback.fst q e) ⁻¹'
      (((reductionι f g) ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ f.smoothLocus)) :
        Set (reducedPullback f g))) := by
    convert hd using 1
    ext z
    change (pullback.fst q e ≫ reductionι f g ≫ pullback.fst f g) z ∈ f.smoothLocus ↔
      (b ≫ pullback.fst p e ≫ pullback.fst f g) z ∈ f.smoothLocus
    rw [← Category.assoc, (reductionBaseChangeMap_isPullback f g e).w, Category.assoc]
  exact hred.mono (Set.preimage_mono (originalLocus_le_reduced_smoothLocus f g))


/-- Original generic smoothness survives the actual dominant whole-pullback base change. -/
theorem genericFiber_smooth [IsIntegral S] [IsIntegral Y]
    (f : X ⟶ S) [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    (g : Y ⟶ S) [IsDominant g] :
    Smooth ((pullback.snd f g).fiberToSpecResidueField (genericPoint Y)) := by
  have H := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) (genericPoint Y)
  have hf : Smooth (f.fiberToSpecResidueField (g (genericPoint Y))) := by
    rw [genericPoint_map_of_isDominant g]
    infer_instance
  exact MorphismProperty.of_isPullback H hf

/-- The SAME actual whole reduction retains smoothness of the native generic fibre. -/
theorem reducedSecond_genericFiber_smooth [IsIntegral S] [IsIntegral Y]
    (f : X ⟶ S) [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    (g : Y ⟶ S) [IsDominant g] :
    Smooth ((reductionι f g ≫ pullback.snd f g).fiberToSpecResidueField (genericPoint Y)) := by
  let e := Y.fromSpecResidueField (genericPoint Y)
  let p := pullback.snd f g
  let b := reductionBaseChangeMap f g e
  let : Smooth (p.fiberToSpecResidueField (genericPoint Y)) := genericFiber_smooth f g
  let : IsReduced (pullback (pullback.snd f g) e : Scheme.{u}) := by
    change IsReduced (p.fiber (genericPoint Y))
    exact isReduced_of_smooth_field (p.fiberToSpecResidueField (genericPoint Y))
  let : IsClosedImmersion b :=
    MorphismProperty.of_isPullback (reductionBaseChangeMap_isPullback f g e) inferInstance
  let : Surjective b :=
    MorphismProperty.of_isPullback (reductionBaseChangeMap_isPullback f g e) inferInstance
  let : IsIso b := isIso_of_isClosedImmersion_of_surjective b
  have H : Smooth (b ≫ p.fiberToSpecResidueField (genericPoint Y)) := inferInstance
  simpa [b, p, e, reductionBaseChangeMap, Scheme.Hom.fiberToSpecResidueField] using H

end DeJongAlterations.Geometry.CurveFibrationBaseChange
