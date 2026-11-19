import Hironaka.Geometry.CurveFibrationMarkedOpenRestriction
import Hironaka.Geometry.CurveFibrationMarkedOpenSmooth
import Hironaka.Geometry.CurveFibrationBaseChangeFibers

/-! # Actual geometric components and three ORIGINAL smooth boundary points on the literal restricted family. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace Hironaka.Geometry.CurveFibrationMarkedOpen
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual literal restricted field fibre is canonically the ORIGINAL composite-point field fibre. -/
def restrictedFieldFiberIso {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ V.toScheme) :
    pullback (f ∣_ V) a ≅ pullback f (a ≫ V.ι) :=
  ((IsPullback.of_hasPullback (f ∣_ V) a).paste_horiz (isPullback_morphismRestrict f V).flip).isoPullback

@[reassoc (attr := simp)]
theorem restrictedFieldFiberIso_hom_fst {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ V.toScheme) :
    (restrictedFieldFiberIso f V a).hom ≫ pullback.fst f (a ≫ V.ι) =
      pullback.fst (f ∣_ V) a ≫ (f ⁻¹ᵁ V).ι :=
  IsPullback.isoPullback_hom_fst _

/-- The actual restricted-fibre homeomorphism carries EVERY actual component to an ORIGINAL component. -/
theorem restrictedFieldFiber_image_component {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ V.toScheme)
    (C : Set (pullback (f ∣_ V) a : Scheme.{u}))
    (hC : C ∈ irreducibleComponents (pullback (f ∣_ V) a : Scheme.{u})) :
    ((restrictedFieldFiberIso f V a).hom.homeomorph) '' C ∈
      irreducibleComponents (pullback f (a ≫ V.ι) : Scheme.{u}) := by
  let h := (restrictedFieldFiberIso f V a).hom.homeomorph
  rw [h.image_eq_preimage_symm]
  exact preimage_mem_irreducibleComponents hC h.symm.isOpenEmbedding (by
    simpa only [h.symm.surjective.range_eq, Set.inter_univ] using hC.1.nonempty)

/-- ORIGINAL geometric connectedness survives on the SAME literal actual restricted family. -/
theorem restricted_geometricallyConnected {X S : Scheme.{u}}
    (f : X ⟶ S) [GeometricallyConnected f] (V : S.Opens) : GeometricallyConnected (f ∣_ V) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict f V).flip inferInstance

/-- EVERY actual restricted field-fibre component retains its ORIGINAL dimension. -/
theorem restricted_fieldFiber_components_dimension {X S : Scheme.{u}}
    (f : X ⟶ S) (V : S.Opens) (d : ℕ)
    (hd : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) → topologicalKrullDim C = d)
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ V.toScheme)
    (C : Set (pullback (f ∣_ V) a : Scheme.{u}))
    (hC : C ∈ irreducibleComponents (pullback (f ∣_ V) a : Scheme.{u})) :
    topologicalKrullDim C = d :=
  CurveFibrationBaseChange.component_dimension_of_homeomorph
    (restrictedFieldFiberIso f V a).hom.homeomorph d (hd K (a ≫ V.ι)) C hC

/-- EVERY actual restricted geometric component retains three ORIGINAL smooth full-boundary points. -/
theorem restricted_geometric_three_points {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (V : S.Opens) [Smooth (f ∣_ V)]
    (D : X.IdealSheafData)
    (hthree : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) →
      ∃ v : Fin 3 → (pullback f a : Scheme.{u}), Function.Injective v ∧ ∀ i,
        v i ∈ C ∧ pullback.fst f a (v i) ∈ f.smoothLocus ∧
          pullback.fst f a (v i) ∈ D.support) :
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ V.toScheme)
      (C : Set (pullback (f ∣_ V) a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback (f ∣_ V) a : Scheme.{u}) →
      ∃ v : Fin 3 → (pullback (f ∣_ V) a : Scheme.{u}), Function.Injective v ∧ ∀ i,
        v i ∈ C ∧ pullback.fst (f ∣_ V) a (v i) ∈ (f ∣_ V).smoothLocus ∧
          pullback.fst (f ∣_ V) a (v i) ∈ (D.comap (f ⁻¹ᵁ V).ι).support := by
  intro K _ _ a C hC
  let h := (restrictedFieldFiberIso f V a).hom.homeomorph
  obtain ⟨v, hvinj, hv⟩ := hthree K (a ≫ V.ι) (h '' C)
    (restrictedFieldFiber_image_component f V a C hC)
  let w : Fin 3 → (pullback (f ∣_ V) a : Scheme.{u}) := fun i => h.symm (v i)
  refine ⟨w, h.symm.injective.comp hvinj, ?_⟩
  intro i
  have hwi : w i ∈ C := by
    obtain ⟨z, hzC, hzv⟩ := (hv i).1
    change h.symm (v i) ∈ C
    rw [← hzv, h.symm_apply_apply]
    exact hzC
  have hwX : pullback.fst f (a ≫ V.ι) (v i) =
      (pullback.fst (f ∣_ V) a ≫ (f ⁻¹ᵁ V).ι) (w i) := by
    have H := congrArg (fun m => m (w i)) (restrictedFieldFiberIso_hom_fst f V a)
    change pullback.fst f (a ≫ V.ι) (h (h.symm (v i))) = _ at H
    simpa only [h.apply_symm_apply] using H
  refine ⟨hwi, ?_, ?_⟩
  · rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  · rw [Scheme.IdealSheafData.support_comap]
    change (pullback.fst (f ∣_ V) a ≫ (f ⁻¹ᵁ V).ι) (w i) ∈ D.support
    rw [← hwX]
    exact (hv i).2.2

end Hironaka.Geometry.CurveFibrationMarkedOpen
