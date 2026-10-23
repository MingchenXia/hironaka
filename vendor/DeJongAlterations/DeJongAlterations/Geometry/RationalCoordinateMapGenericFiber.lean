import DeJongAlterations.Algebra.FunctionFieldDimensionGenericFiber
import DeJongAlterations.Geometry.RationalCoordinateMapGenericFiberDimension
import DeJongAlterations.Geometry.RationalCoordinateMapSeparating
import Mathlib.AlgebraicGeometry.Fiber

/-!
# Actual generic fibres of rational coordinate morphisms

The fibre is Mathlib's scheme-theoretic pullback at the actual generic point
of affine coordinate space. Its ring model is the native generic residue-field
tensor product. Coefficient maps to the canonical function field are built
internally by ordinary localization, with all scalar towers proved.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace DeJongAlterations.Geometry.RationalCoordinateMapGenericFiber

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open RationalCoordinateMap

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {n : ℕ}

/-- The actual generic fibre is canonically the spectrum of its actual residue-field tensor ring. -/
def coordinateFiberIso (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    letI := (coordinateRingMap p r).toAlgebra
    (coordinateMap p r).fiber (⊥ : PrimeSpectrum (MvPolynomial (Fin n) k)) ≅
      Spec (.of ((⊥ : Ideal (MvPolynomial (Fin n) k)).Fiber Γ(X, (coordinateOpen r).1))) := by
  let P := MvPolynomial (Fin n) k
  let A := Γ(X, (coordinateOpen r).1)
  let := (coordinateRingMap p r).toAlgebra
  let g := Spec.map (CommRingCat.ofHom (algebraMap P A))
  let q := (Spec (.of P)).fromSpecResidueField (⊥ : PrimeSpectrum P)
  let e := (coordinateOpen r).2.isoSpec
  have he : coordinateMap p r = e.hom ≫ g := rfl
  let e₁ : (coordinateMap p r).fiber (⊥ : PrimeSpectrum P) ≅
      g.fiber (⊥ : PrimeSpectrum P) :=
    asIso (pullback.map _ _ _ _ e.hom (𝟙 _) (𝟙 _) (by simpa using he)
      (by simp only [Category.comp_id, Category.id_comp]; rfl))
  exact e₁ ≪≫ Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso P A ⊥)

/-- The generic residue field acts on the canonical function field by actual fraction lifting. -/
abbrev coordinateCoefficientFieldAlgebra (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField)
    (hr : letI := SeparableGenericSmoothness.functionFieldAlgebra p; AlgebraicIndependent k r) :
    Algebra (⊥ : Ideal (MvPolynomial (Fin n) k)).ResidueField X.functionField := by
  let P := MvPolynomial (Fin n) k
  let A := Γ(X, (coordinateOpen r).1)
  let K := X.functionField
  let := sectionAlgebra p (coordinateOpen r)
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  let := functionFieldScalarTower p (coordinateOpen r)
  let : Algebra P A := (coordinateRingMap p r).toAlgebra
  let : Algebra P K :=
    ((X.germToFunctionField (coordinateOpen r).1).hom.comp (coordinateRingMap p r)).toAlgebra
  have : IsScalarTower P A K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsFractionRing A K := functionField_isFractionRing_of_isAffineOpen X
    (coordinateOpen r).1 (coordinateOpen r).2
  exact Algebra.FunctionFieldDimension.coefficientFractionAlgebra P A
    (⊥ : Ideal P).ResidueField K (coordinateRingMap_injective p r hr)

/-- Relative transcendence degree one computes the dimension of the actual native generic fibre. -/
theorem genericFiber_dimension_eq (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (r : Fin n → X.functionField)
    (hr : letI := SeparableGenericSmoothness.functionFieldAlgebra p; AlgebraicIndependent k r)
    (d : ℕ)
    (htr : letI := coordinateCoefficientFieldAlgebra p r hr
      Algebra.trdeg (⊥ : Ideal (MvPolynomial (Fin n) k)).ResidueField X.functionField = d) :
    topologicalKrullDim ((coordinateMap p r).fiber
      (genericPoint (Spec (.of (MvPolynomial (Fin n) k))))) = d := by
  let P := MvPolynomial (Fin n) k
  let A := Γ(X, (coordinateOpen r).1)
  let F := (⊥ : Ideal P).ResidueField
  let K := X.functionField
  let := sectionAlgebra p (coordinateOpen r)
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  let := functionFieldScalarTower p (coordinateOpen r)
  let : Algebra P A := (coordinateRingMap p r).toAlgebra
  let : Algebra P K :=
    ((X.germToFunctionField (coordinateOpen r).1).hom.comp (coordinateRingMap p r)).toAlgebra
  have : IsScalarTower P A K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsDomain A := IsIntegral.component_integral (coordinateOpen r).1
  have : IsFractionRing A K := functionField_isFractionRing_of_isAffineOpen X
    (coordinateOpen r).1 (coordinateOpen r).2
  have : Algebra.FiniteType k A := FunctionFieldDimension.affineSections_finiteType p (coordinateOpen r)
  have : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq'
    (coordinateRingMap_comp_algebraMap p r).symm
  have : Algebra.FiniteType P A := Algebra.FiniteType.of_restrictScalars_finiteType k P A
  have hdim := Algebra.FunctionFieldDimension.genericTensor_dimension_eq P A F K
    (coordinateRingMap_injective p r hr) d htr
  rw [genericPoint_eq_bot_of_affine]
  have e := coordinateFiberIso p r
  rw [e.schemeIsoToHomeo.isHomeomorph.topologicalKrullDim_eq]
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans hdim

set_option maxHeartbeats 800000 in
/-- The full finite basis gives relative degree one over the actual generic residue field. -/
theorem relative_trdeg_eq_one (p : X ⟶ Spec (.of k)) (r : Fin (n + 1) → X.functionField)
    (hb : letI := SeparableGenericSmoothness.functionFieldAlgebra p; IsTranscendenceBasis k r) :
    letI := SeparableGenericSmoothness.functionFieldAlgebra p
    let r' := fun i : Fin n ↦ r i.castSucc
    letI := coordinateCoefficientFieldAlgebra p r'
      (hb.1.comp Fin.castSucc (Fin.castSucc_injective n))
    Algebra.trdeg (⊥ : Ideal (MvPolynomial (Fin n) k)).ResidueField X.functionField = 1 := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  let r' := fun i : Fin n ↦ r i.castSucc
  have hr : AlgebraicIndependent k r' := hb.1.comp Fin.castSucc (Fin.castSucc_injective n)
  let P := MvPolynomial (Fin n) k
  let A := Γ(X, (coordinateOpen r').1)
  let F := (⊥ : Ideal P).ResidueField
  let K := X.functionField
  let := sectionAlgebra p (coordinateOpen r')
  let := functionFieldScalarTower p (coordinateOpen r')
  let : Algebra P A := (coordinateRingMap p r').toAlgebra
  let : Algebra P K :=
    ((X.germToFunctionField (coordinateOpen r').1).hom.comp (coordinateRingMap p r')).toAlgebra
  have : IsScalarTower P A K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsFractionRing A K := functionField_isFractionRing_of_isAffineOpen X
    (coordinateOpen r').1 (coordinateOpen r').2
  have : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq'
    (coordinateRingMap_comp_algebraMap p r').symm
  have : IsScalarTower k P K := IsScalarTower.to₁₂₄ k P A K
  let : Algebra k F := ((algebraMap P F).comp (algebraMap k P)).toAlgebra
  have : IsScalarTower k P F := IsScalarTower.of_algebraMap_eq' rfl
  let := Algebra.FunctionFieldDimension.coefficientFractionAlgebra P A F K
    (coordinateRingMap_injective p r' hr)
  let := Algebra.FunctionFieldDimension.coefficientFractionScalarTower P A F K
    (coordinateRingMap_injective p r' hr)
  have : IsScalarTower k F K := IsScalarTower.to₁₃₄ k P F K
  have hF : Algebra.trdeg k F = n := by
    have : Algebra.IsAlgebraic P F := IsLocalization.isAlgebraic F (nonZeroDivisors P)
    rw [← Algebra.FunctionFieldDimension.trdeg_eq_of_isAlgebraic k P F]
    simp [P]
  have hK : Algebra.trdeg k K = (n + 1 : ℕ) := by
    have h := hb.lift_cardinalMk_eq_trdeg
    simpa using h.symm
  have : FaithfulSMul F K := (faithfulSMul_iff_algebraMap_injective F K).mpr
    (algebraMap F K).injective
  have hadd := trdeg_add_eq k F (A := K)
  rw [hF, hK] at hadd
  have hcancel : Algebra.trdeg F K + n = (1 : Cardinal) + n := by
    simpa [add_comm, Nat.cast_add] using hadd
  exact (Cardinal.add_nat_inj n).mp hcancel

/-- The actual generic fibre of the constructed projection has dimension exactly one. -/
theorem genericFiber_dimension_one (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (r : Fin (n + 1) → X.functionField)
    (hb : letI := SeparableGenericSmoothness.functionFieldAlgebra p; IsTranscendenceBasis k r) :
    topologicalKrullDim ((coordinateMap p (fun i : Fin n ↦ r i.castSucc)).fiber
      (genericPoint (Spec (.of (MvPolynomial (Fin n) k))))) = 1 := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  exact genericFiber_dimension_eq p _ (hb.1.comp Fin.castSucc (Fin.castSucc_injective n)) 1
    (relative_trdeg_eq_one p r hb)

/-- A separating finite basis internally constructs a projection with actual generic fibre a curve. -/
theorem exists_separating_projection_genericFiber_dimension_one
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (h : SeparableGenericSmoothness.FunctionFieldSeparablyGenerated p)
    (htr : letI := SeparableGenericSmoothness.functionFieldAlgebra p
      Algebra.Transcendental k X.functionField) :
    letI := SeparableGenericSmoothness.functionFieldAlgebra p
    ∃ n : ℕ, ∃ r : Fin (n + 1) → X.functionField, IsTranscendenceBasis k r ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (Set.range r)) X.functionField ∧
      IsDominant (coordinateMap p (fun i : Fin n ↦ r i.castSucc)) ∧
      topologicalKrullDim ((coordinateMap p (fun i : Fin n ↦ r i.castSucc)).fiber
        (genericPoint (Spec (.of (MvPolynomial (Fin n) k))))) = 1 := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  obtain ⟨n, r, hb, hs, -, hd, -⟩ := exists_separating_projection p h htr
  exact ⟨n, r, hb, hs, hd, genericFiber_dimension_one p r hb⟩

end DeJongAlterations.Geometry.RationalCoordinateMapGenericFiber
