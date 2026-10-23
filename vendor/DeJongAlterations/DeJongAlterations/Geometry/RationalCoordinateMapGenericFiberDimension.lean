import DeJongAlterations.Algebra.FunctionFieldDimension
import DeJongAlterations.Geometry.RationalCoordinateMap

/-!
# Actual scheme dimension from the canonical function field

Scalar compatibility is derived from the structure morphism. Affine-local
dimension bounds descend through the actual specialization-point coheight,
which is unchanged by an open immersion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.FunctionFieldDimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual open-cover bounds descend to scheme dimension, by point coheight. -/
theorem topologicalKrullDim_le_of_openCover (X : Scheme.{u}) (d : ℕ) (𝒰 : X.OpenCover)
    (h : ∀ i, topologicalKrullDim (𝒰.X i) ≤ d) : topologicalKrullDim X ≤ d := by
  change Order.krullDim (IrreducibleCloseds X) ≤ d
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ ?_
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  rw [coheight_eq_of_isOpenImmersion (𝒰.f i)]
  have ho : Order.krullDim (𝒰.X i) ≤ d := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := 𝒰.X i))]
    exact h i
  exact (Order.coheight_le_krullDim y).trans ho

/-- Bounds on all actual nonempty affine coordinate rings bound the scheme itself. -/
theorem topologicalKrullDim_le_of_affine_sections (X : Scheme.{u}) (d : ℕ)
    (h : ∀ U : X.affineOpens, Nonempty U.1 → ringKrullDim Γ(X, U.1) ≤ d) :
    topologicalKrullDim X ≤ d := by
  change Order.krullDim (IrreducibleCloseds X) ≤ d
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (⊤ : X.Opens) from trivial)
      (⊤ : X.Opens).isOpen
  obtain ⟨z, hz⟩ : x ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  rw [← hz, coheight_eq_of_isOpenImmersion hU.fromSpec]
  have hdim : topologicalKrullDim (Spec Γ(X, U)) ≤ d := by
    change topologicalKrullDim (PrimeSpectrum Γ(X, U)) ≤ d
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact h ⟨U, hU⟩ ⟨⟨x, hx⟩⟩
  have ho : Order.krullDim (Spec Γ(X, U)) ≤ d := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Spec Γ(X, U)))]
    exact hdim
  exact (Order.coheight_le_krullDim z).trans ho

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

omit [IsIntegral X] in
/-- Actual finite type on each affine coordinate ring follows from the structure morphism. -/
theorem affineSections_finiteType (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (U : X.affineOpens) :
    letI := RationalCoordinateMap.sectionAlgebra p U
    Algebra.FiniteType k Γ(X, U.1) := by
  apply (p.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
  exact RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2

/-- Every actual nonempty affine chart has the dimension of the canonical function-field degree. -/
theorem affineSections_dimension_eq (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (U : X.affineOpens) [Nonempty U.1] (d : ℕ)
    (htr : letI := SeparableGenericSmoothness.functionFieldAlgebra p
      Algebra.trdeg k X.functionField = d) : ringKrullDim Γ(X, U.1) = d := by
  let := RationalCoordinateMap.sectionAlgebra p U
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  let := RationalCoordinateMap.functionFieldScalarTower p U
  have : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  have : Algebra.FiniteType k Γ(X, U.1) := affineSections_finiteType p U
  have : IsFractionRing Γ(X, U.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  exact Algebra.FunctionFieldDimension.ringKrullDim_eq_of_trdeg_eq_nat
    k Γ(X, U.1) X.functionField d htr

/-- Canonical finite-type field degree determines the actual global scheme dimension. -/
theorem topologicalKrullDim_eq_of_trdeg_eq_nat (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (d : ℕ) (htr : letI := SeparableGenericSmoothness.functionFieldAlgebra p
      Algebra.trdeg k X.functionField = d) : topologicalKrullDim X = d := by
  apply le_antisymm
  · apply topologicalKrullDim_le_of_affine_sections X d
    intro U hU
    let := hU
    exact (affineSections_dimension_eq p U d htr).le
  · let U := RationalCoordinateMap.coordinateOpen (X := X) (fun i : Fin 0 ↦ i.elim0)
    have hd := affineSections_dimension_eq p U d htr
    have hle := U.2.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    change topologicalKrullDim (PrimeSpectrum Γ(X, U.1)) ≤ topologicalKrullDim X at hle
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hd] at hle

/-- Both dimensions are internally produced from an actual nonempty affine coordinate ring. -/
theorem exists_dimension_and_trdeg (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    letI := SeparableGenericSmoothness.functionFieldAlgebra p
    ∃ d : ℕ, topologicalKrullDim X = d ∧ Algebra.trdeg k X.functionField = d := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  let U := RationalCoordinateMap.coordinateOpen (X := X) (fun i : Fin 0 ↦ i.elim0)
  let := RationalCoordinateMap.sectionAlgebra p U
  let := RationalCoordinateMap.functionFieldScalarTower p U
  have : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  have : Algebra.FiniteType k Γ(X, U.1) := affineSections_finiteType p U
  have : IsFractionRing Γ(X, U.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  obtain ⟨d, -, htr⟩ := Algebra.FunctionFieldDimension.exists_dimension_and_trdeg
    k Γ(X, U.1) X.functionField
  exact ⟨d, topologicalKrullDim_eq_of_trdeg_eq_nat p d htr, htr⟩

end DeJongAlterations.Geometry.FunctionFieldDimension
