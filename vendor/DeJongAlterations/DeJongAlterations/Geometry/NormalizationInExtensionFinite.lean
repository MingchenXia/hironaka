import DeJongAlterations.Geometry.NormalizationInExtensionGluing
import DeJongAlterations.Geometry.NormalizationFinite

/-! # Normality, integrality and finiteness in the specified extension -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.NormalizationInExtension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L]

attribute [local instance] sectionsAlgebra

/-- The native chart coefficient map is injective because actual germs and field maps are. -/
theorem affineCoefficient_injective (U : NonemptyAffineOpen X) :
    Function.Injective (algebraMap Γ(X, U.1.1) (closureRing L U)) := by
  intro a b hab
  apply X.germToFunctionField_injective U.1.1
  apply (algebraMap X.functionField L).injective
  exact congrArg (fun c : closureRing L U => (c : L)) hab

/-- Integral lying over proves actual affine chart surjectivity without separability. -/
theorem affineStructure_surjective (U : NonemptyAffineOpen X) :
    Function.Surjective (affineStructure L U) :=
  (show (algebraMap Γ(X, U.1.1) (closureRing L U)).IsIntegral from
    algebraMap_isIntegral_iff.mpr inferInstance).comap_surjective
      (affineCoefficient_injective L U)

/-- Every genuine common-field affine normalization chart is integral. -/
theorem chart_isIntegral (U : NonemptyAffineOpen X) :
    IsIntegral (Spec (.of (closureRing L U))) := by
  infer_instance

/-- Each actual affine normalization chart maps dominantly to the original scheme. -/
theorem chartInclusion_comp_isDominant (U : NonemptyAffineOpen X) :
    IsDominant (chartInclusion X L U ≫ normalizationStructure X L) := by
  rw [chartInclusion_structure]
  let : IsDominant (affineStructure L U) :=
    ⟨(affineStructure_surjective L U).denseRange⟩
  let := NormalizationFinite.affineCoordinate_isDominant ⟨U.1.1, U.1.2⟩
  infer_instance

/-- The native affine chart images intersect inside the actual normalization. -/
theorem chartInclusion_not_disjoint (U V : NonemptyAffineOpen X) :
    ¬ Disjoint (chartInclusion X L U).opensRange (chartInclusion X L V).opensRange := by
  let := chartInclusion_comp_isDominant L U
  obtain ⟨p, hp⟩ := (chartInclusion X L U ≫ normalizationStructure X L).denseRange.exists_mem_open
    V.1.1.isOpen (Set.nonempty_coe_sort.mp (inferInstance : Nonempty V.1.1))
  have hpV : chartInclusion X L U p ∈ (chartInclusion X L V).opensRange := by
    rw [chartInclusion_opensRange]
    exact hp
  intro hd
  exact hd.le_bot ⟨⟨p, rfl⟩, hpV⟩

/-- Integrality is derived for the constructed global normalization from its
actual integral charts and their pairwise intersecting open images. -/
theorem isIntegral_normalization : IsIntegral (normalization X L) := by
  let C := normalizationCover X L
  let : ∀ i : C.I₀, IsIntegral (C.X i) := fun i => chart_isIntegral L i
  let : AlgebraicGeometry.IsReduced (normalization X L) :=
    AlgebraicGeometry.IsReduced.of_openCover (normalization X L) C
  have hpair : Pairwise (fun i j : C.I₀ =>
      ¬ Disjoint (C.f i).opensRange (C.f j).opensRange) := by
    intro i j _
    exact chartInclusion_not_disjoint L i j
  have hpre (i : C.I₀) : PreirreducibleSpace (C.f i).opensRange := by
    apply isPreirreducible_iff_preirreducibleSpace.mp
    have h := (PreirreducibleSpace.isPreirreducible_univ :
      IsPreirreducible (Set.univ : Set (C.X i))).image
      (C.f i) (C.f i).continuous.continuousOn
    simpa only [Set.image_univ, Scheme.Hom.coe_opensRange] using h
  let : PreirreducibleSpace (normalization X L) :=
    PreirreducibleSpace.of_isOpenCover hpair C.isOpenCover_opensRange hpre
  let : Nonempty (normalization X L) := by
    let U : NonemptyAffineOpen X :=
      (NormalizationFinite.nonemptyAffineCoordinateOpenCover X).idx (Classical.choice inferInstance)
    let : IsIntegral (Spec (.of (closureRing L U))) := chart_isIntegral L U
    exact ⟨chartInclusion X L U (Classical.choice inferInstance)⟩
  let : IrreducibleSpace (normalization X L) :=
    { toPreirreducibleSpace := inferInstance, toNonempty := inferInstance }
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Dominance is derived for the same actual normalization structure morphism. -/
theorem normalizationStructure_isDominant : IsDominant (normalizationStructure X L) := by
  let U : NonemptyAffineOpen X :=
    (NormalizationFinite.nonemptyAffineCoordinateOpenCover X).idx (Classical.choice inferInstance)
  let := chartInclusion_comp_isDominant L U
  exact IsDominant.of_comp (chartInclusion X L U) (normalizationStructure X L)


section FiniteExtension

variable [FiniteDimensional X.functionField L]

/-- The actual specified extension is the fraction field of each closure chart. -/
theorem closureRing_isFractionRing (U : NonemptyAffineOpen X) :
    IsFractionRing (closureRing L U) L := by
  let : IsDomain Γ(X, U.1.1) := IsIntegral.component_integral U.1.1
  let : IsFractionRing Γ(X, U.1.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1.1 U.1.2
  exact integralClosure.isFractionRing_of_finite_extension X.functionField L

/-- Every actual affine normalization ring is integrally closed in its fraction field. -/
theorem closureRing_isIntegrallyClosed (U : NonemptyAffineOpen X) :
    IsIntegrallyClosed (closureRing L U) := by
  let : IsFractionRing Γ(X, U.1.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1.1 U.1.2
  exact integralClosure.isIntegrallyClosedOfFiniteExtension X.functionField

/-- The actual global normalization is normal on its genuine local rings. -/
theorem normalization_isNormalScheme :
    IsNormalScheme (normalization X L) := by
  intro x
  let C := normalizationCover X L
  obtain ⟨y, hy⟩ := C.covers x
  let U : NonemptyAffineOpen X := C.idx x
  let := closureRing_isIntegrallyClosed L U
  have hnormal := isNormalScheme_spec (closureRing L U) y
  let : IsDomain ((C.X U).presheaf.stalk y) := hnormal.1
  let : IsIntegrallyClosed ((C.X U).presheaf.stalk y) := hnormal.2
  let e := (asIso ((C.f U).stalkMap y)).commRingCatIsoToRingEquiv
  have h : IsDomain ((normalization X L).presheaf.stalk (C.f U y)) ∧
      IsIntegrallyClosed ((normalization X L).presheaf.stalk (C.f U y)) :=
    ⟨MulEquiv.isDomain _ e.toMulEquiv, IsIntegrallyClosed.of_equiv e.symm⟩
  rw [hy] at h
  exact h

variable {k : Type u} [Field k]

/-- Actual extension normalization rings are finite over their original affine coefficients,
over an arbitrary ground field. -/
theorem closureRing_finite (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (U : NonemptyAffineOpen X) : Module.Finite Γ(X, U.1.1) (closureRing L U) := by
  let := (NormalizationFinite.affineCoefficientMap p ⟨U.1.1, U.1.2⟩).toAlgebra
  let : Algebra.FiniteType k Γ(X, U.1.1) :=
    NormalizationFinite.affineSections_finiteType p ⟨U.1.1, U.1.2⟩
  let : IsDomain Γ(X, U.1.1) := IsIntegral.component_integral U.1.1
  let : IsFractionRing Γ(X, U.1.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1.1 U.1.2
  exact Algebra.IntegralClosureFiniteType.finite_of_isIntegralClosure_of_finiteType
    k Γ(X, U.1.1) X.functionField L (closureRing L U)

/-- The actual affine coefficient map is finite. -/
theorem affineStructure_isFinite (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (U : NonemptyAffineOpen X) : IsFinite (affineStructure L U) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr (closureRing_finite L p U)

/-- Native Cartesian charts descend finiteness of the actual global structure map. -/
theorem normalizationStructure_isFinite (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    IsFinite (normalizationStructure X L) := by
  apply IsZariskiLocalAtTarget.of_openCover (NormalizationFinite.nonemptyAffineCoordinateOpenCover X)
  intro U
  let V : NonemptyAffineOpen X := U
  let h := (isPullback_chart L V).flip
  change IsFinite (Limits.pullback.snd (normalizationStructure X L) V.1.2.fromSpec)
  rw [← h.isoPullback_inv_snd]
  let : IsFinite (affineStructure L V) := affineStructure_isFinite L p V
  infer_instance

/-- The actual finite dominant normalization in the specified extension is an alteration. -/
theorem normalizationStructure_isAlteration (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    IsAlteration (normalizationStructure X L) := by
  let : IsIntegral (normalization X L) := isIntegral_normalization L
  let : IsFinite (normalizationStructure X L) := normalizationStructure_isFinite L p
  let : IsDominant (normalizationStructure X L) := normalizationStructure_isDominant L
  exact isAlteration_of_isFinite _

end FiniteExtension

end DeJongAlterations.Geometry.NormalizationInExtension
