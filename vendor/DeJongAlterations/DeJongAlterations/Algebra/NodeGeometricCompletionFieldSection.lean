import DeJongAlterations.Algebra.NodeEtaleCoefficients

/-!
# A literal residue field coefficient section over an original base field

The input is the original local K-algebra C, completeness of C, and finite
separability of its CANONICAL original residue extension. The actual field
section, its full residue identity, and the original K-coefficient triangle
are all constructed using the same native Hensel coefficient algebra.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeGeometricCompletionFieldSection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (K : Type u) [Field K]

/-- The canonical residue map of the ORIGINAL field is an actual ring isomorphism. -/
def baseResidueEquiv : K ≃+* ResidueField K :=
  RingEquiv.ofBijective (residue K) ⟨RingHom.injective _, residue_surjective⟩

variable (C : Type u) [CommRing C] [IsLocalRing C] [Algebra K C]
  [IsLocalHom (algebraMap K C)]

/-- The actual canonical residue coefficient triangle. -/
theorem baseResidue_triangle :
    (algebraMap (ResidueField K) (ResidueField C)).comp (baseResidueEquiv K).toRingHom =
      algebraMap K (ResidueField C) := by
  ext a
  exact ResidueField.algebraMap_residue a

variable [FiniteDimensional K (ResidueField C)] [Algebra.IsSeparable K (ResidueField C)]

omit [Algebra.IsSeparable K (ResidueField C)] in
/-- Original finite residue degree gives the native local coefficient residue degree. -/
theorem baseResidue_finite : FiniteDimensional (ResidueField K) (ResidueField C) :=
  Module.Finite.of_equiv_equiv (baseResidueEquiv K) (RingEquiv.refl (ResidueField C))
    (baseResidue_triangle K C)

omit [FiniteDimensional K (ResidueField C)] in
/-- Original canonical separability gives separability for the native local coefficient action. -/
theorem baseResidue_separable : Algebra.IsSeparable (ResidueField K) (ResidueField C) :=
  Algebra.IsSeparable.of_equiv_equiv (baseResidueEquiv K) (RingEquiv.refl (ResidueField C))
    (baseResidue_triangle K C)

attribute [local instance] baseResidue_finite baseResidue_separable
attribute [local instance] NodeEtaleCoefficients.residueAlgebra NodeEtaleCoefficients.idealResidueAlgebra

variable [IsAdicComplete (maximalIdeal C) C]

/-- The actual Hensel coefficient ring over the original field. -/
abbrev CoefficientRing := NodeEtaleCoefficients.CoefficientRing K C

omit [IsAdicComplete (maximalIdeal C) C] in
/-- Its actual maximal ideal is zero, derived from the original field maximal ideal. -/
theorem coefficient_maximalIdeal_eq_bot : maximalIdeal (CoefficientRing K C) = ⊥ := by
  rw [← NodeEtaleCoefficients.coefficients_map_maximalIdeal K (ResidueField C)]
  exact (congrArg (Ideal.map (algebraMap K (CoefficientRing K C)))
    (IsLocalRing.maximalIdeal_eq_bot (R := K))).trans Ideal.map_bot

/-- The actual residue map of the SAME constructed coefficient ring is an isomorphism. -/
def coefficientOwnResidueEquiv : CoefficientRing K C ≃+* ResidueField (CoefficientRing K C) :=
  RingEquiv.ofBijective (residue (CoefficientRing K C)) ⟨by
    rw [RingHom.injective_iff_ker_eq_bot, IsLocalRing.ker_residue]
    exact coefficient_maximalIdeal_eq_bot K C,
    residue_surjective⟩

/-- The actual coefficient ring is identified with the actual original target residue field. -/
def coefficientFieldEquiv : CoefficientRing K C ≃+* ResidueField C :=
  (coefficientOwnResidueEquiv K C).trans (NodeEtaleCoefficients.coefficientResidueEquiv K C)

/-- Its actual map is the literal residue of the actual Hensel coefficient map. -/
theorem coefficientFieldEquiv_apply (d : CoefficientRing K C) :
    coefficientFieldEquiv K C d = residue C (NodeEtaleCoefficients.coefficientMap K C d) :=
  ResidueField.map_residue (NodeEtaleCoefficients.coefficientMap K C).toRingHom d

/-- The internally constructed section of the actual native target residue map. -/
def fieldSection : ResidueField C →+* C :=
  (NodeEtaleCoefficients.coefficientMap K C).toRingHom.comp (coefficientFieldEquiv K C).symm.toRingHom

/-- The entire actual residue field is fixed, not only a chosen primitive generator. -/
theorem residue_fieldSection (a : ResidueField C) : residue C (fieldSection K C a) = a := by
  change residue C (NodeEtaleCoefficients.coefficientMap K C ((coefficientFieldEquiv K C).symm a)) = a
  rw [← coefficientFieldEquiv_apply, RingEquiv.apply_symm_apply]

/-- The literal native residue map composed with the constructed section is the identity. -/
theorem residue_comp_fieldSection : (residue C).comp (fieldSection K C) = RingHom.id _ :=
  RingHom.ext (residue_fieldSection K C)

/-- Every original base coefficient is retained by the actual coefficient section. -/
theorem fieldSection_original (a : K) :
    fieldSection K C (residue C (algebraMap K C a)) = algebraMap K C a := by
  have he : coefficientFieldEquiv K C (algebraMap K (CoefficientRing K C) a) =
      residue C (algebraMap K C a) := by
    rw [coefficientFieldEquiv_apply, AlgHom.commutes]
  change NodeEtaleCoefficients.coefficientMap K C
    ((coefficientFieldEquiv K C).symm (residue C (algebraMap K C a))) = _
  rw [← he, RingEquiv.symm_apply_apply, AlgHom.commutes]

/-- The actual coefficient section is an algebra homomorphism over the ORIGINAL base field. -/
def fieldSectionAlgHom : ResidueField C →ₐ[K] C where
  toRingHom := fieldSection K C
  commutes' a := fieldSection_original K C a

/-- The entire original base coefficient map factors through the actual residue section. -/
theorem fieldSection_triangle :
    (fieldSection K C).comp (algebraMap K (ResidueField C)) = algebraMap K C :=
  RingHom.ext (fieldSection_original K C)

/-- The exact new coefficient action of the actual residue section. -/
@[instance_reducible]
def sectionAlgebra : Algebra (ResidueField C) C := (fieldSection K C).toAlgebra

/-- The original field action is retained under the internally constructed coefficient field. -/
theorem sectionAlgebra_scalarTower :
    letI := sectionAlgebra K C
    IsScalarTower K (ResidueField C) C := by
  let := sectionAlgebra K C
  exact IsScalarTower.of_algebraMap_eq' (fieldSection_triangle K C).symm

end DeJongAlterations.Algebra.NodeGeometricCompletionFieldSection
