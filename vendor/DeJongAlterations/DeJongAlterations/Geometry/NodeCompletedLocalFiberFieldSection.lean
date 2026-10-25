import DeJongAlterations.Geometry.NodeCompletedLocalFiberQuotient
import DeJongAlterations.Algebra.NodeGeometricCompletionOriginalFiberSection

/-! Actual base-residue coefficients and original point coefficient fields in the ACTUAL scheme fibre. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

namespace DeJongAlterations.Geometry.NodeCompletedLocalMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- A local-point stalk map retains the actual original base map of its scheme morphism. -/
theorem baseToStalk_stalkClosedPointTo {K Q : CommRingCat.{u}} [IsLocalRing Q]
    {Y : Scheme.{u}} (q : Spec Q ⟶ Y) (p : Y ⟶ Spec K) (φ : K ⟶ Q)
    (h : q ≫ p = Spec.map φ) :
    Scheme.baseToStalk p (q (closedPoint Q)) ≫ Scheme.stalkClosedPointTo q = φ := by
  unfold Scheme.stalkClosedPointTo
  rw [← Category.assoc, Scheme.baseToStalk_comp_stalkMap, h]
  change ((Scheme.ΓSpecIso K).inv ≫ (Spec.map φ).appTop) ≫
    (Spec Q).presheaf.germ ⊤ (closedPoint Q) trivial ≫ (stalkClosedPointIso Q).hom = φ
  rw [← Scheme.ΓSpecIso_inv_naturality, germ_stalkClosedPointIso_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

attribute [local instance] originalAlgebra

local instance originalStalkMap_fieldCoefficients :
    IsLocalHom (algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
  inferInstanceAs (IsLocalHom (f.stalkMap x).hom)

local instance originalFiber_fieldCoefficients_local : IsLocalRing (OriginalFiberRing f x) :=
  originalFiberLocalRing f x

/-- The actual original base point residue algebra of the literal original quotient. -/
@[instance_reducible]
def originalFiberResidueAlgebra :
    Algebra (S.residueField (f x)) (OriginalFiberRing f x) :=
  Algebra.NodeGeometricCompletionOriginalFiberSection.baseResidueAlgebra
    (S.presheaf.stalk (f x)) (X.presheaf.stalk x)

attribute [local instance] originalFiberResidueAlgebra

/-- The actual point-residue projection is the literal original residue-quotient factor map. -/
theorem originalFiberToPointResidue_eq :
    originalFiberToPointResidue f x = Spec.map (CommRingCat.ofHom
      (Algebra.NodeGeometricCompletionOriginalFiberSection.baseResidueMap
        (S.presheaf.stalk (f x)) (X.presheaf.stalk x))) := by
  change Spec.map (CommRingCat.ofHom (originalFiberTensorEquiv f x).symm.toRingHom) ≫
    (pullbackSpecIso (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (ResidueField (S.presheaf.stalk (f x)))).inv ≫ pullback.snd _ _ = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  obtain ⟨r, rfl⟩ := residue_surjective a
  change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (X.presheaf.stalk x)
      (maximalIdeal (S.presheaf.stalk (f x)))).symm
      (1 ⊗ₜ[S.presheaf.stalk (f x)] Ideal.Quotient.mk (maximalIdeal (S.presheaf.stalk (f x))) r) =
    Ideal.Quotient.mk (originalFiberIdeal f x) (algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x) r)
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  simp only [Algebra.smul_def, mul_one]
  rfl

/-- The actual fibre stalk equivalence is over the WHOLE actual original base point residue field. -/
def originalFiberStalkAlgEquiv :
    letI := Scheme.stalkAlgebra (f.fiberToSpecResidueField (f x)) (originalFiberPoint f x)
    (f.fiber (f x)).presheaf.stalk (originalFiberPoint f x) ≃ₐ[S.residueField (f x)]
      OriginalFiberRing f x := by
  let := Scheme.stalkAlgebra (f.fiberToSpecResidueField (f x)) (originalFiberPoint f x)
  refine AlgEquiv.ofRingEquiv (f := originalFiberStalkEquiv f x) ?_
  intro a
  have h := baseToStalk_stalkClosedPointTo (originalFiberMap f x)
    (f.fiberToSpecResidueField (f x)) (CommRingCat.ofHom
      (Algebra.NodeGeometricCompletionOriginalFiberSection.baseResidueMap
        (S.presheaf.stalk (f x)) (X.presheaf.stalk x)))
      ((originalFiberMap_residue f x).trans (originalFiberToPointResidue_eq f x))
  exact ConcreteCategory.congr_hom h a

/-- The completed ACTUAL fibre comparison preserves the literal original base residue action. -/
def originalFiberCompletedAlgEquiv :
    letI := Scheme.completedLocalRingAlgebra (f.fiberToSpecResidueField (f x)) (originalFiberPoint f x)
    (f.fiber (f x)).completedLocalRing (originalFiberPoint f x) ≃ₐ[S.residueField (f x)]
      Algebra.CompletionRegularityBasics.Completion (OriginalFiberRing f x) := by
  let := Scheme.stalkAlgebra (f.fiberToSpecResidueField (f x)) (originalFiberPoint f x)
  let := Scheme.completedLocalRingAlgebra (f.fiberToSpecResidueField (f x)) (originalFiberPoint f x)
  refine AlgEquiv.ofRingEquiv (f := originalFiberCompletedEquiv f x) ?_
  intro a
  change originalFiberCompletedEquiv f x
    (algebraMap ((f.fiber (f x)).presheaf.stalk (originalFiberPoint f x))
      ((f.fiber (f x)).completedLocalRing (originalFiberPoint f x))
      (algebraMap (S.residueField (f x))
        ((f.fiber (f x)).presheaf.stalk (originalFiberPoint f x)) a)) =
    algebraMap (OriginalFiberRing f x) (Algebra.CompletionRegularityBasics.Completion (OriginalFiberRing f x))
      (algebraMap (S.residueField (f x)) (OriginalFiberRing f x) a)
  unfold originalFiberCompletedEquiv
  rw [Algebra.CompletionLocalMap.completionEquiv_apply, Algebra.CompletionLocalMap.completionMap_algebraMap]
  exact congrArg (algebraMap (OriginalFiberRing f x)
    (Algebra.CompletionRegularityBasics.Completion (OriginalFiberRing f x)))
      ((originalFiberStalkAlgEquiv f x).commutes a)

variable [LocallyOfFiniteType f] [IsLocallyNoetherian S]

/-- Actual fibre stalk Noetherianity follows internally from the original finite type map. -/
theorem actualFiberStalk_isNoetherianRing :
    IsNoetherianRing ((f.fiber (f x)).presheaf.stalk (originalFiberPoint f x)) := by
  let := originalTarget_isNoetherianRing f x
  exact isNoetherianRing_of_ringEquiv (OriginalFiberRing f x) (originalFiberStalkEquiv f x).symm

variable [FiniteDimensional (ResidueField (S.presheaf.stalk (f x)))
    (ResidueField (X.presheaf.stalk x))]
  [Algebra.IsSeparable (ResidueField (S.presheaf.stalk (f x)))
    (ResidueField (X.presheaf.stalk x))]

/-- The original point residue field is actual coefficients in the ACTUAL original scheme fibre completion. -/
def actualPointFieldSection : ResidueField (X.presheaf.stalk x) →+*
    (f.fiber (f x)).completedLocalRing (originalFiberPoint f x) := by
  let := originalTarget_isNoetherianRing f x
  exact (originalFiberCompletedEquiv f x).symm.toRingHom.comp
    (Algebra.NodeGeometricCompletionOriginalFiberSection.pointFieldSection
      (S.presheaf.stalk (f x)) (X.presheaf.stalk x))

/-- The canonical ORIGINAL point residue identification of the ACTUAL fibre completed local ring. -/
def actualPointResidueEquiv :
    letI := actualFiberStalk_isNoetherianRing f x
    ResidueField (X.presheaf.stalk x) ≃+*
      ResidueField ((f.fiber (f x)).completedLocalRing (originalFiberPoint f x)) := by
  let := originalTarget_isNoetherianRing f x
  let := actualFiberStalk_isNoetherianRing f x
  exact (Algebra.NodeGeometricCompletionOriginalFiberSection.originalResidueEquiv
      (S.presheaf.stalk (f x)) (X.presheaf.stalk x)).trans
    (ResidueField.mapEquiv (originalFiberCompletedEquiv f x).symm)

/-- The entire actual native residue map agrees with the actual ORIGINAL point residue identification. -/
theorem residue_actualPointFieldSection (a : ResidueField (X.presheaf.stalk x)) :
    letI := actualFiberStalk_isNoetherianRing f x
    residue ((f.fiber (f x)).completedLocalRing (originalFiberPoint f x))
      (actualPointFieldSection f x a) = actualPointResidueEquiv f x a := by
  let := originalTarget_isNoetherianRing f x
  let := actualFiberStalk_isNoetherianRing f x
  let : IsLocalHom (originalFiberCompletedEquiv f x).symm.toRingHom :=
    Algebra.CompletionLocalMap.instIsLocalHomRingEquivToRingHom
      (originalFiberCompletedEquiv f x).symm
  change residue ((f.fiber (f x)).completedLocalRing (originalFiberPoint f x))
      ((originalFiberCompletedEquiv f x).symm
        (Algebra.NodeGeometricCompletionOriginalFiberSection.pointFieldSection
          (S.presheaf.stalk (f x)) (X.presheaf.stalk x) a)) =
    ResidueField.map (originalFiberCompletedEquiv f x).symm.toRingHom
      (Algebra.NodeGeometricCompletionOriginalFiberSection.originalResidueEquiv
        (S.presheaf.stalk (f x)) (X.presheaf.stalk x) a)
  exact (ResidueField.map_residue (originalFiberCompletedEquiv f x).symm.toRingHom
    (Algebra.NodeGeometricCompletionOriginalFiberSection.pointFieldSection
      (S.presheaf.stalk (f x)) (X.presheaf.stalk x) a)).symm.trans
    (congrArg (ResidueField.map (originalFiberCompletedEquiv f x).symm.toRingHom)
      (Algebra.NodeGeometricCompletionOriginalFiberSection.residue_pointFieldSection
        (S.presheaf.stalk (f x)) (X.presheaf.stalk x) a))

/-- The original native point residue extension, unbundled over the actual scheme base field. -/
@[instance_reducible]
def originalPointResidueAlgebra :
    Algebra (S.residueField (f x)) (ResidueField (X.presheaf.stalk x)) :=
  inferInstanceAs (Algebra (ResidueField (S.presheaf.stalk (f x))) (ResidueField (X.presheaf.stalk x)))

attribute [local instance] originalPointResidueAlgebra

/-- The actual original point field section preserves the WHOLE native geometric base field action. -/
def actualPointFieldSectionAlgHom :
    letI := Scheme.completedLocalRingAlgebra (f.fiberToSpecResidueField (f x)) (originalFiberPoint f x)
    ResidueField (X.presheaf.stalk x) →ₐ[S.residueField (f x)]
      (f.fiber (f x)).completedLocalRing (originalFiberPoint f x) := by
  let := originalTarget_isNoetherianRing f x
  let := Scheme.completedLocalRingAlgebra (f.fiberToSpecResidueField (f x)) (originalFiberPoint f x)
  refine { toRingHom := actualPointFieldSection f x, commutes' := ?_ }
  intro a
  change (originalFiberCompletedEquiv f x).symm
    (Algebra.NodeGeometricCompletionOriginalFiberSection.pointFieldSection
      (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (algebraMap (S.residueField (f x)) (ResidueField (X.presheaf.stalk x)) a)) = _
  exact (congrArg (originalFiberCompletedEquiv f x).symm
    (Algebra.NodeGeometricCompletionOriginalFiberSection.pointFieldSection_base
      (S.presheaf.stalk (f x)) (X.presheaf.stalk x) a)).trans
    ((originalFiberCompletedAlgEquiv f x).symm.commutes a)

/-- The literal native residue projection, through the canonical ORIGINAL point isomorphism,
composed with the actual section is the identity on the ORIGINAL point field. -/
theorem actualPointResidueProjection_comp_section :
    letI := actualFiberStalk_isNoetherianRing f x
    (actualPointResidueEquiv f x).symm.toRingHom.comp
      ((residue ((f.fiber (f x)).completedLocalRing (originalFiberPoint f x))).comp
        (actualPointFieldSection f x)) = RingHom.id _ := by
  let := actualFiberStalk_isNoetherianRing f x
  ext a
  change (actualPointResidueEquiv f x).symm
    (residue ((f.fiber (f x)).completedLocalRing (originalFiberPoint f x))
      (actualPointFieldSection f x a)) = a
  rw [residue_actualPointFieldSection, RingEquiv.symm_apply_apply]

end DeJongAlterations.Geometry.NodeCompletedLocalMap
