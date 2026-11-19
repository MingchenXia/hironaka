import Hironaka.Algebra.NodeEtaleClosedFiber
import Hironaka.Algebra.NodeGeometricCompletionCoefficients
import Hironaka.Algebra.NodeGeometricCompletionOriginalFiberSection

/-! # Actual upper residue coefficients on the SAME native original closed-fibre completion -/

noncomputable section

namespace Hironaka.Algebra.NodeEtaleCompletedClosedFiber

open IsLocalRing CompletionRegularityBasics CompletionLocalMap NodeGeometricCompletion
  NodeGeometricCompletionOriginalFiberSection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [FiniteDimensional (ResidueField A) (ResidueField B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

attribute [local instance] CompletionFlatMap.completedAlgebra baseResidueAlgebra

local instance completedBase_local : IsLocalHom (algebraMap (Completion A) (Completion B)) :=
  isLocalHom_completionMap (algebraMap A B)
local instance completedResidueFinite :
    FiniteDimensional (ResidueField (Completion A)) (ResidueField (Completion B)) :=
  completedResidue_finite A B
local instance completedResidueSeparable :
    Algebra.IsSeparable (ResidueField (Completion A)) (ResidueField (Completion B)) :=
  completedResidue_separable A B

local notation "Q" => FiberRing A B
local notation "C" => Completion (FiberRing A B)
local notation "T" => CompletedCoefficientRing A B

local instance originalFiber_local : IsLocalRing Q :=
  CompletionIdealQuotient.quotientLocalRing _ (closedFiberIdeal_le_maximalIdeal (algebraMap A B))
local instance : Algebra T (Completion B) := upperCompletedAlgebra A B
local instance : IsLocalHom (algebraMap T (Completion B)) := completedCoefficientMap_local A B
local instance : IsLocalHom (completedCoefficientMap A B).toRingHom := completedCoefficientMap_local A B

/-- The ACTUAL forward upper quotient followed by the existing original closed-fibre completion comparison. -/
def targetMap : Completion B →+* C :=
  (upperClosedFiberCompletionEquiv A B).toRingHom.comp
    (Ideal.Quotient.mk ((maximalIdeal T).map (completedCoefficientMap A B).toRingHom))

/-- EVERY completed original target element follows the entire original lower quotient-completion map. -/
theorem targetMap_lower (b : Completion B) :
    targetMap A B b = closedFiberEquiv (algebraMap A B)
      (Ideal.Quotient.mk ((maximalIdeal (Completion A)).map
        (completionMap (algebraMap A B))) b) := by
  change closedFiberEquiv (algebraMap A B)
    (Ideal.quotEquivOfEq (completedCoefficient_maximalIdeal_image A B)
      (Ideal.Quotient.mk _ b)) = _
  rw [Ideal.quotEquivOfEq_mk]

/-- EVERY original uncompleted target representative retains its SAME native quotient/completion image. -/
theorem targetMap_original (b : B) :
    targetMap A B (algebraMap B (Completion B) b) =
      algebraMap Q C (Ideal.Quotient.mk (closedFiberIdeal (algebraMap A B)) b) :=
  upperClosedFiberCompletionEquiv_coefficient A B b

/-- The SAME actual original completed-target quotient map is surjective. -/
theorem targetMap_surjective : Function.Surjective (targetMap A B) :=
  (upperClosedFiberCompletionEquiv A B).surjective.comp Ideal.Quotient.mk_surjective

/-- Native locality belongs to the SAME forward map, not an assumed comparison certificate. -/
theorem targetMap_isLocalHom : IsLocalHom (targetMap A B) :=
  IsLocalHom.of_surjective _ (targetMap_surjective A B)

local instance : IsLocalHom (targetMap A B) := targetMap_isLocalHom A B

/-- The upper residue action factors the ACTUAL forward upper coefficient map and original quotient only. -/
def upperResidueMap : ResidueField T →+* C :=
  (closedFiberEquiv (algebraMap A B)).toRingHom.comp
    (NodeEtaleClosedFiber.upperResidueMap (Completion A) (Completion B))

/-- EVERY native upper residue representative retains its actual original forward coefficient image. -/
theorem upperResidueMap_residue (t : T) :
    upperResidueMap A B (residue T t) = targetMap A B (completedCoefficientMap A B t) := by
  rw [targetMap_lower]
  rfl

/-- The entire upper coefficient action is precisely the actual forward composite. -/
theorem upperResidueMap_wholeCoefficient :
    (upperResidueMap A B).comp (residue T) =
      (targetMap A B).comp (completedCoefficientMap A B).toRingHom :=
  RingHom.ext (upperResidueMap_residue A B)

/-- EVERY original completed-base coefficient follows the SAME actual completed structural map. -/
theorem upperResidueMap_completedBase (a : Completion A) :
    upperResidueMap A B (residue T (algebraMap (Completion A) T a)) =
      targetMap A B (completionMap (algebraMap A B) a) := by
  rw [upperResidueMap_residue, AlgHom.commutes]
  rfl

/-- The SAME original completed fibre receives the actual forward upper residue action. -/
@[instance_reducible]
def upperResidueAlgebra : Algebra (ResidueField T) C := (upperResidueMap A B).toAlgebra

local instance : Algebra (ResidueField T) C := upperResidueAlgebra A B
local instance : Algebra (ResidueField T) (NodeFlatPresentation.ClosedFiber T (Completion B)) :=
  NodeFlatPresentation.closedFiberAlgebra T (Completion B)

/-- The existing native comparison is genuinely linear over the SAME forward upper residue coefficients. -/
def upperClosedFiberEquiv :
    NodeFlatPresentation.ClosedFiber T (Completion B) ≃ₐ[ResidueField T] C := by
  refine AlgEquiv.ofRingEquiv (f := upperClosedFiberCompletionEquiv A B) ?_
  intro a
  obtain ⟨t, rfl⟩ := residue_surjective a
  change targetMap A B (completedCoefficientMap A B t) = upperResidueMap A B (residue T t)
  exact (upperResidueMap_residue A B t).symm

/-- EVERY original germ has its literal original quotient/completion image under this SAME coefficient-linear comparison. -/
theorem upperClosedFiberEquiv_original (b : B) :
    upperClosedFiberEquiv A B (Ideal.Quotient.mk _ (algebraMap B (Completion B) b)) =
      algebraMap Q C (Ideal.Quotient.mk (closedFiberIdeal (algebraMap A B)) b) :=
  targetMap_original A B b

/-- The WHOLE native completed-target residue map retains the canonical ORIGINAL point residue identification. -/
theorem targetResidue_triangle :
    (ResidueField.map (targetMap A B)).comp (residueFieldEquiv B).toRingHom =
      (originalResidueEquiv A B).toRingHom := by
  ext a
  obtain ⟨b, rfl⟩ := residue_surjective a
  change ResidueField.map (targetMap A B)
    (ResidueField.map (algebraMap B (Completion B)) (residue B b)) = _
  rw [ResidueField.map_residue, ResidueField.map_residue, targetMap_original]
  exact (originalResidueEquiv_residue A B b).symm

/-- The entire actual upper coefficient map retains the native residue functor triangle. -/
theorem upperResidueMap_nativeResidue :
    (residue C).comp (upperResidueMap A B) =
      (ResidueField.map (targetMap A B)).comp (completedCoefficientResidueEquiv A B).toRingHom := by
  ext a
  obtain ⟨t, rfl⟩ := residue_surjective a
  change residue C (upperResidueMap A B (residue T t)) =
    ResidueField.map (targetMap A B)
      (ResidueField.map (completedCoefficientMap A B).toRingHom (residue T t))
  rw [upperResidueMap_residue, ResidueField.map_residue, ResidueField.map_residue]
  rfl

/-- Only canonical ACTUAL residue maps identify the upper coefficient field with the ORIGINAL point field. -/
def upperOriginalResidueEquiv : ResidueField T ≃+* ResidueField B :=
  (completedCoefficientResidueEquiv A B).trans (residueFieldEquiv B).symm

/-- The WHOLE actual forward upper field action induces exactly the canonical ORIGINAL point residue map. -/
theorem upperResidueMap_originalResidue :
    (residue C).comp (upperResidueMap A B) =
      (originalResidueEquiv A B).toRingHom.comp (upperOriginalResidueEquiv A B).toRingHom := by
  ext a
  have h := RingHom.congr_fun (targetResidue_triangle A B)
    ((residueFieldEquiv B).symm (completedCoefficientResidueEquiv A B a))
  have hr := RingHom.congr_fun (upperResidueMap_nativeResidue A B) a
  change residue C (upperResidueMap A B a) = _ at hr
  change residue C (upperResidueMap A B a) = _
  rw [hr]
  change ResidueField.map (targetMap A B) (completedCoefficientResidueEquiv A B a) =
    originalResidueEquiv A B
      ((residueFieldEquiv B).symm (completedCoefficientResidueEquiv A B a))
  change ResidueField.map (targetMap A B)
      (residueFieldEquiv B ((residueFieldEquiv B).symm (completedCoefficientResidueEquiv A B a))) =
    originalResidueEquiv A B
      ((residueFieldEquiv B).symm (completedCoefficientResidueEquiv A B a)) at h
  rw [RingEquiv.apply_symm_apply] at h
  exact h

end Hironaka.Algebra.NodeEtaleCompletedClosedFiber
