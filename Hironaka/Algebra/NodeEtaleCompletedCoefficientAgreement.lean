import Hironaka.Algebra.NodeEtaleCompletedClosedFiber
import Hironaka.Algebra.NodeGeometricCompletionOriginalCoefficientAgreement

/-! # The actual forward upper coefficients equal the original Hensel point coefficients -/

noncomputable section

namespace Hironaka.Algebra.NodeEtaleCompletedCoefficientAgreement

open IsLocalRing CompletionRegularityBasics CompletionLocalMap NodeGeometricCompletion
  NodeGeometricCompletionOriginalFiberSection NodeEtaleCompletedClosedFiber

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

local notation "Q" => FiberRing A B
local notation "C" => Completion (FiberRing A B)
local notation "T" => CompletedCoefficientRing A B
local instance originalFiber_local : IsLocalRing Q :=
  CompletionIdealQuotient.quotientLocalRing _ (closedFiberIdeal_le_maximalIdeal (algebraMap A B))

/-- Every ORIGINAL base representative retains its actual native residue through the entire upper construction. -/
theorem upperOriginalResidueEquiv_originalBase (a : A) :
    upperOriginalResidueEquiv A B
      (residue T (algebraMap (Completion A) T (algebraMap A (Completion A) a))) =
        residue B (algebraMap A B a) := by
  let : IsLocalHom (completedCoefficientMap A B).toRingHom := completedCoefficientMap_local A B
  change (residueFieldEquiv B).symm
    (ResidueField.map (completedCoefficientMap A B).toRingHom
      (residue T (algebraMap (Completion A) T (algebraMap A (Completion A) a)))) = _
  rw [ResidueField.map_residue]
  change (residueFieldEquiv B).symm
    (residue (Completion B) (completedCoefficientMap A B
      (algebraMap (Completion A) T (algebraMap A (Completion A) a)))) = _
  rw [completedCoefficientMap_original]
  apply (residueFieldEquiv B).injective
  rw [RingEquiv.apply_symm_apply, residueFieldEquiv_apply, ResidueField.map_residue]

/-- Only actual canonical residue equivalences reindex the actual forward upper field section. -/
def originalSection : ResidueField B →+* C :=
  (upperResidueMap A B).comp (upperOriginalResidueEquiv A B).symm.toRingHom

/-- The ENTIRE original base field action agrees, proved from actual original representatives. -/
theorem originalSection_base (a : ResidueField A) :
    originalSection A B (algebraMap (ResidueField A) (ResidueField B) a) =
      algebraMap (ResidueField A) C a := by
  obtain ⟨a, rfl⟩ := residue_surjective a
  rw [ResidueField.algebraMap_residue]
  change upperResidueMap A B ((upperOriginalResidueEquiv A B).symm
    (residue B (algebraMap A B a))) = _
  rw [← upperOriginalResidueEquiv_originalBase A B a, RingEquiv.symm_apply_apply,
    upperResidueMap_completedBase, completionMap_algebraMap, targetMap_original]
  rfl

/-- The SAME forward upper section is genuinely an algebra map for the original native base residue action. -/
def originalSectionAlgHom : ResidueField B →ₐ[ResidueField A] C where
  toRingHom := originalSection A B
  commutes' := originalSection_base A B

/-- EVERY actual original point coefficient has exactly the SAME canonical native residue. -/
theorem residue_originalSection (a : ResidueField B) :
    residue C (originalSection A B a) = originalResidueEquiv A B a := by
  have h := RingHom.congr_fun (upperResidueMap_originalResidue A B)
    ((upperOriginalResidueEquiv A B).symm a)
  change residue C (upperResidueMap A B ((upperOriginalResidueEquiv A B).symm a)) =
    originalResidueEquiv A B
      (upperOriginalResidueEquiv A B ((upperOriginalResidueEquiv A B).symm a)) at h
  rw [RingEquiv.apply_symm_apply] at h
  exact h

/-- Native formal unramifiedness and native Krull intersection equate the WHOLE two actual sections. -/
theorem originalSectionAlgHom_eq :
    originalSectionAlgHom A B =
      NodeGeometricCompletionOriginalCoefficientAgreement.originalHenselSection A B := by
  let : Algebra.FormallyUnramified (ResidueField A) (ResidueField B) :=
    Algebra.FormallyUnramified.of_isSeparable (ResidueField A) (ResidueField B)
  apply Algebra.FormallyUnramified.ext_of_iInf
    (I := maximalIdeal C)
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal C).ne_top)
  intro a
  change residue C (originalSection A B a) = residue C (pointFieldSection A B a)
  rw [residue_originalSection, residue_pointFieldSection]

/-- The WHOLE actual original-point section agrees with the original Hensel section; no agreement is supplied. -/
theorem originalSection_eq_pointFieldSection : originalSection A B = pointFieldSection A B :=
  congrArg AlgHom.toRingHom (originalSectionAlgHom_eq A B)

/-- The ENTIRE actual upper residue action is the original Hensel section composed with canonical actual residue maps. -/
theorem upperResidueMap_eq_pointFieldSection :
    upperResidueMap A B = (pointFieldSection A B).comp (upperOriginalResidueEquiv A B).toRingHom := by
  apply RingHom.ext
  intro a
  have h := RingHom.congr_fun (originalSection_eq_pointFieldSection A B)
    (upperOriginalResidueEquiv A B a)
  change upperResidueMap A B
      ((upperOriginalResidueEquiv A B).symm (upperOriginalResidueEquiv A B a)) =
    pointFieldSection A B (upperOriginalResidueEquiv A B a) at h
  rw [RingEquiv.symm_apply_apply] at h
  exact h

/-- EVERY actual upper residue coefficient has precisely its SAME original point-field section image. -/
theorem upperResidueMap_pointFieldSection (a : ResidueField T) :
    upperResidueMap A B a = pointFieldSection A B (upperOriginalResidueEquiv A B a) :=
  RingHom.congr_fun (upperResidueMap_eq_pointFieldSection A B) a

end Hironaka.Algebra.NodeEtaleCompletedCoefficientAgreement
