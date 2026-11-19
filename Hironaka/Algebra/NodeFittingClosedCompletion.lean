import Hironaka.Algebra.NodeFittingCompletionDensity
import Hironaka.Algebra.NodeFittingIdealSheafQuotient
import Hironaka.Algebra.CompletionIdealQuotient
import Hironaka.Geometry.NodeCompletedLocalMap

/-! # Actual native closed-subscheme completed stalks and the WHOLE original ideal

The entire forward map is the actual completed closed inclusion. Original target
coefficients are defined by that forward stalk map and native completion only.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hironaka.Algebra.NodeFittingClosedCompletion

open NodeFittingIdealSheaf CompletionLocalMap

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000

universe u
variable {X : Scheme.{u}} (I : X.IdealSheafData) (z : I.subscheme)

local notation "x" => I.subschemeι z
local notation "R" => X.presheaf.stalk x
local notation "L" => I.subscheme.presheaf.stalk z
local notation "C" => X.completedLocalRing x
local notation "D" => I.subscheme.completedLocalRing z
local notation "J" => stalkIdeal I x

/-- The ENTIRE actual closed stalk ideal lies in the SAME original native maximal ideal. -/
theorem stalkIdeal_le_maximalIdeal : J ≤ maximalIdeal R := by
  rw [← ker_stalkMap_subschemeι I z]
  intro a ha
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have htarget := hu.map (I.subschemeι.stalkMap z).hom
  rw [RingHom.mem_ker.mp ha] at htarget
  exact not_isUnit_zero htarget

variable [IsLocallyNoetherian X]

/-- The actual native completed closed stalk is the quotient by the ENTIRE extended original ideal. -/
def closedCompletionQuotientRingEquiv :
    (C ⧸ (J).map (X.toCompletedLocalRing x)) ≃+* D := by
  letI := CompletionIdealQuotient.quotientLocalRing J (stalkIdeal_le_maximalIdeal I z)
  exact (CompletionRegularityQuotient.quotientCompletionEquiv J).trans
    (completionEquiv (stalkQuotientEquiv I z))

/-- EVERY original ambient germ follows the SAME actual closed-inclusion stalk map and native completion. -/
theorem closedCompletionQuotientRingEquiv_original (a : X.presheaf.stalk (I.subschemeι z)) :
    closedCompletionQuotientRingEquiv I z
      (Ideal.Quotient.mk ((J).map (X.toCompletedLocalRing x)) (X.toCompletedLocalRing x a)) =
        I.subscheme.toCompletedLocalRing z (I.subschemeι.stalkMap z a) := by
  let := CompletionIdealQuotient.quotientLocalRing J (stalkIdeal_le_maximalIdeal I z)
  dsimp only [closedCompletionQuotientRingEquiv, RingEquiv.trans_apply]
  change completionEquiv (stalkQuotientEquiv I z)
      (CompletionRegularityQuotient.quotientCompletionEquiv J
        (Ideal.Quotient.mk ((J).map (algebraMap R C))
          (AdicCompletion.of (maximalIdeal R) R a))) =
    AdicCompletion.of (maximalIdeal L) L (I.subschemeι.stalkMap z a)
  rw [CompletionRegularityQuotient.quotientCompletionEquiv_coefficient]
  let := CompletionLocalMap.instIsLocalHomRingEquivToRingHom (stalkQuotientEquiv I z)
  exact completionMap_of (stalkQuotientEquiv I z : (R ⧸ J) →+* L) (Ideal.Quotient.mk J a)

/-- The ACTUAL forward original stalk map followed by native completion supplies the original coefficient action. -/
@[instance_reducible]
def closedCompletedOriginalAlgebra : Algebra R D :=
  ((I.subscheme.toCompletedLocalRing z).comp (I.subschemeι.stalkMap z).hom).toAlgebra

local instance : Algebra R D := closedCompletedOriginalAlgebra I z

/-- The genuine quotient equivalence retains that SAME actual original ambient local-ring action. -/
def closedCompletionQuotientAlgEquiv :
    (C ⧸ (J).map (X.toCompletedLocalRing x)) ≃ₐ[R] D where
  toRingEquiv := closedCompletionQuotientRingEquiv I z
  commutes' := closedCompletionQuotientRingEquiv_original I z

/-- The actual completed closed inclusion is an original-algebra map for its SAME forward original action. -/
def completedInclusionAlgHom : C →ₐ[R] D where
  __ := Geometry.NodeCompletedLocalMap.completedMap I.subschemeι z
  commutes' := Geometry.NodeCompletedLocalMap.completedMap_coefficient I.subschemeι z

omit [IsLocallyNoetherian X] in
/-- Native target completion is Hausdorff for the SAME original ambient maximal ideal. -/
theorem target_originalHausdorff : IsHausdorff (maximalIdeal R) D := by
  let : Algebra R L := (I.subschemeι.stalkMap z).hom.toAlgebra
  let : IsScalarTower R L D := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  apply (IsHausdorff.map_algebraMap_iff (I := maximalIdeal R) (S := L) (M := D)).mp
  change IsHausdorff ((maximalIdeal R).map (I.subschemeι.stalkMap z).hom) D
  rw [map_maximalIdeal_of_surjective (I.subschemeι.stalkMap z).hom
    (I.subschemeι.stalkMap_surjective z)]
  infer_instance

/-- EVERY actual completed element follows the ENTIRE native completed closed-inclusion map. -/
theorem closedCompletionQuotientAlgEquiv_mk (c : X.completedLocalRing (I.subschemeι z)) :
    closedCompletionQuotientAlgEquiv I z
      (Ideal.Quotient.mk ((J).map (X.toCompletedLocalRing x)) c) =
        Geometry.NodeCompletedLocalMap.completedMap I.subschemeι z c := by
  let := target_originalHausdorff I z
  let F : C →ₐ[R] D := (closedCompletionQuotientAlgEquiv I z).toAlgHom.comp
    (Ideal.Quotient.mkₐ R ((J).map (X.toCompletedLocalRing x)))
  have h := NodeFittingCompletionDensity.algHom_ext (maximalIdeal R)
    (IsNoetherian.noetherian (maximalIdeal R)) F (completedInclusionAlgHom I z)
  exact DFunLike.congr_fun h c

end Hironaka.Algebra.NodeFittingClosedCompletion
