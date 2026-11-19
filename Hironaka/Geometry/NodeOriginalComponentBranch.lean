import Hironaka.Algebra.CompletionSurjectiveLocalMap
import Hironaka.Algebra.NodeFieldRegularBranch
import Hironaka.Geometry.NodeCompletedLocalMap
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! The actual original closed component germ supplies the whole completed original-field branch. -/

noncomputable section

namespace Hironaka.Geometry.NodeOriginalComponentBranch

open AlgebraicGeometry CategoryTheory IsLocalRing
open Algebra.CompletionLocalMap Algebra.NodeNonsplit NodeCompletedLocalMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {K : Type u} [Field K] {D Z : Scheme.{u}}
  (i : D ⟶ Z) (p : Z ⟶ Spec (.of K)) (x : D)

/-- The SAME actual completed stalk map, over the unchanged ORIGINAL field coefficient actions. -/
def completedAlgMap :
    letI := Scheme.completedLocalRingAlgebra p (i x)
    letI := Scheme.completedLocalRingAlgebra (i ≫ p) x
    Z.completedLocalRing (i x) →ₐ[K] D.completedLocalRing x := by
  letI := Scheme.completedLocalRingAlgebra p (i x)
  letI := Scheme.completedLocalRingAlgebra (i ≫ p) x
  refine { completedMap i x with commutes' := ?_ }
  intro a
  change completedMap i x (Z.toCompletedLocalRing (i x) (Scheme.baseToStalk p (i x) a)) =
    D.toCompletedLocalRing x (Scheme.baseToStalk (i ≫ p) x a)
  rw [completedMap_coefficient]
  congr 1
  exact DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp (Scheme.baseToStalk_comp_stalkMap i p x)) a

/-- EVERY native original germ follows its actual component stalk image and canonical completion. -/
theorem completedAlgMap_coefficient (a : Z.presheaf.stalk (i x)) :
    completedAlgMap i p x (Z.toCompletedLocalRing (i x) a) =
      D.toCompletedLocalRing x (i.stalkMap x a) :=
  completedMap_coefficient i x a

variable [IsClosedImmersion i] [IsLocallyNoetherian Z]

include i in
private theorem branch_stalk_noetherian : IsNoetherianRing (D.presheaf.stalk x) :=
  originalTarget_isNoetherianRing i x

/-- Closed immersion surjectivity on the ACTUAL original germs internally gives the WHOLE completion. -/
theorem completedAlgMap_surjective : Function.Surjective (completedAlgMap i p x) := by
  let := branch_stalk_noetherian i x
  exact Algebra.CompletionSurjectiveLocalMap.surjective (i.stalkMap x).hom
    (i.stalkMap_surjective x)

variable (q : Quadratic K)

/-- The WHOLE actual original quadratic model follows its SAME genuine completed component map. -/
def branchMap (e : letI := Scheme.completedLocalRingAlgebra p (i x)
    QuadraticNode q ≃ₐ[K] Z.completedLocalRing (i x)) :
    letI := Scheme.completedLocalRingAlgebra (i ≫ p) x
    QuadraticNode q →ₐ[K] D.completedLocalRing x := by
  letI := Scheme.completedLocalRingAlgebra p (i x)
  letI := Scheme.completedLocalRingAlgebra (i ≫ p) x
  exact (completedAlgMap i p x).comp e.toAlgHom

/-- The whole ORIGINAL quadratic-to-branch map is surjective, with no supplied completion certificate. -/
theorem branchMap_surjective (e : letI := Scheme.completedLocalRingAlgebra p (i x)
    QuadraticNode q ≃ₐ[K] Z.completedLocalRing (i x)) :
    Function.Surjective (branchMap i p x q e) := by
  let := Scheme.completedLocalRingAlgebra p (i x)
  exact (completedAlgMap_surjective i p x).comp e.surjective

variable [IsRegularLocalRing (D.completedLocalRing x)]

/-- One actual complete regular dimension-one original component INTERNALLY splits the SAME quadratic. -/
def quotientEquiv (e : letI := Scheme.completedLocalRingAlgebra p (i x)
    QuadraticNode q ≃ₐ[K] Z.completedLocalRing (i x))
    (hdim : ringKrullDim (D.completedLocalRing x) = 1) :
    QuadraticNode q ≃ₐ[K] Algebra.NodeFlatPresentation.SplitNode K := by
  letI := Scheme.completedLocalRingAlgebra (i ≫ p) x
  letI := branch_stalk_noetherian i x
  exact Algebra.NodeFieldRegularBranch.quotientEquiv q (branchMap i p x q e)
    (branchMap_surjective i p x q e) hdim

/-- The SAME actual original completed local ring has its native original-field split node model. -/
def completedNodeEquiv (e : letI := Scheme.completedLocalRingAlgebra p (i x)
    QuadraticNode q ≃ₐ[K] Z.completedLocalRing (i x))
    (hdim : ringKrullDim (D.completedLocalRing x) = 1) :
    letI := Scheme.completedLocalRingAlgebra p (i x)
    Z.completedLocalRing (i x) ≃ₐ[K] Algebra.NodeFlatPresentation.SplitNode K := by
  letI := Scheme.completedLocalRingAlgebra p (i x)
  exact e.symm.trans (quotientEquiv i p x q e hdim)

/-- EVERY original field coefficient remains its literal standard split-node coefficient. -/
theorem completedNodeEquiv_coefficient (e : letI := Scheme.completedLocalRingAlgebra p (i x)
    QuadraticNode q ≃ₐ[K] Z.completedLocalRing (i x))
    (hdim : ringKrullDim (D.completedLocalRing x) = 1) (a : K) :
    letI := Scheme.completedLocalRingAlgebra p (i x)
    completedNodeEquiv i p x q e hdim (algebraMap K (Z.completedLocalRing (i x)) a) =
      Ideal.Quotient.mk _ (MvPowerSeries.C a) := by
  let := Scheme.completedLocalRingAlgebra p (i x)
  exact (completedNodeEquiv i p x q e hdim).commutes a

end Hironaka.Geometry.NodeOriginalComponentBranch
