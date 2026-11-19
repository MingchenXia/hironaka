import Hironaka.Geometry.ProperSteinProjectiveCechCompleteLocalConnected
import Hironaka.Geometry.ProperSteinProjectiveCechFactorBaseChangePresentation

/-! # Actual closed fibres of the SAME factor over complete flat local coefficients

Polynomial projectivity is DERIVED from the original source projectivity.
The actual original coefficient algebra equivalence is DERIVED by genuine flat
base change of the same original factor. All closed-fibre maps remain literal.
-/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.FactorCompleteLocalConnected
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f] [LocallyOfFiniteType f] [AlgebraicGeometry.IsNoetherian X]
  (hdim : topologicalKrullDim (f.fiber (genericPoint S)) ≤ 1)
  {k : Type u} [Field k] (p : S ⟶ Spec (.of k)) [LocallyOfFiniteType p]
  (hf : IsProper f) (hnormal : IsNormalScheme X) (hp : IsProjectiveOver (f ≫ p))
  (V : (SteinCurveFactor.base f).Opens) (hV : IsAffineOpen V)
  (B : Type u) [CommRing B] [Algebra Γ(SteinCurveFactor.base f, V) B]
  [Module.Flat Γ(SteinCurveFactor.base f, V) B] [IsNoetherianRing B] [IsLocalRing B]

include hf hp

/-- ONLY original geometry and actual flat complete local coefficients give native connectedness of the SAME literal ORIGINAL closed fibre. -/
theorem affineFlat_closedFiber_connectedSpace (J : Ideal B) [IsAdicComplete J B] :
    ConnectedSpace (ProperSteinGlobalIdempotents.closedFiber
      (ProperGeometricGlobalFunctions.structureMap (S := B)
        (ProperSteinFlatSections.affineFactor f hdim p hnormal V hV)) J) := by
  let j := FactorBaseChangePresentation.factorBaseChangeEmbedding f hdim p hf hnormal hp V hV B
  have hj := FactorBaseChangePresentation.factorBaseChangeEmbedding_structure f hdim p hf hnormal hp V hV B
  have e : letI := (ProperGeometricGlobalFunctions.coefficientMap (j ≫ projectiveSpaceStructure B _)).toAlgebra
      B ≃ₐ[B] Γ(ProperGeometricGlobalFunctions.baseChange (S := B)
        (ProperSteinFlatSections.affineFactor f hdim p hnormal V hV), ⊤) := by
    rw [hj]
    exact ProperSteinFlatSections.affineFlatSectionsAlgEquiv f hdim p hf hnormal V hV B
  have h := CompleteLocalConnected.closedFiber_connectedSpace J j e
  exact (congrArg (fun q => ConnectedSpace (ProperSteinGlobalIdempotents.closedFiber q J)) hj).mp h

/-- The SAME actual maximal-ideal closed fibre is genuinely connected, with all original maps preserved. -/
theorem affineFlat_maximalClosedFiber_connectedSpace
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] :
    ConnectedSpace (ProperSteinGlobalIdempotents.closedFiber
      (ProperGeometricGlobalFunctions.structureMap (S := B)
        (ProperSteinFlatSections.affineFactor f hdim p hnormal V hV))
          (IsLocalRing.maximalIdeal B)) :=
  affineFlat_closedFiber_connectedSpace f hdim p hf hnormal hp V hV B (IsLocalRing.maximalIdeal B)

end Hironaka.Geometry.ProperSteinProjectiveCech.FactorCompleteLocalConnected
