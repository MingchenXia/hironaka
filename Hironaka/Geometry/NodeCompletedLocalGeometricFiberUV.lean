import Hironaka.Geometry.NodeCompletedLocalCoherentUV
import Mathlib.AlgebraicGeometry.Fiber

/-! The ACTUAL scalar-extended scheme fibre and the ORIGINAL field-stalk coherent Ω.
No Noetherian hypothesis on the original base, and no original point residue-separability
hypothesis, is needed. The input completed uv model belongs to the actual scalar-extended
FIELD-FIBRE at its actual point, not to the original relative total-space completion. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace Hironaka.Geometry.NodeCompletedLocalGeometricFiberUV

open Algebra.NodeGeometricCompletionCoherentDifferentials
  Algebra.NodeGeometricCompletionDifferentialTransport
  Algebra.NodeGeometricCompletionFormalUV

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
  (K : Type u) [Field K] [Algebra (S.residueField s) K]

/-- The literal scalar extension of the ACTUAL original scheme fibre. -/
abbrev GeometricFiber : Scheme.{u} :=
  pullback (f.fiberToSpecResidueField s)
    (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)))

/-- The actual field structure morphism of this literal geometric fibre. -/
def fieldProjection : GeometricFiber f s K ⟶ Spec (.of K) := pullback.snd _ _

/-- The actual original-fibre projection retains its entire base-field coefficient square. -/
theorem fieldProjection_condition :
    pullback.fst (f.fiberToSpecResidueField s)
        (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K))) ≫
      f.fiberToSpecResidueField s =
    fieldProjection f s K ≫ Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)) :=
  pullback.condition

variable [LocallyOfFiniteType f]

/-- Actual geometric-fibre finite type is derived by the TWO literal scheme base changes. -/
theorem fieldProjection_locallyOfFiniteType : LocallyOfFiniteType (fieldProjection f s K) := by
  let : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- The actual geometric-fibre stalk is Noetherian even when the original base is arbitrary. -/
theorem geometricStalk_isNoetherianRing (y : GeometricFiber f s K) :
    IsNoetherianRing ((GeometricFiber f s K).presheaf.stalk y) := by
  let := fieldProjection_locallyOfFiniteType f s K
  exact NodeCompletedLocalCoherentUV.stalk_isNoetherianRing (fieldProjection f s K) y

/-- Essential finite type uses the SAME actual native field-stalk coefficients. -/
theorem geometricStalk_essFiniteType (y : GeometricFiber f s K) :
    letI := Scheme.stalkAlgebra (fieldProjection f s K) y
    Algebra.EssFiniteType K ((GeometricFiber f s K).presheaf.stalk y) := by
  let := fieldProjection_locallyOfFiniteType f s K
  exact NodeCompletedLocalCoherentUV.stalkAlgebra_essFiniteType (fieldProjection f s K) y

/-- An actual coefficient-compatible completed geometric FIELD-FIBRE uv model gives the
completion of the ORIGINAL geometric-stalk Ω as the literal B²/B(v,u). -/
def geometricCoherentUVEquiv (y : GeometricFiber f s K) :
    letI := Scheme.stalkAlgebra (fieldProjection f s K) y
    letI := Scheme.completedLocalRingAlgebra (fieldProjection f s K) y
    (e : (GeometricFiber f s K).completedLocalRing y ≃ₐ[K] FormalUV K) →
      letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e.toRingEquiv
      letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm.toRingEquiv
      LocalOmega K ((GeometricFiber f s K).presheaf.stalk y) ≃ₛₗ[e.toRingHom] DifferentialModule K := by
  letI := fieldProjection_locallyOfFiniteType f s K
  exact NodeCompletedLocalCoherentUV.coherentUVEquiv (fieldProjection f s K) y

/-- Native finite presentation of the completed ORIGINAL coherent module is deduced
internally on this same actual geometric stalk. -/
theorem geometricCompletedOmega_finitePresentation (y : GeometricFiber f s K) :
    letI := Scheme.stalkAlgebra (fieldProjection f s K) y
    Module.FinitePresentation ((GeometricFiber f s K).completedLocalRing y)
      (LocalOmega K ((GeometricFiber f s K).presheaf.stalk y)) := by
  let := Scheme.stalkAlgebra (fieldProjection f s K) y
  let := geometricStalk_isNoetherianRing f s K y
  let := geometricStalk_essFiniteType f s K y
  exact completedOmega_finitePresentation K ((GeometricFiber f s K).presheaf.stalk y)
    (maximalIdeal ((GeometricFiber f s K).presheaf.stalk y))

/-- Every actual completed scalar is retained through the SAME geometric model e. -/
theorem geometricCoherentUVEquiv_smul (y : GeometricFiber f s K) :
    letI := Scheme.stalkAlgebra (fieldProjection f s K) y
    letI := Scheme.completedLocalRingAlgebra (fieldProjection f s K) y
    ∀ (e : (GeometricFiber f s K).completedLocalRing y ≃ₐ[K] FormalUV K)
      (a : (GeometricFiber f s K).completedLocalRing y)
      (ω : LocalOmega K ((GeometricFiber f s K).presheaf.stalk y)),
      geometricCoherentUVEquiv f s K y e (a • ω) = e a • geometricCoherentUVEquiv f s K y e ω := by
  let := fieldProjection_locallyOfFiniteType f s K
  exact NodeCompletedLocalCoherentUV.coherentUVEquiv_smul (fieldProjection f s K) y

/-- Both actual coordinate-preimage differential classes survive the SAME comparison. -/
theorem geometricCoherentUVEquiv_coordinate (y : GeometricFiber f s K) :
    letI := Scheme.stalkAlgebra (fieldProjection f s K) y
    letI := Scheme.completedLocalRingAlgebra (fieldProjection f s K) y
    ∀ (e : (GeometricFiber f s K).completedLocalRing y ≃ₐ[K] FormalUV K) (i : Fin 2),
      geometricCoherentUVEquiv f s K y e
        (completedUniversalDerivation K ((GeometricFiber f s K).presheaf.stalk y)
          (maximalIdeal ((GeometricFiber f s K).presheaf.stalk y)) (e.symm (coordinate K i))) =
        Submodule.Quotient.mk (Pi.single i 1) := by
  let := fieldProjection_locallyOfFiniteType f s K
  exact NodeCompletedLocalCoherentUV.coherentUVEquiv_coordinate (fieldProjection f s K) y

omit [LocallyOfFiniteType f] in
/-- The completed uv model preserves every ORIGINAL residue-field coefficient through the
actual field extension and the actual structure map, not just the final residue. -/
theorem geometricModel_originalCoefficient (y : GeometricFiber f s K) :
    letI := Scheme.completedLocalRingAlgebra (fieldProjection f s K) y
    ∀ (e : (GeometricFiber f s K).completedLocalRing y ≃ₐ[K] FormalUV K) (a : S.residueField s),
      e ((GeometricFiber f s K).toCompletedLocalRing y
        (Scheme.baseToStalk (fieldProjection f s K) y (algebraMap (S.residueField s) K a))) =
      algebraMap K (FormalUV K) (algebraMap (S.residueField s) K a) := by
  let := Scheme.completedLocalRingAlgebra (fieldProjection f s K) y
  exact fun e a => e.commutes (algebraMap (S.residueField s) K a)

end Hironaka.Geometry.NodeCompletedLocalGeometricFiberUV
