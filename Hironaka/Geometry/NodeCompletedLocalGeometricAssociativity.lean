import Hironaka.Geometry.NodeCompletedLocalGeometricChart
import Hironaka.Geometry.NodeCompletedLocalGeometricFiberUV

/-! Literal actual geometric fibre associativity, preserving BOTH original projections
and its actual completed field-algebra map at the SAME original geometric point. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.NodeCompletedLocalGeometricAssociativity

open NodeCompletedLocalGeometricChart NodeCompletedLocalGeometricFiberUV

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
  (K : Type u) [Field K] [Algebra (S.residueField s) K]

/-- The native associativity isomorphism between the TWO actual original geometric fibres. -/
def geometricFiberIso : GeometricFiber f s K ≅ OriginalGeometricScheme f s K :=
  pullbackLeftPullbackSndIso f (S.fromSpecResidueField s)
    (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)))

/-- The ENTIRE original-source projection survives the SAME actual associativity isomorphism. -/
theorem geometricFiberIso_source :
    (geometricFiberIso f s K).hom ≫ pullback.fst f (originalFieldMap s K) =
      pullback.fst (f.fiberToSpecResidueField s)
        (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K))) ≫ f.fiberι s :=
  pullbackLeftPullbackSndIso_hom_fst _ _ _

/-- The ENTIRE original geometric-field projection also survives this SAME actual map. -/
theorem geometricFiberIso_field :
    (geometricFiberIso f s K).hom ≫ pullback.snd f (originalFieldMap s K) =
      fieldProjection f s K :=
  pullbackLeftPullbackSndIso_hom_snd _ _ _

/-- The native completed local-ring equivalence at the SAME actual original geometric point,
over the WHOLE actual field action, independent of any node/model/Noetherian hypothesis. -/
def completedFieldEquiv (y : GeometricFiber f s K) :
    letI := Scheme.completedLocalRingAlgebra (pullback.snd f (originalFieldMap s K))
      ((geometricFiberIso f s K).hom y)
    letI := Scheme.completedLocalRingAlgebra (fieldProjection f s K) y
    (OriginalGeometricScheme f s K).completedLocalRing ((geometricFiberIso f s K).hom y)
      ≃ₐ[K] (GeometricFiber f s K).completedLocalRing y :=
  Scheme.completedLocalRingAlgEquivOfIsoOver (geometricFiberIso f s K)
    (fieldProjection f s K) (pullback.snd f (originalFieldMap s K))
    (geometricFiberIso_field f s K) y

/-- The ENTIRE actual completed map is the native induced original associativity map. -/
theorem completedFieldEquiv_toRingEquiv (y : GeometricFiber f s K) :
    letI := Scheme.completedLocalRingAlgebra (pullback.snd f (originalFieldMap s K))
      ((geometricFiberIso f s K).hom y)
    letI := Scheme.completedLocalRingAlgebra (fieldProjection f s K) y
    (completedFieldEquiv f s K y).toRingEquiv =
      Scheme.completedLocalRingRingEquivOfIso (geometricFiberIso f s K) y :=
  NodeCompletedLocalActualAffineUV.completedOver_toRingEquiv (geometricFiberIso f s K) K
    (fieldProjection f s K) (pullback.snd f (originalFieldMap s K))
    (geometricFiberIso_field f s K) y

/-- EVERY original direct-fibre stalk element retains its actual associativity stalk image. -/
theorem completedFieldEquiv_original (y : GeometricFiber f s K)
    (a : (OriginalGeometricScheme f s K).presheaf.stalk ((geometricFiberIso f s K).hom y)) :
    letI := Scheme.completedLocalRingAlgebra (pullback.snd f (originalFieldMap s K))
      ((geometricFiberIso f s K).hom y)
    letI := Scheme.completedLocalRingAlgebra (fieldProjection f s K) y
    completedFieldEquiv f s K y
      ((OriginalGeometricScheme f s K).toCompletedLocalRing ((geometricFiberIso f s K).hom y) a) =
      (GeometricFiber f s K).toCompletedLocalRing y ((geometricFiberIso f s K).hom.stalkMap y a) := by
  let := Scheme.completedLocalRingAlgebra (pullback.snd f (originalFieldMap s K))
    ((geometricFiberIso f s K).hom y)
  let := Scheme.completedLocalRingAlgebra (fieldProjection f s K) y
  change (completedFieldEquiv f s K y).toRingEquiv _ = _
  rw [completedFieldEquiv_toRingEquiv]
  exact Scheme.completedLocalRingRingEquivOfIso_toCompletedLocalRing (geometricFiberIso f s K) y a

end Hironaka.Geometry.NodeCompletedLocalGeometricAssociativity
