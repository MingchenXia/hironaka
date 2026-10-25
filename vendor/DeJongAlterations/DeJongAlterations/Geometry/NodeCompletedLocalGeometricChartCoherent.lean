import DeJongAlterations.Geometry.NodeCompletedLocalGeometricChartCompletion
import DeJongAlterations.Geometry.NodeCompletedLocalActualAffineCoherent

/-! Completion of the ORIGINAL chart-relative Ω at the SAME actual geometric-fibre
point, compared to the completed ORIGINAL field-stalk Ω without any node-model premise. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing

namespace DeJongAlterations.Geometry.NodeCompletedLocalGeometricChartCoherent

open Algebra.NodeFittingOmegaCharts NodeCompletedLocalAffineBaseChangeUV
  NodeCompletedLocalGeometricChart NodeCompletedLocalGeometricChartCompletion
  Algebra.NodeGeometricCompletionCoherentDifferentials
  Algebra.NodeGeometricCompletionDifferentialTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (C : Chart f)
  (s : S) (hs : s ∈ C.base.1) (K : Type u) [Field K] [Algebra (S.residueField s) K]

local instance originalChartAlgebra : Algebra Γ(S, C.base.1) Γ(X, C.source.1) := C.algebra f
local instance originalChartFiniteType : Algebra.FiniteType Γ(S, C.base.1) Γ(X, C.source.1) :=
  chartAlgebra_finiteType f C

local notation "Z" => ChartScheme f C s hs K
local notation "Y" => OriginalGeometricScheme f s K
local notation "j" => chartMap f C s hs K
local notation "q" => pullback.snd f (originalFieldMap s K)

attribute [local instance]
  NodeCompletedLocalActualAffineUV.actualOriginalAlgebra
  NodeCompletedLocalActualAffineUV.actualFieldAlgebra
  NodeCompletedLocalActualAffineUV.actualCompletedOriginalAlgebra
  NodeCompletedLocalActualAffineUV.actualCompletedFieldAlgebra
  NodeCompletedLocalGeometricChartCompletion.originalStalkAlgebra
  NodeCompletedLocalGeometricChartCompletion.originalCompletedAlgebra

local instance sourceOriginalAlgebra (z : Z) : Algebra Γ(X, C.source.1) ((Z).presheaf.stalk z) :=
  Scheme.stalkAlgebra (chartOriginalProjection f C s hs K) z
local instance sourceCompletedOriginalAlgebra (z : Z) : Algebra Γ(X, C.source.1) ((Z).completedLocalRing z) :=
  Scheme.completedLocalRingAlgebra (chartOriginalProjection f C s hs K) z
local instance sourceFieldAlgebra (z : Z) : Algebra K ((Z).presheaf.stalk z) :=
  Scheme.stalkAlgebra (chartFieldProjection f C s hs K) z
local instance sourceCompletedFieldAlgebra (z : Z) : Algebra K ((Z).completedLocalRing z) :=
  Scheme.completedLocalRingAlgebra (chartFieldProjection f C s hs K) z

local instance targetFieldAlgebra (z : Z) : Algebra K ((Y).presheaf.stalk (j z)) :=
  Scheme.stalkAlgebra q (j z)
local instance targetCompletedFieldAlgebra (z : Z) : Algebra K ((Y).completedLocalRing (j z)) :=
  Scheme.completedLocalRingAlgebra q (j z)

local instance sourceStalkNoetherian (z : Z) : IsNoetherianRing ((Z).presheaf.stalk z) := by
  let := chartFieldAlgebra f C s hs K
  let := NodeCompletedLocalActualAffineUV.fieldProjection_locallyOfFiniteType
    Γ(S, C.base.1) Γ(X, C.source.1) K
  exact NodeCompletedLocalCoherentUV.stalk_isNoetherianRing
    (NodeCompletedLocalActualAffineUV.fieldProjection Γ(S, C.base.1) Γ(X, C.source.1) K) z
local instance sourceStalkEssFiniteType (z : Z) : Algebra.EssFiniteType K ((Z).presheaf.stalk z) := by
  let := chartFieldAlgebra f C s hs K
  let := NodeCompletedLocalActualAffineUV.fieldProjection_locallyOfFiniteType
    Γ(S, C.base.1) Γ(X, C.source.1) K
  exact NodeCompletedLocalCoherentUV.stalkAlgebra_essFiniteType
    (NodeCompletedLocalActualAffineUV.fieldProjection Γ(S, C.base.1) Γ(X, C.source.1) K) z
local instance targetStalkNoetherian (z : Z) : IsNoetherianRing ((Y).presheaf.stalk (j z)) := by
  let : LocallyOfFiniteType q := inferInstance
  exact NodeCompletedLocalCoherentUV.stalk_isNoetherianRing q (j z)
local instance targetStalkEssFiniteType (z : Z) : Algebra.EssFiniteType K ((Y).presheaf.stalk (j z)) := by
  let : LocallyOfFiniteType q := inferInstance
  exact NodeCompletedLocalCoherentUV.stalkAlgebra_essFiniteType q (j z)

omit [LocallyOfFiniteType f] in
/-- Equality of the two WHOLE native completed maps cancels every actual target scalar. -/
theorem completedField_cancelOriginal (z : Z) (a : (Y).completedLocalRing (j z)) :
    (completedFieldEquiv f C s hs K z).symm ((completedOriginalEquiv f C s hs K z) a) = a := by
  change (completedFieldEquiv f C s hs K z).toRingEquiv.symm
    ((completedOriginalEquiv f C s hs K z).toRingEquiv a) = a
  rw [completedOriginalEquiv_eq_completedFieldEquiv]
  exact (completedFieldEquiv f C s hs K z).symm_apply_apply a

set_option maxHeartbeats 800000 in
/-- The ACTUAL original-relative coherent map at the SAME geometric point, with ALL
original section coefficients coming from their original germs and projection stalk map. -/
def actualRelativeCoherentMap (z : Z) :
    ((Y).completedLocalRing (j z) ⊗[Γ(X, C.source.1)]
      KaehlerDifferential Γ(S, C.base.1) Γ(X, C.source.1))
      →ₗ[(Y).completedLocalRing (j z)] LocalOmega K ((Y).presheaf.stalk (j z)) := by
  letI := chartFieldAlgebra f C s hs K
  let U := NodeCompletedLocalActualAffineUV.tensorCoefficientMap
    (M := KaehlerDifferential Γ(S, C.base.1) Γ(X, C.source.1))
    (completedOriginalEquiv f C s hs K z)
  let G := (NodeCompletedLocalActualAffineCoherent.actualRelativeCoherentEquiv
    Γ(S, C.base.1) Γ(X, C.source.1) K z).toLinearMap
  refine {
    toFun := fun ω => differentialFun K ((Z).presheaf.stalk z) ((Y).presheaf.stalk (j z))
      (completedFieldEquiv f C s hs K z).symm (G (U ω))
    map_add' := ?_
    map_smul' := ?_ }
  · intro ω η
    rw [U.map_add, G.map_add, differentialFun_add]
  · intro a ω
    rw [U.map_smulₛₗ, G.map_smul, differentialFun_smul]
    change (completedFieldEquiv f C s hs K z).symm
      (completedOriginalEquiv f C s hs K z a) • _ = a • _
    rw [completedField_cancelOriginal]

/-- The genuine actual original-relative coherent map is bijective without a node model. -/
def actualRelativeCoherentEquiv (z : Z) :
    ((Y).completedLocalRing (j z) ⊗[Γ(X, C.source.1)]
      KaehlerDifferential Γ(S, C.base.1) Γ(X, C.source.1))
      ≃ₗ[(Y).completedLocalRing (j z)] LocalOmega K ((Y).presheaf.stalk (j z)) := by
  letI := chartFieldAlgebra f C s hs K
  letI : RingHomInvPair (completedFieldEquiv f C s hs K z).symm.toRingHom
      (completedFieldEquiv f C s hs K z).toRingHom :=
    RingHomInvPair.of_ringEquiv (completedFieldEquiv f C s hs K z).symm.toRingEquiv
  letI : RingHomInvPair (completedFieldEquiv f C s hs K z).toRingHom
      (completedFieldEquiv f C s hs K z).symm.toRingHom :=
    RingHomInvPair.of_ringEquiv (completedFieldEquiv f C s hs K z).toRingEquiv
  exact LinearEquiv.ofBijective (actualRelativeCoherentMap f C s hs K z)
    ((differentialEquiv K ((Z).presheaf.stalk z) ((Y).presheaf.stalk (j z))
      (completedFieldEquiv f C s hs K z).symm).bijective.comp
      ((NodeCompletedLocalActualAffineCoherent.actualRelativeCoherentEquiv
        Γ(S, C.base.1) Γ(X, C.source.1) K z).bijective.comp
        (NodeCompletedLocalActualAffineUV.tensorCoefficientEquiv
          (M := KaehlerDifferential Γ(S, C.base.1) Γ(X, C.source.1))
          (completedOriginalEquiv f C s hs K z)).bijective))

omit [LocallyOfFiniteType f] in
/-- The inverse of the SAME actual field map preserves EVERY natural original coefficient. -/
theorem completedField_symm_originalCoefficient (z : Z) (r : Γ(X, C.source.1)) :
    (completedFieldEquiv f C s hs K z).symm
      (algebraMap Γ(X, C.source.1) ((Z).completedLocalRing z) r) =
      algebraMap Γ(X, C.source.1) ((Y).completedLocalRing (j z)) r := by
  apply (completedFieldEquiv f C s hs K z).injective
  rw [AlgEquiv.apply_symm_apply, completedFieldEquiv_originalCoefficient]

set_option maxHeartbeats 800000 in
/-- EVERY original family differential is exactly its ORIGINAL section-germ differential
under the ACTUAL original-source projection, at the SAME actual geometric point. -/
theorem actualRelativeCoherentEquiv_original (z : Z)
    (a : (Y).completedLocalRing (j z)) (r : Γ(X, C.source.1)) :
    actualRelativeCoherentEquiv f C s hs K z
      (a ⊗ₜ[Γ(X, C.source.1)] KaehlerDifferential.D Γ(S, C.base.1) Γ(X, C.source.1) r) =
      a • AdicCompletion.of (maximalIdeal ((Y).presheaf.stalk (j z)))
        (KaehlerDifferential K ((Y).presheaf.stalk (j z)))
        (KaehlerDifferential.D K ((Y).presheaf.stalk (j z))
          (originalCoefficient f C s hs K z r)) := by
  let := chartFieldAlgebra f C s hs K
  change differentialFun K ((Z).presheaf.stalk z) ((Y).presheaf.stalk (j z))
    (completedFieldEquiv f C s hs K z).symm
    (NodeCompletedLocalActualAffineCoherent.actualRelativeCoherentEquiv
      Γ(S, C.base.1) Γ(X, C.source.1) K z
      (completedOriginalEquiv f C s hs K z a ⊗ₜ[Γ(X, C.source.1)]
        KaehlerDifferential.D Γ(S, C.base.1) Γ(X, C.source.1) r)) = _
  rw [NodeCompletedLocalActualAffineCoherent.actualRelativeCoherentEquiv_original,
    differentialFun_smul, completedField_cancelOriginal,
    ← completedUniversalDerivation_original, differentialFun_derivation]
  change a • completedUniversalDerivation K ((Y).presheaf.stalk (j z))
    (maximalIdeal ((Y).presheaf.stalk (j z)))
    ((completedFieldEquiv f C s hs K z).symm
      (algebraMap Γ(X, C.source.1) ((Z).completedLocalRing z) r)) = _
  rw [completedField_symm_originalCoefficient]
  change a • completedUniversalDerivation K ((Y).presheaf.stalk (j z))
    (maximalIdeal ((Y).presheaf.stalk (j z)))
    (algebraMap ((Y).presheaf.stalk (j z)) ((Y).completedLocalRing (j z))
      (originalCoefficient f C s hs K z r)) = _
  rw [completedUniversalDerivation_original]

/-- Native finite presentation of the actual pulled ORIGINAL relative module is internal,
over an arbitrary original base and without any node-model premise. -/
theorem actualCompletedOriginalOmega_finitePresentation (z : Z) :
    Module.FinitePresentation ((Y).completedLocalRing (j z))
      ((Y).completedLocalRing (j z) ⊗[Γ(X, C.source.1)]
        KaehlerDifferential Γ(S, C.base.1) Γ(X, C.source.1)) := by
  exact Module.finitePresentation_of_finite ((Y).completedLocalRing (j z))
    ((Y).completedLocalRing (j z) ⊗[Γ(X, C.source.1)]
      KaehlerDifferential Γ(S, C.base.1) Γ(X, C.source.1))

/-- The ENTIRE native completed scalar action is linear on this SAME actual comparison. -/
theorem actualRelativeCoherentEquiv_smul (z : Z)
    (a : (Y).completedLocalRing (j z))
    (ω : (Y).completedLocalRing (j z) ⊗[Γ(X, C.source.1)]
      KaehlerDifferential Γ(S, C.base.1) Γ(X, C.source.1)) :
    actualRelativeCoherentEquiv f C s hs K z (a • ω) =
      a • actualRelativeCoherentEquiv f C s hs K z ω :=
  (actualRelativeCoherentEquiv f C s hs K z).map_smul a ω

end DeJongAlterations.Geometry.NodeCompletedLocalGeometricChartCoherent
