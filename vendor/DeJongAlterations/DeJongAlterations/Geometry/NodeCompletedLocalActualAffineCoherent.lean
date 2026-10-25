import DeJongAlterations.Geometry.NodeCompletedLocalActualAffineUV

/-! ORIGINAL relative Ω pulled to the ACTUAL geometric scheme point and compared
with its completed ORIGINAL field-stalk Ω, independently of any node model. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing

namespace DeJongAlterations.Geometry.NodeCompletedLocalActualAffineCoherent

open NodeCompletedLocalAffineBaseChangeUV NodeCompletedLocalActualAffineUV
  Algebra.NodeGeometricCompletionOriginalBaseChange
  Algebra.NodeGeometricCompletionCoherentDifferentials
  Algebra.NodeGeometricCompletionDifferentialTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000

universe u
variable (A R K : Type u) [CommRing A] [CommRing R] [Field K]
  [Algebra A R] [Algebra A K] [Algebra.FiniteType A R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  NodeCompletedLocalActualAffineUV.actualOriginalAlgebra
  NodeCompletedLocalActualAffineUV.actualFieldAlgebra
  NodeCompletedLocalActualAffineUV.actualCompletedOriginalAlgebra
  NodeCompletedLocalActualAffineUV.actualCompletedFieldAlgebra
  NodeCompletedLocalActualAffineUV.tensorOriginalAlgebra
  NodeCompletedLocalActualAffineUV.tensorFieldAlgebra
  NodeCompletedLocalActualAffineUV.tensorCompletedOriginalAlgebra
  NodeCompletedLocalActualAffineUV.tensorCompletedFieldAlgebra

/-- The actual tensor-spectrum field structure map is locally finite type internally. -/
theorem tensorFieldProjection_locallyOfFiniteType :
    LocallyOfFiniteType (tensorFieldProjection A R K) := by
  let : Algebra.FiniteType K (ScalarExtension A R K) := inferInstance
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
  exact RingHom.finiteType_algebraMap.mpr inferInstance

local instance actualStalkNoetherian (y : ActualBaseChange A R K) :
    IsNoetherianRing ((ActualBaseChange A R K).presheaf.stalk y) := by
  let := fieldProjection_locallyOfFiniteType A R K
  exact NodeCompletedLocalCoherentUV.stalk_isNoetherianRing (fieldProjection A R K) y

local instance actualStalkEssFiniteType (y : ActualBaseChange A R K) :
    Algebra.EssFiniteType K ((ActualBaseChange A R K).presheaf.stalk y) := by
  let := fieldProjection_locallyOfFiniteType A R K
  exact NodeCompletedLocalCoherentUV.stalkAlgebra_essFiniteType (fieldProjection A R K) y

local instance tensorStalkNoetherian (y : ActualBaseChange A R K) :
    IsNoetherianRing ((Spec (.of (ScalarExtension A R K))).presheaf.stalk ((actualTensorIso A R K).hom y)) := by
  let := tensorFieldProjection_locallyOfFiniteType A R K
  exact NodeCompletedLocalCoherentUV.stalk_isNoetherianRing (tensorFieldProjection A R K)
    ((actualTensorIso A R K).hom y)

local instance tensorStalkEssFiniteType (y : ActualBaseChange A R K) :
    Algebra.EssFiniteType K
      ((Spec (.of (ScalarExtension A R K))).presheaf.stalk ((actualTensorIso A R K).hom y)) := by
  let := tensorFieldProjection_locallyOfFiniteType A R K
  exact NodeCompletedLocalCoherentUV.stalkAlgebra_essFiniteType (tensorFieldProjection A R K)
    ((actualTensorIso A R K).hom y)

omit [Algebra.FiniteType A R] in
/-- Cancellation for the WHOLE actual completed ring map, independently of any node model. -/
theorem completedField_cancelOriginal (y : ActualBaseChange A R K)
    (a : (ActualBaseChange A R K).completedLocalRing y) :
    (completedFieldEquiv A R K y) ((completedOriginalEquiv A R K y).symm a) = a := by
  change (completedFieldEquiv A R K y).toRingEquiv
    ((completedOriginalEquiv A R K y).toRingEquiv.symm a) = a
  rw [← completedOriginalEquiv_eq_completedFieldEquiv]
  exact (completedOriginalEquiv A R K y).apply_symm_apply a

set_option maxHeartbeats 800000 in
/-- Genuine native completed ORIGINAL-relative to ORIGINAL-field-stalk differential map
at the SAME ACTUAL geometric scheme-pullback point; there is NO node-model input. -/
def actualRelativeCoherentMap (y : ActualBaseChange A R K) :
    ((ActualBaseChange A R K).completedLocalRing y ⊗[R] KaehlerDifferential A R)
      →ₗ[(ActualBaseChange A R K).completedLocalRing y]
        LocalOmega K ((ActualBaseChange A R K).presheaf.stalk y) := by
  let q := (actualTensorIso A R K).hom y
  let L := (Spec (.of (ScalarExtension A R K))).presheaf.stalk q
  letI := nativeSpecStalkAlgebra (ScalarExtension A R K) q
  letI := nativeSpecStalkLocalization (ScalarExtension A R K) q
  letI := specStalk_scalarTower R (ScalarExtension A R K) q
  letI := specStalk_scalarTower K (ScalarExtension A R K) q
  let U := tensorCoefficientMap (M := KaehlerDifferential A R) (completedOriginalEquiv A R K y).symm
  let G := (completedOriginalBaseChangeEquiv A R K L q.asIdeal (maximalIdeal L)).toLinearMap
  refine {
    toFun := fun ω =>
      differentialFun K L ((ActualBaseChange A R K).presheaf.stalk y)
        (completedFieldEquiv A R K y) (G (U ω))
    map_add' := ?_
    map_smul' := ?_ }
  · intro ω η
    rw [U.map_add, G.map_add, differentialFun_add]
  · intro a ω
    rw [U.map_smulₛₗ, G.map_smul, differentialFun_smul]
    change (completedFieldEquiv A R K y) ((completedOriginalEquiv A R K y).symm a) • _ = a • _
    rw [completedField_cancelOriginal]

/-- The actual relative coherent comparison is bijective, with NO node-model premise. -/
def actualRelativeCoherentEquiv (y : ActualBaseChange A R K) :
    ((ActualBaseChange A R K).completedLocalRing y ⊗[R] KaehlerDifferential A R)
      ≃ₗ[(ActualBaseChange A R K).completedLocalRing y]
        LocalOmega K ((ActualBaseChange A R K).presheaf.stalk y) := by
  let q := (actualTensorIso A R K).hom y
  let L := (Spec (.of (ScalarExtension A R K))).presheaf.stalk q
  letI := nativeSpecStalkAlgebra (ScalarExtension A R K) q
  letI := nativeSpecStalkLocalization (ScalarExtension A R K) q
  letI := specStalk_scalarTower R (ScalarExtension A R K) q
  letI := specStalk_scalarTower K (ScalarExtension A R K) q
  letI : RingHomInvPair (completedFieldEquiv A R K y).toRingHom
      (completedFieldEquiv A R K y).symm.toRingHom :=
    RingHomInvPair.of_ringEquiv (completedFieldEquiv A R K y).toRingEquiv
  letI : RingHomInvPair (completedFieldEquiv A R K y).symm.toRingHom
      (completedFieldEquiv A R K y).toRingHom :=
    RingHomInvPair.of_ringEquiv (completedFieldEquiv A R K y).symm.toRingEquiv
  exact LinearEquiv.ofBijective (actualRelativeCoherentMap A R K y)
    ((differentialEquiv K L ((ActualBaseChange A R K).presheaf.stalk y)
      (completedFieldEquiv A R K y)).bijective.comp
      ((completedOriginalBaseChangeEquiv A R K L q.asIdeal (maximalIdeal L)).bijective.comp
        (tensorCoefficientEquiv (M := KaehlerDifferential A R)
          (completedOriginalEquiv A R K y).symm).bijective))

omit [Algebra.FiniteType A R] in
/-- The SAME canonical actual completed field map retains EVERY original R-coefficient. -/
theorem completedField_originalCoefficient (y : ActualBaseChange A R K) (r : R) :
    (completedFieldEquiv A R K y)
      (algebraMap R ((Spec (.of (ScalarExtension A R K))).completedLocalRing
        ((actualTensorIso A R K).hom y)) r) =
      algebraMap R ((ActualBaseChange A R K).completedLocalRing y) r := by
  have hc (b : (Spec (.of (ScalarExtension A R K))).completedLocalRing ((actualTensorIso A R K).hom y)) :
      (completedFieldEquiv A R K y) b = (completedOriginalEquiv A R K y) b :=
    congrArg (fun ρ => ρ b) (completedOriginalEquiv_eq_completedFieldEquiv A R K y).symm
  rw [hc, (completedOriginalEquiv A R K y).commutes]

set_option maxHeartbeats 800000 in
/-- EVERY original family differential is its actual original geometric germ differential
in the SAME native module completion; no node model is needed to define or prove this square. -/
theorem actualRelativeCoherentEquiv_original (y : ActualBaseChange A R K)
    (a : (ActualBaseChange A R K).completedLocalRing y) (r : R) :
    actualRelativeCoherentEquiv A R K y (a ⊗ₜ[R] KaehlerDifferential.D A R r) =
      a • AdicCompletion.of (maximalIdeal ((ActualBaseChange A R K).presheaf.stalk y))
        (KaehlerDifferential K ((ActualBaseChange A R K).presheaf.stalk y))
        (KaehlerDifferential.D K ((ActualBaseChange A R K).presheaf.stalk y)
          (Scheme.baseToStalk (originalProjection A R K) y r)) := by
  let q := (actualTensorIso A R K).hom y
  let L := (Spec (.of (ScalarExtension A R K))).presheaf.stalk q
  let := nativeSpecStalkAlgebra (ScalarExtension A R K) q
  let := nativeSpecStalkLocalization (ScalarExtension A R K) q
  let := specStalk_scalarTower R (ScalarExtension A R K) q
  let := specStalk_scalarTower K (ScalarExtension A R K) q
  change differentialFun K L ((ActualBaseChange A R K).presheaf.stalk y)
    (completedFieldEquiv A R K y)
    (completedOriginalBaseChangeEquiv A R K L q.asIdeal (maximalIdeal L)
      ((completedOriginalEquiv A R K y).symm a ⊗ₜ[R] KaehlerDifferential.D A R r)) = _
  rw [completedOriginalBaseChangeEquiv_tmul_D, differentialFun_smul,
    completedField_cancelOriginal, ← completedUniversalDerivation_original,
    differentialFun_derivation, ← IsScalarTower.algebraMap_apply R L
      ((Spec (.of (ScalarExtension A R K))).completedLocalRing q),
    completedField_originalCoefficient, IsScalarTower.algebraMap_apply R
      ((ActualBaseChange A R K).presheaf.stalk y) ((ActualBaseChange A R K).completedLocalRing y),
    completedUniversalDerivation_original]
  rfl

/-- The ENTIRE native actual completed scalar action is linear, independently of any model. -/
theorem actualRelativeCoherentEquiv_smul (y : ActualBaseChange A R K)
    (a : (ActualBaseChange A R K).completedLocalRing y)
    (ω : (ActualBaseChange A R K).completedLocalRing y ⊗[R] KaehlerDifferential A R) :
    actualRelativeCoherentEquiv A R K y (a • ω) = a • actualRelativeCoherentEquiv A R K y ω :=
  (actualRelativeCoherentEquiv A R K y).map_smul a ω

end DeJongAlterations.Geometry.NodeCompletedLocalActualAffineCoherent
