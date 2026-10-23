import DeJongAlterations.Geometry.NodeCompletedLocalAffineBaseChangeUV

/-! ORIGINAL relative Ω on the ACTUAL scheme pullback at its ACTUAL point.
The same canonical scheme isomorphism transports BOTH original-ring and field
coefficient actions; the completed field-node model remains the original one. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing

namespace DeJongAlterations.Geometry.NodeCompletedLocalActualAffineUV

open NodeCompletedLocalAffineBaseChangeUV
  Algebra.NodeGeometricCompletionOriginalBaseChange
  Algebra.NodeGeometricCompletionFormalUV

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000

universe u

section TensorCoefficient
variable {R C D M : Type u} [CommRing R] [CommRing C] [CommRing D]
  [Algebra R C] [Algebra R D] [AddCommGroup M] [Module R M]
  (c : C ≃ₐ[R] D)

/-- Actual whole-coefficient tensor transport for the SAME original module. -/
def tensorCoefficientMap : C ⊗[R] M →ₛₗ[c.toRingHom] D ⊗[R] M where
  toFun := TensorProduct.congr c.toLinearEquiv (LinearEquiv.refl R M)
  map_add' := (TensorProduct.congr c.toLinearEquiv (LinearEquiv.refl R M)).map_add
  map_smul' a ω := by
    induction ω using TensorProduct.induction_on with
    | zero => rw [TensorProduct.smul_zero, map_zero, smul_zero]
    | tmul b m => simp [smul_tmul', smul_eq_mul, map_mul]
    | add t s ht hs => rw [TensorProduct.smul_add, map_add, map_add, ht, hs, smul_add]

local instance : RingHomInvPair c.toRingHom c.symm.toRingHom := RingHomInvPair.of_ringEquiv c.toRingEquiv
local instance : RingHomInvPair c.symm.toRingHom c.toRingHom := RingHomInvPair.of_ringEquiv c.symm.toRingEquiv

/-- The genuine native semilinear coefficient change, with no module output premise. -/
def tensorCoefficientEquiv : C ⊗[R] M ≃ₛₗ[c.toRingHom] D ⊗[R] M :=
  LinearEquiv.ofBijective (tensorCoefficientMap c)
    (TensorProduct.congr c.toLinearEquiv (LinearEquiv.refl R M)).bijective

/-- Every original-module pure tensor retains its actual whole coefficient value. -/
theorem tensorCoefficientEquiv_tmul (a : C) (m : M) :
    tensorCoefficientEquiv c (a ⊗ₜ[R] m) = c a ⊗ₜ[R] m := by
  rfl

end TensorCoefficient

/-- The whole completed ring map of an actual scheme isomorphism is independent of
which affine coefficient triangle is used to record it. -/
theorem completedOver_toRingEquiv {X Y : Scheme.{u}} (ι : X ≅ Y)
    (B : Type u) [CommRing B] (f : X ⟶ Spec (.of B)) (p : Y ⟶ Spec (.of B))
    (h : ι.hom ≫ p = f) (x : X) :
    letI := Scheme.completedLocalRingAlgebra p (ι.hom x)
    letI := Scheme.completedLocalRingAlgebra f x
    (Scheme.completedLocalRingAlgEquivOfIsoOver ι f p h x).toRingEquiv =
      Scheme.completedLocalRingRingEquivOfIso ι x := by
  subst f
  rfl

variable (A R K : Type u) [CommRing A] [CommRing R] [Field K]
  [Algebra A R] [Algebra A K]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The literal actual scheme-pullback original-family projection. -/
abbrev originalProjection : ActualBaseChange A R K ⟶ Spec (.of R) := pullback.fst _ _

/-- The literal actual scheme-pullback field structure morphism. -/
abbrev fieldProjection : ActualBaseChange A R K ⟶ Spec (.of K) := pullback.snd _ _

/-- The tensor-spectrum actual original-family projection. -/
abbrev tensorOriginalProjection : Spec (.of (ScalarExtension A R K)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (ScalarExtension A R K)))

/-- The tensor-spectrum actual field structure morphism. -/
abbrev tensorFieldProjection : Spec (.of (ScalarExtension A R K)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (ScalarExtension A R K)))

/-- The SAME canonical completed scheme-isomorphism map over the WHOLE original R. -/
def completedOriginalEquiv (y : ActualBaseChange A R K) :
    letI := Scheme.completedLocalRingAlgebra (tensorOriginalProjection A R K) ((actualTensorIso A R K).hom y)
    letI := Scheme.completedLocalRingAlgebra (originalProjection A R K) y
    (Spec (.of (ScalarExtension A R K))).completedLocalRing ((actualTensorIso A R K).hom y)
      ≃ₐ[R] (ActualBaseChange A R K).completedLocalRing y :=
  Scheme.completedLocalRingAlgEquivOfIsoOver (actualTensorIso A R K)
    (originalProjection A R K) (tensorOriginalProjection A R K) (actualTensorIso_hom_original A R K) y

/-- The SAME canonical completed scheme-isomorphism map over the WHOLE field K. -/
def completedFieldEquiv (y : ActualBaseChange A R K) :
    letI := Scheme.completedLocalRingAlgebra (tensorFieldProjection A R K) ((actualTensorIso A R K).hom y)
    letI := Scheme.completedLocalRingAlgebra (fieldProjection A R K) y
    (Spec (.of (ScalarExtension A R K))).completedLocalRing ((actualTensorIso A R K).hom y)
      ≃ₐ[K] (ActualBaseChange A R K).completedLocalRing y :=
  Scheme.completedLocalRingAlgEquivOfIsoOver (actualTensorIso A R K)
    (fieldProjection A R K) (tensorFieldProjection A R K) (actualTensorIso_hom_field A R K) y

local instance actualOriginalAlgebra (y : ActualBaseChange A R K) :
    Algebra R ((ActualBaseChange A R K).presheaf.stalk y) :=
  Scheme.stalkAlgebra (originalProjection A R K) y
local instance actualFieldAlgebra (y : ActualBaseChange A R K) :
    Algebra K ((ActualBaseChange A R K).presheaf.stalk y) :=
  Scheme.stalkAlgebra (fieldProjection A R K) y
local instance actualCompletedOriginalAlgebra (y : ActualBaseChange A R K) :
    Algebra R ((ActualBaseChange A R K).completedLocalRing y) :=
  Scheme.completedLocalRingAlgebra (originalProjection A R K) y
local instance actualCompletedFieldAlgebra (y : ActualBaseChange A R K) :
    Algebra K ((ActualBaseChange A R K).completedLocalRing y) :=
  Scheme.completedLocalRingAlgebra (fieldProjection A R K) y
local instance tensorOriginalAlgebra (y : ActualBaseChange A R K) :
    Algebra R ((Spec (.of (ScalarExtension A R K))).presheaf.stalk ((actualTensorIso A R K).hom y)) :=
  Scheme.stalkAlgebra (tensorOriginalProjection A R K) ((actualTensorIso A R K).hom y)
local instance tensorFieldAlgebra (y : ActualBaseChange A R K) :
    Algebra K ((Spec (.of (ScalarExtension A R K))).presheaf.stalk ((actualTensorIso A R K).hom y)) :=
  Scheme.stalkAlgebra (tensorFieldProjection A R K) ((actualTensorIso A R K).hom y)
local instance tensorCompletedOriginalAlgebra (y : ActualBaseChange A R K) :
    Algebra R ((Spec (.of (ScalarExtension A R K))).completedLocalRing ((actualTensorIso A R K).hom y)) :=
  Scheme.completedLocalRingAlgebra (tensorOriginalProjection A R K) ((actualTensorIso A R K).hom y)
local instance tensorCompletedFieldAlgebra (y : ActualBaseChange A R K) :
    Algebra K ((Spec (.of (ScalarExtension A R K))).completedLocalRing ((actualTensorIso A R K).hom y)) :=
  Scheme.completedLocalRingAlgebra (tensorFieldProjection A R K) ((actualTensorIso A R K).hom y)

/-- The original-ring and field coefficient equivalences have literally the SAME
underlying actual completed scheme-isomorphism map. -/
theorem completedOriginalEquiv_eq_completedFieldEquiv (y : ActualBaseChange A R K) :
    (completedOriginalEquiv A R K y).toRingEquiv = (completedFieldEquiv A R K y).toRingEquiv := by
  exact (completedOver_toRingEquiv (actualTensorIso A R K) R
    (originalProjection A R K) (tensorOriginalProjection A R K)
    (actualTensorIso_hom_original A R K) y).trans
    (completedOver_toRingEquiv (actualTensorIso A R K) K
      (fieldProjection A R K) (tensorFieldProjection A R K)
      (actualTensorIso_hom_field A R K) y).symm

variable [Algebra.FiniteType A R]

/-- Finite type of the ORIGINAL affine family gives actual field-projection LocFT
by the literal scheme base change, without a Noetherian original base. -/
theorem fieldProjection_locallyOfFiniteType : LocallyOfFiniteType (fieldProjection A R K) := by
  let : LocallyOfFiniteType (originalFamily A R) := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- Native finite presentation of the pulled ORIGINAL family Ω on this ACTUAL completed
scheme-pullback stalk follows internally, independently of any node model. -/
theorem actualCompletedOriginalOmega_finitePresentation (y : ActualBaseChange A R K) :
    Module.FinitePresentation ((ActualBaseChange A R K).completedLocalRing y)
      ((ActualBaseChange A R K).completedLocalRing y ⊗[R] KaehlerDifferential A R) := by
  let := fieldProjection_locallyOfFiniteType A R K
  let : IsNoetherianRing ((ActualBaseChange A R K).presheaf.stalk y) :=
    NodeCompletedLocalCoherentUV.stalk_isNoetherianRing (fieldProjection A R K) y
  exact Module.finitePresentation_of_finite ((ActualBaseChange A R K).completedLocalRing y)
    ((ActualBaseChange A R K).completedLocalRing y ⊗[R] KaehlerDifferential A R)

/-- The ACTUAL completed field-node model transported through the SAME scheme isomorphism. -/
def tensorNodeModel (y : ActualBaseChange A R K)
    (e : (ActualBaseChange A R K).completedLocalRing y ≃ₐ[K] FormalUV K) :
    (Spec (.of (ScalarExtension A R K))).completedLocalRing ((actualTensorIso A R K).hom y)
      ≃ₐ[K] FormalUV K :=
  (completedFieldEquiv A R K y).trans e

set_option maxHeartbeats 800000 in
/-- Genuine original-family differential map on the ACTUAL scheme-pullback point,
semilinear for the ORIGINAL e rather than a separately supplied coefficient map. -/
def actualRelativeUVMap (y : ActualBaseChange A R K)
    (e : (ActualBaseChange A R K).completedLocalRing y ≃ₐ[K] FormalUV K) :
    ((ActualBaseChange A R K).completedLocalRing y ⊗[R] KaehlerDifferential A R)
      →ₛₗ[e.toRingHom] DifferentialModule K := by
  let U := tensorCoefficientMap (M := KaehlerDifferential A R)
    (completedOriginalEquiv A R K y).symm
  letI : RingHomInvPair (tensorNodeModel A R K y e).toRingHom
      (tensorNodeModel A R K y e).symm.toRingHom :=
    RingHomInvPair.of_ringEquiv (tensorNodeModel A R K y e).toRingEquiv
  letI : RingHomInvPair (tensorNodeModel A R K y e).symm.toRingHom
      (tensorNodeModel A R K y e).toRingHom :=
    RingHomInvPair.of_ringEquiv (tensorNodeModel A R K y e).symm.toRingEquiv
  let F := (actualAffineStalkRelativeUVEquiv A R K ((actualTensorIso A R K).hom y)
    (tensorNodeModel A R K y e)).toLinearMap
  refine { toFun := fun ω => F (U ω), map_add' := ?_, map_smul' := ?_ }
  · intro ω η
    rw [U.map_add, F.map_add]
  · intro a ω
    rw [U.map_smulₛₗ, F.map_smulₛₗ]
    change e ((completedFieldEquiv A R K y) ((completedOriginalEquiv A R K y).symm a)) • _ = e a • _
    have h : (completedFieldEquiv A R K y) ((completedOriginalEquiv A R K y).symm a) = a := by
      change (completedFieldEquiv A R K y).toRingEquiv
        ((completedOriginalEquiv A R K y).toRingEquiv.symm a) = a
      rw [← completedOriginalEquiv_eq_completedFieldEquiv]
      exact (completedOriginalEquiv A R K y).apply_symm_apply a
    rw [h]

/-- The ORIGINAL family coherent differential module on the ACTUAL completed geometric
scheme-pullback point has the literal uv row, retaining the SAME given completed model e. -/
def actualRelativeUVEquiv (y : ActualBaseChange A R K)
    (e : (ActualBaseChange A R K).completedLocalRing y ≃ₐ[K] FormalUV K) :
    letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e.toRingEquiv
    letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm.toRingEquiv
    ((ActualBaseChange A R K).completedLocalRing y ⊗[R] KaehlerDifferential A R)
      ≃ₛₗ[e.toRingHom] DifferentialModule K := by
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e.toRingEquiv
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm.toRingEquiv
  exact LinearEquiv.ofBijective (actualRelativeUVMap A R K y e)
    ((actualAffineStalkRelativeUVEquiv A R K ((actualTensorIso A R K).hom y)
      (tensorNodeModel A R K y e)).bijective.comp
      (tensorCoefficientEquiv (M := KaehlerDifferential A R)
        (completedOriginalEquiv A R K y).symm).bijective)

/-- Every original-module tensor keeps its exact original coefficient transport. -/
theorem actualRelativeUVEquiv_tmul (y : ActualBaseChange A R K)
    (e : (ActualBaseChange A R K).completedLocalRing y ≃ₐ[K] FormalUV K)
    (a : (ActualBaseChange A R K).completedLocalRing y) (ω : KaehlerDifferential A R) :
    actualRelativeUVEquiv A R K y e (a ⊗ₜ[R] ω) =
      actualAffineStalkRelativeUVEquiv A R K ((actualTensorIso A R K).hom y)
        (tensorNodeModel A R K y e) ((completedOriginalEquiv A R K y).symm a ⊗ₜ[R] ω) := by
  rfl

omit [Algebra.FiniteType A R] in
/-- The ENTIRE original R-coefficient triangle passes through the SAME original node e. -/
theorem tensorNodeModel_originalCoefficient (y : ActualBaseChange A R K)
    (e : (ActualBaseChange A R K).completedLocalRing y ≃ₐ[K] FormalUV K) (r : R) :
    tensorNodeModel A R K y e
      (algebraMap R ((Spec (.of (ScalarExtension A R K))).completedLocalRing
        ((actualTensorIso A R K).hom y)) r) =
      e (algebraMap R ((ActualBaseChange A R K).completedLocalRing y) r) := by
  have hc (b : (Spec (.of (ScalarExtension A R K))).completedLocalRing ((actualTensorIso A R K).hom y)) :
      (completedFieldEquiv A R K y) b = (completedOriginalEquiv A R K y) b :=
    congrArg (fun ρ => ρ b) (completedOriginalEquiv_eq_completedFieldEquiv A R K y).symm
  change e ((completedFieldEquiv A R K y) _) = _
  rw [hc, (completedOriginalEquiv A R K y).commutes]

omit [Algebra.FiniteType A R] in
/-- The whole scalar cancellation retains the ORIGINAL completed field-node model. -/
theorem tensorNodeModel_cancel (y : ActualBaseChange A R K)
    (e : (ActualBaseChange A R K).completedLocalRing y ≃ₐ[K] FormalUV K)
    (a : (ActualBaseChange A R K).completedLocalRing y) :
    tensorNodeModel A R K y e ((completedOriginalEquiv A R K y).symm a) = e a := by
  change e ((completedFieldEquiv A R K y) ((completedOriginalEquiv A R K y).symm a)) = _
  have hc : (completedFieldEquiv A R K y) ((completedOriginalEquiv A R K y).symm a) =
      (completedOriginalEquiv A R K y) ((completedOriginalEquiv A R K y).symm a) :=
    congrArg (fun ρ => ρ ((completedOriginalEquiv A R K y).symm a))
      (completedOriginalEquiv_eq_completedFieldEquiv A R K y).symm
  rw [hc, AlgEquiv.apply_symm_apply]

/-- The actual pullback comparison retains EVERY original family differential as its
actual geometric completed derivative through the SAME original field-node model e. -/
theorem actualRelativeUVEquiv_original (y : ActualBaseChange A R K)
    (e : (ActualBaseChange A R K).completedLocalRing y ≃ₐ[K] FormalUV K)
    (a : (ActualBaseChange A R K).completedLocalRing y) (r : R) :
    actualRelativeUVEquiv A R K y e (a ⊗ₜ[R] KaehlerDifferential.D A R r) =
      e a • Algebra.NodeGeometricCompletionLocalUV.localOmegaGradientEquiv K
        (Algebra.NodeGeometricCompletionCoherentDifferentials.completedUniversalDerivation K
          (Algebra.NodeGeometricCompletionLocalUV.LocalUV K)
          (maximalIdeal (Algebra.NodeGeometricCompletionLocalUV.LocalUV K))
          ((Algebra.NodeGeometricCompletionLocalUV.localCompletionFieldEquiv K).symm
            (e (algebraMap R ((ActualBaseChange A R K).completedLocalRing y) r)))) := by
  let q := (actualTensorIso A R K).hom y
  let L := (Spec (.of (ScalarExtension A R K))).presheaf.stalk q
  let := nativeSpecStalkAlgebra (ScalarExtension A R K) q
  let := nativeSpecStalkLocalization (ScalarExtension A R K) q
  let := specStalk_scalarTower R (ScalarExtension A R K) q
  let := specStalk_scalarTower K (ScalarExtension A R K) q
  rw [actualRelativeUVEquiv_tmul]
  change Algebra.NodeGeometricCompletionOriginalBaseChangeUV.originalCompletedUVEquiv
    A R K L q.asIdeal (tensorNodeModel A R K y e)
    ((completedOriginalEquiv A R K y).symm a ⊗ₜ[R] KaehlerDifferential.D A R r) = _
  rw [Algebra.NodeGeometricCompletionOriginalBaseChangeUV.originalCompletedUVEquiv_original,
    tensorNodeModel_cancel, ← IsScalarTower.algebraMap_apply R L
      ((Spec (.of (ScalarExtension A R K))).completedLocalRing q), tensorNodeModel_originalCoefficient]

/-- The ENTIRE actual completed scalar action passes through the SAME original model e. -/
theorem actualRelativeUVEquiv_smul (y : ActualBaseChange A R K)
    (e : (ActualBaseChange A R K).completedLocalRing y ≃ₐ[K] FormalUV K)
    (a : (ActualBaseChange A R K).completedLocalRing y)
    (ω : (ActualBaseChange A R K).completedLocalRing y ⊗[R] KaehlerDifferential A R) :
    actualRelativeUVEquiv A R K y e (a • ω) = e a • actualRelativeUVEquiv A R K y e ω :=
  (actualRelativeUVEquiv A R K y e).map_smulₛₗ a ω

end DeJongAlterations.Geometry.NodeCompletedLocalActualAffineUV
