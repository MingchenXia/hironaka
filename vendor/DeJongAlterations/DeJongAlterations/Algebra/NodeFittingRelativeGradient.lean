import DeJongAlterations.Algebra.NodeFittingRelativeTransport
import DeJongAlterations.Algebra.NodeFittingFormalHausdorff
import DeJongAlterations.Algebra.NodeGeometricCompletionDifferentialTransport

/-! # The actual gradient differential on the SAME original completed algebra

All original coefficient and completion maps are retained. Actual ideal powers
and native Leibniz give continuity internally; no differential-model certificate.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeFittingRelativeGradient

open NodeFittingFormalDerivation NodeFittingCompletedCoefficients
  NodeFittingCompletedEtaleCoefficients NodeFittingRelativeTransport
  NodeGeometricCompletionCoherentDifferentials
  NodeGeometricCompletionHausdorffDifferentials

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000

universe u
variable (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]
  [IsLocalRing A] [IsLocalRing R] [IsLocalHom (algebraMap A R)]

local notation "Â" => AdicCompletion (maximalIdeal A) A
local notation "C" => AdicCompletion (maximalIdeal R) R
local notation "P" => CompletedOmega A R (maximalIdeal R)

local instance : Algebra Â C := completedBaseAlgebra A R

variable (S : Type u) [CommRing S]
  [Algebra (AdicCompletion (maximalIdeal A) A) S]
  [Algebra S (AdicCompletion (maximalIdeal R) R)]
  [IsScalarTower (AdicCompletion (maximalIdeal A) A) S
    (AdicCompletion (maximalIdeal R) R)]

local instance : Algebra A S := originalCoefficientAlgebra A S

variable (F : Series S)
  (e : AdicCompletion (maximalIdeal R) R ≃ₐ[S] Hypersurface F)

/-- The literal actual gradient module records the SAME original completed normal form. -/
def TransportedGradient (_ : C ≃ₐ[S] Hypersurface F) := GradientModule F

instance : AddCommGroup (TransportedGradient R S F e) :=
  inferInstanceAs (AddCommGroup (GradientModule F))
instance : Module (Hypersurface F) (TransportedGradient R S F e) :=
  inferInstanceAs (Module (Hypersurface F) (GradientModule F))
instance : Module S (TransportedGradient R S F e) :=
  inferInstanceAs (Module S (GradientModule F))
instance : Module C (TransportedGradient R S F e) := Module.compHom _ e.toRingHom
instance : Module R (TransportedGradient R S F e) :=
  Module.compHom _ (e.toRingHom.comp (algebraMap R C))
instance : Module A (TransportedGradient R S F e) :=
  Module.compHom _ (e.toRingHom.comp (algebraMap A C))

instance transportedGradient_originalCompletedTower :
    IsScalarTower R C (TransportedGradient R S F e) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

instance transportedGradient_baseCompletedTower :
    IsScalarTower A C (TransportedGradient R S F e) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

instance transportedGradient_baseOriginalTower :
    IsScalarTower A R (TransportedGradient R S F e) := by
  apply IsScalarTower.of_algebraMap_smul
  intro a ω
  change e (algebraMap R C (algebraMap A R a)) • (ω : GradientModule F) =
    e (algebraMap A C a) • (ω : GradientModule F)
  rw [← IsScalarTower.algebraMap_apply A R C]

instance transportedGradient_modelCoefficientTower :
    IsScalarTower S (Hypersurface F) (TransportedGradient R S F e) :=
  inferInstanceAs (IsScalarTower S (Hypersurface F) (GradientModule F))

instance transportedGradient_coefficientCompletedTower :
    IsScalarTower S C (TransportedGradient R S F e) := by
  apply IsScalarTower.of_algebraMap_smul
  intro s ω
  change e (algebraMap S C s) • (ω : GradientModule F) = s • (ω : GradientModule F)
  rw [e.commutes, algebraMap_smul (Hypersurface F)]

local instance : RingHomInvPair e.toRingHom e.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv e.toRingEquiv
local instance : RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.of_ringEquiv e.symm.toRingEquiv

/-- The actual identity retains precisely the SAME e-semilinear original action. -/
def modelSemilinearEquiv :
    TransportedGradient R S F e ≃ₛₗ[e.toRingHom] GradientModule F where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Native finite presentation comes from the internally proved literal gradient presentation. -/
theorem transportedGradient_finitePresentation :
    Module.FinitePresentation C (TransportedGradient R S F e) :=
  NodeFittingModule.finitePresentation_semilinear e.symm.toRingEquiv
    (modelSemilinearEquiv R S F e).symm

/-- The ENTIRE original coefficient triangle through the SAME actual formal model. -/
theorem model_original_coefficient (a : A) :
    e (algebraMap A C a) = algebraMap S (Hypersurface F) (algebraMap A S a) := by
  have h := originalCoefficient_triangle A R S a
  rw [← IsScalarTower.algebraMap_apply A R C] at h
  rw [← h, e.commutes]

/-- Pull back the SAME literal formal differential along the SAME actual normal form. -/
def modelPullbackDerivation : Derivation S C (TransportedGradient R S F e) where
  toFun c := formalDerivation F (e c)
  map_add' c d := by
    change formalDerivation F (e (c + d)) = _
    rw [map_add, map_add]
  map_smul' s c := by
    change formalDerivation F (e (s • c)) = s • formalDerivation F (e c)
    have he : e (s • c) = s • e c := e.toLinearMap.map_smul s c
    rw [he, Derivation.map_smul]
  map_one_eq_zero' := by
    change formalDerivation F (e 1) = 0
    rw [map_one, Derivation.map_one_eq_zero]
  leibniz' c d := by
    change formalDerivation F (e (c * d)) =
      e c • formalDerivation F (e d) + e d • formalDerivation F (e c)
    rw [map_mul, Derivation.leibniz]

/-- Original coefficient linearity is proved from the WHOLE actual coefficient triangle. -/
@[simps! apply]
def pulledDerivation : Derivation A C (TransportedGradient R S F e) :=
  overBase (modelPullbackDerivation R S F e) (fun a => by
    change formalDerivation F (e (algebraMap A C a)) = 0
    rw [model_original_coefficient]
    exact formalDerivation_coefficient F _)

variable [IsNoetherianRing R]

/-- The actual finite target is Hausdorff for the ORIGINAL native maximal-ideal action. -/
theorem transportedGradient_isHausdorff :
    IsHausdorff (maximalIdeal R) (TransportedGradient R S F e) := by
  let := transportedGradient_finitePresentation R S F e
  have h : IsHausdorff (maximalIdeal C) (TransportedGradient R S F e) := inferInstance
  rw [AdicCompletion.maximalIdeal_eq_map] at h
  exact (IsHausdorff.map_algebraMap_iff (I := maximalIdeal R)
    (M := TransportedGradient R S F e) (S := C)).mp h

/-- Native Leibniz and the WHOLE actual ideal image prove the original continuity estimate internally. -/
theorem pulledDerivation_continuous :
    IsAdicallyContinuous (maximalIdeal R) (pulledDerivation A R S F e) := by
  intro n
  refine ⟨n + 1, fun c hc => ?_⟩
  have hmem := NodeGeometricCompletionDerivation.differential_mem_pow_smul
    (maximalIdeal C) (pulledDerivation A R S F e) n
    ((NodeGeometricCompletionDifferentialTransport.coordinate_zero_iff R (n + 1) c).mp hc)
  have hpow : (maximalIdeal R ^ n • ⊤ : Submodule R (TransportedGradient R S F e)) =
      (maximalIdeal C ^ n • ⊤ : Submodule C (TransportedGradient R S F e)).restrictScalars R := by
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
    exact (Submodule.restrictScalars_map_smul_eq (maximalIdeal R ^ n)
      (⊤ : Submodule C (TransportedGradient R S F e))).symm
  rw [hpow]
  exact hmem

variable [Algebra.EssFiniteType A R]

/-- The ORIGINAL completed coherent differential maps natively to the actual transported gradient module. -/
def originalToGradient : P →ₗ[C] TransportedGradient R S F e :=
  universalLift A R (TransportedGradient R S F e) (maximalIdeal R)
    (pulledDerivation A R S F e)

/-- The ENTIRE original completed differential triangle holds for the SAME actual e. -/
theorem originalToGradient_comp :
    (originalToGradient A R S F e).compDer (completedUniversalDerivation A R (maximalIdeal R)) =
      pulledDerivation A R S F e := by
  let := transportedGradient_isHausdorff R S F e
  exact universalLift_comp A R (TransportedGradient R S F e) (maximalIdeal R)
    (pulledDerivation A R S F e) (pulledDerivation_continuous A R S F e)

/-- EVERY original native differential retains its actual SAME-model value. -/
theorem originalToGradient_original (r : R) :
    originalToGradient A R S F e
      (AdicCompletion.of (maximalIdeal R) (KaehlerDifferential A R)
        (KaehlerDifferential.D A R r)) =
      formalDerivation F (e (algebraMap R C r)) :=
  universalLift_original A R (TransportedGradient R S F e) (maximalIdeal R)
    (pulledDerivation A R S F e) r

end DeJongAlterations.Algebra.NodeFittingRelativeGradient
