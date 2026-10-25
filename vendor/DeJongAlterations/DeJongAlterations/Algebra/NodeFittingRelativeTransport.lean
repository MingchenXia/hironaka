import DeJongAlterations.Algebra.NodeFittingCompletedEtaleCoefficients
import DeJongAlterations.Algebra.NodeFittingFormalUniversal
import DeJongAlterations.Algebra.NodeFittingModuleSemilinear
import DeJongAlterations.Algebra.NodeGeometricCompletionContinuousDifferentials
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import DeJongAlterations.Algebra.NoetherianCompletion

/-! # The SAME original completed relative differential under its ACTUAL formal normal form

All original completed-ring and original coefficient actions remain native.
Only the NEW formal-model action is transported through the SAME actual normal
form. The module type records that exact isomorphism; no differential certificate.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeFittingRelativeTransport

open NodeFittingCompletedCoefficients NodeFittingCompletedEtaleCoefficients
  NodeGeometricCompletionCoherentDifferentials NodeFittingFormalDerivation

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

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
  [Algebra.FormallyUnramified (AdicCompletion (maximalIdeal A) A) S]

/-- The original coefficient action is the actual original-base completion followed by the actual S coefficient map. -/
@[instance_reducible]
def originalCoefficientAlgebra : Algebra A S :=
  ((algebraMap Â S).comp (algebraMap A Â)).toAlgebra

local instance : Algebra A S := originalCoefficientAlgebra A S

local instance : IsScalarTower A Â S := IsScalarTower.of_algebraMap_eq fun _ => rfl

omit [Algebra.FormallyUnramified (AdicCompletion (maximalIdeal A) A) S] in
/-- The ENTIRE original coefficient triangle retains every original coefficient. -/
theorem originalCoefficient_triangle (a : A) :
    algebraMap S C (algebraMap A S a) = algebraMap R C (algebraMap A R a) := by
  change algebraMap S C (algebraMap Â S (algebraMap A Â a)) = _
  rw [← IsScalarTower.algebraMap_apply Â S C]
  exact completedBase_original_coefficient A R a

omit [Algebra.FormallyUnramified (AdicCompletion (maximalIdeal A) A) S] in
/-- The SAME original native A action on the actual completion is retained. -/
theorem originalCoefficient_tower : IsScalarTower A S C :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [originalCoefficient_triangle A R S]
    exact IsScalarTower.algebraMap_apply A R C a

local instance : Module Â P := completedBaseModule A R
local instance : IsScalarTower Â C P := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
local instance : Module S P := Module.compHom P (algebraMap S C)
local instance : IsScalarTower S C P := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The original completed differential is genuinely S-linear for the SAME actual coefficient action. -/
@[simps! apply]
def coefficientDerivation : Derivation S C P :=
  overBase (completedBaseDerivation A R) (fun s =>
    completedUniversalDerivation_etale_coefficient A R S
      (IsScalarTower.toAlgHom Â S C) s)

/-- EVERY original relative differential retains its original native completion image. -/
theorem coefficientDerivation_original (r : R) :
    coefficientDerivation A R S (algebraMap R C r) =
      AdicCompletion.of (maximalIdeal R) (KaehlerDifferential A R)
        (KaehlerDifferential.D A R r) :=
  (coefficientDerivation_apply A R S _).trans
    (completedUniversalDerivation_original A R (maximalIdeal R) r)

variable (F : Series S)
  (e : AdicCompletion (maximalIdeal R) R ≃ₐ[S] Hypersurface F)

/-- The SAME native original differential module, recording the ACTUAL original formal model isomorphism. -/
def TransportedOriginal (_ : C ≃ₐ[S] Hypersurface F) := P

instance : AddCommGroup (TransportedOriginal A R S F e) := inferInstanceAs (AddCommGroup P)
instance : Module C (TransportedOriginal A R S F e) := inferInstanceAs (Module C P)
instance : Module S (TransportedOriginal A R S F e) := inferInstanceAs (Module S P)
instance : Module A (TransportedOriginal A R S F e) := inferInstanceAs (Module A P)
instance : Module R (TransportedOriginal A R S F e) := inferInstanceAs (Module R P)
instance : Module (Hypersurface F) (TransportedOriginal A R S F e) :=
  Module.compHom _ e.symm.toRingHom

instance transportedNative_coefficientTower :
    IsScalarTower S C (TransportedOriginal A R S F e) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

instance transportedModel_coefficientTower :
    IsScalarTower S (Hypersurface F) (TransportedOriginal A R S F e) where
  smul_assoc s b ω := by
    change e.symm (s • b) • (ω : P) = s • (e.symm b • (ω : P))
    have he : e.symm (s • b) = s • e.symm b := e.symm.toLinearMap.map_smul s b
    rw [he, smul_assoc]

local instance : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e.toRingEquiv
local instance : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm.toRingEquiv

/-- The actual identity on the SAME original module is semilinear for precisely the SAME e. -/
def nativeSemilinearEquiv : P ≃ₛₗ[e.toRingHom] TransportedOriginal A R S F e where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c ω := by
    change c • ω = e.symm (e c) • ω
    rw [e.symm_apply_apply]

/-- The actual transported native original completed relative derivation. -/
def transportedDerivation : Derivation S (Hypersurface F) (TransportedOriginal A R S F e) where
  toFun b := coefficientDerivation A R S (e.symm b)
  map_add' b d := by
    change coefficientDerivation A R S (e.symm (b + d)) = _
    rw [map_add, map_add]
  map_smul' s b := by
    change coefficientDerivation A R S (e.symm (s • b)) = s • coefficientDerivation A R S (e.symm b)
    have he : e.symm (s • b) = s • e.symm b := e.symm.toLinearMap.map_smul s b
    rw [he, Derivation.map_smul]
  map_one_eq_zero' := by
    change coefficientDerivation A R S (e.symm 1) = 0
    rw [map_one, Derivation.map_one_eq_zero]
  leibniz' b d := by
    change coefficientDerivation A R S (e.symm (b * d)) =
      e.symm b • coefficientDerivation A R S (e.symm d) +
      e.symm d • coefficientDerivation A R S (e.symm b)
    rw [map_mul, Derivation.leibniz]

/-- The ENTIRE actual completed original differential triangle is retained. -/
theorem transportedDerivation_completed (c : C) :
    transportedDerivation A R S F e (e c) = completedUniversalDerivation A R (maximalIdeal R) c := by
  change coefficientDerivation A R S (e.symm (e c)) = _
  rw [e.symm_apply_apply]
  exact coefficientDerivation_apply A R S c

/-- EVERY original relative differential retains its original native value under the SAME actual formal model. -/
theorem transportedDerivation_original (r : R) :
    transportedDerivation A R S F e (e (algebraMap R C r)) =
      AdicCompletion.of (maximalIdeal R) (KaehlerDifferential A R)
        (KaehlerDifferential.D A R r) := by
  rw [transportedDerivation_completed]
  exact completedUniversalDerivation_original A R (maximalIdeal R) r

/-- EVERY actual original S coefficient is killed by the actual transported S-linear differential. -/
theorem transportedDerivation_coefficient (s : S) :
    transportedDerivation A R S F e (algebraMap S (Hypersurface F) s) = 0 :=
  (transportedDerivation A R S F e).map_algebraMap s

variable [hR : IsNoetherianRing R]

include e in
/-- Locality is transported from the SAME original completed local ring, not supplied as a model certificate. -/
theorem model_isLocalRing : IsLocalRing (Hypersurface F) := e.toRingEquiv.isLocalRing

include e hR in
/-- Noetherianity is transported from the SAME original completed local ring. -/
theorem model_isNoetherianRing : IsNoetherianRing (Hypersurface F) :=
  isNoetherianRing_of_ringEquiv C e.toRingEquiv

variable [Algebra.EssFiniteType A R]

omit [IsLocalRing A] [IsLocalHom (algebraMap A R)]
  [Algebra (AdicCompletion (maximalIdeal A) A) S]
  [IsScalarTower (AdicCompletion (maximalIdeal A) A) S (AdicCompletion (maximalIdeal R) R)]
  [Algebra.FormallyUnramified (AdicCompletion (maximalIdeal A) A) S] in
/-- Native original coherent completion and the SAME semilinear identity internally give actual model-side finite presentation. -/
theorem transportedOriginal_finitePresentation :
    Module.FinitePresentation (Hypersurface F) (TransportedOriginal A R S F e) := by
  let := completedOmega_finitePresentation A R (maximalIdeal R)
  exact NodeFittingModule.finitePresentation_semilinear e.toRingEquiv (nativeSemilinearEquiv A R S F e)

end DeJongAlterations.Algebra.NodeFittingRelativeTransport
