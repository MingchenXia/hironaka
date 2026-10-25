import DeJongAlterations.Algebra.NodeFittingCompletedCoefficients

/-! # The original relative completed differential over the actual etale coefficient lift

All scalar actions are restrictions of the SAME native completed-ring action.
The base action is the actual completion of the ORIGINAL local algebra map.
No geometric or relative normal-form differential presentation is supplied.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeFittingCompletedEtaleCoefficients

open NodeFittingCompletedCoefficients NodeGeometricCompletionCoherentDifferentials

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]
  [IsLocalRing A] [IsLocalRing R] [IsLocalHom (algebraMap A R)]

local notation "Â" => AdicCompletion (maximalIdeal A) A
local notation "B" => AdicCompletion (maximalIdeal R) R
local notation "P" => CompletedOmega A R (maximalIdeal R)

/-- The actual completed original-base action; it is not induced through a model inverse. -/
@[instance_reducible]
def completedBaseAlgebra : Algebra Â B :=
  (CompletionLocalMap.completionMap (algebraMap A R)).toAlgebra

local instance : Algebra Â B := completedBaseAlgebra A R

/-- Restrict the SAME native completed original differential-module action. -/
@[instance_reducible]
def completedBaseModule : Module Â P :=
  Module.compHom P (algebraMap Â B)

local instance : Module Â P := completedBaseModule A R
local instance : IsScalarTower Â B P := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The ENTIRE original coefficient triangle retains the actual native local map. -/
theorem completedBase_original_coefficient (a : A) :
    algebraMap Â B (algebraMap A Â a) =
      algebraMap R B (algebraMap A R a) :=
  CompletionLocalMap.completionMap_algebraMap (algebraMap A R) a

/-- The SAME original completed universal differential is now linear over the ENTIRE actual completed base. -/
def completedBaseDerivation : Derivation Â B P :=
  overBase (completedUniversalDerivation A R (maximalIdeal R))
    (completedUniversalDerivation_completedBase A R)

/-- Scalar enlargement retains the ENTIRE original completed differential function. -/
@[simp]
theorem completedBaseDerivation_apply (b : B) :
    completedBaseDerivation A R b = completedUniversalDerivation A R (maximalIdeal R) b := rfl

/-- EVERY original relative differential retains its actual original completion image. -/
theorem completedBaseDerivation_original (r : R) :
    completedBaseDerivation A R (algebraMap R B r) =
      AdicCompletion.of (maximalIdeal R) (KaehlerDifferential A R)
        (KaehlerDifferential.D A R r) :=
  completedUniversalDerivation_original A R (maximalIdeal R) r

/-- The actual formally unramified coefficient lift is killed on EVERY coefficient, over the SAME original base. -/
theorem completedUniversalDerivation_etale_coefficient
    (S : Type u) [CommRing S] [Algebra Â S] [Algebra.FormallyUnramified Â S]
    (c : S →ₐ[Â] B) (s : S) :
    completedUniversalDerivation A R (maximalIdeal R) (c s) = 0 := by
  let : Algebra S B := c.toRingHom.toAlgebra
  let : Module S P := Module.compHom P c.toRingHom
  let : IsScalarTower Â S B := IsScalarTower.of_algHom c
  let : IsScalarTower S B P := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower Â S P := IsScalarTower.of_algebraMap_smul fun a p => by
    change c (algebraMap Â S a) • p = algebraMap Â B a • p
    rw [c.commutes]
  exact derivation_unramified_coefficient S (completedBaseDerivation A R) s

end DeJongAlterations.Algebra.NodeFittingCompletedEtaleCoefficients
