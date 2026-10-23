import DeJongAlterations.Algebra.NodeGeometricCompletionHausdorffDifferentials
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.Algebra.Algebra.RestrictScalars

/-! Actual transported original completed coherent modules. The type synonym records the
actual completed algebra isomorphism, so all scalar actions are tied to that SAME map. -/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeGeometricCompletionDifferentialTransport

open NodeGeometricCompletionCoherentDifferentials NodeGeometricCompletionContinuousDifferentials
  NodeGeometricCompletionHausdorffDifferentials

universe u
variable (K R S : Type u) [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [IsLocalRing R] [IsLocalRing S]
  [IsNoetherianRing R] [IsNoetherianRing S]

abbrev LocalCompletion (A : Type u) [CommRing A] [IsLocalRing A] := AdicCompletion (maximalIdeal A) A
abbrev LocalOmega (A : Type u) [CommRing A] [Algebra K A] [IsLocalRing A] :=
  CompletedOmega K A (maximalIdeal A)

variable (e : LocalCompletion R ≃ₐ[K] LocalCompletion S)

/-- The literal native target module, with its SAME actual completed algebra isomorphism recorded. -/
def TransportedOmega (_ : LocalCompletion R ≃ₐ[K] LocalCompletion S) := LocalOmega K S

instance : AddCommGroup (TransportedOmega K R S e) := inferInstanceAs (AddCommGroup (LocalOmega K S))
instance : Module (LocalCompletion S) (TransportedOmega K R S e) :=
  inferInstanceAs (Module (LocalCompletion S) (LocalOmega K S))
instance : Module K (TransportedOmega K R S e) := inferInstanceAs (Module K (LocalOmega K S))
instance : Module R (TransportedOmega K R S e) :=
  Module.compHom _ (e.toRingHom.comp (algebraMap R (LocalCompletion R)))
instance : Module (LocalCompletion R) (TransportedOmega K R S e) := Module.compHom _ e.toRingHom

instance transportedNativeField_scalarTower :
    IsScalarTower K (LocalCompletion S) (TransportedOmega K R S e) :=
  inferInstanceAs (IsScalarTower K (LocalCompletion S) (LocalOmega K S))

instance transportedOriginalCompleted_scalarTower :
    IsScalarTower R (LocalCompletion R) (TransportedOmega K R S e) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

instance transportedFieldCompleted_scalarTower :
    IsScalarTower K (LocalCompletion R) (TransportedOmega K R S e) := by
  apply IsScalarTower.of_algebraMap_smul
  intro a ω
  change (e (algebraMap K (LocalCompletion R) a)) • (ω : LocalOmega K S) = a • (ω : LocalOmega K S)
  rw [e.commutes, algebraMap_smul (LocalCompletion S)]

instance transportedFieldOriginal_scalarTower : IsScalarTower K R (TransportedOmega K R S e) := by
  apply IsScalarTower.of_algebraMap_smul
  intro a ω
  change (e (algebraMap R (LocalCompletion R) (algebraMap K R a))) • (ω : LocalOmega K S) =
    a • (ω : LocalOmega K S)
  rw [← IsScalarTower.algebraMap_apply K R (LocalCompletion R), e.commutes,
    algebraMap_smul (LocalCompletion S)]

/-- The actual original R coefficient map into the target completion. -/
def originalToTarget : R →+* LocalCompletion S :=
  e.toRingHom.comp (algebraMap R (LocalCompletion R))

/-- The original maximal ideal maps to the ACTUAL target completed maximal ideal. -/
theorem originalToTarget_maximalIdeal :
    (maximalIdeal R).map (originalToTarget K R S e) = maximalIdeal (LocalCompletion S) := by
  rw [originalToTarget, ← Ideal.map_map, ← AdicCompletion.maximalIdeal_eq_map]
  exact IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv

/-- The literal native target differential completion remains Hausdorff for the actual
transported ORIGINAL source maximal-ideal action. -/
theorem transportedOmega_isHausdorff :
    IsHausdorff (maximalIdeal R) (TransportedOmega K R S e) := by
  let : Algebra R (LocalCompletion S) := (originalToTarget K R S e).toAlgebra
  let : IsScalarTower R (LocalCompletion S) (TransportedOmega K R S e) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hS : IsHausdorff (maximalIdeal (LocalCompletion S)) (LocalOmega K S) := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact (IsHausdorff.map_algebraMap_iff (I := maximalIdeal S)
      (M := LocalOmega K S) (S := LocalCompletion S)).mpr inferInstance
  apply (IsHausdorff.map_algebraMap_iff (I := maximalIdeal R)
    (M := TransportedOmega K R S e) (S := LocalCompletion S)).mp
  change IsHausdorff ((maximalIdeal R).map (originalToTarget K R S e)) (TransportedOmega K R S e)
  rw [originalToTarget_maximalIdeal]
  exact hS

/-- The actual native coordinate kernels are the powers of the ACTUAL completed maximal ideal. -/
theorem coordinate_zero_iff (n : ℕ) (a : LocalCompletion R) :
    a.val n = 0 ↔ a ∈ maximalIdeal (LocalCompletion R) ^ n := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow,
    ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian (maximalIdeal R))]
  rfl

/-- An actual local completed algebra isomorphism preserves EVERY actual coordinate kernel. -/
theorem equiv_coordinate_zero (n : ℕ) (a : LocalCompletion R) (ha : a.val n = 0) :
    (e a).val n = 0 := by
  rw [coordinate_zero_iff S]
  have he : (maximalIdeal (LocalCompletion R) ^ n).map e.toRingHom =
      maximalIdeal (LocalCompletion S) ^ n := by
    rw [Ideal.map_pow]
    exact congrArg (fun J => J ^ n) (IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv)
  rw [← he]
  exact Ideal.mem_map_of_mem _ ((coordinate_zero_iff R n a).mp ha)

/-- Actual target coordinate kernels give actual ORIGINAL source ideal powers under the
same transported scalar action. -/
theorem transportedCoordinate_mem (n : ℕ) (ω : TransportedOmega K R S e)
    (hω : (ω : LocalOmega K S).val n = 0) :
    ω ∈ (maximalIdeal R ^ n • ⊤ : Submodule R (TransportedOmega K R S e)) := by
  let : Algebra R (LocalCompletion S) := (originalToTarget K R S e).toAlgebra
  let : IsScalarTower R (LocalCompletion S) (TransportedOmega K R S e) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let η : LocalOmega K S := ω
  have hnative : η ∈
      (maximalIdeal S ^ n • ⊤ : Submodule S (LocalOmega K S)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian (maximalIdeal S))]
    exact hω
  have hcompleted : η ∈
      (maximalIdeal (LocalCompletion S) ^ n • ⊤ : Submodule (LocalCompletion S) (LocalOmega K S)) := by
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow,
      ← Submodule.restrictScalars_mem S, Submodule.restrictScalars_map_smul_eq]
    exact hnative
  have hpow : (maximalIdeal R ^ n • ⊤ : Submodule R (TransportedOmega K R S e)) =
      (maximalIdeal (LocalCompletion S) ^ n • ⊤ :
        Submodule (LocalCompletion S) (TransportedOmega K R S e)).restrictScalars R := by
    rw [← originalToTarget_maximalIdeal K R S e, ← Ideal.map_pow]
    exact (Submodule.restrictScalars_map_smul_eq (maximalIdeal R ^ n)
      (⊤ : Submodule (LocalCompletion S) (TransportedOmega K R S e))).symm
  rw [hpow]
  exact hcompleted

/-- Pull back the actual completed ORIGINAL target derivation through the SAME actual
coefficient-compatible completed-local algebra isomorphism. -/
def transportedDerivation : Derivation K (LocalCompletion R) (TransportedOmega K R S e) where
  toFun a := completedUniversalDerivation K S (maximalIdeal S) (e a)
  map_add' a b := by
    change completedUniversalDerivation K S (maximalIdeal S) (e (a + b)) = _
    rw [map_add, map_add]
    rfl
  map_smul' k a := by
    change completedUniversalDerivation K S (maximalIdeal S) (e (k • a)) = _
    have he : e (k • a) = k • e a := e.toLinearMap.map_smul k a
    rw [he, Derivation.map_smul]
    rfl
  map_one_eq_zero' := by
    change completedUniversalDerivation K S (maximalIdeal S) (e 1) = 0
    rw [map_one, Derivation.map_one_eq_zero]
  leibniz' a b := by
    change completedUniversalDerivation K S (maximalIdeal S) (e (a * b)) =
      e a • completedUniversalDerivation K S (maximalIdeal S) (e b) +
      e b • completedUniversalDerivation K S (maximalIdeal S) (e a)
    rw [map_mul, Derivation.leibniz]

/-- Continuity follows from local isomorphism and the explicit ORIGINAL differential estimate. -/
theorem transportedDerivation_continuous :
    IsAdicallyContinuous (maximalIdeal R) (transportedDerivation K R S e) := by
  intro n
  refine ⟨n + 1, fun a ha => ?_⟩
  exact transportedCoordinate_mem K R S e n _
    (completedUniversalDerivation_filtration K S (maximalIdeal S) n (e a)
      (equiv_coordinate_zero K R S e (n + 1) a ha))

variable [Algebra.EssFiniteType K R]

/-- The actual completed coherent differential map is constructed internally from universal
continuous derivations, even though the original algebras need not map to one another. -/
def differentialMap : LocalOmega K R →ₗ[LocalCompletion R] TransportedOmega K R S e :=
  universalLift K R (TransportedOmega K R S e) (maximalIdeal R) (transportedDerivation K R S e)

/-- The map preserves the entire actual completed universal derivation. -/
theorem differentialMap_derivation (a : LocalCompletion R) :
    differentialMap K R S e (completedUniversalDerivation K R (maximalIdeal R) a) =
      completedUniversalDerivation K S (maximalIdeal S) (e a) := by
  let := transportedOmega_isHausdorff K R S e
  exact DFunLike.congr_fun
    (universalLift_comp K R (TransportedOmega K R S e) (maximalIdeal R)
      (transportedDerivation K R S e) (transportedDerivation_continuous K R S e)) a

/-- The actual map, unwrapped into the literal ORIGINAL target module completion. -/
def differentialFun (ω : LocalOmega K R) : LocalOmega K S := differentialMap K R S e ω

omit [IsNoetherianRing S] in
theorem differentialFun_add (ω η : LocalOmega K R) :
    differentialFun K R S e (ω + η) = differentialFun K R S e ω + differentialFun K R S e η :=
  (differentialMap K R S e).map_add ω η

omit [IsNoetherianRing S] in
/-- Full actual completed-scalar equivariance, with the SAME original completed algebra map. -/
theorem differentialFun_smul (a : LocalCompletion R) (ω : LocalOmega K R) :
    differentialFun K R S e (a • ω) = e a • differentialFun K R S e ω :=
  (differentialMap K R S e).map_smul a ω

/-- The transported map preserves the ENTIRE actual completed universal derivation. -/
theorem differentialFun_derivation (a : LocalCompletion R) :
    differentialFun K R S e (completedUniversalDerivation K R (maximalIdeal R) a) =
      completedUniversalDerivation K S (maximalIdeal S) (e a) := differentialMap_derivation K R S e a

variable [Algebra.EssFiniteType K S]

local instance : RingHomInvPair e.toRingHom e.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv e.toRingEquiv

local instance : RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.of_ringEquiv e.symm.toRingEquiv

/-- Compose the internally constructed maps through the actual inverse algebra isomorphism. -/
def differentialComposite : LocalOmega K R →ₗ[LocalCompletion R] LocalOmega K R where
  toFun ω := differentialFun K S R e.symm (differentialFun K R S e ω)
  map_add' ω η := by rw [differentialFun_add, differentialFun_add]
  map_smul' a ω := by
    rw [differentialFun_smul, differentialFun_smul, AlgEquiv.symm_apply_apply]
    rfl

/-- Invertibility is a consequence of the ACTUAL original continuous universal property. -/
theorem differentialComposite_eq_id : differentialComposite K R S e = LinearMap.id := by
  apply universalLift_unique K R (LocalOmega K R) (maximalIdeal R)
  apply DFunLike.ext
  intro a
  change differentialFun K S R e.symm
    (differentialFun K R S e (completedUniversalDerivation K R (maximalIdeal R) a)) =
      completedUniversalDerivation K R (maximalIdeal R) a
  rw [differentialFun_derivation, differentialFun_derivation, AlgEquiv.symm_apply_apply]

theorem differentialFun_inverse (ω : LocalOmega K R) :
    differentialFun K S R e.symm (differentialFun K R S e ω) = ω :=
  LinearMap.congr_fun (differentialComposite_eq_id K R S e) ω

/-- Actual completed coherent differential transport, as an honest semilinear map. -/
def differentialSemilinearMap : LocalOmega K R →ₛₗ[e.toRingHom] LocalOmega K S where
  toFun := differentialFun K R S e
  map_add' := differentialFun_add K R S e
  map_smul' := differentialFun_smul K R S e

/-- Coefficient-compatible isomorphic ACTUAL completed local rings have isomorphic
completed ORIGINAL coherent differential modules, retaining the entire actual derivation. -/
def differentialEquiv : LocalOmega K R ≃ₛₗ[e.toRingHom] LocalOmega K S :=
  LinearEquiv.ofBijective (differentialSemilinearMap K R S e) ⟨by
    intro ω η h
    have hh := congrArg (differentialFun K S R e.symm) h
    change differentialFun K S R e.symm (differentialFun K R S e ω) =
      differentialFun K S R e.symm (differentialFun K R S e η) at hh
    simpa only [differentialFun_inverse] using hh, by
    intro η
    refine ⟨differentialFun K S R e.symm η, ?_⟩
    exact differentialFun_inverse K S R e.symm η⟩

/-- Full completed universal differential formula for the SAME actual semilinear equivalence. -/
theorem differentialEquiv_derivation (a : LocalCompletion R) :
    differentialEquiv K R S e (completedUniversalDerivation K R (maximalIdeal R) a) =
      completedUniversalDerivation K S (maximalIdeal S) (e a) := differentialFun_derivation K R S e a

end DeJongAlterations.Algebra.NodeGeometricCompletionDifferentialTransport
