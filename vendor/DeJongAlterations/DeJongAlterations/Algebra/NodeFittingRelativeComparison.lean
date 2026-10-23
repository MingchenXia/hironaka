import DeJongAlterations.Algebra.NodeFittingRelativeGradient

/-! # The SAME original completed coherent differential and actual formal gradient

Both universal maps are constructed from their actual derivations. Two genuine
native linear round trips prove the inverse identities; no comparison certificate.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeFittingRelativeComparison

open NodeFittingFormalDerivation NodeFittingCompletedEtaleCoefficients
  NodeFittingRelativeTransport NodeFittingFormalHausdorff
  NodeGeometricCompletionCoherentDifferentials

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000

universe u
variable (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]
  [IsLocalRing A] [IsLocalRing R] [IsLocalHom (algebraMap A R)]
  [IsNoetherianRing R] [Algebra.EssFiniteType A R]

local notation "Â" => AdicCompletion (maximalIdeal A) A
local notation "C" => AdicCompletion (maximalIdeal R) R
local notation "P" => CompletedOmega A R (maximalIdeal R)

local instance : Algebra Â C := completedBaseAlgebra A R

variable (S : Type u) [CommRing S] [IsLocalRing S]
  [Algebra (AdicCompletion (maximalIdeal A) A) S]
  [Algebra S (AdicCompletion (maximalIdeal R) R)]
  [IsScalarTower (AdicCompletion (maximalIdeal A) A) S
    (AdicCompletion (maximalIdeal R) R)]
  [Algebra.FormallyUnramified (AdicCompletion (maximalIdeal A) A) S]
  (F : Series S) (e : AdicCompletion (maximalIdeal R) R ≃ₐ[S] Hypersurface F)

local instance : RingHomInvPair e.toRingHom e.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv e.toRingEquiv
local instance : RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.of_ringEquiv e.symm.toRingEquiv

/-- The actual original finite differential target, not a supplied gradient presentation. -/
def gradientToOriginal : GradientModule F →ₗ[Hypersurface F] TransportedOriginal A R S F e := by
  letI := model_isLocalRing R S F e
  letI := model_isNoetherianRing R S F e
  letI := transportedOriginal_finitePresentation A R S F e
  exact finiteUniversalLift F (transportedDerivation A R S F e)

/-- Full native factorization through the SAME actual inverse normal form. -/
theorem gradientToOriginal_comp :
    (gradientToOriginal A R S F e).compDer (formalDerivation F) =
      transportedDerivation A R S F e := by
  let := model_isLocalRing R S F e
  let := model_isNoetherianRing R S F e
  let := transportedOriginal_finitePresentation A R S F e
  exact finiteUniversalLift_comp F (transportedDerivation A R S F e)

/-- BOTH literal coordinate classes map to the actual original completed differential. -/
theorem gradientToOriginal_coordinate (i : Fin 2) :
    gradientToOriginal A R S F e (coordinateClass F i) =
      completedUniversalDerivation A R (maximalIdeal R)
        (e.symm (quotientMap F (MvPowerSeries.X i))) := by
  have h := DFunLike.congr_fun (gradientToOriginal_comp A R S F e)
    (quotientMap F (MvPowerSeries.X i))
  change gradientToOriginal A R S F e
    (formalDerivation F (quotientMap F (MvPowerSeries.X i))) = _ at h
  rw [formalDerivation_coordinate] at h
  exact h

/-- The first round trip is natively linear for the SAME original completed-ring action. -/
def originalRoundTrip : P →ₗ[C] P where
  toFun ω := gradientToOriginal A R S F e
    (NodeFittingRelativeGradient.originalToGradient A R S F e ω)
  map_add' ω η := by
    rw [map_add, map_add]
  map_smul' c ω := by
    rw [(NodeFittingRelativeGradient.originalToGradient A R S F e).map_smul]
    change gradientToOriginal A R S F e
      (e c • (NodeFittingRelativeGradient.originalToGradient A R S F e ω : GradientModule F)) = _
    rw [(gradientToOriginal A R S F e).map_smul]
    exact ((nativeSemilinearEquiv A R S F e).map_smulₛₗ c
      (gradientToOriginal A R S F e
        (NodeFittingRelativeGradient.originalToGradient A R S F e ω))).symm

/-- The native original completed universal property proves the ENTIRE first inverse identity. -/
theorem originalRoundTrip_eq_id : originalRoundTrip A R S F e = LinearMap.id := by
  apply NodeGeometricCompletionHausdorffDifferentials.universalLift_unique A R P (maximalIdeal R)
  apply DFunLike.ext
  intro c
  change gradientToOriginal A R S F e
    (NodeFittingRelativeGradient.originalToGradient A R S F e
      (completedUniversalDerivation A R (maximalIdeal R) c)) =
        completedUniversalDerivation A R (maximalIdeal R) c
  have hL := DFunLike.congr_fun
    (NodeFittingRelativeGradient.originalToGradient_comp A R S F e) c
  change NodeFittingRelativeGradient.originalToGradient A R S F e
    (completedUniversalDerivation A R (maximalIdeal R) c) = formalDerivation F (e c) at hL
  rw [hL]
  have hG := DFunLike.congr_fun (gradientToOriginal_comp A R S F e) (e c)
  change gradientToOriginal A R S F e (formalDerivation F (e c)) =
    completedUniversalDerivation A R (maximalIdeal R) (e.symm (e c)) at hG
  simpa only [e.symm_apply_apply] using hG

/-- The other round trip is natively linear over the SAME actual formal quotient. -/
def modelRoundTrip : GradientModule F →ₗ[Hypersurface F] GradientModule F where
  toFun η := NodeFittingRelativeGradient.originalToGradient A R S F e
    (gradientToOriginal A R S F e η)
  map_add' ω η := by
    rw [map_add, map_add]
  map_smul' b η := by
    rw [(gradientToOriginal A R S F e).map_smul]
    change NodeFittingRelativeGradient.originalToGradient A R S F e
      (e.symm b • (gradientToOriginal A R S F e η : P)) = _
    rw [(NodeFittingRelativeGradient.originalToGradient A R S F e).map_smul]
    have hs := (NodeFittingRelativeGradient.modelSemilinearEquiv R S F e).map_smulₛₗ
      (e.symm b) (NodeFittingRelativeGradient.originalToGradient A R S F e
        (gradientToOriginal A R S F e η))
    change _ = e (e.symm b) • _ at hs
    rw [e.apply_symm_apply] at hs
    exact hs

/-- The actual original coordinate generators prove the ENTIRE second inverse identity. -/
theorem modelRoundTrip_eq_id : modelRoundTrip A R S F e = LinearMap.id := by
  apply NodeFittingFormalUniversal.gradientLinearMap_ext F
  intro i
  change NodeFittingRelativeGradient.originalToGradient A R S F e
    (gradientToOriginal A R S F e (coordinateClass F i)) = coordinateClass F i
  rw [gradientToOriginal_coordinate]
  have h := DFunLike.congr_fun
    (NodeFittingRelativeGradient.originalToGradient_comp A R S F e)
    (e.symm (quotientMap F (MvPowerSeries.X i)))
  change NodeFittingRelativeGradient.originalToGradient A R S F e
    (completedUniversalDerivation A R (maximalIdeal R)
      (e.symm (quotientMap F (MvPowerSeries.X i)))) =
        formalDerivation F (e (e.symm (quotientMap F (MvPowerSeries.X i)))) at h
  simpa only [e.apply_symm_apply, formalDerivation_coordinate] using h

/-- Genuine SAME-e semilinear comparison, built from the two proved actual universal maps. -/
def completedGradientEquiv : P ≃ₛₗ[e.toRingHom] GradientModule F where
  toFun := NodeFittingRelativeGradient.originalToGradient A R S F e
  invFun := gradientToOriginal A R S F e
  left_inv ω := LinearMap.congr_fun (originalRoundTrip_eq_id A R S F e) ω
  right_inv η := LinearMap.congr_fun (modelRoundTrip_eq_id A R S F e) η
  map_add' ω η := (NodeFittingRelativeGradient.originalToGradient A R S F e).map_add ω η
  map_smul' c ω := (NodeFittingRelativeGradient.originalToGradient A R S F e).map_smul c ω

/-- EVERY actual completed differential follows the SAME original normal form. -/
theorem completedGradientEquiv_derivation (c : C) :
    completedGradientEquiv A R S F e (completedUniversalDerivation A R (maximalIdeal R) c) =
      formalDerivation F (e c) :=
  DFunLike.congr_fun (NodeFittingRelativeGradient.originalToGradient_comp A R S F e) c

/-- EVERY native original relative differential retains its SAME actual completed model value. -/
theorem completedGradientEquiv_original (r : R) :
    completedGradientEquiv A R S F e
      (AdicCompletion.of (maximalIdeal R) (KaehlerDifferential A R)
        (KaehlerDifferential.D A R r)) =
      formalDerivation F (e (algebraMap R C r)) :=
  NodeFittingRelativeGradient.originalToGradient_original A R S F e r

/-- BOTH literal coordinate classes retain the original completed differential of their SAME preimages. -/
theorem completedGradientEquiv_coordinate (i : Fin 2) :
    (completedGradientEquiv A R S F e).symm (coordinateClass F i) =
      completedUniversalDerivation A R (maximalIdeal R)
        (e.symm (quotientMap F (MvPowerSeries.X i))) :=
  gradientToOriginal_coordinate A R S F e i

/-- The ENTIRE actual completed scalar action follows precisely the SAME e. -/
theorem completedGradientEquiv_smul (c : C) (ω : P) :
    completedGradientEquiv A R S F e (c • ω) =
      e c • completedGradientEquiv A R S F e ω :=
  (completedGradientEquiv A R S F e).map_smulₛₗ c ω

end DeJongAlterations.Algebra.NodeFittingRelativeComparison
