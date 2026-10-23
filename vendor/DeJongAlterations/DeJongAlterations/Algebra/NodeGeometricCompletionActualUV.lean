import DeJongAlterations.Algebra.NodeGeometricCompletionLocalUV

/-! From an ACTUAL coefficient-compatible uv model of the completed ORIGINAL local
field-algebra to the completed ORIGINAL coherent differential module. This is a field-fibre
producer; it is not a relative total-space normal-form hypothesis or residue-separability proof. -/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeGeometricCompletionActualUV

open NodeGeometricCompletionCoherentDifferentials NodeGeometricCompletionDifferentialTransport
  NodeGeometricCompletionFormalUV NodeGeometricCompletionLocalUV

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (K R : Type u) [Field K] [CommRing R] [Algebra K R]
  [IsNoetherianRing R] [IsLocalRing R] [Algebra.EssFiniteType K R]
  (e : LocalCompletion R ≃ₐ[K] FormalUV K)

/-- The internally constructed actual LOCAL-model completion equivalence, from the SAME original e. -/
def actualLocalModelEquiv : LocalCompletion R ≃ₐ[K] LocalUVCompletion K :=
  e.trans (localCompletionFieldEquiv K).symm

/-- The actual original coherent differential comparison map into B²/B(v,u). -/
def actualGradientMap : LocalOmega K R →ₛₗ[e.toRingHom] DifferentialModule K where
  toFun ω := localOmegaGradientEquiv K
    (differentialFun K R (LocalUV K) (actualLocalModelEquiv K R e) ω)
  map_add' ω η := by rw [differentialFun_add, map_add]
  map_smul' a ω := by
    rw [differentialFun_smul, localOmegaGradientEquiv_smul]
    change (localCompletionFieldEquiv K)
      ((localCompletionFieldEquiv K).symm (e a)) • _ = e a • _
    rw [AlgEquiv.apply_symm_apply]

local instance : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e.toRingEquiv
local instance : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm.toRingEquiv

/-- An ACTUAL uv completion model determines the ORIGINAL coherent differential completion
as the literal finite continuous-differential cokernel, without residue-separability assumptions. -/
def actualGradientEquiv : LocalOmega K R ≃ₛₗ[e.toRingHom] DifferentialModule K :=
  LinearEquiv.ofBijective (actualGradientMap K R e)
    ((localOmegaGradientEquiv K).bijective.comp
      (differentialEquiv K R (LocalUV K) (actualLocalModelEquiv K R e)).bijective)

/-- The comparison preserves the ENTIRE actual completed universal derivation through the
actual canonical local polynomial model, not merely its residue or its two generators. -/
theorem actualGradientEquiv_derivation (a : LocalCompletion R) :
    actualGradientEquiv K R e (completedUniversalDerivation K R (maximalIdeal R) a) =
      localOmegaGradientEquiv K (completedUniversalDerivation K (LocalUV K) (maximalIdeal (LocalUV K))
        ((localCompletionFieldEquiv K).symm (e a))) := by
  change localOmegaGradientEquiv K
    (differentialFun K R (LocalUV K) (actualLocalModelEquiv K R e)
      (completedUniversalDerivation K R (maximalIdeal R) a)) = _
  rw [differentialFun_derivation]
  rfl

/-- The actual original preimages of the literal formal coordinates retain BOTH differential classes. -/
theorem actualGradientEquiv_coordinate (i : Fin 2) :
    actualGradientEquiv K R e
      (completedUniversalDerivation K R (maximalIdeal R) (e.symm (coordinate K i))) =
      Submodule.Quotient.mk (Pi.single i 1) := by
  rw [actualGradientEquiv_derivation, AlgEquiv.apply_symm_apply]
  have hc : (localCompletionFieldEquiv K).symm (coordinate K i) =
      algebraMap (LocalUV K) (LocalUVCompletion K)
        (algebraMap (NodeGeometricCompletionFormalUV.PolynomialUV K) (LocalUV K)
          (Ideal.Quotient.mk (NodeFittingGeneral.polynomialIdeal (uvPolynomial K)) (MvPolynomial.X i))) := by
    apply (localCompletionFieldEquiv K).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (localCompletionEquiv_coordinate K i).symm
  rw [hc, completedUniversalDerivation_original, localOmegaGradientEquiv_coordinate]

/-- The ENTIRE actual completed scalar action is retained through the ORIGINAL e. -/
theorem actualGradientEquiv_smul (a : LocalCompletion R) (ω : LocalOmega K R) :
    actualGradientEquiv K R e (a • ω) = e a • actualGradientEquiv K R e ω :=
  (actualGradientEquiv K R e).map_smulₛₗ a ω

end DeJongAlterations.Algebra.NodeGeometricCompletionActualUV
