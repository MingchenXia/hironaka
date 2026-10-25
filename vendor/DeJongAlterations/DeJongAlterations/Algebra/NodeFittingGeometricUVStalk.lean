import DeJongAlterations.Algebra.NodeFittingOriginalGeometricStalk
import DeJongAlterations.Algebra.NodeFittingFormalUVDescent

/-! # The ACTUAL pulled original singular stalk at an ACTUAL geometric uv node

Only the SAME completed GEOMETRIC fibre model is supplied. The original entire
Fitting ideal, native quotient, scalar maps and coherent differential comparison
are constructed internally, independently of original residue separability.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing

namespace DeJongAlterations.Algebra.NodeFittingGeometricUVStalk

open NodeFittingModule NodeFittingIdealSheaf NodeFittingExternalStalkQuotient
  NodeFittingOriginalGeometricStalk NodeGeometricCompletionCoherentDifferentials
  NodeGeometricCompletionFormalUV
  Geometry.NodeCompletedLocalGeometricChart Geometry.NodeCompletedLocalCoherentUV

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
  (s : S) (K : Type u) [Field K] [Algebra (S.residueField s) K]

local notation "Y" => OriginalGeometricScheme f s K
local notation "π" => pullback.fst f (originalFieldMap s K)
local notation "q" => pullback.snd f (originalFieldMap s K)
local notation "I" => (NodeFittingOmegaGluing.idealSheaf f 1).comap π

local instance targetFieldAlgebra (y : Y) : Algebra K ((Y).presheaf.stalk y) :=
  Scheme.stalkAlgebra q y
local instance targetCompletedFieldAlgebra (y : Y) : Algebra K ((Y).completedLocalRing y) :=
  Scheme.completedLocalRingAlgebra q y

/-- The ACTUAL native pulled original singular stalk is K over the SAME external K, from its actual GEOMETRIC model alone. -/
def geometricNodeStalkEquiv (z : (I).subscheme)
    (e : (Y).completedLocalRing ((I).subschemeι z) ≃ₐ[K] FormalUV K) :
    letI := Scheme.stalkAlgebra ((I).subschemeι ≫ q) z
    (I).subscheme.presheaf.stalk z ≃ₐ[K] K := by
  let y := (I).subschemeι z
  let R := (Y).presheaf.stalk y
  let H := (Y).completedLocalRing y
  letI := Scheme.stalkAlgebra ((I).subschemeι ≫ q) z
  letI : IsNoetherianRing R := stalk_isNoetherianRing q y
  letI : Algebra.EssFiniteType K R := stalkAlgebra_essFiniteType q y
  letI := geometricStalkOmega_finitePresentation f s K y
  letI : Module.FaithfullyFlat R H := CompletionRegularityBasics.faithfullyFlat R
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e.toRingEquiv
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm.toRingEquiv
  let E : H ⊗[R] KaehlerDifferential K R ≃ₛₗ[e.toRingEquiv.toRingHom] DifferentialModule K :=
    (completedOmegaTensorEquiv K R (maximalIdeal R)).trans (coherentUVEquiv q y e)
  let h := originalFittingStalkIdeal_eq_nativeOmega f s K y 1
  let eIdeal : (R ⧸ stalkIdeal I y) ≃ₐ[K]
      (R ⧸ fittingIdeal (R := R) (M := KaehlerDifferential K R) 1) :=
    { toRingEquiv := Ideal.quotEquivOfEq h, commutes' := fun _ => rfl }
  exact (externalStalkQuotientEquiv K q I z).symm.trans
    (eIdeal.trans (NodeFittingFormalUVDescent.originalQuotientEquiv e E))

/-- EVERY original ambient representative is evaluated by the SAME actual completion and geometric model. -/
theorem geometricNodeStalkEquiv_representative (z : (I).subscheme)
    (e : (Y).completedLocalRing ((I).subschemeι z) ≃ₐ[K] FormalUV K)
    (r : (Y).presheaf.stalk ((I).subschemeι z)) :
    geometricNodeStalkEquiv f s K z e ((I).subschemeι.stalkMap z r) =
      NodeFittingFormalUVQuotient.coefficientMap K
        (e ((Y).toCompletedLocalRing ((I).subschemeι z) r)) := by
  let y := (I).subschemeι z
  let R := (Y).presheaf.stalk y
  let H := (Y).completedLocalRing y
  let := Scheme.stalkAlgebra ((I).subschemeι ≫ q) z
  let : IsNoetherianRing R := stalk_isNoetherianRing q y
  let := geometricStalkOmega_finitePresentation f s K y
  let : Module.FaithfullyFlat R H := CompletionRegularityBasics.faithfullyFlat R
  rw [← externalStalkQuotientEquiv_mk K q I z r]
  dsimp only [geometricNodeStalkEquiv, AlgEquiv.trans_apply]
  rw [AlgEquiv.symm_apply_apply]
  change NodeFittingFormalUVDescent.originalQuotientEquiv
    (R := R) (N := KaehlerDifferential K R) e _ (Ideal.Quotient.mk _ r) = _
  exact NodeFittingFormalUVDescent.originalQuotientEquiv_mk e _ r

/-- The ENTIRE original native external-K coefficient map is preserved at the ACTUAL singular stalk. -/
@[simp]
theorem geometricNodeStalkEquiv_coefficient (z : (I).subscheme)
    (e : (Y).completedLocalRing ((I).subschemeι z) ≃ₐ[K] FormalUV K) (k : K) :
    letI := Scheme.stalkAlgebra ((I).subschemeι ≫ q) z
    geometricNodeStalkEquiv f s K z e
      (algebraMap K ((I).subscheme.presheaf.stalk z) k) = k := by
  let := Scheme.stalkAlgebra ((I).subschemeι ≫ q) z
  exact (geometricNodeStalkEquiv f s K z e).commutes k

end DeJongAlterations.Algebra.NodeFittingGeometricUVStalk
