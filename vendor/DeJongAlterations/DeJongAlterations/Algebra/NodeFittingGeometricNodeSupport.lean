/-
The stalk/support argument adapts the minimal proved core of
EnvelopeProperty/deps/hironaka-ep33/Hironaka/Scheme/IdealSheaf/Order/Basic.lean,
SHA256 258578ca6cdbd16584153c003db2bd424a42be800a12dc825344add1e384bd94.
Copyright (c) 2026 Resolution; author Chris Elliott (Resolution).
Original Lean formalization by Claude Fable 5.1; Apache License 2.0.
Modified: actual whole native stalk ideals, no order theory or Hironaka imports.
License reproduced in Algebra/AdicCompletionTransport.lean.
-/
import DeJongAlterations.Algebra.NodeFittingGeometricUVStalk
import DeJongAlterations.Algebra.NodeFittingGeometricPullback

/-! # An ACTUAL ambient geometric node belongs to the ACTUAL original Sing -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing

namespace DeJongAlterations.Algebra.NodeFittingGeometricNodeSupport

open NodeFittingModule NodeFittingIdealSheaf NodeFittingOriginalGeometricStalk
  NodeGeometricCompletionCoherentDifferentials NodeGeometricCompletionFormalUV
  Geometry.NodeCompletedLocalGeometricChart Geometry.NodeCompletedLocalCoherentUV

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}}

/-- The native closed support detects the ENTIRE actual stalk ideal. -/
theorem mem_support_iff_stalkIdeal_le_maximalIdeal (I : X.IdealSheafData) (x : X) :
    x ∈ I.support ↔ stalkIdeal I x ≤ maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, Scheme.mem_zeroLocus_iff,
    stalkIdeal_eq_map_germ I U hxU, Ideal.map_le_iff_le_comap]
  constructor
  · intro h a ha
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => h a ha ((Scheme.mem_basicOpen X a x hxU).mpr hu)
  · intro h a ha hxa
    have hnon := h ha
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff] at hnon
    exact hnon ((Scheme.mem_basicOpen X a x hxU).mp hxa)

variable (f : X ⟶ S) [LocallyOfFinitePresentation f]
  (s : S) (K : Type u) [Field K] [Algebra (S.residueField s) K]

local notation "Y" => OriginalGeometricScheme f s K
local notation "π" => pullback.fst f (originalFieldMap s K)
local notation "q" => pullback.snd f (originalFieldMap s K)
local notation "J" => NodeFittingOmegaGluing.idealSheaf f 1
local notation "I" => (J).comap π

local instance targetFieldAlgebra (y : Y) : Algebra K ((Y).presheaf.stalk y) :=
  Scheme.stalkAlgebra q y
local instance targetCompletedFieldAlgebra (y : Y) : Algebra K ((Y).completedLocalRing y) :=
  Scheme.completedLocalRingAlgebra q y

/-- The ambient point's ENTIRE original singular quotient is K; no Sing point is supplied. -/
def ambientNodeQuotientEquiv (y : Y)
    (e : (Y).completedLocalRing y ≃ₐ[K] FormalUV K) :
    ((Y).presheaf.stalk y ⧸ stalkIdeal I y) ≃ₐ[K] K := by
  let R := (Y).presheaf.stalk y
  let H := (Y).completedLocalRing y
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
  exact eIdeal.trans (NodeFittingFormalUVDescent.originalQuotientEquiv e E)

/-- The WHOLE ambient original Fitting stalk ideal is proper, from the actual geometric model. -/
theorem ambientNode_stalkIdeal_ne_top (y : Y)
    (e : (Y).completedLocalRing y ≃ₐ[K] FormalUV K) : stalkIdeal I y ≠ ⊤ := by
  intro htop
  have hone : Ideal.Quotient.mk (stalkIdeal I y) (1 : (Y).presheaf.stalk y) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [htop]; trivial)
  have hbad := congrArg (ambientNodeQuotientEquiv f s K y e) hone
  exact one_ne_zero (by simpa only [map_one, map_zero] using hbad)

/-- The ACTUAL ambient node lies in the pulled ORIGINAL singular support. -/
theorem ambientNode_mem_support (y : Y)
    (e : (Y).completedLocalRing y ≃ₐ[K] FormalUV K) : y ∈ (I).support :=
  (mem_support_iff_stalkIdeal_le_maximalIdeal I y).mpr
    (le_maximalIdeal (ambientNode_stalkIdeal_ne_top f s K y e))

/-- An ACTUAL pulled original singular point exists over the supplied ambient node. -/
theorem exists_geometricSingPoint (y : Y)
    (e : (Y).completedLocalRing y ≃ₐ[K] FormalUV K) :
    ∃ z : (I).subscheme, (I).subschemeι z = y := by
  have h : y ∈ ((I).support : Set Y) := ambientNode_mem_support f s K y e
  rw [← (I).range_subschemeι] at h
  exact h

/-- The SAME original ambient point lifts to the native ORIGINAL singular scheme. -/
theorem exists_originalSingPoint (y : Y)
    (e : (Y).completedLocalRing y ≃ₐ[K] FormalUV K) :
    ∃ z : (J).subscheme, (J).subschemeι z = π y := by
  obtain ⟨w, hw⟩ := exists_geometricSingPoint f s K y e
  refine ⟨NodeFittingGeometricPullback.closedProjection J π w, ?_⟩
  have h := congrArg (fun a : (I).subscheme ⟶ X => a w)
    (NodeFittingGeometricPullback.closedProjection_inclusion J π)
  simpa only [Scheme.Hom.comp_apply, hw] using h

end DeJongAlterations.Algebra.NodeFittingGeometricNodeSupport
