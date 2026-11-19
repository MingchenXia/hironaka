/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualTangentCutLayers
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualAmbientHS

/-!
# Ambient Hilbert--Samuel convolution at the selected original centre point

The actual finite free normal layers give the whole ambient weighted-jet
dimension formula. The geometric endpoint obtains those layers internally
from the original coherent ideal and constant intrinsic Hilbert--Samuel
function along a regular centre. One unchanged flattening and original
origin ideal work at all orders, including at the selected centre point.

This supplies no canonical reduced-vertex centre-power compatibility,
arbitrary blowup Bennett inequality or termination assertion.
Blueprint: `hironaka-actual-hs-constant-centre-ambient-convolution-extension.tex`.
-/

set_option autoImplicit false
open scoped BigOperators Topology Manifold ContDiff DirectSum
namespace Hironaka.HironakaActualHSConstantCentreAmbientConvolution
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalGradedAlgebra
  HironakaRelativeNormalIdeal HironakaRelativeNormalActualWeightedTruncations
  HironakaRelativeNormalActualHSConvolution HironakaHolomorphicPointJets
  HironakaActualTangentCutLayers HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations

variable (d t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t
local instance : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  IsScalarTower.of_algHom (tangentPullback d t)

/-- All actual finite free normal layers compute the unchanged ideal's ambient HS function. -/
theorem hilbertSamuelValue_eq_normal_layer_convolution
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hfinite : ∀ q : ℕ, Module.Finite (HolGerm (ComplexModel d))
      (originalNormalGradedPiece d t I q))
    (hfree : ∀ q : ℕ, Module.Free (HolGerm (ComplexModel d))
      (originalNormalGradedPiece d t I q)) (ℓ : ℕ) :
    hilbertSamuelValue I ℓ = ∑ q : Fin (ℓ+1),
      Module.finrank (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q.val) *
        (d+ℓ-q.val).choose d := by
  let : ∀ q, Module.Free (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) I (normalIdeal d t) q) := hfree
  let : ∀ q, Module.Finite (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) I (normalIdeal d t) q) := hfinite
  let : ∀ q : Fin (ℓ+1), Module.Finite ℂ
      (actualWeightedLayerQuotient (B := HolGerm (ComplexModel d)) I (normalIdeal d t)
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) (ℓ+1) q.val) :=
    fun q => actualOriginalWeightedLayerFinite d t I ℓ q.val (Nat.le_of_lt_succ q.isLt)
  let : ∀ q : Fin (ℓ+1), Module.Free ℂ
      (actualWeightedLayerQuotient (B := HolGerm (ComplexModel d)) I (normalIdeal d t)
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) (ℓ+1) q.val) :=
    fun _ => inferInstance
  let e := actualAmbientWeightedLayersEquiv (B := HolGerm (ComplexModel d))
    I (normalIdeal d t) (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) (ℓ+1)
  let em := Ideal.quotientEquivAlgOfEq ℂ
    (congrArg (fun J => I ⊔ J)
      (originalActualMixedPower_eq_maximalIdeal_power d t (ℓ+1)).symm)
  let E := em.toLinearEquiv.trans (e.restrictScalars ℂ)
  change Module.finrank ℂ (HolGerm (ComplexModel (d+t)) ⧸
    (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ (ℓ+1))) = _
  rw [E.finrank_eq,Module.finrank_directSum]
  apply Finset.sum_congr rfl
  intro q _
  exact actualOriginalWeightedLayerDimension d t I ℓ q.val (Nat.le_of_lt_succ q.isLt)

section OriginalCentre
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original coherent constant-HS centre geometry gives the ambient convolution at the selected point. -/
theorem exists_original_hs_constant_centre_ambient_convolution
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      (∀ q : ℕ,
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I0 q) ∧
        Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I0 q)) ∧
      ∀ ℓ : ℕ, hilbertSamuelAt A x ℓ = ∑ q : Fin (ℓ+1),
        Module.finrank (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I0 q.val) *
          (d+ℓ-q.val).choose d := by
  obtain ⟨Φ,hsrc,h0,hflat,hG⟩ :=
    exists_original_hs_constant_centre_normal_layers_finite_free d t C x hreg A hA hhs
  refine ⟨Φ,hsrc,h0,hflat,hG,?_⟩
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf A x Φ) 0)
  intro ℓ
  have h0T := actualFlattening_target_zero_mem x Φ h0
  have hwhole : hilbertSamuelAt A (actualFlatteningInverseMap x Φ 0) ℓ =
      hilbertSamuelValue I0 ℓ := by
    rw [hilbertSamuelAt_eq_fixedChart A x _
      (actualNearbyPoint_mem_chart_source x Φ hsrc 0 h0T) ℓ]
    exact fixed_real_original_whole_stalk_ambient_hs_dictionary A hA x Φ hsrc 0 h0T ℓ
  have hd : hilbertSamuelAt A x ℓ = hilbertSamuelValue I0 ℓ := by
    simpa only [actualFlatteningInverseMap_zero x Φ h0] using hwhole
  exact hd.trans (hilbertSamuelValue_eq_normal_layer_convolution d t I0
    (fun q => (hG q).1) (fun q => (hG q).2) ℓ)

end OriginalCentre
end
end Hironaka.HironakaActualHSConstantCentreAmbientConvolution
