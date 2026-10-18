/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.OriginalFixedFlatteningStalkDictionaryExact
import Hironaka.Support.GenuineAmbientJetAlgEquivExact

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff DirectSum
namespace Hironaka.HironakaSmoothCentreRealDomainActualAmbientHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicPointJets HironakaSmoothCentreRealDomainOriginalStalkFreeness
  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreNearbyIdeal HironakaHolomorphicJetRankLoci
  HironakaRelativeNormalDeformationInitialRelations
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- ANY fixed actual nonlinear flattening retains the SAME WHOLE original chart-stalk ambient HS at EVERY true target point. -/
theorem fixed_real_original_whole_stalk_ambient_hs_dictionary
    (A : GermIdeal n M) (hA : A.IsCoherent) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (a : ComplexModel n) (ha : a ∈ Φ.target) (ℓ : ℕ) :
    let y := actualFlatteningInverseMap x Φ a
    let hy := actualNearbyPoint_mem_chart_source x Φ hsrc a ha
    hilbertSamuelValue (wholeChartStalkIdeal A x y hy) ℓ =
      hilbertSamuelValue
        (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) a)) ℓ := by
  dsimp only
  have hmap := (whole_original_stalk_dictionary_at_actual_target A hA x Φ hsrc a ha).1
  rw [← hmap]
  exact actualAmbientHS_eq_of_genuineAlgEquiv (actualNearbyGermEquiv Φ a ha) _ ℓ

end
end Hironaka.HironakaSmoothCentreRealDomainActualAmbientHS
