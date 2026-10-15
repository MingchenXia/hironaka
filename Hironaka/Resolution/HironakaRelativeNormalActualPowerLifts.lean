/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalMixedTangentPowers

/-! Actual original normal graded layers lift linearly to their SAME whole
normal powers. Original coherence internally supplies all lifts on one
genuine nearby open, with the original uniform ranks retained. -/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaRelativeNormalActualPowerLifts
noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalGradedAlgebra HironakaRelativeNormalNearbyUniformRanks
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalCoherentTranslatedJets

section ActualLayer
variable {B R : Type*} [CommRing B] [CommRing R] [Algebra B R]

/-- An internally chosen basis of the actual free layer lifts through the genuine whole power map. -/
def actualFreeLayerPowerLift (I J : Ideal R) (q : ℕ)
    [Module.Free B (idealPowerLayer B I J q)] :
    idealPowerLayer B I J q →ₗ[B] powerModule B J q :=
  (Module.Free.chooseBasis B (idealPowerLayer B I J q)).constr B
    (fun i => Classical.choose
      (idealPowerLayerMap_surjective B I J q
        (Module.Free.chooseBasis B (idealPowerLayer B I J q) i)))

/-- The genuine original power-layer map of the true linear lift is the WHOLE identity. -/
theorem actualFreeLayerPowerLift_rightInverse (I J : Ideal R) (q : ℕ)
    [Module.Free B (idealPowerLayer B I J q)] :
    (idealPowerLayerMap B I J q).comp (actualFreeLayerPowerLift (B := B) I J q) =
      LinearMap.id := by
  apply (Module.Free.chooseBasis B (idealPowerLayer B I J q)).ext
  intro i
  change idealPowerLayerMap B I J q
      (actualFreeLayerPowerLift (B := B) I J q
        (Module.Free.chooseBasis B (idealPowerLayer B I J q) i)) = _
  unfold actualFreeLayerPowerLift
  rw [Module.Basis.constr_basis]
  exact Classical.choose_spec (idealPowerLayerMap_surjective B I J q
    (Module.Free.chooseBasis B (idealPowerLayer B I J q) i))

/-- Every true whole normal numerator retains the SAME original quotient class. -/
theorem actualFreeLayerPowerLift_class (I J : Ideal R) (q : ℕ)
    [Module.Free B (idealPowerLayer B I J q)] (x : idealPowerLayer B I J q) :
    Ideal.Quotient.mk (I ⊔ J ^ (q+1))
      (actualFreeLayerPowerLift (B := B) I J q x).val = x.val := by
  exact congrArg Subtype.val (LinearMap.congr_fun
    (actualFreeLayerPowerLift_rightInverse (B := B) I J q) x)

end ActualLayer

/-- ONLY the original coherent ideal supplies every whole power lift on ONE true open, retaining all ranks. -/
theorem exists_original_nearby_all_normal_layer_power_lifts (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ U : Set (ComplexModel d), ∃ r : ℕ → ℕ, IsOpen U ∧
      (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
      ∀ a ∈ U, ∀ q : ℕ,
        let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))
        Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t Ia q) ∧
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t Ia q) ∧
        Module.finrank (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t Ia q) = r q ∧
        ∃ lift : originalNormalGradedPiece d t Ia q →ₗ[HolGerm (ComplexModel d)]
          powerModule (HolGerm (ComplexModel d)) (normalIdeal d t) q,
          (idealPowerLayerMap (HolGerm (ComplexModel d)) Ia (normalIdeal d t) q).comp lift =
            LinearMap.id := by
  let := tangentAlgebra d t
  obtain ⟨U,r,hU,hmeet,hdegree⟩ := exists_original_nearby_all_degree_uniform_rank_open d t I hI
  refine ⟨U,r,hU,hmeet,?_⟩
  intro a ha q
  obtain ⟨hfree,hfinite,hrank⟩ := hdegree a ha q
  let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))
  let : Module.Free (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) Ia (normalIdeal d t) q) := hfree
  refine ⟨hfree,hfinite,hrank,
    actualFreeLayerPowerLift (B := HolGerm (ComplexModel d)) Ia (normalIdeal d t) q,?_⟩
  exact actualFreeLayerPowerLift_rightInverse Ia (normalIdeal d t) q

end
end Hironaka.HironakaRelativeNormalActualPowerLifts
