/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionGermIdealColon
set_option autoImplicit false
namespace Hironaka.HironakaSmoothSubmersionFiniteIdealIntersections
open Hironaka.HolomorphicIdealSheaves HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaSmoothSubmersionProjectionIdealColon HironakaSmoothSubmersionGermIdealColon
  HironakaSmoothSubmersionComposition
open scoped Topology Manifold ContDiff
universe u
noncomputable section

theorem projection_mem_extended_ideal_iff_all_coefficients (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) (g : HolGerm (ComplexModel (d+t))) :
    g ∈ Ideal.map (tangentPullback d t).toRingHom I ↔
      ∀ q α, projectionJetCoefficients d t q g α ∈ I := by
  constructor
  · intro hg q α
    exact projection_extended_ideal_coefficients d t q I hg α
  · intro hg
    apply (mem_iff_mem_all_normal_truncations d t _ g).mpr
    intro q
    exact (projection_extended_ideal_mod_normal_pow_iff d t q I g).mpr (hg q)

theorem projection_map_inf_eq (d t : ℕ)
    (I L : Ideal (HolGerm (ComplexModel d))) :
    Ideal.map (tangentPullback d t).toRingHom (I ⊓ L) =
      Ideal.map (tangentPullback d t).toRingHom I ⊓
        Ideal.map (tangentPullback d t).toRingHom L := by
  ext g
  simp only [projection_mem_extended_ideal_iff_all_coefficients,Submodule.mem_inf]
  constructor
  · intro h
    exact ⟨fun q α => (h q α).1,fun q α => (h q α).2⟩
  · intro h q α
    exact ⟨h.1 q α,h.2 q α⟩

theorem projection_map_iInf_eq (d t : ℕ) {ι : Type*}
    (I : ι → Ideal (HolGerm (ComplexModel d))) :
    Ideal.map (tangentPullback d t).toRingHom (⨅ i, I i) =
      ⨅ i, Ideal.map (tangentPullback d t).toRingHom (I i) := by
  ext g
  simp only [projection_mem_extended_ideal_iff_all_coefficients,Submodule.mem_iInf]
  constructor
  · intro h i q α
    exact h q α i
  · intro h q α i
    exact h i q α

theorem original_coherent_family_stalk_intersection
    {n t : ℕ} {X Y : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (n+t)) Y] [IsComplexManifold (n+t) Y]
    {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (r : ℕ) (I : Fin r → GermIdeal n X) (hI : ∀ i, (I i).IsCoherent) (y : Y) :
    (⨅ i, adaptedIdeal (GermIdeal.pullback (m := n+t) f (I i)) y
      (actualSourceCoordinates hf y) (actualSourceCoordinates_zero hf y)) =
    Ideal.map (tangentPullback n t).toRingHom
      (⨅ i, adaptedIdeal (I i) (f y) (centeredCoordinates (f y)) (centeredCoordinates_zero (f y))) := by
  rw [projection_map_iInf_eq]
  apply iInf_congr
  intro i
  exact adaptedIdeal_actual_pullback hf (I i) (hI i) y

end
end Hironaka.HironakaSmoothSubmersionFiniteIdealIntersections
