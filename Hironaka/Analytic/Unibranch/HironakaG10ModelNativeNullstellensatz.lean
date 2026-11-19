import Hironaka.Analytic.Unibranch.HironakaG10ManifoldNativeNullstellensatz
import Hironaka.Resolution.HironakaIntrinsicReducedCentreOpenPullback

/-! # Support containment gives native radical containment on an analytic model -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10ModelNativeNullstellensatz
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaActualAnalyticSubspace
  HironakaG10PNIdealFamily HironakaG10PNIdealNoetherModel
  HironakaIntrinsicReducedCentreIdealModel HironakaIntrinsicReducedCentreOpenPullback
  Hironaka.Analytic.Unibranch.HironakaG10ManifoldNativeNullstellensatz

noncomputable section

/-- On an actual embedded reduced analytic space, the intrinsic vanishing
  ideal of a set is contained in the radical of any locally generated ideal
  family whose support is locally contained in that set. -/
theorem intrinsicCentre_le_radical_of_support_subset {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {W : Set M} (hW : IsComplexAnalyticSubset (n := n) W)
    (J : ∀ x : actualSubspaceLocallyRingedSpace (n := n) W,
      Ideal ((actualSubspaceLocallyRingedSpace (n := n) W).presheaf.stalk x))
    (hJ : IsLocallyFinitelyGenerated (actualSubspaceLocallyRingedSpace (n := n) W) J)
    (C : Set W) (x : W) (hC : ∀ᶠ y in 𝓝 x, J y ≠ ⊤ → y ∈ C) :
    intrinsicCentreStalkRange (actualSubspaceLocallyRingedSpace (n := n) W) C x ≤
      (J x).radical := by
  let D : Set M := (Subtype.val : W → M) '' C
  have hDW : D ⊆ W := by rintro _ ⟨y,hy,rfl⟩; exact y.property
  have hCD : (Subtype.val : W → M) ⁻¹' D = C := Set.preimage_image_eq C Subtype.val_injective
  obtain ⟨S,hSC,hSopen,hxS⟩ := mem_nhds_iff.mp hC
  obtain ⟨T,hTopen,hTS⟩ := isOpen_induced_iff.mp hSopen
  have hxT : x.val ∈ T := by
    have : x ∈ (Subtype.val : W → M) ⁻¹' T := hTS ▸ hxS
    exact this
  have hpush : ∀ᶠ y in 𝓝 x.val, pushFamily W J y ≠ ⊤ → y ∈ D := by
    filter_upwards [hTopen.mem_nhds hxT] with y hyT hyJ
    by_cases hyW : y ∈ W
    · let y' : W := ⟨y,hyW⟩
      have hyS : y' ∈ S := by
        have : y' ∈ (Subtype.val : W → M) ⁻¹' T := hyT
        rwa [hTS] at this
      have hyJ' : J y' ≠ ⊤ := by
        intro htop
        apply hyJ
        rw [pushFamily_of_mem W J y', htop, Ideal.comap_top]
      exact ⟨y', hSC hyS hyJ', rfl⟩
    · exact (hyJ (pushFamily_of_not_mem W J y hyW)).elim
  have hambient := wholeVanishing_le_radical_of_support_subset (pushFamily W J)
    (pushFamily_isLocallyFinitelyGenerated hW J hJ) D x.val hpush
  rw [← hCD]
  change LinearMap.range (intrinsicReducedCentreStalkInclusion
    (actualSubspaceLocallyRingedSpace (n := n) W) ((Subtype.val : W → M) ⁻¹' D) x) ≤ _
  rw [intrinsicReducedCentreStalkInclusion_range_model hDW x]
  apply (Ideal.map_mono hambient).trans
  have h := Ideal.map_radical_le ((actualSubspaceInclusion (n := n) W).stalkMap x).hom
    (I := pushFamily W J x.val)
  change Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap x).hom
    (pushFamily W J x.val).radical ≤
      (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap x).hom
        (pushFamily W J x.val)).radical at h
  have heq : Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap x).hom
      (pushFamily W J x.val) = J x := (pull_pushFamily W J x).symm
  rw [heq] at h
  exact h

end
end Hironaka.Analytic.Unibranch.HironakaG10ModelNativeNullstellensatz
