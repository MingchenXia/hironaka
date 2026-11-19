import Hironaka.Resolution.HironakaG8DenseBoundaryEmbeddedResolution

/-! Compact original singular loci admit one finite boundary-relative embedded resolution. -/

set_option autoImplicit false

open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8CompactSingularEmbeddedResolution

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaAdmissibleSequence
  HironakaG8DenseBoundaryEmbeddedResolution

/-- With empty initial boundary, compactness of the original singular locus
suffices for a finite actual embedded resolution, with the two centre phases
and the exact exceptional preimage on the same ambient tower. -/
theorem exists_embedded_resolution_of_compact_singular_locus {m : ℕ} {X : CMfd.{0} (m + 1)}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := m + 1) W)
    (hK : IsCompact (singularSet (n := m + 1) W)) :
    ∃ (Z : CMfd.{0} (m + 1)) (U : BlowupTower X Z),
      let M : MarkedIdeal (m + 1) X := ⟨univ, [], vanishingIdeal (n := m + 1) W, 1⟩
      let WU := strictTransform (m + 1) U.proj W
      let EU := (geoTransformAlong M U).E
      IsAdmissibleBlowupSequence (m + 1) X [] (singularSet (n := m + 1) W) Z U.proj EU ∧
      StageCentres (fun P C =>
        (C ⊆ {x | x ∈ strictTransform (m + 1) P.proj W ∧
          ∀ k, ¬ RegularAtDim (n := m + 1) (strictTransform (m + 1) P.proj W) x k} ∨
        (IsClosedSubmanifold (m + 1) (strictTransform (m + 1) P.proj W) ∧
          C ⊆ strictTransform (m + 1) P.proj W ∩ ⋃ H ∈ (geoTransformAlong M P).E, H)) ∧
          HasNormalCrossings (m + 1) C (geoTransformAlong M P).E) U ∧
      IsClosedSubmanifold (m + 1) WU ∧ IsSNCDivisor (m + 1) EU ∧
      HasNormalCrossings (m + 1) WU EU ∧ IsTransverse (m + 1) WU EU ∧
      ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ U.proj ∧
      IsProperMap U.proj ∧ Surjective U.proj ∧ U.proj '' WU = W ∧
      IsIsomorphismOver (m + 1) U.proj (singularSet (n := m + 1) W)ᶜ ∧
      exceptionalLocus (m + 1) U.proj = U.proj ⁻¹' singularSet (n := m + 1) W := by
  have hEmpty : W ⊆ closure (W \ ⋃ H ∈ ([] : List (Set X)), H) := by
    simpa using (subset_closure : W ⊆ closure W)
  obtain ⟨Z, U, hAdm, hStages, hSmooth, hSNC, hNC, hTrans, _,
    hHolo, hProper, hSurj, hImage, hIso, hExc⟩ :=
    exists_embedded_resolution_of_dense_boundary_complement hW [] isSNCDivisor_nil hEmpty
      (by simpa using hK)
  exact ⟨Z, U, by simpa using hAdm, hStages, hSmooth, hSNC, hNC, hTrans,
    hHolo, hProper, hSurj, hImage, by simpa using hIso, hExc rfl⟩

end
end Hironaka.HironakaG8CompactSingularEmbeddedResolution
