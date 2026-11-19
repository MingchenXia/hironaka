import Hironaka.Resolution.HironakaG8DenseBoundaryRestart
import Hironaka.Resolution.HironakaG8CompactNativePhase
import Hironaka.Resolution.HironakaG8CompactLexInduction
import Hironaka.Resolution.HironakaG8CompactSharpFinish
import Hironaka.Resolution.HironakaG8DenseBoundaryReadback

/-! Finite embedded resolution on a compact singular and boundary footprint
for an initial SNC boundary with dense complement in the carrier. -/

set_option autoImplicit false

open Set Function
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8DenseBoundaryEmbeddedResolution

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaAdmissibleSequence
  HironakaG11InvBMClass HironakaG8LocalHistory CanonicalCentres
  HironakaG1OriginalInvariantClassFunctorial HironakaG8CompactNativePhase HironakaG8CompactLexInduction
  HironakaG8DenseBoundaryRestart HironakaG8CompactSharpFinish

/-- An arbitrary initial SNC boundary with dense complement in the carrier
and compact singular and boundary footprint gives a finite actual embedded
resolution. The actual full final boundary is retained at every position. -/
theorem exists_embedded_resolution_of_dense_boundary_complement {m : ℕ} {X : CMfd.{0} (m + 1)}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := m + 1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (m + 1) E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hK : IsCompact (singularSet (n := m + 1) W ∪ (W ∩ ⋃ H ∈ E, H))) :
    ∃ (Z : CMfd.{0} (m + 1)) (U : BlowupTower X Z),
      let M : MarkedIdeal (m + 1) X := ⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩
      let F := singularSet (n := m + 1) W ∪ (W ∩ ⋃ H ∈ E, H)
      let WU := strictTransform (m + 1) U.proj W
      let EU := (geoTransformAlong M U).E
      IsAdmissibleBlowupSequence (m + 1) X E F Z U.proj EU ∧
      StageCentres (fun P C =>
        (C ⊆ {x | x ∈ strictTransform (m + 1) P.proj W ∧
          ∀ k, ¬ RegularAtDim (n := m + 1) (strictTransform (m + 1) P.proj W) x k} ∨
        (IsClosedSubmanifold (m + 1) (strictTransform (m + 1) P.proj W) ∧
          C ⊆ strictTransform (m + 1) P.proj W ∩ ⋃ H ∈ (geoTransformAlong M P).E, H)) ∧
          HasNormalCrossings (m + 1) C (geoTransformAlong M P).E) U ∧
      IsClosedSubmanifold (m + 1) WU ∧ IsSNCDivisor (m + 1) EU ∧
      HasNormalCrossings (m + 1) WU EU ∧ IsTransverse (m + 1) WU EU ∧
      WU ⊆ closure (WU \ ⋃ H ∈ EU, H) ∧
      ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ U.proj ∧
      IsProperMap U.proj ∧ Surjective U.proj ∧ U.proj '' WU = W ∧
      IsIsomorphismOver (m + 1) U.proj Fᶜ ∧
      (E = [] → exceptionalLocus (m + 1) U.proj = U.proj ⁻¹' singularSet (n := m + 1) W) := by
  have hKsing := hK.of_isClosed_subset (isClosed_singularSet hW.isClosed) subset_union_left
  let R : BMInvariant.{0,0} (m + 1) (fun {A} P Q => LocWPEquiv (X := A) P Q) (m + 1) (ValTy (m + 1)) :=
    ⟨canonicalInvariant (m + 1), classFunctorialFor_canonicalInvariant (m + 1)⟩
  obtain ⟨Y, T, hTest, hStage, hSmooth⟩ :=
    exists_compact_singular_resolution_of_lex_phases_of_compact_singular hW hKsing E hE
      (fun V hV hVK hNonSmooth F hF hNot => by
        obtain ⟨a, ha, _, B, S, hTest, hStage, _, hDrop⟩ :=
          exists_finite_compact_native_phase_of_compact_singular (Nat.succ_pos m)
            R hV hVK hNonSmooth F hF hNot
        exact ⟨a, ha, B, S, hTest, hStage, hDrop⟩)
      (fun T hTest hStage => boundary_noncontainment_at_current_singular_of_dense_complement
        (Nat.succ_pos m) hW E hE hDense T hTest hStage)
  obtain ⟨Z, S, hAdm, hStages, hFinalSmooth, hSNC, hNC, hProper, hSurj, hIso, hExc⟩ :=
    exists_compact_singular_history_with_snc_finish hW E hE hK T hTest hStage hSmooth
  let U := T.append S
  obtain ⟨hDensity, hTransverse, hImage⟩ :=
    HironakaG8DenseBoundaryReadback.terminal_dense_transverse_image hW E hE hDense U hAdm hNC
  exact ⟨Z, U, hAdm, hStages, hFinalSmooth, hSNC, hNC, hTransverse, hDensity,
    U.contMDiff_proj, hProper, hSurj, hImage, hIso, hExc⟩

end Hironaka.HironakaG8DenseBoundaryEmbeddedResolution
