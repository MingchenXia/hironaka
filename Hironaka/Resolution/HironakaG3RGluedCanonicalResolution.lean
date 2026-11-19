import Hironaka.Resolution.HironakaOriginalGlobalOffZero
import Hironaka.Resolution.HironakaOriginalTerminalProperProjection
import Hironaka.Resolution.HironakaOriginalTerminalLocalBiholomorphism

/-! # G3, target (A): the glued canonical resolution of a marked ideal on a noncompact manifold

Lane G3 (run 0080, round 2).  Blueprint: `hironaka-g3-r-glued-canonical-resolution.tex`.  Notes: `work/hironaka-resume-20261111/G3/G3-TARGET-A.md`.
Human decision (I-1339, option (A)): G3's global target is the glued terminal atlas -- a proper holomorphic map
`P : X' → X`, locally a finite canonical resolution, the pieces agreeing on overlaps -- instead of an ℕ-indexed schedule of
global blowups (which does not exist in general: `work/hironaka-resume-20261111/G3/G3-SCHEDULE-OBSTRUCTION.md`).

This module states target (A) for an arbitrary marked ideal of the domain of the canonical invariant on an arbitrary
(noncompact) complex manifold and proves it from the held glued terminal atlas
(`HironakaOriginalTerminalAtlas`, `HironakaOriginalTerminalManifold`, `HironakaOriginalTerminalProperProjection`,
`HironakaOriginalTerminalLocalBiholomorphism`, `HironakaOriginalGlobalOffZero`):

* **`exists_glued_canonical_resolution`**: a complex manifold `X'` and a holomorphic, proper, surjective `P : X' → X` such
  that every point of `X` has an open neighbourhood `U` and a canonical segment `T` of `M|_U` resolving it (empty final
  cosupport) whose last stage is biholomorphic to `P⁻¹U` over `U`.

The pieces agree on overlaps automatically: two local identifications are open embeddings into the SAME `X'` commuting
with `P`, so on an overlap they differ by a projection-preserving biholomorphism of the restricted final stages, which is
THE canonical comparison (projection-preserving biholomorphisms between terminal canonical towers are unique,
`HironakaOriginalTerminalProjectionUniqueness`).  This module adds no mathematics beyond packaging; it records the literal
endpoint of target (A).
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RGluedCanonicalResolution

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres
  HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold HironakaOriginalTerminalLocalBiholomorphism
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Target (A) of G3: the glued canonical resolution.**  For every marked ideal `M` of the domain of the canonical
invariant on a (not necessarily compact) complex manifold `X` there are a complex manifold `X'` and a holomorphic, proper,
surjective map `P : X' → X` which is locally a finite canonical resolution: every point of `X` has an open neighbourhood
`U` with a canonical segment `T` of `M|_U` with empty final cosupport, and an open `V = P⁻¹U` of `X'` with a biholomorphism
from the last stage of `T` onto `V` commuting with the projections. -/
theorem exists_glued_canonical_resolution (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    ∃ (X' : CMfd.{u} n) (P : X' → X),
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P ∧ IsProperMap P ∧ Surjective P ∧
      ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        IsCanonical (pullback (Subtype.val : U → X) M) ((canonicalInvariant n).inv (pullback (Subtype.val : U → X) M)) T ∧
        IsGeoResolution (pullback (Subtype.val : U → X) M) T ∧
        ∃ V : Opens X', (V : Set X') = P ⁻¹' (U : Set X) ∧
          ∃ φ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V,
            ∀ y : Y, P (φ y : X') = ((T.proj y : U) : X) := by
  let A := actualLocalTerminalAtlas M hM
  refine ⟨originalTerminalManifold M hM, originalTerminalGluedProjection M hM,
    originalTerminalGluedProjection_contMDiff M hM,
    HironakaOriginalTerminalProperProjection.originalTerminalGluedProjection_isProperMap M hM,
    HironakaOriginalGlobalOffZero.originalTerminalGluedProjection_surjective M hM, fun x => ?_⟩
  refine ⟨A.openSet x, A.point_mem x, A.finalSpace x, A.tower x, A.canonical x, A.terminal x,
    originalTerminalLocalRangeOpen M hM x, originalTerminalLocalInclusion_range M hM x,
    originalTerminalLocalBiholomorphism M hM x, fun y => ?_⟩
  change originalTerminalGluedProjection M hM (originalTerminalLocalInclusion M hM x y) = _
  rw [originalTerminalGluedProjection_local]
  rfl

end

end Hironaka.HironakaG3RGluedCanonicalResolution
