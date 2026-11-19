import Hironaka.Resolution.HironakaG11ContainingGermAbstractBlowup

import Hironaka.Resolution.HironakaG11TraceGermTransport
import Hironaka.Resolution.HironakaG8TraceLocalSection
set_option autoImplicit false

/-! A locally contained birth trace forces uniform tangent containment on
nearby centre points once the actual trace projection is locally open. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11TraceUniformTangency
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupSpaceTangent BlowupStrictSubmanifold
  HironakaG11ContainingGermAbstractBlowup

/-- An open-projecting strict exceptional trace that lies locally in the old
strict member forces tangent containment at all nearby centre points. -/
theorem uniform_tangent_of_trace_containment
    {n : ℕ} {X Y : CMfd.{0} n} {C P H : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {p : Y}
    (hCH : ∀ᶠ x in 𝓝 (π p), x ∈ C → x ∈ H)
    (htrace : ∀ᶠ q in 𝓝 p, q ∈ geoStrictTransform π C P → π q ∈ C →
      q ∈ geoStrictTransform π C H)
    (hproj : ∀ W : Set Y, IsOpen W → p ∈ W →
      ∀ᶠ x in 𝓝 (π p), x ∈ C → ∃ q ∈ W, π q = x ∧ q ∈ geoStrictTransform π C P) :
    ∀ᶠ x in 𝓝 (π p), x ∈ C → tangentSpace n P x ≤ tangentSpace n H x := by
  let : Fact (IsClosedSubmanifold n C) := ⟨hπ.1⟩
  obtain ⟨W,hWsub,hWopen,hpW⟩ := mem_nhds_iff.mp htrace
  have hnear := (hproj W hWopen hpW).and hCH.eventually_nhds
  filter_upwards [hnear] with x hx hxC
  obtain ⟨q,hqW,hqπ,hqP⟩ := hx.1 hxC
  have hqC : π q ∈ C := hqπ ▸ hxC
  have hqCH : ∀ᶠ t in 𝓝 (π q), t ∈ C → t ∈ H := hqπ ▸ hx.2
  by_contra hnt
  have hnt' : ¬ tangentSpace n P (π q) ≤ tangentSpace n H (π q) := hqπ ▸ hnt
  have hf := frequently_strict_not_boundary_of_containing_germ hπ hπ.2.1 hP hCP hqP hqC hqCH hnt'
  obtain ⟨r,⟨hrπ,hrP,hrH⟩,hrW⟩ := (hf.and_eventually (hWopen.mem_nhds hqW)).exists
  have hrC : π r ∈ C := hrπ ▸ hqC
  exact hrH (hWsub hrW hrP hrC)


/-- For an arbitrary actual blowup, local trace containment forces tangent
containment at every nearby centre point, with no projection hypothesis. -/
theorem actual_uniform_tangent_of_trace_containment
    {n : ℕ} {X Y : CMfd.{0} n} {C P H : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {p : Y} (hp : p ∈ geoStrictTransform π C P) (hpC : π p ∈ C)
    (hCH : ∀ᶠ x in 𝓝 (π p), x ∈ C → x ∈ H)
    (htrace : ∀ᶠ q in 𝓝 p, q ∈ geoStrictTransform π C P → π q ∈ C →
      q ∈ geoStrictTransform π C H) :
    ∀ᶠ x in 𝓝 (π p), x ∈ C → tangentSpace n P x ≤ tangentSpace n H x := by
  apply uniform_tangent_of_trace_containment hπ hP hCP hCH htrace
  intro W hW hpW
  exact HironakaG8TraceLocalSection.actual_trace_projects_near_base hπ hP hCP hp hpC
    W (hW.mem_nhds hpW)

end Hironaka.HironakaG11TraceUniformTangency
