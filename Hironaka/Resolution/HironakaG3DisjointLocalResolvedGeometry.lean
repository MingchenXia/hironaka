import Hironaka.Resolution.HironakaG3DisjointAtlasComponentChart
import Hironaka.Resolution.HironakaG3RPureEmbedded
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointLocalResolvedGeometry
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings SubmanifoldChartedSpace
  HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3DisjointLocalTowerAtlas
  HironakaG3DisjointAtlasComponentChart

theorem disjoint_atlas_component_resolved_geometry {n : ℕ} {X Z : CMfd.{0} n} {ι : Type*}
    (C : ι → Set X) (r : ι → ℕ) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hClosed : ∀ i, IsClosed (C i))
    (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set X))
    (hLocal : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T →
      T.proj '' strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C i) = (Subtype.val : U → X) ⁻¹' C i ∧
      ∀ y ∈ strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C i),
        RegularAtDim (n := n) (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C i)) y (r i))
    {P : Z → X} (hG : IsGluedFrom (disjointWindowClass C W K) Z P) :
    ∀ i, P '' strictTransform n P (C i) = C i ∧
      IsClosedSubmanifold n (strictTransform n P (C i)) ∧
      ∀ z ∈ strictTransform n P (C i), RegularAtDim (n := n) (strictTransform n P (C i)) z (r i) := by
  intro i
  have hReg : ∀ z ∈ strictTransform n P (C i), RegularAtDim (n := n) (strictTransform n P (C i)) z (r i) := by
    intro z hz
    have hzC : P z ∈ C i := HironakaAdmissibleCalculus.strictTransform_subset_preimage hG.1.continuous (hClosed i) hz
    obtain ⟨c,hU,_⟩ := exists_component_chart_for_disjoint_atlas C W K hWindow hG i hzC
    have hzV : z ∈ c.V := c.mem_V hU
    let y := c.φ.symm ⟨z,hzV⟩
    have hyz : chartIncl c y = z := chartIncl_symm c ⟨z,hzV⟩
    have hy : y ∈ strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' C i) := by
      rw [strictTransform_chart c hG.1 (C i)]
      change chartIncl c y ∈ strictTransform n P (C i)
      rwa [hyz]
    have hreg := (hLocal i c.U c.Y c.T c.mem).2 y hy
    rw [strictTransform_chart c hG.1 (C i)] at hreg
    have hglobal := regularAtDim_of_chart c hreg
    rwa [hyz] at hglobal
  refine ⟨?_,⟨isClosed_closure,fun z hz => ⟨r i,hReg z hz⟩⟩,hReg⟩
  apply Set.Subset.antisymm
  · rintro x ⟨z,hz,rfl⟩
    exact HironakaAdmissibleCalculus.strictTransform_subset_preimage hG.1.continuous (hClosed i) hz
  · intro x hx
    obtain ⟨c,hU,_⟩ := exists_component_chart_for_disjoint_atlas C W K hWindow hG i hx
    have hxU : (⟨x,hU⟩ : c.U) ∈ (Subtype.val : c.U → X) ⁻¹' C i := hx
    have hProj := (hLocal i c.U c.Y c.T c.mem).1
    rw [← hProj] at hxU
    obtain ⟨y,hy,hyP⟩ := hxU
    refine ⟨chartIncl c y,?_,?_⟩
    · rw [strictTransform_chart c hG.1 (C i)] at hy
      exact hy
    · have heq := proj_chartIncl c y
      rw [hyP] at heq
      exact heq
end
end Hironaka.HironakaG3DisjointLocalResolvedGeometry
