import Hironaka.Resolution.HironakaEmbeddedDimensionParts
import Hironaka.Resolution.HironakaEmbeddedAnalytic
import Hironaka.Resolution.HironakaG4MaximalMatrixFibreGeometry
import Hironaka.Resolution.HironakaG8LocalPureFinish

/-! Disjoint smooth dimension parts and their protection during a finite
boundary phase on a different part. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG8SeparatedSmoothGeometry

open Hironaka.BlowupSequences BlowupTowers
  HironakaEmbeddedAnalytic HironakaEmbeddedDimensionParts
  HironakaAdmissibleSequence HironakaAdmissibleCalculus HironakaEmbeddedBoundary
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaSharpNormalCrossingsOpenLocus
  HironakaG4MaximalMatrixFibreGeometry RestrictEmptyTower

/-- On a smooth carrier every closed dimension part consists exactly of the
original regular points of that dimension. -/
theorem dimensionPart_eq_regularLocus_of_smooth {n d : ℕ} {X : CMfd.{u} n} {W : Set X}
    (hW : IsClosedSubmanifold n W) : dimensionPart (n := n) W d = regularLocus (n := n) W d := by
  apply Subset.antisymm ?_ subset_closure
  intro x hx
  obtain ⟨k, hk⟩ := hW.2 x (dimensionPart_subset hW.1 d hx)
  have hkd : k = d := by
    by_contra hne
    exact notMem_dimensionPart_of_regularAtDim hk hne hx
  exact hkd ▸ hk

theorem eventually_mem_union_iff_left {X : Type u} [TopologicalSpace X]
    {A B : Set X} (hB : IsClosed B) {x : X} (hx : x ∉ B) :
    ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ A ∪ B := by
  filter_upwards [hB.isOpen_compl.mem_nhds hx] with y hy
  exact ⟨Or.inl, fun h => h.elim id (fun hB => (hy hB).elim)⟩

/-- A disjoint union of closed smooth sets is smooth, with each dimension
retained on its own part. -/
theorem closedSubmanifold_union_disjoint {n : ℕ} {X : CMfd.{u} n} {A B : Set X}
    (hA : IsClosedSubmanifold n A) (hB : IsClosedSubmanifold n B) (hAB : Disjoint A B) :
    IsClosedSubmanifold n (A ∪ B) := by
  refine ⟨hA.1.union hB.1, fun x hx => ?_⟩
  rcases hx with hx | hx
  · obtain ⟨d, hd⟩ := hA.2 x hx
    exact ⟨d, CodimOneSupport.regularAtDim_of_eventually_mem_iff
      (eventually_mem_union_iff_left hB.1 (disjoint_left.mp hAB hx)) hd⟩
  · obtain ⟨d, hd⟩ := hB.2 x hx
    rw [union_comm]
    exact ⟨d, CodimOneSupport.regularAtDim_of_eventually_mem_iff
      (eventually_mem_union_iff_left hA.1 (disjoint_left.mp hAB.symm hx)) hd⟩

/-- Normal crossings joins pointwise on a disjoint union of closed parts. -/
theorem normalCrossings_union_disjoint {n : ℕ} {X : CMfd.{u} n} {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) {E : List (Set X)}
    (hAN : HasNormalCrossings n A E) (hBN : HasNormalCrossings n B E) : HasNormalCrossings n (A ∪ B) E := by
  intro x hx
  rcases hx with hx | hx
  · exact normalCrossingsAt_of_eventually_carrier_iff
      (eventually_mem_union_iff_left hB (disjoint_left.mp hAB hx)) (hAN x hx)
  · rw [union_comm]
    exact normalCrossingsAt_of_eventually_carrier_iff
      (eventually_mem_union_iff_left hA (disjoint_left.mp hAB.symm hx)) (hBN x hx)

/-- Density off one boundary union passes to each disjoint closed part. -/
theorem dense_complement_left_of_disjoint {X : Type u} [TopologicalSpace X]
    {A B D : Set X} (hB : IsClosed B) (hAB : Disjoint A B)
    (hDense : A ∪ B ⊆ closure ((A ∪ B) \ D)) : A ⊆ closure (A \ D) := by
  intro x hx
  rw [mem_closure_iff]
  intro U hU hxU
  obtain ⟨y, ⟨hyU, hyB⟩, ⟨hy, hyD⟩⟩ := mem_closure_iff.mp (hDense (Or.inl hx))
    (U ∩ Bᶜ) (hU.inter hB.isOpen_compl) ⟨hxU, disjoint_left.mp hAB hx⟩
  exact ⟨y, hyU, hy.elim id (fun h => (hyB h).elim), hyD⟩

/-- An actual phase over one closed part leaves the other part as its exact
inverse image, preserving its smoothness, dimension, density and any existing
normal crossings with the whole actual accumulated divisor. -/
theorem protected_smooth_part {n : ℕ} {X Y : CMfd.{u} n} {A B F : Set X}
    (hA : IsClosed A) (hB : IsClosedSubmanifold n B) (hAB : Disjoint A B)
    (hF : IsClosed F) (hFA : F ⊆ A) (M : MarkedIdeal n X)
    (hE : ∀ H ∈ M.E, IsClosed H)
    (T : BlowupTower X Y) (hTest : IsGeoTestTower M T) (hOver : CentresOver F T) :
    let D := strictTransform n T.proj B
    let ET := (geoTransformAlong M T).E
    D = T.proj ⁻¹' B ∧ IsClosedSubmanifold n D ∧
    Disjoint (strictTransform n T.proj A) D ∧
    (∀ y d, RegularAtDim (n := n) B (T.proj y) d → RegularAtDim (n := n) D y d) ∧
    (B ⊆ closure (B \ ⋃ H ∈ M.E, H) → D ⊆ closure (D \ ⋃ H ∈ ET, H)) ∧
    (HasNormalCrossings n B M.E → HasNormalCrossings n D ET) := by
  let D := strictTransform n T.proj B
  let ET := (geoTransformAlong M T).E
  have hBF : Disjoint B F := hAB.symm.mono_right hFA
  have hAdm := isAdmissibleBlowupSequence_proj M F T hTest hOver
  have hExc := IsAdmissibleBlowupSequence.exceptionalLocus_subset hAdm
  have hD : D = T.proj ⁻¹' B := strictTransform_eq_preimage_of_disjoint T.contMDiff_proj.continuous hExc hB.1 hBF
  have hReg (y : Y) (d : ℕ) (h : RegularAtDim (n := n) B (T.proj y) d) : RegularAtDim (n := n) D y d := by
    rw [hD]
    exact regularAtDim_preimage_of_disjoint T.contMDiff_proj hExc hBF h
  have hDcl : IsClosedSubmanifold n D := ⟨isClosed_closure, fun y hy => by
    have hyB : y ∈ T.proj ⁻¹' B := hD ▸ hy
    obtain ⟨d, hd⟩ := hB.2 (T.proj y) hyB
    exact ⟨d, hReg y d hd⟩⟩
  have hDisjoint : Disjoint (strictTransform n T.proj A) D := by
    apply disjoint_left.mpr
    intro y hy hD₀
    have hyB : y ∈ T.proj ⁻¹' B := hD ▸ hD₀
    exact disjoint_left.mp hAB (strictTransform_subset_preimage T.contMDiff_proj.continuous hA hy) hyB
  refine ⟨hD, hDcl, hDisjoint, hReg, ?_, ?_⟩
  · intro hDense
    have hDense' : B ⊆ closure (B \ ((⋃ H ∈ M.E, H) ∪ F)) := by
      apply hDense.trans (closure_mono ?_)
      rintro z ⟨hzB,hzE⟩
      exact ⟨hzB, fun h => h.elim hzE (disjoint_left.mp hBF hzB)⟩
    exact (strictTransform_subset_closure_diff T.contMDiff_proj hB.1 hDense').trans
      (closure_mono (sdiff_subset_sdiff_right (IsAdmissibleBlowupSequence.biUnion_subset hAdm hE)))
  · intro hNC
    change HasNormalCrossings n D ET
    rw [hD]
    exact IsAdmissibleBlowupSequence.hasNormalCrossings_preimage_of_disjoint hAdm hE hF hBF hNC

end Hironaka.HironakaG8SeparatedSmoothGeometry
