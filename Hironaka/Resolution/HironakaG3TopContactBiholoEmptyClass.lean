import Hironaka.Resolution.HironakaG3TopContactEmptyClass
import Hironaka.Invariant.CodimOnePartCanonical
import Hironaka.Analytic.AnalyticSubsetOpens
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3TopContactBiholoEmptyClass
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings SubmanifoldChartedSpace
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation HironakaG3RTowerClass
  HironakaG3DisjointLocalTowerAtlas HironakaG3IndexedContainingBoundary HironakaG3IndexedTopContact
  HironakaG3TopContactEmptyClass RestrictEmptyTower
open ResolutionInvariantExt (IsEmptyTower)

def biholoEmptyClass {n : ℕ} {X : CMfd.{0} n} : LocalTowerClass X :=
  fun U Y T => IsEmptyTower T ∧ ∃ e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) U),
    ∀ y, T.proj y = e y

theorem biholo_empty_class_comparisons {n : ℕ} {X : CMfd.{0} n} : HasComparisons (biholoEmptyClass (X := X)) := by
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
  exact avoiding_overlap_comparison U₁ U₂ T₁ T₂ (empty_avoids _ T₁ h₁.1) (empty_avoids _ T₂ h₂.1)

theorem biholo_empty_class_resolved {n r : ℕ} {X : CMfd.{0} n} (C : Set X)
    (hClosed : IsClosed C) (hReg : ∀ x ∈ C, RegularAtDim (n := n) C x r)
    (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y)
    (hT : biholoEmptyClass U Y T) :
    T.proj '' strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C) = (Subtype.val : U → X) ⁻¹' C ∧
    ∀ y ∈ strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C),
      RegularAtDim (n := n) (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C)) y r := by
  obtain ⟨_hEmpty,e,hProj⟩ := hT
  have hFun : T.proj = (e : Y → U) := funext hProj
  have hExc : exceptionalLocus n T.proj = ∅ := by
    rw [hFun]
    exact Set.eq_empty_iff_forall_notMem.mpr (fun y => MarkedIdealTowerTransport.notMem_exceptionalLocus e y)
  have hC : IsClosed ((Subtype.val : U → X) ⁻¹' C) := hClosed.preimage continuous_subtype_val
  have hEq : strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C) = e ⁻¹' ((Subtype.val : U → X) ⁻¹' C) := by
    rw [strictTransform,hExc,sdiff_empty,hFun,(hC.preimage e.continuous).closure_eq]
  constructor
  · rw [hEq,hFun]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x,by simpa using hx,e.apply_symm_apply x⟩
  · intro y hy
    have hy' : e y ∈ (Subtype.val : U → X) ⁻¹' C := by simpa only [hEq,mem_preimage] using hy
    have hxReg : RegularAtDim (n := n) ((Subtype.val : U → X) ⁻¹' C) (e y) r :=
      AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hReg (e y) hy')
    have hyReg := (CodimOnePartCanonical.regularAtDim_preimage_iff e).mpr hxReg
    simpa only [hEq] using hyReg

theorem top_contact_biholo_empty_class_data {n r : ℕ} {X : CMfd.{0} n} {κ : Type*} [LinearOrder κ]
    (C : Set X) (D : κ → Set X) (hC : IsComplexAnalyticallyIrreducible (n := n) C)
    (hD : IsLocallyFiniteSNCDivisor n D) (hpure : C ⊆ closure (regularLocus (n := n) C r))
    (htop : n - (containingLabels C D hC.nonempty hD.1).card ≤ r) :
    HasComparisons (biholoEmptyClass (X := X)) ∧
      (∀ U : Opens X, ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), biholoEmptyClass U Y T) ∧
      (∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        biholoEmptyClass U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' C) T) ∧
      (∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        biholoEmptyClass U Y T →
        T.proj '' strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C) = (Subtype.val : U → X) ⁻¹' C ∧
        ∀ y ∈ strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C),
          RegularAtDim (n := n) (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C)) y r) ∧
      HasNormalCrossingsWithBoundary C D := by
  obtain ⟨_O,_hO,hSmooth,hReg,hNC⟩ := indexed_top_contact_already_normal C D hC hD hpure htop
  refine ⟨biholo_empty_class_comparisons,?_,?_,?_,hNC⟩
  · intro U
    exact ⟨CMfd.of (n := n) U,.refl,trivial,Diffeomorph.refl _ _ ∞,fun _ => rfl⟩
  · intro U Y T hT
    exact empty_tower_class_centres_over C U Y T hT.1
  · intro U Y T hT
    exact biholo_empty_class_resolved C hC.analytic.isClosed hReg U Y T hT
end
end Hironaka.HironakaG3TopContactBiholoEmptyClass
