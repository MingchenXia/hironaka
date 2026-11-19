import Hironaka.Resolution.HironakaG3LocallyFiniteStrictUnion
import Hironaka.Resolution.HironakaG3IndexedSeparatedComponents
import Hironaka.Resolution.HironakaG3RSimultaneousBlowup
import Hironaka.Resolution.StrictTransformComposition
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ComposedSeparatedStrictGeometry
noncomputable section
open Hironaka.BlowupSequences BlowupTowers SubmanifoldChartedSpace
  HironakaG3LocallyFiniteStrictUnion HironakaG3IndexedSeparatedComponents
  HironakaG3RSimultaneousBlowup

theorem composed_separated_strict_geometry {n d : ℕ} {X Z Y : CMfd.{0} n} {ι : Type*}
    (C : ι → Set X) (hClosed : ∀ i, IsClosed (C i)) (hLF : LocallyFinite C)
    {P : Z → X} {Q : Y → Z}
    (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (hQ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ Q)
    (hDis : ∀ i j, i ≠ j → Disjoint (strictTransform n P (C i)) (strictTransform n P (C j)))
    (hProjP : ∀ i, P '' strictTransform n P (C i) = C i)
    (hProjQ : ∀ i, Q '' strictTransform n Q (strictTransform n P (C i)) = strictTransform n P (C i))
    (hSmooth : ∀ i, IsClosedSubmanifold n (strictTransform n Q (strictTransform n P (C i))))
    (hRegular : ∀ i y, y ∈ strictTransform n Q (strictTransform n P (C i)) →
      RegularAtDim (n := n) (strictTransform n Q (strictTransform n P (C i))) y d) :
    let W := ⋃ i, C i
    (P ∘ Q) '' strictTransform n (P ∘ Q) W = W ∧
      IsClosedSubmanifold n (strictTransform n (P ∘ Q) W) ∧
      ∀ y ∈ strictTransform n (P ∘ Q) W, RegularAtDim (n := n) (strictTransform n (P ∘ Q) W) y d := by
  let A : ι → Set Z := fun i => strictTransform n P (C i)
  let T : ι → Set Y := fun i => strictTransform n Q (A i)
  have hALF : LocallyFinite A := locallyFinite_strictTransforms C hClosed hLF hP.continuous
  have hTLF : LocallyFinite T := locallyFinite_strictTransforms A (fun _ => isClosed_closure) hALF hQ.continuous
  have hTDis : Pairwise (Disjoint on T) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro y hi hj
    exact Set.disjoint_left.mp (hDis i j hij)
      (HironakaAdmissibleCalculus.strictTransform_subset_preimage hQ.continuous isClosed_closure hi)
      (HironakaAdmissibleCalculus.strictTransform_subset_preimage hQ.continuous isClosed_closure hj)
  have hEq : strictTransform n (P ∘ Q) (⋃ i, C i) = ⋃ i, T i := by
    rw [StrictTransformComposition.strictTransform_comp hP hQ, strictTransform_iUnion_of_locallyFinite C hLF P hP.continuous,
      strictTransform_iUnion_of_locallyFinite A hALF Q hQ.continuous]
  refine ⟨?_,?_,?_⟩
  · rw [hEq, image_iUnion]
    apply iUnion_congr
    intro i
    rw [image_comp, hProjQ i, hProjP i]
  · rw [hEq]
    exact isClosedSubmanifold_iUnion hTLF hTDis hSmooth
  · rw [hEq]
    intro y hy
    obtain ⟨i,hyi⟩ := mem_iUnion.mp hy
    obtain ⟨O,hO,hyO,hEqO⟩ := exists_open_iUnion_inter_eq hTLF (fun i => (hSmooth i).1) hTDis hyi
    exact RegularPointDimension.regularAtDim_of_inter_eq hO hyO hEqO.symm (hRegular i y hyi)
end
end Hironaka.HironakaG3ComposedSeparatedStrictGeometry
