import Hironaka.Resolution.HironakaG8CaseTSingleCut

/-!
# The singleton exceptional sum has the literal single-member cosupport

This identifies the actual Step I.B singleton finite sum with the single
power at every cosupport threshold, without assuming ideal equality.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseTSingleCutCosupport
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  GermIdealOrder DivisorExponentAlong IdealWeightPowers HomogenizedGlueing
  HironakaG8CaseTSingleCut

/-- The finite singleton exceptional sum and the corresponding literal
ideal power define the same cosupport at every threshold. -/
theorem cosupport_singleCut_iff
    {n : ℕ} {X : CMfd.{u} n} (A : MarkedIdeal n X)
    (G : List (Set X)) (H : Set X)
    (hHol : ∀ x f, A.ideal.mem x f → HolomorphicAt n f x)
    (e : ℕ) (x : X) :
    x ∈ cosupport n A.N (singleCut A G H).ideal e ↔
      x ∈ cosupport n A.N (RestrictedIdealExtension.sumIdeal A.ideal
        (idealPow (vanishingIdeal (n := n) H) A.d)) e := by
  have hPow : ∀ i x f,
      (idealPow (vanishingIdeal (n := n) ([H].getD i ∅)) A.d).mem x f → HolomorphicAt n f x :=
    fun _ _ _ hf => GermIdealOrder.holomorphicAt_of_mem_idealPow hf
  have hFin : cosupport n A.N
      (finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) ([H].getD i ∅)) A.d) [H].length) e =
      cosupport n A.N (idealPow (vanishingIdeal (n := n) H) A.d) e := by
    rw [HironakaG8LogFiniteSumCut.cosupport_finSumIdeal hPow]
    ext z
    constructor
    · rintro ⟨_hzN, hall⟩
      simpa using hall 0 (by simp)
    · intro hz
      refine ⟨hz.1, ?_⟩
      intro i hi
      have hi0 : i = 0 := by simpa using hi
      subst i
      simpa using hz
  have hFinHol : ∀ z f,
      (finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) ([H].getD i ∅)) A.d) [H].length).mem z f →
        HolomorphicAt n f z := by
    intro z f hf
    exact hf.1
  change x ∈ cosupport n A.N (RestrictedIdealExtension.sumIdeal A.ideal
    (finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) ([H].getD i ∅)) A.d) [H].length)) e ↔ _
  rw [IdealOrderArithmetic.cosupport_sumIdeal hHol hFinHol e,
    IdealOrderArithmetic.cosupport_sumIdeal hHol (fun _ _ hf =>
      GermIdealOrder.holomorphicAt_of_mem_idealPow hf) e, hFin]

end
end Hironaka.HironakaG8CaseTSingleCutCosupport
