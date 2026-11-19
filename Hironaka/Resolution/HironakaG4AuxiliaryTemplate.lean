import Hironaka.Resolution.HironakaG4AmbientPreparedGammaChart
import Hironaka.Resolution.HironakaG4WellFormedSubopen

/-! The local auxiliary divisor defines the enlarged zero-marked template. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4AuxiliaryTemplate
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupRestrictOpen
  NormalCrossings HironakaSharpActualFiniteChronologicalHistory HironakaG4OpenClosedExtension
  IdealWeightPowers GermIdealPullbackCalculus

variable {n : ℕ} {X : CMfd.{u} n}

/-- Closing the auxiliary divisor in the ambient space gives a zero-marked
record which is well formed on the protected source window. -/
theorem auxiliary_geometric_template_on_window (U : Opens X) (N S : Set X)
    (F : List (Set X)) (Haux : Set U) (hN : IsClosedSubmanifold n N)
    (hEF : IsSNCDivisor n (Haux :: F.map ((Subtype.val : U → X) ⁻¹' ·)))
    (hTF : IsTransverse n ((Subtype.val : U → X) ⁻¹' N)
      (Haux :: F.map ((Subtype.val : U → X) ⁻¹' ·)))
    (hSlice : (Subtype.val : U → X) ⁻¹' S = (Subtype.val : U → X) ⁻¹' N ∩ Haux) :
    let G : Set X := closure ((Subtype.val : U → X) '' Haux)
    let D : MarkedIdeal n X := geometricTemplate N (G :: F)
    IsClosed G ∧ (MarkedIdeal.pullback (Subtype.val : U → X) D).IsWellFormed ∧
      (Subtype.val : U → X) ⁻¹' S = (Subtype.val : U → X) ⁻¹' (D.N ∩ G) := by
  let G : Set X := closure ((Subtype.val : U → X) '' Haux)
  let D : MarkedIdeal n X := geometricTemplate N (G :: F)
  have hG : (Subtype.val : U → X) ⁻¹' G = Haux :=
    preimage_closure_image_eq U (hEF.1 Haux (by simp))
  refine ⟨isClosed_closure, ?_, ?_⟩
  · refine ⟨isClosedSubmanifold_preimage_val hN U,
      isCoherent_pullback contMDiff_subtype_val (isCoherent_unitIdeal (n := n) (M := X)), ?_, ?_⟩
    · change IsSNCDivisor n ((Subtype.val : U → X) ⁻¹' G :: F.map ((Subtype.val : U → X) ⁻¹' ·))
      rw [hG]
      exact hEF
    · change IsTransverse n ((Subtype.val : U → X) ⁻¹' N)
        ((Subtype.val : U → X) ⁻¹' G :: F.map ((Subtype.val : U → X) ⁻¹' ·))
      rw [hG]
      exact hTF
  · change (Subtype.val : U → X) ⁻¹' S = (Subtype.val : U → X) ⁻¹' N ∩ (Subtype.val : U → X) ⁻¹' G
    rw [hG]
    exact hSlice

end
end Hironaka.HironakaG4AuxiliaryTemplate
