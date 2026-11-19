import Hironaka.Analytic.PotentialTheory.Plurisubharmonic
import Hironaka.Analytic.PshConvexCone

/-!
# Addition of extended-real plurisubharmonic functions

Finite upper bounds turn addition into addition of nonnegative deficits. The
argument therefore retains negative-infinite values and never subtracts
infinite integrals. Compact discs supply the separate finite upper bounds.
-/

open Set MeasureTheory
open scoped Topology ENNReal

namespace Hironaka

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Deficits below separate finite upper bounds add, including at poles. -/
theorem finiteDeficit_add (C D : ℝ) {z w : EReal}
    (hz : z ≤ (C : EReal)) (hw : w ≤ (D : EReal)) :
    (((C + D : ℝ) : EReal) - (z + w)).toENNReal =
      ((C : EReal) - z).toENNReal + ((D : EReal) - w).toENNReal := by
  have hzT : z ≠ ⊤ := ne_of_lt (hz.trans_lt (EReal.coe_lt_top C))
  have hwT : w ≠ ⊤ := ne_of_lt (hw.trans_lt (EReal.coe_lt_top D))
  have hzN : 0 ≤ (C : EReal) - z :=
    (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top C))
      (Or.inl (EReal.coe_ne_bot C))).mpr hz
  have hwN : 0 ≤ (D : EReal) - w :=
    (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top D))
      (Or.inl (EReal.coe_ne_bot D))).mpr hw
  have heq : ((C + D : ℝ) : EReal) - (z + w) =
      ((C : EReal) - z) + ((D : EReal) - w) := by
    rw [EReal.coe_add, sub_eq_add_neg, EReal.neg_add (Or.inr hwT) (Or.inl hzT)]
    simp only [sub_eq_add_neg]
    ac_rfl
  rw [heq, EReal.toENNReal_add hzN hwN]

/-- The angular deficit of a sum is the sum of its measurable deficits. -/
theorem DiscPshOn.circleDeficit_add {u w : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (x v : E) {r : ℝ} (hr : 0 ≤ r)
    (hD : affineClosedDisc x v r ⊆ U) (C D : ℝ)
    (hC : ∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal))
    (hW : ∀ y ∈ affineClosedDisc x v r, w y ≤ (D : EReal)) :
    circleDeficit (fun y => u y + w y) x v r (C + D) =
      circleDeficit u x v r C + circleDeficit w x v r D := by
  unfold circleDeficit
  simp_rw [finiteDeficit_add C D
    (hC _ (circle_mem_affineClosedDisc x v hr _))
    (hW _ (circle_mem_affineClosedDisc x v hr _))]
  exact lintegral_add_left (hu.measurable_circle_deficit x v hr hD C) _

end Hironaka
