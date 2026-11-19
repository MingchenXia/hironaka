import Hironaka.Blowup.BlowupTowerTransforms

/-! The entire native TOTAL-created exceptional ideal of an actual appended tower.
Blueprint FIRST: `hironaka-actual-tower-exceptional-append.tex`.
No marked ideal, frame, order, cosupport or coherence packet is an input. -/

set_option autoImplicit false

open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaActualTowerExceptionalAppend

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupExceptionalDivisor GermIdealPullbackCalculus
  GermIdealTotalTransform InvertibleIdealQuotient

noncomputable section

/-- The SAME native appended tower accumulates the entire pulled old TOTAL
    ideal and the entire tail TOTAL ideal, with all coherence derived. -/
theorem exceptionalDivisor_append_ideal
    {n : ℕ} {X Y Z : CMfd.{u} n}
    (A : BlowupTower X Y) (R : BlowupTower Y Z) :
    (BlowupTowerTransforms.exceptionalDivisor (A.append R)).ideal =
      (GermIdeal.pullback (m := n) R.proj
        (BlowupTowerTransforms.exceptionalDivisor A).ideal).mul
          (BlowupTowerTransforms.exceptionalDivisor R).ideal := by
  have hA := isCoherent_ideal (BlowupTowerTransforms.exceptionalDivisor A)
  induction R with
  | refl =>
      change (BlowupTowerTransforms.exceptionalDivisor A).ideal =
        (GermIdeal.pullback (m := n) (id : Y → Y)
          (BlowupTowerTransforms.exceptionalDivisor A).ideal).mul (IdealWeightPowers.unitIdeal n Y)
      rw [BlowupControlledTransform.pullback_id hA, RestrictLeCalculus.mul_unitIdeal hA]
  | @step V W R0 C π hπ ih =>
      have hR := isCoherent_ideal (BlowupTowerTransforms.exceptionalDivisor R0)
      have hPR := isCoherent_pullback R0.contMDiff_proj hA
      have hK := isCoherent_pullback (R0.contMDiff_proj.comp hπ.contMDiff) hA
      have hL := isCoherent_pullback hπ.contMDiff hR
      have hJ := isCoherent_ideal (BlowupExceptionalDivisor.exceptionalDivisor hπ)
      change (GermIdeal.pullback (m := n) π
          (BlowupTowerTransforms.exceptionalDivisor (A.append R0)).ideal).mul
            (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal =
        (GermIdeal.pullback (m := n) (R0.proj ∘ π)
          (BlowupTowerTransforms.exceptionalDivisor A).ideal).mul
            ((GermIdeal.pullback (m := n) π
              (BlowupTowerTransforms.exceptionalDivisor R0).ideal).mul
                (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal)
      rw [ih, pullback_mul hπ.contMDiff hPR hR,
        ← pullback_comp R0.contMDiff_proj hπ.contMDiff hA, mul_assoc hK hL hJ]

end

end Hironaka.HironakaActualTowerExceptionalAppend
