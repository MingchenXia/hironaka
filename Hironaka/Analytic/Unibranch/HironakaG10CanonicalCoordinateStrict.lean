import Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges

/-! Original geometric strict carriers in the existing canonical product coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold
namespace Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka BlowupFlatCoordinates BlowupStrictSubmanifold BlowupConstruction BlowupMonomialCharts
  HironakaG10RecenteredMonomialDomain
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart

variable {n r : ℕ} {P : Type} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P]
  [IsComplexManifold n P]
variable (a : ProductNormalCharts n r P) (j : Fin r)

/-- The original subset in the actual target flat coordinate open. -/
def coordinateSubset (W : Set (P × ComplexModel r)) : Set (canonicalTargetOpen a j) :=
  {u | (chartAt (ComplexModel (n+r)) ((a.base,0) : P × ComplexModel r)).symm
    ((productNormalChart (n := n) a.base j).Φ.invFun u.val) ∈ W}

/-- Its entire original geometric strict carrier is the monomial strict carrier. -/
theorem strict_carrier_coordinates (W : Set (P × ComplexModel r)) :
    strictChartCarrier a W j = (productChartDiffeomorph a j) ⁻¹'
      geoStrictTransform (monomialProjection n r j (canonicalTargetOpen a j))
        ((Subtype.val : canonicalTargetOpen a j → ComplexModel (n+r)) ⁻¹'
          complexCoordinatePlane (n+r) n) (coordinateSubset a j W) := by
  let c := productNormalChart (n := n) a.base j
  let O := productChartOpen a j
  let E := productChartDiffeomorph a j
  have hraw : (Subtype.val : O → _) ⁻¹'
      ((blowupProj (n+r) {q : P × ComplexModel r | q.2 = 0}) ⁻¹'
        (W \ {q : P × ComplexModel r | q.2 = 0})) =
      E ⁻¹' ((monomialProjection n r j (canonicalTargetOpen a j)) ⁻¹'
        (coordinateSubset a j W \
          ((Subtype.val : canonicalTargetOpen a j → ComplexModel (n+r)) ⁻¹'
            complexCoordinatePlane (n+r) n))) := by
    ext z
    have hsrc : z.val ∈ c.source := z.property
    have hdom : z.val.base ∈ c.dom := hsrc.1
    have hp := c.monomial_toFun hsrc
    have hinv := flatInverse_flat c.Φ hdom
    have hc := c.hflat hdom.1 hdom.2
    change monomial n (j.natAdd n) (c.toFun z.val) =
      c.Φ.toFun (chartAt (ComplexModel (n+r)) ((a.base,0) : P × ComplexModel r) z.val.base) at hp
    change (chartAt (ComplexModel (n+r)) ((a.base,0) : P × ComplexModel r)).symm
      (c.Φ.invFun (c.Φ.toFun (chartAt (ComplexModel (n+r)) ((a.base,0) : P × ComplexModel r)
        z.val.base))) = z.val.base at hinv
    change (z.val.base.2 = 0 ↔ c.Φ.toFun
      (chartAt (ComplexModel (n+r)) ((a.base,0) : P × ComplexModel r) z.val.base) ∈
        complexCoordinatePlane (n+r) n) at hc
    change (z.val.base ∈ W ∧ ¬ z.val.base.2 = 0) ↔ _
    change (z.val.base ∈ W ∧ ¬ z.val.base.2 = 0) ↔
      ((chartAt (ComplexModel (n+r)) ((a.base,0) : P × ComplexModel r)).symm
        (c.Φ.invFun (monomial n (j.natAdd n) (c.toFun z.val))) ∈ W ∧
      ¬ monomial n (j.natAdd n) (c.toFun z.val) ∈ complexCoordinatePlane (n+r) n)
    rw [hp,hinv]
    exact and_congr_right (fun _ => not_congr hc)
  change (Subtype.val : O → _) ⁻¹'
    closure ((blowupProj (n+r) {q : P × ComplexModel r | q.2 = 0}) ⁻¹'
      (W \ {q : P × ComplexModel r | q.2 = 0})) =
    E ⁻¹' closure ((monomialProjection n r j (canonicalTargetOpen a j)) ⁻¹'
      (coordinateSubset a j W \
        ((Subtype.val : canonicalTargetOpen a j → ComplexModel (n+r)) ⁻¹'
          complexCoordinatePlane (n+r) n)))
  calc
    _ = closure ((Subtype.val : O → _) ⁻¹'
        ((blowupProj (n+r) {q : P × ComplexModel r | q.2 = 0}) ⁻¹'
          (W \ {q : P × ComplexModel r | q.2 = 0}))) :=
      O.isOpen.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
        continuous_subtype_val _
    _ = closure (E ⁻¹' ((monomialProjection n r j (canonicalTargetOpen a j)) ⁻¹'
        (coordinateSubset a j W \ ((Subtype.val : canonicalTargetOpen a j → ComplexModel (n+r)) ⁻¹'
          complexCoordinatePlane (n+r) n)))) := congrArg closure hraw
    _ = _ := (E.toHomeomorph.preimage_closure _).symm

end
end Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict
