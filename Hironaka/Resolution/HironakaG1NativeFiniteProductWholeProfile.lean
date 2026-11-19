import Hironaka.Resolution.HironakaG1NativeFiniteProductState
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport

/-! All points of the ACTUAL finite free product retain their whole
intrinsic HS profile. Blueprint FIRST; no native/cosupport packet. -/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1NativeFiniteProductWholeProfile
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HironakaG1NativeFiniteProductState HironakaG11PresLineState HironakaG11PresLineStable
  HironakaActualProjectionTestRecord HironakaActualVanishingIntrinsicHSTransport
  HironakaHolomorphicJetChartInvariance
open scoped ProductComplexManifold

variable {n : ℕ} {X : CMfd.{0} n} (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)

include hW in
/-- ALL points and ALL orders, including regular and outside-support points. -/
theorem finite_product_vanishing_profile (r : ℕ) (p : finiteProductAmbient X r) :
    hilbertSamuelAt (vanishingIdeal (n := n+r)
      ((Prod.fst : finiteProductAmbient X r→X) ⁻¹' W)) p=
      finiteProductHS r (hilbertSamuelAt (vanishingIdeal (n := n) W) p.1) := by
  induction r with
  | zero =>
    funext l
    exact hilbertSamuelAt_vanishing_actual_biholomorphic_any (zeroProductEquiv X) W p l
  | succ r ih =>
    let : ChartedSpace (ComplexModel (n+(r+1))) (projectionAmbient (finiteProductAmbient X r)) := by
      change ChartedSpace (ComplexModel ((n+r)+1)) (projectionAmbient (finiteProductAmbient X r))
      infer_instance
    let : IsComplexManifold (n+(r+1)) (projectionAmbient (finiteProductAmbient X r)) := by
      change IsComplexManifold ((n+r)+1) (projectionAmbient (finiteProductAmbient X r))
      infer_instance
    let Wr : Set (finiteProductAmbient X r) :=
      (Prod.fst : finiteProductAmbient X r→X) ⁻¹' W
    have hWr : IsComplexAnalyticSubset (n := n+r) Wr :=
      AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage ProductComplexManifold.contMDiff_fst hW
    let E:=successorProductEquiv X r
    funext l
    have hb:=hilbertSamuelAt_vanishing_actual_biholomorphic_any E
      ((Prod.fst : projectionAmbient (finiteProductAmbient X r)→finiteProductAmbient X r) ⁻¹' Wr) p l
    change hilbertSamuelAt (vanishingIdeal (n := n+(r+1))
      ((Prod.fst : finiteProductAmbient X (r+1)→X) ⁻¹' W)) p l=_ at hb
    rw [hb,hilbertSamuelAt_line Wr (CartanIrreducible.cartanCoherence Wr hWr)]
    have hi:=ih (E p).1
    change hilbertSamuelAt (vanishingIdeal (n := n+r) Wr) (E p).1=
      finiteProductHS r (hilbertSamuelAt (vanishingIdeal (n := n) W) p.1) at hi
    rw [hi]
    rfl

end
end Hironaka.HironakaG1NativeFiniteProductWholeProfile
