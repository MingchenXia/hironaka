import Hironaka.Resolution.HironakaG10JointStrictTorsion
import Hironaka.Resolution.HironakaActualAnalyticSubspaceOpenRestriction

/-! # The actual native target-stalk image in the open-chart joint ideal -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG10JointNativeIdealMap
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualWholeStalkHolomorphicPullback HironakaActualAnalyticSubspaceOpenRestriction
  HironakaHolomorphicJetRankLoci
variable (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
  (U : Opens (ComplexModel (d+t))) (W : Set U)
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
variable (f : realOpenChartDomain d t j b U → Y) (V : Set Y)

/-- For an analytic target and its actual holomorphic map, the pullback
section ideal has exactly the image ideal of the genuine native stalk map. -/
theorem targetIdeal_eq_native_map [IsComplexManifold n Y]
    (hf : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hV : IsComplexAnalyticSubset (n := n) V) (y : realOpenChartDomain d t j b U) :
    targetIdeal (n := n) d t j b U f V y =
      Ideal.map ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) V) (f y)) := by
  let es := actualStalkChartEquiv (n := d+t) y
  let et := actualStalkChartEquiv (n := n) (f y)
  let F := (ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y
  have hcomp : es.toRingHom.comp F.hom = (actualHolomorphicGermPullback hf y).toRingHom.comp et.toRingHom := by
    apply RingHom.ext
    intro r
    exact actualNativeStalk_chart_pullback hf y r
  apply es.idealComapOrderIso.symm.injective
  change Ideal.map es.toRingHom (actualWholeSheafStalkIdeal
      (GermIdeal.pullback (m := d+t) f (vanishingIdeal (n := n) V)) y) =
    Ideal.map es.toRingHom (Ideal.map F.hom (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) V) (f y)))
  calc
    _ = wholeChartStalkIdeal (GermIdeal.pullback (m := d+t) f (vanishingIdeal (n := n) V))
        y y (mem_chart_source _ y) := map_actualWholeSheafStalkIdeal _ y
    _ = Ideal.map (actualHolomorphicGermPullback hf y).toRingHom
        (wholeChartStalkIdeal (vanishingIdeal (n := n) V) (f y) (f y) (mem_chart_source _ _)) :=
      (map_wholeChartStalkIdeal_actual_pullback hf _ (CartanIrreducible.cartanCoherence V hV) y).symm
    _ = Ideal.map (actualHolomorphicGermPullback hf y).toRingHom
        (Ideal.map et.toRingHom (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) V) (f y))) := by
      rw [map_actualWholeSheafStalkIdeal]
    _ = Ideal.map ((actualHolomorphicGermPullback hf y).toRingHom.comp et.toRingHom)
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) V) (f y)) :=
      Ideal.map_map et.toRingHom (actualHolomorphicGermPullback hf y).toRingHom
    _ = Ideal.map (es.toRingHom.comp F.hom)
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) V) (f y)) := by
      exact congrArg (fun h : actualComplexStructureStalk (n := n) (f y) →+* HolGerm (ComplexModel (d+t)) =>
        Ideal.map h (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) V) (f y))) hcomp.symm
    _ = _ := (Ideal.map_map F.hom es.toRingHom).symm


/-- The whole actual target-stalk image is contained in the strict-source
stalk ideal whenever the actual map sends the strict source into the target. -/
theorem targetNativeIdeal_le_strict [IsComplexManifold n Y]
    (hf : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hV : IsComplexAnalyticSubset (n := n) V)
    (hland : realOpenStrictTransform d t j b U W ⊆ f ⁻¹' V)
    (y : realOpenChartDomain d t j b U) :
    Ideal.map ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) V) (f y)) ≤
        geometricStrictIdeal d t j b U W y := by
  rw [←targetIdeal_eq_native_map (n := n) d t j b U f V hf hV y]
  exact targetIdeal_le_strict (n := n) d t j b U W f V hf.continuous hland y
end
end Hironaka.HironakaG10JointNativeIdealMap
