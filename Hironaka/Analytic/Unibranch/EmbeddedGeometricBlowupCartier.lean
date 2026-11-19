import Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowup
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalIdealStalk
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartier
import Hironaka.Resolution.HironakaSingularRankOneLocalGenerators
import Hironaka.Resolution.HironakaSingularIdealRegularPrincipal

/-!
# The SAME geometric projection's own actual Cartier ideal, without target density

The genuine geometric-transform invertibility theorem supplies the ambient
generator. The original quotient-stalk and canonical ideal-sheaf dictionaries
retain the entire ideal and actual scalar action. Native rank-one data are
derived from actual sections, never supplied as an extra geometric premise.
Blueprint FIRST: `embedded-geometric-blowup-cartier.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowupCartier

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSingularSubspaceBlowupCartier
  HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf
  HironakaSingularSubspaceBlowupCartierUniversalIdealStalk
  HironakaSingularRankOneLocalGenerators HironakaSingularIdealRegularPrincipal
  BlowupStrictSubmanifold IdealWeightPowers MarkedIdeals.MarkedIdeal EmbeddedGeometricBlowup

noncomputable section

variable {n : ℕ} {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C W : Set M} {π : Y → M}

/-- ONE actual ambient section generates the ENTIRE original nested
projection ideal regularly at EVERY nearby geometric-source stalk. -/
theorem exists_local_geometric_cartier_generator
    (hπ : IsBlowupAlong n C π) (hW : IsClosed W) (x : geoStrictTransform π C W) :
    ∃ (U : Opens Y) (_hxU : x.val ∈ U) (a : actualComplexSection (n := n) U),
      ∀ (y : geoStrictTransform π C W) (hy : y.val ∈ U),
        let p := geometricProjection hπ hW
        let alpha := ((actualSubspaceInclusion (n := n) (geoStrictTransform π C W)).stalkMap y)
          ((actualComplexStructureSheaf (n := n) Y).presheaf.germ U y.val hy a)
        Ideal.map (p.stalkMap y).hom
          (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (p.base y)).hom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (π y.val))) =
          Ideal.span {alpha} ∧ IsRegular alpha := by
  have hinv := isInvertibleAlong_geoStrictTransform hπ W 1
  have hpow : idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 1 =
      GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C) :=
    BlowupStrictIdeal.idealPow_one_exceptionalDivisor hπ
  rw [hpow] at hinv
  obtain ⟨U, hxU, a, ha⟩ := exists_local_actual_cartier_generator hinv x
  refine ⟨U, hxU, a, ?_⟩
  intro y hy
  have hmap := map_actualSubspace_stalk_ideal_pullback hπ.contMDiff
    (fun z (hz : z ∈ geoStrictTransform π C W) =>
      geoStrictTransform_subset_preimage hπ.contMDiff.continuous hW hz)
    (vanishingIdeal (n := n) C)
    (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ) y
  change Ideal.map ((geometricProjection hπ hW).stalkMap y).hom
      (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap
        ((geometricProjection hπ hW).base y)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (π y.val))) = _ ∧ _
  exact ⟨hmap.trans (ha y hy).1, (ha y hy).2⟩

/-- ONE actual canonical ideal section on ONE original source open has
regular generating original germs at EVERY point of that open. -/
theorem exists_local_geometric_ideal_sheaf_generator
    (hπ : IsBlowupAlong n C π) (hW : IsClosed W) (x : geoStrictTransform π C W) :
    ∃ (U : Opens (actualSubspaceLocallyRingedSpace (n := n) (geoStrictTransform π C W)).toTopCat)
      (_hxU : x ∈ U)
      (s : actualPulledCentreSectionIdeal
        (geometricProjection hπ hW ≫ actualSubspaceInclusion (n := n) W) C U),
      ∀ (y : geoStrictTransform π C W) (hy : y ∈ U),
        Ideal.map ((geometricProjection hπ hW ≫ actualSubspaceInclusion (n := n) W).stalkMap y).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C)
            ((geometricProjection hπ hW ≫ actualSubspaceInclusion (n := n) W).base y)) =
          Ideal.span {((actualSubspaceLocallyRingedSpace (n := n) (geoStrictTransform π C W)).presheaf.germ
            U y hy s.val)} ∧
        IsRegular ((actualSubspaceLocallyRingedSpace (n := n) (geoStrictTransform π C W)).presheaf.germ
          U y hy s.val) := by
  obtain ⟨V, hxV, a, ha⟩ := exists_local_geometric_cartier_generator hπ hW x
  let X := actualSubspaceLocallyRingedSpace (n := n) (geoStrictTransform π C W)
  let j : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) Y :=
    actualSubspaceInclusion (n := n) (geoStrictTransform π C W)
  let p := geometricProjection hπ hW
  let H := p ≫ actualSubspaceInclusion (n := n) W
  let U : Opens X.toTopCat := (Opens.map j.base).obj V
  let s₀ : (X.presheaf.obj (op U)).carrier := j.c.app (op V) a
  have hgen : ∀ (y : geoStrictTransform π C W) (hy : y ∈ U),
      Ideal.map (H.stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (H.base y)) =
        Ideal.span {X.presheaf.germ U y hy s₀} ∧ IsRegular (X.presheaf.germ U y hy s₀) := by
    intro y hy
    have hg : X.presheaf.germ U y hy s₀ =
        j.stalkMap y ((actualComplexStructureSheaf (n := n) Y).presheaf.germ V y.val hy a) :=
      (LocallyRingedSpace.stalkMap_germ_apply j V y hy a).symm
    rw [hg]
    have heq := (actualPulledCentreStalkInclusion_range H C y).symm.trans
      (actualPulledCentreStalkInclusion_range_subspace p C y)
    exact ⟨heq.trans (ha y hy).1, (ha y hy).2⟩
  have hs₀ : s₀ ∈ actualPulledCentreSectionIdeal H C U := by
    intro y hy
    rw [(hgen y hy).1]
    exact Ideal.subset_span (Set.mem_singleton _)
  exact ⟨U, hxV, ⟨s₀, hs₀⟩, hgen⟩

private instance originalOverHasWeakSheafify (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat) :
    HasWeakSheafify ((Opens.grothendieckTopology X.toTopCat).over U) AddCommGrpCat.{0} :=
  CategoryTheory.sheafToPresheaf_isRightAdjoint
    ((Opens.grothendieckTopology X.toTopCat).over U) AddCommGrpCat.{0}

/-- The SAME geometric projection's canonical ideal has DERIVED standard
native rank-one local-free data, including actual singleton indices. -/
theorem geometricProjection_ideal_exists_locallyFreeData
    (hπ : IsBlowupAlong n C π) (hW : IsClosed W) :
    ∃ q : (actualPulledCentreIdealModule
        (geometricProjection hπ hW ≫ actualSubspaceInclusion (n := n) W) C).LocalGeneratorsData.{0},
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (Unique (q.generators i).I) := by
  classical
  let X := actualSubspaceLocallyRingedSpace (n := n) (geoStrictTransform π C W)
  let H := geometricProjection hπ hW ≫ actualSubspaceInclusion (n := n) W
  choose U hxU s hs using exists_local_geometric_ideal_sheaf_generator hπ hW
  exact exists_locallyFreeData_of_regular_sections X.toSheafedSpace.sheaf
    (actualPulledCentreIdealInclusion H C) (fun _ => Subtype.val_injective)
    U (fun x => ⟨x, hxU x⟩) s
    (fun i x hx => (hs i x hx).2)
    (fun i x hx => (actualPulledCentreStalkInclusion_range H C x).trans (hs i x hx).1)

/-- Native local freeness is an OUTPUT on the same canonical module. -/
theorem geometricProjection_ideal_isLocallyFree
    (hπ : IsBlowupAlong n C π) (hW : IsClosed W) :
    (actualPulledCentreIdealModule
      (geometricProjection hπ hW ≫ actualSubspaceInclusion (n := n) W) C).IsLocallyFree := by
  obtain ⟨q, hq, _hunique⟩ := geometricProjection_ideal_exists_locallyFreeData hπ hW
  let : q.IsLocallyFreeData := hq
  exact q.isLocallyFree

/-- Native module invertibility of the ENTIRE nested ideal at EVERY
actual geometric-source stalk, with NO target-density premise. -/
theorem geometricProjection_ideal_moduleInvertible
    (hπ : IsBlowupAlong n C π) (hW : IsClosed W) (x : geoStrictTransform π C W) :
    Module.Invertible ((actualSubspaceSheaf (n := n) (geoStrictTransform π C W)).presheaf.stalk x).carrier
      (Ideal.map ((geometricProjection hπ hW).stalkMap x).hom
        (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap
          ((geometricProjection hπ hW).base x)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C)
            ((geometricProjection hπ hW).base x).val))) := by
  obtain ⟨U, hxU, a, ha⟩ := exists_local_geometric_cartier_generator hπ hW x
  exact moduleInvertible_of_span_eq _ (ha x hxU).1 (ha x hxU).2

end

end Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowupCartier
