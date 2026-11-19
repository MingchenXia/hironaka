import Hironaka.Geometry.MonomialBlowupTowerChartData

/-! Separately checked actual chart maps and structure triangles for the global successor. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.MonomialBlowupTowerCharts.StepContext

open Algebra.NodeBlowupChart Algebra.MonomialBlowupIteration
open MonomialBlowupTower MonomialBlowupTowerBase BlowupGluing

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] [IsDomain A]
    {l : List A} {n : ℕ} {P t : A} {b : List A}
    (S : ChartData l n P (t * b.prod))

local instance (i : S.I) : IsOpenImmersion (S.inclusion i) := S.inclusion_open i
local instance : IsOpenImmersion S.continuationInclusion := S.continuation_open

abbrev center := stageCenter (originalCenter l) n

def finishedIdeal (i : S.I) : Ideal (Node A (S.factor i)) :=
  (prefixCenter l.prod (P * t)).map (S.ringMap i).toRingHom

def continuationIdeal : Ideal (Node A (t * b.prod)) :=
  (prefixCenter l.prod (P * t)).map S.continuationRingMap.toRingHom

omit [IsDomain A] in
theorem finished_comap (hprefix : (l.take (n + 1)).prod = P * t) (i : S.I) :
    (center (l := l) (n := n)).comap (S.inclusion i) =
      SpecIdealSheaf.specIdealSheaf _ (finishedIdeal S i) := by
  rw [stageCenter_comap_chart (S.ringMap i) (S.inclusion i) (S.inclusion_structure i), hprefix]
  rfl

omit [IsDomain A] in
theorem continuation_comap (hprefix : (l.take (n + 1)).prod = P * t) :
    (center (l := l) (n := n)).comap S.continuationInclusion =
      SpecIdealSheaf.specIdealSheaf _ (continuationIdeal S) := by
  rw [stageCenter_comap_chart S.continuationRingMap S.continuationInclusion
    S.continuation_structure, hprefix]
  rfl

def finishedGlobalMap (hprefix : (l.take (n + 1)).prod = P * t) (i : S.I) :
    affineBlowup (finishedIdeal S i) ⟶ blowup (center (l := l) (n := n)) := by
  let : IsOpenImmersion (S.inclusion i) := S.inclusion_open i
  exact BlowupOpenChart.chartMap (S.inclusion i) _ _ (finished_comap S hprefix i)

def continuationGlobalMap (hprefix : (l.take (n + 1)).prod = P * t) :
    affineBlowup (continuationIdeal S) ⟶ blowup (center (l := l) (n := n)) := by
  let : IsOpenImmersion S.continuationInclusion := S.continuation_open
  exact BlowupOpenChart.chartMap S.continuationInclusion _ _ (continuation_comap S hprefix)

instance finishedGlobalMap_open (hprefix : (l.take (n + 1)).prod = P * t) (i : S.I) :
    IsOpenImmersion (finishedGlobalMap S hprefix i) := by
  let : IsOpenImmersion (S.inclusion i) := S.inclusion_open i
  dsimp only [finishedGlobalMap]
  infer_instance

instance continuationGlobalMap_open (hprefix : (l.take (n + 1)).prod = P * t) :
    IsOpenImmersion (continuationGlobalMap S hprefix) := by
  let : IsOpenImmersion S.continuationInclusion := S.continuation_open
  dsimp only [continuationGlobalMap]
  infer_instance

omit [IsDomain A] in
@[reassoc]
theorem finishedGlobalMap_structure (hprefix : (l.take (n + 1)).prod = P * t) (i : S.I) :
    finishedGlobalMap S hprefix i ≫ blowupStructure (center (l := l) (n := n)) =
      affineBlowupStructure (finishedIdeal S i) ≫ S.inclusion i := by
  let : IsOpenImmersion (S.inclusion i) := S.inclusion_open i
  exact BlowupOpenChart.chartMap_structure _ _ _ (finished_comap S hprefix i)

omit [IsDomain A] in
@[reassoc]
theorem continuationGlobalMap_structure (hprefix : (l.take (n + 1)).prod = P * t) :
    continuationGlobalMap S hprefix ≫ blowupStructure (center (l := l) (n := n)) =
      affineBlowupStructure (continuationIdeal S) ≫ S.continuationInclusion := by
  let : IsOpenImmersion S.continuationInclusion := S.continuation_open
  exact BlowupOpenChart.chartMap_structure _ _ _ (continuation_comap S hprefix)

def finishedIso (i : S.I) :
    affineBlowup (finishedIdeal S i) ≅ Spec (CommRingCat.of (Node A (S.factor i))) :=
  MonomialBlowupTowerAlgebra.finishedBlowupIso (S.ringMap i) (S.scale i) (P * t)
    (S.ringMap_u i) (dvd_mul_of_dvd_left (S.divides_prefix i) t)
    (S.scale_ne_zero i) (S.factor_ne_zero i)

theorem finishedIso_hom_structure (i : S.I) :
    (finishedIso S i).hom = affineBlowupStructure (finishedIdeal S i) :=
  MonomialBlowupTowerAlgebra.finishedBlowupIso_hom_structure _ _ _ _ _ _ _

def continuationIso : affineBlowup (continuationIdeal S) ≅ affineBlowup (centerIdeal t b.prod) :=
  MonomialBlowupTowerAlgebra.continuationBlowupIso S.continuationRingMap P t
    S.continuationRingMap_u S.prefix_ne_zero S.remaining_ne_zero

@[reassoc]
theorem continuationIso_hom_structure :
    (continuationIso S).hom ≫ affineBlowupStructure (centerIdeal t b.prod) =
      affineBlowupStructure (continuationIdeal S) :=
  MonomialBlowupTowerAlgebra.continuationBlowupIso_hom_structure _ _ _ _ _ _

def oldInclusion (hprefix : (l.take (n + 1)).prod = P * t) (i : S.I) :
    Spec (CommRingCat.of (Node A (S.factor i))) ⟶ blowup (center (l := l) (n := n)) :=
  (finishedIso S i).inv ≫ finishedGlobalMap S hprefix i

instance oldInclusion_open (hprefix : (l.take (n + 1)).prod = P * t) (i : S.I) :
    IsOpenImmersion (oldInclusion S hprefix i) := by
  dsimp only [oldInclusion]
  infer_instance

@[reassoc]
theorem oldInclusion_structure (hprefix : (l.take (n + 1)).prod = P * t) (i : S.I) :
    oldInclusion S hprefix i ≫ blowupStructure (center (l := l) (n := n)) = S.inclusion i := by
  rw [oldInclusion, Category.assoc, finishedGlobalMap_structure, ← finishedIso_hom_structure S i]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem oldInclusion_opensRange (hprefix : (l.take (n + 1)).prod = P * t) (i : S.I) :
    (oldInclusion S hprefix i).opensRange =
      blowupStructure (center (l := l) (n := n)) ⁻¹ᵁ (S.inclusion i).opensRange := by
  let : IsOpenImmersion (S.inclusion i) := S.inclusion_open i
  change ((finishedIso S i).inv ≫ finishedGlobalMap S hprefix i).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact BlowupOpenChart.chartMap_opensRange _ _ _ (finished_comap S hprefix i)

omit [IsDomain A] in
theorem continuationGlobalMap_opensRange (hprefix : (l.take (n + 1)).prod = P * t) :
    (continuationGlobalMap S hprefix).opensRange =
      blowupStructure (center (l := l) (n := n)) ⁻¹ᵁ S.continuationInclusion.opensRange := by
  let : IsOpenImmersion S.continuationInclusion := S.continuation_open
  exact BlowupOpenChart.chartMap_opensRange _ _ _ (continuation_comap S hprefix)

variable [Fact (t ≠ 0)] [Fact (b.prod ≠ 0)]

def freshInclusion (hprefix : (l.take (n + 1)).prod = P * t) :
    Spec (CommRingCat.of (Node A t)) ⟶ blowup (center (l := l) (n := n)) :=
  uChartInclusion t b.prod ≫ (continuationIso S).inv ≫ continuationGlobalMap S hprefix

def nextInclusion (hprefix : (l.take (n + 1)).prod = P * t) :
    Spec (CommRingCat.of (Node A b.prod)) ⟶ blowup (center (l := l) (n := n)) :=
  MonomialBlowupIteration.continuationChartInclusion t b.prod ≫
    (continuationIso S).inv ≫ continuationGlobalMap S hprefix

instance freshInclusion_open (hprefix : (l.take (n + 1)).prod = P * t) :
    IsOpenImmersion (freshInclusion S hprefix) := by
  dsimp only [freshInclusion]
  infer_instance

instance nextInclusion_open (hprefix : (l.take (n + 1)).prod = P * t) :
    IsOpenImmersion (nextInclusion S hprefix) := by
  dsimp only [nextInclusion]
  infer_instance

@[reassoc]
theorem freshInclusion_structure (hprefix : (l.take (n + 1)).prod = P * t) :
    freshInclusion S hprefix ≫ blowupStructure (center (l := l) (n := n)) =
      Spec.map (CommRingCat.ofHom (uChartOriginalMap t b.prod).toRingHom) ≫ S.continuationInclusion := by
  rw [freshInclusion, Category.assoc, Category.assoc, continuationGlobalMap_structure,
    ← continuationIso_hom_structure S]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, uChartInclusion_structure]

@[reassoc]
theorem nextInclusion_structure (hprefix : (l.take (n + 1)).prod = P * t) :
    nextInclusion S hprefix ≫ blowupStructure (center (l := l) (n := n)) =
      Spec.map (CommRingCat.ofHom (continuationMap t b.prod).toRingHom) ≫ S.continuationInclusion := by
  rw [nextInclusion, Category.assoc, Category.assoc, continuationGlobalMap_structure,
    ← continuationIso_hom_structure S]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, MonomialBlowupIteration.continuationChartInclusion_structure]

end Hironaka.Geometry.MonomialBlowupTowerCharts.StepContext
