import Hironaka.Geometry.NodeFamilyTowerLocality
import Hironaka.Geometry.MonomialBlowupTowerRegular

/-!
# Genuine family preservation on the actual global finite node tower

The actual cover and its coefficient triangles are constructed internally from
the nonzero coefficient list. No flatness or geometric-fibre certificates are inputs.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.NodeFamilyTower

open Algebra.NodeBlowupChart NodeFamilyFlat NodeFamilyFibres
open MonomialBlowupTower MonomialBlowupTowerCharts MonomialBlowupTowerRegular

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A]

/-- The literal original coefficient morphism of the actual global blowup stage. -/
def familyMorphism (l : List A) (n : ℕ) : (tower l n).left ⟶ Spec (CommRingCat.of A) :=
  (tower l n).hom ≫ nodeMorphism l.prod

/-- Actual node algebra chart maps retain the original literal coefficient morphism. -/
theorem chart_coefficient_triangle {l : List A} {n : ℕ} {q : A}
    (F : Node A l.prod →ₐ[A] Node A q)
    (f : Spec (CommRingCat.of (Node A q)) ⟶ (tower l n).left)
    (hf : f ≫ (tower l n).hom = Spec.map (CommRingCat.ofHom F.toRingHom)) :
    f ≫ familyMorphism l n = nodeMorphism q := by
  rw [familyMorphism, ← Category.assoc, hf, nodeMorphism, nodeMorphism, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext F.commutes

private theorem chart_family_properties {l : List A} {n : ℕ} {P q : A}
    (S : ChartData l n P q) (i : Option S.I) :
    Flat (S.map i ≫ familyMorphism l n) ∧
      LocallyOfFinitePresentation (S.map i ≫ familyMorphism l n) ∧
      GeometricallyReduced (S.map i ≫ familyMorphism l n) := by
  cases i with
  | none =>
    change Flat (S.continuationInclusion ≫ familyMorphism l n) ∧
      LocallyOfFinitePresentation (S.continuationInclusion ≫ familyMorphism l n) ∧
      GeometricallyReduced (S.continuationInclusion ≫ familyMorphism l n)
    rw [chart_coefficient_triangle S.continuationRingMap S.continuationInclusion S.continuation_structure]
    exact ⟨nodeMorphism_flat q, nodeMorphism_locallyOfFinitePresentation q,
      nodeMorphism_geometricallyReduced q⟩
  | some i =>
    change Flat (S.inclusion i ≫ familyMorphism l n) ∧
      LocallyOfFinitePresentation (S.inclusion i ≫ familyMorphism l n) ∧
      GeometricallyReduced (S.inclusion i ≫ familyMorphism l n)
    rw [chart_coefficient_triangle (S.ringMap i) (S.inclusion i) (S.inclusion_structure i)]
    exact ⟨nodeMorphism_flat (S.factor i), nodeMorphism_locallyOfFinitePresentation (S.factor i),
      nodeMorphism_geometricallyReduced (S.factor i)⟩

private theorem family_properties_of_charts {l : List A} {n : ℕ} {P q : A}
    (S : ChartData l n P q) :
    Flat (familyMorphism l n) ∧ LocallyOfFinitePresentation (familyMorphism l n) ∧
      GeometricallyReduced (familyMorphism l n) := by
  refine ⟨?_, ?_, ?_⟩
  · apply (IsZariskiLocalAtSource.iff_of_openCover S.openCover).mpr
    intro i
    change Option S.I at i
    exact (chart_family_properties S i).1
  · apply (IsZariskiLocalAtSource.iff_of_openCover S.openCover).mpr
    intro i
    change Option S.I at i
    exact (chart_family_properties S i).2.1
  · apply NodeFamilyTowerLocality.geometricallyReduced_of_openCover _ S.openCover
    intro i
    change Option S.I at i
    exact (chart_family_properties S i).2.2

variable [IsDomain A]

/-- Every actual processed finite prefix retains genuine flat, locally finitely presented,
geometrically reduced family structure over the original coefficient base. -/
theorem prefix_family_properties (l : List A) (hl : (0 : A) ∉ l)
    (a b : List A) (hab : l = a ++ b) :
    Flat (familyMorphism l a.length) ∧ LocallyOfFinitePresentation (familyMorphism l a.length) ∧
      GeometricallyReduced (familyMorphism l a.length) := by
  obtain ⟨S⟩ := nonempty_charts l hl a b hab
  exact family_properties_of_charts S

/-- The actual final global original-prefix blowup is a genuine flat family over its original base. -/
theorem final_family_properties (l : List A) (hl : (0 : A) ∉ l) :
    Flat (resolutionMorphism l ≫ nodeMorphism l.prod) ∧
      LocallyOfFinitePresentation (resolutionMorphism l ≫ nodeMorphism l.prod) ∧
      GeometricallyReduced (resolutionMorphism l ≫ nodeMorphism l.prod) :=
  prefix_family_properties l hl l [] (by simp)

variable [IsNoetherianRing A]

/-- Every actual tower family morphism is quasi-compact over a Noetherian coefficient base. -/
theorem familyMorphism_quasiCompact (l : List A) (hl : (0 : A) ∉ l) (n : ℕ) :
    QuasiCompact (familyMorphism l n) := by
  let : IsAlteration (tower l n).hom := tower_isAlteration l hl n
  let : QuasiCompact (nodeMorphism l.prod) := nodeMorphism_quasiCompact l.prod
  dsimp only [familyMorphism]
  infer_instance

/-- Native finite presentation, flatness and geometric reducedness of the actual final family. -/
theorem final_family_finitelyPresented (l : List A) (hl : (0 : A) ∉ l) :
    Flat (resolutionMorphism l ≫ nodeMorphism l.prod) ∧
      LocallyOfFinitePresentation (resolutionMorphism l ≫ nodeMorphism l.prod) ∧
      QuasiCompact (resolutionMorphism l ≫ nodeMorphism l.prod) ∧
      GeometricallyReduced (resolutionMorphism l ≫ nodeMorphism l.prod) := by
  obtain ⟨hflat, hfp, hred⟩ := final_family_properties l hl
  exact ⟨hflat, hfp, familyMorphism_quasiCompact l hl l.length, hred⟩

end Hironaka.Geometry.NodeFamilyTower
