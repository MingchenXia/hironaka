import Hironaka.Geometry.NodeFamilySmoothDensityLocality
import Hironaka.Geometry.NodeFamilyTowerGeometricPurity

/-! Dense actual relative smooth loci of the genuine field-basechanged finite node towers. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.NodeFamilyTowerSmoothDensity

open NodeFamilyFlat NodeFamilyTower NodeFamilyTowerGeometricPurity
open NodeFamilySmoothDensityLocality
open MonomialBlowupTower MonomialBlowupTowerCharts MonomialBlowupTowerRegular

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] (K : Type u) [Field K] [Algebra A K]

/-- The actual field projection of the actual tower-family base change. -/
def fieldBaseChangeFamilyMorphism (l : List A) (n : ℕ) :
    fieldBaseChange K l n ⟶ Spec (CommRingCat.of K) :=
  pullback.snd (familyMorphism l n) (Spec.map (CommRingCat.ofHom (algebraMap A K)))

instance fieldBaseChangeFamilyMorphism_locallyOfFinitePresentation (l : List A) (n : ℕ)
    [LocallyOfFinitePresentation (familyMorphism l n)] :
    LocallyOfFinitePresentation (fieldBaseChangeFamilyMorphism K l n) := by
  dsimp only [fieldBaseChangeFamilyMorphism]
  infer_instance

private theorem chart_smoothLocus_dense {l : List A} {n : ℕ} {P q : A}
    [LocallyOfFinitePresentation (familyMorphism l n)] (C : ChartData l n P q) (i : Option C.I) :
    Dense ((((C.openCover.pullback₁
      (pullback.fst (familyMorphism l n) (Spec.map (CommRingCat.ofHom (algebraMap A K))))).f i) ≫
        fieldBaseChangeFamilyMorphism K l n).smoothLocus :
      Set ((C.openCover.pullback₁
        (pullback.fst (familyMorphism l n) (Spec.map (CommRingCat.ofHom (algebraMap A K))))).X i)) := by
  cases i with
  | none =>
    let : IsOpenImmersion C.continuationInclusion := C.continuation_open
    exact fieldBaseChange_nodeChart_smoothLocus_dense K (familyMorphism l n) q
      C.continuationInclusion
      (chart_coefficient_triangle C.continuationRingMap C.continuationInclusion C.continuation_structure)
  | some i =>
    let : IsOpenImmersion (C.inclusion i) := C.inclusion_open i
    exact fieldBaseChange_nodeChart_smoothLocus_dense K (familyMorphism l n) (C.factor i)
      (C.inclusion i)
      (chart_coefficient_triangle (C.ringMap i) (C.inclusion i) (C.inclusion_structure i))

private theorem smoothLocus_dense_of_charts {l : List A} {n : ℕ} {P q : A}
    [LocallyOfFinitePresentation (familyMorphism l n)] (C : ChartData l n P q) :
    Dense ((fieldBaseChangeFamilyMorphism K l n).smoothLocus : Set (fieldBaseChange K l n)) := by
  apply smoothLocus_dense_of_openCover _ (C.openCover.pullback₁
    (pullback.fst (familyMorphism l n) (Spec.map (CommRingCat.ofHom (algebraMap A K)))))
  intro i
  change Option C.I at i
  exact chart_smoothLocus_dense K C i

variable [IsDomain A]

/-- Every actual processed-stage family after every field base change has dense native relative smooth locus. -/
theorem prefix_fieldBaseChange_smoothLocus_dense (l : List A) (hl : (0 : A) ∉ l)
    (a b : List A) (hab : l = a ++ b) :
    letI : LocallyOfFinitePresentation (familyMorphism l a.length) :=
      (prefix_family_properties l hl a b hab).2.1
    Dense ((fieldBaseChangeFamilyMorphism K l a.length).smoothLocus :
      Set (fieldBaseChange K l a.length)) := by
  let : LocallyOfFinitePresentation (familyMorphism l a.length) :=
    (prefix_family_properties l hl a b hab).2.1
  obtain ⟨C⟩ := nonempty_charts l hl a b hab
  exact smoothLocus_dense_of_charts K C

omit [Algebra A K] in
/-- After every genuine field-valued point, the actual final family has dense native relative smooth locus. -/
theorem final_geometricFiber_smoothLocus_dense (l : List A) (hl : (0 : A) ∉ l)
    (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A)) :
    letI : LocallyOfFinitePresentation (familyMorphism l l.length) :=
      (final_family_properties l hl).2.1
    Dense ((pullback.snd (familyMorphism l l.length) y).smoothLocus :
      Set (pullback (familyMorphism l l.length) y : Scheme.{u})) := by
  let : LocallyOfFinitePresentation (familyMorphism l l.length) :=
    (final_family_properties l hl).2.1
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  let : Algebra A K := φ.hom.toAlgebra
  exact prefix_fieldBaseChange_smoothLocus_dense K l hl l [] (by simp)

end Hironaka.Geometry.NodeFamilyTowerSmoothDensity
