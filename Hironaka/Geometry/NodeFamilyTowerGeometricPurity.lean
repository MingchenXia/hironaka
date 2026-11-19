import Hironaka.Geometry.NodeFamilyGeometricPurity
import Hironaka.Geometry.NodeFamilyTower
import Hironaka.Geometry.NodeFamilyTowerDimension

/-! Geometric purity of the actual global finite node tower, via actual field-basechange covers. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.NodeFamilyTowerGeometricPurity

open NodeFamilyTower NodeFamilyGeometricPurity NodeFamilyFlat
open MonomialBlowupTower MonomialBlowupTowerCharts MonomialBlowupTowerRegular

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pasting actual pullback squares gives the genuine base-change chart isomorphism. -/
def chartBaseChangeIso {X U S T : Scheme.{u}} (f : U ⟶ X) (g : X ⟶ S) (b : T ⟶ S) :
    pullback (pullback.fst g b) f ≅ pullback (f ≫ g) b :=
  ((IsPullback.of_hasPullback (pullback.fst g b) f).flip.paste_vert
    (IsPullback.of_hasPullback g b)).isoPullback

/-- No actual source open singleton can exist when a genuine cover has none. -/
theorem not_isOpen_singleton_of_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover.{v})
    (h : ∀ i (x : 𝒰.X i), ¬ IsOpen ({x} : Set (𝒰.X i))) (x : X) :
    ¬ IsOpen ({x} : Set X) := by
  intro hx
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  apply h i y
  have heq : (𝒰.f i) ⁻¹' ({𝒰.f i y} : Set X) = {y} := by
    ext z
    exact ⟨fun hz => Set.mem_singleton_iff.mpr
      ((𝒰.f i).isOpenEmbedding.injective (Set.mem_singleton_iff.mp hz)),
      fun hz => Set.mem_singleton_iff.mpr (congrArg (𝒰.f i) (Set.mem_singleton_iff.mp hz))⟩
  rw [← heq]
  exact hx.preimage (𝒰.f i).continuous

variable {A : Type u} [CommRing A] (K : Type u) [Field K] [Algebra A K]

/-- The actual field base change of the original global family morphism. -/
abbrev fieldBaseChange (l : List A) (n : ℕ) : Scheme.{u} :=
  pullback (familyMorphism l n) (Spec.map (CommRingCat.ofHom (algebraMap A K)))

private theorem chart_basechange_dimension {l : List A} {n : ℕ} {P q : A}
    (C : ChartData l n P q) (i : Option C.I) :
    topologicalKrullDim ((C.openCover.pullback₁
      (pullback.fst (familyMorphism l n) (Spec.map (CommRingCat.ofHom (algebraMap A K))))).X i) = 1 := by
  change topologicalKrullDim (pullback
    (pullback.fst (familyMorphism l n) (Spec.map (CommRingCat.ofHom (algebraMap A K))))
    (C.map i) : Scheme.{u}) = 1
  rw [IsHomeomorph.topologicalKrullDim_eq _
    (chartBaseChangeIso (C.map i) (familyMorphism l n)
      (Spec.map (CommRingCat.ofHom (algebraMap A K)))).hom.homeomorph.isHomeomorph]
  cases i with
  | none =>
    change topologicalKrullDim (pullback (C.continuationInclusion ≫ familyMorphism l n)
      (Spec.map (CommRingCat.ofHom (algebraMap A K))) : Scheme.{u}) = 1
    rw [chart_coefficient_triangle C.continuationRingMap C.continuationInclusion C.continuation_structure]
    exact nodeFieldBaseChange_dimension K q
  | some i =>
    change topologicalKrullDim (pullback (C.inclusion i ≫ familyMorphism l n)
      (Spec.map (CommRingCat.ofHom (algebraMap A K))) : Scheme.{u}) = 1
    rw [chart_coefficient_triangle (C.ringMap i) (C.inclusion i) (C.inclusion_structure i)]
    exact nodeFieldBaseChange_dimension K (C.factor i)

private def hasNoOpenSingletons (Y : Scheme.{u}) : Prop :=
  ∀ y : Y, ¬ IsOpen ({y} : Set Y)

private theorem chart_basechange_no_open_singleton {l : List A} {n : ℕ} {P q : A}
    (C : ChartData l n P q) (i : Option C.I)
    (x : (C.openCover.pullback₁
      (pullback.fst (familyMorphism l n) (Spec.map (CommRingCat.ofHom (algebraMap A K))))).X i) :
    ¬ IsOpen ({x} : Set ((C.openCover.pullback₁
      (pullback.fst (familyMorphism l n) (Spec.map (CommRingCat.ofHom (algebraMap A K))))).X i)) := by
  let e := chartBaseChangeIso (C.map i) (familyMorphism l n)
    (Spec.map (CommRingCat.ofHom (algebraMap A K)))
  intro hx
  have ho := e.hom.homeomorph.isOpenMap _ hx
  rw [Set.image_singleton] at ho
  have hn : hasNoOpenSingletons (pullback (C.map i ≫ familyMorphism l n)
      (Spec.map (CommRingCat.ofHom (algebraMap A K)))) := by
    cases i with
    | none =>
      change hasNoOpenSingletons (pullback (C.continuationInclusion ≫ familyMorphism l n)
        (Spec.map (CommRingCat.ofHom (algebraMap A K))))
      rw [chart_coefficient_triangle C.continuationRingMap C.continuationInclusion C.continuation_structure]
      exact nodeFieldBaseChange_not_isOpen_singleton K q
    | some i =>
      change hasNoOpenSingletons (pullback (C.inclusion i ≫ familyMorphism l n)
        (Spec.map (CommRingCat.ofHom (algebraMap A K))))
      rw [chart_coefficient_triangle (C.ringMap i) (C.inclusion i) (C.inclusion_structure i)]
      exact nodeFieldBaseChange_not_isOpen_singleton K (C.factor i)
  exact hn (e.hom x) ho

private theorem basechange_properties_of_charts {l : List A} {n : ℕ} {P q : A}
    (C : ChartData l n P q) :
    topologicalKrullDim (fieldBaseChange K l n) = 1 ∧
      ∀ x : fieldBaseChange K l n, ¬ IsOpen ({x} : Set (fieldBaseChange K l n)) := by
  let 𝒰 := C.openCover.pullback₁
    (pullback.fst (familyMorphism l n) (Spec.map (CommRingCat.ofHom (algebraMap A K))))
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · apply FunctionFieldDimension.topologicalKrullDim_le_of_openCover _ 1 𝒰
    intro i
    change Option C.I at i
    exact (chart_basechange_dimension K C i).le
  · have hle := (𝒰.f (none : Option C.I)).isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    exact (chart_basechange_dimension K C none).symm.le.trans hle
  · apply not_isOpen_singleton_of_openCover 𝒰
    intro i x
    change Option C.I at i
    exact chart_basechange_no_open_singleton K C i x

variable [IsDomain A]

/-- Actual field base changes of every processed stage have dimension one and no isolated open point. -/
theorem prefix_fieldBaseChange_properties (l : List A) (hl : (0 : A) ∉ l)
    (a b : List A) (hab : l = a ++ b) :
    topologicalKrullDim (fieldBaseChange K l a.length) = 1 ∧
      ∀ x : fieldBaseChange K l a.length,
        ¬ IsOpen ({x} : Set (fieldBaseChange K l a.length)) := by
  obtain ⟨C⟩ := nonempty_charts l hl a b hab
  exact basechange_properties_of_charts K C

/-- The actual pullback after every field base change is reduced, from the genuine family property. -/
theorem prefix_fieldBaseChange_isReduced (l : List A) (hl : (0 : A) ∉ l)
    (a b : List A) (hab : l = a ++ b) : IsReduced (fieldBaseChange K l a.length) := by
  let : GeometricallyReduced (familyMorphism l a.length) :=
    (prefix_family_properties l hl a b hab).2.2
  exact GeometricallyReduced.geometrically_isReduced
    (Spec.map (CommRingCat.ofHom (algebraMap A K))) _ _
    (IsPullback.of_hasPullback (familyMorphism l a.length)
      (Spec.map (CommRingCat.ofHom (algebraMap A K))))

variable [IsNoetherianRing A]

/-- Every actual component after every field base change of the actual processed tower has dimension one. -/
theorem prefix_fieldBaseChange_component_dimension (l : List A) (hl : (0 : A) ∉ l)
    (a b : List A) (hab : l = a ++ b) (Z : Set (fieldBaseChange K l a.length))
    (hZ : Z ∈ irreducibleComponents (fieldBaseChange K l a.length)) :
    topologicalKrullDim Z = 1 := by
  let : LocallyOfFinitePresentation (familyMorphism l a.length) :=
    (prefix_family_properties l hl a b hab).2.1
  let : QuasiCompact (familyMorphism l a.length) := familyMorphism_quasiCompact l hl a.length
  let s := Spec.map (CommRingCat.ofHom (algebraMap A K))
  let : IsLocallyNoetherian (fieldBaseChange K l a.length) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (familyMorphism l a.length) s)
  let : IsNoetherian (fieldBaseChange K l a.length) := ⟨⟩
  obtain ⟨hdim, hno⟩ := prefix_fieldBaseChange_properties K l hl a b hab
  exact le_antisymm ((topologicalKrullDim_subspace_le _ Z).trans hdim.le)
    (one_le_component_dimension_of_no_open_singletons _ hno Z hZ)

/-- Every actual irreducible component of every field base change of the final tower is one dimensional. -/
theorem final_fieldBaseChange_component_dimension (l : List A) (hl : (0 : A) ∉ l)
    (Z : Set (fieldBaseChange K l l.length))
    (hZ : Z ∈ irreducibleComponents (fieldBaseChange K l l.length)) :
    topologicalKrullDim Z = 1 :=
  prefix_fieldBaseChange_component_dimension K l hl l [] (by simp) Z hZ

/-- The actual final family has reduced, pure one-dimensional geometric fibres over every field. -/
theorem final_fieldBaseChange_reduced_pure_curve (l : List A) (hl : (0 : A) ∉ l) :
    IsReduced (fieldBaseChange K l l.length) ∧
      topologicalKrullDim (fieldBaseChange K l l.length) = 1 ∧
      ∀ Z : Set (fieldBaseChange K l l.length),
        Z ∈ irreducibleComponents (fieldBaseChange K l l.length) → topologicalKrullDim Z = 1 :=
  ⟨prefix_fieldBaseChange_isReduced K l hl l [] (by simp),
    (prefix_fieldBaseChange_properties K l hl l [] (by simp)).1,
    fun Z hZ => final_fieldBaseChange_component_dimension K l hl Z hZ⟩

omit [Algebra A K] in
/-- Every genuine geometric fibre of the final tower is a reduced pure one-dimensional scheme. -/
theorem final_geometricFiber_reduced_pure_curve (l : List A) (hl : (0 : A) ∉ l)
    (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A)) :
    let Y : Scheme.{u} := pullback (familyMorphism l l.length) y
    IsReduced Y ∧ topologicalKrullDim Y = 1 ∧
      ∀ Z : Set Y, Z ∈ irreducibleComponents Y → topologicalKrullDim Z = 1 := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  let : Algebra A K := φ.hom.toAlgebra
  exact final_fieldBaseChange_reduced_pure_curve K l hl

end Hironaka.Geometry.NodeFamilyTowerGeometricPurity
