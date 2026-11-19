import Hironaka.Geometry.ProperSteinProjectiveCechSheafSections

/-!
# Actual normalized Cech comparison from original nonempty intersections

Generic native-only adaptation from same-workspace
`BingWangEntropy/NonemptySubsetCechComparison.lean`,
SHA256 e042df7571d2d29bc6495cc405240ff4c8e23432e28b57aa03d00b589d812067.
The later represented-sections output-premise interface is not imported.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K I : Type u} [CommRing K] [LinearOrder I]

/-- The genuine inclusion of the poset of nonempty finite subsets. -/
def nonemptySubsetInclusion (I : Type u) [LinearOrder I] :
    {S : Finset I // S.Nonempty} ⥤ Finset I where
  obj S := S.val
  map h := homOfLE (leOfHom h)

/-- Restrict the actual intersection diagram to its nonempty intersections. -/
def nonemptySubsetDiagram (F : Finset I ⥤ ModuleCat.{u} K) :
    {S : Finset I // S.Nonempty} ⥤ ModuleCat.{u} K :=
  nonemptySubsetInclusion I ⋙ F

/-- A true nonempty-diagram map acts on cube values, assigning zero to the empty subset. -/
def nonemptySubsetCechCubeMap {F G : Finset I ⥤ ModuleCat.{u} K}
    (α : nonemptySubsetDiagram F ⟶ nonemptySubsetDiagram G) :
    subsetCechCube F →ₗ[K] subsetCechCube G where
  toFun c S := if h : S.Nonempty then α.app ⟨S, h⟩ (c S) else 0
  map_add' c d := by
    funext S
    by_cases h : S.Nonempty
    · simp only [dif_pos h, Pi.add_apply, map_add]
    · simp only [dif_neg h, Pi.add_apply, add_zero]
  map_smul' r c := by
    funext S
    by_cases h : S.Nonempty
    · simp only [dif_pos h, Pi.smul_apply, map_smul, RingHom.id_apply]
    · simp only [dif_neg h, Pi.smul_apply, smul_zero]

/-- The actual nonempty map preserves every cardinal piece. -/
def nonemptySubsetCechCardMap {F G : Finset I ⥤ ModuleCat.{u} K}
    (α : nonemptySubsetDiagram F ⟶ nonemptySubsetDiagram G) (n : ℕ) :
    subsetCechCardPiece F n →ₗ[K] subsetCechCardPiece G n :=
  ((nonemptySubsetCechCubeMap α).comp (subsetCechCardPiece F n).subtype).codRestrict
    (subsetCechCardPiece G n) (by
      intro c S hS
      change (if h : S.Nonempty then α.app ⟨S, h⟩ (c.val S) else (0 : G.obj S)) =
        (0 : G.obj S)
      rw [c.property S hS]
      split <;> simp only [map_zero])

/-- Naturality on genuine nonempty faces commutes with the positive-cardinality differential. -/
theorem nonemptySubsetCechCubeMap_comm {F G : Finset I ⥤ ModuleCat.{u} K}
    (α : nonemptySubsetDiagram F ⟶ nonemptySubsetDiagram G) (p : ℕ)
    (c : subsetCechCardPiece F (p + 1)) :
    nonemptySubsetCechCubeMap α (subsetCechDifferential F c.val) =
      subsetCechDifferential G (nonemptySubsetCechCubeMap α c.val) := by
  funext S
  by_cases hS : S.Nonempty
  · change (if h : S.Nonempty then α.app ⟨S, h⟩
        (subsetCechDifferential F c.val S) else (0 : G.obj S)) = _
    rw [dif_pos hS]
    change (α.app ⟨S, hS⟩).hom (∑ i ∈ S, _) = ∑ i ∈ S, _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul]
    by_cases hSi : (S.erase i).Nonempty
    · change subsetCechSign S i •
          (α.app ⟨S, hS⟩).hom (subsetCechRestriction F _ (c.val (S.erase i))) =
        subsetCechSign S i • subsetCechRestriction G _
          (if h : (S.erase i).Nonempty then α.app ⟨S.erase i, h⟩ (c.val (S.erase i)) else 0)
      rw [dif_pos hSi]
      congr 1
      exact ConcreteCategory.congr_hom
        (α.naturality (homOfLE (Finset.erase_subset i S) :
          (⟨S.erase i, hSi⟩ : {T : Finset I // T.Nonempty}) ⟶ ⟨S, hS⟩))
        (c.val (S.erase i))
    · have hzero : c.val (S.erase i) = 0 := c.property _ (by
        rw [Finset.not_nonempty_iff_eq_empty.mp hSi, Finset.card_empty]
        omega)
      change subsetCechSign S i •
          (α.app ⟨S, hS⟩).hom (subsetCechRestriction F _ (c.val (S.erase i))) =
        subsetCechSign S i • subsetCechRestriction G _
          (if h : (S.erase i).Nonempty then α.app ⟨S.erase i, h⟩ (c.val (S.erase i)) else 0)
      rw [dif_neg hSi, hzero, map_zero, map_zero, map_zero]
  · have hE : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [nonemptySubsetCechCubeMap, subsetCechDifferential_apply]

/-- A genuine nonempty-diagram morphism induces a native normalized Čech morphism. -/
def nonemptySubsetCechComplexMap {F G : Finset I ⥤ ModuleCat.{u} K}
    (α : nonemptySubsetDiagram F ⟶ nonemptySubsetDiagram G) :
    subsetCechComplex F ⟶ subsetCechComplex G :=
  CochainComplex.ofHom
    (fun p => ModuleCat.ofHom (nonemptySubsetCechCardMap α (p + 1))) (by
      intro p
      simp only [subsetCechComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply Subtype.ext
      exact (nonemptySubsetCechCubeMap_comm α p c).symm)

/-- Actual inverse nonempty maps are inverse on every positive cardinal term. -/
theorem nonemptySubsetCechCardMap_inverse {F G : Finset I ⥤ ModuleCat.{u} K}
    (e : nonemptySubsetDiagram F ≅ nonemptySubsetDiagram G) (p : ℕ)
    (c : subsetCechCardPiece F (p + 1)) :
    nonemptySubsetCechCardMap e.inv (p + 1)
      (nonemptySubsetCechCardMap e.hom (p + 1) c) = c := by
  apply Subtype.ext
  funext S
  by_cases hS : S.Nonempty
  · change (if h : S.Nonempty then e.inv.app ⟨S, h⟩
        (if h' : S.Nonempty then e.hom.app ⟨S, h'⟩ (c.val S) else 0) else 0) = c.val S
    simp only [dif_pos hS]
    exact Iso.hom_inv_id_apply (e.app ⟨S, hS⟩) (c.val S)
  · have hE : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change (if h : S.Nonempty then _ else 0) = c.val S
    rw [dif_neg hS, c.property S (by rw [hE, Finset.card_empty]; omega)]

/-- The genuine native Čech complexes are isomorphic using only nonempty intersections. -/
def nonemptySubsetCechComplexIso {F G : Finset I ⥤ ModuleCat.{u} K}
    (e : nonemptySubsetDiagram F ≅ nonemptySubsetDiagram G) :
    subsetCechComplex F ≅ subsetCechComplex G where
  hom := nonemptySubsetCechComplexMap e.hom
  inv := nonemptySubsetCechComplexMap e.inv
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact nonemptySubsetCechCardMap_inverse e p c
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact nonemptySubsetCechCardMap_inverse e.symm p c

/-- Native homology transports through the actual comparison without any empty term. -/
def nonemptySubsetCechHomologyIso {F G : Finset I ⥤ ModuleCat.{u} K}
    (e : nonemptySubsetDiagram F ≅ nonemptySubsetDiagram G) (p : ℕ) :
    (subsetCechComplex F).homology p ≅ (subsetCechComplex G).homology p :=
  HomologicalComplex.homologyMapIso (nonemptySubsetCechComplexIso e) p

end

end Hironaka.Geometry.ProperSteinProjectiveCech
