import Hironaka.Geometry.NodeFamilySmoothDensityPullback
import Hironaka.Geometry.NodeFamilyTowerSmoothDensity

/-! Fibrewise density of the original actual tower-family relative smooth locus. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.NodeFamilyTowerSmoothDensityPullback

open Algebra.NodeBlowupChart NodeFamilyFlat NodeFamilyTower NodeFamilyGeometricPurity
open NodeFamilySmoothDensityBaseChange NodeFamilySmoothDensityPullback NodeFamilySmoothDensityLocality
open NodeFamilyTowerGeometricPurity
open MonomialBlowupTower MonomialBlowupTowerCharts MonomialBlowupTowerRegular

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original relative smooth locus has dense inverse image on each genuine field-basechanged node chart. -/
theorem fieldBaseChange_nodeChart_original_smooth_preimage_dense {A : Type u} [CommRing A]
    (K : Type u) [Field K] [Algebra A K] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFinitePresentation g]
    (q : A) (f : Spec (CommRingCat.of (Node A q)) ⟶ X) [IsOpenImmersion f]
    (hf : f ≫ g = nodeMorphism q) :
    Dense ((pullback.fst (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap A K)))) f) ⁻¹'
      ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap A K)))) ⁻¹'
        (g.smoothLocus : Set X))) := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap A K))
  let : LocallyOfFinitePresentation (nodeMorphism q) := nodeMorphism_locallyOfFinitePresentation q
  have hpb : IsPullback (pullback.snd (pullback.fst g s) f)
      (pullback.fst (pullback.fst g s) f ≫ pullback.snd g s) (nodeMorphism q) s := by
    rw [← hf]
    exact (IsPullback.of_hasPullback (pullback.fst g s) f).flip.paste_vert
      (IsPullback.of_hasPullback g s)
  have hloc : f ⁻¹ᵁ g.smoothLocus = (nodeMorphism q).smoothLocus :=
    (Scheme.Hom.preimage_smoothLocus_eq f g).trans (smoothLocus_eq_of_eq _ _ hf)
  have heq : hpb.isoPullback.hom ⁻¹ᵁ
      (pullback.fst (nodeMorphism q) s) ⁻¹ᵁ (nodeMorphism q).smoothLocus =
      (pullback.fst (pullback.fst g s) f) ⁻¹ᵁ (pullback.fst g s) ⁻¹ᵁ g.smoothLocus := by
    rw [← Scheme.Hom.comp_preimage, hpb.isoPullback_hom_fst, ← hloc,
      ← Scheme.Hom.comp_preimage]
    rw [show pullback.snd (pullback.fst g s) f ≫ f =
      pullback.fst (pullback.fst g s) f ≫ pullback.fst g s from pullback.condition.symm]
    rw [Scheme.Hom.comp_preimage]
  have hd := (original_smoothLocus_preimage_dense K q).preimage
    hpb.isoPullback.hom.isOpenEmbedding.isOpenMap
  change Dense ((hpb.isoPullback.hom ⁻¹ᵁ
    (pullback.fst (nodeMorphism q) s) ⁻¹ᵁ (nodeMorphism q).smoothLocus) :
    Set (pullback (pullback.fst g s) f : Scheme.{u})) at hd
  rw [heq] at hd
  exact hd

variable {A : Type u} [CommRing A] (K : Type u) [Field K] [Algebra A K]

private theorem original_smooth_preimage_dense_of_charts {l : List A} {n : ℕ} {P q : A}
    [LocallyOfFinitePresentation (familyMorphism l n)] (C : ChartData l n P q) :
    Dense ((pullback.fst (familyMorphism l n) (Spec.map (CommRingCat.ofHom (algebraMap A K)))) ⁻¹'
      ((familyMorphism l n).smoothLocus : Set (tower l n).left)) := by
  apply dense_of_openCover (C.openCover.pullback₁
    (pullback.fst (familyMorphism l n) (Spec.map (CommRingCat.ofHom (algebraMap A K)))))
  intro i
  change Option C.I at i
  cases i with
  | none =>
    let : IsOpenImmersion C.continuationInclusion := C.continuation_open
    exact fieldBaseChange_nodeChart_original_smooth_preimage_dense K (familyMorphism l n) q
      C.continuationInclusion
      (chart_coefficient_triangle C.continuationRingMap C.continuationInclusion C.continuation_structure)
  | some i =>
    let : IsOpenImmersion (C.inclusion i) := C.inclusion_open i
    exact fieldBaseChange_nodeChart_original_smooth_preimage_dense K (familyMorphism l n) (C.factor i)
      (C.inclusion i)
      (chart_coefficient_triangle (C.ringMap i) (C.inclusion i) (C.inclusion_structure i))

variable [IsDomain A]

/-- Every actual processed-stage original relative smooth locus is dense after every field coefficient extension. -/
theorem prefix_original_smoothLocus_preimage_dense (l : List A) (hl : (0 : A) ∉ l)
    (a b : List A) (hab : l = a ++ b) :
    letI : LocallyOfFinitePresentation (familyMorphism l a.length) :=
      (prefix_family_properties l hl a b hab).2.1
    Dense ((pullback.fst (familyMorphism l a.length) (Spec.map (CommRingCat.ofHom (algebraMap A K)))) ⁻¹'
      ((familyMorphism l a.length).smoothLocus : Set (tower l a.length).left)) := by
  let : LocallyOfFinitePresentation (familyMorphism l a.length) :=
    (prefix_family_properties l hl a b hab).2.1
  obtain ⟨C⟩ := nonempty_charts l hl a b hab
  exact original_smooth_preimage_dense_of_charts K C

omit [Algebra A K] in
/-- The original actual final relative smooth locus has dense inverse image after every genuine field point. -/
theorem final_geometricFiber_original_smoothLocus_preimage_dense (l : List A) (hl : (0 : A) ∉ l)
    (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A)) :
    letI : LocallyOfFinitePresentation (familyMorphism l l.length) :=
      (final_family_properties l hl).2.1
    Dense ((pullback.fst (familyMorphism l l.length) y) ⁻¹'
      ((familyMorphism l l.length).smoothLocus : Set (tower l l.length).left)) := by
  let : LocallyOfFinitePresentation (familyMorphism l l.length) :=
    (final_family_properties l hl).2.1
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  let : Algebra A K := φ.hom.toAlgebra
  exact prefix_original_smoothLocus_preimage_dense K l hl l [] (by simp)

/-- The original final relative smooth locus is dense in every actual native scheme-theoretic fibre. -/
theorem final_fiber_original_smoothLocus_preimage_dense (l : List A) (hl : (0 : A) ∉ l)
    (p : Spec (CommRingCat.of A)) :
    letI : LocallyOfFinitePresentation (familyMorphism l l.length) :=
      (final_family_properties l hl).2.1
    Dense (((familyMorphism l l.length).fiberι p) ⁻¹'
      ((familyMorphism l l.length).smoothLocus : Set (tower l l.length).left)) := by
  let : LocallyOfFinitePresentation (familyMorphism l l.length) :=
    (final_family_properties l hl).2.1
  exact final_geometricFiber_original_smoothLocus_preimage_dense
    ((Spec (CommRingCat.of A)).residueField p) l hl
    ((Spec (CommRingCat.of A)).fromSpecResidueField p)

end Hironaka.Geometry.NodeFamilyTowerSmoothDensityPullback
