/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechSubsetDirectSum
import Hironaka.Geometry.ProperSteinProjectiveCechDirectSumHomologyNaturality

/-! # Original degree inclusions in the actual direct-sum complex and homology

Closed native proof pattern adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/ReesCechDegreeInclusions.lean`,
SHA256 e185f9c7682d9a0443e827f05e14192204f99d0b91c377a17d9e5b7706f81661.
The genuine cochain family is arbitrary here; only native Mathlib+own imports.
-/
open CategoryTheory
open scoped DirectSum
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.DirectSumDegreeInclusions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {R : Type u} [CommRing R] (C : ℕ → CochainComplex (ModuleCat.{u} R) ℕ)

/-- Every actual original complex includes as its LITERAL original degree summand in the SAME original sum complex. -/
def complexInclusion (d : ℕ) : C d ⟶ SubsetDirectSum.complexSum C where
  f n := ModuleCat.ofHom (DirectSum.lof R ℕ (fun k => (C k).X n) d)
  comm' n m hnm := by
    have hm : n+1=m := hnm
    subst m
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DirectSum.ext
    intro k
    change (show ⨁ j : ℕ, (C j).X (n+1) from
      ((SubsetDirectSum.complexSum C).d n (n+1)).hom
        (DirectSum.lof R ℕ (fun j => (C j).X n) d x)) k =
      DirectSum.lof R ℕ (fun j => (C j).X (n+1)) d (((C d).d n (n+1)).hom x) k
    rw [SubsetDirectSum.complexSum_d_apply]
    by_cases hk : k=d
    · subst k
      rw [DirectSum.lof_apply, DirectSum.lof_apply]
    · simp only [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hk, map_zero]

/-- The SAME original native short-complex map is exactly the actual literal direct-sum inclusion. -/
theorem shortComplexInclusion (d n : ℕ) :
    (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n).map (complexInclusion C d) ≫
      (SubsetDirectSum.shortComplexIso C n).hom =
    DirectSumHomologyNaturality.inclusion (fun j => (C j).sc n) d := by
  apply ShortComplex.Hom.ext
  · exact (DirectSumHomologyNaturality.inclusion_left (R := R) (fun j => (C j).sc n) d).symm
  · exact (DirectSumHomologyNaturality.inclusion_middle (R := R) (fun j => (C j).sc n) d).symm
  · exact (DirectSumHomologyNaturality.inclusion_right (R := R) (fun j => (C j).sc n) d).symm

private theorem comparison_assoc {D : Type*} [Category D]
    {A B E F : D} (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ E) (t : E ⟶ F) (z : A ⟶ F)
    (h : a ≫ b=c) (hc : c ≫ t=z) : a ≫ b ≫ t=z := by
  rw [← Category.assoc, h, hc]

/-- EVERY actual original homology inclusion is the SAME literal original homology summand inclusion. -/
theorem homologyInclusion (d n : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).map (complexInclusion C d) ≫
      (SubsetDirectSum.complexSumHomologyIso C n).hom =
    ModuleCat.ofHom (DirectSum.lof R ℕ (fun j => (C j).homology n) d) := by
  have h := congrArg (fun a => ShortComplex.homologyMap a) (shortComplexInclusion C d n)
  have h' := (ShortComplex.homologyMap_comp _ _).symm.trans h
  exact comparison_assoc _ _ _ _ _ h'
    (DirectSumHomologyNaturality.inclusion_homology (fun j => (C j).sc n) d)

end Hironaka.Geometry.ProperSteinProjectiveCech.DirectSumDegreeInclusions
