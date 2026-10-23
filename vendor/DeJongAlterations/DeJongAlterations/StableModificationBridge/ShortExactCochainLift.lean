import DeJongAlterations.StableModification.Cohomology.CechComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! Actual native short-exact cochain geometry internally lifts whole closed degree-zero cochains. -/

noncomputable section

namespace DeJongAlterations.StableModificationBridge.ShortExactCochainLift

open CategoryTheory Limits
open StableModification.Cohomology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- The SAME actual native short exact complexes and H1 vanishing INTERNALLY lift every whole closed zero-cochain. -/
theorem exists_closed_lift {R : Type u} [CommRing R]
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact)
    (hH : IsZero (S.X₁.homology 1)) (t : S.X₃.X 0) (ht : S.X₃.d 0 1 t = 0) :
    ∃ s : S.X₂.X 0, S.X₂.d 0 1 s = 0 ∧ S.g.f 0 s = t := by
  have hdeg := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS
  have hsurj : Function.Surjective (S.g.f 0) := (hdeg 0).moduleCat_surjective_g
  have hinj : Function.Injective (S.f.f 2) := (hdeg 2).moduleCat_injective_f
  have hex : Function.Exact (S.f.f 1) (S.g.f 1) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S.map (HomologicalComplex.eval (ModuleCat.{u} R) _ 1))).mp (hdeg 1).exact
  obtain ⟨a, ha⟩ := hsurj t
  have hda : S.g.f 1 (S.X₂.d 0 1 a) = 0 := by
    have h := ConcreteCategory.congr_hom (S.g.comm 0 1).symm a
    change S.g.f 1 (S.X₂.d 0 1 a) = S.X₃.d 0 1 (S.g.f 0 a) at h
    rw [h, ha, ht]
  obtain ⟨w, hw⟩ := (hex _).mp hda
  have hwc : S.X₁.d 1 2 w = 0 := by
    apply hinj
    rw [map_zero]
    have h := ConcreteCategory.congr_hom (S.f.comm 1 2).symm w
    change S.f.f 2 (S.X₁.d 1 2 w) = S.X₂.d 1 2 (S.f.f 1 w) at h
    rw [h, hw]
    exact ConcreteCategory.congr_hom (S.X₂.d_comp_d 0 1 2) a
  obtain ⟨z, hz⟩ := (isZero_homology_succ_iff S.X₁ 0).mp hH w hwc
  refine ⟨a - S.f.f 0 z, ?_, ?_⟩
  · rw [map_sub]
    have h := ConcreteCategory.congr_hom (S.f.comm 0 1).symm z
    change S.f.f 1 (S.X₁.d 0 1 z) = S.X₂.d 0 1 (S.f.f 0 z) at h
    rw [← h, hz, hw, sub_self]
  · rw [map_sub, ha]
    have hzero : S.g.f 0 (S.f.f 0 z) = 0 :=
      (S.map (HomologicalComplex.eval (ModuleCat.{u} R) _ 0)).zero_apply z
    rw [hzero, sub_zero]

end DeJongAlterations.StableModificationBridge.ShortExactCochainLift
