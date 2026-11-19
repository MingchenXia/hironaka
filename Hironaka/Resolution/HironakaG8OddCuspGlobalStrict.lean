import Hironaka.Resolution.HironakaG8OddCuspMonomialStrict

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8OddCuspGlobalStrict
noncomputable section

open Hironaka.BlowupSequences
  HironakaG8OddCuspVanishingStalk HironakaG8OddCuspStrictChart HironakaG8OddCuspMonomialStrict
  BlowupExistenceOriginModel BlowupExistenceOriginGenerator BlowupExistenceOriginUniversal
  BlowupStrictSubmanifold BlowupStrictIdeal BlowupMonomialCharts

private abbrev X := ComplexModel 3

private theorem closed_chart_condition {A : Set (OriginBlowup 3)} (j : Fin 3)
    {V : Set X} (hV : IsClosed V)
    (h : ∀ a ∈ A, a ∈ originSource j → originCoord j a ∈ V) :
    ∀ a ∈ closure A, a ∈ originSource j → originCoord j a ∈ V := by
  intro a ha haS
  by_contra hNot
  let O : Set (OriginBlowup 3) := originSource j ∩ (originCoord j) ⁻¹' Vᶜ
  have hO : IsOpen O := (continuousOn_originCoord j).isOpen_inter_preimage
    (isOpen_originSource j) hV.isOpen_compl
  obtain ⟨b,hbO,hb⟩ := mem_closure_iff.mp ha O hO ⟨haS,hNot⟩
  exact hbO.2 (h b hb hbO.1)

private theorem y_chart_equation (p : ℕ) (hp : 2 < p) :
    ∀ a ∈ geoStrictTransform originProj ({0} : Set X) (embeddedCuspSet p), a ∈ originSource 1 →
      (originCoord 1 a) 1 ^ (p-2) * (originCoord 1 a) 0 ^ p = 1 := by
  let V : Set X := {z | z 1 ^ (p-2) * z 0^p = 1}
  have hV : IsClosed V := isClosed_eq
    (((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).continuous.pow (p-2)).mul
      ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).continuous.pow p)) continuous_const
  apply closed_chart_condition 1 hV
  intro a ha haS
  let z := originCoord 1 a
  have haZ : originMk 1 z = a := originMk_originCoord haS
  have hNe : z 1 ≠ 0 := by
    intro hu
    apply ha.2
    apply mem_singleton_iff.mpr
    rw [← haZ,originProj_originMk,hu,zero_smul]
  have hSub : originProj a = monomial 0 (1 : Fin 3) z := by
    rw [← haZ]
    exact congrFun (originProj_comp_originMk_eq_monomial 1) z
  have hs := ((embedded_cusp_mem_iff p _).mp ha.1).1
  rw [hSub] at hs
  simp only [monomial_apply,zero_le,and_true,ne_eq,
    show (0 : Fin 3) ≠ 1 by decide,not_false_eq_true,not_true_eq_false,if_true] at hs
  have hpw : z 1 ^ p = z 1 ^ 2 * z 1 ^ (p-2) := by
    rw [← pow_add,show 2+(p-2)=p by omega]
  change z 1 ^ (p-2) * z 0 ^ p = 1
  apply mul_left_cancel₀ (pow_ne_zero 2 hNe)
  calc
    z 1 ^ 2 * (z 1 ^ (p-2) * z 0 ^ p) = (z 0 * z 1) ^ p := by
      rw [mul_pow,hpw]
      ring
    _ = z 1 ^ 2 := hs.symm
    _ = z 1 ^ 2 * 1 := (mul_one _).symm

private theorem z_chart_empty (p : ℕ) :
    ∀ a ∈ geoStrictTransform originProj ({0} : Set X) (embeddedCuspSet p), a ∉ originSource 2 := by
  intro a ha hs
  have hh := closed_chart_condition (A := originProj ⁻¹' (embeddedCuspSet p \ ({0} : Set X))) 2
    (V := ∅) isClosed_empty (by
      intro b hb hbS
      exfalso
      have hw := ((embedded_cusp_mem_iff p _).mp hb.1).2
      have hG := originProj_apply_eq hbS (2 : Fin 3)
      simp only [gen_self,mul_one] at hG
      apply hb.2
      exact mem_singleton_iff.mpr ((originProj_eq_zero_iff hbS).mpr (hG.symm.trans hw)))
    a ha hs
  exact hh

/-- No point of the strict transform is missing from the actual x-chart.
The y-chart equation excludes exceptional points there, and the z-chart
has empty strict trace. -/
theorem geoStrictTransform_cusp_subset_first_chart (p : ℕ) (hp : 2 < p) :
    geoStrictTransform originProj ({0} : Set X) (embeddedCuspSet p) ⊆ originSource 0 := by
  intro a ha
  obtain ⟨j,hj⟩ := exists_mem_originSource a
  fin_cases j
  · exact hj
  · let z := originCoord 1 a
    have hz : originMk 1 z = a := originMk_originCoord hj
    have hh : z 1 ^ (p-2) * z 0 ^ p = 1 := y_chart_equation p hp a ha hj
    have h0 : z 0 ≠ 0 := by
      intro he
      rw [he,zero_pow hp.pos.ne',mul_zero] at hh
      exact zero_ne_one hh
    rw [← hz,originMk_mem_originSource_iff]
    simpa [show (0 : Fin 3) ≠ 1 by decide] using h0
  · exact (z_chart_empty p a ha hj).elim

/-- The globally defined strict transform is the exact chart image of
the lower-exponent cusp. This covers every projective direction. -/
theorem strictTransform_cusp_eq_image_first_chart (p : ℕ) (hp : 2 < p) :
    strictTransform 3 originProj (embeddedCuspSet p) =
      originMk (0 : Fin 3) '' embeddedCuspSet (p-2) := by
  have hg := geoStrictTransform_eq_strictTransform (isBlowupAlong_originProj (by decide : 0 < 3))
    (cusp_subset_closure_punctured p hp.pos)
  rw [← hg]
  ext a
  constructor
  · intro ha
    have hs := geoStrictTransform_cusp_subset_first_chart p hp ha
    refine ⟨originCoord 0 a,?_,originMk_originCoord hs⟩
    rw [← first_chart_geoStrictTransform_cusp p hp]
    change originMk 0 (originCoord 0 a) ∈ geoStrictTransform originProj ({0} : Set X) (embeddedCuspSet p)
    rwa [originMk_originCoord hs]
  · rintro ⟨z,hz,rfl⟩
    rw [← first_chart_geoStrictTransform_cusp p hp] at hz
    exact hz

/-- The whole exceptional fibre of the strict cusp is its unique
first-chart origin. -/
theorem strictTransform_cusp_exceptional_fibre (p : ℕ) (hp : 2 < p) :
    strictTransform 3 originProj (embeddedCuspSet p) ∩ originProj ⁻¹' ({0} : Set X) =
      {originMk (0 : Fin 3) (0 : X)} := by
  rw [strictTransform_cusp_eq_image_first_chart p hp]
  ext a
  constructor
  · rintro ⟨⟨z,hz,rfl⟩,hE⟩
    have h0 : z 0 = 0 := by
      have hp0 := mem_singleton_iff.mp hE
      rwa [originProj_eq_zero_iff (originMk_mem_originSource 0 z),originGen_originMk] at hp0
    obtain ⟨h1,h2⟩ := (embedded_cusp_mem_iff (p-2) z).mp hz
    rw [h0,zero_pow (by omega : p-2 ≠ 0)] at h1
    have h1' : z 1 = 0 := by
      by_contra h
      exact pow_ne_zero 2 h h1
    have hz0 : z = 0 := by
      apply PiLp.ext
      intro i
      fin_cases i
      · exact h0
      · exact h1'
      · exact h2
    rw [hz0]
    exact mem_singleton _
  · rintro h
    have he := mem_singleton_iff.mp h
    subst a
    refine ⟨⟨0,(embedded_cusp_mem_iff _ _).mpr ?_,rfl⟩,?_⟩
    · simp [zero_pow (by omega : p-2 ≠ 0)]
    · change originProj (originMk (0 : Fin 3) (0 : X)) = 0
      simp

end
end Hironaka.HironakaG8OddCuspGlobalStrict

#print axioms Hironaka.HironakaG8OddCuspGlobalStrict.strictTransform_cusp_eq_image_first_chart

#print axioms Hironaka.HironakaG8OddCuspGlobalStrict.strictTransform_cusp_exceptional_fibre
