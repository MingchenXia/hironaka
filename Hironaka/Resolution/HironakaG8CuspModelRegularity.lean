import Hironaka.Resolution.HironakaG8BFamilyEmptyMember
import Hironaka.Resolution.HironakaG8OddCuspGeometricSource
import Hironaka.Resolution.HironakaG8CaseTCoordinateReplacement
import Hironaka.Invariant.CodimOnePartCanonical

/-! Polynomial flattening of the smooth terminal equation of an odd cusp. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
open Set
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CuspModelRegularity

open Hironaka.BlowupSequences BlowupStrictSubmanifold
  NormalCrossings HironakaG8BFamilyEmptyMember HironakaG8OddCuspVanishingStalk
  HironakaG8OddCuspGeometricSource HironakaG8CaseTCoordinateReplacement
  HironakaG8MemberLoci HironakaEmbeddedAnalytic

private def shear (a : ℂ) (z : ComplexModel 3) : ComplexModel 3 :=
  WithLp.toLp 2 (fun j => if j = 0 then z 0 + a * z 1 ^ 2 else z j)

private theorem shear_smooth (a : ℂ) :
    ContMDiff 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ComplexModel 3) ∞ (shear a) := by
  have hp (j : Fin 3) : ContDiff ℂ ∞ (fun z : ComplexModel 3 => z j) :=
    (EuclideanSpace.proj j : ComplexModel 3 →L[ℂ] ℂ).contDiff
  have hc (j : Fin 3) : ContDiff ℂ ∞ (fun z : ComplexModel 3 =>
      if j = 0 then z 0 + a * z 1 ^ 2 else z j) := by
    split_ifs
    · exact (hp 0).add (contDiff_const.mul ((hp 1).pow 2))
    · exact hp j
  exact ((EuclideanSpace.equiv (Fin 3) ℂ).symm.contDiff.comp (contDiff_pi.mpr hc)).contMDiff

private theorem shear_neg_inverse (a : ℂ) (z : ComplexModel 3) :
    shear a (shear (-a) z) = z := by
  ext j
  by_cases hj : j = 0
  · subst j
    change (if (0 : Fin 3) = 0 then (shear (-a) z) 0 + a * (shear (-a) z) 1 ^ 2 else
      (shear (-a) z) 0) = z 0
    simp [shear, WithLp.ofLp_toLp]
  · change (if j = 0 then (shear (-a) z) 0 + a * (shear (-a) z) 1 ^ 2 else
      (shear (-a) z) j) = z j
    simp [shear, WithLp.ofLp_toLp, hj]

/-- The terminal cusp equation \(z_1^2=z_0\), together with \(z_2=0\),
defines a closed smooth embedded curve. -/
theorem embedded_cusp_one_isClosedSubmanifold :
    IsClosedSubmanifold 3 (embeddedCuspSet 1) := by
  let C := ({0,2} : Finset (Fin 3))
  have hEq : embeddedCuspSet 1 = shear (-1) ⁻¹' coordSubspace C := by
    ext z
    change (∀ i, embeddedCuspEquations 1 i z = 0) ↔ _
    have h0 : (shear (-1) z) 0 = z 0 - z 1 ^ 2 := by
      change z 0 + (-1 : ℂ) * z 1 ^ 2 = _
      ring
    have h2 : (shear (-1) z) 2 = z 2 := rfl
    constructor
    · intro hz
      have hz0 : z 1 ^ 2 - z 0 = 0 := by
        simpa [embeddedCuspEquations] using hz 0
      have hz2 : z 2 = 0 := by simpa [embeddedCuspEquations] using hz 1
      change ∀ j ∈ C, (shear (-1) z) j = 0
      intro j hj
      have hj' : j = 0 ∨ j = 2 := by simpa [C] using hj
      rcases hj' with rfl | rfl
      · rw [h0, sub_eq_zero]
        exact (sub_eq_zero.mp hz0).symm
      · rw [h2, hz2]
    · intro hz i
      change ∀ j ∈ C, (shear (-1) z) j = 0 at hz
      fin_cases i
      · have hz0 := hz 0 (by simp [C])
        rw [h0, sub_eq_zero] at hz0
        simpa [embeddedCuspEquations, sub_eq_zero] using hz0.symm
      · have hz2 := hz 2 (by simp [C])
        rw [h2] at hz2
        simpa [embeddedCuspEquations] using hz2
  rw [hEq]
  exact MarkedIdealBiholomorphism.isClosedSubmanifold_preimage
    (shear_smooth (-1)) (shear_smooth 1)
    (fun z => by simpa using shear_neg_inverse (-1) z)
    (fun z => by simpa using shear_neg_inverse 1 z)
    (isClosedSubmanifold_coordSubspace C)

private def translate (x : ComplexModel 3) :
    ComplexModel 3 ≃ₘ⟮𝓘(ℂ,ComplexModel 3),𝓘(ℂ,ComplexModel 3)⟯ ComplexModel 3 where
  toFun z := z + x
  invFun z := z - x
  left_inv z := add_sub_cancel_right z x
  right_inv z := sub_add_cancel z x
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

/-- Away from the origin the second coordinate has a nonzero partial
derivative in the cusp equation, so it supplies a local defining coordinate. -/
theorem regularAtDim_embedded_cusp_off_zero {p : ℕ} {x : ComplexModel 3}
    (hx : x ∈ embeddedCuspSet p) (hNe : x ≠ 0) :
    RegularAtDim (n := 3) (embeddedCuspSet p) x 1 := by
  have hx01 : x 1 ^ 2 = x 0 ^ p := sub_eq_zero.mp (by
    simpa [embeddedCuspSet, embeddedCuspEquations] using hx 0)
  have hx2 : x 2 = 0 := by simpa [embeddedCuspSet, embeddedCuspEquations] using hx 1
  have hx1 : x 1 ≠ 0 := by
    intro h
    have hx0 : x 0 = 0 := by
      by_contra h0
      exact pow_ne_zero p h0 (by simpa [h] using hx01.symm)
    exact hNe (by ext j; fin_cases j <;> assumption)
  let f (z : ComplexModel 3) : ℂ := (z 1 + x 1)^2 - (z 0 + x 0)^p
  have hf_diff (i : Fin 3) :
      HasFDerivAt (fun z : ComplexModel 3 => z i + x i)
        (EuclideanSpace.proj i : ComplexModel 3 →L[ℂ] ℂ) (0 : ComplexModel 3) :=
    (EuclideanSpace.proj i : ComplexModel 3 →L[ℂ] ℂ).hasFDerivAt.add_const (x i)
  have hF := ((hf_diff 1).pow 2).sub ((hf_diff 0).pow p)
  change HasFDerivAt f _ _ at hF
  have hf0 : f 0 = 0 := by simpa [f] using sub_eq_zero.mpr hx01
  have hPartial : fderiv ℂ f 0 (EuclideanSpace.single 1 (1 : ℂ)) ≠ 0 := by
    rw [hF.fderiv]
    simpa [EuclideanSpace.proj, two_mul] using hx1
  have hp (i : Fin 3) : Differentiable ℂ (fun z : ComplexModel 3 => z i + x i) :=
    (EuclideanSpace.proj i : ComplexModel 3 →L[ℂ] ℂ).differentiable.add_const (x i)
  have hf : DifferentiableOn ℂ f univ :=
    (((hp 1).pow 2).sub ((hp 0).pow p)).differentiableOn
  obtain ⟨Ψ,_,hΨ0,hΨ1,hΨ⟩ := exists_coordinate_replacement_at isOpen_univ (mem_univ _) hf hf0 1 hPartial
  let T := ({1,2} : Finset (Fin 3))
  let τ := translate x
  have hChart : (complexChartAt (n := 3) (0 : ComplexModel 3)).val =
      OpenPartialHomeomorph.refl (ComplexModel 3) := by
    simp [complexChartAt, chartAt_self_eq]
  have hChart_apply (z : ComplexModel 3) :
      (complexChartAt (n := 3) (0 : ComplexModel 3)).val z = z := by
    rw [hChart]
    rfl
  have hChart_target : (complexChartAt (n := 3) (0 : ComplexModel 3)).val.target = univ := by
    rw [hChart]
    rfl
  let Φ : LocalHolomorphicEquivAt
      ((complexChartAt (n := 3) (0 : ComplexModel 3)).val 0) :=
    { Ψ with center_mem_source := by rw [hChart_apply]; exact Ψ.center_mem_source }
  have hFlat :
      RegularAtDim (n := 3) (τ ⁻¹' embeddedCuspSet p) (0 : ComplexModel 3) (3 - T.card) := by
    apply regularAtDim_of_flat_coordSubspace (T := T) Φ
    · rw [hChart_target]
      exact subset_univ _
    · change Ψ.toFun ((complexChartAt (n := 3) (0 : ComplexModel 3)).val 0) = 0
      rw [hChart_apply, hΨ0]
    · intro z _ _
      change (∀ i, embeddedCuspEquations p i (z + x) = 0) ↔
        ∀ j ∈ T, Ψ.toFun ((complexChartAt (n := 3) (0 : ComplexModel 3)).val z) j = 0
      rw [hChart_apply]
      have hz1 : embeddedCuspEquations p 0 (z + x) = Ψ.toFun z 1 := by
        rw [hΨ1, embeddedCuspEquations, if_pos rfl]
        rfl
      have hz2 : embeddedCuspEquations p 1 (z + x) = Ψ.toFun z 2 := by
        rw [hΨ _ _ (by decide), embeddedCuspEquations, if_neg (by decide)]
        change z 2 + x 2 = z 2
        rw [hx2, add_zero]
      constructor
      · intro hz i hi
        have hi' : i = 1 ∨ i = 2 := by simpa [T] using hi
        rcases hi' with rfl | rfl
        · rw [← hz1, hz 0]
        · rw [← hz2, hz 1]
      · intro hz i
        fin_cases i
        · exact hz1.trans (hz 1 (by simp [T]))
        · exact hz2.trans (hz 2 (by simp [T]))
  have hdim : 3 - T.card = 1 := by decide
  rw [hdim] at hFlat
  have hRegular := (CodimOnePartCanonical.regularAtDim_preimage_iff τ).mp hFlat
  change RegularAtDim (n := 3) (embeddedCuspSet p) (0 + x) 1 at hRegular
  simpa using hRegular

/-- The origin is the entire singular locus of an odd embedded cusp. -/
theorem embedded_odd_cusp_singularSet_eq_singleton (p : ℕ) (hp : Odd p) (hgt : 2 < p) :
    singularSet (n := 3) (embeddedCuspSet p) = {0} := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨hxW,hn⟩ := mem_singularSet_iff.mp hx
    by_contra hNe
    exact hn 1 (regularAtDim_embedded_cusp_off_zero hxW (by simpa using hNe))
  · rw [Set.singleton_subset_iff]
    exact embedded_odd_cusp_singular_at_zero p hp hgt

end Hironaka.HironakaG8CuspModelRegularity
