import Hironaka.Resolution.HironakaActualAnalyticBlockGraphTranslation
import Hironaka.Manifold.LocalHolomorphicInverse

/-! The actual next graph is solved internally from the SAME current
inherited analytic monic family. Its selected equations, true derivative
injectivity, local holomorphic inverse, free first-jet priority and WHOLE
new-block memberships are produced. No graph, Jacobian, basis, rank,
formal lifting or flag certificate is supplied as input. This is one
actual extension producer, rather than the complete finite nested flag. -/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualInheritedNextBlockGraph

noncomputable section

open HolGerm HolomorphicTaylorTail OkaRelationSheaf HironakaHolomorphicJetMonomialSpan
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualAnalyticBlockGraphTranslation
  HironakaActualRelativeNormalJetDivision HironakaActualCanonicalBlockJacobian
  HironakaActualRelativeStandardnessBlockSupport HironakaActualFormalInitialDiagram
  HironakaActualCoefficientPresentationCentrePower HironakaActualOriginalFormalTaylor
  HironakaActualFormalIdealContraction HironakaActualFormalCoordinatePowerDivision

variable {n : ℕ}

private def unitPriority (m : MonomialOrder (Fin n)) (i : Fin n) : m.syn :=
  m.toSyn (Finsupp.single i 1)

private theorem unitPriority_injective (m : MonomialOrder (Fin n)) :
    Function.Injective (unitPriority m) := by
  intro i j hij
  exact Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) (m.toSyn.injective hij)

private theorem coordinate_linear_expansion (L : ComplexModel n →L[ℂ] ComplexModel n)
    (v : ComplexModel n) (j : Fin n) :
    L v j = ∑ i : Fin n, v i * L (EuclideanSpace.single i 1) j := by
  have hsum : ∑ i : Fin n, v i • EuclideanSpace.single i (1 : ℂ) = v := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [← hsum]
  simp [map_sum, map_smul, smul_eq_mul]

/-- A real finite maximum-of-support argument supplies the inverse zero pattern.
It does not assume an inverse-matrix triangularity or target first-jet certificate. -/
theorem actual_upper_triangular_coordinate_preimage
    (m : MonomialOrder (Fin n)) (L : ComplexModel n →L[ℂ] ComplexModel n)
    (hdiag : ∀ j : Fin n, L (EuclideanSpace.single j 1) j ≠ 0)
    (htri : ∀ j i : Fin n, unitPriority m i < unitPriority m j →
      L (EuclideanSpace.single i 1) j = 0)
    (i : Fin n) (v : ComplexModel n)
    (hLv : ∀ j : Fin n, unitPriority m i < unitPriority m j → L v j = 0) :
    ∀ j : Fin n, unitPriority m i < unitPriority m j → v j = 0 := by
  intro j hij
  by_contra hjv
  let S := Finset.univ.filter (fun k : Fin n => unitPriority m i < unitPriority m k ∧ v k ≠ 0)
  have hS : S.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hjv⟩⟩
  obtain ⟨a, ha, hmax⟩ := S.exists_max_image (unitPriority m) hS
  have hia := (Finset.mem_filter.mp ha).2.1
  have hva := (Finset.mem_filter.mp ha).2.2
  have hrow : L v a = v a * L (EuclideanSpace.single a 1) a := by
    rw [coordinate_linear_expansion]
    apply Finset.sum_eq_single a
    · intro b _ hba
      by_cases hlt : unitPriority m b < unitPriority m a
      · rw [htri a b hlt, mul_zero]
      · have hvb : v b = 0 := by
          by_contra hb
          have hab : unitPriority m a ≤ unitPriority m b := le_of_not_gt hlt
          have hib := lt_of_lt_of_le hia hab
          have hbS : b ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hib, hb⟩
          have he : unitPriority m b = unitPriority m a := le_antisymm (hmax b hbS) hab
          exact hba (unitPriority_injective m he)
        rw [hvb, zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_univ a)).elim
  exact (mul_ne_zero hva (hdiag a)) ((hrow.symm.trans (hLv a hia)))

/-- The SAME true coordinate zero pattern and nonzero diagonal internally give
injectivity of the actual continuous-linear derivative. -/
theorem actual_upper_triangular_coordinate_injective
    (m : MonomialOrder (Fin n)) (L : ComplexModel n →L[ℂ] ComplexModel n)
    (hdiag : ∀ j : Fin n, L (EuclideanSpace.single j 1) j ≠ 0)
    (htri : ∀ j i : Fin n, unitPriority m i < unitPriority m j →
      L (EuclideanSpace.single i 1) j = 0) : Function.Injective L := by
  have hker : ∀ v : ComplexModel n, L v = 0 → v = 0 := by
    intro v hLv
    ext j
    have hbig := actual_upper_triangular_coordinate_preimage m L hdiag htri j v
      (fun a _ => by rw [hLv]; rfl)
    have hrow : L v j = v j * L (EuclideanSpace.single j 1) j := by
      rw [coordinate_linear_expansion]
      apply Finset.sum_eq_single j
      · intro a _ haj
        by_cases hlt : unitPriority m a < unitPriority m j
        · rw [htri j a hlt, mul_zero]
        · have hja : unitPriority m j < unitPriority m a := by
            apply lt_of_le_of_ne (le_of_not_gt hlt)
            intro he
            exact haj (unitPriority_injective m he).symm
          rw [hbig a hja, zero_mul]
      · intro hnot
        exact (hnot (Finset.mem_univ j)).elim
    have hzero : v j * L (EuclideanSpace.single j 1) j = 0 := by
      rw [← hrow, hLv]
      rfl
    exact (mul_eq_zero.mp hzero).resolve_right (hdiag j)
  intro v w hvw
  have hzero : L (v-w) = 0 := by rw [map_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hker (v-w) hzero)

private theorem unshifted_extension_injective (n : ℕ) :
    Function.Injective (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom) := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    Function.Injective (Ideal.map f.toRingHom)
  have hc {m : ℕ} (hm : m = n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) (original_formal_ideal_extension_injective n)

private theorem mem_ideal_of_actualTaylor_mem_map
    (I : Ideal (HolGerm (ComplexModel n))) (F : HolGerm (ComplexModel n))
    (hF : actualUnshiftedTaylorAlgHom n F ∈ Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) :
    F ∈ I := by
  have hmap : Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
      (I ⊔ Ideal.span ({F} : Set (HolGerm (ComplexModel n)))) =
      Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    exact sup_eq_left.mpr (Ideal.span_le.mpr (by
      intro G hG
      rcases Set.mem_singleton_iff.mp hG with rfl
      exact hF))
  have he := unshifted_extension_injective n hmap
  have hm : F ∈ I ⊔ Ideal.span ({F} : Set (HolGerm (ComplexModel n))) :=
    (show Ideal.span ({F} : Set (HolGerm (ComplexModel n))) ≤ _ from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton F))
  rwa [he] at hm

theorem map_actualAnalyticCoordinateBlockIdeal_actualTaylor (B : Set (Fin n)) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (actualAnalyticCoordinateBlockIdeal B) =
      actualFormalCoordinateIdeal n B := by
  rw [actualAnalyticCoordinateBlockIdeal, Ideal.map_span, Set.image_image]
  change Ideal.span ((fun i => actualUnshiftedTaylorAlgHom n (coordinateGerm i)) '' B) = _
  simp_rw [actualUnshiftedTaylor_coordinate]
  rfl

/-- Exact WHOLE actual coordinate-plane kernel for ANY original coordinate
block; no supplied trace-kernel or ideal-equality certificate is used. -/
theorem mem_actualAnalyticCoordinateBlockIdeal_iff_projection_zero
    (B : Set (Fin n)) (F : HolGerm (ComplexModel n)) :
    F ∈ actualAnalyticCoordinateBlockIdeal B ↔ actualBlockProjectionGermHom Bᶜ F = 0 := by
  constructor
  · intro hF
    have hle : actualAnalyticCoordinateBlockIdeal B ≤
        RingHom.ker (actualBlockProjectionGermHom Bᶜ).toRingHom := by
      apply Ideal.span_le.mpr
      rintro G ⟨i, hi, rfl⟩
      change actualBlockProjectionGermHom Bᶜ (coordinateGerm i) = 0
      rw [actualBlockProjectionGermHom_coordinate, if_neg (by simpa using hi)]
    exact hle hF
  · intro hz
    apply mem_ideal_of_actualTaylor_mem_map
    rw [map_actualAnalyticCoordinateBlockIdeal_actualTaylor]
    have hp : actualFormalBlockCoordinateProjection Bᶜ (actualUnshiftedTaylorAlgHom n F) = 0 := by
      have h := congrArg (fun f : HolGerm (ComplexModel n) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ => f F)
        (actualTaylor_blockProjection Bᶜ)
      change actualUnshiftedTaylorAlgHom n (actualBlockProjectionGermHom Bᶜ F) = _ at h
      rw [hz, map_zero] at h
      exact h.symm
    have hpow : actualUnshiftedTaylorAlgHom n F ∈ actualFormalCoordinateIdeal n B ^ 1 := by
      apply (mem_actualFormalCoordinateIdeal_pow_iff B 1 _).mpr
      intro α hα
      have hsupport : ∀ i ∉ Bᶜ, α i = 0 := by
        intro i hi
        have hiB : i ∈ B := by simpa using hi
        by_contra hne
        have hw := Finsupp.le_weight_of_ne_zero' (actualCoordinateWeight B) hne
        rw [actualCoordinateWeight, if_pos hiB] at hw
        omega
      have hc := congrArg (MvPowerSeries.coeff α) hp
      rw [coeff_actualFormalBlockCoordinateProjection, if_pos hsupport, map_zero] at hc
      exact hc
    simpa only [pow_one] using hpow

variable {K : Ideal (MvPowerSeries (Fin n) ℂ)}

/-- The true new coordinate block, without a terminal-interval assumption. -/
def actualNextBlockCoordinates (kprev k : ℕ) : Set (Fin n) :=
  actualDegreePrefixVariables MonomialOrder.degLex K k \
    actualDegreePrefixVariables MonomialOrder.degLex K kprev

/-- Embed a genuinely new coordinate into the internally fixed essential index. -/
def actualNextBlockEssentialIndex (kprev k : ℕ) (j : actualNextBlockCoordinates (K := K) kprev k) :
    actualCanonicalEssentialVariables MonomialOrder.degLex K :=
  actualCanonicalBlockEssentialVariable MonomialOrder.degLex K k ⟨j.val, j.property.1⟩

/-- The actual equations are selected derivatives of the SAME current members. -/
def actualNextBlockDerivativeGerm (G : ActualAnalyticInheritedFamily n 0 K) (kprev k : ℕ)
    (j : actualNextBlockCoordinates (K := K) kprev k) : HolGerm (ComplexModel n) :=
  actualInheritedEssentialDerivative G (actualNextBlockEssentialIndex kprev k j)

/-- Form the genuine equation-coordinate map after restricting the ENTIRE old
block to zero. All remaining coordinates are left exactly unchanged. -/
def actualNextBlockEquationMap (kprev k : ℕ)
    (f : actualNextBlockCoordinates (K := K) kprev k → ComplexModel n → ℂ)
    (z : ComplexModel n) : ComplexModel n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm (fun i : Fin n =>
    if hi : i ∈ actualNextBlockCoordinates (K := K) kprev k then
      f ⟨i, hi⟩ (actualBlockCoordinateProjection
        (actualDegreePrefixVariables MonomialOrder.degLex K kprev)ᶜ z)
    else z i)

theorem actualNextBlockEquationMap_apply (kprev k : ℕ)
    (f : actualNextBlockCoordinates (K := K) kprev k → ComplexModel n → ℂ)
    (z : ComplexModel n) (i : Fin n) :
    actualNextBlockEquationMap kprev k f z i =
      if hi : i ∈ actualNextBlockCoordinates (K := K) kprev k then
        f ⟨i, hi⟩ (actualBlockCoordinateProjection
          (actualDegreePrefixVariables MonomialOrder.degLex K kprev)ᶜ z)
      else z i := rfl

theorem actualNextBlockEquationMap_zero (G : ActualAnalyticInheritedFamily n 0 K)
    (kprev k : ℕ) (f : actualNextBlockCoordinates (K := K) kprev k → ComplexModel n → ℂ)
    (hf : ∀ j, HolAt (f j) 0)
    (he : ∀ j, HolGerm.mk (f j) (hf j) = actualNextBlockDerivativeGerm G kprev k j) :
    actualNextBlockEquationMap kprev k f 0 = 0 := by
  ext i
  rw [actualNextBlockEquationMap_apply]
  split_ifs with hi
  · rw [map_zero]
    have h := congrArg HolGerm.eval (he ⟨i, hi⟩)
    rw [HolGerm.eval_mk] at h
    exact h.trans (actualInheritedEssentialDerivative_eval_zero G _)
  · rfl

/-- All SAME selected derivative germs are realized on one honest open domain;
the entire old block is killed before forming the actual equation map. -/
theorem exists_actual_next_block_equation_neighbourhood
    (G : ActualAnalyticInheritedFamily n 0 K) (kprev k : ℕ) :
    ∃ (f : actualNextBlockCoordinates (K := K) kprev k → ComplexModel n → ℂ)
      (hf : ∀ j, HolAt (f j) 0),
      (∀ j, HolGerm.mk (f j) (hf j) = actualNextBlockDerivativeGerm G kprev k j) ∧
      ∃ U : Set (ComplexModel n), IsOpen U ∧ (0 : ComplexModel n) ∈ U ∧
        DifferentiableOn ℂ (actualNextBlockEquationMap kprev k f) U := by
  have hex (j : actualNextBlockCoordinates (K := K) kprev k) :
      ∃ f : ComplexModel n → ℂ, ∃ hf : HolAt f 0,
        HolGerm.mk f hf = actualNextBlockDerivativeGerm G kprev k j := by
    obtain ⟨f, hf, hrep⟩ := HolGerm.exists_eq_mk (actualNextBlockDerivativeGerm G kprev k j)
    exact ⟨f, hf, hrep.symm⟩
  choose f hf he using hex
  have hall : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      ∀ j : actualNextBlockCoordinates (K := K) kprev k, DifferentiableAt ℂ (f j) z :=
    eventually_all.mpr hf
  obtain ⟨V, hVf, hVo, h0V⟩ := eventually_nhds_iff.mp hall
  let P := actualBlockCoordinateProjection (actualDegreePrefixVariables MonomialOrder.degLex K kprev)ᶜ
  let U := P ⁻¹' V
  have hU : IsOpen U := hVo.preimage P.continuous
  have h0U : (0 : ComplexModel n) ∈ U := by
    change P 0 ∈ V
    simpa only [map_zero] using h0V
  refine ⟨f, hf, he, U, hU, h0U, ?_⟩
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.differentiableAt.comp z
  apply differentiableAt_pi.mpr
  intro i
  by_cases hi : i ∈ actualNextBlockCoordinates (K := K) kprev k
  · simp only [dif_pos hi]
    exact (hVf (P z) hz ⟨i, hi⟩).comp z P.differentiableAt
  · simp only [dif_neg hi]
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt

private theorem projection_single (B : Set (Fin n)) (i : Fin n) :
    actualBlockCoordinateProjection B (EuclideanSpace.single i (1 : ℂ)) =
      if i ∈ B then EuclideanSpace.single i 1 else 0 := by
  ext j
  by_cases hi : i ∈ B <;> by_cases hji : j = i
  · subst j
    simp [actualBlockCoordinateProjection_apply, hi]
  · simp [actualBlockCoordinateProjection_apply, hi, hji]
  · subst j
    simp [actualBlockCoordinateProjection_apply, hi]
  · simp [actualBlockCoordinateProjection_apply, hi, hji]

private theorem analytic_coordinate_derivative_mk_eval (i : Fin n)
    (f : ComplexModel n → ℂ) (hf : HolAt f 0) :
    HolGerm.eval (actualAnalyticCoordinateDerivative i (HolGerm.mk f hf)) =
      fderiv ℂ f 0 (EuclideanSpace.single i 1) := rfl

private theorem fderiv_coordinate_apply (F : ComplexModel n → ComplexModel n)
    (hF : DifferentiableAt ℂ F 0) (i j : Fin n) :
    fderiv ℂ F 0 (EuclideanSpace.single i 1) j =
      fderiv ℂ (fun z => F z j) 0 (EuclideanSpace.single i 1) := by
  have h := ((EuclideanSpace.proj j).hasFDerivAt.comp 0 hF.hasFDerivAt).fderiv
  exact (congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L (EuclideanSpace.single i 1)) h).symm

theorem actualNextBlockEquationMap_fderiv_new_coordinate
    (G : ActualAnalyticInheritedFamily n 0 K) (kprev k : ℕ)
    (f : actualNextBlockCoordinates (K := K) kprev k → ComplexModel n → ℂ)
    (hf : ∀ j, HolAt (f j) 0)
    (he : ∀ j, HolGerm.mk (f j) (hf j) = actualNextBlockDerivativeGerm G kprev k j)
    (hΓ : DifferentiableAt ℂ (actualNextBlockEquationMap kprev k f) 0)
    (j : actualNextBlockCoordinates (K := K) kprev k) (i : Fin n) :
    fderiv ℂ (actualNextBlockEquationMap kprev k f) 0 (EuclideanSpace.single i 1) j.val =
      if i ∈ actualDegreePrefixVariables MonomialOrder.degLex K kprev then 0 else
        HolGerm.eval (actualAnalyticCoordinateDerivative i (actualNextBlockDerivativeGerm G kprev k j)) := by
  rw [fderiv_coordinate_apply _ hΓ]
  let P := actualBlockCoordinateProjection (actualDegreePrefixVariables MonomialOrder.degLex K kprev)ᶜ
  have hfunc : (fun z => actualNextBlockEquationMap kprev k f z j.val) = (f j) ∘ P := by
    funext z
    rw [actualNextBlockEquationMap_apply, dif_pos j.property]
    rfl
  rw [hfunc]
  have hcomp : fderiv ℂ ((f j) ∘ P) 0 = (fderiv ℂ (f j) 0).comp P := by
    have hfj : DifferentiableAt ℂ (f j) (P 0) := by
      simpa only [map_zero] using (hf j).self_of_nhds
    have h0 : HasFDerivAt ((f j) ∘ P) ((fderiv ℂ (f j) (P 0)).comp P) 0 :=
      hfj.hasFDerivAt.comp 0 P.hasFDerivAt
    simpa only [map_zero] using h0.fderiv
  rw [hcomp]
  change fderiv ℂ (f j) 0 (P (EuclideanSpace.single i 1)) = _
  rw [projection_single]
  by_cases hi : i ∈ actualDegreePrefixVariables MonomialOrder.degLex K kprev
  · rw [if_neg (by simpa using hi), if_pos hi, map_zero]
  · rw [if_pos (by simpa using hi), if_neg hi, ← he j, analytic_coordinate_derivative_mk_eval]

theorem actualNextBlockEquationMap_fderiv_fixed_coordinate
    (kprev k : ℕ) (f : actualNextBlockCoordinates (K := K) kprev k → ComplexModel n → ℂ)
    (hΓ : DifferentiableAt ℂ (actualNextBlockEquationMap kprev k f) 0)
    (j : Fin n) (hj : j ∉ actualNextBlockCoordinates (K := K) kprev k) (i : Fin n) :
    fderiv ℂ (actualNextBlockEquationMap kprev k f) 0 (EuclideanSpace.single i 1) j =
      (EuclideanSpace.single i (1 : ℂ)) j := by
  rw [fderiv_coordinate_apply _ hΓ]
  have hfunc : (fun z => actualNextBlockEquationMap kprev k f z j) = EuclideanSpace.proj j := by
    funext z
    rw [actualNextBlockEquationMap_apply, dif_neg hj]
    rfl
  rw [hfunc, (EuclideanSpace.proj (𝕜 := ℂ) j).fderiv]
  rfl

/-- Actual representative equations internally have nonzero entire derivative
diagonal. The selected factorials come from the SAME current inherited family. -/
theorem actualNextBlockEquationMap_fderiv_diagonal_ne_zero
    (G : ActualAnalyticInheritedFamily n 0 K) (kprev k : ℕ)
    (f : actualNextBlockCoordinates (K := K) kprev k → ComplexModel n → ℂ)
    (hf : ∀ j, HolAt (f j) 0)
    (he : ∀ j, HolGerm.mk (f j) (hf j) = actualNextBlockDerivativeGerm G kprev k j)
    (hΓ : DifferentiableAt ℂ (actualNextBlockEquationMap kprev k f) 0) (j : Fin n) :
    fderiv ℂ (actualNextBlockEquationMap kprev k f) 0 (EuclideanSpace.single j 1) j ≠ 0 := by
  by_cases hj : j ∈ actualNextBlockCoordinates (K := K) kprev k
  · have h := actualNextBlockEquationMap_fderiv_new_coordinate G kprev k f hf he hΓ ⟨j, hj⟩ j
    rw [if_neg hj.2] at h
    rw [h]
    change HolGerm.eval (actualAnalyticCoordinateDerivative j
      (actualInheritedEssentialDerivative G (actualNextBlockEssentialIndex kprev k ⟨j, hj⟩))) ≠ 0
    have hd := actualInheritedEssentialDerivative_jacobian_diagonal G
      (actualNextBlockEssentialIndex kprev k ⟨j, hj⟩)
    change HolGerm.eval (actualAnalyticCoordinateDerivative j
      (actualInheritedEssentialDerivative G (actualNextBlockEssentialIndex kprev k ⟨j, hj⟩))) = _ at hd
    rw [hd]
    exact actualExponentFactorial_ne_zero _
  · rw [actualNextBlockEquationMap_fderiv_fixed_coordinate kprev k f hΓ j hj j]
    simp

theorem actualNextBlockEquationMap_fderiv_upper_triangular
    (G : ActualAnalyticInheritedFamily n 0 K) (kprev k : ℕ)
    (f : actualNextBlockCoordinates (K := K) kprev k → ComplexModel n → ℂ)
    (hf : ∀ j, HolAt (f j) 0)
    (he : ∀ j, HolGerm.mk (f j) (hf j) = actualNextBlockDerivativeGerm G kprev k j)
    (hΓ : DifferentiableAt ℂ (actualNextBlockEquationMap kprev k f) 0)
    (j i : Fin n)
    (hij : MonomialOrder.degLex.toSyn (Finsupp.single i 1) <
      MonomialOrder.degLex.toSyn (Finsupp.single j 1)) :
    fderiv ℂ (actualNextBlockEquationMap kprev k f) 0 (EuclideanSpace.single i 1) j = 0 := by
  by_cases hj : j ∈ actualNextBlockCoordinates (K := K) kprev k
  · rw [actualNextBlockEquationMap_fderiv_new_coordinate G kprev k f hf he hΓ ⟨j, hj⟩ i]
    split_ifs with hi
    · rfl
    · exact actualInheritedEssentialDerivative_jacobian_lower_coordinate G
        (actualNextBlockEssentialIndex kprev k ⟨j, hj⟩) i hij
  · rw [actualNextBlockEquationMap_fderiv_fixed_coordinate kprev k f hΓ j hj i]
    have hji : j ≠ i := by
      intro heq
      subst j
      exact (lt_irrefl _ hij)
    simp [hji]

/-- The genuine holomorphic inverse function theorem is applied to the actual
selected equations. All derivative injectivity is produced internally. -/
theorem exists_actual_next_block_equation_local_equiv
    (G : ActualAnalyticInheritedFamily n 0 K) (kprev k : ℕ) :
    ∃ (f : actualNextBlockCoordinates (K := K) kprev k → ComplexModel n → ℂ)
      (hf : ∀ j, HolAt (f j) 0),
      (∀ j, HolGerm.mk (f j) (hf j) = actualNextBlockDerivativeGerm G kprev k j) ∧
      ∃ Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n),
        Φ.toFun = actualNextBlockEquationMap kprev k f ∧ Φ.toFun 0 = 0 ∧
        (∀ j : Fin n, fderiv ℂ Φ.toFun 0 (EuclideanSpace.single j 1) j ≠ 0) ∧
        ∀ j i : Fin n,
          MonomialOrder.degLex.toSyn (Finsupp.single i 1) <
            MonomialOrder.degLex.toSyn (Finsupp.single j 1) →
          fderiv ℂ Φ.toFun 0 (EuclideanSpace.single i 1) j = 0 := by
  obtain ⟨f, hf, he, U, hU, h0U, hΓ⟩ := exists_actual_next_block_equation_neighbourhood G kprev k
  have hΓ0 := hΓ.differentiableAt (hU.mem_nhds h0U)
  have hdiag := actualNextBlockEquationMap_fderiv_diagonal_ne_zero G kprev k f hf he hΓ0
  have htri := actualNextBlockEquationMap_fderiv_upper_triangular G kprev k f hf he hΓ0
  have hinj : Function.Injective (fderiv ℂ (actualNextBlockEquationMap kprev k f) 0) :=
    actual_upper_triangular_coordinate_injective MonomialOrder.degLex _ hdiag htri
  obtain ⟨Φ, _hsrc, hΦ, _hall⟩ := exists_localHolomorphicEquivAt hU h0U hΓ hinj
  refine ⟨f, hf, he, Φ, hΦ, ?_, ?_, ?_⟩
  · rw [hΦ]
    exact actualNextBlockEquationMap_zero G kprev k f hf he
  · simpa only [hΦ] using hdiag
  · simpa only [hΦ] using htri

private theorem local_equiv_derivative_right_inverse
    (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (hΦ0 : Φ.toFun 0 = 0)
    (v : ComplexModel n) :
    fderiv ℂ Φ.toFun 0 (fderiv ℂ Φ.invFun 0 v) = v := by
  have h0tar : (0 : ComplexModel n) ∈ Φ.target := by
    simpa only [hΦ0] using Φ.mapsTo_toFun Φ.center_mem_source
  have hcomp : Φ.toFun ∘ Φ.invFun =ᶠ[𝓝 (0 : ComplexModel n)] id := by
    filter_upwards [Φ.isOpen_target.mem_nhds h0tar] with z hz
    exact Φ.right_inv z hz
  have hto := (HironakaHolomorphicJetChartInvariance.local_toFun_holomorphic Φ).self_of_nhds
  have hinv := (HironakaHolomorphicJetChartInvariance.local_invFun_holomorphic Φ hΦ0).self_of_nhds
  have hd := hcomp.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_comp 0 (by simpa only [HironakaHolomorphicJetChartInvariance.local_invFun_zero Φ hΦ0] using hto)
    hinv, fderiv_id] at hd
  simpa only [HironakaHolomorphicJetChartInvariance.local_invFun_zero Φ hΦ0,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun L : ComplexModel n →L[ℂ] ComplexModel n => L v) hd

/-- A real free-coordinate graph is extracted from the ACTUAL local inverse;
its function is independent of every coordinate in the full new block. -/
def actualInverseFreeBlockGraphData (B C : Set (Fin n)) (hCB : C ⊆ B)
    (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (hΦ0 : Φ.toFun 0 = 0) :
    ActualBlockGraphData B C where
  subset := hCB
  baseDomain := actualBlockCoordinateProjection Bᶜ ⁻¹' Φ.target
  isOpen_baseDomain := Φ.isOpen_target.preimage (actualBlockCoordinateProjection Bᶜ).continuous
  zero_mem_baseDomain := by
    change actualBlockCoordinateProjection Bᶜ 0 ∈ Φ.target
    rw [map_zero]
    simpa only [hΦ0] using Φ.mapsTo_toFun Φ.center_mem_source
  value := Φ.invFun ∘ actualBlockCoordinateProjection Bᶜ
  holomorphic := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    exact (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz)).comp z
      (actualBlockCoordinateProjection Bᶜ).differentiableAt
  zero := by
    rw [Function.comp_apply, map_zero]
    exact HironakaHolomorphicJetChartInvariance.local_invFun_zero Φ hΦ0

private theorem actualTaylor_single_coefficient (F : HolGerm (ComplexModel n)) (i : Fin n) :
    MvPowerSeries.coeff (Finsupp.single i 1) (actualUnshiftedTaylorAlgHom n F) =
      HolGerm.eval (actualAnalyticCoordinateDerivative i F) := by
  have h := congrArg (MvPowerSeries.coeff 0) (actualTaylor_actualAnalyticCoordinateDerivative i F)
  rw [HironakaActualCauchyCoefficientLimits.actualTaylor_coeff_zero,
    MvPowerSeries.coeff_pderiv, zero_add, Finsupp.zero_apply] at h
  simpa only [Nat.cast_zero, zero_add, mul_one] using h.symm

theorem actualInverseFreeBlockGraphData_linear_priority
    (B C : Set (Fin n)) (hCB : C ⊆ B)
    (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (hΦ0 : Φ.toFun 0 = 0)
    (hdiag : ∀ j : Fin n, fderiv ℂ Φ.toFun 0 (EuclideanSpace.single j 1) j ≠ 0)
    (htri : ∀ j i : Fin n,
      MonomialOrder.degLex.toSyn (Finsupp.single i 1) <
        MonomialOrder.degLex.toSyn (Finsupp.single j 1) →
      fderiv ℂ Φ.toFun 0 (EuclideanSpace.single i 1) j = 0) :
    ActualBlockGraphLinearPriority (actualInverseFreeBlockGraphData B C hCB Φ hΦ0) := by
  intro j _hj i hi hij
  let D := actualInverseFreeBlockGraphData B C hCB Φ hΦ0
  let w := fderiv ℂ Φ.invFun 0 (EuclideanSpace.single i 1)
  have hw : fderiv ℂ Φ.toFun 0 w = EuclideanSpace.single i 1 :=
    local_equiv_derivative_right_inverse Φ hΦ0 _
  have hzero : w j = 0 := by
    apply actual_upper_triangular_coordinate_preimage MonomialOrder.degLex
      (fderiv ℂ Φ.toFun 0) hdiag htri i w ?_ j hij
    intro a hia
    rw [hw]
    have hai : a ≠ i := by
      intro he
      subst a
      exact lt_irrefl _ hia
    simp [hai]
  rw [actualTaylor_single_coefficient]
  change HolGerm.eval (actualAnalyticCoordinateDerivative i (actualBlockGraphValueGerm D j)) = 0
  unfold actualBlockGraphValueGerm
  rw [analytic_coordinate_derivative_mk_eval]
  have hDv : DifferentiableAt ℂ D.value 0 :=
    D.holomorphic.differentiableAt (D.isOpen_baseDomain.mem_nhds D.zero_mem_baseDomain)
  rw [← fderiv_coordinate_apply D.value hDv i j]
  have hInv := (HironakaHolomorphicJetChartInvariance.local_invFun_holomorphic Φ hΦ0).self_of_nhds
  have hc : fderiv ℂ D.value 0 =
      (fderiv ℂ Φ.invFun 0).comp (actualBlockCoordinateProjection Bᶜ) := by
    have hInv' : DifferentiableAt ℂ Φ.invFun (actualBlockCoordinateProjection Bᶜ 0) := by
      simpa only [map_zero] using hInv
    have h : HasFDerivAt (Φ.invFun ∘ actualBlockCoordinateProjection Bᶜ)
        ((fderiv ℂ Φ.invFun (actualBlockCoordinateProjection Bᶜ 0)).comp
          (actualBlockCoordinateProjection Bᶜ)) 0 :=
      hInv'.hasFDerivAt.comp 0 (actualBlockCoordinateProjection Bᶜ).hasFDerivAt
    simpa only [D, actualInverseFreeBlockGraphData, map_zero] using h.fderiv
  rw [hc]
  change fderiv ℂ Φ.invFun 0 (actualBlockCoordinateProjection Bᶜ (EuclideanSpace.single i 1)) j = 0
  rw [projection_single, if_pos (by simpa using hi)]
  exact hzero

private theorem block_projection_idempotent (B : Set (Fin n)) (z : ComplexModel n) :
    actualBlockCoordinateProjection B (actualBlockCoordinateProjection B z) =
      actualBlockCoordinateProjection B z := by
  ext i
  by_cases hi : i ∈ B <;> simp [actualBlockCoordinateProjection_apply, hi]

private theorem degree_prefix_block_mono {kprev k : ℕ} (hcut : kprev ≤ k) :
    actualDegreePrefixVariables MonomialOrder.degLex K kprev ⊆
      actualDegreePrefixVariables MonomialOrder.degLex K k := by
  intro i hi
  obtain ⟨a, ha, hai⟩ := hi
  exact ⟨a, ha.trans hcut, hai⟩

/-- The next true graph is constructed solely from the SAME current analytic
monic family. Its first-jet priority and whole selected-equation membership
are internally proved, rather than supplied as certificates. -/
theorem exists_actual_inherited_next_block_graph (G : ActualAnalyticInheritedFamily n 0 K)
    (kprev k : ℕ) (hcut : kprev ≤ k) :
    ∃ D : ActualBlockGraphData
        (actualDegreePrefixVariables MonomialOrder.degLex K k)
        (actualNextBlockCoordinates (K := K) kprev k),
      ActualBlockGraphLinearPriority D ∧
      ∀ j : actualNextBlockCoordinates (K := K) kprev k,
        actualBlockGraphGermEquiv D (actualNextBlockDerivativeGerm G kprev k j) ∈
          actualAnalyticCoordinateBlockIdeal (actualDegreePrefixVariables MonomialOrder.degLex K k) := by
  obtain ⟨f, hf, he, Φ, hΦ, hΦ0, hdiag, htri⟩ :=
    exists_actual_next_block_equation_local_equiv G kprev k
  let B := actualDegreePrefixVariables MonomialOrder.degLex K k
  let Bprev := actualDegreePrefixVariables MonomialOrder.degLex K kprev
  let C := actualNextBlockCoordinates (K := K) kprev k
  have hCB : C ⊆ B := fun _ hi => hi.1
  let D := actualInverseFreeBlockGraphData B C hCB Φ hΦ0
  have hpriority : ActualBlockGraphLinearPriority D :=
    actualInverseFreeBlockGraphData_linear_priority B C hCB Φ hΦ0 hdiag htri
  refine ⟨D, hpriority, ?_⟩
  intro j
  apply (mem_actualAnalyticCoordinateBlockIdeal_iff_projection_zero B _).mpr
  rw [← he j]
  unfold actualBlockProjectionGermHom
  rw [actualBlockGraphGermEquiv_mk, HironakaHolomorphicJetChartInvariance.compAlgHom_mk,
    ← HolGerm.mk_zero]
  apply HolGerm.mk_eq_mk_iff.mpr
  have h0tar : (0 : ComplexModel n) ∈ Φ.target := by
    simpa only [hΦ0] using Φ.mapsTo_toFun Φ.center_mem_source
  have hN : IsOpen (actualBlockCoordinateProjection Bᶜ ⁻¹' Φ.target) :=
    Φ.isOpen_target.preimage (actualBlockCoordinateProjection Bᶜ).continuous
  have h0N : (0 : ComplexModel n) ∈ actualBlockCoordinateProjection Bᶜ ⁻¹' Φ.target := by
    simpa only [Set.mem_preimage, map_zero] using h0tar
  filter_upwards [hN.mem_nhds h0N] with z hz
  let w := actualBlockCoordinateProjection Bᶜ z
  let u := Φ.invFun w
  have hw : w ∈ Φ.target := hz
  have hΓ : actualNextBlockEquationMap kprev k f u = w := by
    rw [← hΦ]
    exact Φ.right_inv w hw
  have hold : ∀ i ∈ Bprev, u i = 0 := by
    intro i hi
    have hinot : i ∉ C := fun hc => hc.2 hi
    have h := congrArg (fun v : ComplexModel n => v i) hΓ
    rw [actualNextBlockEquationMap_apply, dif_neg hinot] at h
    have hiB : i ∈ B := degree_prefix_block_mono hcut hi
    have hw0 : w i = 0 := by simp [w, actualBlockCoordinateProjection_apply, hiB]
    exact h.trans hw0
  have hPu : actualBlockCoordinateProjection Bprevᶜ u = u := by
    ext i
    by_cases hi : i ∈ Bprev
    · simp [actualBlockCoordinateProjection_apply, hi, hold i hi]
    · simp [actualBlockCoordinateProjection_apply, hi]
  have hψ : actualBlockGraphMap B C D.value w = u := by
    ext i
    rw [actualBlockGraphMap_apply]
    by_cases hi : i ∈ C
    · rw [if_pos hi]
      have hw0 : w i = 0 := by simp [w, actualBlockCoordinateProjection_apply, hCB hi]
      have hval : D.value (actualBlockCoordinateProjection Bᶜ w) i = u i := by
        have hwP : actualBlockCoordinateProjection Bᶜ w = w :=
          block_projection_idempotent Bᶜ z
        change Φ.invFun (actualBlockCoordinateProjection Bᶜ
          (actualBlockCoordinateProjection Bᶜ w)) i = u i
        rw [hwP, hwP]
      rw [hw0, hval, zero_add]
    · rw [if_neg hi, add_zero]
      have h := congrArg (fun v : ComplexModel n => v i) hΓ
      rw [actualNextBlockEquationMap_apply, dif_neg hi] at h
      exact h.symm
  have hj := congrArg (fun v : ComplexModel n => v j.val) hΓ
  rw [actualNextBlockEquationMap_apply, dif_pos j.property, hPu] at hj
  have hwj : w j.val = 0 := by
    have hjB : j.val ∈ B := j.property.1
    simp [w, actualBlockCoordinateProjection_apply, hjB]
  change f j (actualBlockGraphMap B C D.value w) = 0
  rw [hψ]
  exact hj.trans hwj

end

end Hironaka.HironakaActualInheritedNextBlockGraph
