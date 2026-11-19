import Hironaka.Resolution.HironakaActualFixedInheritedSelector
import Hironaka.Resolution.HironakaActualTaylorCoordinateNaturality
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Genuine analytic coordinate permutations transport a FIXED selector.
This raw-family theorem asserts no head preservation for arbitrary p and
never recomputes a fresh Classical.choose after changing coordinates. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualFixedInheritedSelectorPermutation
noncomputable section
open HolGerm HironakaRelativeNormalMonomialBasis
  HironakaActualFixedInheritedSelector HironakaActualCanonicalBlockJacobian
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualCoefficientPresentationCentrePower
  HironakaActualTaylorCoordinateNaturality HironakaActualAnalyticFormalNormalPowers
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
  HironakaActualFormalCoordinatePowerDivision HironakaActualAnalyticBlockGraphTranslation
  HironakaActualCauchyCoefficientLimits
variable {n : ℕ}

private theorem permute_apply (p : Fin n ≃ Fin n) (α : Fin n →₀ ℕ) (i : Fin n) :
    Finsupp.domCongr p α i = α (p.symm i) := by
  simp only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.mapDomain_equiv_apply]

private theorem permute_degree (p : Fin n ≃ Fin n) (α : Fin n →₀ ℕ) :
    normalExponentDegree (Finsupp.domCongr p α) = normalExponentDegree α := by
  unfold normalExponentDegree
  exact Fintype.sum_equiv p.symm _ _ (fun i => permute_apply p α i)

private theorem permute_factorial (p : Fin n ≃ Fin n) (α : Fin n →₀ ℕ) :
    actualExponentFactorial (Finsupp.domCongr p α) = actualExponentFactorial α := by
  unfold actualExponentFactorial
  exact Fintype.prod_equiv p.symm _ _ (fun i => congrArg (fun k : ℕ => (k.factorial : ℂ)) (permute_apply p α i))

private theorem coeff_rename (p : Fin n ≃ Fin n) (F : MvPowerSeries (Fin n) ℂ) (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.domCongr p α) (MvPowerSeries.rename p F) = MvPowerSeries.coeff α F := by
  simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding] using
    MvPowerSeries.coeff_embDomain_rename p.toEmbedding F α

def actualPermutationLinearEquiv (p : Fin n ≃ Fin n) : ComplexModel n ≃L[ℂ] ComplexModel n :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ p.symm).toContinuousLinearEquiv

theorem actualPermutationLinearEquiv_apply (p : Fin n ≃ Fin n) (z : ComplexModel n) (i : Fin n) :
    actualPermutationLinearEquiv p z i = z (p i) := rfl

def actualPermutationLocalEquiv (p : Fin n ≃ Fin n) :
    LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ _
  toFun := actualPermutationLinearEquiv p
  invFun := (actualPermutationLinearEquiv p).symm
  toFun_holomorphic := (actualPermutationLinearEquiv p).differentiable.differentiableOn
  invFun_holomorphic := (actualPermutationLinearEquiv p).symm.differentiable.differentiableOn
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun z _ => (actualPermutationLinearEquiv p).left_inv z
  right_inv := fun z _ => (actualPermutationLinearEquiv p).right_inv z

def actualPermutationGermEquiv (p : Fin n ≃ Fin n) :
    HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) :=
  localGermAlgEquiv (actualPermutationLocalEquiv p) (map_zero (actualPermutationLinearEquiv p))

theorem actualPermutationGermEquiv_coordinate (p : Fin n ≃ Fin n) (i : Fin n) :
    actualPermutationGermEquiv p (coordinateGerm i) = coordinateGerm (p i) := by
  rfl

theorem actualTaylor_actualPermutationGermEquiv (p : Fin n ≃ Fin n) (F : HolGerm (ComplexModel n)) :
    actualUnshiftedTaylorAlgHom n (actualPermutationGermEquiv p F) =
      MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n F) := by
  have h : (actualUnshiftedTaylorAlgHom n).comp (actualPermutationGermEquiv p).toAlgHom =
      (MvPowerSeries.rename p).comp (actualUnshiftedTaylorAlgHom n) := by
    apply actualGermAlgHom_eq_of_coordinate_images
    · intro i
      change actualUnshiftedTaylorAlgHom n (actualPermutationGermEquiv p (coordinateGerm i)) =
        MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n (coordinateGerm i))
      rw [actualPermutationGermEquiv_coordinate, actualUnshiftedTaylor_coordinate,
        actualUnshiftedTaylor_coordinate, MvPowerSeries.rename_X]
    · intro i
      change actualUnshiftedTaylorAlgHom n (actualPermutationGermEquiv p (coordinateGerm i)) ∈ _
      rw [actualPermutationGermEquiv_coordinate, actualUnshiftedTaylor_coordinate]
      exact Ideal.subset_span ⟨p i, mem_univ _, rfl⟩
  exact DFunLike.congr_fun h F

theorem actualFormalMultiDerivative_rename (p : Fin n ≃ Fin n) (β : Fin n →₀ ℕ)
    (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalMultiDerivative (Finsupp.domCongr p β) (MvPowerSeries.rename p F) =
      MvPowerSeries.rename p (actualFormalMultiDerivative β F) := by
  apply MvPowerSeries.ext
  intro γ
  obtain ⟨γ, rfl⟩ := (Finsupp.domCongr p).surjective γ
  rw [coeff_actualFormalMultiDerivative, ← map_add, coeff_rename, permute_factorial,
    permute_factorial, coeff_rename, coeff_actualFormalMultiDerivative]

theorem actualAnalyticMultiDerivative_permutation (p : Fin n ≃ Fin n) (β : Fin n →₀ ℕ)
    (F : HolGerm (ComplexModel n)) :
    actualAnalyticMultiDerivative (Finsupp.domCongr p β) (actualPermutationGermEquiv p F) =
      actualPermutationGermEquiv p (actualAnalyticMultiDerivative β F) := by
  apply actualUnshiftedTaylorAlgHom_injective n
  rw [actualTaylor_actualAnalyticMultiDerivative, actualTaylor_actualPermutationGermEquiv,
    actualTaylor_actualPermutationGermEquiv, actualTaylor_actualAnalyticMultiDerivative,
    actualFormalMultiDerivative_rename]

def fixedPermutedVertices (p : Fin n ≃ Fin n) (V : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) :=
  V.map (Finsupp.domCongr p).toEquiv.toEmbedding

def fixedVertexPermutation (p : Fin n ≃ Fin n) (V : Finset (Fin n →₀ ℕ)) : V ≃ fixedPermutedVertices p V where
  toFun a := ⟨Finsupp.domCongr p a.val, Finset.mem_map.mpr ⟨a.val, a.property, rfl⟩⟩
  invFun a := ⟨(Finsupp.domCongr p).symm a.val, by
    obtain ⟨b, hb, he⟩ := Finset.mem_map.mp a.property
    rw [← he]
    change (Finsupp.domCongr p).symm ((Finsupp.domCongr p) b) ∈ V
    simpa only [AddEquiv.symm_apply_apply] using hb⟩
  left_inv a := Subtype.ext ((Finsupp.domCongr p).symm_apply_apply a.val)
  right_inv a := Subtype.ext ((Finsupp.domCongr p).apply_symm_apply a.val)

theorem fixedVertexPermutation_coeff (p : Fin n ≃ Fin n) (V : Finset (Fin n →₀ ℕ))
    (a : V) (i : Fin n) : (fixedVertexPermutation p V a).val (p i) = a.val i := by
  change Finsupp.domCongr p a.val (p i) = _
  rw [permute_apply, Equiv.symm_apply_apply]

def fixedEssentialPermutation (p : Fin n ≃ Fin n) (V : Finset (Fin n →₀ ℕ)) :
    fixedSelectorEssential V ≃ fixedSelectorEssential (fixedPermutedVertices p V) where
  toFun j := ⟨p j.val, by
    obtain ⟨a, ha⟩ := j.property
    exact ⟨fixedVertexPermutation p V a, by rwa [fixedVertexPermutation_coeff]⟩⟩
  invFun j := ⟨p.symm j.val, by
    obtain ⟨a, ha⟩ := j.property
    obtain ⟨a, rfl⟩ := (fixedVertexPermutation p V).surjective a
    refine ⟨a, ?_⟩
    have hc := fixedVertexPermutation_coeff p V a (p.symm j.val)
    rw [Equiv.apply_symm_apply] at hc
    rwa [hc] at ha⟩
  left_inv j := Subtype.ext (p.symm_apply_apply j.val)
  right_inv j := Subtype.ext (p.apply_symm_apply j.val)

def fixedBlockPermutation (p : Fin n ≃ Fin n) (V : Finset (Fin n →₀ ℕ)) (k : ℕ) :
    fixedSelectorBlock V k ≃ fixedSelectorBlock (fixedPermutedVertices p V) k where
  toFun j := ⟨p j.val, by
    obtain ⟨a, ha, hai⟩ := j.property
    exact ⟨fixedVertexPermutation p V a, (permute_degree p a.val).symm ▸ ha,
      by rwa [fixedVertexPermutation_coeff]⟩⟩
  invFun j := ⟨p.symm j.val, by
    obtain ⟨a, ha, hai⟩ := j.property
    obtain ⟨a, rfl⟩ := (fixedVertexPermutation p V).surjective a
    refine ⟨a, ?_, ?_⟩
    · change normalExponentDegree (Finsupp.domCongr p a.val) ≤ k at ha
      simpa only [permute_degree] using ha
    · have hc := fixedVertexPermutation_coeff p V a (p.symm j.val)
      rw [Equiv.apply_symm_apply] at hc
      rwa [hc] at hai⟩
  left_inv j := Subtype.ext (p.symm_apply_apply j.val)
  right_inv j := Subtype.ext (p.apply_symm_apply j.val)

/-- Transported original labels, never a new choice on the changed raw set. -/
def actualFixedSelectorPermutation (p : Fin n ≃ Fin n) {V : Finset (Fin n →₀ ℕ)}
    (S : ActualFixedInheritedSelector V) : ActualFixedInheritedSelector (fixedPermutedVertices p V) where
  selected j := fixedVertexPermutation p V (S.selected ((fixedEssentialPermutation p V).symm j))
  positive j := by
    obtain ⟨j, rfl⟩ := (fixedEssentialPermutation p V).surjective j
    change (fixedVertexPermutation p V
      (S.selected ((fixedEssentialPermutation p V).symm (fixedEssentialPermutation p V j)))).val (p j.val) ≠ 0
    rw [Equiv.symm_apply_apply, fixedVertexPermutation_coeff]
    exact S.positive j
  least_degree j a ha := by
    obtain ⟨j, rfl⟩ := (fixedEssentialPermutation p V).surjective j
    obtain ⟨a, rfl⟩ := (fixedVertexPermutation p V).surjective a
    change (fixedVertexPermutation p V a).val (p j.val) ≠ 0 at ha
    rw [fixedVertexPermutation_coeff] at ha
    change normalExponentDegree (Finsupp.domCongr p
      (S.selected ((fixedEssentialPermutation p V).symm (fixedEssentialPermutation p V j))).val) ≤
        normalExponentDegree (Finsupp.domCongr p a.val)
    rw [Equiv.symm_apply_apply, permute_degree, permute_degree]
    exact S.least_degree j a ha

theorem fixedSelectorBeta_permutation (p : Fin n ≃ Fin n) {V : Finset (Fin n →₀ ℕ)}
    (S : ActualFixedInheritedSelector V) (j : fixedSelectorEssential V) :
    fixedSelectorBeta (actualFixedSelectorPermutation p S) (fixedEssentialPermutation p V j) =
      Finsupp.domCongr p (fixedSelectorBeta S j) := by
  change Finsupp.domCongr p
      (S.selected ((fixedEssentialPermutation p V).symm (fixedEssentialPermutation p V j))).val -
        Finsupp.single (p j.val) 1 =
      Finsupp.domCongr p ((S.selected j).val - Finsupp.single j.val 1)
  rw [Equiv.symm_apply_apply]
  ext i
  simp only [Finsupp.tsub_apply, permute_apply]
  by_cases hi : i = p j.val
  · subst i
    simp
  · have hj : p.symm i ≠ j.val := by
      intro h
      exact hi (by simpa only [Equiv.apply_symm_apply] using congrArg p h)
    simp only [Finsupp.single_eq_of_ne hi, Finsupp.single_eq_of_ne hj]

def actualPermutedSelectorFamily (p : Fin n ≃ Fin n) {V : Finset (Fin n →₀ ℕ)}
    (G : V → HolGerm (ComplexModel n)) : fixedPermutedVertices p V → HolGerm (ComplexModel n) :=
  fun a => actualPermutationGermEquiv p (G ((fixedVertexPermutation p V).symm a))

theorem actualFixedSelectorDerivative_permutation (p : Fin n ≃ Fin n) {V : Finset (Fin n →₀ ℕ)}
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel n)) (j : fixedSelectorEssential V) :
    actualFixedSelectorDerivative (actualFixedSelectorPermutation p S) (actualPermutedSelectorFamily p G)
        (fixedEssentialPermutation p V j) =
      actualPermutationGermEquiv p (actualFixedSelectorDerivative S G j) := by
  rw [actualFixedSelectorDerivative, fixedSelectorBeta_permutation]
  simp only [actualFixedSelectorPermutation, Equiv.symm_apply_apply, actualPermutedSelectorFamily]
  exact actualAnalyticMultiDerivative_permutation p _ _

theorem map_coordinateIdeal_actualPermutation (p : Fin n ≃ Fin n) (B : Set (Fin n)) :
    Ideal.map (actualPermutationGermEquiv p).toRingEquiv.toRingHom (actualAnalyticCoordinateBlockIdeal B) =
      actualAnalyticCoordinateBlockIdeal (p '' B) := by
  rw [actualAnalyticCoordinateBlockIdeal, Ideal.map_span, actualAnalyticCoordinateBlockIdeal,
    Set.image_image, Set.image_image]
  congr 1

private theorem block_image (p : Fin n ≃ Fin n) (V : Finset (Fin n →₀ ℕ)) (k : ℕ) :
    p '' fixedSelectorBlock V k = fixedSelectorBlock (fixedPermutedVertices p V) k := by
  ext i
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact (fixedBlockPermutation p V k ⟨j,hj⟩).property
  · intro hi
    let j := (fixedBlockPermutation p V k).symm ⟨i,hi⟩
    exact ⟨j.val, j.property, congrArg Subtype.val ((fixedBlockPermutation p V k).apply_symm_apply ⟨i,hi⟩)⟩

theorem actualFixedSelectorContact_permutation (p : Fin n ≃ Fin n) {V : Finset (Fin n →₀ ℕ)}
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel n)) (k : ℕ)
    (hadapt : actualFixedSelectorContactAt S G k) :
    actualFixedSelectorContactAt (actualFixedSelectorPermutation p S) (actualPermutedSelectorFamily p G) k := by
  intro j
  obtain ⟨j, rfl⟩ := (fixedBlockPermutation p V k).surjective j
  have he : fixedSelectorBlockEssential k (fixedBlockPermutation p V k j) =
      fixedEssentialPermutation p V (fixedSelectorBlockEssential k j) := Subtype.ext rfl
  rw [he, actualFixedSelectorDerivative_permutation]
  have hm := Ideal.mem_map_of_mem (actualPermutationGermEquiv p).toRingEquiv.toRingHom (hadapt j)
  rwa [map_coordinateIdeal_actualPermutation, block_image] at hm

private theorem permute_single (p : Fin n ≃ Fin n) (i : Fin n) :
    Finsupp.domCongr p (Finsupp.single i 1) = Finsupp.single (p i) 1 := by
  ext j
  rw [permute_apply]
  by_cases hj : j = p i
  · subst j
    simp
  · have hi : p.symm j ≠ i := by intro h; exact hj (by simpa using congrArg p h)
    simp [Finsupp.single_eq_of_ne hj, Finsupp.single_eq_of_ne hi]

private theorem analytic_single (i : Fin n) (F : HolGerm (ComplexModel n)) :
    actualAnalyticMultiDerivative (Finsupp.single i 1) F = actualAnalyticCoordinateDerivative i F := by
  apply actualUnshiftedTaylorAlgHom_injective n
  rw [actualTaylor_actualAnalyticMultiDerivative, actualTaylor_actualAnalyticCoordinateDerivative]
  simpa only [zero_add, actualFormalMultiDerivative_zero] using
    actualFormalMultiDerivative_add_single 0 i (actualUnshiftedTaylorAlgHom n F)

private theorem analytic_partial_permutation (p : Fin n ≃ Fin n) (i : Fin n) (F : HolGerm (ComplexModel n)) :
    actualAnalyticCoordinateDerivative (p i) (actualPermutationGermEquiv p F) =
      actualPermutationGermEquiv p (actualAnalyticCoordinateDerivative i F) := by
  have h := actualAnalyticMultiDerivative_permutation p (Finsupp.single i 1) F
  rwa [permute_single, analytic_single, analytic_single] at h

private theorem eval_permutation (p : Fin n ≃ Fin n) (F : HolGerm (ComplexModel n)) :
    HolGerm.eval (actualPermutationGermEquiv p F) = HolGerm.eval F := by
  rw [← actualTaylor_coeff_zero, actualTaylor_actualPermutationGermEquiv, ← actualTaylor_coeff_zero]
  simpa only [map_zero] using coeff_rename p (actualUnshiftedTaylorAlgHom n F) 0

/-- Actual derivative/evaluation entries, with the SAME fixed selector, agree. -/
theorem actualFixedSelectorJacobian_permutation (p : Fin n ≃ Fin n) {V : Finset (Fin n →₀ ℕ)}
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel n)) (k : ℕ) :
    (actualFixedSelectorJacobian (actualFixedSelectorPermutation p S) (actualPermutedSelectorFamily p G) k).submatrix
      (fixedBlockPermutation p V k) (fixedBlockPermutation p V k) = actualFixedSelectorJacobian S G k := by
  ext j i
  have he : fixedSelectorBlockEssential k (fixedBlockPermutation p V k j) =
      fixedEssentialPermutation p V (fixedSelectorBlockEssential k j) := Subtype.ext rfl
  change HolGerm.eval (actualAnalyticCoordinateDerivative (p i.val)
    (actualFixedSelectorDerivative (actualFixedSelectorPermutation p S) (actualPermutedSelectorFamily p G)
      (fixedSelectorBlockEssential k (fixedBlockPermutation p V k j)))) = _
  rw [he, actualFixedSelectorDerivative_permutation, analytic_partial_permutation, eval_permutation]
  rfl

theorem actualFixedSelectorJacobian_permutation_det (p : Fin n ≃ Fin n) {V : Finset (Fin n →₀ ℕ)}
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel n)) (k : ℕ) :
    (actualFixedSelectorJacobian (actualFixedSelectorPermutation p S) (actualPermutedSelectorFamily p G) k).det =
      (actualFixedSelectorJacobian S G k).det := by
  rw [← Matrix.det_submatrix_equiv_self (fixedBlockPermutation p V k), actualFixedSelectorJacobian_permutation]

end
end Hironaka.HironakaActualFixedInheritedSelectorPermutation
