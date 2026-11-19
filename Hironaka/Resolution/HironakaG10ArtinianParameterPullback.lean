import Hironaka.Resolution.HironakaActualRelativeCoefficientGerms
import Hironaka.Resolution.HironakaActualJointBaseFibre
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Actual nilpotent parameter substitution on the whole joint germ algebra

An ordinary base-germ algebra homomorphism killing a maximal-ideal power
internally constructs substitution into the whole tensor fibre-germ algebra.
Both original scalar maps and the actual finite relative coefficients are
retained. No norm, finite-dimensionality, or base-change-map certificate is
assumed. Compact holomorphic realization and persistence are separate steps.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology TensorProduct

namespace Hironaka.HironakaG10ArtinianParameterPullback

open HolGerm HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetChartInvariance HironakaRelativeNormalIdeal
  HironakaRelativeNormalMonomialBasis HironakaRelativeNormalPolynomialJetAlgebra
  HironakaActualRelativeCoefficientGerms HironakaActualCentreJointJets
  HironakaActualJointBaseFibre

noncomputable section

private def swapLinear (d t : ℕ) : ComplexModel (d+t) ≃L[ℂ] ComplexModel (t+d) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (finAddFlip : Fin (d+t) ≃ Fin (t+d))).toContinuousLinearEquiv

private theorem swapLinear_first (d t : ℕ) (w : ComplexModel (d+t)) (i : Fin t) :
    swapLinear d t w (i.castAdd d) = w (i.natAdd d) := by
  change w ((finAddFlip : Fin (d+t) ≃ Fin (t+d)).symm (i.castAdd d)) = _
  rw [(finAddFlip : Fin (d+t) ≃ Fin (t+d)).symm_apply_eq.mpr
    (finAddFlip_apply_natAdd i d).symm]

private theorem swapLinear_second (d t : ℕ) (w : ComplexModel (d+t)) (i : Fin d) :
    swapLinear d t w (i.natAdd t) = w (i.castAdd t) := by
  change w ((finAddFlip : Fin (d+t) ≃ Fin (t+d)).symm (i.natAdd t)) = _
  rw [(finAddFlip : Fin (d+t) ≃ Fin (t+d)).symm_apply_eq.mpr
    (finAddFlip_apply_castAdd i t).symm]

/-- Actual whole-germ pullback by interchange of the original coordinate blocks. -/
def swapParameterFibre (d t : ℕ) :
    HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (t+d)) where
  toRingEquiv := HolGerm.comapEquiv (swapLinear t d)
  commutes' _ := rfl

/-- Original base scalars become actual normal scalars after the permutation. -/
theorem swapParameterFibre_base (d t : ℕ) (a : HolGerm (ComplexModel d)) :
    swapParameterFibre d t (tangentPullback d t a) = jointNormalPullback t d a := by
  induction a using HolGerm.induction_on with
  | h f hf =>
    change HolGerm.comapEquiv (swapLinear t d) (tangentPullback d t (HolGerm.mk f hf)) = _
    unfold tangentPullback jointNormalPullback
    rw [compAlgHom_mk, HolGerm.comapEquiv_mk, compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro w
    apply congrArg f
    ext i
    exact swapLinear_first t d w i

/-- Original fibre scalars become the tangential coefficient germs after the permutation. -/
theorem swapParameterFibre_fibre (d t : ℕ) (h : HolGerm (ComplexModel t)) :
    swapParameterFibre d t (jointNormalPullback d t h) = tangentPullback t d h := by
  induction h using HolGerm.induction_on with
  | h f hf =>
    change HolGerm.comapEquiv (swapLinear t d) (jointNormalPullback d t (HolGerm.mk f hf)) = _
    unfold tangentPullback jointNormalPullback
    rw [compAlgHom_mk, HolGerm.comapEquiv_mk, compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro w
    apply congrArg f
    ext i
    exact swapLinear_second t d w i

/-- The genuine original parameter coefficient, as a whole fibre germ,
obtained after actual interchange of the original blocks. -/
def parameterCoefficientGerm (d t : ℕ) (g : HolGerm (ComplexModel (d+t)))
    (α : Fin d →₀ ℕ) : HolGerm (ComplexModel t) :=
  actualNormalAnalyticCoefficientGerm t d (swapParameterFibre d t g) α

private theorem algHom_eq_of_coordinate_images_of_kills_power {d : ℕ} {B : Type*}
    [CommRing B] [Algebra ℂ B] (N : ℕ)
    (f g : HolGerm (ComplexModel d) →ₐ[ℂ] B)
    (hf : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ N ≤ RingHom.ker f.toRingHom)
    (hg : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ N ≤ RingHom.ker g.toRingHom)
    (hcoord : ∀ i : Fin d, f (coordinateGerm i) = g (coordinateGerm i)) : f = g := by
  have hspan (p : HolGerm (ComplexModel d)) (hp : p ∈ monomialSpan d N) : f p = g p := by
    apply Submodule.span_induction (p := fun p _ => f p = g p) ?_ ?_ ?_ ?_ hp
    · rintro p ⟨w, rfl⟩
      simp only [wordMonomial, map_prod]
      exact Finset.prod_congr rfl fun i _ => hcoord (w.2 i)
    · simp
    · intro p r _ _ hp hr
      rw [map_add, map_add, hp, hr]
    · intro c p _ hp
      rw [map_smul, map_smul, hp]
  apply AlgHom.ext
  intro a
  obtain ⟨p, hp, hrem⟩ := exists_monomial_representative N a
  have hf0 : f (a-p) = 0 := hf hrem
  have hg0 : g (a-p) = 0 := hg hrem
  rw [map_sub, sub_eq_zero] at hf0 hg0
  exact hf0.trans ((hspan p hp).trans hg0.symm)

section Construction

variable {Γ : Type*} [CommRing Γ] [Algebra ℂ Γ]
  (d t q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
  (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
    RingHom.ker φ.toRingHom)

local instance : Algebra (HolGerm (ComplexModel t)) (HolGerm (ComplexModel (t+d))) :=
  tangentAlgebra t d
local instance : IsScalarTower ℂ (HolGerm (ComplexModel t)) (HolGerm (ComplexModel (t+d))) :=
  IsScalarTower.of_algHom (tangentPullback t d)
local instance : Algebra (HolGerm (ComplexModel t)) (Γ ⊗[ℂ] HolGerm (ComplexModel t)) :=
  Algebra.TensorProduct.rightAlgebra
local instance : IsScalarTower ℂ (HolGerm (ComplexModel t)) (Γ ⊗[ℂ] HolGerm (ComplexModel t)) :=
  Algebra.TensorProduct.right_isScalarTower

/-- Actual relative polynomial evaluation at the original nilpotent parameter images. -/
def parameterPolynomialEval :
    MvPolynomial (Fin d) (HolGerm (ComplexModel t)) →ₐ[HolGerm (ComplexModel t)]
      (Γ ⊗[ℂ] HolGerm (ComplexModel t)) :=
  MvPolynomial.aeval fun i => φ (coordinateGerm i) ⊗ₜ[ℂ] (1 : HolGerm (ComplexModel t))

include hφ in
private theorem parameterPolynomialEval_kills_power :
    actualPolynomialNormalIdeal t d ^ (q+1) ≤
      RingHom.ker (parameterPolynomialEval d t φ).toRingHom := by
  let u : HolGerm (ComplexModel d) →ₐ[ℂ] (Γ ⊗[ℂ] HolGerm (ComplexModel t)) :=
    (Algebra.TensorProduct.includeLeft : Γ →ₐ[ℂ] _).comp φ
  have hm : Ideal.map u.toRingHom
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1)) = ⊥ := by
    apply (Ideal.map_eq_bot_iff_le_ker _).mpr
    intro a ha
    change (Algebra.TensorProduct.includeLeft : Γ →ₐ[ℂ]
      (Γ ⊗[ℂ] HolGerm (ComplexModel t))) (φ a) = 0
    rw [show φ a = 0 from hφ ha, map_zero]
  have hmap : Ideal.map (parameterPolynomialEval d t φ).toRingHom
      (actualPolynomialNormalIdeal t d) ≤
      Ideal.map u.toRingHom (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) := by
    rw [actualPolynomialNormalIdeal, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hi : coordinateGerm i ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) :=
      (HolGerm.mem_maximalIdeal_iff _).mpr rfl
    simpa [parameterPolynomialEval, u] using Ideal.mem_map_of_mem u.toRingHom hi
  apply (Ideal.map_eq_bot_iff_le_ker _).mp
  apply le_antisymm ?_ bot_le
  rw [Ideal.map_pow]
  calc
    _ ≤ (Ideal.map u.toRingHom (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)))) ^ (q+1) :=
      pow_le_pow_left' hmap (q+1)
    _ = ⊥ := by rw [← Ideal.map_pow, hm]

/-- Actual relative polynomial-jet substitution with internally derived nilpotence. -/
def normalParameterPullback :
    HolGerm (ComplexModel (t+d)) →ₐ[HolGerm (ComplexModel t)]
      (Γ ⊗[ℂ] HolGerm (ComplexModel t)) :=
  (Ideal.Quotient.liftₐ (actualPolynomialNormalIdeal t d ^ (q+1))
    (parameterPolynomialEval d t φ)
      (fun _ ha => parameterPolynomialEval_kills_power d t q φ hφ ha)).comp
      (actualWholePolynomialJet t d (q+1))

/-- Substitution on a relative polynomial is the literal polynomial evaluation. -/
theorem normalParameterPullback_polynomial
    (P : MvPolynomial (Fin d) (HolGerm (ComplexModel t))) :
    normalParameterPullback d t q φ hφ (normalPolynomialEval t d P) =
      parameterPolynomialEval d t φ P := by
  unfold normalParameterPullback
  rw [AlgHom.comp_apply, actualWholePolynomialJet_evaluation]
  rfl

private theorem parameterPolynomialEval_monomial (α : Fin d →₀ ℕ)
    (c : HolGerm (ComplexModel t)) :
    parameterPolynomialEval d t φ (MvPolynomial.monomial α c) =
      (∏ i : Fin d, φ (coordinateGerm i) ^ α i) ⊗ₜ[ℂ] c := by
  classical
  rw [parameterPolynomialEval, MvPolynomial.aeval_monomial]
  change ((1 : Γ) ⊗ₜ[ℂ] c) *
    α.prod (fun i k => ((Algebra.TensorProduct.includeLeft : Γ →ₐ[ℂ]
      (Γ ⊗[ℂ] HolGerm (ComplexModel t))) (φ (coordinateGerm i))) ^ k) = _
  rw [α.prod_fintype (fun i k => ((Algebra.TensorProduct.includeLeft : Γ →ₐ[ℂ]
    (Γ ⊗[ℂ] HolGerm (ComplexModel t))) (φ (coordinateGerm i))) ^ k) (fun _ => pow_zero _)]
  have hp : (∏ i : Fin d, ((Algebra.TensorProduct.includeLeft : Γ →ₐ[ℂ]
      (Γ ⊗[ℂ] HolGerm (ComplexModel t))) (φ (coordinateGerm i))) ^ α i) =
      (Algebra.TensorProduct.includeLeft : Γ →ₐ[ℂ] (Γ ⊗[ℂ] HolGerm (ComplexModel t)))
        (∏ i : Fin d, φ (coordinateGerm i) ^ α i) := by
    simp only [map_prod, map_pow]
  rw [hp, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- The entire actual normal-coordinate power is killed by the constructed substitution. -/
theorem normalParameterPullback_kills_power
    (g : HolGerm (ComplexModel (t+d))) (hg : g ∈ normalIdeal t d ^ (q+1)) :
    normalParameterPullback d t q φ hφ g = 0 := by
  have hz : actualWholePolynomialJet t d (q+1) g = 0 := by
    change (actualPolynomialJetAlgebraEquiv t d (q+1)).symm
      (Ideal.Quotient.mk (normalIdeal t d ^ (q+1)) g) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]
  simp only [normalParameterPullback, AlgHom.comp_apply, hz, map_zero]

private theorem normalPolynomialEval_C (c : HolGerm (ComplexModel t)) :
    normalPolynomialEval t d (MvPolynomial.C c) = tangentPullback t d c := by
  rw [normalPolynomialEval, MvPolynomial.aeval_C]
  rfl

private theorem normalParameterPullback_tangent (c : HolGerm (ComplexModel t)) :
    normalParameterPullback d t q φ hφ (tangentPullback t d c) = 1 ⊗ₜ[ℂ] c := by
  rw [← normalPolynomialEval_C d t c, normalParameterPullback_polynomial]
  simp only [parameterPolynomialEval, MvPolynomial.aeval_C]
  rfl

private theorem normalParameterPullback_coordinate (i : Fin d) :
    normalParameterPullback d t q φ hφ (normalCoordinate t d i) =
      φ (coordinateGerm i) ⊗ₜ[ℂ] (1 : HolGerm (ComplexModel t)) := by
  have he : normalPolynomialEval t d (MvPolynomial.X i) = normalCoordinate t d i := by
    simp only [normalPolynomialEval, MvPolynomial.aeval_X]
  rw [← he, normalParameterPullback_polynomial]
  simp only [parameterPolynomialEval, MvPolynomial.aeval_X]

private theorem jointNormalPullback_coordinate (i : Fin d) :
    jointNormalPullback t d (coordinateGerm i) = normalCoordinate t d i := by
  unfold jointNormalPullback coordinateGerm normalCoordinate
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun _ => rfl

private theorem jointNormalPullback_map_maximal_le :
    Ideal.map (jointNormalPullback t d).toRingHom
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) ≤ normalIdeal t d := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro g hg
  obtain ⟨a, he⟩ := exists_coordinate_decomposition g
  have hz : HolGerm.eval g = 0 := (HolGerm.mem_maximalIdeal_iff g).mp hg
  rw [hz, map_zero, zero_add] at he
  change jointNormalPullback t d g ∈ normalIdeal t d
  rw [he, map_sum]
  apply Ideal.sum_mem
  intro i _
  rw [map_mul, jointNormalPullback_coordinate]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

private theorem normalParameterPullback_base (a : HolGerm (ComplexModel d)) :
    normalParameterPullback d t q φ hφ (jointNormalPullback t d a) =
      φ a ⊗ₜ[ℂ] (1 : HolGerm (ComplexModel t)) := by
  let f : HolGerm (ComplexModel d) →ₐ[ℂ] (Γ ⊗[ℂ] HolGerm (ComplexModel t)) :=
    (normalParameterPullback d t q φ hφ).restrictScalars ℂ |>.comp (jointNormalPullback t d)
  let h : HolGerm (ComplexModel d) →ₐ[ℂ] (Γ ⊗[ℂ] HolGerm (ComplexModel t)) :=
    (Algebra.TensorProduct.includeLeft : Γ →ₐ[ℂ] _).comp φ
  have hf : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker f.toRingHom := by
    intro g hg
    apply normalParameterPullback_kills_power d t q φ hφ
    have hm := Ideal.mem_map_of_mem (jointNormalPullback t d).toRingHom hg
    rw [Ideal.map_pow] at hm
    exact (pow_le_pow_left' (jointNormalPullback_map_maximal_le d t) (q+1)) hm
  have hh : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker h.toRingHom := by
    intro g hg
    change (φ g) ⊗ₜ[ℂ] (1 : HolGerm (ComplexModel t)) = 0
    rw [show φ g = 0 from hφ hg, TensorProduct.zero_tmul]
  have he := algHom_eq_of_coordinate_images_of_kills_power (q+1) f h hf hh (fun i => by
    change normalParameterPullback d t q φ hφ (jointNormalPullback t d (coordinateGerm i)) = _
    rw [jointNormalPullback_coordinate, normalParameterPullback_coordinate]
    rfl)
  exact congrArg (fun u : HolGerm (ComplexModel d) →ₐ[ℂ] _ => u a) he

/-- The internally constructed nilpotent substitution on the whole original
base-first joint germ algebra. -/
def actualArtinianParameterPullback :
    HolGerm (ComplexModel (d+t)) →ₐ[ℂ] (Γ ⊗[ℂ] HolGerm (ComplexModel t)) :=
  ((normalParameterPullback d t q φ hφ).restrictScalars ℂ).comp
    (swapParameterFibre d t).toAlgHom

/-- The whole original base scalar map is exactly the given ordinary φ. -/
theorem actualArtinianParameterPullback_base (a : HolGerm (ComplexModel d)) :
    actualArtinianParameterPullback d t q φ hφ (tangentPullback d t a) =
      φ a ⊗ₜ[ℂ] (1 : HolGerm (ComplexModel t)) := by
  change normalParameterPullback d t q φ hφ
    (swapParameterFibre d t (tangentPullback d t a)) = _
  rw [swapParameterFibre_base, normalParameterPullback_base]

/-- The whole original fibre scalar map is exactly inclusion into the right tensor factor. -/
theorem actualArtinianParameterPullback_fibre (c : HolGerm (ComplexModel t)) :
    actualArtinianParameterPullback d t q φ hφ (jointNormalPullback d t c) = 1 ⊗ₜ[ℂ] c := by
  change normalParameterPullback d t q φ hφ
    (swapParameterFibre d t (jointNormalPullback d t c)) = _
  rw [swapParameterFibre_fibre, normalParameterPullback_tangent]

/-- Nilpotent substitution retains exactly the actual finite original
relative coefficient germs, including either empty coordinate block. -/
theorem actualArtinianParameterPullback_eq_sum (g : HolGerm (ComplexModel (d+t))) :
    letI := normalExponentFintype d (q+1)
    actualArtinianParameterPullback d t q φ hφ g =
      ∑ α : normalExponentIndex d (q+1),
        (∏ i : Fin d, φ (coordinateGerm i) ^ α.val i) ⊗ₜ[ℂ]
          parameterCoefficientGerm d t g α.val := by
  let := normalExponentFintype d (q+1)
  let F := swapParameterFibre d t g
  change normalParameterPullback d t q φ hφ F = _
  have hz := normalParameterPullback_kills_power d t q φ hφ
    (F - normalPolynomialEval t d (actualNormalTaylorPolynomial t d (q+1) F))
    (actualNormalTaylorPolynomial_remainder t d (q+1) F)
  rw [map_sub, sub_eq_zero] at hz
  rw [hz, normalParameterPullback_polynomial]
  simp only [actualNormalTaylorPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [parameterPolynomialEval_monomial]
  have hc : actualNormalJetCoordinates t d (q+1) F α =
      actualNormalAnalyticCoefficientGerm t d F α.val := by
    rw [← actualNormalTaylorPolynomial_coefficient t d (q+1) F α,
      actualNormalTaylorPolynomial_coefficient_eq_germ t d (q+1) F α.val α.property]
  rw [hc]
  rfl

end Construction

end
end Hironaka.HironakaG10ArtinianParameterPullback
