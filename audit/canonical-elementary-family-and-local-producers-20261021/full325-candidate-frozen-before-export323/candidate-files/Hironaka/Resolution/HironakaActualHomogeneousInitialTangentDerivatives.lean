/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFirstSymbolTangentClosure
import Hironaka.Resolution.HironakaActualHomogeneousInitialHS
import Hironaka.Resolution.HironakaActualOriginalTaylorDerivatives
import Hironaka.Resolution.HironakaActualCoefficientPresentationCentrePower
import Hironaka.Resolution.HironakaActualAnalyticVertexBasis

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHomogeneousInitialTangentDerivatives
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaRelativeNormalIdeal
  HironakaRelativeNormalTaylorCoefficients HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalActualBaseJetDimension HironakaActualOriginalTaylorPolynomial
  HironakaActualOriginalFormalTaylor HironakaActualFormalIdealContraction
  HironakaActualOriginalFormalHSTransfer HironakaActualFormalInitialDiagram
  HironakaActualHomogeneousInitialHS HironakaActualOriginalTaylorDerivatives
  HironakaActualFirstSymbolTangentClosure HironakaActualCoefficientPresentationCentrePower
  HironakaActualAnalyticVertexBasis
  Hironaka.HolomorphicIdealSheaves OkaRelationSheaf HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaSmoothCentreRealDomainOriginalStalkFreeness
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations

attribute [local instance 2000] IsOrderedRing.toIsOrderedAddMonoid in
/-- The WHOLE genuine initial ideal contains each true degree-q component of an original ideal member of order at least q. -/
theorem homogeneousComponent_mem_actual_initial_of_mem_power {n : ℕ}
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ K) (hpow : F ∈ genuineFormalVariables n ^ q) :
    MvPowerSeries.homogeneousComponent q F ∈ actualHomogeneousInitialIdeal K := by
  by_cases hzero : F = 0
  · rw [hzero, map_zero]
    exact Ideal.zero_mem _
  let d := actualHomogeneousInitialDegree F hzero
  have hqd : q ≤ d := by
    by_contra h
    have hz := (mem_genuineFormalVariables_pow_iff_coefficients_zero n q F).mp hpow
      (actualInitialExponent MonomialOrder.degLex F hzero) (lt_of_not_ge h)
    exact (actualInitialExponent_spec MonomialOrder.degLex F hzero).1 hz
  by_cases he : d = q
  · rw [← he]
    exact Ideal.subset_span ⟨⟨F, hF, hzero⟩, rfl⟩
  · have hlt : q < d := lt_of_le_of_ne hqd (Ne.symm he)
    have ho : (q : ℕ∞) < F.order := by
      rw [← actualHomogeneousInitialDegree_eq_order F hzero]
      exact_mod_cast hlt
    rw [MvPowerSeries.homogeneousComponent_of_lt_order_eq_zero ho]
    exact Ideal.zero_mem _

/-- Actual total homogeneous selection and literal formal partial differentiation commute at successive degrees. -/
theorem pderiv_homogeneousComponent_succ {n : ℕ} (q : ℕ) (i : Fin n)
    (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries.pderiv ℂ i (MvPowerSeries.homogeneousComponent (q+1) F) =
      MvPowerSeries.homogeneousComponent q (MvPowerSeries.pderiv ℂ i F) := by
  apply MvPowerSeries.ext
  intro α
  have hd : Finsupp.degree (α+Finsupp.single i 1) = Finsupp.degree α+1 := by
    simp [Finsupp.degree_eq_weight_one, Finsupp.weight_single]
  simp only [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_homogeneousComponent]
  rw [hd]
  by_cases h : Finsupp.degree α = q <;> simp [h]

/-- The literal actual constant component has zero partial derivative. -/
theorem pderiv_homogeneousComponent_zero {n : ℕ} (i : Fin n)
    (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries.pderiv ℂ i (MvPowerSeries.homogeneousComponent 0 F) = 0 := by
  apply MvPowerSeries.ext
  intro α
  have hd : Finsupp.degree (α+Finsupp.single i 1) = Finsupp.degree α+1 := by
    simp [Finsupp.degree_eq_weight_one, Finsupp.weight_single]
  simp [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_homogeneousComponent, hd]

attribute [local instance 2000] IsOrderedRing.toIsOrderedAddMonoid in
attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- Actual original first-symbol closure preserves the ENTIRE SAME homogeneous initial ideal, including all formal generators. -/
theorem actual_homogeneous_initial_ideal_pderiv_of_first_symbol_closure (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel (0+n)))) (i : Fin n)
    (hclosure : ∀ q : ℕ, 0 < q → ∀ g ∈ I,
      g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q →
      iteratedDerivativeGerm [normalVector 0 n i] g ∈
        I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q)
    (H : MvPowerSeries (Fin n) ℂ)
    (hH : H ∈ actualHomogeneousInitialIdeal (Ideal.map (originalTaylorAlgHom n).toRingHom I)) :
    MvPowerSeries.pderiv ℂ i H ∈
      actualHomogeneousInitialIdeal (Ideal.map (originalTaylorAlgHom n).toRingHom I) := by
  let K := Ideal.map (originalTaylorAlgHom n).toRingHom I
  let J := actualHomogeneousInitialIdeal K
  have hgen (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ K) (hne : F ≠ 0) :
      MvPowerSeries.pderiv ℂ i (actualHomogeneousInitialForm F hne) ∈ J := by
    let d := actualHomogeneousInitialDegree F hne
    have hFP : F ∈ genuineFormalVariables n ^ d := by
      apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n d F).mpr
      intro α hα
      apply MvPowerSeries.coeff_of_lt_order
      rw [← actualHomogeneousInitialDegree_eq_order F hne]
      have hdegree : Finsupp.degree α < actualHomogeneousInitialDegree F hne := by
        simpa only [d, normalExponentDegree, Finsupp.degree_eq_sum] using hα
      exact_mod_cast hdegree
    cases hd : d with
    | zero =>
      change MvPowerSeries.pderiv ℂ i (MvPowerSeries.homogeneousComponent d F) ∈ J
      rw [hd, pderiv_homogeneousComponent_zero]
      exact Ideal.zero_mem _
    | succ k =>
      rw [hd] at hFP
      obtain ⟨g, hgI, hcoeff⟩ := exists_original_ideal_member_jet_lift n I F hF (k+1+1)
      have hgpow : g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (k+1) := by
        apply (mem_original_maximal_pow_iff_formal_coefficients_zero n (k+1) g).mpr
        intro α hα
        rw [hcoeff α (by omega)]
        exact (mem_genuineFormalVariables_pow_iff_coefficients_zero n (k+1) F).mp hFP α hα
      have hHC : MvPowerSeries.homogeneousComponent (k+1) (originalTaylorAlgHom n g) =
          MvPowerSeries.homogeneousComponent (k+1) F := by
        apply MvPowerSeries.ext
        intro α
        simp only [MvPowerSeries.coeff_homogeneousComponent]
        split_ifs with hα
        · apply hcoeff α
          have he : normalExponentDegree α = k+1 := by
            simpa only [normalExponentDegree, Finsupp.degree_eq_sum] using hα
          omega
        · rfl
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hclosure (k+1) (by omega) g hgI hgpow)
      have hDpow : iteratedDerivativeGerm [normalVector 0 n i] g ∈
          IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ k := by
        let := tangentAlgebra 0 n
        have hgn : g ∈ normalIdeal 0 n ^ (k+1) := by
          rw [zeroTangentNormalIdeal_eq_maximalIdeal]
          exact hgpow
        have hz := normalDerivation_mem_normalIdeal_pow 0 n k i g hgn
        rw [zeroTangentNormalIdeal_eq_maximalIdeal] at hz
        exact hz
      have hapow : a ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ k := by
        have hbk : b ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ k :=
          Ideal.pow_le_pow_right (by omega) hb
        have he : a = iteratedDerivativeGerm [normalVector 0 n i] g - b := by rw [← hab]; abel
        rw [he]
        exact Ideal.sub_mem _ hDpow hbk
      have hbHC : MvPowerSeries.homogeneousComponent k (originalTaylorAlgHom n b) = 0 := by
        apply MvPowerSeries.ext
        intro α
        rw [MvPowerSeries.coeff_homogeneousComponent, map_zero]
        split_ifs with hα
        · apply (mem_original_maximal_pow_iff_formal_coefficients_zero n (k+1) b).mp hb α
          have he : normalExponentDegree α = k := by
            simpa only [normalExponentDegree, Finsupp.degree_eq_sum] using hα
          omega
        · rfl
      have hAP : originalTaylorAlgHom n a ∈ genuineFormalVariables n ^ k := by
        change originalTaylorAlgHom n a ∈ Ideal.span (range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) ℂ)) ^ k
        rw [← map_original_maximal_pow_eq_formal_variables_pow n k]
        exact Ideal.mem_map_of_mem _ hapow
      have hID : MvPowerSeries.pderiv ℂ i (actualHomogeneousInitialForm F hne) =
          MvPowerSeries.homogeneousComponent k (originalTaylorAlgHom n a) := by
        change MvPowerSeries.pderiv ℂ i (MvPowerSeries.homogeneousComponent d F) = _
        rw [hd, ← hHC, pderiv_homogeneousComponent_succ,
          ← originalTaylorAlgHom_coordinate_derivative]
        rw [← hab, map_add, map_add, hbHC, add_zero]
      rw [hID]
      exact homogeneousComponent_mem_actual_initial_of_mem_power K k (originalTaylorAlgHom n a)
        (Ideal.mem_map_of_mem _ ha) hAP
  change H ∈ Ideal.span _ at hH
  induction hH using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨G, rfl⟩ := hF
    exact hgen G.val G.property.1 G.property.2
  | zero =>
    rw [map_zero]
    exact J.zero_mem
  | add F G _ _ hF hG => simpa only [map_add] using J.add_mem hF hG
  | smul A F hF ih =>
    change MvPowerSeries.pderiv ℂ i (A*F) ∈ J
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact J.add_mem (J.mul_mem_left A ih) (J.mul_mem_right _ hF)

/-- Literal ORIGINAL polynomial pderiv preserves membership in the SAME actual homogeneous initial ideal under genuine inclusion. -/
theorem actual_polynomial_pderiv_mem_initial_of_first_symbol_closure (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel (0+n)))) (i : Fin n)
    (hclosure : ∀ q : ℕ, 0 < q → ∀ g ∈ I,
      g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q →
      iteratedDerivativeGerm [normalVector 0 n i] g ∈
        I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q)
    (P : MvPolynomial (Fin n) ℂ)
    (hP : (P : MvPowerSeries (Fin n) ℂ) ∈
      actualHomogeneousInitialIdeal (Ideal.map (originalTaylorAlgHom n).toRingHom I)) :
    (MvPolynomial.pderiv i P : MvPowerSeries (Fin n) ℂ) ∈
      actualHomogeneousInitialIdeal (Ideal.map (originalTaylorAlgHom n).toRingHom I) := by
  rw [← MvPowerSeries.pderiv_coe]
  exact actual_homogeneous_initial_ideal_pderiv_of_first_symbol_closure n I i hclosure P hP

private theorem unshiftedTaylor_directions_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) →
      (Fin n → ComplexModel m) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n) (normalVector 0 n)) :
    P n (actualUnshiftedTaylorAlgHom n) (fun i => EuclideanSpace.single i 1) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ)
      (v : Fin n → ComplexModel m) (hf : P m f v) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f)
        (fun i => cast (congrArg ComplexModel hm) (v i)) := by
    subst m
    exact hf
  have ht := hc (Nat.zero_add n) (originalTaylorAlgHom n) (normalVector 0 n) h
  have hv : (fun i : Fin n => cast (congrArg ComplexModel (Nat.zero_add n))
      (normalVector 0 n i)) = (fun i => EuclideanSpace.single i (1 : ℂ)) := by
    funext i
    have hs {m : ℕ} (hm : m=n) (j : Fin m) :
        cast (congrArg ComplexModel hm) (EuclideanSpace.single j (1 : ℂ)) =
          EuclideanSpace.single (Fin.cast hm j) 1 := by
      subst m
      rfl
    rw [normalVector, hs (Nat.zero_add n)]
    congr 1
    apply Fin.ext
    simp
  change P n (actualUnshiftedTaylorAlgHom n) _ at ht
  rw [hv] at ht
  exact ht
private theorem unshifted_initial_pderiv_of_closure (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (i : Fin n)
    (hclosure : ∀ q : ℕ, 0 < q → ∀ g ∈ I,
      g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q →
      iteratedDerivativeGerm [EuclideanSpace.single i 1] g ∈
        I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)
    (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)) :
    MvPowerSeries.pderiv ℂ i F ∈
      actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ)
      (v : Fin n → ComplexModel m) : Prop :=
    ∀ (I : Ideal (HolGerm (ComplexModel m))) (i : Fin n),
      (∀ q : ℕ, 0 < q → ∀ g ∈ I,
        g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel m)) ^ q →
        iteratedDerivativeGerm [v i] g ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel m)) ^ q) →
      ∀ F : MvPowerSeries (Fin n) ℂ,
        F ∈ actualHomogeneousInitialIdeal (Ideal.map f.toRingHom I) →
        MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal (Ideal.map f.toRingHom I)
  exact unshiftedTaylor_directions_property n P
    (actual_homogeneous_initial_ideal_pderiv_of_first_symbol_closure n) I i hclosure F hF

/-- The genuine tangent coordinate vector is EXACTLY the same ambient coordinate vector used by actual Taylor pderiv. -/
theorem tangentInclusion_coordinateVector (d t : ℕ) (i : Fin d) :
    tangentInclusion d t (EuclideanSpace.single i 1) = EuclideanSpace.single (i.castAdd t) 1 := by
  ext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    rw [tangentInclusion_tangent]
    simp [PiLp.single_apply]
  · intro k
    rw [tangentInclusion_normal]
    have hne : k.natAdd d ≠ i.castAdd t := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    simp [hne]

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original HSconstant centre geometry internally gives WHOLE initial-ideal tangent partial stability and literal polynomial pderiv at the SAME I0. -/
theorem exists_original_hs_constant_centre_initial_tangent_pderiv
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ = hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ (O : Set M), IsOpen O ∧ x ∈ O ∧ ∃ (N : ℕ) (G : Fin N → M → ℂ),
        (∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (G i) O) ∧
        (∀ y ∈ O, ∀ g, A.mem y g ↔ IsInSpanAt (n := d+t) (· ∈ range G) y g) ∧
      ∃ (U : Set (ComplexModel (d+t))), IsOpen U ∧ 0 ∈ U ∧ ∃ _hUT : U ⊆ Φ.target,
        MapsTo (actualFlatteningInverseMap x Φ) U O ∧
        let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
        (∀ i, DifferentiableOn ℂ (H i) U) ∧
        ∃ hhol : ∀ p ∈ U, ∀ i, HolAt (H i) p,
          (∀ p (hp : p ∈ U), originalCoherentOriginIdeal
            (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) p) =
              translatedIdeal H p (hhol p hp)) ∧
          let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
            (actualFlattenedOriginalSheaf A x Φ) 0)
          let K0 := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0
          (∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ), F ∈ actualHomogeneousInitialIdeal K0 →
            MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈ actualHomogeneousInitialIdeal K0) ∧
          ∀ (i : Fin d) (P : MvPolynomial (Fin (d+t)) ℂ),
            (P : MvPowerSeries (Fin (d+t)) ℂ) ∈ actualHomogeneousInitialIdeal K0 →
            (MvPolynomial.pderiv (i.castAdd t) P : MvPowerSeries (Fin (d+t)) ℂ) ∈
              actualHomogeneousInitialIdeal K0 := by
  obtain ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, hClosure⟩ :=
    exists_original_hs_constant_centre_first_symbol_tangent_closure C x hreg A hA hhs
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) 0)
  have hcl (i : Fin d) : ∀ q : ℕ, 0 < q → ∀ g ∈ I0,
      g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q →
      iteratedDerivativeGerm [EuclideanSpace.single (i.castAdd t) 1] g ∈
        I0 ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q := by
    intro q hq g hg hgpow
    cases q with
    | zero => omega
    | succ ℓ =>
      obtain ⟨k, rows, cols, D, _hD, _h0D, _hDU, _hdet, _hV, h0V, hclose⟩ := hClosure ℓ
      have hi := hclose 0 h0V (EuclideanSpace.single i 1) g (by simpa only [map_zero] using hg) hgpow
      simpa only [map_zero, tangentInclusion_coordinateVector] using hi
  refine ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, ?_, ?_⟩
  · intro i F hF
    exact unshifted_initial_pderiv_of_closure (d+t) I0 (i.castAdd t) (hcl i) F hF
  · intro i P hP
    rw [← MvPowerSeries.pderiv_coe]
    exact unshifted_initial_pderiv_of_closure (d+t) I0 (i.castAdd t) (hcl i) P hP

end OriginalCentre
end
end Hironaka.HironakaActualHomogeneousInitialTangentDerivatives
