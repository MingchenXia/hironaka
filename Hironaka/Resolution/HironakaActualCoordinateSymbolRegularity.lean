import Hironaka.Resolution.HironakaActualHomogeneousInitialTangentDerivatives
import Hironaka.Resolution.HironakaActualInitialPolynomialContraction
import Hironaka.Resolution.HironakaPDerivStablePolynomialXSaturation
import Hironaka.Resolution.HironakaHolomorphicRegularSymbolHilbertSamuel

/-!
# Regular tangent symbols from the original constant-value centre

Polynomial partial stability of the actual homogeneous initial ideal gives regular
coordinate symbols on the entire original finite quotients. The genuine Taylor
extension/contraction dictionary transports the result back to original holomorphic
germs. The final producer supplies the stability premise from the original coherent
ideal and constant-Hilbert–Samuel centre geometry on one chosen flattening.
-/

set_option autoImplicit false

open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualCoordinateSymbolRegularity

noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalIdeal
  HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalTaylor
  HironakaActualFormalIdealContraction HironakaActualOriginalFormalHSTransfer
  HironakaActualHomogeneousInitialHS HironakaActualInitialPolynomialContraction
  HironakaActualHomogeneousInitialTangentDerivatives
  HironakaPDerivStablePolynomialXSaturation HironakaActualCoefficientPresentationCentrePower
  HironakaHolomorphicRegularSymbolHilbertSamuel
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaHolomorphicJetChartInvariance HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalCoherentTranslatedJets

private theorem component_zero_of_mem_higher_power {n : ℕ} (p q : ℕ) (hpq : p < q)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ genuineFormalVariables n ^ q) :
    MvPowerSeries.homogeneousComponent p F = 0 := by
  apply MvPowerSeries.ext
  intro a
  rw [map_zero, MvPowerSeries.coeff_homogeneousComponent]
  split_ifs with ha
  · apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q F).mp hF a
    simpa only [normalExponentDegree, ← Finsupp.degree_eq_sum, ha] using hpq
  · rfl

private theorem component_X_mul {n : ℕ} (q : ℕ) (i : Fin n)
    (B : MvPowerSeries (Fin n) ℂ) (hB : B ∈ genuineFormalVariables n ^ q) :
    MvPowerSeries.homogeneousComponent (q + 1) (MvPowerSeries.X i * B) =
      MvPowerSeries.X i * MvPowerSeries.homogeneousComponent q B := by
  have hBo : (q : ℕ∞) ≤ B.order := by
    apply MvPowerSeries.nat_le_order
    intro a ha
    apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q B).mp hB a
    simpa only [normalExponentDegree, ← Finsupp.degree_eq_sum] using ha
  have hXo : (1 : ℕ∞) ≤ (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ).order := by
    rw [MvPowerSeries.X, MvPowerSeries.order_monomial_of_ne_zero one_ne_zero]
    simp [Finsupp.degree_eq_weight_one, Finsupp.weight_single]
  have hX : MvPowerSeries.homogeneousComponent 1
      (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ) = MvPowerSeries.X i := by
    apply MvPowerSeries.ext
    intro a
    by_cases ha : a = Finsupp.single i 1
    · subst a
      simp [MvPowerSeries.coeff_homogeneousComponent, MvPowerSeries.coeff_X,
        Finsupp.degree_eq_weight_one, Finsupp.weight_single]
    · simp [MvPowerSeries.coeff_homogeneousComponent, MvPowerSeries.coeff_X, ha]
  have h := MvPowerSeries.homogeneousComponent_mul_of_le_order hXo hBo
  simpa only [Nat.add_comm 1 q, hX] using h

/-- Stability of the literal polynomial contraction gives regularity on the actual
formal finite quotients, without a supplied regular-symbol hypothesis. -/
theorem formal_regular_symbol_of_initial_pderiv {n : ℕ}
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (i : Fin n)
    (hD : ∀ P : MvPolynomial (Fin n) ℂ,
      (P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal K →
      (MvPolynomial.pderiv i P : MvPowerSeries (Fin n) ℂ) ∈
        actualHomogeneousInitialIdeal K)
    (q : ℕ) (B : MvPowerSeries (Fin n) ℂ)
    (hB : B ∈ genuineFormalVariables n ^ q)
    (hXB : MvPowerSeries.X i * B ∈ K ⊔ genuineFormalVariables n ^ (q + 2)) :
    B ∈ K ⊔ genuineFormalVariables n ^ (q + 1) := by
  obtain ⟨F, hFK, C, hC, he⟩ := Submodule.mem_sup.mp hXB
  have hX : (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ) ∈ genuineFormalVariables n :=
    Ideal.subset_span ⟨i, rfl⟩
  have hXBpow : MvPowerSeries.X i * B ∈ genuineFormalVariables n ^ (q + 1) := by
    rw [pow_succ']
    exact Ideal.mul_mem_mul hX hB
  have hFpow : F ∈ genuineFormalVariables n ^ (q + 1) := by
    have hF : F = MvPowerSeries.X i * B - C := (eq_sub_iff_add_eq).mpr he
    rw [hF]
    exact (genuineFormalVariables n ^ (q + 1)).sub_mem hXBpow
      (Ideal.pow_le_pow_right (by omega) hC)
  have hFC := homogeneousComponent_mem_actual_initial_of_mem_power K (q + 1) F hFK hFpow
  have hcomp : MvPowerSeries.homogeneousComponent (q + 1) F =
      MvPowerSeries.X i * MvPowerSeries.homogeneousComponent q B := by
    have h := congrArg (MvPowerSeries.homogeneousComponent (q + 1)) he
    rw [map_add, component_zero_of_mem_higher_power (q + 1) (q + 2) (by omega) C hC,
      add_zero, component_X_mul q i B hB] at h
    exact h
  rw [hcomp] at hFC
  let P := MvPowerSeries.truncTotal (q + 1) (MvPowerSeries.homogeneousComponent q B)
  have hP : (P : MvPowerSeries (Fin n) ℂ) = MvPowerSeries.homogeneousComponent q B :=
    homogeneousComponent_truncTotal_coe q B
  let J := Ideal.comap MvPolynomial.coeToMvPowerSeries.ringHom
    (actualHomogeneousInitialIdeal K)
  have hJD : ∀ P ∈ J, MvPolynomial.pderiv i P ∈ J := by
    intro P hPJ
    exact hD P hPJ
  have hXP : MvPolynomial.X i * P ∈ J := by
    change ((MvPolynomial.X i * P : MvPolynomial (Fin n) ℂ) :
      MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal K
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, hP]
    exact hFC
  have hPJ := (X_mul_mem_iff_of_pderiv_stable J i hJD P).mp hXP
  have hBQ : MvPowerSeries.homogeneousComponent q B ∈ actualHomogeneousInitialIdeal K := by
    rw [← hP]
    exact hPJ
  obtain ⟨L, hLK, hLpow, hLcomp⟩ :=
    actual_homogeneous_initial_ideal_degree_lift K _ hBQ q
  have hidem : MvPowerSeries.homogeneousComponent q
      (MvPowerSeries.homogeneousComponent q B) = MvPowerSeries.homogeneousComponent q B :=
    (MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp
      (MvPowerSeries.isHomogeneous_homogeneousComponent B q)).symm
  rw [hidem] at hLcomp
  have hrem : B - L ∈ genuineFormalVariables n ^ (q + 1) := by
    apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n (q + 1) _).mpr
    intro a ha
    rw [map_sub]
    by_cases hlow : normalExponentDegree a < q
    · rw [(mem_genuineFormalVariables_pow_iff_coefficients_zero n q B).mp hB a hlow,
        (mem_genuineFormalVariables_pow_iff_coefficients_zero n q L).mp hLpow a hlow,
        sub_self]
    · have hdegree : Finsupp.degree a = q := by
        have hd : normalExponentDegree a = q := by omega
        simpa only [normalExponentDegree, ← Finsupp.degree_eq_sum] using hd
      have hc := congrArg (MvPowerSeries.coeff a) hLcomp
      simp only [MvPowerSeries.coeff_homogeneousComponent, if_pos hdegree] at hc
      exact sub_eq_zero.mpr hc.symm
  have hsum := (K ⊔ genuineFormalVariables n ^ (q + 1)).add_mem
    (Ideal.mem_sup_left hLK) (Ideal.mem_sup_right hrem)
  have he : L + (B - L) = B := by abel
  rwa [he] at hsum

private theorem unshiftedTaylor_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0 + n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m = n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

/-- Literal membership in every whole original thickening is reflected and preserved
by the actual unshifted Taylor map. -/
theorem mem_original_thickening_iff_unshifted_taylor (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (q : ℕ) (g : HolGerm (ComplexModel n)) :
    g ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ↔
      actualUnshiftedTaylorAlgHom n g ∈
        Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I ⊔ genuineFormalVariables n ^ q := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ (I : Ideal (HolGerm (ComplexModel m))) (q : ℕ) (g : HolGerm (ComplexModel m)),
      g ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel m)) ^ q ↔
        f g ∈ Ideal.map f.toRingHom I ⊔ genuineFormalVariables n ^ q
  have hs : P (0 + n) (originalTaylorAlgHom n) := by
    intro I q g
    rw [mem_original_ideal_iff_formal_extension n
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0 + n))) ^ q) g,
      map_original_thickening_eq_formal_thickening]
    rfl
  exact unshiftedTaylor_property n P hs I q g

/-- Differential stability of the actual initial ideal produces the regular coordinate
symbol on the original holomorphic ring, through entire ideal contraction. -/
theorem original_regular_symbol_of_initial_pderiv (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (i : Fin n)
    (hD : ∀ P : MvPolynomial (Fin n) ℂ,
      (P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) →
      (MvPolynomial.pderiv i P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I))
    (q : ℕ) (b : HolGerm (ComplexModel n))
    (hb : b ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)
    (hvb : coordinateGerm i * b ∈ I ⊔
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (q + 2)) :
    b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (q + 1) := by
  have hB : actualUnshiftedTaylorAlgHom n b ∈ genuineFormalVariables n ^ q := by
    have h := (mem_original_thickening_iff_unshifted_taylor n ⊥ q b).mp
      (by simpa only [bot_sup_eq] using hb)
    simpa only [Ideal.map_bot, bot_sup_eq] using h
  have hXB := (mem_original_thickening_iff_unshifted_taylor n I (q + 2)
    (coordinateGerm i * b)).mp hvb
  rw [map_mul, actualUnshiftedTaylor_coordinate] at hXB
  exact (mem_original_thickening_iff_unshifted_taylor n I (q + 1) b).mpr
    (formal_regular_symbol_of_initial_pderiv _ i hD q _ hB hXB)

section OriginalCentre

variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d + t)) M] [IsComplexManifold (d + t) M]

/-- Original constant-value centre geometry internally supplies all tangent regular
symbols and the original numerical recurrences on one chosen flattening. -/
theorem exists_original_hs_constant_centre_regular_tangent_symbols
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d + t) C x d)
    (A : GermIdeal (d + t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ = hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d + t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d + t)) x).target ∧
      Φ.toFun (chartAt (ComplexModel (d + t)) x x) = 0 ∧
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d + t)) x).source →
        chartAt (ComplexModel (d + t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d + t)) x y) ∈
          complexCoordinatePlane (d + t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      ∀ i : Fin d,
        (∀ q : ℕ, ∀ b ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d + t))) ^ q,
          coordinateGerm (i.castAdd t) * b ∈ I0 ⊔
            IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d + t))) ^ (q + 2) →
          b ∈ I0 ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d + t))) ^ (q + 1)) ∧
        (∀ q : ℕ,
          hilbertSamuelValue (I0 ⊔ Ideal.span {coordinateGerm (i.castAdd t)}) (q + 1) +
            hilbertSamuelValue I0 q = hilbertSamuelValue I0 (q + 1)) ∧
        (∀ q : ℕ, hilbertSamuelValue I0 q =
          ∑ j ∈ Finset.range (q + 1),
            hilbertSamuelValue (I0 ⊔ Ideal.span {coordinateGerm (i.castAdd t)}) j) := by
  obtain ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, _hformal, hPolynomial⟩ :=
    exists_original_hs_constant_centre_initial_tangent_pderiv C x hreg A hA hhs
  refine ⟨Φ, hsrc, h0, hflat, ?_⟩
  dsimp only
  intro i
  have hi := original_regular_symbol_of_initial_pderiv (d + t) _ (i.castAdd t) (hPolynomial i)
  have hv : coordinateGerm (i.castAdd t) ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d + t))) :=
    (HolGerm.mem_maximalIdeal_iff _).mpr rfl
  refine ⟨hi, ?_, ?_⟩
  · intro q
    exact hilbertSamuelValue_parameter_recurrence _ _ hv hi q
  · intro q
    exact hilbertSamuelValue_eq_sum_parameter _ _ hv hi q

end OriginalCentre

end

end Hironaka.HironakaActualCoordinateSymbolRegularity
