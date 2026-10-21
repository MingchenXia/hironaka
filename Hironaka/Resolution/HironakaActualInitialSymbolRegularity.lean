/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHomogeneousInitialTangentDerivatives
import Hironaka.Resolution.HironakaActualInitialPolynomialContraction
import Hironaka.Resolution.HironakaPDerivStablePolynomialXSaturation
import Hironaka.Resolution.HironakaStrictFilteredRegularElement

/-! # Actual tangent coordinates are regular symbols

Polynomial tangent stability of the genuine homogeneous initial ideal gives
regularity for the actual maximal-ideal filtration, first in formal series
and then in the unchanged original holomorphic germ ring. The original
constant-Hilbert--Samuel centre geometry supplies this hypothesis internally.
The resulting strict finite-power identities do not assert normal flatness.
-/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualInitialSymbolRegularity
noncomputable section

open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalActualBaseJetDimension HironakaActualOriginalFormalTaylor
  HironakaActualOriginalFormalHSTransfer HironakaActualFormalIdealContraction
  HironakaActualHomogeneousInitialHS HironakaActualHomogeneousInitialTangentDerivatives
  HironakaActualInitialPolynomialContraction HironakaPDerivStablePolynomialXSaturation
  HironakaStrictFilteredRegularElement HironakaActualCoefficientPresentationCentrePower
  Hironaka.HolomorphicIdealSheaves OkaRelationSheaf HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations

private theorem homogeneousComponent_zero_of_mem_power {n : ℕ} (q : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ genuineFormalVariables n ^ (q+1)) :
    MvPowerSeries.homogeneousComponent q F = 0 := by
  apply MvPowerSeries.ext
  intro α
  rw [MvPowerSeries.coeff_homogeneousComponent, map_zero]
  split_ifs with hα
  · apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n (q+1) F).mp hF α
    simpa only [normalExponentDegree, Finsupp.degree_eq_sum] using
      (show Finsupp.degree α < q+1 by omega)
  · rfl

private theorem variable_isHomogeneous {n : ℕ} (i : Fin n) :
    (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ).IsHomogeneous 1 := by
  intro α hα
  by_cases he : α = Finsupp.single i 1
  · subst α
    simp [Finsupp.weight_single]
  · simp [MvPowerSeries.coeff_X, he] at hα

/-- Partial stability of the actual initial cone gives regularity in the original formal maximal filtration. -/
theorem formal_regular_symbol_of_initial_pderiv {n : ℕ}
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (i : Fin n)
    (hD : ∀ P : MvPolynomial (Fin n) ℂ,
      (P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal K →
      (MvPolynomial.pderiv i P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal K)
    (q : ℕ) (b : MvPowerSeries (Fin n) ℂ)
    (hb : b ∈ genuineFormalVariables n ^ q)
    (hvb : MvPowerSeries.X i * b ∈ K ⊔ genuineFormalVariables n ^ (q+2)) :
    b ∈ K ⊔ genuineFormalVariables n ^ (q+1) := by
  let m := genuineFormalVariables n
  let J := actualHomogeneousInitialIdeal K
  have hX : (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ) ∈ m :=
    Ideal.subset_span ⟨i, rfl⟩
  have hprod : MvPowerSeries.X i * b ∈ m ^ (q+1) := by
    rw [pow_succ']
    exact Ideal.mul_mem_mul hX hb
  obtain ⟨G, hGK, C, hC, hGC⟩ := Submodule.mem_sup.mp hvb
  have hGlow : G ∈ m ^ (q+1) := by
    have he : G = MvPowerSeries.X i * b - C := by rw [← hGC]; ring
    rw [he]
    exact (m ^ (q+1)).sub_mem hprod (Ideal.pow_le_pow_right (by omega) hC)
  have hcomp : MvPowerSeries.homogeneousComponent (q+1) G =
      MvPowerSeries.homogeneousComponent (q+1) (MvPowerSeries.X i * b) := by
    have he := congrArg (MvPowerSeries.homogeneousComponent (q+1)) hGC
    simpa only [map_add, homogeneousComponent_zero_of_mem_power (q+1) C hC, add_zero] using he
  have hproduct : MvPowerSeries.X i * MvPowerSeries.homogeneousComponent q b ∈ J := by
    have hm := homogeneousComponent_mem_actual_initial_of_mem_power K (q+1) G hGK hGlow
    rw [hcomp, mul_comm (MvPowerSeries.X i) b,
      homogeneousComponent_mul_homogeneous_of_le (q+1) 1 b (MvPowerSeries.X i)
        (variable_isHomogeneous i) (by omega)] at hm
    simpa only [Nat.add_sub_cancel, mul_comm] using hm
  let P := MvPowerSeries.truncTotal (q+1) (MvPowerSeries.homogeneousComponent q b)
  have hP : (P : MvPowerSeries (Fin n) ℂ) = MvPowerSeries.homogeneousComponent q b :=
    homogeneousComponent_truncTotal_coe q b
  let JP := Ideal.comap MvPolynomial.coeToMvPowerSeries.ringHom J
  have hPD : ∀ Q ∈ JP, MvPolynomial.pderiv i Q ∈ JP := by
    intro Q hQ
    exact hD Q hQ
  have hXP : MvPolynomial.X i * P ∈ JP := by
    change ((MvPolynomial.X i * P : MvPolynomial (Fin n) ℂ) :
      MvPowerSeries (Fin n) ℂ) ∈ J
    simpa only [MvPolynomial.coe_mul, MvPolynomial.coe_X, hP] using hproduct
  have hcomponent : MvPowerSeries.homogeneousComponent q b ∈ J := by
    rw [← hP]
    exact (X_mul_mem_iff_of_pderiv_stable JP i hPD P).mp hXP
  obtain ⟨L, hLK, hLpow, hLcomponent⟩ :=
    actual_homogeneous_initial_ideal_degree_lift K
      (MvPowerSeries.homogeneousComponent q b) hcomponent q
  have hcomponents : MvPowerSeries.homogeneousComponent q L =
      MvPowerSeries.homogeneousComponent q b := by
    simpa only [← MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp
      (MvPowerSeries.isHomogeneous_homogeneousComponent b q)] using hLcomponent
  have hrem : b-L ∈ m ^ (q+1) := by
    apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n (q+1) (b-L)).mpr
    intro α hα
    rw [map_sub]
    by_cases hsmall : normalExponentDegree α < q
    · rw [(mem_genuineFormalVariables_pow_iff_coefficients_zero n q b).mp hb α hsmall,
        (mem_genuineFormalVariables_pow_iff_coefficients_zero n q L).mp hLpow α hsmall,
        sub_self]
    · have hd : Finsupp.degree α = q := by
        have : normalExponentDegree α = q := by omega
        simpa only [normalExponentDegree, Finsupp.degree_eq_sum] using this
      have he := congrArg (MvPowerSeries.coeff α) hcomponents
      simp only [MvPowerSeries.coeff_homogeneousComponent, if_pos hd] at he
      exact sub_eq_zero.mpr he.symm
  have he : L + (b-L) = b := by ring
  rw [← he]
  exact Ideal.add_mem _ (Ideal.mem_sup_left hLK) (Ideal.mem_sup_right hrem)

/-- The genuine whole Taylor dictionary transfers actual symbol regularity to the original analytic ideal. -/
theorem original_regular_symbol_of_initial_pderiv (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel (0+n)))) (i : Fin n)
    (hD : ∀ P : MvPolynomial (Fin n) ℂ,
      (P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal
        (Ideal.map (originalTaylorAlgHom n).toRingHom I) →
      (MvPolynomial.pderiv i P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal
        (Ideal.map (originalTaylorAlgHom n).toRingHom I))
    (q : ℕ) (b : HolGerm (ComplexModel (0+n)))
    (hb : b ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q)
    (hvb : normalCoordinate 0 n i * b ∈
      I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (q+2)) :
    b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (q+1) := by
  have hbF : originalTaylorAlgHom n b ∈ genuineFormalVariables n ^ q := by
    rw [show genuineFormalVariables n ^ q =
      Ideal.map (originalTaylorAlgHom n).toRingHom
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q) from
          (map_original_maximal_pow_eq_formal_variables_pow n q).symm]
    exact Ideal.mem_map_of_mem _ hb
  have hvF : MvPowerSeries.X i * originalTaylorAlgHom n b ∈
      Ideal.map (originalTaylorAlgHom n).toRingHom I ⊔ genuineFormalVariables n ^ (q+2) := by
    rw [show Ideal.map (originalTaylorAlgHom n).toRingHom I ⊔ genuineFormalVariables n ^ (q+2) =
      Ideal.map (originalTaylorAlgHom n).toRingHom
        (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (q+2)) from
          (map_original_thickening_eq_formal_thickening n (q+2) I).symm]
    rw [← originalTaylorAlgHom_coordinate n i, ← map_mul]
    exact Ideal.mem_map_of_mem _ hvb
  have hformal := formal_regular_symbol_of_initial_pderiv _ i hD q _ hbF hvF
  apply (mem_original_ideal_iff_formal_extension n _ b).mpr
  rwa [map_original_thickening_eq_formal_thickening n (q+1) I]

private theorem unshiftedTaylor_coordinate_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) →
      (Fin n → HolGerm (ComplexModel m)) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n) (normalCoordinate 0 n)) :
    P n (actualUnshiftedTaylorAlgHom n) coordinateGerm := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ)
      (v : Fin n → HolGerm (ComplexModel m)) (hf : P m f v) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f)
        (fun i => cast (congrArg (fun j => HolGerm (ComplexModel j)) hm) (v i)) := by
    subst m
    exact hf
  have ht := hc (Nat.zero_add n) (originalTaylorAlgHom n) (normalCoordinate 0 n) h
  have hv : (fun i : Fin n => cast
      (congrArg (fun j => HolGerm (ComplexModel j)) (Nat.zero_add n))
        (normalCoordinate 0 n i)) = coordinateGerm := by
    funext i
    have hs {m : ℕ} (hm : m=n) (j : Fin m) :
        cast (congrArg (fun k => HolGerm (ComplexModel k)) hm) (coordinateGerm j) =
          coordinateGerm (Fin.cast hm j) := by
      subst m
      rfl
    rw [normalCoordinate, hs (Nat.zero_add n)]
    congr 1
    apply Fin.ext
    simp
  change P n (actualUnshiftedTaylorAlgHom n) _ at ht
  rwa [hv] at ht

/-- Literal dimension reindexing leaves regularity on the same original coordinate germs unchanged. -/
theorem unshifted_original_regular_symbol_of_initial_pderiv (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (i : Fin n)
    (hD : ∀ P : MvPolynomial (Fin n) ℂ,
      (P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) →
      (MvPolynomial.pderiv i P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I))
    (q : ℕ) (b : HolGerm (ComplexModel n))
    (hb : b ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)
    (hvb : coordinateGerm i * b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (q+2)) :
    b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (q+1) := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ)
      (v : Fin n → HolGerm (ComplexModel m)) : Prop :=
    ∀ (I : Ideal (HolGerm (ComplexModel m))) (i : Fin n),
      (∀ Q : MvPolynomial (Fin n) ℂ,
        (Q : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal (Ideal.map f.toRingHom I) →
        (MvPolynomial.pderiv i Q : MvPowerSeries (Fin n) ℂ) ∈
          actualHomogeneousInitialIdeal (Ideal.map f.toRingHom I)) →
      ∀ (q : ℕ) (b : HolGerm (ComplexModel m)),
        b ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel m)) ^ q →
        v i * b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel m)) ^ (q+2) →
        b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel m)) ^ (q+1)
  exact unshiftedTaylor_coordinate_property n P (original_regular_symbol_of_initial_pderiv n)
    I i hD q b hb hvb

private theorem coordinateGerm_mem_maximalIdeal (n : ℕ) (i : Fin n) :
    coordinateGerm i ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
  rw [HolGerm.mem_maximalIdeal_iff]
  simp [coordinateGerm, HolGerm.eval_mk]

/-- Actual analytic separatedness upgrades finite regular symbols to saturation of the entire original ideal. -/
theorem original_coordinate_mul_mem_iff_of_initial_pderiv (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (i : Fin n)
    (hD : ∀ P : MvPolynomial (Fin n) ℂ,
      (P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) →
      (MvPolynomial.pderiv i P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I))
    (a : HolGerm (ComplexModel n)) : coordinateGerm i * a ∈ I ↔ a ∈ I := by
  refine ⟨?_, I.mul_mem_left _⟩
  intro ha
  let m := IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))
  have hv : coordinateGerm i ∈ m := coordinateGerm_mem_maximalIdeal n i
  have hregular := unshifted_original_regular_symbol_of_initial_pderiv n I i hD
  apply (HironakaActualWholeIdealJetDetection.mem_original_ideal_iff_all_positive_thickenings I a).mpr
  intro q
  exact (mem_successor_iff_mem_current_of_regular_symbol I m _ hv hregular (q+1) a).mp
    (Ideal.mem_sup_left ha)

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original regularity, coherence and intrinsic Hilbert--Samuel constancy internally give exact strict tangent division. -/
theorem exists_original_hs_constant_centre_strict_tangent_division
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ = hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      let m := IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))
      ∀ i : Fin d,
        (∀ (q : ℕ) (a : HolGerm (ComplexModel (d+t))),
          coordinateGerm (i.castAdd t) * a ∈ I0 ⊔ m^(q+1) ↔ a ∈ I0 ⊔ m^q) ∧
        (∀ q : ℕ, (I0 ⊔ m^(q+1)) ⊓
          (I0 ⊔ Ideal.span ({coordinateGerm (i.castAdd t)} : Set (HolGerm (ComplexModel (d+t))))) =
            I0 ⊔ Ideal.span ({coordinateGerm (i.castAdd t)} : Set (HolGerm (ComplexModel (d+t)))) * m^q) ∧
        ∀ a : HolGerm (ComplexModel (d+t)), coordinateGerm (i.castAdd t) * a ∈ I0 ↔ a ∈ I0 := by
  obtain ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, hFormal, hPolynomial⟩ :=
    exists_original_hs_constant_centre_initial_tangent_pderiv C x hreg A hA hhs
  refine ⟨Φ, hsrc, h0, hflat, ?_⟩
  dsimp only
  intro i
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf A x Φ) 0)
  let m := IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))
  have hv : coordinateGerm (i.castAdd t) ∈ m := coordinateGerm_mem_maximalIdeal (d+t) _
  have hregular (q : ℕ) (b : HolGerm (ComplexModel (d+t))) (hb : b ∈ m^q)
      (hvb : coordinateGerm (i.castAdd t) * b ∈ I0 ⊔ m^(q+2)) : b ∈ I0 ⊔ m^(q+1) :=
    unshifted_original_regular_symbol_of_initial_pderiv (d+t) I0 (i.castAdd t)
      (hPolynomial i) q b hb hvb
  exact ⟨mem_successor_iff_mem_current_of_regular_symbol I0 m _ hv hregular,
    sup_pow_inf_principal_of_regular_symbol I0 m _ hv hregular,
    original_coordinate_mul_mem_iff_of_initial_pderiv (d+t) I0 (i.castAdd t) (hPolynomial i)⟩

end OriginalCentre
end
end Hironaka.HironakaActualInitialSymbolRegularity
