/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCentrePrincipalPartsFree
import Hironaka.Resolution.HironakaActualHomogeneousInitialTangentDerivatives

/-!
# One actual original family for free principal parts and tangent symbols

One original constant-Hilbert--Samuel centre producer supplies all orders of
finite-free joint principal parts and tangent-stable initial ideals in the same
flattening chart with the same finite holomorphic generators. The exact origin
ideal/generator dictionary is retained. No second existential chart choice or
caller free/symbol certificate is introduced. The degree convention is q+1;
order-zero truncations are handled separately by downstream consumers.
-/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCentreCoupledSymbols
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaRelativeNormalIdeal HironakaHolomorphicPointJets
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetQuotientFrames HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaActualCentreJointJets HironakaActualCentrePrincipalParts
  HironakaActualCentrePrincipalPartsFree HironakaActualFirstSymbolTangentClosure
  HironakaActualHomogeneousInitialTangentDerivatives HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalFormalTaylor HironakaActualFormalInitialDiagram
  HironakaActualHomogeneousInitialHS HironakaRelativeNormalTaylorCoefficients
  HironakaRelativeNormalActualBaseJetDimension HironakaActualOriginalTaylorPolynomial
  HironakaActualCoefficientPresentationCentrePower HironakaActualHSZeroCentreVanishing

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

theorem translatedIdeal_zero_eq_span (n : ℕ) {ι : Type*}
    (H : ι → ComplexModel n → ℂ)
    (hH hH' : ∀ i, HolAt (H i) 0) :
    translatedIdeal H 0 hH = Ideal.span (Set.range fun i => HolGerm.mk (H i) (hH' i)) := by
  unfold translatedIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Filter.Eventually.of_forall fun z => by simp

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

set_option maxHeartbeats 1000000 in
/-- One actual original family supplies the free joint truncations and the tangent-stable origin initial ideal simultaneously. -/
theorem exists_original_hs_constant_centre_coupled_symbols
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
        (∀ y ∈ O, ∀ g, A.mem y g ↔ IsInSpanAt (n := d+t) (· ∈ Set.range G) y g) ∧
      ∃ (U : Set (ComplexModel (d+t))), ∃ _hU : IsOpen U,
        ∃ _h0U : (0 : ComplexModel (d+t)) ∈ U, ∃ _hUT : U ⊆ Φ.target,
        MapsTo (actualFlatteningInverseMap x Φ) U O ∧
        let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
        ∃ _hH : ∀ i, DifferentiableOn ℂ (H i) U,
        ∃ hhol : ∀ p ∈ U, ∀ i, HolAt (H i) p,
          (∀ p (hp : p ∈ U), originalCoherentOriginIdeal
            (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) p) =
              translatedIdeal H p (hhol p hp)) ∧
        ∃ hH0 : ∀ i, HolAt (H i) 0,
          let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
            (actualFlattenedOriginalSheaf A x Φ) 0)
          I0 = Ideal.span (Set.range fun i => HolGerm.mk (H i) (hH0 i)) ∧
          (∀ q : ℕ, letI := tangentAlgebra d (d+t)
            Module.Finite (HolGerm (ComplexModel d))
              (HolGerm (ComplexModel (d+(d+t))) ⧸
                (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t) ^ (q+1))) ∧
            Module.Projective (HolGerm (ComplexModel d))
              (HolGerm (ComplexModel (d+(d+t))) ⧸
                (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t) ^ (q+1))) ∧
            Module.Free (HolGerm (ComplexModel d))
              (HolGerm (ComplexModel (d+(d+t))) ⧸
                (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t) ^ (q+1)))) ∧
          (∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ),
            F ∈ actualHomogeneousInitialIdeal
              (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0) →
            MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈ actualHomogeneousInitialIdeal
              (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0)) ∧
          (∀ (i : Fin d) (P : MvPolynomial (Fin (d+t)) ℂ),
            (P : MvPowerSeries (Fin (d+t)) ℂ) ∈ actualHomogeneousInitialIdeal
              (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0) →
            (MvPolynomial.pderiv (i.castAdd t) P : MvPowerSeries (Fin (d+t)) ℂ) ∈
              actualHomogeneousInitialIdeal
                (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0)) := by
  obtain ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,
    _hHS,_hR,hH0,hpiv⟩ :=
    exists_original_hs_constant_centre_all_order_principal_parts_free C x hreg A hA hhs
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf A x Φ) 0)
  have hcl (i : Fin d) : ∀ q : ℕ, 0 < q → ∀ g ∈ I0,
      g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q →
      iteratedDerivativeGerm [EuclideanSpace.single (i.castAdd t) 1] g ∈
        I0 ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q := by
    intro q hq g hg hgpow
    cases q with
    | zero => omega
    | succ ℓ =>
      obtain ⟨k,rows,cols,_hk,D,hD,h0D,hDU,_hV,_h0V,hdet,hrank,_hunit,
        _hker,_hsurj,_hframe,_hf,_hp,_hfree⟩ := hpiv ℓ
      have hc : tangentInclusion d t 0 ∈ D := by simpa only [map_zero] using h0D
      have hg' : g ∈ translatedIdeal H (tangentInclusion d t 0)
          (actual_family_holomorphicAt hU H hH _ (hDU hc)) := by
        have hgp : g ∈ originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
            (actualFlattenedOriginalSheaf A x Φ) (tangentInclusion d t 0)) := by
          simpa only [map_zero] using hg
        rw [hI _ (hDU hc)] at hgp
        exact hgp
      have ht := actual_projected_tangent_derivative_mem_ideal_sup_point_pow d t (ℓ+1) H
        rows cols hU hD hH hDU hdet
        (fun c hc => hrank _ hc (tangentInclusion_mem_plane d t c))
        0 (EuclideanSpace.single i 1) hc g hg' hgpow
      rw [← hI _ (hDU hc)] at ht
      simpa only [map_zero, tangentInclusion_coordinateVector] using ht
  refine ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,hH0,?_,?_,?_,?_⟩
  · exact (hI 0 h0U).trans (translatedIdeal_zero_eq_span (d+t) H (hhol 0 h0U) hH0)
  · intro q
    obtain ⟨k,rows,cols,_hk,D,hD,h0D,hDU,_hV,_h0V,hdet,hrank,_hunit,
      _hker,_hsurj,_hframe,hf,hp,hfree⟩ := hpiv q
    exact ⟨hf,hp,hfree⟩
  · intro i F hF
    exact unshifted_initial_pderiv_of_closure (d+t) I0 (i.castAdd t) (hcl i) F hF
  · intro i P hP
    rw [← MvPowerSeries.pderiv_coe]
    exact unshifted_initial_pderiv_of_closure (d+t) I0 (i.castAdd t) (hcl i) P hP

end OriginalCentre
end
end Hironaka.HironakaActualCentreCoupledSymbols
