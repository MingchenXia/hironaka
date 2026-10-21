/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualTangentCutLayers
import Hironaka.Resolution.HironakaActualInitialNormalExtension

/-!
# Original normal freeness and initial cylinder in one actual flattening

The original coupled-symbol producer is invoked once. Its genuine joint
normal jets yield actual finite free original normal layers through the
whole tangent-cut dictionaries, while its initial derivative stability is
retained for exactly the same origin ideal and yields its normal cylinder.
No free-layer, derivative-stability or cylinder certificate is an input.
Blueprint: `hironaka-actual-coupled-normal-freeness-extension.tex`.
-/
set_option autoImplicit false
open Set
open scoped Manifold ContDiff
namespace Hironaka.HironakaActualCoupledNormalFreeness
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaHolomorphicJetMonomialSpan
  HironakaActualTangentDisplacementZeroQuotient HironakaRelativeNormalAssociatedGraded
  HironakaActualPrincipalPartsResidueSymbols HironakaActualJointTangentCuts
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaActualCentrePrincipalParts HironakaStrictFilteredGradedQuotient
  HironakaActualCentreCoupledSymbols HironakaActualTangentCutLayers
  HironakaActualHomogeneousInitialHS HironakaActualInitialNormalExtension
  HironakaActualCoefficientPresentationCentrePower
  HironakaRelativeNormalUniformTruncations HironakaActualJointBaseFibre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+(d+t)))) := tangentAlgebra d (d+t)
local instance : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+(d+t)))) :=
  IsScalarTower.of_algHom (tangentPullback d (d+t))

private theorem free_original_layer_of_cut (d t : ℕ)
    (K : Ideal (HolGerm (ComplexModel (d+(d+t)))))
    (hV : tangentDisplacementIdeal d t ≤ K)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hI : Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K=I)
    (q : ℕ)
    [Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d (d+t) K q)]
    [Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d (d+t) K q)] :
    Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) ∧
      Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) := by
  subst I
  let E := tangentCutLayerEquiv d t K hV q
  exact ⟨Module.Finite.of_surjective E.toLinearMap E.surjective,Module.Free.of_equiv E⟩

set_option maxHeartbeats 1000000 in
/-- One original flattening supplies actual finite free normal layers and the same initial cylinder. -/
theorem exists_original_hs_constant_centre_coupled_normal_data
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      (∀ q : ℕ,
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I0 q) ∧
        Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I0 q) ) ∧
      (∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ),
        F ∈ actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0) →
        MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈
          actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0)) ∧
      (∀ (i : Fin d) (P : MvPolynomial (Fin (d+t)) ℂ),
        (P : MvPowerSeries (Fin (d+t)) ℂ) ∈
          actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0) →
        (MvPolynomial.pderiv (i.castAdd t) P : MvPowerSeries (Fin (d+t)) ℂ) ∈
          actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0)) ∧
      actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0) =
        Ideal.map (MvPowerSeries.rename (Fin.natAdd d : Fin t → Fin (d+t))).toRingHom
          (Ideal.comap (MvPowerSeries.rename (Fin.natAdd d : Fin t → Fin (d+t))).toRingHom
            (actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0))) := by
  obtain ⟨Φ,hsrc,h0,hflat,O,_hO,_hxO,N,G,_hG,_hgen,U,_hU,_h0U,_hUT,
    _hMap,_hH,_hhol,_hI,hH0,hspan,horders,hD,hDP⟩ :=
    exists_original_hs_constant_centre_coupled_symbols C x hreg A hA hhs
  refine ⟨Φ,hsrc,h0,hflat,?_,hD,hDP,?_⟩
  · let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf A x Φ) 0)
    let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
    let J := Ideal.map (actualCentreJointPullback d t).toRingHom I0
    have hJ : J=actualCentreJointIdeal d t H hH0 := by
      dsimp only [J,I0]
      rw [hspan,Ideal.map_span,← Set.range_comp]
      rfl
    have hQ : ∀ q : ℕ, Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d (d+t) J q) ∧
        Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d (d+t) J q) := by
      intro q
      cases q with
      | zero =>
        let : Subsingleton (originalNormalTruncation d (d+t) J 0) := originalNormalTruncation_zero_subsingleton d (d+t) J
        exact ⟨inferInstance,inferInstance⟩
      | succ q =>
        change Module.Finite (HolGerm (ComplexModel d))
            (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t)^(q+1))) ∧
          Module.Free (HolGerm (ComplexModel d))
            (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t)^(q+1)))
        rw [hJ]
        exact ⟨(horders q).1,(horders q).2.2⟩
    have hGjoint := normalLayers_finite_free_of_truncations d (d+t) J hQ
    let L := List.ofFn (fun i : Fin d => i.castAdd t)
    let K := jointCoordinateCuts d (d+t) J L
    have hL : L.Nodup := List.nodup_ofFn.mpr (Fin.castAdd_injective d t)
    have hcut : ∀ q : ℕ, Module.Finite (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d (d+t)) q) ∧
        Module.Free (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d (d+t)) q) := by
      intro q
      apply normalLayers_after_coordinate_cuts_finite_free d (d+t) J L hL
        (fun q => (hGjoint q).1) (fun q => (hGjoint q).2)
      intro i hi F hF
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
      have hmap : Ideal.map (jointBaseZeroTrace d (d+t)).toRingHom J=I0 := map_jointIdeal_eq_original d t I0
      rw [hmap] at hF ⊢
      exact hD j F hF
    have hV : tangentDisplacementIdeal d t ≤ K := tangentDisplacementIdeal_le_allTangentCuts d t J
    have hmap : Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K=I0 :=
      (map_allTangentCuts d t J).trans (map_jointIdeal_eq_original d t I0)
    intro q
    let : Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d (d+t) K q) := by
      change Module.Finite (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d (d+t)) q)
      exact (hcut q).1
    let : Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d (d+t) K q) := by
      change Module.Free (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d (d+t)) q)
      exact (hcut q).2
    exact free_original_layer_of_cut d t K hV I0 hmap q
  · exact actualHomogeneousInitialIdeal_eq_normal_extension_of_tangent_pderiv d t _ hDP

end
end Hironaka.HironakaActualCoupledNormalFreeness
