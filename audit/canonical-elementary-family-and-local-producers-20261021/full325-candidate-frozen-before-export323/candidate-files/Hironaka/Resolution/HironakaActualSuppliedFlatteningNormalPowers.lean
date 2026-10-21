/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualStandardNormalIndependence
import Hironaka.Resolution.HironakaActualCentreContactCoordinates

/-!
# Canonical normal powers for a supplied actual flattening

Original coherence and Hilbert--Samuel constancy supply one finite original
family in the SAME prescribed real flattening. Actual constant-rank pivots,
joint principal parts and tangent cuts produce coupled normal data and actual
canonical normal powers without choosing a replacement chart.
Blueprint: `hironaka-actual-supplied-flattening-normal-powers-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualSuppliedFlatteningNormalPowers
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm OkaRelationSheaf
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci HironakaHolomorphicJetMonomialSpan
  HironakaActualCentreCoupledSymbols HironakaActualCentrePrincipalPartsFree HironakaActualCentrePrincipalParts
  HironakaActualFirstSymbolTangentClosure HironakaActualHomogeneousInitialTangentDerivatives
  HironakaActualCentreJointJets HironakaRelativeNormalIdeal HironakaActualFormalInitialDiagram
  HironakaActualOriginalFormalTaylor HironakaRelativeNormalMonomialBasis
  HironakaActualJointTangentCuts HironakaActualTangentCutLayers HironakaActualCoupledNormalFreeness
  HironakaActualCoefficientPresentationCentrePower HironakaActualStandardNormalIndependence
  HironakaActualPrincipalPartsResidueSymbols HironakaActualJointBaseFibre
  HironakaRelativeNormalUniformTruncations HironakaRelativeNormalAssociatedGraded
  HironakaStrictFilteredGradedQuotient HironakaActualTangentDisplacementZeroQuotient
  HironakaActualHSConstantCentreJetFrames HironakaActualHSZeroCentreVanishing
  HironakaHolomorphicJetQuotientFrames HironakaRelativeNormalTaylorCoefficients
  HironakaActualHomogeneousInitialHS HironakaActualOriginalTaylorPolynomial
  HironakaActualFormalCoordinatePowerDivision HironakaActualReducedFormalStandardBasis GiraudAlong
  HironakaActualCentreContactCoordinates BlowupTowers BlowupFlatCoordinates GermIdealOrder

section SuppliedDictionary
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- All actual translated whole ideals use the SAME supplied chart and literal original function family. -/
theorem exists_supplied_flattening_real_translated_ideal_dictionary
    (A : GermIdeal n M) (hA : A.IsCoherent) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
      ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ ∃ (N : ℕ) (G : Fin N → M → ℂ),
        (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G i) O) ∧
        (∀ y ∈ O, ∀ g, A.mem y g ↔ IsInSpanAt (n := n) (· ∈ range G) y g) ∧
        ∃ U : Set (ComplexModel n), IsOpen U ∧ 0 ∈ U ∧ U ⊆ Φ.target ∧
          MapsTo (actualFlatteningInverseMap x Φ) U O ∧
          let H : Fin N → ComplexModel n → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
          (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (H i) U) ∧
          (∀ z ∈ U, ∀ g, (actualFlattenedOriginalSheaf A x Φ).mem z g ↔
            IsInSpanAt (n := n) (· ∈ range H) z g) ∧
          ∃ hhol : ∀ a ∈ U, ∀ i, HolAt (H i ∘ actualAffineTranslation n a) 0,
            (∀ a (ha : a ∈ U),
              originalCoherentOriginIdeal (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) a) =
                Ideal.span (range fun i => HolGerm.mk (H i ∘ actualAffineTranslation n a) (hhol a ha i))) ∧
            ∀ a ∈ U, ∀ g,
              (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) a).mem 0 g ↔
                IsInSpanAt (n := n) (· ∈ range fun i => H i ∘ actualAffineTranslation n a) 0 g := by
  have h0T := actualFlattening_target_zero_mem x Φ h0
  obtain ⟨O, hO, h0O, N, G, hG, hgen, U, hU, h0U, hUT, hMap, hH, hF⟩ :=
    exists_local_original_pullback_generators A hA Φ.target Φ.isOpen_target
      (actualFlatteningInverseMap_mdifferentiable x Φ hsrc) 0 h0T
  have hxO : x ∈ O := by
    simpa only [actualFlatteningInverseMap_zero x Φ h0] using h0O
  let H : Fin N → ComplexModel n → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  have hhol : ∀ a ∈ U, ∀ i, HolAt (H i ∘ actualAffineTranslation n a) 0 :=
    fun _ ha i => translated_function_holAt hU (hH i) ha
  refine ⟨O, hO, hxO, N, G, hG, hgen,
    U, hU, h0U, hUT, hMap, hH, hF, hhol, ?_, ?_⟩
  · intro a ha
    exact translated_origin_ideal_eq_span_of_real_generators
      (actualFlattenedOriginalSheaf A x Φ) H hU hH hF ha (hhol a ha)
  · intro a ha g
    exact translated_sheaf_mem_iff_of_real_generators
      (actualFlattenedOriginalSheaf A x Φ) H hU hH hF ha g

end SuppliedDictionary

section SuppliedRanks
variable {d t : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original all-order HS constancy gives ALL actual ranks for one family in the SAME prescribed flattening. -/
theorem exists_supplied_flattening_common_jet_ranks
    (C : Set M) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0)
    (hflat : ∀ {y : M}, y∈(chartAt (ComplexModel (d+t)) x).source →
      chartAt (ComplexModel (d+t)) x y∈Φ.source →
      (y∈C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y)∈complexCoordinatePlane (d+t) d))
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y∈C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
      ∃ (O : Set M), IsOpen O ∧ x ∈ O ∧ ∃ (N : ℕ) (G : Fin N → M → ℂ),
        (∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (G i) O) ∧
        (∀ y ∈ O,∀ g,A.mem y g ↔ IsInSpanAt (n := d+t) (· ∈ range G) y g) ∧
      ∃ (U : Set (ComplexModel (d+t))), IsOpen U ∧ 0 ∈ U ∧ U ⊆ Φ.target ∧
        MapsTo (actualFlatteningInverseMap x Φ) U O ∧
        let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
        (∀ i,DifferentiableOn ℂ (H i) U) ∧
        ∃ hhol : ∀ p ∈ U,∀ i,HolAt (H i) p,
          (∀ p (hp : p ∈ U),originalCoherentOriginIdeal
            (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) p)=translatedIdeal H p (hhol p hp)) ∧
          (∀ p (_hp : p ∈ U) (ℓ : ℕ),
            hilbertSamuelAt A (actualFlatteningInverseMap x Φ p) ℓ=
              Module.finrank ℂ (LinearMap.range (finiteJet (n := d+t) (ℓ+1)))-
                Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p))) ∧
          (∀ p ∈ U,p ∈ complexCoordinatePlane (d+t) d → ∀ ℓ : ℕ,
            Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p))=
              Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H 0))) := by
  obtain ⟨O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hF,hlocal,hI,_⟩ :=
    exists_supplied_flattening_real_translated_ideal_dictionary A hA x Φ hsrc h0
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  have hhol : ∀ p ∈ U,∀ i,HolAt (H i) p := by
    intro p hp i
    exact (InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hH i) hp).mono
      (fun _ hz => hz.differentiableAt)
  have hdiff (i : Fin N) : DifferentiableOn ℂ (H i) U :=
    fun p hp => (hhol p hp i).self_of_nhds.differentiableWithinAt
  have hIt (p : ComplexModel (d+t)) (hp : p ∈ U) :
      originalCoherentOriginIdeal
        (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) p)=translatedIdeal H p (hhol p hp) := by
    rw [hI p hp,translatedIdeal]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    change H i (p+z)=H i (z+p)
    rw [add_comm]
  have hV (p : ComplexModel (d+t)) (hp : p ∈ U) (ℓ : ℕ) :
      hilbertSamuelAt A (actualFlatteningInverseMap x Φ p) ℓ=
        hilbertSamuelValue (translatedIdeal H p (hhol p hp)) ℓ := by
    rw [hilbertSamuelAt_eq_fixedChart A x _
      (actualNearbyPoint_mem_chart_source x Φ hsrc p (hUT hp)),
      fixed_real_original_whole_stalk_ambient_hs_dictionary A hA x Φ hsrc p (hUT hp) ℓ,hIt p hp]
  refine ⟨O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hdiff,hhol,hIt,?_,?_⟩
  · intro p hp ℓ
    exact (hV p hp ℓ).trans
      (hilbertSamuelValue_translatedIdeal_eq_original_matrix_rank ℓ H p (hhol p hp))
  · intro p hp hplane ℓ
    apply originalMacaulay_rank_eq_of_translated_hs_eq ℓ H p 0 (hhol p hp) (hhol 0 h0U)
    rw [← hV p hp ℓ,← hV 0 h0U ℓ,actualFlatteningInverseMap_zero x Φ h0]
    have hdom := actualNearbyPoint_mem_flatDomain x Φ hsrc p (hUT hp)
    apply hhs _ ((hflat hdom.1 hdom.2).mpr ?_) ℓ
    rw [actualNearbyPoint_chart_value x Φ hsrc p (hUT hp),Φ.right_inv p (hUT hp)]
    exact hplane


end SuppliedRanks

local instance (d n : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+n))) := tangentAlgebra d n
local instance (d n : ℕ) : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+n))) :=
  IsScalarTower.of_algHom (tangentPullback d n)

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


private theorem actual_normal_layers_free_of_joint_truncations (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hQ : ∀ q : ℕ,
      Module.Finite (HolGerm (ComplexModel d))
        (originalNormalTruncation d (d+t) (Ideal.map (actualCentreJointPullback d t).toRingHom I) q) ∧
      Module.Free (HolGerm (ComplexModel d))
        (originalNormalTruncation d (d+t) (Ideal.map (actualCentreJointPullback d t).toRingHom I) q))
    (hD : ∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ),
      F∈actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) →
      MvPowerSeries.pderiv ℂ (i.castAdd t) F∈
        actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)) :
    ∀ q : ℕ, Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) ∧
      Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) := by
  let J := Ideal.map (actualCentreJointPullback d t).toRingHom I
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
    simp only [J,HironakaActualJointBaseFibre.map_jointIdeal_eq_original] at hF ⊢
    exact hD j F hF
  have hV : tangentDisplacementIdeal d t≤K := tangentDisplacementIdeal_le_allTangentCuts d t J
  have hmap : Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K=I :=
    (map_allTangentCuts d t J).trans (HironakaActualTangentDisplacementZeroQuotient.map_jointIdeal_eq_original d t I)
  intro q
  let : Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d (d+t) K q) := by
    change Module.Finite (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d (d+t)) q)
    exact (hcut q).1
  let : Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d (d+t) K q) := by
    change Module.Free (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d (d+t)) q)
    exact (hcut q).2
  exact free_original_layer_of_cut d t K hV I hmap q


/-- One actual finite family and true centre-rank constancy internally produce coupled normal freeness and tangent stability. -/
theorem actual_family_coupled_normal_data (d t : ℕ) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel (d+t) → ℂ) (U : Set (ComplexModel (d+t)))
    (hU : IsOpen U) (h0U : (0 : ComplexModel (d+t))∈U)
    (hH : ∀ i, DifferentiableOn ℂ (H i) U)
    (hR : ∀ p∈U, p∈complexCoordinatePlane (d+t) d → ∀ ℓ : ℕ,
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p))=
        Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H 0))) :
    let I := Ideal.span (range fun i => HolGerm.mk (H i) (actual_family_holomorphicAt hU H hH 0 h0U i))
    (∀ q : ℕ, Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) ∧
      Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q)) ∧
    ∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ),
      F∈actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) →
      MvPowerSeries.pderiv ℂ (i.castAdd t) F∈
        actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) := by
  let hH0 := actual_family_holomorphicAt hU H hH 0 h0U
  let I := Ideal.span (range fun i => HolGerm.mk (H i) (hH0 i))
  change (∀ q : ℕ, Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) ∧
    Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q)) ∧ _
  have hpiv (ℓ : ℕ) : ∃ (k : ℕ) (rows : Fin k → monomialIndex (d+t) (ℓ+1))
      (cols : Fin k → monomialIndex (d+t) (ℓ+1) × ι),
      ∃ (D : Set (ComplexModel (d+t))) (hD : IsOpen D) (h0D : (0 : ComplexModel (d+t))∈D)
        (hDU : D⊆U),
        (∀ p∈D, (pivotMatrix (ℓ+1) H rows cols p).det≠0) ∧
        ∀ p∈D, p∈complexCoordinatePlane (d+t) d →
          Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p))=k := by
    let k := Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H 0))
    have hminor : ¬ ∀ (rows : Fin k → monomialIndex (d+t) (ℓ+1))
        (cols : Fin k → monomialIndex (d+t) (ℓ+1) × ι),
        (Matrix.of fun i j => originalMacaulayMatrix (ℓ+1) H 0 (rows i) (cols j)).det=0 := by
      intro hz
      have hlt := (finite_column_rank_lt_iff_minors_eq_zero (originalMacaulayMatrix (ℓ+1) H 0) k).mpr hz
      change k<k at hlt
      exact (lt_irrefl k) hlt
    push Not at hminor
    obtain ⟨rows,cols,hdet0⟩ := hminor
    let f : ComplexModel (d+t) → ℂ := originalMacaulayMinor (ℓ+1) H rows cols
    let D : Set (ComplexModel (d+t)) := U∩f ⁻¹' ({0} : Set ℂ)ᶜ
    have hD : IsOpen D :=
      (differentiableOn_originalMacaulayMinor (ℓ+1) H hU hH rows cols).continuousOn.isOpen_inter_preimage
        hU isClosed_singleton.isOpen_compl
    exact ⟨k,rows,cols,D,hD,⟨h0U,hdet0⟩,inter_subset_left,
      (fun _ hp => hp.2),fun p hp hplane => hR p hp.1 hplane ℓ⟩
  have hcl (i : Fin d) : ∀ q : ℕ, 0<q → ∀ g∈I,
      g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^q →
      iteratedDerivativeGerm [EuclideanSpace.single (i.castAdd t) 1] g∈
        I⊔IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^q := by
    intro q hq g hg hgpow
    cases q with
    | zero => omega
    | succ ℓ =>
      obtain ⟨k,rows,cols,D,hD,h0D,hDU,hdet,hrank⟩ := hpiv ℓ
      have hc : tangentInclusion d t 0∈D := by simpa only [map_zero] using h0D
      have hg' : g∈translatedIdeal H (tangentInclusion d t 0)
          (actual_family_holomorphicAt hU H hH _ (hDU hc)) := by
        simpa only [map_zero,translatedIdeal_zero_eq_span (d+t) H _ hH0] using hg
      have ht := actual_projected_tangent_derivative_mem_ideal_sup_point_pow d t (ℓ+1) H
        rows cols hU hD hH hDU hdet
        (fun c hc => hrank _ hc (tangentInclusion_mem_plane d t c))
        0 (EuclideanSpace.single i 1) hc g hg' hgpow
      simpa only [map_zero,tangentInclusion_coordinateVector,
        translatedIdeal_zero_eq_span (d+t) H _ hH0] using ht
  have hD : ∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ),
      F∈actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) →
      MvPowerSeries.pderiv ℂ (i.castAdd t) F∈
        actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) :=
    fun i F hF => unshifted_initial_pderiv_of_closure (d+t) I (i.castAdd t) (hcl i) F hF
  refine ⟨?_,hD⟩
  let J := Ideal.map (actualCentreJointPullback d t).toRingHom I
  have hJ : J=actualCentreJointIdeal d t H hH0 := by
    dsimp only [J,I]
    rw [Ideal.map_span,← Set.range_comp]
    rfl
  have hQ : ∀ q : ℕ, Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d (d+t) J q) ∧
      Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d (d+t) J q) := by
    intro q
    cases q with
    | zero =>
      let : Subsingleton (originalNormalTruncation d (d+t) J 0) := originalNormalTruncation_zero_subsingleton d (d+t) J
      exact ⟨inferInstance,inferInstance⟩
    | succ ℓ =>
      obtain ⟨k,rows,cols,D,hDo,h0D,hDU,hdet,hrank⟩ := hpiv ℓ
      change Module.Finite (HolGerm (ComplexModel d))
        (HolGerm (ComplexModel (d+(d+t))) ⧸ (J⊔normalIdeal d (d+t)^(ℓ+1))) ∧
        Module.Free (HolGerm (ComplexModel d))
        (HolGerm (ComplexModel (d+(d+t))) ⧸ (J⊔normalIdeal d (d+t)^(ℓ+1)))
      rw [hJ]
      have hf := actualCentrePrincipalPartsQuotient_finite_free d t (ℓ+1) H hU hH hDo h0D hDU hH0 rows cols hdet hrank
      exact ⟨hf.1,hf.2.2⟩
  exact actual_normal_layers_free_of_joint_truncations d t I hQ hD

section SuppliedNormalPowers
variable {d t : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Genuine original coherence and HS constancy give canonical normal powers in the SAME supplied actual flattening. -/
theorem supplied_flattening_reduced_normal_powers
    (C : Set M) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0)
    (hflat : ∀ {y : M}, y∈(chartAt (ComplexModel (d+t)) x).source →
      chartAt (ComplexModel (d+t)) x y∈Φ.source →
      (y∈C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y)∈complexCoordinatePlane (d+t) d))
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y∈C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf A x Φ) 0)
    ∀ a : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0),
      actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0) a∈
          actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^
            Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val := by
  obtain ⟨O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,hHS,hR⟩ :=
    exists_supplied_flattening_common_jet_ranks C x Φ hsrc h0 hflat A hA hhs
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf A x Φ) 0)
  have hI0 : I0=Ideal.span (range fun i => HolGerm.mk (H i) (actual_family_holomorphicAt hU H hH 0 h0U i)) :=
    (hI 0 h0U).trans (translatedIdeal_zero_eq_span (d+t) H _ _)
  obtain ⟨hf,hD⟩ := actual_family_coupled_normal_data d t H U hU h0U hH hR
  rw [← hI0] at hf hD
  exact actual_reduced_vertices_mem_normal_powers_of_normal_free_and_initial_stable d t I0
    (fun q => (hf q).2) hD

end SuppliedNormalPowers

section OriginalJoint
variable {d t : ℕ} {X : CMfd.{u} (d+t)}

/-- Original maximal marked order and all-order HS constancy give ONE actual literal-contact chart with canonical normal powers. -/
theorem exists_original_joint_contact_reduced_normal_powers
    {A : GermIdeal (d+t) X} (hA : A.IsCoherent) {m : ℕ} (hm : 1≤m)
    (hmax : MaximalContact.IsMaximalOrder A m)
    {C : Set X} {x : X} (hC : RegularAtDim (n := d+t) C x d)
    (hCC : C⊆cosupport (d+t) univ A m)
    (hhs : ∀ y∈C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ (U : Set X) (u : X → ℂ), x∈U ∧ MaximalContact.IsTangentDirection A m U u ∧
      ∃ (hn : 0<d+t) (Φ : LocalHolomorphicEquivAt (n := d+t) (chartAt (ComplexModel (d+t)) x x)),
        d≤d+t-1 ∧ Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
        Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0 ∧ flatDomain Φ ⊆ U ∧
        (∀ z∈flatDomain Φ,
          (z∈C ↔ flatMap Φ z∈complexCoordinatePlane (d+t) d) ∧
          flatCoord Φ ⟨d+t-1,Nat.sub_lt hn one_pos⟩ z=u z) ∧
        let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf A x Φ) 0)
        ∀ a : actualInitialVertices MonomialOrder.degLex
            (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0),
          actualReducedVertexSeries MonomialOrder.degLex
            (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0) a∈
              actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^
                Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val := by
  obtain ⟨U,u,hxU,hu,hn,Φ,hdk,hsrc,h0,hDom,hΦ⟩ :=
    exists_original_maximal_order_centre_contact_coordinates hA hm hmax hC hCC
  refine ⟨U,u,hxU,hu,hn,Φ,hdk,hsrc,h0,hDom,hΦ,?_⟩
  apply supplied_flattening_reduced_normal_powers C x Φ hsrc h0 _ A hA hhs
  intro y hy hyΦ
  exact (hΦ y ⟨hy,hyΦ⟩).1

end OriginalJoint

end
end Hironaka.HironakaActualSuppliedFlatteningNormalPowers
