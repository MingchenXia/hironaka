import Hironaka.Resolution.HironakaActualInheritedFreeProductPresentation
import Hironaka.Resolution.HironakaActualFreeProductFlattening
import Hironaka.Resolution.HironakaActualInheritedContactSpanCentre
import Hironaka.Resolution.HironakaActualInheritedEssentialPriority

/-! Natural original-HS composition of the SAME historical presentation.
The original HS/contact producer gives the source essential plane; actual
source priority chooses its free-first permutation; genuine zero-section
reflection and the restricted product map flatten the SAME C. The returned
germ map is proved to be inverse pullback by the actual final chart.
No compatible flattening, target diagram/HS or fresh selector is supplied.
Blueprint: hir:actual-original-hs-free-product-presentation.
Complete source draft only; no elaboration or kernel acceptance is claimed. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology ContDiff Manifold

namespace Hironaka.HironakaActualInheritedFreeProductPresentation
noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalDeformationInitialRelations HironakaSmoothCentreCoherentDomain
  HironakaHolomorphicJetChartInvariance HironakaActualCoefficientPresentationCentrePower
  HironakaActualFormalInitialDiagram HironakaActualRelativeNormalJetDivision
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualInheritedNestedContactFlag
  HironakaActualFixedInheritedSelector HironakaActualFixedInheritedSelectorPermutation
  HironakaActualInheritedSourcePermutationFamily HironakaActualInheritedSourceOwnerPermutation
  HironakaActualInheritedCurrentSourceRelabel
  HironakaActualInheritedEssentialPriority HironakaActualInheritedContactSpanCentre
  HironakaActualInheritedHSContactContainment HironakaActualFreeProductFlattening
  HironakaActualFreeProductGermTransport HironakaActualZeroSectionCentreGeometry

private theorem centre_model_regular_iff (n k : ℕ) (C : Set (ComplexModel n)) :
    RegularAtDim (n := n) C 0 k ↔
      k ≤ n ∧ (0 : ComplexModel n) ∈ C ∧
        ∃ Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n),
          Φ.toFun 0 = 0 ∧ ∀ {y}, y ∈ Φ.source →
            (y ∈ C ↔ Φ.toFun y ∈ complexCoordinatePlane n k) := by
  simp [RegularAtDim, complexChartAt, chartAt_self_eq]
  intro _ _
  rfl

/-- Precomposition by an actual global linear change keeps the real domains
and both inverse identities. In the final chart L is the OLD-to-priority map. -/
private def centrePrecomposeLinear {n : ℕ}
    (L : ComplexModel n ≃L[ℂ] ComplexModel n)
    (Ψ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) :
    LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) where
  source := L ⁻¹' Ψ.source
  target := Ψ.target
  isOpen_source := Ψ.isOpen_source.preimage L.continuous
  isOpen_target := Ψ.isOpen_target
  center_mem_source := by simpa only [mem_preimage, map_zero] using Ψ.center_mem_source
  toFun := Ψ.toFun ∘ L
  invFun := L.symm ∘ Ψ.invFun
  toFun_holomorphic := Ψ.toFun_holomorphic.comp L.differentiable.differentiableOn
    (fun _ hz => hz)
  invFun_holomorphic := L.symm.differentiable.comp_differentiableOn Ψ.invFun_holomorphic
  mapsTo_toFun := fun z hz => Ψ.mapsTo_toFun hz
  mapsTo_invFun := by
    intro z hz
    change L (L.symm (Ψ.invFun z)) ∈ Ψ.source
    rw [L.apply_symm_apply]
    exact Ψ.mapsTo_invFun hz
  left_inv := by
    intro z hz
    change L.symm (Ψ.invFun (Ψ.toFun (L z))) = z
    rw [Ψ.left_inv (L z) hz, L.symm_apply_apply]
  right_inv := by
    intro z hz
    change Ψ.toFun (L (L.symm (Ψ.invFun z))) = z
    rw [L.apply_symm_apply]
    exact Ψ.right_inv z hz

private theorem centre_regular_linear_preimage {n k : ℕ}
    (L : ComplexModel n ≃L[ℂ] ComplexModel n) (C : Set (ComplexModel n))
    (hreg : RegularAtDim (n := n) C 0 k) :
    RegularAtDim (n := n) (L ⁻¹' C) 0 k := by
  obtain ⟨hkn, h0C, Θ, hΘ0, hflat⟩ := (centre_model_regular_iff n k C).mp hreg
  apply (centre_model_regular_iff n k (L ⁻¹' C)).mpr
  refine ⟨hkn, ?_, centrePrecomposeLinear L Θ, ?_, ?_⟩
  · simpa only [mem_preimage, map_zero] using h0C
  · change Θ.toFun (L 0) = 0
    simpa only [map_zero] using hΘ0
  · intro z hz
    exact hflat hz

private theorem centre_source_members {n : ℕ}
    (A : GermIdeal n (ComplexModel n))
    (G : ActualAnalyticInheritedFamily n 0 (actualInheritedOriginFormalIdeal A))
    (hspan : Ideal.span (Set.range G.germs) = originalCoherentOriginIdeal A) :
    ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ actualInheritedOriginFormalIdeal A := by
  intro a
  apply Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom
  rw [← hspan]
  exact Ideal.subset_span ⟨a, rfl⟩

private theorem centre_complement_card {n : ℕ} (B : Set (Fin n)) :
    Fintype.card (↥(Bᶜ)) + Fintype.card B = n := by
  simpa only [Fintype.card_sum, Fintype.card_fin] using
    Fintype.card_congr ((Equiv.sumComm (↥(Bᶜ)) B).trans (Equiv.Set.sumCompl B))

private theorem centre_priority_pure {n : ℕ}
    {K : Ideal (MvPowerSeries (Fin n) ℂ)}
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) :
    let B := fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex K)
    let m := Fintype.card (↥(Bᶜ))
    let p := essentialFreeFirstEquiv B
    ∀ a : actualInitialVertices MonomialOrder.degLex (Ideal.map (MvPowerSeries.rename p).toRingHom K),
      ∀ i : Fin n, ¬ m ≤ i.val → a.val i = 0 := by
  dsimp only
  let B := fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex K)
  let p := essentialFreeFirstEquiv B
  intro a i hi
  obtain ⟨a, rfl⟩ := (actualSourcePermutationVertexEquiv G hmem p
    (essentialPriority_family_lower G)).surjective a
  rw [actualSourcePermutationVertexEquiv_val, sourceExponentPermutation_apply]
  by_contra hai
  have hB : p.symm i ∈ B := ⟨a, hai⟩
  have himage : i ∈ p '' B := ⟨p.symm i, hB, p.apply_symm_apply i⟩
  rw [essentialFreeFirstEquiv_block_image] at himage
  exact hi himage

private theorem centre_inverse_product_germ {m e : ℕ}
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0 = 0)
    (Ψ : LocalHolomorphicEquivAt (n := m+e) (0 : ComplexModel (m+e)))
    (hΨ0 : Ψ.toFun 0 = 0)
    (hinv : Ψ.invFun = (actual_zeroSection_localEquiv m e 0 χ).invFun) :
    (localGermAlgEquiv Ψ hΨ0).symm = actualFreeProductGermEquiv m e χ hχ0 := by
  apply AlgEquiv.ext
  intro F
  induction F using HolGerm.induction_on with
  | h f hf =>
    have hl := holomorphic_comp Ψ.invFun (local_invFun_holomorphic Ψ hΨ0)
      (local_invFun_zero Ψ hΨ0) hf
    have hr : HolAt (f ∘ (actual_zeroSection_localEquiv m e 0 χ).invFun) 0 := by
      simpa only [hinv] using hl
    change HolGerm.mk (f ∘ Ψ.invFun) hl =
      HolGerm.mk (f ∘ (actual_zeroSection_localEquiv m e 0 χ).invFun) hr
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => congrArg f (congrFun hinv z)

/-- Only actual dimension equality is used here; it supplies no geometry or
presentation certificate. The returned chart still has the ORIGINAL model. -/
private theorem centre_product_dimension {n m e k : ℕ} (hdim : m+e=n)
    (C : Set (ComplexModel n)) (hreg : RegularAtDim (n := n) C 0 k)
    (hplane : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ C → z ∈ complexCoordinatePlane n m) :
    ∃ (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0 = 0),
    ∃ (Ψ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (hΨ0 : Ψ.toFun 0 = 0),
      Ψ.toFun = (hdim ▸ (actual_zeroSection_localEquiv m e 0 χ).toFun) ∧
      Ψ.invFun = (hdim ▸ (actual_zeroSection_localEquiv m e 0 χ).invFun) ∧
      Ψ.source ⊆ (hdim ▸ (actual_zeroSection_localEquiv m e 0 χ).source) ∧
      (∀ z ∈ Ψ.source, z ∈ C ↔ Ψ.toFun z ∈ complexCoordinatePlane n k) ∧
      (localGermAlgEquiv Ψ hΨ0).symm = (hdim ▸ actualFreeProductGermEquiv m e χ hχ0) := by
  subst n
  obtain ⟨χ, hχ0, Ψ, hΨ0, hto, hinv, hsrc, hflat, _hessential, _hinvEssential⟩ :=
    exists_actual_same_centre_free_product_flattening m e k C hreg hplane
  exact ⟨χ, hχ0, Ψ, hΨ0, hto, hinv, hsrc, hflat,
    centre_inverse_product_germ χ hχ0 Ψ hΨ0 hinv⟩

private theorem centre_family_dimension {n m e : ℕ} (hdim : m+e=n)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0 = 0)
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K)
    (hpure : ∀ a : actualInitialVertices MonomialOrder.degLex K,
      ∀ i : Fin n, ¬ m ≤ i.val → a.val i = 0) :
    let E : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) :=
      hdim ▸ actualFreeProductGermEquiv m e χ hχ0
    let I := Ideal.span (Set.range G.germs)
    let K' := actualInheritedCurrentSourceIdeal (Ideal.map E.toRingEquiv.toRingHom I)
    actualInitialDiagram MonomialOrder.degLex K' = actualInitialDiagram MonomialOrder.degLex K ∧
      ∃ hV : actualInitialVertices MonomialOrder.degLex K =
          actualInitialVertices MonomialOrder.degLex K',
      ∃ G' : ActualAnalyticInheritedFamily n 0 K',
        (∀ a, G'.germs (sourceVertexSetCast hV a) = E (G.germs a)) ∧
        Ideal.span (Set.range G'.germs) = Ideal.map E.toRingEquiv.toRingHom I ∧
        (∀ a, actualUnshiftedTaylorAlgHom n (G'.germs a) ∈ K') ∧
        (∀ k, ActualInheritedPrefixReducedAt G k → ActualInheritedPrefixReducedAt G' k) ∧
        ∀ S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K),
          (∀ k, actualFixedSelectorContactAt S G.germs k →
            actualFixedSelectorContactAt (sourceFixedSelectorCast hV S) G'.germs k) ∧
          ∀ k, (actualFixedSelectorJacobian (sourceFixedSelectorCast hV S) G'.germs k).submatrix
            (sourceBlockCast hV k) (sourceBlockCast hV k) = actualFixedSelectorJacobian S G.germs k := by
  subst n
  exact actualFreeProduct_same_family_initialDiagram χ hχ0 K G hmem hpure

private theorem centre_inverse_permutation_product {n : ℕ} (p : Fin n ≃ Fin n)
    (Ψ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
    (hΨ0 : Ψ.toFun 0 = 0) :
    let R := actualPermutationLinearEquiv p
    let Φ := centrePrecomposeLinear R.symm Ψ
    let hΦ0 : Φ.toFun 0 = 0 := by
      change Ψ.toFun ((actualPermutationLinearEquiv p).symm 0) = 0
      simpa only [map_zero] using hΨ0
    (localGermAlgEquiv Φ hΦ0).symm =
      (actualPermutationGermEquiv p).trans (localGermAlgEquiv Ψ hΨ0).symm := by
  dsimp only
  apply AlgEquiv.ext
  intro F
  induction F using HolGerm.induction_on with
  | h f hf =>
    have hR := holomorphic_comp (actualPermutationLinearEquiv p)
      (Eventually.of_forall fun z => (actualPermutationLinearEquiv p).differentiableAt)
      (map_zero (actualPermutationLinearEquiv p)) hf
    have hcomp := holomorphic_comp Ψ.invFun (local_invFun_holomorphic Ψ hΨ0)
      (local_invFun_zero Ψ hΨ0) hR
    change HolGerm.mk (f ∘ ((actualPermutationLinearEquiv p) ∘ Ψ.invFun)) hcomp =
      HolGerm.mk ((f ∘ (actualPermutationLinearEquiv p)) ∘ Ψ.invFun) hcomp
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun _ => rfl

/-- ONLY original local FG, the SAME current inherited family and historical
selector, source whole (4)/(5), and original local HS constancy on the SAME
regular C produce one compatible free-product flattening and presentation.
The returned whole-germ map is the actual inverse pullback of the returned
OLD-to-flat chart; historical labels and selectors are never reselected. -/
theorem exists_actual_original_hs_free_product_presentation {n k : ℕ}
    (A : GermIdeal n (ComplexModel n)) (hfg : IdealFGAt A.mem 0)
    (G : ActualAnalyticInheritedFamily n 0 (actualInheritedOriginFormalIdeal A))
    (hspan : Ideal.span (Set.range G.germs) = originalCoherentOriginIdeal A)
    (hred : ∀ r, ActualInheritedPrefixReducedAt G r)
    (S : ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (actualInheritedOriginFormalIdeal A)))
    (hadapt : ∀ r, actualFixedSelectorContactAt S G.germs r)
    (C : Set (ComplexModel n)) (hreg : RegularAtDim (n := n) C 0 k)
    (hHS : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ C →
      ∀ ℓ : ℕ, hilbertSamuelAt A z ℓ = hilbertSamuelAt A 0 ℓ) :
    let K := actualInheritedOriginFormalIdeal A
    let B := fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex K)
    let p := essentialFreeFirstEquiv B
    let hmem := centre_source_members A G hspan
    let Gp := actualSourcePermutedInheritedFamily G hmem p (essentialPriority_family_lower G)
    let Sp := actualSourcePermutedFixedSelector G hmem p (essentialPriority_family_lower G) S
    let Kp := Ideal.map (MvPowerSeries.rename p).toRingHom K
    let R := actualPermutationLinearEquiv p
    ∃ (m e : ℕ) (hdim : m+e=n),
    ∃ (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0 = 0),
    ∃ (Ψ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (_hΨ0 : Ψ.toFun 0 = 0),
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (hΦ0 : Φ.toFun 0 = 0),
      m = Fintype.card (↥(Bᶜ)) ∧ e = Fintype.card B ∧
      Ψ.toFun = (hdim ▸ (actual_zeroSection_localEquiv m e 0 χ).toFun) ∧
      Ψ.invFun = (hdim ▸ (actual_zeroSection_localEquiv m e 0 χ).invFun) ∧
      Ψ.source ⊆ (hdim ▸ (actual_zeroSection_localEquiv m e 0 χ).source) ∧
      Φ.toFun = Ψ.toFun ∘ R.symm ∧ Φ.invFun = R ∘ Ψ.invFun ∧
      Φ.source = R.symm ⁻¹' Ψ.source ∧
      (∀ z ∈ Φ.source, z ∈ C ↔ Φ.toFun z ∈ complexCoordinatePlane n k) ∧
      let E0 : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) :=
        hdim ▸ actualFreeProductGermEquiv m e χ hχ0
      let E := (localGermAlgEquiv Φ hΦ0).symm
      let K' := actualInheritedCurrentSourceIdeal (Ideal.map E.toRingEquiv.toRingHom
        (originalCoherentOriginIdeal A))
      E = (actualPermutationGermEquiv p).trans E0 ∧
      actualInitialDiagram MonomialOrder.degLex K' = actualInitialDiagram MonomialOrder.degLex Kp ∧
      ∃ hV : actualInitialVertices MonomialOrder.degLex Kp =
          actualInitialVertices MonomialOrder.degLex K',
      ∃ G' : ActualAnalyticInheritedFamily n 0 K',
        (∀ a, G'.germs (sourceVertexSetCast hV
          (actualSourcePermutationVertexEquiv G hmem p (essentialPriority_family_lower G) a)) =
            E (G.germs a)) ∧
        Ideal.span (Set.range G'.germs) = Ideal.map E.toRingEquiv.toRingHom
          (originalCoherentOriginIdeal A) ∧
        (∀ a, actualUnshiftedTaylorAlgHom n (G'.germs a) ∈ K') ∧
        (∀ r, ActualInheritedPrefixReducedAt G' r) ∧
        (∀ r, actualFixedSelectorContactAt (sourceFixedSelectorCast hV Sp) G'.germs r) ∧
        (∀ r, (actualFixedSelectorJacobian (sourceFixedSelectorCast hV Sp) G'.germs r).submatrix
          (sourceBlockCast hV r) (sourceBlockCast hV r) = actualFixedSelectorJacobian Sp Gp.germs r) ∧
        ∀ r, ((actualFixedSelectorJacobian (sourceFixedSelectorCast hV Sp) G'.germs r).submatrix
          (sourceBlockCast hV r) (sourceBlockCast hV r)).submatrix
            ((fixedBlockPermutation p _ r).trans (sourceBlockCast
              (actualSourcePermutationVertices_eq G hmem p (essentialPriority_family_lower G)).symm r))
            ((fixedBlockPermutation p _ r).trans (sourceBlockCast
              (actualSourcePermutationVertices_eq G hmem p (essentialPriority_family_lower G)).symm r)) =
          actualFixedSelectorJacobian S G.germs r := by
  let K := actualInheritedOriginFormalIdeal A
  let B := fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex K)
  let p := essentialFreeFirstEquiv B
  let hmem := centre_source_members A G hspan
  let hlower := essentialPriority_family_lower G
  let Gp := actualSourcePermutedInheritedFamily G hmem p hlower
  let Sp := actualSourcePermutedFixedSelector G hmem p hlower S
  let Kp := Ideal.map (MvPowerSeries.rename p).toRingHom K
  let R := actualPermutationLinearEquiv p
  let m := Fintype.card (↥(Bᶜ))
  let e := Fintype.card B
  have hdim : m+e=n := centre_complement_card B
  obtain ⟨_hcoord, U, hU, h0U, hCplane⟩ :=
    actual_hs_centre_germ_subset_historical_plane A hfg G hspan hred S hadapt C hHS
  obtain ⟨hBimage, _hcurrent, hprefixP, hcontactP, _hdetP⟩ :=
    actual_essentialFreeFirst_same_family_transport G hmem S
  have hBimage' : p '' B = {i : Fin n | m ≤ i.val} := hBimage
  let Cp : Set (ComplexModel n) := R ⁻¹' C
  have hCpReg : RegularAtDim (n := n) Cp 0 k := centre_regular_linear_preimage R C hreg
  have hCpPlane : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      z ∈ Cp → z ∈ complexCoordinatePlane n m := by
    have hpreopen : IsOpen (R ⁻¹' U) := hU.preimage R.continuous
    have h0pre : (0 : ComplexModel n) ∈ R ⁻¹' U := by
      simpa only [mem_preimage, map_zero] using h0U
    filter_upwards [hpreopen.mem_nhds h0pre] with z hz hCz j hj
    have hjimage : j ∈ p '' B := by
      rw [hBimage']
      exact hj
    obtain ⟨i, hi, rfl⟩ := hjimage
    exact hCplane (R z) hz hCz i hi
  obtain ⟨χ, hχ0, Ψ, hΨ0, hΨto, hΨinv, hΨsrc, hΨflat, hΨgerm⟩ :=
    centre_product_dimension hdim Cp hCpReg hCpPlane
  let Φ := centrePrecomposeLinear R.symm Ψ
  have hΦ0 : Φ.toFun 0 = 0 := by
    change Ψ.toFun (R.symm 0) = 0
    simpa only [map_zero] using hΨ0
  have hΦflat (z : ComplexModel n) (hz : z ∈ Φ.source) :
      z ∈ C ↔ Φ.toFun z ∈ complexCoordinatePlane n k := by
    have hflat := hΨflat (R.symm z) hz
    change z ∈ C ↔ Ψ.toFun (R.symm z) ∈ complexCoordinatePlane n k
    simpa only [Cp, mem_preimage, R.apply_symm_apply] using hflat
  let E0 : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) :=
    hdim ▸ actualFreeProductGermEquiv m e χ hχ0
  let E := (localGermAlgEquiv Φ hΦ0).symm
  have hEgerm : E = (actualPermutationGermEquiv p).trans E0 := by
    have hcomp := centre_inverse_permutation_product p Ψ hΨ0
    change E = (actualPermutationGermEquiv p).trans (localGermAlgEquiv Ψ hΨ0).symm at hcomp
    exact hcomp.trans (congrArg (fun D => (actualPermutationGermEquiv p).trans D) hΨgerm)
  have hGpMem : ∀ a, actualUnshiftedTaylorAlgHom n (Gp.germs a) ∈ Kp :=
    actualSourcePermutedInheritedFamily_mem G hmem p hlower
  have hGpPure : ∀ a : actualInitialVertices MonomialOrder.degLex Kp,
      ∀ i : Fin n, ¬ m ≤ i.val → a.val i = 0 := centre_priority_pure G hmem
  have hGpSpan : Ideal.span (Set.range Gp.germs) =
      Ideal.map (actualPermutationGermEquiv p).toRingEquiv.toRingHom
        (originalCoherentOriginIdeal A) := by
    rw [actualSourcePermutedInheritedFamily_span, hspan]
  have hIdeal : Ideal.map E0.toRingEquiv.toRingHom (Ideal.span (Set.range Gp.germs)) =
      Ideal.map E.toRingEquiv.toRingHom (originalCoherentOriginIdeal A) := by
    rw [hGpSpan, Ideal.map_map, hEgerm]
    rfl
  have hFamily := centre_family_dimension hdim χ hχ0 Kp Gp hGpMem hGpPure
  dsimp only at hFamily
  rw [hIdeal] at hFamily
  obtain ⟨hD, hV, G', hliteral, hspan', hmem', hred', hhistorical⟩ := hFamily
  obtain ⟨hcontact', hJac'⟩ := hhistorical Sp
  refine ⟨m, e, hdim, χ, hχ0, Ψ, hΨ0, Φ, hΦ0, rfl, rfl,
    hΨto, hΨinv, hΨsrc, rfl, rfl, rfl, hΦflat, hEgerm,
    hD, hV, G', ?_, hspan', hmem', ?_, ?_, hJac', ?_⟩
  · intro a
    rw [hliteral, actualSourcePermutedInheritedFamily_germ]
    change E0 ((actualPermutationGermEquiv p) (G.germs a)) = E (G.germs a)
    rw [hEgerm]
    rfl
  · intro r
    exact hred' r (hprefixP r (hred r))
  · intro r
    exact hcontact' r (hcontactP r (hadapt r))
  · intro r
    rw [hJac']
    exact actualSourcePermutedFixedSelector_jacobian G hmem p hlower S r

end
end Hironaka.HironakaActualInheritedFreeProductPresentation
