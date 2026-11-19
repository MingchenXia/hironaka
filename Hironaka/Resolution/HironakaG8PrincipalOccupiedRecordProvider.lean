import Hironaka.Resolution.HironakaG8RestartedPrincipalProvider

/-! Intrinsic principal initialization with a literal inherited ordered boundary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8PrincipalOccupiedRecordProvider
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  NormalCrossings HironakaEmbeddedAnalytic ResolutionInvariantSpec HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaActualFormalInitialDiagram HironakaActualNormalZeroAnalyticSaturation
  HironakaActualOriginalInitialHSPhase HironakaActualGeometricCurrentNeighborhoodHS
  HironakaActualHistoricalHSMarkedDomain HironakaActualHistoricalInitialAffineDictionary
  HironakaG8PrincipalNativeInitialization HironakaG1OriginalWeightedMaximalOrder
  HironakaActualControlledNeighborhoodGenerators HironakaActualFixedFlatteningHSComparison
  HironakaRelativeNormalDeformationInitialRelations HironakaSmoothCentreCoherentDomain
  HironakaSmoothSubmersionGermIdealColon HironakaActualPrescribedCentreRebasing
  HironakaActualOpenEmbeddingVanishingIdeal HomogenizedIdealAlong HironakaG8NativePhaseCertificate
  HironakaG8RestartedPrincipalProvider GermIdealOrder MarkedIdealRestrictOpen

variable {n : ℕ} {X : CMfd.{0} (n+1)}

/-- The actual native producer retains the whole principal vanishing sheaf and
the complete inherited boundary on its returned literal open. -/
theorem exists_principal_native_record_on_inherited_open
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (n+1) E)
    (x : X) (hx : x ∈ singularSet (n := n+1) W)
    (hInvertible : (vanishingIdeal (n := n+1) W).IsInvertible) :
    ∃ (V : Opens X) (hxV : x ∈ V) (q : ℕ),
      let W' := (Subtype.val : V → X) ⁻¹' W
      let Q : MarkedIdeal (n+1) (CMfd.of (n := n+1) V) := ⟨univ,E.map ((Subtype.val : V → X) ⁻¹' ·),vanishingIdeal (n := n+1) W',q⟩
      order (n+1) univ (vanishingIdeal (n := n+1) W) x = q ∧
      IsInvDomain (n+1) Q ∧ IsMaximalOrderAlong Q.N Q.ideal q ∧
      (⟨x,hxV⟩ : V) ∈ Q.cosupp ∧
      Q.cosupp = {v | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n+1) W) v.val ℓ =
        hilbertSamuelAt (vanishingIdeal (n := n+1) W) x ℓ} ∧
      Q.cosupp ⊆ (Subtype.val : V → X) ⁻¹' singularSet (n := n+1) W := by
  have hp : NonzeroPrincipalAt (vanishingIdeal (n := n+1) W) x := by
    obtain ⟨U,hU,hxU,f,hf,hNonzero,hGen⟩ := hInvertible x
    refine ⟨f,InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU hf hxU,?_,hGen x hxU⟩
    intro hZero
    obtain ⟨O,hO,hOpen,hxO⟩ := mem_nhds_iff.mp (hZero.and (hU.mem_nhds hxU))
    obtain ⟨y,hy,hfy⟩ := hNonzero O hOpen (fun z hz => (hO hz).2) ⟨x,hxO⟩
    exact hfy (hO hy).1
  obtain ⟨Φ,hΦsrc,hΦ0⟩ := NormalCrossings.exists_centred_coordinates (n := n+1) x
  obtain ⟨Ψ,hΨ0,hΞsrc,hΞ0,G,_S,P,hSpan,_hMem,hw,_hPrefix,_hContact,_hJac,hU,hRef,
    V,η,hxV,hη,_hCov,hDom,hCos,hSing,hZero,_hTerminal⟩ :=
    exists_original_initial_hs_phase W hW x hx E hE Φ hΦsrc hΦ0
  let Ξ := currentCoordinateFlattening x Φ hΦ0 Ψ hΨ0
  let W₀ := actualFixedFlatteningSet x Ξ W
  let U := presentationOpen P
  let b : U → X := fun y => (η y : X)
  let Q₀ : MarkedIdeal (n+1) U := initialWeightedRecord P b E
  obtain ⟨g,hg,hI⟩ := flattened_origin_principal_of_intrinsic W hW x hp Ξ hΞsrc hΞ0
  have hSet : (Subtype.val : U → ComplexModel (n+1)) ⁻¹' W₀ = b ⁻¹' W := by
    ext y
    change (y.val ∈ Ξ.target ∧ actualFlatteningInverseMap x Ξ y.val ∈ W) ↔ (η y : X) ∈ W
    rw [hη]
    exact and_iff_right (hU y.property)
  have hIdeal : Q₀.ideal = vanishingIdeal (n := n+1) (b ⁻¹' W) := by
    rw [← hSet]
    exact principal_initialWeightedRecord_ideal P g hg hI hw b
  have hBound : IsMaximalOrderAlong Q₀.N Q₀.ideal Q₀.d :=
    initialWeightedRecord_maximalOrder P hSpan hRef hw b E hDom
  let Qv : MarkedIdeal (n+1) V :=
    ⟨univ,E.map ((Subtype.val : V → X) ⁻¹' ·),
      vanishingIdeal (n := n+1) ((Subtype.val : V → X) ⁻¹' W),Q₀.d⟩
  have hInv : ((η.symm : V → U) ⁻¹' (b ⁻¹' W)) = (Subtype.val : V → X) ⁻¹' W := by
    ext y
    change (η (η.symm y) : X) ∈ W ↔ (y : X) ∈ W
    rw [η.apply_symm_apply]
  have hQv : MarkedIdeal.pullback η.symm Q₀ = Qv := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ rfl
    · exact preimage_univ
    · change (E.map (b ⁻¹' ·)).map ((η.symm : V → U) ⁻¹' ·) = _
      rw [List.map_map]
      apply List.map_congr_left
      intro Z _
      ext y
      change (η (η.symm y) : X) ∈ Z ↔ (y : X) ∈ Z
      rw [η.apply_symm_apply]
    ·
      change GermIdeal.pullback (m := n+1) η.symm Q₀.ideal = Qv.ideal
      rw [hIdeal,pullback_vanishingIdeal_of_biholomorphism,hInv]
  have hDomV := InvDomainTowerAlong.isInvDomain_pullback η.symm hDom
  change IsInvDomain (n+1) (MarkedIdeal.pullback η.symm Q₀) at hDomV
  rw [hQv] at hDomV
  have hCosV : Qv.cosupp = (η.symm : V → U) ⁻¹' Q₀.cosupp := by
    rw [← hQv]
    exact cosupp_pullback η.symm.contMDiff η.contMDiff η.symm_apply_apply η.apply_symm_apply Q₀
      (fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hDom.isWellFormed.isCoherent hf)
  let Qhi : MarkedIdeal (n+1) U := {Q₀ with d := Q₀.d+1}
  have hCapV : IsMaximalOrderAlong Qv.N Qv.ideal Qv.d := by
    have hHi := cosupp_pullback η.symm.contMDiff η.contMDiff η.symm_apply_apply η.apply_symm_apply Qhi
      (fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hDom.isWellFormed.isCoherent hf)
    intro y hy
    have hy' : y ∈ (MarkedIdeal.pullback η.symm Qhi).cosupp := by
      change y ∈ ({MarkedIdeal.pullback η.symm Q₀ with d := Q₀.d+1}).cosupp
      rwa [hQv]
    rw [hHi] at hy'
    exact hBound (η.symm y) hy'
  have hProfile : Qv.cosupp = {v : V | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n+1) W) v.val ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n+1) W) x ℓ} := by
    rw [hCosV]
    change Q₀.cosupp = _ at hCos
    rw [hCos]
    ext y
    change (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n+1) W) (η (η.symm y) : X) ℓ = _) ↔ _
    rw [η.apply_symm_apply]
    rfl
  have hAt : (⟨x,hxV⟩ : V) ∈ Qv.cosupp := by
    rw [hProfile]
    exact fun _ => rfl
  let A (r : ℕ) : MarkedIdeal (n+1) X := ⟨univ,E,vanishingIdeal (n := n+1) W,r⟩
  have hpull (r : ℕ) : MarkedIdeal.pullback (Subtype.val : V → X) (A r) = {Qv with d := r} := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of preimage_univ rfl ?_ rfl
    exact pullback_vanishingIdeal_of_isOpenHoloEmbedding _ (HironakaBaseChange.isOpenHoloEmbedding_val V) W
  have hCut (r : ℕ) : (⟨x,hxV⟩ : V) ∈ ({Qv with d := r} : MarkedIdeal (n+1) V).cosupp ↔
      x ∈ (A r).cosupp := by
    rw [← hpull r,cosupp_pullback_val (A r) (fun _ _ hf => hf.1) V]
    rfl
  have hAtOrder : order (n+1) univ (vanishingIdeal (n := n+1) W) x = Q₀.d := by
    have hLo := (hCut Q₀.d).1 hAt
    have hHi : x ∉ (A (Q₀.d+1)).cosupp :=
      fun hx' => hCapV ⟨x,hxV⟩ ((hCut (Q₀.d+1)).2 hx')
    have hOrd (r : ℕ) : (r : ℕ∞) ≤ order (n+1) univ (vanishingIdeal (n := n+1) W) x ↔ x ∈ (A r).cosupp := by
      rw [le_order_iff (𝔞 := vanishingIdeal (n := n+1) W) (fun _ hg => hg.1)]
      exact ⟨fun h => ⟨mem_univ x,h⟩,And.right⟩
    have hLT : order (n+1) univ (vanishingIdeal (n := n+1) W) x < (↑(Q₀.d+1) : ℕ∞) :=
      lt_of_not_ge (fun h => hHi ((hOrd (Q₀.d+1)).1 h))
    have hLT' : order (n+1) univ (vanishingIdeal (n := n+1) W) x < (Q₀.d : ℕ∞) + 1 := by
      exact_mod_cast hLT
    exact le_antisymm ((ENat.lt_add_one_iff (by simp)).1 hLT') ((hOrd Q₀.d).2 hLo)
  refine ⟨V,hxV,Q₀.d,hAtOrder,hDomV,hCapV,hAt,hProfile,?_⟩
  intro y hy
  have hy₀ : η.symm y ∈ Q₀.cosupp := by
    change y ∈ Qv.cosupp at hy
    rwa [hCosV] at hy
  have hyS := hSing hy₀
  change (η (η.symm y) : X) ∈ singularSet (n := n+1) W at hyS
  rw [η.apply_symm_apply] at hyS
  exact hyS

end
end Hironaka.HironakaG8PrincipalOccupiedRecordProvider
