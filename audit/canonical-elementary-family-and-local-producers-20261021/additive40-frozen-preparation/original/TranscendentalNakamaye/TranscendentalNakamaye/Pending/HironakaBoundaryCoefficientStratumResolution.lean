import TranscendentalNakamaye.Pending.HironakaNormalCrossingsCoefficientStratumResolution
import TranscendentalNakamaye.Pending.HironakaNormalCrossingsBoundaryTransform

/-!
# Actual coefficient-stratum resolutions retain the whole born boundary

The canonical nonzero-remainder datum includes the SAME entire SNC boundary.
True clopen carrier germs supply its missing transversality; the actual zero
component append uses general whole-boundary selected strict geometry.
Original joint NC coordinates internally discharge highest-stratum/born-E
transversality. No empty-boundary shortcut or caller phase certificate.
Blueprint: `hironaka-boundary-coefficient-stratum-resolution-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace TranscendentalNakamaye.Pending.HironakaBoundaryCoefficientStratumResolution
noncomputable section
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings GermIdealOrder CoefficientIdeal CoefficientIdealRestriction
  CoefficientRestrictionTower HomogenizedGlueingTower MemberInterTowerAlong
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HironakaStepOneSpecialAnalyticLoci HironakaStepOneMemberLowerExtension
  HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaStepOneZeroContactRemainderExtension HironakaCoherentTransformExtension
  HironakaOpenCarrierTestTowerExtension CanonicalCentres HironakaAdmissibleSequence
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsCoefficientStratumResolution
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- All actual original boundary entries remain in the TRUE remainder domain. -/
theorem contactRemainder_boundary_domain (L : MarkedIdeal n X) (hw : L.IsWellFormed)
    (hd : 1≤L.d) :
    let A := contactRemainderMarked L 0
    let F := selectedComponents (n := n) L.N L.cosupp
    let G : Opens X := ⟨Fᶜ,(isClosedSubmanifold_selectedComponents hw.isClosedSubmanifold_N L.cosupp).1.isOpen_compl⟩
    IsInvDomain n A ∧ A.cosupp=L.cosupp∩A.N ∧ A.N⊆G ∧
      MarkedIdeal.pullback (Subtype.val : G→X) A=
        MarkedIdeal.pullback (Subtype.val : G→X) L := by
  dsimp only
  let A := contactRemainderMarked L 0
  let F := selectedComponents (n := n) L.N L.cosupp
  let G : Opens X := ⟨Fᶜ,(isClosedSubmanifold_selectedComponents hw.isClosedSubmanifold_N L.cosupp).1.isOpen_compl⟩
  have hN := hw.isClosedSubmanifold_N
  have hI := hw.isCoherent
  have hDim : ResolutionInvariantSpec.DimLE n L.N n := by
    intro x hx
    obtain ⟨j,hj⟩ := hN.2 x hx
    exact ⟨j,BlowupStrictSubmanifold.le_of_regularAtDim_subset hj
      (AnalyticIrreducibleComponents.regularAtDim_univ x) (subset_univ _),hj⟩
  obtain ⟨hR,hAI,hADim,hnz,hcs⟩ :=
    HironakaOriginalWholeContactRemainderDomain.contactRemainder_geometry_and_nonzero L 0 hN hI hd hDim
  have hAG : A.N⊆G := by
    change remainingComponents (n := n) L.N L.cosupp⊆Fᶜ
    rw [remainingComponents_eq_diff_selected hN]
    exact fun _ hx=>hx.2
  have hTr : IsTransverse n A.N L.E := by
    apply CodimOneAdmissibleAlong.isTransverse_of_forall_eventually
    intro x hx
    have he := eventually_mem_remainingComponents_iff hN hx
    exact ⟨L.N,he.self_of_nhds.mp hx,he,hw.isTransverse⟩
  refine ⟨⟨⟨hR,hAI,hw.isSNCDivisor,hTr⟩,hADim,hd,hnz⟩,hcs,hAG,?_⟩
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · ext x
    change ((x:X)∈remainingComponents (n := n) L.N L.cosupp↔(x:X)∈L.N)
    rw [remainingComponents_eq_diff_selected hN]
    exact ⟨fun hx=>hx.1,fun hx=>⟨hx,x.2⟩⟩
  · rfl
  · rfl
  · rfl

/-- An actual canonical remainder history includes the SAME WHOLE boundary. -/
theorem exists_boundary_remainder_parent_phase (L : MarkedIdeal n X)
    (hw : L.IsWellFormed) (hd : 1≤L.d) (hK : IsCompact L.cosupp) :
    let A := contactRemainderMarked L 0
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonical A ((canonicalInvariant n).inv A) T ∧ IsGeoResolution A T ∧
      IsGeoTestTower L T ∧ CentresIn A.N T ∧
      (geoTransformAlong L T).cosupp∩strictAlong T A.N=∅ := by
  dsimp only
  have hN := hw.isClosedSubmanifold_N
  have hI := hw.isCoherent
  let A := contactRemainderMarked L 0
  let F := selectedComponents (n := n) L.N L.cosupp
  let G : Opens X := ⟨Fᶜ,(isClosedSubmanifold_selectedComponents hN L.cosupp).1.isOpen_compl⟩
  obtain ⟨hA,hcs,hAG,heq⟩ := contactRemainder_boundary_domain L hw hd
  have hKA : IsCompact A.cosupp := by
    rw [hcs]
    exact hK.inter_right hA.isWellFormed.isClosedSubmanifold_N.1
  obtain ⟨Y,T,hcan,hres⟩ := exists_isGeoResolution_isCanonical_of_isCompact (canonicalInvariant n) hA hKA
  have hTL : IsGeoTestTower L T := isGeoTestTower_parent A L G
    hA.isWellFormed.isClosedSubmanifold_N hN hA.isWellFormed.isCoherent hI heq hAG rfl T hres.1
  refine ⟨Y,T,hcan,hres,hTL,?_,?_⟩
  · exact centresIn_of_isGeoTestTower_withN A A.N T hres.1
  · apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyL,hyR⟩
    have hyG : T.proj y∈G := hAG
      (strictAlong_subset_preimage T hA.isWellFormed.isClosedSubmanifold_N.1 hyR)
    let p : openPreimage T G := ⟨y,hyG⟩
    have hcohL := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI T hTL).2
    have hcohA := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent T hres.1).2
    have hp : p∈(MarkedIdeal.pullback (Subtype.val : openPreimage T G→Y) (geoTransformAlong L T)).cosupp := by
      rw [cosupp_pullback_val (geoTransformAlong L T)
        (fun _ _ hg=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcohL hg)]
      exact hyL
    rw [←current_open_record_eq A L G hA.isWellFormed.isClosedSubmanifold_N hN
      hA.isWellFormed.isCoherent hI heq T hres.1 hTL,
      cosupp_pullback_val (geoTransformAlong A T)
        (fun _ _ hg=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcohA hg)] at hp
    have hyA : y∈(geoTransformAlong A T).cosupp := hp
    rw [hres.2] at hyA
    exact hyA

/-- TRUE whole-boundary remainder driver and actual selected-zero append. -/
theorem exists_boundary_resolution_of_positive_codimension_carrier
    (L : MarkedIdeal n X) (hw : L.IsWellFormed) (hd : 1≤L.d) {k : ℕ}
    (hDim : ResolutionInvariantSpec.DimLE n L.N k) (hk : k<n) (hK : IsCompact L.cosupp) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),IsGeoResolution L T ∧ CentresIn L.N T := by
  have hN := hw.isClosedSubmanifold_N
  have hI := hw.isCoherent
  obtain ⟨Y,P,_hcan,_hres,hPL,hPR,hclear⟩ := exists_boundary_remainder_parent_phase L hw hd hK
  let F := selectedComponents (n := n) L.N L.cosupp
  let R := remainingComponents (n := n) L.N L.cosupp
  let C := strictAlong P F
  change (geoTransformAlong L P).cosupp∩strictAlong P R=∅ at hclear
  obtain ⟨hC,hCE,hCcos,hpart,hdis⟩ := selected_strict_geometry L hw P hPL hPR
  have hwP := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw P hPL
  have hCP : C⊆(geoTransformAlong L P).N := fun _ hx=>(geoTransformAlong L P).cosupp_subset_N (hCcos hx)
  have hDimP := InvDomainTowerAlong.dimLE_geoTransformAlong hN hI hDim P hPL
  have hInt : interior C=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hyn : RegularAtDim (n := n) C y n :=
      EmbeddedFromResolution.regularAtDim_of_mem_nhds (mem_interior_iff_mem_nhds.mp hy)
    obtain ⟨j,hj,hreg⟩ := hDimP y (hCP (interior_subset hy))
    have hnle := BlowupStrictSubmanifold.le_of_regularAtDim_subset hyn hreg hCP
    omega
  obtain ⟨Y',tY',cY',mY',π,hπ⟩ := BlowupExistence.exists_isBlowupAlong C hC hInt
  let Z : CMfd.{u} n := {carrier:=Y',topologicalSpace:=tY',chartedSpace:=cY',isComplexManifold:=mY'}
  let T : BlowupTower X Z := .step P C π hπ
  have hTL : IsGeoTestTower L T := ⟨hPL,hC,hCcos,hCE.hasNormalCrossings⟩
  refine ⟨Z,T,⟨hTL,?_⟩,centresIn_of_isGeoTestTower_withN L L.N T hTL⟩
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hNZ : (geoTransformAlong L T).N=BlowupStrictSubmanifold.geoStrictTransform π C (strictAlong P R) := by
    change BlowupStrictSubmanifold.geoStrictTransform π C (geoTransformAlong L P).N=_
    have hpart' : (geoTransformAlong L P).N=strictAlong P R∪C := hpart
    rw [hpart']
    simp only [BlowupStrictSubmanifold.geoStrictTransform,union_sdiff_distrib,sdiff_self,
      union_empty]
  have hzR : π z∈strictAlong P R := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage
    hπ.contMDiff.continuous
    (isClosed_strictAlong P (isClosedSubmanifold_remainingComponents hN L.cosupp).1)
    (hNZ ▸ (geoTransformAlong L T).cosupp_subset_N hz)
  have hzC : π z∉C := fun hc=>Set.disjoint_left.mp hdis hzR hc
  have hzL : π z∈(geoTransformAlong L P).cosupp := TransformOffCentre.mem_cosupp_of_mem_cosupp_geoTransform
    (geoTransformAlong L P) hwP.isClosedSubmanifold_N.1
    (fun _ _ hg=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hwP.isCoherent hg)
    hπ hzC hz
  have hh : π z∈(geoTransformAlong L P).cosupp∩strictAlong P R := ⟨hzL,hzR⟩
  rw [hclear] at hh
  exact hh

/-- Actual SAME joint old/born coordinates give whole highest-carrier transversality. -/
theorem highest_stratum_isTransverse {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {r : ℕ}
    (hbound : ∀ x : X,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x≤r) :
    IsTransverse n {x : X | r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} E := by
  intro x hx
  obtain ⟨Φ,S,B,hsrc,h0,hH,hB,_hinj,hE⟩ := h.2.2 x
  obtain ⟨_hcard,hC⟩ := highest_superlevel_flattening
    (isNormalCrossingsCarrier_of_boundaryAdapted h) hbound hx Φ h0 S hH
  refine ⟨S,B,⟨Φ,hsrc,h0,?_⟩,fun i hi=>⟨(hB i hi).1,(hB i hi).2.symm⟩⟩
  rintro (_ | i) hi y hy hyΦ
  · exact hC y ⟨hy,hyΦ⟩
  · exact hE i hi y ⟨hy,hyΦ⟩

/-- ONLY original coherent I/positive marking/compact cosupport and TRUE adapted
old/born geometry supply a WHOLE stratum phase retaining EVERY boundary entry. -/
theorem exists_original_boundary_nc_coefficient_stratum_resolution
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1≤d)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0<r)
    (hbound : ∀ x : X,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x≤r) :
    let M : MarkedIdeal n X := ⟨univ,E,I,d⟩
    let Z := {x : X | r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let L := withN (coeffMarked M) Z
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),IsGeoResolution L T ∧
      IsGeoTestTower M T ∧ CentresIn Z T ∧
      (geoTransformAlong M T).cosupp∩strictAlong T Z=∅ := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,E,I,d⟩
  let hH := isNormalCrossingsCarrier_of_boundaryAdapted h
  let Z := {x : X | r≤branchMultiplicity hH x}
  let L := withN (coeffMarked M) Z
  have hZ := isClosedSubmanifold_highest_superlevel hH hbound
  have hL : L.ideal.IsCoherent := isCoherent_coeffMarked (𝔪:=M) rfl hI
  have hLW : L.IsWellFormed :=
    ⟨hZ,hL,isSNCDivisor_of_boundaryAdapted h,highest_stratum_isTransverse h hbound⟩
  have hLd : 1≤L.d := by
    change 1≤(Finset.range d).prod (fun i=>d-i)
    have hp : 0<(Finset.range d).prod (fun i=>d-i) := Finset.prod_pos fun i hi=> by
      have hi' := Finset.mem_range.mp hi
      omega
    omega
  have hcs : L.cosupp=M.cosupp∩Z := cosupp_coeff_withN M rfl hI hd Z
  have hKL : IsCompact L.cosupp := by
    rw [hcs]
    exact hK.inter_right hZ.1
  have hRes : ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),IsGeoResolution L T := by
    by_cases hn : 0<n
    · have hDim : ResolutionInvariantSpec.DimLE n L.N (n-r) := fun _ hx=>
        ⟨n-r,le_rfl,regularAtDim_highest_superlevel hH hbound hx⟩
      obtain ⟨Y,T,hT,_hCentres⟩ := exists_boundary_resolution_of_positive_codimension_carrier
        L hLW hLd hDim (by omega) hKL
      exact ⟨Y,T,hT⟩
    · have hZero : Z=∅ := eq_empty_iff_forall_notMem.mpr fun x hx=> by
        have hb := branchMultiplicity_le hH x
        change r≤branchMultiplicity hH x at hx
        omega
      refine ⟨X,.refl,trivial,?_⟩
      change L.cosupp=∅
      rw [hcs,hZero,inter_empty]
  obtain ⟨Y,T,hres⟩ := hRes
  obtain ⟨hTM,hTZ⟩ := (coeff_restrict_tower_iff M rfl hI hd hZ T).1.mp hres.1
  have hcos := (coeff_restrict_tower_iff M rfl hI hd hZ T).2 hres.1
  exact ⟨Y,T,hres,hTM,hTZ,hcos.symm.trans hres.2⟩

end
end TranscendentalNakamaye.Pending.HironakaBoundaryCoefficientStratumResolution
