import TranscendentalNakamaye.Pending.HironakaNormalCrossingsCoefficientBranchHistories

/-!
# An actual selected-zero append resolves the entire coefficient stratum

The true original component split constructs the final zero-component centre.
Its SAME ideal/mark cosupport condition, smoothness and whole-boundary NC are
proved, then its real positive-codimension blowup kills that carrier component.
No nonzero/phase/parent-test/terminal certificate is supplied. Clearing the
strict stratum does not claim a smaller GLOBAL old count outside cosupport.
Blueprint: `hironaka-normal-crossings-coefficient-stratum-resolution-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace TranscendentalNakamaye.Pending.HironakaNormalCrossingsCoefficientStratumResolution
noncomputable section
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings GermIdealOrder CoefficientIdeal CoefficientIdealRestriction
  CoefficientRestrictionTower HomogenizedGlueingTower MemberInterTowerAlong
  HironakaStepOneSpecialAnalyticLoci HironakaStepOneMemberLowerExtension
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaStepOneMemberTailExtension
  HironakaStepOneZeroContactRemainderExtension
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsCoefficientRemainderPhase
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem component_partition (L : MarkedIdeal n X) (hN : IsClosedSubmanifold n L.N) :
    L.N=remainingComponents (n := n) L.N L.cosupp∪selectedComponents (n := n) L.N L.cosupp ∧
      Disjoint (remainingComponents (n := n) L.N L.cosupp) (selectedComponents (n := n) L.N L.cosupp) := by
  have hF : selectedComponents (n := n) L.N L.cosupp⊆L.N := by
    rintro x ⟨B,⟨_hB,hBcos⟩,hxB⟩
    exact L.cosupp_subset_N (hBcos hxB)
  rw [remainingComponents_eq_diff_selected hN]
  exact ⟨(sdiff_union_of_subset hF).symm,disjoint_sdiff_left⟩

private theorem selected_strict_subset_cosupp (L : MarkedIdeal n X) (hw : L.IsWellFormed) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower L T→
      CentresIn (remainingComponents (n := n) L.N L.cosupp) T→
      strictAlong T (selectedComponents (n := n) L.N L.cosupp)⊆(geoTransformAlong L T).cosupp
  | _,.refl,_,_ => by
    rintro x ⟨B,⟨_hB,hBcos⟩,hxB⟩
    exact hBcos hxB
  | _,.step T C π hπ,hT,hTR => by
    intro z hz
    have hF := isClosedSubmanifold_selectedComponents hw.isClosedSubmanifold_N L.cosupp
    have hR := isClosedSubmanifold_remainingComponents hw.isClosedSubmanifold_N L.cosupp
    have hdis := disjoint_strictAlong T hR.1 hF.1 (component_partition L hw.isClosedSubmanifold_N).2
    have hzF : π z∈strictAlong T (selectedComponents (n := n) L.N L.cosupp) :=
      BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous
        (isClosed_strictAlong T hF.1) hz
    have hzC : π z∉C := fun hc=>Set.disjoint_left.mp hdis (hTR.2 hc) hzF
    exact TransformOffCentre.mem_cosupp_geoTransform_of_mem_cosupp (geoTransformAlong L T)
      (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT.1).isClosedSubmanifold_N.1
      hπ hzC (selected_strict_subset_cosupp L hw T hT.1 hTR.1 hzF)

/-- The ACTUAL whole selected strict union has derived smoothness, born-boundary
transversality and SAME-current-ideal cosupport membership. -/
theorem selected_strict_geometry (L : MarkedIdeal n X) (hw : L.IsWellFormed)
    (T : BlowupTower X Y) (hT : IsGeoTestTower L T)
    (hTR : CentresIn (remainingComponents (n := n) L.N L.cosupp) T) :
    let F := selectedComponents (n := n) L.N L.cosupp
    let R := remainingComponents (n := n) L.N L.cosupp
    IsClosedSubmanifold n (strictAlong T F) ∧
      IsTransverse n (strictAlong T F) (geoTransformAlong L T).E ∧
      strictAlong T F⊆(geoTransformAlong L T).cosupp ∧
      (geoTransformAlong L T).N=strictAlong T R∪strictAlong T F ∧
      Disjoint (strictAlong T R) (strictAlong T F) := by
  dsimp only
  let F := selectedComponents (n := n) L.N L.cosupp
  let R := remainingComponents (n := n) L.N L.cosupp
  have hF := isClosedSubmanifold_selectedComponents hw.isClosedSubmanifold_N L.cosupp
  have hR := isClosedSubmanifold_remainingComponents hw.isClosedSubmanifold_N L.cosupp
  obtain ⟨hpart,hdis⟩ := component_partition L hw.isClosedSubmanifold_N
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT
  have hev : ∀ x∈strictAlong T F,∀ᶠ y in 𝓝 x,y∈strictAlong T F↔y∈(geoTransformAlong L T).N := by
    intro x hx
    rw [N_geoTransformAlong]
    exact eventually_mem_strictAlong_iff_of_closed_partition hF.1 hR.1 hdis.symm
      (hpart.trans (union_comm _ _)) T hx
  have hFT : IsClosedSubmanifold n (strictAlong T F) := by
    refine ⟨isClosed_strictAlong T hF.1,?_⟩
    intro x hx
    obtain ⟨j,hj⟩ := hwT.isClosedSubmanifold_N.2 x ((hev x hx).self_of_nhds.mp hx)
    exact ⟨j,CodimOneSupport.regularAtDim_of_eventually_mem_iff
      ((hev x hx).mono fun _ h=>h.symm) hj⟩
  refine ⟨hFT,?_,selected_strict_subset_cosupp L hw T hT hTR,?_,disjoint_strictAlong T hR.1 hF.1 hdis⟩
  · apply CodimOneAdmissibleAlong.isTransverse_of_forall_eventually
    intro x hx
    exact ⟨_,(hev x hx).self_of_nhds.mp hx,hev x hx,hwT.isTransverse⟩
  · rw [N_geoTransformAlong]
    exact (congrArg (strictAlong T) hpart).trans (strictAlong_union T _ _)

/-- The remainder phase and a real blowup of its genuine selected-zero strict
union internally construct a finite WHOLE resolution, without nonzero input. -/
theorem exists_resolution_of_positive_codimension_carrier
    (L : MarkedIdeal n X) (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (hd : 1≤L.d) (hE : L.E=[]) {k : ℕ}
    (hDim : ResolutionInvariantSpec.DimLE n L.N k) (hk : k<n) (hK : IsCompact L.cosupp) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),IsGeoResolution L T ∧ CentresIn L.N T := by
  have hw : L.IsWellFormed := by
    refine ⟨hN,hI,?_,?_⟩
    · rw [hE];exact isSNCDivisor_nil
    · rw [hE];exact isTransverse_nil_of_isClosedSubmanifold hN
  obtain ⟨Y,P,_hcan,_hres,hPL,hPR,hclear⟩ := exists_canonical_remainder_parent_phase L hN hI hd hE hK
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

/-- ORIGINAL coherent I/positive mark/compact cosupport and actual NC geometry
internally resolve the WHOLE coefficient stratum at SAME original marking. -/
theorem exists_original_nc_coefficient_stratum_resolution
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1≤d)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0<r)
    (hbound : ∀ x : X,branchMultiplicity hH x≤r) :
    let M : MarkedIdeal n X := ⟨univ,[],I,d⟩
    let Z := {x : X | r≤branchMultiplicity hH x}
    let L := withN (coeffMarked M) Z
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),IsGeoResolution L T ∧
      IsGeoTestTower M T ∧ CentresIn Z T ∧
      (geoTransformAlong M T).cosupp∩strictAlong T Z=∅ := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,[],I,d⟩
  let Z := {x : X | r≤branchMultiplicity hH x}
  let L := withN (coeffMarked M) Z
  have hZ := isClosedSubmanifold_highest_superlevel hH hbound
  have hL : L.ideal.IsCoherent := isCoherent_coeffMarked (𝔪:=M) rfl hI
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
      obtain ⟨Y,T,hT,_hCentres⟩ := exists_resolution_of_positive_codimension_carrier L hZ hL hLd rfl hDim (by omega) hKL
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
end TranscendentalNakamaye.Pending.HironakaNormalCrossingsCoefficientStratumResolution
