import Hironaka.Resolution.HironakaActualLocallyFiniteTransverseContinuation

/-! The actual all-prefix limit controlled ideal stays nonzero along the
actual whole limit carrier. Actual LF histories are given; an internally
fair resolving scheduler is not asserted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualLocallyFiniteNonzeroIdealContinuation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteHistoryFactors HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaActualLocallyFiniteCarrierTransverse HironakaActualLocallyFiniteControlledIdeal
  DivisorExponentAlong RelativePrincipalizationSpan InvertibleIdealQuotient
attribute [local instance] limitChartedSpace
variable {n : ℕ} {X : CMfd.{u} n}

theorem isNonzeroAlongAt_limitControlledIdeal
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hnz : ∀x∈M.N,IsNonzeroAlongAt M.N M.ideal x)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀j,IsGeoTestTower M (s.stage j).2) :
    ∀z∈limitStrictTransform s hLF M.N,
      IsNonzeroAlongAt (limitStrictTransform s hLF M.N) (limitControlledIdeal M s hLF) z := by
  let : IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF
  intro z hz
  obtain ⟨x,q,rfl⟩:=actualHistoryLocalInclusion_jointly_surjective s hLF z
  let N:=stableIndex s hLF x
  let A:=geoTransformAlong M (s.stage N).2
  have hq : q.val∈A.N:=
    (Set.ext_iff.mp (localInclusion_preimage_limitCarrier M hM s hLF x) q).mp hz
  have hA:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM (s.stage N).2 (hT N)
  obtain ⟨f,hf,hfreq⟩:=InvDomainTowerAlong.isNonzeroAlongAt_geoTransformAlong
    hM.isClosedSubmanifold_N hM.isCoherent hnz (s.stage N).2 (hT N) q.val hq
  have hfactor : stageFactor s hLF N (actualHistoryLocalInclusion s hLF x q)=q.val:=
    stableFactor_local s hLF x q
  have hf' : A.ideal.mem (stageFactor s hLF N (actualHistoryLocalInclusion s hLF x q)) f:=
    hfactor.symm ▸ hf
  let F:=f ∘ stageFactor s hLF N
  have hFhol : HolomorphicAt n F (actualHistoryLocalInclusion s hLF x q):=
    HadamardBridge.holomorphicAt_comp_map
      (Eventually.of_forall fun a=>(stageFactor_contMDiff s hLF N a).mdifferentiableAt (by simp))
      (GermIdeal.IsCoherent.holomorphicAt_mem hA.isCoherent hf')
  refine ⟨F,⟨N,?_⟩,?_⟩
  · exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨f,hf',rfl⟩ hFhol)
  · have hfreqQ : ∃ᶠp : localEndpoint s hLF x in 𝓝 q,p.val∈A.N ∧ f p.val≠0 := by
      rw [nhds_subtype_eq_comap,Filter.frequently_comap]
      exact (hfreq.and_eventually ((openPreimage (s.stage N).2 (stableWindow s hLF x)).isOpen.mem_nhds q.property)).mono
        fun y ⟨hy,hyU⟩=>⟨⟨y,hyU⟩,rfl,hy⟩
    have hcont : Tendsto (actualHistoryLocalInclusion s hLF x) (𝓝 q)
        (𝓝 (actualHistoryLocalInclusion s hLF x q)):=
      (actualHistoryLocalInclusion_openEmbedding s hLF x).continuous.continuousAt
    apply hcont.frequently
    refine hfreqQ.mono fun p hp=>⟨?_,?_⟩
    · exact (Set.ext_iff.mp (localInclusion_preimage_limitCarrier M hM s hLF x) p).mpr hp.1
    · change f (stageFactor s hLF N (actualHistoryLocalInclusion s hLF x p))≠0
      rw [stableFactor_local]
      exact hp.2

open GermIdealOrder

theorem interior_cosupport_eq_empty_of_nonzero {Y : CMfd.{u} n}
    (A : Set Y) (I : GermIdeal n Y) (hI : I.IsCoherent)
    (hnz : ∀x∈A,IsNonzeroAlongAt A I x) {d : ℕ} (hd : 1≤d) :
    interior (cosupport n A I d)=∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun y hy=>?_
  have hyA : y∈A := (interior_subset hy : y∈cosupport n A I d).1
  obtain ⟨g,hg,hfreq⟩:=hnz y hyA
  obtain ⟨U,hU,hyU,m,s,hs,hgen⟩:=hI y
  obtain ⟨_,m',s',a,hs',_,hgeq⟩:=(hgen y hyU g).mp hg
  have hvan : ∀z∈U,z∈interior (cosupport n A I d) → ∀j,s j z=0 := by
    intro z hzU hzi j
    have hzc : z∈cosupport n A I d:=interior_subset hzi
    have hhol : HolomorphicAt n (s j) z := by
      filter_upwards [hU.mem_nhds hzU] with w hw
      exact (hs j w hw).mdifferentiableAt (hU.mem_nhds hw)
    have hmem : I.mem z (s j):=(hgen z hzU (s j)).mpr (isInSpanAt_self ⟨j,rfl⟩ hhol)
    exact (vanishesToOrderOn_one_iff hzc.1 hhol).mp ((hzc.2 (s j) hmem).mono hd)
  have hev : ∀ᶠz in 𝓝 y,g z=0 := by
    filter_upwards [hgeq,hU.mem_nhds hyU,isOpen_interior.mem_nhds hy] with z hz hzU hzi
    rw [hz]
    refine Finset.sum_eq_zero fun i _=>?_
    obtain ⟨j,hj⟩:=hs' i
    rw [←hj,hvan z hzU hzi j,mul_zero]
  obtain ⟨z,⟨_,hgz⟩,hgz'⟩:=(hfreq.and_eventually hev).exists
  exact hgz hgz'

open HironakaActualLocallyFiniteBoundary HironakaActualLocallyFiniteBoundaryContinuation
  HironakaActualLocallyFiniteTransverseContinuation BlowupStrictSubmanifold
  NormalCrossings RestrictedIdealQuotient IdealWeightPowers ResolutionDriver

theorem exists_actual_limit_centre_blowup
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hnz : ∀x∈M.N,IsNonzeroAlongAt M.N M.ideal x) (hd : 1≤M.d)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀j,IsGeoTestTower M (s.stage j).2)
    (C : Set (limitManifold s hLF)) (hC : IsClosedSubmanifold n C)
    (hCos : C⊆cosupport n (limitStrictTransform s hLF M.N) (limitControlledIdeal M s hLF) M.d)
    (hNC : HasNormalCrossingsWithIndexedBoundary C (limitBoundaryMember M s hLF)) :
    ∃(Z : CMfd.{u} n)(π : Z → limitManifold s hLF)(_hπ : IsBlowupAlong n C π),
      IsProperMap (fun z=>gluedProjection s hLF (π z)) ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
        (fun z=>gluedProjection s hLF (π z)) ∧
      IsLocallyFiniteSNCDivisor n (continuedBoundary (limitBoundaryMember M s hLF) C π) ∧
      IsClosedSubmanifold n (geoStrictTransform π C (limitStrictTransform s hLF M.N)) ∧
      IsTransverseBoundaryFamily n (geoStrictTransform π C (limitStrictTransform s hLF M.N))
        (continuedBoundary (limitBoundaryMember M s hLF) C π) ∧
      (colonAlong n (geoStrictTransform π C (limitStrictTransform s hLF M.N))
        (GermIdeal.pullback (m:=n) π (limitControlledIdeal M s hLF))
        (idealPow (GermIdeal.pullback (m:=n) π (vanishingIdeal (n:=n) C)) M.d)).IsCoherent := by
  let : IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF
  have hI:=isCoherent_limitControlledIdeal M
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hM.isClosedSubmanifold_N)
    hM.isCoherent s hLF
  have hThin:=interior_cosupport_eq_empty_of_nonzero (limitStrictTransform s hLF M.N)
    (limitControlledIdeal M s hLF) hI (isNonzeroAlongAt_limitControlledIdeal M hM hnz s hLF hT) hd
  have hInt : interior C=∅:=eq_empty_of_subset_empty ((interior_mono hCos).trans hThin.subset)
  obtain ⟨Z,π,hπ⟩:=exists_blowup C hC hInt
  have hCN : C⊆limitStrictTransform s hLF M.N:=fun _ hx=>(hCos hx).1
  obtain ⟨hp,hh,hB,hN,hTrans⟩:=actual_limit_carrier_continuation M hM s hLF hT hπ hCN hNC
  exact ⟨Z,π,hπ,hp,hh,hB,hN,hTrans,actual_limit_controlled_ideal_continuation M hM s hLF hT hπ hCN⟩

end
end Hironaka.HironakaActualLocallyFiniteNonzeroIdealContinuation
