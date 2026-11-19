import Hironaka.Resolution.HironakaActualProtectedOtherRowLocalStep
import Hironaka.Analytic.MonomialCaseLocal
import Hironaka.Invariant.CodimOneAdmissibleAlong

/-! Same entire actual native maximum on the fixed prepared ambient window.
Source-first full mathematics: hironaka-actual-protected-gamma-maximum-window.tex.
No finite history, full lower driver, gluing or global K1 closure is claimed. -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualProtectedGammaMaximumWindow
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms NormalCrossings NormalCrossingsComparison
  NormalCrossingsInvariance SimultaneousNormalCrossings BlowupStrictSubmanifold
  BlowupSNCTransform MemberInterAlong BoundaryCount BlowupFlatCoordinates
  HironakaActualProtectedOtherRowLocalStep HironakaG4PreparedCentreCoordinates
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalProductTraceOrder
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualTraceIncidence HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4ResidualInductionInputs HironakaG4ActiveMonomialSharpBad
  RelativePrincipalizationSpan RestrictedIdealExtension GermIdealOrder MonomialPartAlong
  MonomialCaseAlong MonomialCase MonomialInvariant MonomialStepAlong
  DivisorExponentAlong MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionDriver
  HomogenizedGlueingTower IdealWeightPowers

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Reused private source-coordinate argument; zero separate achievement credit. -/
private theorem transverse_stratum_omitted (hn : 0 < n) {N H : Set X}
    {F : List (Set X)} (hE : IsSNCDivisor n (H :: F))
    (hTr : IsTransverse n N (H :: F)) (S : Finset (Fin F.length)) :
    IsTransverse n (N ∩ memberInter F S) [H] := by
  intro x hx
  obtain ⟨_kC,kN,Φ,s,_hsrc,hs,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn (Subset.refl N) hE hTr hTr.hasNormalCrossings hx.1
  let z : Fin (H :: F).length := ⟨0,by simp⟩
  let c : Fin F.length → Fin (H :: F).length := fun a =>
    ⟨a.val+1,by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using a.isLt⟩
  have hz : (H :: F).get z=H := rfl
  have hc (a : Fin F.length) : (H :: F).get (c a)=F.get a := by
    simp [c,List.get_eq_getElem]
  let QN : Finset (Fin n) := Finset.univ.filter fun t => kN ≤ t.val
  let QF : Finset (Fin n) := S.biUnion fun a => {s (c a)}
  refine ⟨QN ∪ QF,fun _ => {s z},?_,?_⟩
  · apply coordinateFamilyAt_of_flattening Φ ?_
      (mem_complexChartAt_source x) Φ.center_mem_source (fun _ hi => hi)
    rintro (_ | a) hxa y hy hyΦ
    · change y ∈ N ∩ memberInter F S ↔
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (QN ∪ QF)
      rw [ExceptionalPushforwardAlong.coordSubspace_union]
      change (y ∈ N ∧ ∀ b ∈ S,y ∈ F.get b) ↔
        (Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace QN ∧
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace QF)
      refine and_congr ?_ ?_
      · rw [show coordSubspace QN=complexCoordinatePlane n kN by
          simp only [QN,coordSubspace_eq_complexCoordinatePlane]]
        simpa only [complexChartAt] using (hflat hy hyΦ).2.1
      · rw [show coordSubspace QF=coordSubspace (S.biUnion fun b => {s (c b)}) by rfl,
          BoundaryCount.mem_coordSubspace_biUnion]
        apply forall₂_congr
        intro b hb
        rw [BlowupSNCTransform.mem_coordSubspace_singleton]
        have hxb : x ∈ (H :: F).get (c b) := by rw [hc];exact hx.2 b hb
        simpa only [hc,complexChartAt] using (hflat hy hyΦ).2.2 (c b) hxb
    · have ha : [H].get a=H := by fin_cases a;rfl
      change x ∈ [H].get a at hxa
      change (y ∈ [H].get a ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace {s z})
      rw [ha] at hxa ⊢
      rw [BlowupSNCTransform.mem_coordSubspace_singleton]
      have hxh : x ∈ (H :: F).get z := by rw [hz];exact hxa
      simpa only [hz,complexChartAt] using (hflat hy hyΦ).2.2 z hxh
  · intro a hxa
    have ha : [H].get a=H := by fin_cases a;rfl
    rw [ha] at hxa
    have hxh : x ∈ (H :: F).get z := by rw [hz];exact hxa
    refine ⟨by simp,Finset.disjoint_singleton_left.mpr ?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with hQN | hQF
    · have hge := (Finset.mem_filter.mp hQN).2
      exact Nat.not_lt_of_ge hge (hs z hxh)
    · obtain ⟨b,hb,he⟩ := Finset.mem_biUnion.mp hQF
      have hxb : x ∈ (H :: F).get (c b) := by rw [hc];exact hx.2 b hb
      have hidx := hinj hxh hxb (Finset.mem_singleton.mp he)
      have hv := congrArg Fin.val hidx
      dsimp [z,c] at hv
      omega

private theorem embedded_memberInter {E F : List (Set X)}
    (e : Fin E.length ↪ Fin F.length) (hGet : ∀ i,F.get (e i)=E.get i)
    (S : Finset (Fin E.length)) : memberInter F (S.map e)=memberInter E S := by
  ext y
  constructor
  · intro hy i hi
    rw [←hGet i]
    exact hy (e i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
  · intro hy i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    rw [hGet]
    exact hy j hj

private theorem union_memberInter (F : List (Set X)) (Q S : Finset (Fin F.length)) :
    memberInter F (Q ∪ S)=memberInter F Q ∩ memberInter F S := by
  ext y
  constructor
  · intro hy
    exact ⟨fun i hi => hy i (Finset.mem_union_left S hi),
      fun i hi => hy i (Finset.mem_union_right Q hi)⟩
  · rintro ⟨hyQ,hyS⟩ i hi
    exact (Finset.mem_union.mp hi).elim (hyQ i) (hyS i)

private theorem stratum_nc_auxiliary {N H : Set X} {F : List (Set X)}
    (hTr : IsTransverse n N (H :: F)) (Q : Finset (Fin F.length)) :
    HasNormalCrossings n (N ∩ memberInter F Q) (H :: F) := by
  let e : Fin F.length ↪ Fin (H :: F).length :=
    ⟨Fin.succ,fun a b he => Fin.ext (Nat.succ.inj (congrArg Fin.val he))⟩
  have hGet (i : Fin F.length) : (H :: F).get (e i)=F.get i := rfl
  have hNC := hasNormalCrossings_inter_memberInter hTr (Q.map e)
  rw [embedded_memberInter e hGet Q] at hNC
  exact hNC

/-- Actual native maximum geometry, globally on the SAME ambient window.
The omitted auxiliary coordinate is derived from genuine local top-index
germs, with no caller centre-transversality/protection certificate. -/
theorem native_gamma_maximum_omits_auxiliary_coordinate (hn : 0<n)
    {N H : Set X} {F : List (Set X)}
    (hAux : IsSNCDivisor n (H :: F)) (hAuxTr : IsTransverse n N (H :: F))
    (P : MarkedIdeal n X) (hP : P.IsWellFormed)
    (hNZ : ∀ x ∈ P.N,IsNonzeroAlongAt P.N P.ideal x)
    (hMono : IsMonomialAlong n P.N P.ideal P.E)
    (Q₀ : Finset (Fin F.length)) (hCarrier : P.N=N ∩ memberInter F Q₀)
    (e : Fin P.E.length ↪ Fin F.length) (hGet : ∀ i,F.get (e i)=P.E.get i) :
    IsTransverse n (maxLocusA P) [H] ∧
      HasNormalCrossings n (maxLocusA P) (H :: F) := by
  have hLocal : ∀ x ∈ maxLocusA P,∃ Q : Finset (Fin F.length),
      x ∈ N ∩ memberInter F Q ∧
      ∀ᶠ y in 𝓝 x,y ∈ maxLocusA P ↔ y ∈ N ∩ memberInter F Q := by
    intro x hx
    have hNotBot : gammaAlong n P.N P.ideal P.E P.d x ≠ ⊥ := by
      intro he
      exact ((gammaAlong_eq_bot_iff_of_isMonomialAlong hn hP.isClosedSubmanifold_N
        hP.isSNCDivisor hP.isTransverse hP.isCoherent hNZ hMono P.d
        (P.cosupp_subset_N hx.1)).mp he) hx.1
    obtain ⟨v,hv⟩ : ∃ v : Val,gammaAlong n P.N P.ideal P.E P.d x=(v : WithBot Val) := by
      cases he : gammaAlong n P.N P.ideal P.E P.d x with
      | bot => exact False.elim (hNotBot he)
      | coe v => exact ⟨v,rfl⟩
    let S := topIdx P.E v
    let Q := Q₀ ∪ S.map e
    have hW : P.N ∩ memberInter P.E S=N ∩ memberInter F Q := by
      rw [hCarrier,inter_assoc,←embedded_memberInter e hGet S,←union_memberInter]
    have hNear := eventually_mem_maxLocusA_iff hn hP hNZ hMono hx hv
    have hNear' : ∀ᶠ y in 𝓝 x,y ∈ maxLocusA P ↔ y ∈ N ∩ memberInter F Q := by
      filter_upwards [hNear] with y hy
      change (y ∈ maxLocusA P ↔ y ∈ P.N ∩ memberInter P.E S) at hy
      rwa [hW] at hy
    exact ⟨Q,hNear'.self_of_nhds.mp hx,hNear'⟩
  constructor
  · apply CodimOneAdmissibleAlong.isTransverse_of_forall_eventually
    intro x hx
    obtain ⟨Q,hxQ,hNear⟩ := hLocal x hx
    exact ⟨N ∩ memberInter F Q,hxQ,hNear,transverse_stratum_omitted hn hAux hAuxTr Q⟩
  · apply CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually
    intro x hx
    obtain ⟨Q,hxQ,hNear⟩ := hLocal x hx
    exact ⟨N ∩ memberInter F Q,hxQ,hNear,stratum_nc_auxiliary hAuxTr Q⟩

private theorem full_boundary_nc_of_lower {C : Set X} {old born : List (Set X)}
    (hE : IsSNCDivisor n (old ++ born)) (j : Fin old.length)
    (hOwn : C ⊆ old.get j)
    (hSmall : HasNormalCrossings n C (old.eraseIdx j.val ++ born)) :
    HasNormalCrossings n C (old ++ born) := by
  apply hasNormalCrossings_of_forall_notMem hE hSmall
  intro H hH hNot
  rcases List.mem_append.mp hH with hOld | hBorn
  · obtain ⟨a,ha⟩ := List.mem_iff_get.mp hOld
    have haj : a.val=j.val := by
      by_contra hne
      exact hNot (List.mem_append_left born
        (List.mem_eraseIdx_iff_getElem.mpr ⟨a.val,a.isLt,hne,ha⟩))
    have he : a=j := Fin.ext haj
    rw [he] at ha
    rw [←ha]
    exact hOwn
  · exact False.elim (hNot (List.mem_append_right _ hBorn))

private theorem canonical_monomial_proper_bad (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born))
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length) :
    {x | x ∈ N ∧ ¬(oldMonomialPart N old born i).mem x 1} ⊆
      originalSharpBadLocus (n := n) N (old ++ born) := by
  intro x hx
  refine ⟨hx.1,fun hNC => hx.2 ?_⟩
  apply (one_mem_monomialPartAlong_iff (oldTraceIdeal N old i) born hx.1).mpr
  intro b hxb
  let aF : Fin (old ++ born).length := ⟨i.val,by simp only [List.length_append];omega⟩
  let bF : Fin (old ++ born).length := ⟨old.length+b.val,by simp only [List.length_append];omega⟩
  have hA : (old ++ born).get aF=old.get i := by
    simp only [List.get_eq_getElem,aF,List.getElem_append_left i.isLt]
  have hB : (old ++ born).get bF=born.get b := by
    simp only [List.get_eq_getElem,bF,List.getElem_append_right (by omega :
      old.length ≤ old.length+b.val),Nat.add_sub_cancel_left]
  have hne : aF ≠ bF := by
    intro he
    have hv := congrArg (fun a : Fin (old ++ born).length => a.val) he
    change i.val=old.length+b.val at hv
    omega
  have hb : x ∈ (old ++ born).get bF := by rw [hB];exact hxb
  simpa only [hA,hB,oldTraceIdeal] using
    divExpAlong_restricted_member_eq_zero_at_normalCrossings hn hN hE hdense hx.1 hNC aF bF hne hb

private theorem canonical_monomial_proper_subset_member (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length) :
    {x | x ∈ N ∧ ¬(oldMonomialPart N old born i).mem x 1} ⊆ old.get i := by
  intro x hx
  obtain ⟨hcI,_hnzI,_hcJ,_hnzJ,hcD,_hnzD,_hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  have hOld : IsSNCDivisor n old := isSNCDivisor_of_sublist hE (List.sublist_append_left old born)
  have hBorn : IsSNCDivisor n born := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hH := MonomialPart.isClosedSubmanifold_get hn hOld i
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hH
  have hxD : x ∈ (oldMonomialPart N old born i).zeroLocus := by
    intro g hg
    by_contra hne
    exact hx.2 (CompanionReduction.one_mem_of_apply_ne_zero hcD hg hne)
  have hLe : (oldTraceIdeal N old i).Le (oldMonomialPart N old born i) :=
    le_monomialPartAlong hn hBorn hTr hcI
  have hxI : x ∈ (oldTraceIdeal N old i).zeroLocus := fun g hg => hxD g (hLe x g hg)
  have hxH := (zeroLocus_restrictOn_iff hcH hx.1).mp hxI
  rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hH.1] at hxH


/-- Whole protected-row geometry on ANY GIVEN blowup of the SAME entire
native Gamma maximum, on the SAME prepared source window. Native phase,
upper tests/sharp footprints and literal strict auxiliary/lower traces
are derived internally; no future protection premise is supplied. -/
theorem actual_current_given_gamma_maximum_protects_other_row (hn : 0<n)
    {N H L : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ K ∈ old ++ born,K))
    (i j : Fin old.length) (hne : j ≠ i)
    (hAux : IsSNCDivisor n (H :: (old.eraseIdx i.val ++ born)))
    (hAuxTr : IsTransverse n N (H :: (old.eraseIdx i.val ++ born)))
    (hL : IsClosedSubmanifold n L) (hLTrace : L=N ∩ old.get j)
    (hLSupport : L=N ∩ (oldResidualPart N old born j).zeroLocus)
    (hLTr : IsTransverse n L born)
    (hLDense : L ⊆ closure (L \ ⋃ K ∈ old.eraseIdx j.val ++ born,K))
    (a : Fin (old.eraseIdx j.val).length) (ha : (old.eraseIdx j.val).get a=old.get i)
    (π : Y → X)
    (hπ : IsBlowupAlong n (maxLocusA
      (⟨L,born,oldMonomialPart L (old.eraseIdx j.val) born a,1⟩ : MarkedIdeal n X)) π) :
    let Phase : MarkedIdeal n X := ⟨L,born,oldMonomialPart L (old.eraseIdx j.val) born a,1⟩
    let C := maxLocusA Phase
    let F := old.eraseIdx i.val ++ born
    let R : BlowupTower X Y := .step .refl C π hπ
    let N' := geoStrictTransform π C N
    let H' := geoStrictTransform π C H
    let F' := F.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    Phase.IsWellFormed ∧ IsGeoTestTower Phase R ∧
      (C.Nonempty → IsCanonicalSegment Phase (fun {Q} R => towerInvAlong Phase (Y := Q) R) R) ∧
      (geoTransformAlong Phase R).IsWellFormed ∧
      (∀ y ∈ (geoTransformAlong Phase R).N,
        IsNonzeroAlongAt (geoTransformAlong Phase R).N (geoTransformAlong Phase R).ideal y) ∧
      IsMonomialAlong n (geoTransformAlong Phase R).N (geoTransformAlong Phase R).ideal
        (geoTransformAlong Phase R).E ∧
      (∀ x ∈ C,∀ y ∈ (geoTransformAlong Phase R).cosupp,
        towerInvAlong Phase R y < towerInvAlong Phase (BlowupTower.refl (X := X)) x) ∧
      HasNormalCrossings n C (old ++ born) ∧
      C ⊆ originalSharpBadLocus (n := n) L (old.eraseIdx j.val ++ born) ∧
      C ⊆ originalSharpBadLocus (n := n) N (old ++ born) ∧
      IsGeoTestTower (geometricTemplate N born) R ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) R ∧
      IsClosedSubmanifold n (geoStrictTransform π C (N ∩ H)) ∧
      nextRelativeStrict N (vanishingIdeal (n := n) (N ∩ H)) C π=
        vanishingIdeal (n := n) (geoStrictTransform π C (N ∩ H)) ∧
      HasNormalCrossings n (geoStrictTransform π C (N ∩ H)) F' ∧
      geoStrictTransform π C (N ∩ H) ⊆ closure (geoStrictTransform π C (N ∩ H) \ ⋃ K ∈ F',K) ∧
      IsSNCDivisor n (H' :: F') ∧ IsTransverse n N' (H' :: F') ∧
      geoStrictTransform π C (N ∩ H)=N' ∩ H' ∧
      geoStrictTransform π C L=N' ∩ geoStrictTransform π C (old.get j) := by
  let lo := old.eraseIdx j.val
  let D := oldMonomialPart L lo born a
  let Phase : MarkedIdeal n X := ⟨L,born,D,1⟩
  let C := maxLocusA Phase
  let F := old.eraseIdx i.val ++ born
  have hLowerFull : IsSNCDivisor n (lo ++ born) := isSNCDivisor_of_sublist hFull
    ((List.eraseIdx_sublist old j.val).append (List.Sublist.refl born))
  obtain ⟨_hcI,_hnzI,_hcJ,_hnzJ,hcD,hnzD,hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hL hLowerFull hLTr hLDense a
  have hBorn : IsSNCDivisor n born := isSNCDivisor_of_sublist hFull (List.sublist_append_right old born)
  have hPhase : Phase.IsWellFormed := ⟨hL,hcD,hBorn,hLTr⟩
  have hAdm : Phase.IsAdmissibleCentre C := isAdmissibleCentre_maxLocusA hn hPhase hnzD hmD
  have hCN : C ⊆ N := by
    intro x hx
    have hh : x ∈ L := (Phase.cosupp_subset_N hx.1)
    rw [hLTrace] at hh
    exact hh.1
  have hProper : C ⊆ {x | x ∈ L ∧ ¬D.mem x 1} := by
    intro x hx
    have hCos : x ∈ cosupport n L D 1 := hx.1
    refine ⟨hCos.1,?_⟩
    intro hUnit
    exact one_ne_zero ((vanishesToOrderOn_one_iff hCos.1 (holomorphicAt_const 1)).mp (hCos.2 1 hUnit))
  have hLowerBad : C ⊆ originalSharpBadLocus (n := n) L (lo ++ born) :=
    hProper.trans (canonical_monomial_proper_bad hn hL hLowerFull hLDense a)
  have hOwn : C ⊆ old.get i := by
    rw [←ha]
    exact hProper.trans (canonical_monomial_proper_subset_member hn hL hLowerFull hLTr hLDense a)
  have hUpperBad : C ⊆ originalSharpBadLocus (n := n) N (old ++ born) := by
    have hb := originalSharpBadLocus_residual_subset hn hN hFull hTr hdense j
    rw [←hLSupport] at hb
    exact hLowerBad.trans hb
  have hMemj : old.get j ∈ F := by
    apply List.mem_append_left
    exact List.mem_eraseIdx_iff_getElem.mpr
      ⟨j.val,j.isLt,(fun he => hne (Fin.ext he)),rfl⟩
  obtain ⟨b,hb⟩ := List.mem_iff_get.mp hMemj
  let e : Fin born.length ↪ Fin F.length :=
    ⟨fun b => ⟨(old.eraseIdx i.val).length+b.val,by simp only [F,List.length_append];omega⟩,
      fun a b he => Fin.ext (Nat.add_left_cancel (congrArg Fin.val he))⟩
  have hGet (b : Fin born.length) : F.get (e b)=born.get b := by
    change (old.eraseIdx i.val ++ born).get
      ⟨(old.eraseIdx i.val).length+b.val,by
        simpa only [List.length_append,Nat.add_lt_add_iff_left] using b.isLt⟩=born.get b
    simp only [List.get_eq_getElem,List.getElem_append_right (by omega :
      (old.eraseIdx i.val).length ≤ (old.eraseIdx i.val).length+b.val),Nat.add_sub_cancel_left]
  have hSingleton : memberInter F {b}=old.get j := by
    ext x
    constructor
    · intro hx
      rw [←hb]
      exact hx b (Finset.mem_singleton_self _)
    · intro hx c hc
      rw [Finset.mem_singleton.mp hc,hb]
      exact hx
  have hCarrier : Phase.N=N ∩ memberInter F {b} := by
    change L=N ∩ memberInter F {b}
    rw [hSingleton,hLTrace]
  obtain ⟨hCH,hCNCaux⟩ := native_gamma_maximum_omits_auxiliary_coordinate hn hAux hAuxTr
    Phase hPhase hnzD hmD {b} hCarrier e hGet
  have hCNCF : HasNormalCrossings n C F := hasNormalCrossings_of_forall_mem hCNCaux
    (fun K hK => List.mem_cons_of_mem H hK)
  have hCNC : HasNormalCrossings n C (old ++ born) := full_boundary_nc_of_lower hFull i hOwn hCNCF
  have hProtect := transverse_slice_step hn hN hAux hAuxTr hCN hCNCaux hCH hπ
  have hCborn : HasNormalCrossings n C born := hasNormalCrossings_of_forall_mem hCNC
    (fun K hK => List.mem_append_right old hK)
  have hCarrierTest : IsGeoTestTower (geometricTemplate N born) (.step (.refl (X := X)) C π hπ) := by
    refine ⟨trivial,hπ.1,?_,hCborn⟩
    change C ⊆ cosupport n N (unitIdeal n X) 0
    rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem isCoherent_unitIdeal hg)]
    exact hCN
  have hAmbientTest : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born))
      (.step (.refl (X := X)) C π hπ) := by
    refine ⟨trivial,hπ.1,?_,hCNC⟩
    change C ⊆ cosupport n univ (unitIdeal n X) 0
    rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem isCoherent_unitIdeal hg)]
    exact subset_univ C
  have hAux' : IsSNCDivisor n (geoStrictTransform π C H ::
      (F.map (geoStrictTransform π C) ++ [π ⁻¹' C])) := by
    simpa only [List.map_cons,List.cons_append] using
      isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hAux hCNCaux
  have hAuxTr' : IsTransverse n (geoStrictTransform π C N) (geoStrictTransform π C H ::
      (F.map (geoStrictTransform π C) ++ [π ⁻¹' C])) := by
    simpa only [List.map_cons,List.cons_append] using
      isTransverse_geoTransformE_of_hasNormalCrossings hπ hN.1 hCN hAux hAuxTr hCNCaux
  have hSi' : geoStrictTransform π C (N ∩ H)=geoStrictTransform π C N ∩ geoStrictTransform π C H := by
    calc
      _ = geoStrictTransform π C (H ∩ N) := congrArg _ (inter_comm N H)
      _ = geoStrictTransform π C H ∩ geoStrictTransform π C N :=
        ExceptionalPushforwardAlong.geoStrictTransform_inter_eq hπ hN.1 hCN hAux hAuxTr hCNCaux
          (0 : Fin (H :: F).length)
      _ = _ := inter_comm _ _
  have hL' : geoStrictTransform π C L=geoStrictTransform π C N ∩ geoStrictTransform π C (old.get j) := by
    rw [hLTrace]
    let bAux : Fin (H :: F).length := b.succ
    have hGetb : (H :: F).get bAux=old.get j := by
      change F.get b=old.get j
      exact hb
    calc
      _ = geoStrictTransform π C (old.get j ∩ N) := congrArg _ (inter_comm N (old.get j))
      _ = geoStrictTransform π C (old.get j) ∩ geoStrictTransform π C N := by
        have hStrict := ExceptionalPushforwardAlong.geoStrictTransform_inter_eq
          hπ hN.1 hCN hAux hAuxTr hCNCaux bAux
        change geoStrictTransform π C ((H :: F).get bAux ∩ N)=
          geoStrictTransform π C ((H :: F).get bAux) ∩ geoStrictTransform π C N at hStrict
        rwa [hGetb] at hStrict
      _ = _ := inter_comm _ _
  obtain ⟨hNew,hNewNZ,hNewMono,_hOver,_hOff,hDrop⟩ := monomial_step_along hn hPhase hnzD hmD hπ
  exact ⟨hPhase,⟨trivial,hAdm⟩,(fun hC => ⟨trivial,hC,rfl⟩),hNew,hNewNZ,hNewMono,hDrop,
    hCNC,hLowerBad,hUpperBad,hCarrierTest,hAmbientTest,hProtect.1,hProtect.2.1,hProtect.2.2.1,
    hProtect.2.2.2,hAux',hAuxTr',hSi',hL'⟩

end
end Hironaka.HironakaActualProtectedGammaMaximumWindow
