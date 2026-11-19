import Hironaka.Resolution.HironakaNormalCrossingsPrescribedLabelledHistory
import Hironaka.Resolution.HironakaNormalCrossingsLabelledBoundaryRegrouping

/-!
# Whole original labelled NC throughout a genuine highest phase

Actual prescribed joint test histories and literal original groups prove
the whole labelled geometry at every actual head, including empty slots.
Original ideal data internally construct that SAME genuine count-drop phase.
Blueprint: `hironaka-normal-crossings-labelled-phase-preservation-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsLabelledPhasePreservation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit HomogenizedGlueingTower
  MemberInterTowerAlong MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen NormalCrossings NormalCrossingsInvariance GermIdealOrder CoefficientIdealRestriction
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsLabelledBoundary
  HironakaNormalCrossingsLabelledBoundaryTransport HironakaNormalCrossingsLabelledJointBranches
  HironakaNormalCrossingsPrescribedLabelledHistory HironakaNormalCrossingsHighestSubcentreAdmissibility
  HironakaBoundaryCoefficientBranchHistories HironakaNormalCrossingsLabelledBoundaryRegrouping
  BlowupFlatCoordinates HironakaNormalCrossingsGlobalPhaseCarrier RestrictEmptyTower AnalyticSubsetOpens
  HironakaNormalCrossingsOpenRestrictionSeparation
open ResolutionInvariantExt (IsEmptyTower)
variable {n : ℕ}

theorem isNormalCrossingsBoundary_grouped_append
    {A : Type u} [TopologicalSpace A] [ChartedSpace (ComplexModel n) A]
    {b q : ℕ} (C : Fin b→Set A) (E : List (Set A))
    (hF : IsSNCDivisor n (List.ofFn C++E))
    (G : Fin q→Finset (Fin b)) (hG : ∀ i j,i≠j → Disjoint (G i) (G j)) :
    IsNormalCrossingsBoundary (n:=n) ((List.ofFn fun i=>⋃ j∈G i,C j)++E) := by
  let F:=List.ofFn C++E
  let left (i : Fin b) : Fin F.length:=⟨i.val,by simp only [F,List.length_append,List.length_ofFn];omega⟩
  let right (i : Fin E.length) : Fin F.length:=
    ⟨b+i.val,by simp only [F,List.length_append,List.length_ofFn];omega⟩
  have hleft (i : Fin b) : F.get (left i)=C i := by simp [F,left,List.get_eq_getElem]
  have hright (i : Fin E.length) : F.get (right i)=E.get i := by
    change (List.ofFn C++E)[b+i.val]=E[i.val]
    rw [List.getElem_append_right (by simp)]
    simp
  have hinjl : Function.Injective left := by
    intro i j h
    exact Fin.ext (congrArg (fun a : Fin F.length=>a.val) h)
  let GG : Fin (q+E.length)→Finset (Fin F.length):=
    Fin.append (fun i=>(G i).image left) (fun i=>{right i})
  have hGG : ∀ i j,i≠j → Disjoint (GG i) (GG j) := by
    intro i j hij
    revert j hij
    refine Fin.addCases ?_ ?_ i
    · intro i j hij
      revert hij
      refine Fin.addCases ?_ ?_ j
      · intro j hij
        have hne : i≠j:=fun he=>hij (congrArg (Fin.castAdd E.length) he)
        simp only [GG,Fin.append_left]
        apply Finset.disjoint_left.mpr
        intro k hki hkj
        obtain ⟨a,ha,hak⟩:=Finset.mem_image.mp hki
        obtain ⟨b,hb,hbk⟩:=Finset.mem_image.mp hkj
        have he:=hinjl (hak.trans hbk.symm)
        exact Finset.disjoint_left.mp (hG i j hne) ha (he ▸ hb)
      · intro j _hij
        simp only [GG,Fin.append_left,Fin.append_right]
        apply Finset.disjoint_left.mpr
        intro k hk hkj
        obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hk
        have he:=congrArg Fin.val (Finset.mem_singleton.mp hkj)
        change a.val=b+j.val at he
        have ha':=a.isLt
        omega
    · intro i j hij
      revert hij
      refine Fin.addCases ?_ ?_ j
      · intro j _hij
        simp only [GG,Fin.append_left,Fin.append_right]
        apply Finset.disjoint_left.mpr
        intro k hki hk
        obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hk
        have he:=congrArg Fin.val (Finset.mem_singleton.mp hki)
        change a.val=b+i.val at he
        have ha':=a.isLt
        omega
      · intro j hij
        have hne : i≠j:=fun he=>hij (congrArg (Fin.natAdd q) he)
        simp only [GG,Fin.append_right]
        apply Finset.disjoint_singleton.mpr
        intro he
        apply hne
        apply Fin.ext
        have hv:=congrArg Fin.val he
        change b+i.val=b+j.val at hv
        omega
  have h:=isNormalCrossingsBoundary_grouped_of_snc hF GG hGG
  have he : (List.ofFn fun i=>⋃ j∈GG i,F.get j)=
      (List.ofFn fun i=>⋃ j∈G i,C j)++E := by
    conv_rhs => rw [←List.ofFn_get E]
    rw [←List.ofFn_fin_append]
    apply congrArg List.ofFn
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simp only [GG,Fin.append_left]
      ext p
      simp only [mem_iUnion,Finset.mem_image]
      constructor
      · rintro ⟨j,⟨k,hk,rfl⟩,hp⟩
        exact ⟨k,hk,by rwa [hleft] at hp⟩
      · rintro ⟨k,hk,hp⟩
        exact ⟨left k,⟨k,hk,rfl⟩,by rwa [hleft]⟩
    · intro i
      simp only [GG,Fin.append_right,Finset.mem_singleton,iUnion_iUnion_eq_left,hright]
  exact he ▸ h

theorem isNormalCrossingsBoundary_of_open_traces
    {A : Type u} [TopologicalSpace A] [ChartedSpace (ComplexModel n) A] [IsComplexManifold n A]
    {F : List (Set A)} (hClosed : ∀ H∈F,IsClosed H)
    (hloc : ∀ x : A,∃ U : Opens A,x∈U ∧
      IsNormalCrossingsBoundary (n:=n) (F.map ((Subtype.val : U→A) ⁻¹' ·))) :
    IsNormalCrossingsBoundary (n:=n) F := by
  refine ⟨hClosed,fun x=>?_⟩
  obtain ⟨U,hxU,hU⟩:=hloc x
  let p : U:=⟨x,hxU⟩
  obtain ⟨Φ,S,hsrc,h0,hdis,hEq⟩:=hU.2 p
  let c : Fin F.length→Fin (F.map ((Subtype.val : U→A) ⁻¹' ·)).length:=
    Fin.cast (List.length_map _).symm
  have hget (i : Fin F.length) :
      (F.map ((Subtype.val : U→A) ⁻¹' ·)).get (c i)=(Subtype.val : U→A) ⁻¹' F.get i := by
    simp [c,List.get_eq_getElem]
  have hInside {y : A} (hy : y∈flatDomain (M:=A) (y₀:=x) Φ) : y∈U:=
    mem_opens_of_chart_mem_target hy.1 (hsrc hy.2)
  refine ⟨Φ,(fun i=>S (c i)),hsrc.trans (chartAt_opens_target_subset p),h0,?_,?_⟩
  · intro i j hij
    exact hdis (c i) (c j) (fun he=>hij (Fin.cast_injective _ he))
  · intro i y hy
    have he:=hEq (c i) ⟨y,hInside hy⟩ ⟨mem_chartAt_opens_source.mpr hy.1,hy.2⟩
    rw [hget] at he
    exact he

variable {X Y : CMfd.{u} n}

private theorem local_labelled_of_groups
    (L : List (Set X)) (T : BlowupTower X Y) (U : Opens X)
    (B : List (Set U)) (G : Fin L.length→Finset (Fin B.length))
    (hG : ∀ i j,i≠j → Disjoint (G i) (G j)) (E : List (Set Y))
    (hSNC : IsSNCDivisor n (B.map (strictAlong (restrict U T))++
      E.map ((Subtype.val : openPreimage T U→Y) ⁻¹' ·)))
    (hLabels : ∀ i,(Subtype.val : openPreimage T U→Y) ⁻¹' strictAlong T (L.get i)=
      ⋃ k∈G i,strictAlong (restrict U T) (B.get k)) :
    IsNormalCrossingsBoundary (n:=n)
      ((L.map (strictAlong T)++E).map ((Subtype.val : openPreimage T U→Y) ⁻¹' ·)) := by
  have he:=List.ofFn_comp' B.get (strictAlong (restrict U T))
  rw [List.ofFn_get] at he
  rw [←he] at hSNC
  have hGrouped:=isNormalCrossingsBoundary_grouped_append
    (fun k=>strictAlong (restrict U T) (B.get k))
    (E.map ((Subtype.val : openPreimage T U→Y) ⁻¹' ·)) hSNC G hG
  have hList : (L.map (strictAlong T)).map ((Subtype.val : openPreimage T U→Y) ⁻¹' ·)=
      List.ofFn (fun i : Fin L.length=>⋃ k∈G i,strictAlong (restrict U T) (B.get k)) := by
    rw [List.map_map]
    change List.map (fun A=>(Subtype.val : openPreimage T U→Y) ⁻¹' strictAlong T A) L=_
    have hf:=List.ofFn_comp' L.get
      (fun A=>(Subtype.val : openPreimage T U→Y) ⁻¹' strictAlong T A)
    rw [List.ofFn_get] at hf
    rw [←hf]
    apply congrArg List.ofFn
    funext i
    exact hLabels i
  simpa only [List.map_append,hList] using hGrouped

private theorem current_labelled_closed
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) {L E : List (Set X)}
    (h : IsNormalCrossingsBoundary (n:=n) (L++E)) (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (⟨univ,E,I,d⟩ : MarkedIdeal n X) T) :
    ∀ A∈L.map (strictAlong T)++(geoTransformAlong (⟨univ,E,I,d⟩ : MarkedIdeal n X) T).E,IsClosed A := by
  have hM : (⟨univ,E,I,d⟩ : MarkedIdeal n X).IsWellFormed:=
    ⟨isClosedSubmanifold_univ,hI,hE,SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hWF:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT
  intro A hA
  rcases List.mem_append.mp hA with hOld|hBorn
  · obtain ⟨D,hD,rfl⟩:=List.mem_map.mp hOld
    exact isClosed_strictAlong T (h.1 D (List.mem_append_left _ hD))
  · exact hWF.isSNCDivisor.1 A hBorn

private theorem centresIn_of_empty :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsEmptyTower T→CentresIn (∅ : Set X) T
  | _,.refl,_ => trivial
  | _,.step T C _ _,h => ⟨centresIn_of_empty T h.1,by rw [h.2];exact empty_subset _⟩

theorem labelledNC_empty_test_history
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) {L E : List (Set X)}
    (h : IsNormalCrossingsBoundary (n:=n) (L++E)) (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (⟨univ,E,I,d⟩ : MarkedIdeal n X) T)
    (he : IsEmptyTower T) :
    IsNormalCrossingsBoundary (n:=n)
      (L.map (strictAlong T)++(geoTransformAlong (⟨univ,E,I,d⟩ : MarkedIdeal n X) T).E) := by
  let M : MarkedIdeal n X:=⟨univ,E,I,d⟩
  apply isNormalCrossingsBoundary_of_open_traces (current_labelled_closed I hI d h hE T hT)
  intro y
  obtain ⟨U,B,G,hyU,hBE,hG,hMember,_hUnion,_hHighest⟩:=exists_labelled_joint_branch_chart h hE (T.proj y)
  let P:=restrict U T
  let MU:=MarkedIdeal.pullback (Subtype.val : U→X) M
  let MB:=localBranchMarked U (B++E.map ((Subtype.val : U→X) ⁻¹' ·)) univ I d
  have hMB : MB.IsWellFormed := by
    change (⟨(Subtype.val : U→X) ⁻¹' univ,B++E.map ((Subtype.val : U→X) ⁻¹' ·),
      GermIdeal.pullback (m:=n) (Subtype.val : U→X) I,d⟩ : MarkedIdeal n U).IsWellFormed
    rw [preimage_univ]
    exact ⟨isClosedSubmanifold_univ,GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI,
      hBE,SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hBE⟩
  have hP : IsGeoTestTower MB P:=prescribed_joint_test_history I hI d E ∅ T hT
    (centresIn_of_empty T he) U B hBE (by intro A hA;rw [preimage_empty];exact empty_subset _)
  have hSNC:=(MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hMB P hP).isSNCDivisor
  have hEntire : (geoTransformAlong MB P).E=B.map (strictAlong P)++(geoTransformAlong MU P).E:=
    entire_old_retained_boundary MU B P
  have hRecord:=geoTransformAlong_restrict U isClosedSubmanifold_univ hI T hT
  rw [hEntire,hRecord] at hSNC
  refine ⟨openPreimage T U,hyU,local_labelled_of_groups L T U B G hG (geoTransformAlong M T).E hSNC ?_⟩
  intro i
  rw [←strictAlong_restrict U T (L.get i),hMember i]
  exact strictAlong_finset_union P (G i) B.get

private theorem centresOver_of_centresIn {Z : Set X} (hZ : IsClosed Z) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),CentresIn Z T→CentresOver Z T
  | _,.refl,_ => trivial
  | _,.step T _ _ _,h =>
    ⟨centresOver_of_centresIn hZ T h.1,fun _ hp=>strictAlong_subset_preimage T hZ (h.2 hp)⟩

private theorem centresIn_head (Z : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),CentresIn Z T→∀ j : ℕ,CentresIn Z (head T j)
  | _,T,h,0 => by cases T <;>exact h
  | _,.refl,_,_+1 => trivial
  | _,.step T _ _ _,h,j+1 => centresIn_head Z T h.1 j

theorem labelledNC_highest_test_history
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) {L E : List (Set X)}
    (h : IsNormalCrossingsBoundary (n:=n) (L++E)) (hE : IsSNCDivisor n E) {r : ℕ}
    (hbound : ∀ x : X,branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) x≤r)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (⟨univ,E,I,d⟩ : MarkedIdeal n X) T)
    (hTZ : CentresIn {x : X | r≤branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) x} T) :
    IsNormalCrossingsBoundary (n:=n)
      (L.map (strictAlong T)++(geoTransformAlong (⟨univ,E,I,d⟩ : MarkedIdeal n X) T).E) := by
  let M : MarkedIdeal n X:=⟨univ,E,I,d⟩
  let Z:={x : X | r≤branchMultiplicity
    (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) x}
  have hZ : IsClosed Z:=isClosed_branchMultiplicity_superlevel _ _
  apply isNormalCrossingsBoundary_of_open_traces (current_labelled_closed I hI d h hE T hT)
  intro y
  by_cases hy : T.proj y∈Z
  · obtain ⟨U,B,G,hyU,_hBE,hG,_hMember,_hJoint,hHeads⟩:=
      exists_highest_labelled_joint_histories I hI d h hE hbound T hT hTZ hy
    have hCurrent : IsSNCDivisor n
        (B.map (strictAlong (restrict U T))++(geoTransformAlong M T).E.map
          ((Subtype.val : openPreimage T U→Y) ⁻¹' ·)) ∧
        ∀ i,(Subtype.val : openPreimage T U→Y) ⁻¹' strictAlong T (L.get i)=
          ⋃ k∈G i,strictAlong (restrict U T) (B.get k) := by
      cases T <;>exact hHeads 0
    exact ⟨openPreimage T U,hyU,
      local_labelled_of_groups L T U B G hG (geoTransformAlong M T).E hCurrent.1 hCurrent.2⟩
  · let U : Opens X:=⟨Zᶜ,hZ.isOpen_compl⟩
    have he : IsEmptyTower (restrict U T):=isEmptyTower_restrict_of_centresOver U
      (by exact disjoint_compl_left) T (centresOver_of_centresIn hZ T hTZ)
    have hIU : (GermIdeal.pullback (m:=n) (Subtype.val : U→X) I).IsCoherent:=
      GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI
    have hLocal:=isNormalCrossingsBoundary_open U h
    rw [List.map_append] at hLocal
    have hEU : IsSNCDivisor n (E.map ((Subtype.val : U→X) ⁻¹' ·)):=
      isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
    have hTU:=isGeoTestTower_restrict U isClosedSubmanifold_univ hI T hT
    have hTU' : IsGeoTestTower
        (⟨univ,E.map ((Subtype.val : U→X) ⁻¹' ·),
          GermIdeal.pullback (m:=n) (Subtype.val : U→X) I,d⟩ : MarkedIdeal n U) (restrict U T) := by
      simpa only [MarkedIdeal.pullback,preimage_univ] using hTU
    have hNC:=labelledNC_empty_test_history
      (GermIdeal.pullback (m:=n) (Subtype.val : U→X) I) hIU d hLocal hEU (restrict U T) hTU' he
    have hOld : (L.map ((Subtype.val : U→X) ⁻¹' ·)).map (strictAlong (restrict U T))=
        (L.map (strictAlong T)).map ((Subtype.val : openPreimage T U→Y) ⁻¹' ·) := by
      rw [List.map_map,List.map_map]
      apply List.map_congr_left
      intro A _hA
      exact strictAlong_restrict U T A
    have hRecord:=geoTransformAlong_restrict U isClosedSubmanifold_univ hI T hT
    have hMUeq : (⟨univ,E.map ((Subtype.val : U→X) ⁻¹' ·),
        GermIdeal.pullback (m:=n) (Subtype.val : U→X) I,d⟩ : MarkedIdeal n U)=
        MarkedIdeal.pullback (Subtype.val : U→X) M := by
      apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      · exact preimage_univ.symm
      · rfl
      · rfl
      · rfl
    rw [hOld,hMUeq,hRecord] at hNC
    exact ⟨openPreimage T U,hy,by simpa only [List.map_append,MarkedIdeal.pullback] using hNC⟩

theorem labelledNC_highest_test_history_head
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) {L E : List (Set X)}
    (h : IsNormalCrossingsBoundary (n:=n) (L++E)) (hE : IsSNCDivisor n E) {r : ℕ}
    (hbound : ∀ x : X,branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) x≤r)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (⟨univ,E,I,d⟩ : MarkedIdeal n X) T)
    (hTZ : CentresIn {x : X | r≤branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) x} T)
    (j : ℕ) :
    IsNormalCrossingsBoundary (n:=n)
      (L.map (strictAlong (head T j))++
        (geoTransformAlong (⟨univ,E,I,d⟩ : MarkedIdeal n X) (head T j)).E) :=
  labelledNC_highest_test_history I hI d h hE hbound (head T j)
    ((isGeoTestTower_iff_head_tail _ T j).mp hT).1 (centresIn_head _ T hTZ j)

theorem exists_original_labelled_count_drop
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1≤d)
    (hK : IsCompact (cosupport n univ I d)) {L E : List (Set X)}
    (h : IsNormalCrossingsBoundary (n:=n) (L++E)) (hE : IsSNCDivisor n E)
    {r : ℕ} (hr : 0<r)
    (hbound : ∀ x : X,branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) x≤r) :
    let M : MarkedIdeal n X:=⟨univ,E,I,d⟩
    let H:=⋃ A∈L,A
    let Z:={x : X | r≤branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) x}
    let K:=withN (CoefficientIdeal.coeffMarked M) Z
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),IsGeoResolution K T ∧
      IsGeoTestTower M T ∧ CentresIn Z T ∧
      (∀ j : ℕ,IsNormalCrossingsBoundary (n:=n)
        (L.map (strictAlong (head T j))++(geoTransformAlong M (head T j)).E)) ∧
      ∃ hp : IsBoundaryAdaptedCarrier (n:=n) (strictAlong T H) (geoTransformAlong M T).E,
        ∃ U : Opens Y,(U : Set Y)=(strictAlong T Z)ᶜ ∧ (geoTransformAlong M T).cosupp⊆U ∧
          ∀ y : U,branchMultiplicity
            (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open U hp)) y≤r-1 := by
  dsimp only
  obtain ⟨Y,T,hres,hT,hTZ,hPair,U,hUeq,hU,hCount⟩:=
    HironakaNormalCrossingsPermittedCountDrop.exists_original_phase_permitted_count_drop
      I hI d hd hK (boundaryAdapted_union_of_labelled h hE) hr hbound
  exact ⟨Y,T,hres,hT,hTZ,
    (fun j=>labelledNC_highest_test_history_head I hI d h hE hbound T hT hTZ j),
    hPair,U,hUeq,hU,hCount⟩

end
end Hironaka.HironakaNormalCrossingsLabelledPhasePreservation
