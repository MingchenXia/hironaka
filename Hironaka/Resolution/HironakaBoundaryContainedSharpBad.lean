import Hironaka.Resolution.HironakaG4GeneralSharpBadLocus

/-! The SAME full original sharp bad locus is analytic and relatively thin
for smooth targets, including components contained in boundary members.
Actual component windows and analytic continuation construct a dense
proof adapter; native containing-member NC comparison retains full E.
No singular target resolver or preparation schedule is constructed.
Blueprint: `hironaka-boundary-contained-sharp-bad-20261101.tex`. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaBoundaryContainedSharpBad
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  RegularLocusComponent NormalCrossings NormalCrossingsInvariance NormalCrossingsComparison
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpOriginalAllBoundaryCentre AnalyticSubsetOpens BlowupRestrictOpen

variable {n : ℕ} {X : CMfd.{u} n}

private theorem normalCrossingsAt_subfamily {W : Set X} {E F : List (Set X)} {x : X}
    (h : normalCrossingsAt (n := n) W E x) (hsub : ∀H∈F,H∈E) :
    normalCrossingsAt (n := n) W F x := by
  classical
  obtain ⟨S₀,S,hfam,hcard⟩ := h
  have hidx : ∀j : Fin F.length,∃i : Fin E.length,E.get i=F.get j :=
    fun j => List.mem_iff_get.mp (hsub _ (List.get_mem F j))
  choose idx hidx using hidx
  refine ⟨S₀,fun j => S (idx j),?_,fun j hj => hcard (idx j) (by rw [hidx];exact hj)⟩
  apply IsCoordinateFamilyAt.reindex hfam (Option.map idx)
  · rintro (_ | j)
    · rfl
    · exact (hidx j).symm
  · rintro (_ | j) <;> rfl

private theorem normalCrossingsAt_iff_of_containing_omitted
    {W : Set X} {E F : List (Set X)} (hW : IsClosed W) (hE : IsSNCDivisor n E)
    (hsub : ∀H∈F,H∈E) (hContains : ∀H∈E,H∉F → W⊆H)
    {x : X} (hx : x∈W) :
    normalCrossingsAt (n := n) W F x ↔ normalCrossingsAt (n := n) W E x := by
  constructor
  · intro h
    obtain ⟨O,hOsub,hOo,hxO⟩ := mem_nhds_iff.mp
      (eventually_normalCrossingsAt hW (fun H hH => hE.1 H (hsub H hH)) h)
    let U : Opens X := ⟨O,hOo⟩
    let WU : Set U := (Subtype.val : U → X) ⁻¹' W
    let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
    let FU := F.map ((Subtype.val : U → X) ⁻¹' ·)
    have hEU : IsSNCDivisor n EU := isSNCDivisor_map_preimage
      (pullsBackCoordinates_val U) continuous_subtype_val hE
    have hFU : HasNormalCrossings n WU FU := by
      intro y _hy
      exact normalCrossingsAt_preimage_val_iff.mpr (hOsub y.property)
    have hSubU : ∀H∈FU,H∈EU := by
      rintro H hH
      obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hH
      exact List.mem_map.mpr ⟨A,hsub A hA,rfl⟩
    have hContainsU : ∀H∈EU,H∉FU → WU⊆H := by
      rintro H hH hNot
      obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hH
      have hNotA : A∉F := fun hAF => hNot (List.mem_map.mpr ⟨A,hAF,rfl⟩)
      exact fun y hy => hContains A hA hNotA hy
    have hFull := (hasNormalCrossings_iff_of_forall_mem hEU hSubU hContainsU).mp hFU
    exact normalCrossingsAt_preimage_val_iff.mp (hFull (⟨x,hxO⟩ : U) hx)
  · exact fun h => normalCrossingsAt_subfamily h hsub

/-- A genuine component window produces a dense proof adapter and the
EXACT full-boundary bad-locus trace, including boundary-contained components.
Only members containing the WHOLE same component are omitted. -/
theorem exists_actual_component_boundary_window (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) {x : X} (hx : x∈W) :
    ∃(U : Opens X)(F : List (Set X)),x∈U ∧ F.Sublist E ∧
      (∀H,H∈F ↔ H∈E ∧ ¬component (n := n) W x⊆H) ∧
      (∀H∈E,H∉F → W∩(U : Set X)⊆H) ∧
      ((Subtype.val : U → X) ⁻¹' W⊆closure
        (((Subtype.val : U → X) ⁻¹' W)\
          ⋃H∈F.map ((Subtype.val : U → X) ⁻¹' ·),H)) ∧
      originalSharpBadLocus (n := n) ((Subtype.val : U → X) ⁻¹' W)
          (F.map ((Subtype.val : U → X) ⁻¹' ·))=
        (Subtype.val : U → X) ⁻¹' originalSharpBadLocus (n := n) W E := by
  classical
  obtain ⟨q,hq⟩ := hW.2 x hx
  obtain ⟨O,hOo,hxO,hComp⟩ := exists_open_inter_subset_component hq (mem_component_self hq)
  let U : Opens X := ⟨O,hOo⟩
  let keep : Set X → Bool := fun H => decide (¬component (n := n) W x⊆H)
  let F := E.filter keep
  have hMem : ∀H,H∈F ↔ H∈E ∧ ¬component (n := n) W x⊆H := by
    intro H
    simp [F,keep]
  have hOmitted : ∀H∈E,H∉F → W∩(U : Set X)⊆H := by
    intro H hHE hNot y hy
    have hCH : component (n := n) W x⊆H := by
      by_contra hNo
      exact hNot ((hMem H).mpr ⟨hHE,hNo⟩)
    exact hCH (hComp hy)
  let s : Finset (Fin E.length) := Finset.univ.filter fun i => keep (E.get i)=true
  have hThin : ∀i∈s,∀P : Set X,IsOpen P → P⊆(U : Set X) →
      (P∩W).Nonempty → ∃y∈P∩W,y∉E.get i := by
    intro i hi P hPo hPU hne
    have hNot : ¬component (n := n) W x⊆E.get i := by
      simpa only [keep,decide_eq_true_eq] using (Finset.mem_filter.mp hi).2
    by_contra hNo
    have hAll : P∩W⊆E.get i := by
      intro y hy
      by_contra hyNot
      exact hNo ⟨y,hy,hyNot⟩
    obtain ⟨y,hyP,hyW⟩ := hne
    apply hNot
    exact component_subset_of_isOpen
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
        (MonomialPart.isClosedSubmanifold_get hn hE i)) hPo
      ⟨y,hyP,hComp ⟨hyW,hPU hyP⟩⟩
      (fun z hz => hAll ⟨hz.1,component_subset W x hz.2⟩)
  have hOpen : ∀i∈s,IsOpen ((U : Set X)\E.get i) :=
    fun i _hi => U.isOpen.inter (hE.1 _ (List.get_mem E i)).isOpen_compl
  have hDenseAmbient : W∩(U : Set X)⊆closure ((W∩(U : Set X))\⋃H∈F,H) := by
    rintro y ⟨hyW,hyU⟩
    apply mem_closure_iff.mpr
    intro P hPo hyP
    obtain ⟨P',_hP'o,hP'P,⟨z,hzP',hzW⟩,hAvoid⟩ :=
      ThinDimensionDrop.exists_isOpen_avoid s hThin hOpen (hPo.inter U.isOpen)
        inter_subset_right ⟨y,⟨hyP,hyU⟩,hyW⟩
    refine ⟨z,(hP'P hzP').1,⟨⟨hzW,(hP'P hzP').2⟩,?_⟩⟩
    intro hzBoundary
    obtain ⟨H,hHF,hzH⟩ := mem_iUnion₂.mp hzBoundary
    obtain ⟨hHE,hNot⟩ := (hMem H).mp hHF
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hHE
    have hi : i∈s := Finset.mem_filter.mpr
      ⟨Finset.mem_univ i,by simpa only [keep,decide_eq_true_eq] using hNot⟩
    exact (eq_empty_iff_forall_notMem.mp (hAvoid i hi) z) ⟨hzP',hzH⟩
  let WU : Set U := (Subtype.val : U → X) ⁻¹' W
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let FU := F.map ((Subtype.val : U → X) ⁻¹' ·)
  have hUnion : (Subtype.val : U → X) ⁻¹' (⋃H∈F,H)=⋃H∈FU,H := by
    ext y
    constructor
    · intro hy
      obtain ⟨H,hHF,hyH⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨(Subtype.val : U → X) ⁻¹' H,List.mem_map.mpr ⟨H,hHF,rfl⟩,hyH⟩
    · intro hy
      obtain ⟨H,hHF,hyH⟩ := mem_iUnion₂.mp hy
      obtain ⟨A,hAF,rfl⟩ := List.mem_map.mp hHF
      exact mem_iUnion₂.mpr ⟨A,hAF,hyH⟩
  have hInside : (Subtype.val : U → X) ⁻¹' ((W∩(U : Set X))\⋃H∈F,H)=
      WU\⋃H∈FU,H := by
    rw [preimage_sdiff,preimage_inter,hUnion]
    have hUall : (Subtype.val : U → X) ⁻¹' (U : Set X)=univ :=
      eq_univ_iff_forall.mpr fun y => y.property
    rw [hUall,inter_univ]
  have hDense : WU⊆closure (WU\⋃H∈FU,H) := by
    intro y hy
    have hcl : y∈(Subtype.val : U → X) ⁻¹' closure ((W∩(U : Set X))\⋃H∈F,H) :=
      hDenseAmbient ⟨hy,y.property⟩
    have h : (Subtype.val : U → X) ⁻¹' closure ((W∩(U : Set X))\⋃H∈F,H)=
        closure ((Subtype.val : U → X) ⁻¹' ((W∩(U : Set X))\⋃H∈F,H)) :=
      U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
        (show Continuous (Subtype.val : U → X) from continuous_subtype_val)
        ((W∩(U : Set X))\⋃H∈F,H)
    rw [hInside] at h
    exact (Set.ext_iff.mp h y).mp hcl
  have hWU : IsClosedSubmanifold n WU := isClosedSubmanifold_preimage_val hW U
  have hEU : IsSNCDivisor n EU := isSNCDivisor_map_preimage
    (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hSubU : ∀H∈FU,H∈EU := by
    rintro H hH
    obtain ⟨A,hAF,rfl⟩ := List.mem_map.mp hH
    exact List.mem_map.mpr ⟨A,((hMem A).mp hAF).1,rfl⟩
  have hContainsU : ∀H∈EU,H∉FU → WU⊆H := by
    rintro H hH hNot
    obtain ⟨A,hAE,rfl⟩ := List.mem_map.mp hH
    have hNotA : A∉F := fun hAF => hNot (List.mem_map.mpr ⟨A,hAF,rfl⟩)
    exact fun y hy => hOmitted A hAE hNotA ⟨hy,y.property⟩
  have hReduced : originalSharpBadLocus (n := n) WU FU=
      originalSharpBadLocus (n := n) WU EU := by
    ext y
    by_cases hy : y∈WU
    · exact and_congr Iff.rfl
        (not_congr (normalCrossingsAt_iff_of_containing_omitted
          (X := CMfd.of (n := n) U) (W := WU) (E := EU) (F := FU)
          hWU.1 hEU hSubU hContainsU hy))
    · change (y∈WU ∧ _) ↔ (y∈WU ∧ _)
      simp only [hy,false_and]
  have hFull : originalSharpBadLocus (n := n) WU EU=
      (Subtype.val : U → X) ⁻¹' originalSharpBadLocus (n := n) W E := by
    ext y
    exact and_congr Iff.rfl (not_congr normalCrossingsAt_preimage_val_iff)
  exact ⟨U,F,hxO,List.filter_sublist,hMem,hOmitted,hDense,hReduced.trans hFull⟩

/-- The literal original FULL-boundary sharp bad locus is analytic and
relatively thin for every closed smooth target, including components
contained in boundary members. No density, purity or positive dimension
hypothesis is supplied. -/
theorem original_sharp_bad_analytic_and_thin
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) :
    IsComplexAnalyticSubset (n := n) (originalSharpBadLocus (n := n) W E) ∧
      ∀O : Set X,IsOpen O → O∩W⊆originalSharpBadLocus (n := n) W E → O∩W=∅ := by
  classical
  by_cases hn : 0<n
  · constructor
    · apply isComplexAnalyticSubset_of_forall_opens
      intro x
      by_cases hx : x∈W
      · obtain ⟨U,F,hxU,hFE,_hMem,_hOmitted,hDense,hEq⟩ :=
          exists_actual_component_boundary_window hn hW hE hx
        have hWU := isClosedSubmanifold_preimage_val hW U
        have hFU : IsSNCDivisor n (F.map ((Subtype.val : U → X) ⁻¹' ·)) :=
          isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val
            (isSNCDivisor_of_sublist hE hFE)
        have hAna := HironakaG4GeneralSharpBadLocus.isComplexAnalyticSubset_originalSharpBadLocus
          (X := CMfd.of (n := n) U) hWU hFU hDense
        exact ⟨U,hxU,hEq ▸ hAna⟩
      · let U : Opens X := ⟨Wᶜ,hW.1.isOpen_compl⟩
        have hEmpty : (Subtype.val : U → X) ⁻¹' originalSharpBadLocus (n := n) W E=∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact y.property hy.1
        refine ⟨U,hx,?_⟩
        rw [hEmpty]
        exact isComplexAnalyticSubset_empty
    · intro O hOo hSub
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hxO,hxW⟩
      obtain ⟨U,F,hxU,_hFE,_hMem,_hOmitted,hDense,hEq⟩ :=
        exists_actual_component_boundary_window hn hW hE hxW
      have hWU := isClosedSubmanifold_preimage_val hW U
      have hLocal : ((Subtype.val : U → X) ⁻¹' O)∩((Subtype.val : U → X) ⁻¹' W)⊆
          originalSharpBadLocus (n := n) ((Subtype.val : U → X) ⁻¹' W)
            (F.map ((Subtype.val : U → X) ⁻¹' ·)) := by
        intro y hy
        rw [hEq]
        exact hSub hy
      have hEmpty := HironakaG4GeneralSharpBadLocus.originalSharpBadLocus_thin
        (X := CMfd.of (n := n) U) hWU hDense
        ((Subtype.val : U → X) ⁻¹' O) (hOo.preimage continuous_subtype_val) hLocal
      have hm : (⟨x,hxU⟩ : U)∈
          ((Subtype.val : U → X) ⁻¹' O)∩((Subtype.val : U → X) ⁻¹' W) := ⟨hxO,hxW⟩
      rw [hEmpty] at hm
      exact hm
  · have hn0 : n=0 := by omega
    have hEmpty : originalSharpBadLocus (n := n) W E=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨H,hHE,hxH⟩ := mem_iUnion₂.mp
        (originalSharpBadLocus_subset_boundary hW hx).2
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hHE
      obtain ⟨S,_hCoord,hCard,_hInj⟩ := hE.2 x
      have hOne := hCard i hxH
      have hLe := Finset.card_le_univ (s := S i)
      simp only [Fintype.card_fin] at hLe
      omega
    constructor
    · rw [hEmpty]
      exact isComplexAnalyticSubset_empty
    · intro O _hOo hSub
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hh := hSub hx
      rw [hEmpty] at hh
      exact hh

end
end Hironaka.HironakaBoundaryContainedSharpBad
