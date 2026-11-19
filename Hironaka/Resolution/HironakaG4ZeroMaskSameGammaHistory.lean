import Hironaka.Resolution.HironakaG4MonomialRowChain
import Hironaka.Resolution.HironakaG4ZeroResidualMonomialSum
import Hironaka.Resolution.HironakaG4CompactWholeMonomialMaskPhase
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Resolution.HironakaSharpOriginalFirstMemberExceptionalFactor
import Hironaka.Invariant.StepOneEmptyPrefix
import Hironaka.Resolution.HironakaG4ZeroMaskGammaStep

set_option autoImplicit false

/-!
# The same compact-supported gamma history and the actual mixed records

The complete source-first proof is in
`blueprint/src/hironaka-g4-zero-mask-same-gamma-history.tex`.
The real native canonical segment is selected ONCE. The actual accepted
global gamma step is applied to each SAME recorded map; no resolving history
or future state is an input to the public producer.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG4ZeroMaskSameGammaHistory

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualFiniteChronologicalHistory HironakaG4CompactWholeMonomialMaskPhase
  HironakaCoherentTransformExtension NormalCrossings MonomialPartAlong
  DivisorExponentAlong RelativePrincipalizationSpan RestrictedIdealExtension
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaSharpOriginalProductTraceOrder HironakaG4ZeroMaskGammaStep
  HironakaSharpActualOriginalControlledHistory BlowupStrictSubmanifold
  NormalCrossingsComparison SimultaneousNormalCrossings GermIdealOrder
  MonomialStepAlong MonomialCaseAlong IdealWeightPowers HironakaG4MonomialRowChain

variable {n : ℕ} {X Y : CMfd.{u} n}

def oldEquiv (old : List (Set X)) (T : BlowupTower X Y) :
    Fin old.length ≃ Fin (old.map (strictAlong T)).length :=
  finCongr (by simp)

theorem get_oldEquiv (old : List (Set X)) (T : BlowupTower X Y)
    (i : Fin old.length) :
    (old.map (strictAlong T)).get (oldEquiv old T i)=strictAlong T (old.get i) := by
  simp [oldEquiv]

private theorem mask_oldEquiv (old : List (Set X)) (T : BlowupTower X Y)
    (P : Finset (Fin old.length)) (i : Fin old.length) :
    oldEquiv old T i ∈ P.map (oldEquiv old T).toEmbedding ↔ i ∈ P := by
  simp

private theorem trace_oldEquiv (N : Set Y) (old : List (Set X)) (T : BlowupTower X Y)
    (i : Fin old.length) :
    oldTraceIdeal N (old.map (strictAlong T)) (oldEquiv old T i)=
      restrictOn n N (vanishingIdeal (n := n) (strictAlong T (old.get i))) := by
  simp only [oldTraceIdeal,get_oldEquiv]

theorem monomial_oldEquiv (N : Set Y) (old : List (Set X))
    (born : List (Set Y)) (T : BlowupTower X Y) (i : Fin old.length) :
    oldMonomialPart N (old.map (strictAlong T)) born (oldEquiv old T i)=
      monomialPartAlong n N
        (restrictOn n N (vanishingIdeal (n := n) (strictAlong T (old.get i)))) born := by
  simp only [oldMonomialPart,trace_oldEquiv]

private theorem residual_oldEquiv (N : Set Y) (old : List (Set X))
    (born : List (Set Y)) (T : BlowupTower X Y) (i : Fin old.length) :
    oldResidualPart N (old.map (strictAlong T)) born (oldEquiv old T i)=
      nonmonomialPartAlong n N
        (restrictOn n N (vanishingIdeal (n := n) (strictAlong T (old.get i)))) born := by
  simp only [oldResidualPart,trace_oldEquiv]

theorem finite_sum_oldEquiv (old : List (Set X)) (T : BlowupTower X Y)
    (P : Finset (Fin old.length)) {Z : CMfd.{u} n}
    (D : Fin (old.map (strictAlong T)).length → GermIdeal n Z) :
    (⟨fun y g => IsInSpanAt (n := n)
      (fun f => ∃ j ∈ P.map (oldEquiv old T).toEmbedding,(D j).mem y f) y g⟩ : GermIdeal n Z)=
    ⟨fun y g => IsInSpanAt (n := n)
      (fun f => ∃ i ∈ P,(D (oldEquiv old T i)).mem y f) y g⟩ := by
  ext y g
  have hgen : (fun f => ∃ j ∈ P.map (oldEquiv old T).toEmbedding,(D j).mem y f)=
      (fun f => ∃ i ∈ P,(D (oldEquiv old T i)).mem y f) := by
    funext f
    apply propext
    constructor
    · rintro ⟨j,hj,hf⟩
      obtain ⟨i,hi,hij⟩ := Finset.mem_map.mp hj
      exact ⟨i,hi,hij ▸ hf⟩
    · rintro ⟨i,hi,hf⟩
      exact ⟨oldEquiv old T i,Finset.mem_map.mpr ⟨i,hi,rfl⟩,hf⟩
  change IsInSpanAt (n := n)
    (fun f => ∃ j ∈ P.map (oldEquiv old T).toEmbedding,(D j).mem y f) y g ↔
    IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D (oldEquiv old T i)).mem y f) y g
  rw [hgen]

private theorem row_full_record (N : Set X) (born : List (Set X))
    (J : GermIdeal n X) (d : ℕ) (T : BlowupTower X Y) :
    geoTransformAlong (⟨N,born,J,d⟩ : MarkedIdeal n X) T=
      ⟨strictAlong T N,(geoTransformAlong (geometricTemplate N born) T).E,
        (geoTransformAlong (⟨N,born,J,d⟩ : MarkedIdeal n X) T).ideal,d⟩ := by
  have hE := geoTransformAlong_E_eq_of_E_eq
    (𝔪 := geometricTemplate N born) (𝔍 := (⟨N,born,J,d⟩ : MarkedIdeal n X)) rfl T
  change (⟨(geoTransformAlong (⟨N,born,J,d⟩ : MarkedIdeal n X) T).N,
    (geoTransformAlong (⟨N,born,J,d⟩ : MarkedIdeal n X) T).E,
    (geoTransformAlong (⟨N,born,J,d⟩ : MarkedIdeal n X) T).ideal,
    (geoTransformAlong (⟨N,born,J,d⟩ : MarkedIdeal n X) T).d⟩ : MarkedIdeal n Y)=_
  rw [N_geoTransformAlong,hE,d_geoTransformAlong]

private theorem full_ordered_list (N : Set X) (old born : List (Set X))
    (T : BlowupTower X Y) :
    (geoTransformAlong (geometricTemplate (univ : Set X) (old ++ born)) T).E=
      old.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate N born) T).E := by
  have h := full_ordered N old.get born T
  have ho : List.ofFn old.get=old := List.ofFn_get old
  have hm : List.ofFn (fun i => strictAlong T (old.get i))=old.map (strictAlong T) := by
    simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map old (strictAlong T)
  rw [ho,hm] at h
  exact h

theorem segment_head (M : MarkedIdeal n X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      ResolutionDriver.IsCanonicalSegment M
        (fun {Y} Q => MonomialStepAlong.towerInvAlong M (Y := Y) Q) T →
      ∀ k,ResolutionDriver.IsCanonicalSegment M
        (fun {Y} Q => MonomialStepAlong.towerInvAlong M (Y := Y) Q)
        (BlowupTowerSplit.head T k)
  | _,.refl,_,0 => trivial
  | _,.refl,_,_+1 => trivial
  | _,.step _ _ _ _,h,0 => h
  | _,.step T _ _ _,h,k+1 => segment_head M T h.1 k

private theorem split_append_tail_length (Q : BlowupTower X Y)
    {Z : CMfd.{u} n} (R : BlowupTower Y Z) :
    BlowupTowerSplit.split (Q.append R) R.length=⟨Y,Q,R⟩ := by
  have h := StepOneEmptyPrefix.split_append_of_le Q R R.length (Nat.le_refl _)
  have hs := StepOneEmptyPrefix.split_of_length_le R R.length (Nat.le_refl _)
  dsimp only [BlowupTowerSplit.head,BlowupTowerSplit.tail] at h
  rw [hs] at h
  exact h

private def canonicalMatrix (N : Set X) (old born : List (Set X)) :
    X → Fin old.length → Fin born.length → ℕ := fun x i j =>
  divExpAlong n N (oldMonomialPart N old born i) (born.get j) x

private def maskMarked (N : Set X) (old born : List (Set X))
    (P : Finset (Fin old.length)) : MarkedIdeal n X :=
  ⟨N,born,⟨fun x g => IsInSpanAt (n := n)
    (fun f => ∃ i ∈ P,(oldMonomialPart N old born i).mem x f) x g⟩,1⟩

private theorem labels_refl (old : List (Set X)) :
    (⟨old.map (strictAlong (BlowupTower.refl : BlowupTower X X)),
      oldEquiv old (BlowupTower.refl : BlowupTower X X)⟩ :
      Σ L : List (Set X),Fin old.length ≃ Fin L.length)=⟨old,Equiv.refl _⟩ := by
  have aux (L : List (Set X)) (hL : L=old) (he : old.length=L.length) :
      (⟨L,finCongr he⟩ : Σ K : List (Set X),Fin old.length ≃ Fin K.length)=
        ⟨old,Equiv.refl _⟩ := by
    subst L
    rfl
  unfold oldEquiv
  exact aux _ (List.map_id old) (by simp)

private def currentStateData (N : Set X) (old born : List (Set X))
    (P : Finset (Fin old.length)) (T : BlowupTower X Y)
    (labels : Σ L : List (Set Y),Fin old.length ≃ Fin L.length) : Prop :=
  let NQ := strictAlong T N
  let oldQ := labels.1
  let bornQ := (geoTransformAlong (geometricTemplate N born) T).E
  let eQ := labels.2
  let PQ := P.map eQ.toEmbedding
  let MQ := maskMarked NQ oldQ bornQ PQ
  geoTransformAlong (maskMarked N old born P) T=MQ ∧
  IsClosedSubmanifold n NQ ∧ IsSNCDivisor n (oldQ ++ bornQ) ∧
  IsTransverse n NQ bornQ ∧ NQ ⊆ closure (NQ \ ⋃ H ∈ oldQ ++ bornQ,H) ∧
  (∀ z ∈ NQ,∀ i,ordinaryTraceOrder NQ (oldResidualPart NQ oldQ bornQ i) z ≤ 1) ∧
  (∀ z ∈ NQ,IsPreparedResidualSNCAt NQ oldQ bornQ z) ∧
  (∀ z ∈ NQ,tauD (canonicalMatrix NQ oldQ bornQ z) ≤ P.card) ∧
  (∀ z ∈ NQ,∀ i : Fin old.length,
    eQ i ∈ properRows (canonicalMatrix NQ oldQ bornQ z) →
      i ∈ properRows (canonicalMatrix N old born (T.proj z))) ∧
  (∀ z ∈ NQ,tauD (canonicalMatrix NQ oldQ bornQ z)=P.card →
    nuOne (canonicalMatrix NQ oldQ bornQ z)=0) ∧
  MQ.IsWellFormed ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ MQ.ideal z) ∧
  IsMonomialAlong n NQ MQ.ideal bornQ ∧
  MQ.cosupp={z | z ∈ NQ ∧ PQ ⊆ properRows (canonicalMatrix NQ oldQ bornQ z)} ∧
  IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T ∧
  CurrentSharpCentres N (old ++ born) T ∧
  (∀ i : Fin old.length,
    let d := if i ∈ P then 1 else 0
    IsGeoTestTower (⟨N,born,oldTraceIdeal N old i,d⟩ : MarkedIdeal n X) T ∧
    IsGeoTestTower (⟨N,born,oldMonomialPart N old born i,d⟩ : MarkedIdeal n X) T ∧
    IsGeoTestTower (⟨N,born,oldResidualPart N old born i,0⟩ : MarkedIdeal n X) T ∧
    geoTransformAlong (⟨N,born,oldTraceIdeal N old i,d⟩ : MarkedIdeal n X) T=
      ⟨NQ,bornQ,oldTraceIdeal NQ oldQ (eQ i),d⟩ ∧
    geoTransformAlong (⟨N,born,oldMonomialPart N old born i,d⟩ : MarkedIdeal n X) T=
      ⟨NQ,bornQ,oldMonomialPart NQ oldQ bornQ (eQ i),d⟩ ∧
    geoTransformAlong (⟨N,born,oldResidualPart N old born i,0⟩ : MarkedIdeal n X) T=
      ⟨NQ,bornQ,oldResidualPart NQ oldQ bornQ (eQ i),0⟩)

private def currentState (N : Set X) (old born : List (Set X))
    (P : Finset (Fin old.length)) (T : BlowupTower X Y) : Prop :=
  currentStateData N old born P T ⟨old.map (strictAlong T),oldEquiv old T⟩

private theorem currentState_refl {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length))
    (hTau : ∀ x ∈ N,tauD (canonicalMatrix N old born x) ≤ P.card)
    (hNu : ∀ x ∈ N,tauD (canonicalMatrix N old born x)=P.card →
      nuOne (canonicalMatrix N old born x)=0)
    (hWF : (maskMarked N old born P).IsWellFormed)
    (hNZ : ∀ x ∈ N,IsNonzeroAlongAt N (maskMarked N old born P).ideal x)
    (hMono : IsMonomialAlong n N (maskMarked N old born P).ideal born)
    (hCosupp : (maskMarked N old born P).cosupp=
      {x | x ∈ N ∧ P ⊆ properRows (canonicalMatrix N old born x)}) :
    currentState N old born P (BlowupTower.refl : BlowupTower X X) := by
  unfold currentState
  rw [labels_refl]
  simp_all [currentStateData,HomogenizedGlueingTower.strictAlong,
    geometricTemplate,IsGeoTestTower,CurrentSharpCentres]

private theorem currentState_step (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hE0 : IsSNCDivisor n (old ++ born))
    (P : Finset (Fin old.length)) (hP : P.Nonempty)
    (T : BlowupTower X Y) (hQ : currentState N old born P T)
    {Z : CMfd.{u} n} (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCenter : C=maxLocusA (geoTransformAlong (maskMarked N old born P) T)) :
    currentState N old born P (.step T C π hπ) := by
  classical
  let NQ := strictAlong T N
  let L := old.map (strictAlong T)
  let B := (geoTransformAlong (geometricTemplate N born) T).E
  let e := oldEquiv old T
  let PQ := P.map e.toEmbedding
  let MQ := maskMarked NQ L B PQ
  change currentStateData N old born P T ⟨L,e⟩ at hQ
  dsimp only [currentStateData] at hQ
  obtain ⟨hSum,hN,hE,hTr,hDense,hOrd,hPrep,hTau,hActivity,hNu,hWF,hNZ,hMono,
    hCos,hFull,hSharp,hRows⟩ := hQ
  have hPQ : PQ.Nonempty := hP.map
  have hTauQ : ∀ y ∈ NQ,tauD (canonicalMatrix NQ L B y) ≤ PQ.card := by
    simpa only [PQ,Finset.card_map] using hTau
  have hG := prepared_zero_mask_global_gamma_step (N := NQ) (old := L) (born := B)
    hn hN hE hTr hDense hOrd hPrep PQ hPQ
    hTauQ hMono
  obtain ⟨_hc,_hnz,_hw,_hs,hAdm,_hThin,hCNC,hBad,_hProper,hAdmRows,hNext⟩ := hG
  have hC : C=maxLocusA MQ := hCenter.trans (congrArg maxLocusA hSum)
  dsimp only [MQ,maskMarked] at hC
  rw [←hC] at hAdm hCNC hBad hAdmRows hNext
  have hCN : C ⊆ NQ := hAdm.subset_N
  have hCB : HasNormalCrossings n C B :=
    hasNormalCrossings_of_forall_mem hCNC (fun _ hH => List.mem_append_right L hH)
  have hNextπ := hNext Z π hπ
  obtain ⟨hN',hE',hTr',hDense',_hOldLen,_hBornLen,hOrd',hPrep',hParts',hSum',
    hWF',hNZ',hMono',hSub',hTau',hNu',hCos'⟩ := hNextπ
  let T' : BlowupTower X Z := .step T C π hπ
  let N' := strictAlong T' N
  let L' := old.map (strictAlong T')
  let B' := (geoTransformAlong (geometricTemplate N born) T').E
  have hList : L.map (geoStrictTransform π C)=L' := by
    simp only [L,L',T',HomogenizedGlueingTower.strictAlong,List.map_map,Function.comp_def]
  have hNnext : geoStrictTransform π C NQ=N' := rfl
  have hBnext : B.map (geoStrictTransform π C) ++ [π ⁻¹' C]=B' := rfl
  have hNout : IsClosedSubmanifold n N' := hN'
  have hEout : IsSNCDivisor n (L' ++ B') := by simpa only [hList,hBnext] using hE'
  have hTrout : IsTransverse n N' B' := hTr'
  have hDenseout : N' ⊆ closure (N' \ ⋃ H ∈ L' ++ B',H) := by
    simpa only [hNnext,hList,hBnext] using hDense'
  have hOrdout : ∀ z ∈ N',∀ i,ordinaryTraceOrder N' (oldResidualPart N' L' B' i) z ≤ 1 := by
    rw [←hList,←hNnext,←hBnext]
    exact hOrd'
  have hPrepout : ∀ z ∈ N',IsPreparedResidualSNCAt N' L' B' z := by
    simpa only [hNnext,hList,hBnext] using hPrep'
  have hFullWF0 : (geometricTemplate (univ : Set X) (old ++ born)).IsWellFormed :=
    ⟨⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩,
      isCoherent_unitIdeal,hE0,isTransverse_univ_of_isSNCDivisor hE0⟩
  have hFullWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hFullWF0 T hFull
  have hFull' : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T' := by
    refine ⟨hFull,hπ.1,?_,?_⟩
    · change C ⊆ cosupport n _ _ (geoTransformAlong
        (geometricTemplate (univ : Set X) (old ++ born)) T).d
      rw [d_geoTransformAlong]
      change C ⊆ cosupport n _ _ 0
      rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hFullWF.isCoherent hg),
        N_geoTransformAlong]
      change C ⊆ strictAlong T (univ : Set X)
      rw [strict_univ T]
      exact subset_univ C
    · rw [full_ordered_list N old born T]
      exact hCNC
  have hSharp' : CurrentSharpCentres N (old ++ born) T' := by
    refine ⟨hSharp,?_⟩
    rw [full_ordered_list N old born T]
    exact hBad
  let Dn : Fin L.length → GermIdeal n Z := fun j =>
    monomialPartAlong n N' (restrictOn n N'
      (vanishingIdeal (n := n) (geoStrictTransform π C (L.get j)))) B'
  let Sn : GermIdeal n Z := ⟨fun z g =>
    IsInSpanAt (n := n) (fun f => ∃ j ∈ PQ,(Dn j).mem z f) z g⟩
  let Mn : MarkedIdeal n Z := ⟨N',B',Sn,1⟩
  let Mout := maskMarked N' L' B' (P.map (oldEquiv old T').toEmbedding)
  have hGetNext (i : Fin old.length) :
      L'.get (oldEquiv old T' i)=geoStrictTransform π C (L.get (e i)) := by
    calc
      L'.get (oldEquiv old T' i)=strictAlong T' (old.get i) := get_oldEquiv old T' i
      _=geoStrictTransform π C (strictAlong T (old.get i)) := rfl
      _=geoStrictTransform π C (L.get (e i)) := congrArg _ (get_oldEquiv old T i).symm
  have hDn (i : Fin old.length) : oldMonomialPart N' L' B' (oldEquiv old T' i)=Dn (e i) := by
    change monomialPartAlong n N' (restrictOn n N' (vanishingIdeal (n := n)
      (L'.get (oldEquiv old T' i)))) B' = _
    rw [hGetNext i]
  have hSigma : Mout.ideal=Sn := by
    change (⟨fun z g => IsInSpanAt (n := n)
      (fun f => ∃ j ∈ P.map (oldEquiv old T').toEmbedding,
        (oldMonomialPart N' L' B' j).mem z f) z g⟩ : GermIdeal n Z)=Sn
    calc
      _=⟨fun z g => IsInSpanAt (n := n) (fun f => ∃ i ∈ P,
          (oldMonomialPart N' L' B' (oldEquiv old T' i)).mem z f) z g⟩ :=
        finite_sum_oldEquiv old T' P _
      _=⟨fun z g => IsInSpanAt (n := n)
          (fun f => ∃ i ∈ P,(Dn (e i)).mem z f) z g⟩ := by simp_rw [hDn]
      _=Sn := (finite_sum_oldEquiv old T P Dn).symm
  have hModel : Mout=Mn :=
    congrArg (fun I : GermIdeal n Z => (⟨N',B',I,1⟩ : MarkedIdeal n Z)) hSigma
  change Mn=MQ.geoTransform C π at hSum'
  have hSumout : geoTransformAlong (maskMarked N old born P) T'=Mout := by
    change (geoTransformAlong (maskMarked N old born P) T).geoTransform C π=Mout
    exact (congrArg (fun R : MarkedIdeal n Y => R.geoTransform C π) hSum).trans
      (hSum'.symm.trans hModel.symm)
  have hRowNext (z : Z) (i : Fin old.length) :
      oldEquiv old T' i ∈ properRows (canonicalMatrix N' L' B' z) ↔
        e i ∈ properRows (fun j k => divExpAlong n N' (Dn j) (B'.get k) z) := by
    simp only [properRows,Finset.mem_filter,Finset.mem_univ,true_and]
    change (0 < ∑ k : Fin B'.length,
      divExpAlong n N' (oldMonomialPart N' L' B' (oldEquiv old T' i)) (B'.get k) z) ↔
        (0 < ∑ k : Fin B'.length,divExpAlong n N' (Dn (e i)) (B'.get k) z)
    rw [hDn i]
  have hMaskNext (z : Z) :
      P.map (oldEquiv old T').toEmbedding ⊆ properRows (canonicalMatrix N' L' B' z) ↔
        PQ ⊆ properRows (fun j k => divExpAlong n N' (Dn j) (B'.get k) z) := by
    constructor
    · intro h j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
      exact (hRowNext z i).mp (h (Finset.mem_map.mpr ⟨i,hi,rfl⟩))
    · intro h j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
      exact (hRowNext z i).mpr (h (Finset.mem_map.mpr ⟨i,hi,rfl⟩))
  let en : Fin L.length ≃ Fin L'.length := finCongr (by simp [L,L'])
  have hAn (z : Z) :
      (fun j k => divExpAlong n N' (Dn j) (B'.get k) z)=
        (fun j k => canonicalMatrix N' L' B' z (en j) k) := by
    funext j k
    change divExpAlong n N' (Dn j) (B'.get k) z=
      divExpAlong n N' (oldMonomialPart N' L' B' (en j)) (B'.get k) z
    obtain ⟨i,rfl⟩ := e.surjective j
    have he : en (e i)=oldEquiv old T' i := Fin.ext rfl
    rw [he,hDn]
  have hFinInv {r s b : ℕ} (h : r=s) (A : Fin s → Fin b → ℕ) :
      tauD (fun i => A (finCongr h i))=tauD A ∧
        nuOne (fun i => A (finCongr h i))=nuOne A := by
    subst s
    exact ⟨rfl,rfl⟩
  have hInv (z : Z) :
      tauD (fun j k => divExpAlong n N' (Dn j) (B'.get k) z)=
          tauD (canonicalMatrix N' L' B' z) ∧
      nuOne (fun j k => divExpAlong n N' (Dn j) (B'.get k) z)=
          nuOne (canonicalMatrix N' L' B' z) := by
    have hh := hFinInv (show L.length=L'.length from by simp [L,L'])
      (canonicalMatrix N' L' B' z)
    exact ⟨(congrArg (fun A => tauD A) (hAn z)).trans hh.1,
      (congrArg (fun A => nuOne A) (hAn z)).trans hh.2⟩
  have hTauout : ∀ z ∈ N',tauD (canonicalMatrix N' L' B' z) ≤ P.card := by
    intro z hz
    rw [←(hInv z).1]
    have hh : tauD (fun j k => divExpAlong n N' (Dn j) (B'.get k) z) ≤ PQ.card := hTau' z hz
    simpa only [PQ,Finset.card_map] using hh
  have hNuout : ∀ z ∈ N',tauD (canonicalMatrix N' L' B' z)=P.card →
      nuOne (canonicalMatrix N' L' B' z)=0 := by
    have hnuQ : ∀ y ∈ NQ,tauD (canonicalMatrix NQ L B y)=PQ.card →
        nuOne (canonicalMatrix NQ L B y)=0 := by simpa only [PQ,Finset.card_map] using hNu
    have hnuNext := hNu' hnuQ
    change ∀ z ∈ N',tauD (fun j k => divExpAlong n N' (Dn j) (B'.get k) z)=PQ.card →
      nuOne (fun j k => divExpAlong n N' (Dn j) (B'.get k) z)=0 at hnuNext
    intro z hz ht
    rw [←(hInv z).2]
    apply hnuNext z hz
    simpa only [(hInv z).1,PQ,Finset.card_map] using ht
  have hActout : ∀ z ∈ N',∀ i : Fin old.length,
      oldEquiv old T' i ∈ properRows (canonicalMatrix N' L' B' z) →
        i ∈ properRows (canonicalMatrix N old born (T'.proj z)) := by
    intro z hz i hi
    have hzQ : π z ∈ NQ := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hz
    have hi' : e i ∈ properRows (canonicalMatrix NQ L B (π z)) :=
      hSub' z hz ((hRowNext z i).mp hi)
    exact hActivity (π z) hzQ i hi'
  have hRowsout : ∀ i : Fin old.length,
      let d := if i ∈ P then 1 else 0
      IsGeoTestTower (⟨N,born,oldTraceIdeal N old i,d⟩ : MarkedIdeal n X) T' ∧
      IsGeoTestTower (⟨N,born,oldMonomialPart N old born i,d⟩ : MarkedIdeal n X) T' ∧
      IsGeoTestTower (⟨N,born,oldResidualPart N old born i,0⟩ : MarkedIdeal n X) T' ∧
      geoTransformAlong (⟨N,born,oldTraceIdeal N old i,d⟩ : MarkedIdeal n X) T'=
        ⟨N',B',oldTraceIdeal N' L' (oldEquiv old T' i),d⟩ ∧
      geoTransformAlong (⟨N,born,oldMonomialPart N old born i,d⟩ : MarkedIdeal n X) T'=
        ⟨N',B',oldMonomialPart N' L' B' (oldEquiv old T' i),d⟩ ∧
      geoTransformAlong (⟨N,born,oldResidualPart N old born i,0⟩ : MarkedIdeal n X) T'=
        ⟨N',B',oldResidualPart N' L' B' (oldEquiv old T' i),0⟩ := by
    intro i
    dsimp only
    obtain ⟨hIT,hDT,hJT,hIR,hDR,hJR⟩ := hRows i
    have hMark : (if e i ∈ PQ then 1 else 0)=(if i ∈ P then 1 else 0) := by simp [PQ,e]
    have hIA := (hAdmRows (e i)).2.2.1
    have hDA := (hAdmRows (e i)).2.2.2
    simp only [hMark] at hIA hDA
    have hJA : (⟨NQ,B,oldResidualPart NQ L B (e i),0⟩ : MarkedIdeal n Y).IsAdmissibleCentre C := by
      refine ⟨hπ.1,?_,hCB⟩
      change C ⊆ cosupport n NQ (oldResidualPart NQ L B (e i)) 0
      have hcJ := (actual_old_parts_geometry hn hN hE hTr hDense (e i)).2.2.1
      rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcJ hg)]
      exact hCN
    have hItest : IsGeoTestTower (⟨N,born,oldTraceIdeal N old i,if i ∈ P then 1 else 0⟩ :
        MarkedIdeal n X) T' := ⟨hIT,by rw [hIR];exact hIA⟩
    have hDtest : IsGeoTestTower (⟨N,born,oldMonomialPart N old born i,if i ∈ P then 1 else 0⟩ :
        MarkedIdeal n X) T' := ⟨hDT,by rw [hDR];exact hDA⟩
    have hJtest : IsGeoTestTower (⟨N,born,oldResidualPart N old born i,0⟩ :
        MarkedIdeal n X) T' := ⟨hJT,by rw [hJR];exact hJA⟩
    obtain ⟨hI,hD,hJ,_hFactor,_hRest⟩ := hParts' (e i)
    simp only [hMark] at hI hD
    have hII : (geoTransformAlong (⟨N,born,oldTraceIdeal N old i,if i ∈ P then 1 else 0⟩ :
        MarkedIdeal n X) T').ideal=oldTraceIdeal N' L' (oldEquiv old T' i) := by
      change ((geoTransformAlong (⟨N,born,oldTraceIdeal N old i,if i ∈ P then 1 else 0⟩ :
        MarkedIdeal n X) T).geoTransform C π).ideal=_
      rw [hIR]
      change _=restrictOn n N' (vanishingIdeal (n := n) (L'.get (oldEquiv old T' i)))
      rw [hGetNext i]
      exact hI
    have hDD : (geoTransformAlong (⟨N,born,oldMonomialPart N old born i,if i ∈ P then 1 else 0⟩ :
        MarkedIdeal n X) T').ideal=oldMonomialPart N' L' B' (oldEquiv old T' i) := by
      change ((geoTransformAlong (⟨N,born,oldMonomialPart N old born i,if i ∈ P then 1 else 0⟩ :
        MarkedIdeal n X) T).geoTransform C π).ideal=_
      rw [hDR]
      rw [hDn i]
      exact hD.symm
    have hJJ : (geoTransformAlong (⟨N,born,oldResidualPart N old born i,0⟩ :
        MarkedIdeal n X) T').ideal=oldResidualPart N' L' B' (oldEquiv old T' i) := by
      change ((geoTransformAlong (⟨N,born,oldResidualPart N old born i,0⟩ :
        MarkedIdeal n X) T).geoTransform C π).ideal=_
      rw [hJR,HironakaSharpOriginalFirstMemberExceptionalFactor.geoTransform_zeroMark_ideal_eq_restricted_total _ rfl]
      have hJT := hJ.symm
      unfold HironakaSharpActualChronologicalStrictStep.nextTotalMarked at hJT
      rw [HironakaSharpOriginalFirstMemberExceptionalFactor.geoTransform_zeroMark_ideal_eq_restricted_total _ rfl] at hJT
      change _=nonmonomialPartAlong n N'
        (restrictOn n N' (vanishingIdeal (n := n) (L'.get (oldEquiv old T' i)))) B'
      rw [hGetNext i]
      exact hJT
    refine ⟨hItest,hDtest,hJtest,?_,?_,?_⟩
    · rw [row_full_record,hII]
    · rw [row_full_record,hDD]
    · rw [row_full_record,hJJ]
  change currentStateData N old born P T' ⟨L',oldEquiv old T'⟩
  dsimp only [currentStateData]
  refine ⟨hSumout,hNout,hEout,hTrout,hDenseout,hOrdout,hPrepout,hTauout,hActout,hNuout,
    ?_,?_,?_,?_,hFull',hSharp',hRowsout⟩
  · change Mout.IsWellFormed
    rw [hModel]
    exact hWF'
  · change ∀ z ∈ N',IsNonzeroAlongAt N' Mout.ideal z
    rw [hModel]
    exact hNZ'
  · change IsMonomialAlong n N' Mout.ideal B'
    rw [hModel]
    exact hMono'
  · change Mout.cosupp={z | z ∈ N' ∧
      P.map (oldEquiv old T').toEmbedding ⊆ properRows (canonicalMatrix N' L' B' z)}
    change Mn.cosupp={z | z ∈ N' ∧
      PQ ⊆ properRows (fun j k => divExpAlong n N' (Dn j) (B'.get k) z)} at hCos'
    rw [hModel,hCos']
    ext z
    exact and_congr_right (fun _ => (hMaskNext z).symm)

private theorem currentState_segment (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty)
    (hTau : ∀ x ∈ N,tauD (canonicalMatrix N old born x) ≤ P.card)
    (hNu : ∀ x ∈ N,tauD (canonicalMatrix N old born x)=P.card →
      nuOne (canonicalMatrix N old born x)=0)
    (hWF : (maskMarked N old born P).IsWellFormed)
    (hNZ : ∀ x ∈ N,IsNonzeroAlongAt N (maskMarked N old born P).ideal x)
    (hMono : IsMonomialAlong n N (maskMarked N old born P).ideal born)
    (hCos : (maskMarked N old born P).cosupp=
      {x | x ∈ N ∧ P ⊆ properRows (canonicalMatrix N old born x)}) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      ResolutionDriver.IsCanonicalSegment (maskMarked N old born P)
        (fun {Y} Q => MonomialStepAlong.towerInvAlong (maskMarked N old born P) (Y := Y) Q) T →
      IsGeoTestTower (maskMarked N old born P) T → currentState N old born P T
  | _,.refl,_hS,_hT => currentState_refl hN hE hTr hdense hOrd hPrepared P
      hTau hNu hWF hNZ hMono hCos
  | _,.step T C π hπ,hS,hT => by
      have hPrev := currentState_segment hn hN hE hTr hdense hOrd hPrepared P hP
        hTau hNu hWF hNZ hMono hCos T hS.1 hT.1
      exact currentState_step hn hE P hP T hPrev C π hπ hS.2.2

theorem exists_prepared_zero_mask_same_gamma_history (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty) :
    let I := oldTraceIdeal N old
    let D := oldMonomialPart N old born
    let J := oldResidualPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let Sigma : GermIdeal n X := ⟨fun x g =>
      IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩
    let M : MarkedIdeal n X := ⟨N,born,Sigma,1⟩
    let d : Fin old.length → ℕ := fun i => if i ∈ P then 1 else 0
    let MI := fun i => (⟨N,born,I i,d i⟩ : MarkedIdeal n X)
    let MD := fun i => (⟨N,born,D i,d i⟩ : MarkedIdeal n X)
    let RJ := fun i => (⟨N,born,J i,0⟩ : MarkedIdeal n X)
    (∀ x ∈ N,tauD (A x) ≤ P.card) →
    (∀ x ∈ N,tauD (A x)=P.card → nuOne (A x)=0) →
    IsCompact M.cosupp →
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      ResolutionDriver.IsCanonicalSegment M
        (fun {Y} Q => MonomialStepAlong.towerInvAlong M (Y := Y) Q) T ∧
      IsGeoResolution M T ∧
      IsGeoTestTower (geometricTemplate N born) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T ∧
      CurrentSharpCentres N (old ++ born) T ∧
      (∀ i : Fin old.length,
        IsGeoTestTower (MI i) T ∧ IsGeoTestTower (MD i) T ∧ IsGeoTestTower (RJ i) T) ∧
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head T k
        let NQ := strictAlong Q N
        let oldQ := old.map (strictAlong Q)
        let bornQ := (geoTransformAlong (geometricTemplate N born) Q).E
        let eQ : Fin old.length ≃ Fin oldQ.length := finCongr (by simp [oldQ])
        let PQ := P.map eQ.toEmbedding
        let IQ := oldTraceIdeal NQ oldQ
        let DQ := oldMonomialPart NQ oldQ bornQ
        let JQ := oldResidualPart NQ oldQ bornQ
        let AQ : (BlowupTowerSplit.split T k).1 → Fin oldQ.length → Fin bornQ.length → ℕ :=
          fun z i j => divExpAlong n NQ (DQ i) (bornQ.get j) z
        let SigmaQ : GermIdeal n (BlowupTowerSplit.split T k).1 := ⟨fun z g =>
          IsInSpanAt (n := n) (fun f => ∃ i ∈ PQ,(DQ i).mem z f) z g⟩
        let MQ : MarkedIdeal n (BlowupTowerSplit.split T k).1 := ⟨NQ,bornQ,SigmaQ,1⟩
        geoTransformAlong M Q=MQ ∧
        IsClosedSubmanifold n NQ ∧ IsSNCDivisor n (oldQ ++ bornQ) ∧
        IsTransverse n NQ bornQ ∧
        NQ ⊆ closure (NQ \ ⋃ H ∈ oldQ ++ bornQ,H) ∧
        (∀ z ∈ NQ,∀ i,ordinaryTraceOrder NQ (JQ i) z ≤ 1) ∧
        (∀ z ∈ NQ,IsPreparedResidualSNCAt NQ oldQ bornQ z) ∧
        (∀ z ∈ NQ,tauD (AQ z) ≤ P.card) ∧
        (∀ z ∈ NQ,∀ i : Fin old.length,
          eQ i ∈ properRows (AQ z) → i ∈ properRows (A (Q.proj z))) ∧
        (∀ z ∈ NQ,tauD (AQ z)=P.card → nuOne (AQ z)=0) ∧
        MQ.IsWellFormed ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ SigmaQ z) ∧
        IsMonomialAlong n NQ SigmaQ bornQ ∧ IsCompact MQ.cosupp ∧
        MQ.cosupp={z | z ∈ NQ ∧ PQ ⊆ properRows (AQ z)} ∧
        ∀ i : Fin old.length,
          (geoTransformAlong (MI i) Q).ideal=IQ (eQ i) ∧
          (geoTransformAlong (MD i) Q).ideal=DQ (eQ i) ∧
          (geoTransformAlong (RJ i) Q).ideal=JQ (eQ i) ∧
          IQ (eQ i)=RestrictedIdealExtension.restrictOn n NQ
            ((DQ (eQ i)).mul (JQ (eQ i))) ∧
          (IQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (IQ (eQ i)) z) ∧
          (DQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (DQ (eQ i)) z) ∧
          IsMonomialAlong n NQ (DQ (eQ i)) bornQ ∧
          (JQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (JQ (eQ i)) z)) ∧
      let NT := strictAlong T N
      let BT := (geoTransformAlong (geometricTemplate N born) T).E
      let AT : Y → Fin old.length → Fin BT.length → ℕ := fun z i j =>
        divExpAlong n NT
          (monomialPartAlong n NT
            (restrictOn n NT (vanishingIdeal (n := n) (strictAlong T (old.get i)))) BT)
          (BT.get j) z
      ∀ z ∈ NT,¬P ⊆ properRows (AT z) := by
  classical
  dsimp only
  intro hTau hNu hK
  let M := maskMarked N old born P
  -- The sole selection of a resolving history occurs here.
  have hNative := HironakaG4ZeroResidualMonomialSum.actual_zero_residual_mask_sum_monomial
    hn hN hE hTr hdense P hP hTau hNu hK
  obtain ⟨hc,hNZ,hMono,hWF,hCos,_hSourceRows,_hSourceCentre,_hSourceWindows,
    Y,T,hSegment,hResolution⟩ := hNative
  have hEnd := currentState_segment hn hN hE hTr hdense hOrd hPrepared P hP
    hTau hNu hWF hNZ hMono hCos T hSegment hResolution.1
  let NT := strictAlong T N
  let LT := old.map (strictAlong T)
  let BT := (geoTransformAlong (geometricTemplate N born) T).E
  let eT := oldEquiv old T
  change currentStateData N old born P T ⟨LT,eT⟩ at hEnd
  dsimp only [currentStateData] at hEnd
  obtain ⟨hSumT,_hNT,_hET,_hTrT,_hDenseT,_hOrdT,_hPrepT,_hTauT,_hActT,_hNuT,
    _hWFT,_hNZT,_hMonoT,hCosT,hFullT,hSharpT,hRowsT⟩ := hEnd
  have hBornT : IsGeoTestTower (geometricTemplate N born) T :=
    actual_original_test_history_template M hWF T hResolution.1
  refine ⟨Y,T,hSegment,hResolution,hBornT,hFullT,hSharpT,?_,?_,?_⟩
  · intro i
    exact ⟨(hRowsT i).1,(hRowsT i).2.1,(hRowsT i).2.2.1⟩
  · intro k
    let Q := BlowupTowerSplit.head T k
    let NQ := strictAlong Q N
    let LQ := old.map (strictAlong Q)
    let BQ := (geoTransformAlong (geometricTemplate N born) Q).E
    let eQ := oldEquiv old Q
    have hTestQ : IsGeoTestTower M Q :=
      ((BlowupTowerSplit.isGeoTestTower_iff_head_tail M T k).mp hResolution.1).1
    have hStateQ := currentState_segment hn hN hE hTr hdense hOrd hPrepared P hP
      hTau hNu hWF hNZ hMono hCos Q (segment_head M T hSegment k) hTestQ
    change currentStateData N old born P Q ⟨LQ,eQ⟩ at hStateQ
    dsimp only [currentStateData] at hStateQ
    obtain ⟨hSumQ,hNQ,hEQ,hTrQ,hDenseQ,hOrdQ,hPrepQ,hTauQ,hActQ,hNuQ,
      hWFQ,hNZQ,hMonoQ,hCosQ,_hFullQ,_hSharpQ,hRowsQ⟩ := hStateQ
    have hKQ : IsCompact (maskMarked NQ LQ BQ (P.map eQ.toEmbedding)).cosupp := by
      rw [←hSumQ]
      exact MonomialCaseLocal.isCompact_cosupp_geoTransformAlong hN hc hK Q hTestQ
    refine ⟨hSumQ,hNQ,hEQ,hTrQ,hDenseQ,hOrdQ,hPrepQ,hTauQ,hActQ,hNuQ,
      hWFQ,hNZQ,hMonoQ,hKQ,hCosQ,?_⟩
    intro i
    obtain ⟨_hIT,_hDT,_hJT,hIR,hDR,hJR⟩ := hRowsQ i
    obtain ⟨hcI,hnzI,hcJ,hnzJ,hcD,hnzD,hmD,hFactor⟩ :=
      actual_old_parts_geometry hn hNQ hEQ hTrQ hDenseQ (eQ i)
    exact ⟨congrArg (fun R : MarkedIdeal n _ => R.ideal) hIR,
      congrArg (fun R : MarkedIdeal n _ => R.ideal) hDR,
      congrArg (fun R : MarkedIdeal n _ => R.ideal) hJR,
      hFactor,hcI,hnzI,hcD,hnzD,hmD,hcJ,hnzJ⟩
  · intro z hz hAll
    have hMapped : P.map eT.toEmbedding ⊆ properRows (canonicalMatrix NT LT BT z) := by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change 0 < ∑ b : Fin BT.length,
        divExpAlong n NT (oldMonomialPart NT LT BT (eT i)) (BT.get b) z
      rw [monomial_oldEquiv NT old BT T i]
      exact (Finset.mem_filter.mp (hAll hi)).2
    have hHit : z ∈ (geoTransformAlong M T).cosupp := by
      rw [hSumT,hCosT]
      exact ⟨hz,hMapped⟩
    have hEmpty : (geoTransformAlong M T).cosupp=∅ := hResolution.2
    rw [hEmpty] at hHit
    exact hHit


/-- A shaped source Gamma bound yields the same sharp full-boundary history
on a noncompact source, with no future selector hypothesis. -/
theorem exists_prepared_zero_mask_bounded_noncompact_history (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty) :
    let I := oldTraceIdeal N old
    let D := oldMonomialPart N old born
    let J := oldResidualPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let Sigma : GermIdeal n X := ⟨fun x g =>
      IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩
    let M : MarkedIdeal n X := ⟨N,born,Sigma,1⟩
    let d : Fin old.length → ℕ := fun i => if i ∈ P then 1 else 0
    let MI := fun i => (⟨N,born,I i,d i⟩ : MarkedIdeal n X)
    let MD := fun i => (⟨N,born,D i,d i⟩ : MarkedIdeal n X)
    let RJ := fun i => (⟨N,born,J i,0⟩ : MarkedIdeal n X)
    (∀ x ∈ N,tauD (A x) ≤ P.card) →
    (∀ x ∈ N,tauD (A x)=P.card → nuOne (A x)=0) →
    (v : MonomialInvariant.Val) → (ofLex v).1 = n - 1 →
    (∀ x ∈ M.cosupp, gammaAlong n M.N M.ideal M.E M.d x ≤ (v : WithBot MonomialInvariant.Val)) →
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      ResolutionDriver.IsCanonicalSegment M
        (fun {Y} Q => MonomialStepAlong.towerInvAlong M (Y := Y) Q) T ∧
      IsGeoResolution M T ∧
      IsGeoTestTower (geometricTemplate N born) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T ∧
      CurrentSharpCentres N (old ++ born) T ∧
      (∀ i : Fin old.length,
        IsGeoTestTower (MI i) T ∧ IsGeoTestTower (MD i) T ∧ IsGeoTestTower (RJ i) T) ∧
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head T k
        let NQ := strictAlong Q N
        let oldQ := old.map (strictAlong Q)
        let bornQ := (geoTransformAlong (geometricTemplate N born) Q).E
        let eQ : Fin old.length ≃ Fin oldQ.length := finCongr (by simp [oldQ])
        let PQ := P.map eQ.toEmbedding
        let IQ := oldTraceIdeal NQ oldQ
        let DQ := oldMonomialPart NQ oldQ bornQ
        let JQ := oldResidualPart NQ oldQ bornQ
        let AQ : (BlowupTowerSplit.split T k).1 → Fin oldQ.length → Fin bornQ.length → ℕ :=
          fun z i j => divExpAlong n NQ (DQ i) (bornQ.get j) z
        let SigmaQ : GermIdeal n (BlowupTowerSplit.split T k).1 := ⟨fun z g =>
          IsInSpanAt (n := n) (fun f => ∃ i ∈ PQ,(DQ i).mem z f) z g⟩
        let MQ : MarkedIdeal n (BlowupTowerSplit.split T k).1 := ⟨NQ,bornQ,SigmaQ,1⟩
        geoTransformAlong M Q=MQ ∧
        IsClosedSubmanifold n NQ ∧ IsSNCDivisor n (oldQ ++ bornQ) ∧
        IsTransverse n NQ bornQ ∧
        NQ ⊆ closure (NQ \ ⋃ H ∈ oldQ ++ bornQ,H) ∧
        (∀ z ∈ NQ,∀ i,ordinaryTraceOrder NQ (JQ i) z ≤ 1) ∧
        (∀ z ∈ NQ,IsPreparedResidualSNCAt NQ oldQ bornQ z) ∧
        (∀ z ∈ NQ,tauD (AQ z) ≤ P.card) ∧
        (∀ z ∈ NQ,∀ i : Fin old.length,
          eQ i ∈ properRows (AQ z) → i ∈ properRows (A (Q.proj z))) ∧
        (∀ z ∈ NQ,tauD (AQ z)=P.card → nuOne (AQ z)=0) ∧
        MQ.IsWellFormed ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ SigmaQ z) ∧
        IsMonomialAlong n NQ SigmaQ bornQ ∧
        MQ.cosupp={z | z ∈ NQ ∧ PQ ⊆ properRows (AQ z)} ∧
        ∀ i : Fin old.length,
          (geoTransformAlong (MI i) Q).ideal=IQ (eQ i) ∧
          (geoTransformAlong (MD i) Q).ideal=DQ (eQ i) ∧
          (geoTransformAlong (RJ i) Q).ideal=JQ (eQ i) ∧
          IQ (eQ i)=RestrictedIdealExtension.restrictOn n NQ
            ((DQ (eQ i)).mul (JQ (eQ i))) ∧
          (IQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (IQ (eQ i)) z) ∧
          (DQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (DQ (eQ i)) z) ∧
          IsMonomialAlong n NQ (DQ (eQ i)) bornQ ∧
          (JQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (JQ (eQ i)) z)) ∧
      let NT := strictAlong T N
      let BT := (geoTransformAlong (geometricTemplate N born) T).E
      let AT : Y → Fin old.length → Fin BT.length → ℕ := fun z i j =>
        divExpAlong n NT
          (monomialPartAlong n NT
            (restrictOn n NT (vanishingIdeal (n := n) (strictAlong T (old.get i)))) BT)
          (BT.get j) z
      ∀ z ∈ NT,¬P ⊆ properRows (AT z) := by
  classical
  dsimp only
  intro hTau hNu v hFirst hBound
  let M := maskMarked N old born P
  -- The sole selection of a resolving history occurs here.
  have hNative := HironakaG4ZeroResidualMonomialSum.actual_zero_residual_mask_sum_noncompact_of_bound
    hn hN hE hTr hdense P hP hTau hNu v hFirst hBound
  obtain ⟨hc,hNZ,hMono,hWF,hCos,_hSourceRows,_hSourceCentre,_hSourceWindows,
    Y,T,hSegment,hResolution⟩ := hNative
  have hEnd := currentState_segment hn hN hE hTr hdense hOrd hPrepared P hP
    hTau hNu hWF hNZ hMono hCos T hSegment hResolution.1
  let NT := strictAlong T N
  let LT := old.map (strictAlong T)
  let BT := (geoTransformAlong (geometricTemplate N born) T).E
  let eT := oldEquiv old T
  change currentStateData N old born P T ⟨LT,eT⟩ at hEnd
  dsimp only [currentStateData] at hEnd
  obtain ⟨hSumT,_hNT,_hET,_hTrT,_hDenseT,_hOrdT,_hPrepT,_hTauT,_hActT,_hNuT,
    _hWFT,_hNZT,_hMonoT,hCosT,hFullT,hSharpT,hRowsT⟩ := hEnd
  have hBornT : IsGeoTestTower (geometricTemplate N born) T :=
    actual_original_test_history_template M hWF T hResolution.1
  refine ⟨Y,T,hSegment,hResolution,hBornT,hFullT,hSharpT,?_,?_,?_⟩
  · intro i
    exact ⟨(hRowsT i).1,(hRowsT i).2.1,(hRowsT i).2.2.1⟩
  · intro k
    let Q := BlowupTowerSplit.head T k
    let NQ := strictAlong Q N
    let LQ := old.map (strictAlong Q)
    let BQ := (geoTransformAlong (geometricTemplate N born) Q).E
    let eQ := oldEquiv old Q
    have hTestQ : IsGeoTestTower M Q :=
      ((BlowupTowerSplit.isGeoTestTower_iff_head_tail M T k).mp hResolution.1).1
    have hStateQ := currentState_segment hn hN hE hTr hdense hOrd hPrepared P hP
      hTau hNu hWF hNZ hMono hCos Q (segment_head M T hSegment k) hTestQ
    change currentStateData N old born P Q ⟨LQ,eQ⟩ at hStateQ
    dsimp only [currentStateData] at hStateQ
    obtain ⟨hSumQ,hNQ,hEQ,hTrQ,hDenseQ,hOrdQ,hPrepQ,hTauQ,hActQ,hNuQ,
      hWFQ,hNZQ,hMonoQ,hCosQ,_hFullQ,_hSharpQ,hRowsQ⟩ := hStateQ
    refine ⟨hSumQ,hNQ,hEQ,hTrQ,hDenseQ,hOrdQ,hPrepQ,hTauQ,hActQ,hNuQ,
      hWFQ,hNZQ,hMonoQ,hCosQ,?_⟩
    intro i
    obtain ⟨_hIT,_hDT,_hJT,hIR,hDR,hJR⟩ := hRowsQ i
    obtain ⟨hcI,hnzI,hcJ,hnzJ,hcD,hnzD,hmD,hFactor⟩ :=
      actual_old_parts_geometry hn hNQ hEQ hTrQ hDenseQ (eQ i)
    exact ⟨congrArg (fun R : MarkedIdeal n _ => R.ideal) hIR,
      congrArg (fun R : MarkedIdeal n _ => R.ideal) hDR,
      congrArg (fun R : MarkedIdeal n _ => R.ideal) hJR,
      hFactor,hcI,hnzI,hcD,hnzD,hmD,hcJ,hnzJ⟩
  · intro z hz hAll
    have hMapped : P.map eT.toEmbedding ⊆ properRows (canonicalMatrix NT LT BT z) := by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change 0 < ∑ b : Fin BT.length,
        divExpAlong n NT (oldMonomialPart NT LT BT (eT i)) (BT.get b) z
      rw [monomial_oldEquiv NT old BT T i]
      exact (Finset.mem_filter.mp (hAll hi)).2
    have hHit : z ∈ (geoTransformAlong M T).cosupp := by
      rw [hSumT,hCosT]
      exact ⟨hz,hMapped⟩
    have hEmpty : (geoTransformAlong M T).cosupp=∅ := hResolution.2
    rw [hEmpty] at hHit
    exact hHit


/-- Uniform incident exponents imply the shaped initial Gamma bound. -/
theorem exists_prepared_zero_mask_exponent_bounded_history (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty) :
    let I := oldTraceIdeal N old
    let D := oldMonomialPart N old born
    let J := oldResidualPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let Sigma : GermIdeal n X := ⟨fun x g =>
      IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩
    let M : MarkedIdeal n X := ⟨N,born,Sigma,1⟩
    let d : Fin old.length → ℕ := fun i => if i ∈ P then 1 else 0
    let MI := fun i => (⟨N,born,I i,d i⟩ : MarkedIdeal n X)
    let MD := fun i => (⟨N,born,D i,d i⟩ : MarkedIdeal n X)
    let RJ := fun i => (⟨N,born,J i,0⟩ : MarkedIdeal n X)
    (∀ x ∈ N,tauD (A x) ≤ P.card) →
    (∀ x ∈ N,tauD (A x)=P.card → nuOne (A x)=0) →
    (B : ℕ) →
    (∀ x ∈ M.cosupp,∀ i : Fin M.E.length,x ∈ M.E.get i →
      divExpAlong n M.N M.ideal (M.E.get i) x ≤ B) →
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      ResolutionDriver.IsCanonicalSegment M
        (fun {Y} Q => MonomialStepAlong.towerInvAlong M (Y := Y) Q) T ∧
      IsGeoResolution M T ∧
      IsGeoTestTower (geometricTemplate N born) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T ∧
      CurrentSharpCentres N (old ++ born) T ∧
      (∀ i : Fin old.length,
        IsGeoTestTower (MI i) T ∧ IsGeoTestTower (MD i) T ∧ IsGeoTestTower (RJ i) T) ∧
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head T k
        let NQ := strictAlong Q N
        let oldQ := old.map (strictAlong Q)
        let bornQ := (geoTransformAlong (geometricTemplate N born) Q).E
        let eQ : Fin old.length ≃ Fin oldQ.length := finCongr (by simp [oldQ])
        let PQ := P.map eQ.toEmbedding
        let IQ := oldTraceIdeal NQ oldQ
        let DQ := oldMonomialPart NQ oldQ bornQ
        let JQ := oldResidualPart NQ oldQ bornQ
        let AQ : (BlowupTowerSplit.split T k).1 → Fin oldQ.length → Fin bornQ.length → ℕ :=
          fun z i j => divExpAlong n NQ (DQ i) (bornQ.get j) z
        let SigmaQ : GermIdeal n (BlowupTowerSplit.split T k).1 := ⟨fun z g =>
          IsInSpanAt (n := n) (fun f => ∃ i ∈ PQ,(DQ i).mem z f) z g⟩
        let MQ : MarkedIdeal n (BlowupTowerSplit.split T k).1 := ⟨NQ,bornQ,SigmaQ,1⟩
        geoTransformAlong M Q=MQ ∧
        IsClosedSubmanifold n NQ ∧ IsSNCDivisor n (oldQ ++ bornQ) ∧
        IsTransverse n NQ bornQ ∧
        NQ ⊆ closure (NQ \ ⋃ H ∈ oldQ ++ bornQ,H) ∧
        (∀ z ∈ NQ,∀ i,ordinaryTraceOrder NQ (JQ i) z ≤ 1) ∧
        (∀ z ∈ NQ,IsPreparedResidualSNCAt NQ oldQ bornQ z) ∧
        (∀ z ∈ NQ,tauD (AQ z) ≤ P.card) ∧
        (∀ z ∈ NQ,∀ i : Fin old.length,
          eQ i ∈ properRows (AQ z) → i ∈ properRows (A (Q.proj z))) ∧
        (∀ z ∈ NQ,tauD (AQ z)=P.card → nuOne (AQ z)=0) ∧
        MQ.IsWellFormed ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ SigmaQ z) ∧
        IsMonomialAlong n NQ SigmaQ bornQ ∧
        MQ.cosupp={z | z ∈ NQ ∧ PQ ⊆ properRows (AQ z)} ∧
        ∀ i : Fin old.length,
          (geoTransformAlong (MI i) Q).ideal=IQ (eQ i) ∧
          (geoTransformAlong (MD i) Q).ideal=DQ (eQ i) ∧
          (geoTransformAlong (RJ i) Q).ideal=JQ (eQ i) ∧
          IQ (eQ i)=RestrictedIdealExtension.restrictOn n NQ
            ((DQ (eQ i)).mul (JQ (eQ i))) ∧
          (IQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (IQ (eQ i)) z) ∧
          (DQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (DQ (eQ i)) z) ∧
          IsMonomialAlong n NQ (DQ (eQ i)) bornQ ∧
          (JQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (JQ (eQ i)) z)) ∧
      let NT := strictAlong T N
      let BT := (geoTransformAlong (geometricTemplate N born) T).E
      let AT : Y → Fin old.length → Fin BT.length → ℕ := fun z i j =>
        divExpAlong n NT
          (monomialPartAlong n NT
            (restrictOn n NT (vanishingIdeal (n := n) (strictAlong T (old.get i)))) BT)
          (BT.get j) z
      ∀ z ∈ NT,¬P ⊆ properRows (AT z) := by
  classical
  dsimp only
  intro hTau hNu B hExp
  obtain ⟨_hc,hNZ,hMono,hWF,_hCos,_hRows,_hCentre,_hLocal⟩ :=
    HironakaG4ZeroResidualMonomialSum.actual_zero_residual_mask_sum_geometry
      hn hN hE hTr hdense P hP hTau hNu
  obtain ⟨v,hFirst,hBound⟩ := HironakaMarkOneGammaBoundedMaxima.markOne_gamma_bound_of_incident_exponents
    hn _ hWF hNZ hMono rfl B hExp
  exact exists_prepared_zero_mask_bounded_noncompact_history
    hn hN hE hTr hdense hOrd hPrepared P hP hTau hNu v hFirst hBound

/-- At an actual prepared canonical step, a uniform bound for all rows and
born columns propagates to the next literal old-plus-born matrix. -/
private theorem currentState_step_uniform_bound (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (P : Finset (Fin old.length)) (hP : P.Nonempty)
    (T : BlowupTower X Y) (hQ : currentState N old born P T) :
    let NQ := strictAlong T N
    let L := old.map (strictAlong T)
    let B := (geoTransformAlong (geometricTemplate N born) T).E
    let MQ := maskMarked N old born P
    let C := maxLocusA (geoTransformAlong MQ T)
    ∀ bound, (∀ z ∈ NQ,∀ i j,canonicalMatrix NQ L B z i j ≤ bound) →
    ∀ (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      let T' : BlowupTower X Z := .step T C π hπ
      let NQ' := strictAlong T' N
      let L' := old.map (strictAlong T')
      let B' := (geoTransformAlong (geometricTemplate N born) T').E
      ∀ z ∈ NQ',∀ i j,canonicalMatrix NQ' L' B' z i j ≤ max bound (B.length * bound) := by
  classical
  dsimp only
  let NQ := strictAlong T N
  let L := old.map (strictAlong T)
  let B := (geoTransformAlong (geometricTemplate N born) T).E
  let e := oldEquiv old T
  let PQ := P.map e.toEmbedding
  let MQ := maskMarked NQ L B PQ
  let C := maxLocusA (geoTransformAlong (maskMarked N old born P) T)
  change currentStateData N old born P T ⟨L,e⟩ at hQ
  dsimp only [currentStateData] at hQ
  obtain ⟨hSum,hN,hE,hTr,hDense,hOrd,hPrep,hTau,_hActivity,_hNu,_hWF,_hNZ,hMono,
    _hCos,_hFull,_hSharp,_hRows⟩ := hQ
  intro bound hBound Z π hπ
  have hPQ : PQ.Nonempty := hP.map
  have hTauQ : ∀ y ∈ NQ,tauD (canonicalMatrix NQ L B y) ≤ PQ.card := by
    simpa only [PQ,Finset.card_map] using hTau
  have hC : C=maxLocusA MQ := congrArg maxLocusA hSum
  have hπ' : IsBlowupAlong n (maxLocusA MQ) π := by rw [←hC]; exact hπ
  have hStep := HironakaG4ZeroMaskGammaStep.prepared_zero_mask_gamma_step_uniform_rows
    (N := NQ) (old := L) (born := B) hn hN hE hTr hDense hOrd hPrep PQ hPQ hTauQ hMono
    bound hBound Z π hπ'
  let T' : BlowupTower X Z := .step T C π hπ
  let NQ' := strictAlong T' N
  let L' := old.map (strictAlong T')
  let B' := (geoTransformAlong (geometricTemplate N born) T').E
  have hN' : NQ'=geoStrictTransform π C NQ := by simp [NQ',T',NQ,strictAlong_step]
  have hL' : L'=L.map (geoStrictTransform π C) := by
    simp [L',T',L,strictAlong_step,List.map_map]
  have hB' : B'=B.map (geoStrictTransform π C) ++ [π ⁻¹' C] := by
    simp [B',T',B,geoTransformAlong]
  intro z hz
  change z ∈ NQ' at hz
  change ∀ i : Fin L'.length,∀ j : Fin B'.length,
    canonicalMatrix NQ' L' B' z i j ≤ max bound (B.length * bound)
  rw [hN'] at hz
  rw [hN',hL',hB']
  rw [hC] at hz ⊢
  intro i j
  let i0 : Fin L.length := ⟨i.val,by simpa using i.isLt⟩
  have hGet : (L.map (geoStrictTransform π (maxLocusA MQ))).get i =
      geoStrictTransform π (maxLocusA MQ) (L.get i0) := by
    simp [i0,List.get_eq_getElem]
  change divExpAlong n (geoStrictTransform π (maxLocusA MQ) NQ)
    (monomialPartAlong n (geoStrictTransform π (maxLocusA MQ) NQ)
      (restrictOn n (geoStrictTransform π (maxLocusA MQ) NQ)
        (vanishingIdeal ((L.map (geoStrictTransform π (maxLocusA MQ))).get i)))
      (B.map (geoStrictTransform π (maxLocusA MQ)) ++ [π ⁻¹' maxLocusA MQ]))
    ((B.map (geoStrictTransform π (maxLocusA MQ)) ++ [π ⁻¹' maxLocusA MQ]).get j) z ≤ _
  rw [hGet]
  exact hStep z hz i0 j

/-- Uniform row bounds persist along every actual canonical zero-mask prefix. -/
private theorem canonical_segment_uniform_rows (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty)
    (hTau : ∀ x ∈ N,tauD (canonicalMatrix N old born x) ≤ P.card)
    (hNu : ∀ x ∈ N,tauD (canonicalMatrix N old born x)=P.card →
      nuOne (canonicalMatrix N old born x)=0)
    (hWF : (maskMarked N old born P).IsWellFormed)
    (hNZ : ∀ x ∈ N,IsNonzeroAlongAt N (maskMarked N old born P).ideal x)
    (hMono : IsMonomialAlong n N (maskMarked N old born P).ideal born)
    (hCos : (maskMarked N old born P).cosupp=
      {x | x ∈ N ∧ P ⊆ properRows (canonicalMatrix N old born x)})
    (B₀ : ℕ) (hB₀ : ∀ x ∈ N,∀ i j,canonicalMatrix N old born x i j ≤ B₀) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      ResolutionDriver.IsCanonicalSegment (maskMarked N old born P)
        (fun {Y} Q => MonomialStepAlong.towerInvAlong (maskMarked N old born P) (Y := Y) Q) T →
      IsGeoTestTower (maskMarked N old born P) T →
      let NQ := strictAlong T N
      let L := old.map (strictAlong T)
      let B := (geoTransformAlong (geometricTemplate N born) T).E
      ∃ bound,∀ z ∈ NQ,∀ i j,canonicalMatrix NQ L B z i j ≤ bound
  | _,.refl,_hS,_hT => by
      refine ⟨B₀,?_⟩
      dsimp only [strictAlong,geoTransformAlong,geometricTemplate]
      rw [show old.map (fun x => x) = old from List.map_id old]
      exact hB₀
  | _,.step T C π hπ,hS,hT => by
      obtain ⟨bound,hBound⟩ := canonical_segment_uniform_rows hn hN hE hTr hdense hOrd hPrepared
        P hP hTau hNu hWF hNZ hMono hCos B₀ hB₀ T hS.1 hT.1
      have hQ := currentState_segment hn hN hE hTr hdense hOrd hPrepared P hP
        hTau hNu hWF hNZ hMono hCos T hS.1 hT.1
      have hC := hS.2.2
      subst C
      exact ⟨max bound ((geoTransformAlong (geometricTemplate N born) T).E.length * bound),
        currentState_step_uniform_bound hn P hP T hQ bound hBound _ π hπ⟩

/-- A source bound for all old-row/born-column exponents propagates along
every actual canonical zero-mask prefix, with no future bound assumed. -/
theorem canonical_zero_mask_prefix_uniform_rows (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty) :
    let D := oldMonomialPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let I : GermIdeal n X := ⟨fun x g => IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩
    let M : MarkedIdeal n X := ⟨N,born,I,1⟩
    (∀ x ∈ N,tauD (A x) ≤ P.card) →
    (∀ x ∈ N,tauD (A x)=P.card → nuOne (A x)=0) →
    (∃ B₀,∀ x ∈ N,∀ i j,A x i j ≤ B₀) →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      ResolutionDriver.IsCanonicalSegment M
        (fun {Y} Q => MonomialStepAlong.towerInvAlong M (Y := Y) Q) T →
      IsGeoTestTower M T →
      let NQ := strictAlong T N
      let L := old.map (strictAlong T)
      let B := (geoTransformAlong (geometricTemplate N born) T).E
      ∃ bound,∀ z ∈ NQ,∀ i : Fin L.length,∀ j : Fin B.length,
        divExpAlong n NQ (oldMonomialPart NQ L B i) (B.get j) z ≤ bound := by
  dsimp only
  intro hTau hNu hInitial Y T hSeg hTest
  obtain ⟨B₀,hB₀⟩ := hInitial
  obtain ⟨_hc,hNZ,hMono,hWF,hCos,_hRows,_hCentre,_hLocal⟩ :=
    HironakaG4ZeroResidualMonomialSum.actual_zero_residual_mask_sum_geometry
      hn hN hE hTr hdense P hP hTau hNu
  have h := canonical_segment_uniform_rows hn hN hE hTr hdense hOrd hPrepared P hP
    hTau hNu hWF hNZ hMono hCos B₀ hB₀ T hSeg hTest
  simpa only [canonicalMatrix] using h

private theorem currentState_step_rowsChain (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (P : Finset (Fin old.length)) (hP : P.Nonempty)
    (T : BlowupTower X Y) (hQ : currentState N old born P T) :
    let NQ := strictAlong T N
    let L := old.map (strictAlong T)
    let B := (geoTransformAlong (geometricTemplate N born) T).E
    let MQ := maskMarked N old born P
    let C := maxLocusA (geoTransformAlong MQ T)
    (∀ z ∈ NQ,RowsChain (canonicalMatrix NQ L B z)) →
    ∀ (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      let T' : BlowupTower X Z := .step T C π hπ
      let NQ' := strictAlong T' N
      let L' := old.map (strictAlong T')
      let B' := (geoTransformAlong (geometricTemplate N born) T').E
      ∀ z ∈ NQ',RowsChain (canonicalMatrix NQ' L' B' z) := by
  classical
  dsimp only
  let NQ := strictAlong T N
  let L := old.map (strictAlong T)
  let B := (geoTransformAlong (geometricTemplate N born) T).E
  let e := oldEquiv old T
  let PQ := P.map e.toEmbedding
  let MQ := maskMarked NQ L B PQ
  let C := maxLocusA (geoTransformAlong (maskMarked N old born P) T)
  change currentStateData N old born P T ⟨L,e⟩ at hQ
  dsimp only [currentStateData] at hQ
  obtain ⟨hSum,hN,hE,hTr,hDense,hOrd,hPrep,hTau,_hActivity,_hNu,_hWF,_hNZ,hMono,
    _hCos,_hFull,_hSharp,_hRows⟩ := hQ
  intro hChain Z π hπ
  have hPQ : PQ.Nonempty := hP.map
  have hTauQ : ∀ y ∈ NQ,tauD (canonicalMatrix NQ L B y) ≤ PQ.card := by
    simpa only [PQ,Finset.card_map] using hTau
  have hC : C=maxLocusA MQ := congrArg maxLocusA hSum
  have hπ' : IsBlowupAlong n (maxLocusA MQ) π := by rw [←hC]; exact hπ
  have hStep := HironakaG4ZeroMaskGammaStep.prepared_zero_mask_gamma_step_rowsChain
    (N := NQ) (old := L) (born := B) hn hN hE hTr hDense hOrd hPrep PQ hPQ hTauQ hMono
    hChain Z π hπ'
  let T' : BlowupTower X Z := .step T C π hπ
  let NQ' := strictAlong T' N
  let L' := old.map (strictAlong T')
  let B' := (geoTransformAlong (geometricTemplate N born) T').E
  have hN' : NQ'=geoStrictTransform π C NQ := by simp [NQ',T',NQ,strictAlong_step]
  have hL' : L'=L.map (geoStrictTransform π C) := by
    simp [L',T',L,strictAlong_step,List.map_map]
  have hB' : B'=B.map (geoStrictTransform π C) ++ [π ⁻¹' C] := by
    simp [B',T',B,geoTransformAlong]
  intro z hz
  change z ∈ NQ' at hz
  change RowsChain (canonicalMatrix NQ' L' B' z)
  rw [hN'] at hz
  rw [hN',hL',hB']
  rw [hC] at hz ⊢
  let C' := maxLocusA MQ
  let N' := geoStrictTransform π C' NQ
  let Bnext := B.map (geoStrictTransform π C') ++ [π ⁻¹' C']
  let M : Fin L.length → Fin Bnext.length → ℕ := fun i j =>
    divExpAlong n N' (monomialPartAlong n N'
      (restrictOn n N' (vanishingIdeal (geoStrictTransform π C' (L.get i)))) Bnext)
      (Bnext.get j) z
  let e' : Fin (L.map (geoStrictTransform π C')).length ≃ Fin L.length := finCongr (by simp)
  have hM : RowsChain M := hStep z hz
  change RowsChain (canonicalMatrix N' (L.map (geoStrictTransform π C')) Bnext z)
  apply rowsChain_of_row_equiv M _ e' ?_ hM
  intro i j
  simp [canonicalMatrix,oldMonomialPart,oldTraceIdeal,M,e',List.get_eq_getElem]


private theorem canonical_segment_rowsChain (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty)
    (hTau : ∀ x ∈ N,tauD (canonicalMatrix N old born x) ≤ P.card)
    (hNu : ∀ x ∈ N,tauD (canonicalMatrix N old born x)=P.card →
      nuOne (canonicalMatrix N old born x)=0)
    (hWF : (maskMarked N old born P).IsWellFormed)
    (hNZ : ∀ x ∈ N,IsNonzeroAlongAt N (maskMarked N old born P).ideal x)
    (hMono : IsMonomialAlong n N (maskMarked N old born P).ideal born)
    (hCos : (maskMarked N old born P).cosupp=
      {x | x ∈ N ∧ P ⊆ properRows (canonicalMatrix N old born x)})
    (hChain₀ : ∀ x ∈ N,RowsChain (canonicalMatrix N old born x)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      ResolutionDriver.IsCanonicalSegment (maskMarked N old born P)
        (fun {Y} Q => MonomialStepAlong.towerInvAlong (maskMarked N old born P) (Y := Y) Q) T →
      IsGeoTestTower (maskMarked N old born P) T →
      let NQ := strictAlong T N
      let L := old.map (strictAlong T)
      let B := (geoTransformAlong (geometricTemplate N born) T).E
      ∀ z ∈ NQ,RowsChain (canonicalMatrix NQ L B z)
  | _,.refl,_hS,_hT => by
      dsimp only [strictAlong,geoTransformAlong,geometricTemplate]
      rw [show old.map (fun x => x) = old from List.map_id old]
      exact hChain₀
  | _,.step T C π hπ,hS,hT => by
      have hChain := canonical_segment_rowsChain hn hN hE hTr hdense hOrd hPrepared
        P hP hTau hNu hWF hNZ hMono hCos hChain₀ T hS.1 hT.1
      have hQ := currentState_segment hn hN hE hTr hdense hOrd hPrepared P hP
        hTau hNu hWF hNZ hMono hCos T hS.1 hT.1
      have hC := hS.2.2
      subst C
      exact currentState_step_rowsChain hn P hP T hQ hChain _ π hπ



/-- Source row comparability persists along each actual canonical prefix. -/
theorem canonical_zero_mask_prefix_rowsChain (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty) :
    let D := oldMonomialPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let I : GermIdeal n X := ⟨fun x g => IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩
    let M : MarkedIdeal n X := ⟨N,born,I,1⟩
    (∀ x ∈ N,tauD (A x) ≤ P.card) →
    (∀ x ∈ N,RowsChain (A x)) →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      ResolutionDriver.IsCanonicalSegment M
        (fun {Y} Q => MonomialStepAlong.towerInvAlong M (Y := Y) Q) T →
      IsGeoTestTower M T →
      let NQ := strictAlong T N
      let L := old.map (strictAlong T)
      let B := (geoTransformAlong (geometricTemplate N born) T).E
      ∀ z ∈ NQ,RowsChain (fun i : Fin L.length => fun j : Fin B.length =>
        divExpAlong n NQ (oldMonomialPart NQ L B i) (B.get j) z) := by
  dsimp only
  intro hTau hChain Y T hSeg hTest
  have hNu : ∀ x ∈ N,tauD (canonicalMatrix N old born x)=P.card →
      nuOne (canonicalMatrix N old born x)=0 := by
    intro x hx _
    exact nuOne_eq_zero_of_rowsChain _ (hChain x hx)
  obtain ⟨_hc,hNZ,hMono,hWF,hCos,_hRows,_hCentre,_hLocal⟩ :=
    HironakaG4ZeroResidualMonomialSum.actual_zero_residual_mask_sum_geometry
      hn hN hE hTr hdense P hP hTau hNu
  have h := canonical_segment_rowsChain hn hN hE hTr hdense hOrd hPrepared P hP
    hTau hNu hWF hNZ hMono hCos hChain T hSeg hTest
  exact h

end

end Hironaka.HironakaG4ZeroMaskSameGammaHistory
