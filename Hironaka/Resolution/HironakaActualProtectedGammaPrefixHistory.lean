import Hironaka.Resolution.HironakaActualProtectedOtherRowLocalStep
import Hironaka.Resolution.HironakaActualProtectedGammaMaximumWindow
import Hironaka.Resolution.HironakaMarkOneGammaBoundedMaxima
import Hironaka.Resolution.HironakaG4ZeroMaskGammaStep
import Hironaka.Invariant.StepOneEmptyPrefix
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Invariant.DropMembers
import Hironaka.Resolution.HironakaG4CompactWholeMonomialMaskPhase

/-! Actual whole lower canonical I/D/J and protected-slice interpretation
of EVERY GIVEN native singleton Gamma prefix on a current prepared source.
Complete source-first proof: hironaka-actual-protected-gamma-prefix-history.tex.
The ORIGINAL source wrapper derives the ordinary source assumptions separately.
No finite history selection, full lower driver, gluing or global G4-K1 claim.
Reused private lower-state/coordinate/clock proofs carry zero extra credit. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualProtectedGammaPrefixHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedGlueingTower HironakaSharpActualFiniteChronologicalHistory
  HironakaG4RecordedTowerResidualCompatibility HironakaG4CompactWholeMonomialMaskPhase
  HironakaSharpActualOriginalControlledHistory NormalCrossings NormalCrossingsComparison SimultaneousNormalCrossings
  HironakaSharpOriginalProductTraceOrder HironakaSharpActualTraceIncidence
  HironakaSharpActualFirstAmbientStrictExponent HironakaSharpActualMixedCentreWholeStrictTraceGeometry
  HironakaSharpNormalCrossingsOpenLocus HironakaActualCleanupDensityCompactness
  HironakaSharpActualChronologicalStrictStep
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4OriginalSelectedResidualTail
  HironakaG4PreparedCentreCoordinates HironakaSharpActualChronologicalResidualDictionary
  RelativePrincipalizationSpan RestrictedIdealExtension GermIdealOrder
  HironakaCoherentTransformExtension HironakaG4MonomialFamilyInvariant HironakaG4ZeroMaskGammaStep
  BlowupStrictSubmanifold MonomialStepAlong MonomialCaseAlong HironakaMarkOneGammaBoundedMaxima
  HironakaActualProtectedGammaMaximumWindow
  MonomialPartAlong DivisorExponentAlong IdealWeightPowers InvertibleIdealQuotient
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Reused private whole transverse trace argument; zero separate credit. -/
private theorem transverse_trace_reduced (hn : 0 < n) {N H : Set X}
    (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hTr : IsTransverse n N [H]) :
    IsClosedSubmanifold n (N ∩ H) ∧
      restrictOn n N (vanishingIdeal (n := n) H)=vanishingIdeal (n := n) (N ∩ H) := by
  obtain ⟨hc,hnz,_hpr,hOne⟩ := actual_normalized_transverse_member_geometry hn hN hH hTr
  have hd : N ⊆ closure (N \ H) := actual_density_of_nonzero_normalized_vanishing hnz
  have hOrd : ∀ x ∈ N,ordinaryTraceOrder N (restrictOn n N (vanishingIdeal (n := n) H)) x ≤ 1 := by
    intro x hxN
    by_cases hxH : x ∈ H
    · exact (hOne x ⟨hxN,hxH⟩).le
    · have hunit : (restrictOn n N (vanishingIdeal (n := n) H)).mem x 1 := by
        apply le_restrictOn (W := N) (VanishingIdealCoherent.isCoherent_vanishingIdeal
          (MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)))
        refine ⟨holomorphicAt_const 1,?_⟩
        filter_upwards [(hH.1 H (by simp)).isOpen_compl.mem_nhds hxH] with y hy hyH
        exact (hy hyH).elim
      by_contra hgt
      have hcos := (ordinaryTraceOrder_cosupport_iff hN hc hnz hxN 1).mpr (by omega)
      exact one_ne_zero ((vanishesToOrderOn_one_iff hxN (holomorphicAt_const 1)).mp (hcos.2 1 hunit))
  have hd' : N ⊆ closure (N \ ⋃ K ∈ [H],K) := by simpa using hd
  obtain ⟨hS,hWhole,_hTail⟩ := actual_original_selected_residual_tail hn hN hH hd'
    (0 : Fin [H].length) (BlowupTower.refl (X := X)) trivial hOrd
  have hHsmooth := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsmooth
  have hSet : N ∩ (restrictOn n N (vanishingIdeal (n := n) H)).zeroLocus=N ∩ H := by
    ext x
    constructor
    · rintro ⟨hxN,hxJ⟩
      refine ⟨hxN,?_⟩
      have hxH := (zeroLocus_restrictOn_iff hcH hxN).mp hxJ
      rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHsmooth.1] at hxH
    · rintro ⟨hxN,hxH⟩
      refine ⟨hxN,(zeroLocus_restrictOn_iff hcH hxN).mpr ?_⟩
      rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHsmooth.1]
  change IsClosedSubmanifold n (N ∩ (restrictOn n N (vanishingIdeal (n := n) H)).zeroLocus) at hS
  change restrictOn n N (vanishingIdeal (n := n) H)=
    vanishingIdeal (n := n) (N ∩ (restrictOn n N (vanishingIdeal (n := n) H)).zeroLocus) at hWhole
  rw [hSet] at hS hWhole
  exact ⟨hS,hWhole⟩

/-- Private ordinary whole-parts transition. It removes no actual clock and
assumes no future lower carrier/support certificate. -/
private theorem transverse_remaining_member_whole_parts (hn : 0<n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hFull : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N (old ++ born))
    (i : Fin old.length) :
    IsClosedSubmanifold n (N ∩ old.get i) ∧
      oldTraceIdeal N old i=vanishingIdeal (n := n) (N ∩ old.get i) ∧
      oldMonomialPart N old born i=unitIdeal n X ∧
      oldResidualPart N old born i=vanishingIdeal (n := n) (N ∩ old.get i) := by
  let v : Fin (old ++ born).length := ⟨i.val,by simp only [List.length_append];omega⟩
  have hv : (old ++ born).get v=old.get i := by
    simp only [v,List.get_eq_getElem,List.getElem_append_left i.isLt]
  have hOldMem : old.get i ∈ old ++ born := List.mem_append_left born (List.get_mem old i)
  have hH : IsSNCDivisor n [old.get i] := isSNCDivisor_of_sublist hFull
    (List.singleton_sublist.mpr hOldMem)
  have hTH : IsTransverse n N [old.get i] := isTransverse_of_forall_mem hTr
    (fun K hK => by rw [List.mem_singleton.mp hK];exact hOldMem)
  obtain ⟨hZ,hWhole⟩ := transverse_trace_reduced hn hN hH hTH
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [old.get i].length))
  obtain ⟨hcI,_hnzI,_hPrincipal,_hOrd⟩ := actual_normalized_transverse_member_geometry hn hN hH hTH
  have hBorn : IsSNCDivisor n born := isSNCDivisor_of_sublist hFull (List.sublist_append_right old born)
  have hTBorn : IsTransverse n N born := isTransverse_of_forall_mem hTr
    (fun K hK => List.mem_append_right old hK)
  have hNoFactor : ∀ x ∈ N,∀ b : Fin born.length,x ∈ born.get b →
      ∃ f,(oldTraceIdeal N old i).mem x f ∧
        ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (born.get b)).mem x) x f := by
    intro x hxN b hxB
    let w : Fin (old ++ born).length := ⟨old.length+b.val,by simp only [List.length_append];omega⟩
    have hw : (old ++ born).get w=born.get b := by
      simp only [w,List.get_eq_getElem,List.getElem_append_right (by omega : old.length ≤ old.length+b.val),
        Nat.add_sub_cancel_left]
    have hvw : v ≠ w := by
      intro he
      have hh := congrArg Fin.val he
      dsimp only [v,w] at hh
      omega
    by_cases hxH : x ∈ old.get i
    · obtain ⟨f,hf,hOld,hNotBorn⟩ := exists_traceSpan_separator hn hFull hTr hxN v w
        (by rw [hv];exact hxH) (by rw [hw];exact hxB) hvw
      rw [hv] at hOld
      rw [hw] at hNotBorn
      exact ⟨f,⟨hf,hOld⟩,hNotBorn⟩
    · have hOne : (oldTraceIdeal N old i).mem x (1 : X → ℂ) :=
        ⟨holomorphicAt_const 1,(traceSpan_unit_iff_notMem (hFull.1 _ hOldMem) hxN).mpr hxH⟩
      exact ⟨1,hOne,fun h => ((traceSpan_unit_iff_notMem
        (hBorn.1 _ (List.get_mem born b)) hxN).mp h) hxB⟩
  have hD : oldMonomialPart N old born i=unitIdeal n X :=
    monomialPartAlong_eq_unit_of_no_member_factor hBorn hTBorn hcI hNoFactor
  have hJ : oldResidualPart N old born i=restrictOn n N (oldTraceIdeal N old i) :=
    nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hN hBorn hTBorn hcI hNoFactor
  have hNorm : restrictOn n N (vanishingIdeal (n := n) (N ∩ old.get i))=
      vanishingIdeal (n := n) (N ∩ old.get i) := by
    ext x g
    constructor
    · intro hg
      exact MemberTraceIdealAlong.mem_vanishingIdeal_of_isInSpanOnAt inter_subset_left hg.1 hg.2
    · exact le_restrictOn (VanishingIdealCoherent.isCoherent_vanishingIdeal hZ) x g
  exact ⟨hZ,hWhole,hD,hJ.trans (by
    change restrictOn n N (restrictOn n N (vanishingIdeal (n := n) (old.get i)))=_
    rw [hWhole,hNorm])⟩

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

private theorem smaller_boundary_members (M : MarkedIdeal n X) (E' : List (Set X))
    (hsub : ∀ H ∈ E',H ∈ M.E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      ∀ H ∈ (geoTransformAlong ({M with E := E'} : MarkedIdeal n X) T).E,
        H ∈ (geoTransformAlong M T).E
  | _,.refl => hsub
  | _,.step T C π _hπ => forall_mem_transformE π C (smaller_boundary_members M E' hsub T)

private theorem forget_initial_boundary_test (M : MarkedIdeal n X) (E' : List (Set X))
    (hsub : ∀ H ∈ E',H ∈ M.E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower M T →
      IsGeoTestTower ({M with E := E'} : MarkedIdeal n X) T
  | _,.refl,_hT => trivial
  | _,.step T C _π _hπ,hT =>
      ⟨forget_initial_boundary_test M E' hsub T hT.1,
        (DropMembers.isAdmissibleCentre_geoTransformAlong_withE_iff M E' T C).mpr
          ⟨hT.2.1,hT.2.2.1,hasNormalCrossings_of_forall_mem hT.2.2.2
            (smaller_boundary_members M E' hsub T)⟩⟩

/-- Private actual density transition from the SAME upper two tests and
ordinary source density. The final original/born clocks stay literal. -/
private theorem upper_current_full_density (hn : 0<n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hFull : IsSNCDivisor n (old ++ born))
    (hDense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (T : BlowupTower X Y) (hCarrier : IsGeoTestTower (geometricTemplate N born) T)
    (hAmbient : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T) :
    let NQ := strictAlong T N
    let oldQ := old.map (strictAlong T)
    let bornQ := (geoTransformAlong (geometricTemplate N born) T).E
    NQ ⊆ closure (NQ \ ⋃ H ∈ oldQ ++ bornQ,H) := by
  have hBare : IsGeoTestTower (geometricTemplate N []) T :=
    forget_initial_boundary_test (geometricTemplate N born) [] (by simp) T hCarrier
  have hRecorded := actual_recorded_tower_residual_dictionary hn hN hFull hDense T hBare hAmbient
  have hDensity := hRecorded.2.2.2.1
  have hOrder₀ := full_ordered_list N (old ++ born) [] T
  simp only [List.append_nil] at hOrder₀
  have hOrder := full_ordered_list N old born T
  have hLists : (old ++ born).map (strictAlong T) ++ (geoTransformAlong (geometricTemplate N []) T).E=
      old.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate N born) T).E :=
    hOrder₀.symm.trans hOrder
  rw [N_geoTransformAlong,hLists] at hDensity
  exact hDensity



/-- Reused compactness-free private lower-state induction; ZERO separate achievement credit. -/
private def oldEquiv (old : List (Set X)) (T : BlowupTower X Y) :
    Fin old.length ≃ Fin (old.map (strictAlong T)).length :=
  finCongr (by simp)

private theorem get_oldEquiv (old : List (Set X)) (T : BlowupTower X Y)
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

private theorem monomial_oldEquiv (N : Set Y) (old : List (Set X))
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

private theorem finite_sum_oldEquiv (old : List (Set X)) (T : BlowupTower X Y)
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

private theorem segment_head (M : MarkedIdeal n X) :
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


private theorem unique_active_invariants {r b : ℕ} (A : Fin r → Fin b → ℕ) (a : Fin r)
    (hSub : properRows A ⊆ {a}) : tauD A ≤ 1 ∧ (tauD A=1 → nuOne A=0) := by
  have hCard : (properRows A).card ≤ 1 := by
    simpa only [Finset.card_singleton] using Finset.card_le_card hSub
  refine ⟨hCard,?_⟩
  intro hTau
  change (properRows A).card=1 at hTau
  have hEq : properRows A={a} := Finset.eq_of_subset_of_card_le hSub (by simp [hTau])
  have hAct : (properRows A).Nonempty := by rw [hEq];simp
  apply (nuOne_eq_zero_iff_exists_gcd_row A hAct).mpr
  refine ⟨a,by rw [hEq];simp,?_⟩
  intro j
  simp [gcdColumn,hEq]

/-- Reused private actual unit/exponent argument; no separate credit. -/
private theorem unit_divExpAlong_zero {N H : Set X} {I : GermIdeal n X} {x : X}
    (hClosed : IsClosed (N ∩ H)) (hUnit : I.mem x (1 : X → ℂ)) :
    divExpAlong n N I H x=0 := by
  by_cases hx : x ∈ N ∩ H
  · have hNot : ¬IsDivNearAlong n N I H 1 x := by
      intro hDiv
      have hCos := hDiv.self_of_nhds hx.1 hx.2
      exact one_ne_zero ((vanishesToOrderOn_one_iff hx.1 (holomorphicAt_const 1)).mp (hCos.2 1 hUnit))
    have hFin : ∃ e,¬IsDivNearAlong n N I H (e+1) x := ⟨0,hNot⟩
    rw [divExpAlong,dif_pos hFin]
    exact (Nat.find_eq_zero hFin).mpr hNot
  · have hInf : ¬∃ e,¬IsDivNearAlong n N I H (e+1) x := by
      rintro ⟨e,he⟩
      exact he (isDivNearAlong_of_notMem hClosed hx (e+1))
    rw [divExpAlong,dif_neg hInf]

private theorem singleton_source_invariants {L : Set X} {lo born : List (Set X)}
    (hL : IsClosedSubmanifold n L) (hFull : IsSNCDivisor n (lo ++ born))
    (a : Fin lo.length)
    (hOther : ∀ x ∈ L,∀ b : Fin lo.length,b ≠ a → (oldMonomialPart L lo born b).mem x 1) :
    ∀ x ∈ L,properRows (canonicalMatrix L lo born x) ⊆ {a} ∧
      tauD (canonicalMatrix L lo born x) ≤ 1 ∧
      (tauD (canonicalMatrix L lo born x)=1 → nuOne (canonicalMatrix L lo born x)=0) := by
  intro x hx
  have hSub : properRows (canonicalMatrix L lo born x) ⊆ {a} := by
    intro b hb
    apply Finset.mem_singleton.mpr
    by_contra hne
    have hUnit := hOther x hx b hne
    have hZero (c : Fin born.length) :
        divExpAlong n L (oldMonomialPart L lo born b) (born.get c) x=0 :=
      unit_divExpAlong_zero (hL.1.inter (hFull.1 _ (List.mem_append_right lo (List.get_mem born c)))) hUnit
    have hSum : ∑ c : Fin born.length,divExpAlong n L (oldMonomialPart L lo born b) (born.get c) x=0 := by
      apply Finset.sum_eq_zero
      intro c _hc
      exact hZero c
    have hPos := (Finset.mem_filter.mp hb).2
    change 0 < ∑ c : Fin born.length,divExpAlong n L (oldMonomialPart L lo born b) (born.get c) x at hPos
    omega
  exact ⟨hSub,unique_active_invariants _ a hSub⟩

private theorem singleton_mask_model {L : Set X} {lo born : List (Set X)}
    (a : Fin lo.length) (hcD : (oldMonomialPart L lo born a).IsCoherent) :
    maskMarked L lo born {a}=(⟨L,born,oldMonomialPart L lo born a,1⟩ : MarkedIdeal n X) := by
  have hIdeal : (maskMarked L lo born {a}).ideal=oldMonomialPart L lo born a := by
    ext x g
    constructor
    · intro hg
      change IsInSpanAt (n := n) (fun f => ∃ b ∈ ({a} : Finset (Fin lo.length)),
        (oldMonomialPart L lo born b).mem x f) x g at hg
      exact HomogenizedIdeal.mem_of_isInSpanAt hcD
        (hg.mono fun f ⟨b,hb,hf⟩ => (Finset.mem_singleton.mp hb) ▸ hf)
    · intro hg
      change IsInSpanAt (n := n) (fun f => ∃ b ∈ ({a} : Finset (Fin lo.length)),
        (oldMonomialPart L lo born b).mem x f) x g
      exact isInSpanAt_self ⟨a,Finset.mem_singleton_self a,hg⟩
        (GermIdeal.IsCoherent.holomorphicAt_mem hcD hg)
  exact congrArg (fun I : GermIdeal n X => (⟨L,born,I,1⟩ : MarkedIdeal n X)) hIdeal

private theorem lower_state_singleton_source (hn : 0<n) {L : Set X}
    {lo born : List (Set X)} (hL : IsClosedSubmanifold n L)
    (hFull : IsSNCDivisor n (lo ++ born)) (hTr : IsTransverse n L born)
    (hDense : L ⊆ closure (L \ ⋃ H ∈ lo ++ born,H))
    (hOrd : ∀ x ∈ L,∀ b,ordinaryTraceOrder L (oldResidualPart L lo born b) x ≤ 1)
    (hPrep : ∀ x ∈ L,IsPreparedResidualSNCAt L lo born x)
    (a : Fin lo.length)
    (hOther : ∀ x ∈ L,∀ b : Fin lo.length,b ≠ a → (oldMonomialPart L lo born b).mem x 1)
    (v : MonomialInvariant.Val) (hFirst : (ofLex v).1=n-1)
    (hBound : ∀ x ∈ (⟨L,born,oldMonomialPart L lo born a,1⟩ : MarkedIdeal n X).cosupp,
      gammaAlong n L (oldMonomialPart L lo born a) born 1 x ≤ (v : WithBot MonomialInvariant.Val))
    (T : BlowupTower X Y)
    (hCan : ResolutionDriver.IsCanonicalSegment (⟨L,born,oldMonomialPart L lo born a,1⟩ : MarkedIdeal n X)
      (fun {Q} R => towerInvAlong (⟨L,born,oldMonomialPart L lo born a,1⟩ : MarkedIdeal n X) (Y := Q) R) T) :
    currentState L lo born {a} T := by
  have hInv := singleton_source_invariants hL hFull a hOther
  have hTau : ∀ x ∈ L,tauD (canonicalMatrix L lo born x) ≤ ({a} : Finset (Fin lo.length)).card := by
    intro x hx
    simpa only [Finset.card_singleton] using (hInv x hx).2.1
  have hNu : ∀ x ∈ L,tauD (canonicalMatrix L lo born x)=({a} : Finset (Fin lo.length)).card →
      nuOne (canonicalMatrix L lo born x)=0 := by
    intro x hx hh
    exact (hInv x hx).2.2 (by simpa only [Finset.card_singleton] using hh)
  obtain ⟨_hcI,_hnzI,_hcJ,_hnzJ,hcD,hnzD,hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hL hFull hTr hDense a
  have hModel := singleton_mask_model a hcD
  have hBorn : IsSNCDivisor n born := isSNCDivisor_of_sublist hFull (List.sublist_append_right lo born)
  have hPhase : (⟨L,born,oldMonomialPart L lo born a,1⟩ : MarkedIdeal n X).IsWellFormed :=
    ⟨hL,hcD,hBorn,hTr⟩
  have hMono : IsMonomialAlong n L (maskMarked L lo born {a}).ideal born := by
    rw [hModel]
    exact hmD
  obtain ⟨_hcSigma,hNZSigma,hWFSigma,hCos,_hAdm,_hThin,_hCNC,_hBad,_hProper,_hRows,_hNext⟩ :=
    prepared_zero_mask_global_gamma_step hn hL hFull hTr hDense hOrd hPrep {a}
      (Finset.singleton_nonempty a) hTau hMono
  have hCanMask : ResolutionDriver.IsCanonicalSegment (maskMarked L lo born {a})
      (fun {Q} R => towerInvAlong (maskMarked L lo born {a}) (Y := Q) R) T := by
    rw [hModel]
    exact hCan
  have hTest : IsGeoTestTower (maskMarked L lo born {a}) T := by
    rw [hModel]
    exact (canonical_prefix_markOne_bounded_maxima hn _ hPhase hnzD hmD rfl v hFirst hBound T hCan).1
  exact currentState_segment hn hL hFull hTr hDense hOrd hPrep {a} (Finset.singleton_nonempty a)
    hTau hNu hWFSigma hNZSigma hMono hCos T hCanMask hTest

private theorem transverse_slice_remaining (hn : 0 < n) {N H : Set X}
    {F : List (Set X)} (hE : IsSNCDivisor n (H :: F))
    (hTr : IsTransverse n N (H :: F)) : IsTransverse n (N ∩ H) F := by
  intro x hx
  obtain ⟨_kC,kN,Φ,s,hsrc,hs,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn (Subset.refl N) hE hTr hTr.hasNormalCrossings hx.1
  let z : Fin (H :: F).length := ⟨0,by simp⟩
  let c : Fin F.length → Fin (H :: F).length := fun a =>
    ⟨a.val+1,by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using a.isLt⟩
  have hz : (H :: F).get z=H := rfl
  have hc (a : Fin F.length) : (H :: F).get (c a)=F.get a := by
    simp [c,List.get_eq_getElem]
  have hxH : x ∈ (H :: F).get z := by rw [hz];exact hx.2
  let Q : Finset (Fin n) := Finset.univ.filter fun t => kN ≤ t.val
  refine ⟨Q ∪ {s z},fun a => {s (c a)},?_,?_⟩
  · apply coordinateFamilyAt_of_flattening Φ ?_
      (mem_complexChartAt_source x) Φ.center_mem_source (fun _ hi => hi)
    rintro (_ | a) hxa y hy hyΦ
    · change y ∈ N ∩ H ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈
        coordSubspace (Q ∪ {s z})
      rw [ExceptionalPushforwardAlong.coordSubspace_union]
      change (y ∈ N ∧ y ∈ H) ↔
        (Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace Q ∧
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace {s z})
      rw [BlowupSNCTransform.mem_coordSubspace_singleton]
      rw [show coordSubspace Q=complexCoordinatePlane n kN by
        simp only [Q,coordSubspace_eq_complexCoordinatePlane]]
      exact and_congr (by simpa only [complexChartAt] using (hflat hy hyΦ).2.1)
        (by simpa only [hz,complexChartAt] using (hflat hy hyΦ).2.2 z hxH)
    · change y ∈ F.get a ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈
        coordSubspace {s (c a)}
      rw [BlowupSNCTransform.mem_coordSubspace_singleton]
      have ha : x ∈ (H :: F).get (c a) := by rw [hc];exact hxa
      simpa only [hc,complexChartAt] using (hflat hy hyΦ).2.2 (c a) ha
  · intro a hxa
    have ha : x ∈ (H :: F).get (c a) := by rw [hc];exact hxa
    refine ⟨by simp,Finset.disjoint_singleton_left.mpr ?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with hQ | heq
    · have hge := (Finset.mem_filter.mp hQ).2
      exact Nat.not_lt_of_ge hge (hs (c a) ha)
    · have he : c a=z := hinj ha hxH (Finset.mem_singleton.mp heq)
      have hv := congrArg Fin.val he
      dsimp [c,z] at hv
      omega

private theorem actual_remaining_residual_support (hn : 0<n) {N H L : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (i j : Fin old.length) (hne : j ≠ i)
    (hAux : IsSNCDivisor n (H :: (old.eraseIdx i.val ++ born)))
    (hAuxTr : IsTransverse n N (H :: (old.eraseIdx i.val ++ born)))
    (hLTrace : L=N ∩ old.get j) : L=N ∩ (oldResidualPart N old born j).zeroLocus := by
  have hReduced : IsSNCDivisor n (old.eraseIdx i.val ++ born) :=
    isSNCDivisor_of_sublist hAux (List.tail_sublist (H :: (old.eraseIdx i.val ++ born)))
  have hReducedTr : IsTransverse n N (old.eraseIdx i.val ++ born) :=
    isTransverse_of_forall_mem hAuxTr (fun K hK => List.mem_cons_of_mem H hK)
  have hMem : old.get j ∈ old.eraseIdx i.val := List.mem_eraseIdx_iff_getElem.mpr
    ⟨j.val,j.isLt,(fun he => hne (Fin.ext he)),rfl⟩
  obtain ⟨b,hb⟩ := List.mem_iff_get.mp hMem
  have hParts := transverse_remaining_member_whole_parts hn hN hReduced hReducedTr b
  have hSmooth : IsClosedSubmanifold n (N ∩ old.get j) := by rw [←hb];exact hParts.1
  have hJ : oldResidualPart N old born j=vanishingIdeal (n := n) (N ∩ old.get j) := by
    simpa only [oldResidualPart,oldTraceIdeal,hb] using hParts.2.2.2
  rw [hJ,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hSmooth.1]
  rw [←inter_assoc,inter_self]
  exact hLTrace

private theorem upper_current_geometry (hn : 0<n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hFull : IsSNCDivisor n (old ++ born))
    (hDense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (T : BlowupTower X Y) (hCarrier : IsGeoTestTower (geometricTemplate N born) T)
    (hAmbient : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T) :
    let NQ := strictAlong T N
    let oldQ := old.map (strictAlong T)
    let bornQ := (geoTransformAlong (geometricTemplate N born) T).E
    IsClosedSubmanifold n NQ ∧ IsSNCDivisor n (oldQ ++ bornQ) ∧
      NQ ⊆ closure (NQ \ ⋃ H ∈ oldQ ++ bornQ,H) := by
  have hBare : IsGeoTestTower (geometricTemplate N []) T :=
    forget_initial_boundary_test (geometricTemplate N born) [] (by simp) T hCarrier
  have hRecorded := actual_recorded_tower_residual_dictionary hn hN hFull hDense T hBare hAmbient
  have hOrder₀ := full_ordered_list N (old ++ born) [] T
  simp only [List.append_nil] at hOrder₀
  have hLists : (old ++ born).map (strictAlong T) ++ (geoTransformAlong (geometricTemplate N []) T).E=
      old.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate N born) T).E :=
    hOrder₀.symm.trans (full_ordered_list N old born T)
  have hNQ : IsClosedSubmanifold n (strictAlong T N) := by
    simpa only [N_geoTransformAlong,geometricTemplate] using hRecorded.1
  have hFullQ := hRecorded.2.1
  rw [hLists] at hFullQ
  exact ⟨hNQ,hFullQ,upper_current_full_density hn hN hFull hDense T hCarrier hAmbient⟩

/-- Output-only actual upper/protected-prefix data, internally constructed
by source geometry and every SAME actual native successor. -/
def protectedGammaPrefixData (N H L : Set X) (old born : List (Set X))
    (i j : Fin old.length) (T : BlowupTower X Y) : Prop :=
  let NQ := strictAlong T N
  let oldQ := old.map (strictAlong T)
  let bornQ := (geoTransformAlong (geometricTemplate N born) T).E
  let HQ := strictAlong T H
  let SiQ := strictAlong T (N ∩ H)
  let LQ := strictAlong T L
  let FQ := oldQ.eraseIdx i.val ++ bornQ
  let M := chronologicalMarked (⟨N,born,vanishingIdeal (n := n) (N ∩ H),0⟩ : MarkedIdeal n X) T
  IsGeoTestTower (geometricTemplate N born) T ∧
    IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T ∧
    CurrentSharpCentres N (old ++ born) T ∧
    IsSNCDivisor n (HQ :: FQ) ∧ IsTransverse n NQ (HQ :: FQ) ∧
    LQ=NQ ∩ strictAlong T (old.get j) ∧
    M.N=NQ ∧ M.E=bornQ ∧ M.d=0 ∧ M.ideal=vanishingIdeal (n := n) SiQ ∧
    IsClosedSubmanifold n SiQ ∧ HasNormalCrossings n SiQ FQ ∧
    SiQ ⊆ closure (SiQ \ ⋃ K ∈ FQ,K) ∧ SiQ=NQ ∩ HQ

private theorem upperProtectedState_refl (hn : 0<n) {N H L : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (i j : Fin old.length)
    (hAux : IsSNCDivisor n (H :: (old.eraseIdx i.val ++ born)))
    (hAuxTr : IsTransverse n N (H :: (old.eraseIdx i.val ++ born)))
    (hLTrace : L=N ∩ old.get j) : protectedGammaPrefixData N H L old born i j (.refl (X := X)) := by
  let F := old.eraseIdx i.val ++ born
  have hH : IsSNCDivisor n [H] := isSNCDivisor_of_sublist hAux (by simp)
  have hNH : IsTransverse n N [H] := isTransverse_of_forall_mem hAuxTr
    (fun K hK => by rw [List.mem_singleton.mp hK];simp)
  have hSi := (transverse_trace_reduced hn hN hH hNH).1
  have hTF : IsTransverse n (N ∩ H) F := transverse_slice_remaining hn hAux hAuxTr
  have hF : IsSNCDivisor n F := isSNCDivisor_of_sublist hAux (List.tail_sublist (H :: F))
  have hDense : N ∩ H ⊆ closure ((N ∩ H) \ ⋃ K ∈ F,K) := by
    simpa only [List.nil_append] using actual_cleanup_source_full_density
      (O := []) (B := F) hn hSi (by simpa using hF) hTF
        (by simpa using (subset_closure : N ∩ H ⊆ closure (N ∩ H)))
  have hSource : IsSNCDivisor n (H :: F) ∧ IsTransverse n N (H :: F) ∧
      L=N ∩ old.get j ∧ IsClosedSubmanifold n (N ∩ H) ∧
      HasNormalCrossings n (N ∩ H) F ∧ N ∩ H ⊆ closure ((N ∩ H) \ ⋃ K ∈ F,K) :=
    ⟨hAux,hAuxTr,hLTrace,hSi,hTF.hasNormalCrossings,hDense⟩
  simpa [protectedGammaPrefixData,strictAlong,geoTransformAlong,chronologicalMarked,
    geometricTemplate,IsGeoTestTower,CurrentSharpCentres,F] using hSource

private theorem list_get_eq_of_eq {A : Type*} {K M : List A} (hKM : K=M)
    {i : Fin K.length} {j : Fin M.length} (hij : i.val=j.val) : K.get i=M.get j := by
  subst M
  rw [Fin.ext hij]

private theorem upperProtectedState_step (hn : 0<n) {N H L : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hFull : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ K ∈ old ++ born,K))
    (i j : Fin old.length) (hne : j ≠ i)
    (a : Fin (old.eraseIdx j.val).length) (ha : (old.eraseIdx j.val).get a=old.get i)
    (T : BlowupTower X Y) (hUpper : protectedGammaPrefixData N H L old born i j T)
    (hLower : currentState L (old.eraseIdx j.val) born {a} T)
    {Z : CMfd.{u} n} (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCenter : C=maxLocusA (geoTransformAlong
      (⟨L,born,oldMonomialPart L (old.eraseIdx j.val) born a,1⟩ : MarkedIdeal n X) T)) :
    protectedGammaPrefixData N H L old born i j (.step T C π hπ) := by
  let lo := old.eraseIdx j.val
  let NQ := strictAlong T N
  let oldQ := old.map (strictAlong T)
  let BQ := (geoTransformAlong (geometricTemplate N born) T).E
  let HQ := strictAlong T H
  let LQ := strictAlong T L
  let SiQ := strictAlong T (N ∩ H)
  let FQ := oldQ.eraseIdx i.val ++ BQ
  let iQ : Fin oldQ.length := ⟨i.val,by simpa only [oldQ,List.length_map] using i.isLt⟩
  let jQ : Fin oldQ.length := ⟨j.val,by simpa only [oldQ,List.length_map] using j.isLt⟩
  let aQ : Fin (oldQ.eraseIdx j.val).length :=
    ⟨a.val,by simpa only [oldQ,List.eraseIdx_map,List.length_map] using a.isLt⟩
  have hneQ : jQ ≠ iQ := by
    intro he
    have hv : jQ.val=iQ.val := congrArg (fun t : Fin oldQ.length => t.val) he
    exact hne (Fin.ext hv)
  have hGeti : oldQ.get iQ=strictAlong T (old.get i) := by simp [oldQ,iQ,List.get_eq_getElem]
  have hGetj : oldQ.get jQ=strictAlong T (old.get j) := by simp [oldQ,jQ,List.get_eq_getElem]
  have hErase : lo.map (strictAlong T)=oldQ.eraseIdx j.val := by simp only [lo,oldQ,List.eraseIdx_map]
  have hGetLower : (lo.map (strictAlong T)).get (oldEquiv lo T a)=(oldQ.eraseIdx j.val).get aQ := by
    exact list_get_eq_of_eq hErase rfl
  have haQ : (oldQ.eraseIdx j.val).get aQ=oldQ.get iQ := by
    rw [←hGetLower,get_oldEquiv lo T a,ha,hGeti]
  dsimp only [protectedGammaPrefixData] at hUpper
  obtain ⟨hCarrier,hAmbient,hSharp,hAux,hAuxTr,hLTrace,hMN,hME,hMD,hMI,hSi,hSiNC,hSiDense,hSiInter⟩ := hUpper
  change IsSNCDivisor n (HQ :: FQ) at hAux
  change IsTransverse n NQ (HQ :: FQ) at hAuxTr
  change SiQ=NQ ∩ HQ at hSiInter
  have hLTraceQ : LQ=NQ ∩ oldQ.get jQ := by rw [hGetj];exact hLTrace
  obtain ⟨hNQ,hFullQ,hDenseQ⟩ := upper_current_geometry hn hN hFull hDense T hCarrier hAmbient
  have hTrQ : IsTransverse n NQ BQ := isTransverse_of_forall_mem hAuxTr
    (fun K hK => List.mem_cons_of_mem HQ (List.mem_append_right _ hK))
  have hSupportQ := actual_remaining_residual_support (X := Y) hn hNQ iQ jQ hneQ hAux hAuxTr hLTraceQ
  change currentStateData L lo born {a} T ⟨lo.map (strictAlong T),oldEquiv lo T⟩ at hLower
  dsimp only [currentStateData] at hLower
  have hBornReadback : (geoTransformAlong (geometricTemplate L born) T).E=BQ :=
    geoTransformAlong_E_eq_of_E_eq (𝔪 := geometricTemplate N born) (𝔍 := geometricTemplate L born) rfl T
  rw [hBornReadback] at hLower
  obtain ⟨_hSum,hLQ,hLowerFullQ,hLTrQ,hLDenseQ,_hLowerOrdQ,_hLowerPrepQ,_hTauQ,_hActQ,_hNuQ,
    _hMaskWFQ,_hMaskNZQ,_hMaskMonoQ,_hMaskCosQ,_hLowerAmbient,_hLowerSharp,hRows⟩ := hLower
  have hDa := (hRows a).2.2.2.2.1
  have hPhaseCurrent : geoTransformAlong
      (⟨L,born,oldMonomialPart L (old.eraseIdx j.val) born a,1⟩ : MarkedIdeal n X) T=
      (⟨LQ,BQ,oldMonomialPart LQ (oldQ.eraseIdx j.val) BQ aQ,1⟩ : MarkedIdeal n Y) := by
    calc
      _=(⟨LQ,BQ,oldMonomialPart LQ (lo.map (strictAlong T)) BQ (oldEquiv lo T a),1⟩ : MarkedIdeal n Y) := by
        simpa only [Finset.mem_singleton,ite_true] using hDa
      _=_ := by
        apply congrArg (fun I : GermIdeal n Y => (⟨LQ,BQ,I,1⟩ : MarkedIdeal n Y))
        change monomialPartAlong n LQ (restrictOn n LQ
          (vanishingIdeal (n := n) ((lo.map (strictAlong T)).get (oldEquiv lo T a)))) BQ=
            monomialPartAlong n LQ (restrictOn n LQ
              (vanishingIdeal (n := n) ((oldQ.eraseIdx j.val).get aQ))) BQ
        rw [hGetLower]
  have hCenterQ : C=maxLocusA
      (⟨LQ,BQ,oldMonomialPart LQ (oldQ.eraseIdx j.val) BQ aQ,1⟩ : MarkedIdeal n Y) :=
    hCenter.trans (congrArg maxLocusA hPhaseCurrent)
  have hπQ : IsBlowupAlong n (maxLocusA
      (⟨LQ,BQ,oldMonomialPart LQ (oldQ.eraseIdx j.val) BQ aQ,1⟩ : MarkedIdeal n Y)) π := by
    rw [←hCenterQ]
    exact hπ
  rw [hErase] at hLDenseQ
  have hStep := actual_current_given_gamma_maximum_protects_other_row (X := Y) (Y := Z)
    hn hNQ hFullQ hTrQ hDenseQ iQ jQ hneQ hAux hAuxTr hLQ hLTraceQ hSupportQ hLTrQ hLDenseQ aQ haQ π hπQ
  dsimp only at hStep
  obtain ⟨_hPWF,_hPTest,_hPCan,_hPWF',_hPNZ',_hPMono',_hPDrop,hCNC,_hLowerBad,hUpperBad,
    hCarrierStep,_hAmbientStep,hSi',hWhole',hSiNC',hSiDense',hAux',hAuxTr',hSiInter',hLTrace'⟩ := hStep
  have hCN := (hCarrierStep.2).subset_N
  have hCBorn := hCarrierStep.2.2.2
  rw [←hCenterQ] at hCN hCBorn hCNC hUpperBad hSi' hWhole' hSiNC' hSiDense' hAux' hAuxTr' hSiInter' hLTrace'
  have hSourceWF : (geometricTemplate N born).IsWellFormed :=
    ⟨hN,isCoherent_unitIdeal,isSNCDivisor_of_sublist hFull (List.sublist_append_right old born),hTr⟩
  have hCarrierWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hSourceWF T hCarrier
  have hCarrier' : IsGeoTestTower (geometricTemplate N born) (.step T C π hπ) := by
    refine ⟨hCarrier,hπ.1,?_,hCBorn⟩
    change C ⊆ cosupport n _ _ (geoTransformAlong (geometricTemplate N born) T).d
    rw [d_geoTransformAlong]
    change C ⊆ cosupport n _ _ 0
    rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hCarrierWF.isCoherent hg),N_geoTransformAlong]
    exact hCN
  have hAmbientWF₀ : (geometricTemplate (univ : Set X) (old ++ born)).IsWellFormed :=
    ⟨⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩,
      isCoherent_unitIdeal,hFull,isTransverse_univ_of_isSNCDivisor hFull⟩
  have hAmbientWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hAmbientWF₀ T hAmbient
  have hAmbient' : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) (.step T C π hπ) := by
    refine ⟨hAmbient,hπ.1,?_,?_⟩
    · change C ⊆ cosupport n _ _ (geoTransformAlong (geometricTemplate (univ : Set X) (old ++ born)) T).d
      rw [d_geoTransformAlong]
      change C ⊆ cosupport n _ _ 0
      rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hAmbientWF.isCoherent hg),N_geoTransformAlong]
      change C ⊆ strictAlong T (univ : Set X)
      rw [strict_univ T]
      exact subset_univ C
    · rw [full_ordered_list N old born T]
      exact hCNC
  have hSharp' : CurrentSharpCentres N (old ++ born) (.step T C π hπ) := by
    refine ⟨hSharp,?_⟩
    rw [full_ordered_list N old born T]
    exact hUpperBad
  let T' : BlowupTower X Z := .step T C π hπ
  have hOldNext : oldQ.map (geoStrictTransform π C)=old.map (strictAlong T') := by
    simp only [oldQ,T',strictAlong,List.map_map,Function.comp_def]
  have hBornNext : BQ.map (geoStrictTransform π C) ++ [π ⁻¹' C]=
      (geoTransformAlong (geometricTemplate N born) T').E := rfl
  have hFNext : (oldQ.eraseIdx i.val ++ BQ).map (geoStrictTransform π C) ++ [π ⁻¹' C]=
      (old.map (strictAlong T')).eraseIdx i.val ++ (geoTransformAlong (geometricTemplate N born) T').E := by
    rw [List.map_append,←List.eraseIdx_map,hOldNext,List.append_assoc,hBornNext]
  change IsSNCDivisor n (geoStrictTransform π C HQ ::
    ((oldQ.eraseIdx i.val ++ BQ).map (geoStrictTransform π C) ++ [π ⁻¹' C])) at hAux'
  change IsTransverse n (geoStrictTransform π C NQ) (geoStrictTransform π C HQ ::
    ((oldQ.eraseIdx i.val ++ BQ).map (geoStrictTransform π C) ++ [π ⁻¹' C])) at hAuxTr'
  rw [←hSiInter] at hSi' hWhole' hSiNC' hSiDense' hSiInter'
  rw [hFNext] at hAux' hAuxTr' hSiNC' hSiDense'
  rw [hGetj] at hLTrace'
  let M₀ : MarkedIdeal n X := ⟨N,born,vanishingIdeal (n := n) (N ∩ H),0⟩
  have hGeom := chronologicalMarked_geometric_fields M₀ T'
  have hMN' : (chronologicalMarked M₀ T').N=strictAlong T' N := hGeom.1.trans (N_geoTransformAlong _ T')
  have hME' : (chronologicalMarked M₀ T').E=(geoTransformAlong (geometricTemplate N born) T').E := hGeom.2
  have hMD' : (chronologicalMarked M₀ T').d=0 := chronologicalMarked_zero_mark M₀ rfl T'
  have hMI' : (chronologicalMarked M₀ T').ideal=vanishingIdeal (n := n) (strictAlong T' (N ∩ H)) := by
    change nextRelativeStrict (chronologicalMarked M₀ T).N (chronologicalMarked M₀ T).ideal C π=_
    rw [hMN,hMI]
    exact hWhole'
  exact ⟨hCarrier',hAmbient',hSharp',hAux',hAuxTr',hLTrace',hMN',hME',hMD',hMI',
    hSi',hSiNC',hSiDense',hSiInter'⟩

private theorem upperProtectedState_segment (hn : 0<n) {N H L : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hFull : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ K ∈ old ++ born,K))
    (i j : Fin old.length) (hne : j ≠ i)
    (hAux : IsSNCDivisor n (H :: (old.eraseIdx i.val ++ born)))
    (hAuxTr : IsTransverse n N (H :: (old.eraseIdx i.val ++ born)))
    (hLTrace : L=N ∩ old.get j) (hL : IsClosedSubmanifold n L)
    (hLTr : IsTransverse n L born)
    (hLDense : L ⊆ closure (L \ ⋃ K ∈ old.eraseIdx j.val ++ born,K))
    (hOrd : ∀ x ∈ L,∀ b,ordinaryTraceOrder L (oldResidualPart L (old.eraseIdx j.val) born b) x ≤ 1)
    (hPrep : ∀ x ∈ L,IsPreparedResidualSNCAt L (old.eraseIdx j.val) born x)
    (a : Fin (old.eraseIdx j.val).length) (ha : (old.eraseIdx j.val).get a=old.get i)
    (hOther : ∀ x ∈ L,∀ b : Fin (old.eraseIdx j.val).length,b ≠ a →
      (oldMonomialPart L (old.eraseIdx j.val) born b).mem x 1)
    (v : MonomialInvariant.Val) (hFirst : (ofLex v).1=n-1)
    (hBound : ∀ x ∈ (⟨L,born,oldMonomialPart L (old.eraseIdx j.val) born a,1⟩ : MarkedIdeal n X).cosupp,
      gammaAlong n L (oldMonomialPart L (old.eraseIdx j.val) born a) born 1 x ≤ (v : WithBot MonomialInvariant.Val)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      ResolutionDriver.IsCanonicalSegment (⟨L,born,oldMonomialPart L (old.eraseIdx j.val) born a,1⟩ : MarkedIdeal n X)
        (fun {Q} R => towerInvAlong (⟨L,born,oldMonomialPart L (old.eraseIdx j.val) born a,1⟩ : MarkedIdeal n X) (Y := Q) R) T →
      protectedGammaPrefixData N H L old born i j T
  | _,.refl,_hCan => upperProtectedState_refl hn hN i j hAux hAuxTr hLTrace
  | _,.step T C π hπ,hCan => by
      have hUpper := upperProtectedState_segment hn hN hFull hTr hDense i j hne hAux hAuxTr
        hLTrace hL hLTr hLDense hOrd hPrep a ha hOther v hFirst hBound T hCan.1
      have hLowerFull : IsSNCDivisor n (old.eraseIdx j.val ++ born) := isSNCDivisor_of_sublist hFull
        ((List.eraseIdx_sublist old j.val).append (List.Sublist.refl born))
      have hLower := lower_state_singleton_source hn hL hLowerFull hLTr hLDense hOrd hPrep
        a hOther v hFirst hBound T hCan.1
      exact upperProtectedState_step hn hN hFull hTr hDense i j hne a ha T hUpper hLower C π hπ hCan.2.2

/-- Output-only current LOWER whole-record interpretation on the SAME
native prefix, with literal original old-position casts and all born clocks. -/
def canonicalLowerGammaPrefixData (L : Set X) (lo born : List (Set X))
    (a : Fin lo.length) (T : BlowupTower X Y) : Prop :=
  let LQ := strictAlong T L
  let loQ := lo.map (strictAlong T)
  let BQ := (geoTransformAlong (geometricTemplate L born) T).E
  let eQ : Fin lo.length ≃ Fin loQ.length := finCongr (by simp [loQ])
  let Phase : MarkedIdeal n X := ⟨L,born,oldMonomialPart L lo born a,1⟩
  geoTransformAlong Phase T=(⟨LQ,BQ,oldMonomialPart LQ loQ BQ (eQ a),1⟩ : MarkedIdeal n Y) ∧
    IsClosedSubmanifold n LQ ∧ IsSNCDivisor n (loQ ++ BQ) ∧ IsTransverse n LQ BQ ∧
    LQ ⊆ closure (LQ \ ⋃ K ∈ loQ ++ BQ,K) ∧
    (∀ x ∈ LQ,∀ b,ordinaryTraceOrder LQ (oldResidualPart LQ loQ BQ b) x ≤ 1) ∧
    (∀ x ∈ LQ,IsPreparedResidualSNCAt LQ loQ BQ x) ∧
    ∀ b : Fin lo.length,
      let d := if b=a then 1 else 0
      IsGeoTestTower (⟨L,born,oldTraceIdeal L lo b,d⟩ : MarkedIdeal n X) T ∧
      IsGeoTestTower (⟨L,born,oldMonomialPart L lo born b,d⟩ : MarkedIdeal n X) T ∧
      IsGeoTestTower (⟨L,born,oldResidualPart L lo born b,0⟩ : MarkedIdeal n X) T ∧
      geoTransformAlong (⟨L,born,oldTraceIdeal L lo b,d⟩ : MarkedIdeal n X) T=
        (⟨LQ,BQ,oldTraceIdeal LQ loQ (eQ b),d⟩ : MarkedIdeal n Y) ∧
      geoTransformAlong (⟨L,born,oldMonomialPart L lo born b,d⟩ : MarkedIdeal n X) T=
        (⟨LQ,BQ,oldMonomialPart LQ loQ BQ (eQ b),d⟩ : MarkedIdeal n Y) ∧
      geoTransformAlong (⟨L,born,oldResidualPart L lo born b,0⟩ : MarkedIdeal n X) T=
        (⟨LQ,BQ,oldResidualPart LQ loQ BQ (eQ b),0⟩ : MarkedIdeal n Y)

private theorem canonicalLowerGammaPrefixData_of_currentState {L : Set X} {lo born : List (Set X)}
    (a : Fin lo.length) (T : BlowupTower X Y) (hState : currentState L lo born {a} T) :
    canonicalLowerGammaPrefixData L lo born a T := by
  dsimp only [currentState,currentStateData] at hState
  obtain ⟨_hSum,hL,hFull,hTr,hDense,hOrd,hPrep,_hTau,_hAct,_hNu,_hWF,_hNZ,_hMono,_hCos,
    _hAmbient,_hSharp,hRows⟩ := hState
  have hPhase := (hRows a).2.2.2.2.1
  refine ⟨?_,hL,hFull,hTr,hDense,hOrd,hPrep,?_⟩
  · simpa only [Finset.mem_singleton,ite_true,oldEquiv] using hPhase
  · intro b
    simpa only [Finset.mem_singleton,oldEquiv] using hRows b

/-- The actual native lower CAN prefix internally supplies BOTH its whole
canonical lower I/D/J interpretation and the SAME original upper protected
row, tests and current sharp footprint. Source preparedness/bound are
ordinary current inputs here; the original producer derives them internally. -/
theorem actual_prepared_singleton_gamma_prefix_protection (hn : 0<n) {N H L : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hFull : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ K ∈ old ++ born,K))
    (i j : Fin old.length) (hne : j ≠ i)
    (hAux : IsSNCDivisor n (H :: (old.eraseIdx i.val ++ born)))
    (hAuxTr : IsTransverse n N (H :: (old.eraseIdx i.val ++ born)))
    (hLTrace : L=N ∩ old.get j) (hL : IsClosedSubmanifold n L)
    (hLTr : IsTransverse n L born)
    (hLDense : L ⊆ closure (L \ ⋃ K ∈ old.eraseIdx j.val ++ born,K))
    (hOrd : ∀ x ∈ L,∀ b,ordinaryTraceOrder L (oldResidualPart L (old.eraseIdx j.val) born b) x ≤ 1)
    (hPrep : ∀ x ∈ L,IsPreparedResidualSNCAt L (old.eraseIdx j.val) born x)
    (a : Fin (old.eraseIdx j.val).length) (ha : (old.eraseIdx j.val).get a=old.get i)
    (hOther : ∀ x ∈ L,∀ b : Fin (old.eraseIdx j.val).length,b ≠ a →
      (oldMonomialPart L (old.eraseIdx j.val) born b).mem x 1)
    (v : MonomialInvariant.Val) (hFirst : (ofLex v).1=n-1)
    (hBound : ∀ x ∈ (⟨L,born,oldMonomialPart L (old.eraseIdx j.val) born a,1⟩ : MarkedIdeal n X).cosupp,
      gammaAlong n L (oldMonomialPart L (old.eraseIdx j.val) born a) born 1 x ≤ (v : WithBot MonomialInvariant.Val))
    (T : BlowupTower X Y)
    (hCan : ResolutionDriver.IsCanonicalSegment (⟨L,born,oldMonomialPart L (old.eraseIdx j.val) born a,1⟩ : MarkedIdeal n X)
      (fun {Q} R => towerInvAlong (⟨L,born,oldMonomialPart L (old.eraseIdx j.val) born a,1⟩ : MarkedIdeal n X) (Y := Q) R) T) :
    protectedGammaPrefixData N H L old born i j T ∧
      canonicalLowerGammaPrefixData L (old.eraseIdx j.val) born a T := by
  have hUpper := upperProtectedState_segment hn hN hFull hTr hDense i j hne hAux hAuxTr
    hLTrace hL hLTr hLDense hOrd hPrep a ha hOther v hFirst hBound T hCan
  have hLowerFull : IsSNCDivisor n (old.eraseIdx j.val ++ born) := isSNCDivisor_of_sublist hFull
    ((List.eraseIdx_sublist old j.val).append (List.Sublist.refl born))
  have hLower := lower_state_singleton_source hn hL hLowerFull hLTr hLDense hOrd hPrep
    a hOther v hFirst hBound T hCan
  exact ⟨hUpper,canonicalLowerGammaPrefixData_of_currentState a T hLower⟩

end
end Hironaka.HironakaActualProtectedGammaPrefixHistory
