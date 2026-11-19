import Hironaka.Resolution.HironakaActualMixedResidualFullBoundaryCentre
import Hironaka.Resolution.HironakaActualFiniteMarkedSumHistories
import Hironaka.Resolution.HironakaActualProcessedMaskFiniteBlock
import Hironaka.Resolution.HironakaSharpActualEquimultipleResidualHistory
import Hironaka.Resolution.HironakaG4EquimultipleRelativeOrder

/-! A genuine joint residual-product/inactive-factor step at the SAME actual
original mixed prefix. Source-first mathematics:
`hironaka-actual-joint-residual-mask-step-20261101.tex`.
A single present order profile is explicit: producing and assembling all real
profile windows and joint finite termination remain separate obligations. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualJointResidualMaskStep
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsComparison RelativePrincipalizationSpan RestrictedIdealExtension
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaActualProcessedMaskFiniteBlock HironakaActualFiniteMarkedSumHistories
  HironakaSharpActualEquimultipleResidualHistory HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualFiniteMemberProduct HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualChronologicalStrictStep
  HironakaG4CompactWholeMonomialMaskPhase HironakaG4EquimultipleRelativeOrder
  HironakaSharpActualTraceIncidence HironakaG4IncidentOldBornStratumCentre
  DivisorExponentAlong GermIdealOrder MonomialPartAlong MarkedIdealOperationsAlong

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- The actual original inactive proper rows, not a supplied support certificate. -/
def inactiveRows {r b : ℕ} (profile : Fin r → ℕ) (A : Fin r → Fin b → ℕ) : Finset (Fin r) :=
  (properRows A).filter fun i => profile i=0


/-- The true canonical old factor at the unchanged original position, mark ONE. -/
def oldFactorMarked (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (i : Fin E.length) : MarkedIdeal n Y :=
  ⟨(geoTransformAlong (geometricTemplate W []) T).N,
    (geoTransformAlong (geometricTemplate W []) T).E,oldFactor W E T i,1⟩

/-- The genuine finite marked sum retains the product mark and every selected
original mark-one factor. The empty mask is the bare residual product. -/
def jointMarked (W : Set X) (E : List (Set X)) (q : ℕ)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (P : Finset (Fin E.length)) : MarkedIdeal n Y :=
  finiteSum (residualMarked W E q T) (P.toList.map (oldFactorMarked W E T))

private theorem chronological_product_order_sum (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    {x : Y} (hx : x ∈ (geoTransformAlong (geometricTemplate W []) T).N) :
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) x=
      ∑ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x := by
  have h := (original_chronological_full_product_actual_geometry hn hW hE hdense T hT).2.2.2 x hx
  have hL : chronologicalMemberFamily W E T=List.ofFn
      (fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) := by
    unfold chronologicalMemberFamily
    conv_lhs => rw [←List.ofFn_get E,List.map_ofFn]
    rfl
  simpa only [hL,List.map_ofFn,List.sum_ofFn,Function.comp_apply] using h

private theorem unit_of_order_zero {N : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x) {x : X} (hx : x ∈ N)
    (hz : ordinaryTraceOrder N I x=0) : I.mem x (fun _ => (1 : ℂ)) := by
  have hnot : x ∉ cosupport n N I 1 := by
    intro hcos
    have hpos := (ordinaryTraceOrder_cosupport_iff hN hI hnz hx 1).mp hcos
    omega
  have hbad : ¬∀ f : X → ℂ,I.mem x f → VanishesToOrderOn n N x 1 f :=
    fun h => hnot ⟨hx,h⟩
  push Not at hbad
  obtain ⟨f,hf,hvan⟩ := hbad
  have hfx : f x ≠ 0 := by
    intro hfz
    exact hvan ((vanishesToOrderOn_one_iff hx (GermIdeal.IsCoherent.holomorphicAt_mem hI hf)).mpr hfz)
  exact CompanionReduction.one_mem_of_apply_ne_zero hI hf hfx

private theorem factor_unit_of_zero_row (hn : 0 < n) {N : Set X}
    {B : List (Set X)} {D : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hB : IsSNCDivisor n B) (hTr : IsTransverse n N B)
    (hcD : D.IsCoherent) (hnzD : ∀ x ∈ N,IsNonzeroAlongAt N D x)
    (hmD : IsMonomialAlong n N D B) {x : X} (hx : x ∈ N)
    (hz : (∑ j : Fin B.length,divExpAlong n N D (B.get j) x)=0) : D.mem x 1 := by
  apply HironakaG4CanonicalZeroRowUnit.one_mem_of_zero_canonical_row hn hN hB hTr hcD hnzD hmD hx
  intro j
  have hj : divExpAlong n N D (B.get j) x ≤
      ∑ j : Fin B.length,divExpAlong n N D (B.get j) x :=
    Finset.single_le_sum (f := fun j : Fin B.length => divExpAlong n N D (B.get j) x)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  omega



private theorem joint_centre_geometry (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (profile : Fin E.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,∀ i : Fin E.length,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ profile i)
    (P : Finset (Fin E.length)) (hP : ∀ i ∈ P,profile i=0)
    (hBound : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMemberProduct W E T) x=q →
      (inactiveRows profile (factorMatrix W E T x)).card ≤ P.card) :
    ResolutionInvariantSpec.IsInvDomain (n+1) (jointMarked W E q T P) ∧
      ∀ C : Set Y,(jointMarked W E q T P).IsAdmissibleCentre C →
        (geoTransformAlong (geometricTemplate W []) T).IsAdmissibleCentre C ∧
        HasNormalCrossings n C (E.map (strictAlong T) ++
          (geoTransformAlong (geometricTemplate W []) T).E) ∧
        (∀ x ∈ C,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMemberProduct W E T) x=q ∧
          ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x=profile i) ∧
        ∀ i ∈ P,(oldFactorMarked W E T i).IsAdmissibleCentre C ∧
          (⟨(geoTransformAlong (geometricTemplate W []) T).N,
            (geoTransformAlong (geometricTemplate W []) T).E,
            restrictOn n (geoTransformAlong (geometricTemplate W []) T).N
              (vanishingIdeal (n := n) (strictAlong T (E.get i))),1⟩ : MarkedIdeal n Y).IsAdmissibleCentre C ∧
          C ⊆ strictAlong T (E.get i) ∧
          ∀ x ∈ C,(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.mem x 1 := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let J := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  let I := fun i : Fin E.length => restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))
  let D := oldFactor W E T
  let R := residualMarked W E q T
  let L := P.toList.map (oldFactorMarked W E T)
  change ∀ x ∈ A.N,∀ i,ordinaryTraceOrder A.N (J i) x ≤ profile i at hOrd
  have hRecorded := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  have hBorn := isSNCDivisor_of_sublist hRecorded.2.1 (List.sublist_append_right _ _)
  have hOld := isSNCDivisor_of_sublist hRecorded.2.1 (List.sublist_append_left _ _)
  have hParts (i : Fin E.length) := NonmonomialTransformAlong.parts_hypotheses hn
    (⟨A.N,A.E,I i,1⟩ : MarkedIdeal n Y)
    ⟨hRecorded.1,(hRecorded.2.2.2.2 i).1,hBorn,hRecorded.2.2.1⟩
    (hRecorded.2.2.2.2 i).2.1
  have hcD (i : Fin E.length) : (D i).IsCoherent := (hParts i).2.1
  have hnzD (i : Fin E.length) : ∀ x ∈ A.N,IsNonzeroAlongAt A.N (D i) x := (hParts i).2.2.1
  have hmD (i : Fin E.length) : IsMonomialAlong n A.N (D i) A.E := (hParts i).2.2.2.1
  have hFamily (i : Fin E.length) := original_members_actual_finite_chronological_geometry
    hn hW hE hdense i T hT
  have hcJ (i : Fin E.length) : (J i).IsCoherent := (hFamily i).2.2.2.1.isCoherent
  have hnzJ (i : Fin E.length) : ∀ x ∈ A.N,IsNonzeroAlongAt A.N (J i) x := by
    have h := (hFamily i).2.2.2.2.1
    rw [(hFamily i).1] at h
    exact h
  obtain ⟨hcProduct,hnzProduct,_hProductPrincipal,_hProductSum⟩ :=
    original_chronological_full_product_actual_geometry hn hW hE hdense T hT
  have hHead : ResolutionInvariantSpec.IsInvDomain (n+1) R := by
    refine ⟨⟨hRecorded.1,hcProduct,hBorn,hRecorded.2.2.1⟩,?_,hq,hnzProduct⟩
    intro x hx
    obtain ⟨d,hd⟩ := hRecorded.1.2 x hx
    exact ⟨d,hd.1.trans (Nat.le_succ n),hd⟩
  have hTail : ∀ B ∈ L,B.N=R.N ∧ B.E=R.E ∧ B.ideal.IsCoherent ∧ 1 ≤ B.d := by
    intro B hB
    obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hB
    exact ⟨rfl,rfl,hcD i,le_rfl⟩
  change ResolutionInvariantSpec.IsInvDomain (n+1) (finiteSum R L) ∧ _
  refine ⟨finiteSum_isInvDomain R L hHead hTail,?_⟩
  intro C hC
  have hEach : R.IsAdmissibleCentre C ∧ ∀ i ∈ P,(oldFactorMarked W E T i).IsAdmissibleCentre C := by
    have hCos := (finiteSum_history R L hRecorded.1 hcProduct hq hTail
      (.refl : BlowupTower Y Y)).2 trivial |>.1
    have hAllCos : ∀ x ∈ C,∀ B ∈ R::L,x ∈ B.cosupp := by
      intro x hx
      have h := hC.2.1 hx
      change x ∈ (finiteSum R L).cosupp at h
      rw [←geoTransformAlong_refl (finiteSum R L),hCos] at h
      simp only [geoTransformAlong_refl] at h
      exact h
    have hE : (finiteSum R L).E=R.E := (finiteSum_geometry R L hcProduct hq hTail).2.1
    have hNC : HasNormalCrossings n C R.E := hE ▸ hC.2.2
    refine ⟨⟨hC.1,fun x hx => hAllCos x hx R (by simp),hNC⟩,?_⟩
    intro i hi
    refine ⟨hC.1,?_,hNC⟩
    intro x hx
    exact hAllCos x hx _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,Finset.mem_toList.mpr hi,rfl⟩))
  have hCN : C ⊆ A.N := hEach.1.subset_N
  have hOnC : ∀ x ∈ C,ordinaryTraceOrder A.N (chronologicalMemberProduct W E T) x=q ∧
      ∀ i,ordinaryTraceOrder A.N (J i) x=profile i := by
    intro x hx
    have hSum := chronological_product_order_sum hn hW hE hdense T hT (hCN hx)
    have hGe := (ordinaryTraceOrder_cosupport_iff hRecorded.1 hcProduct hnzProduct (hCN hx) q).mp
      (hEach.1.2.1 hx)
    change q ≤ ordinaryTraceOrder A.N (chronologicalMemberProduct W E T) x at hGe
    have hLe : (∑ i,ordinaryTraceOrder A.N (J i) x) ≤ ∑ i,profile i :=
      Finset.sum_le_sum (fun i _ => hOrd x (hCN hx) i)
    have hEq : (∑ i,ordinaryTraceOrder A.N (J i) x)=∑ i,profile i := by
      change ordinaryTraceOrder A.N (chronologicalMemberProduct W E T) x=∑ i,ordinaryTraceOrder A.N (J i) x at hSum
      omega
    refine ⟨hSum.trans (hEq.trans hsum),?_⟩
    exact fun i => (Finset.sum_eq_sum_iff_of_le (fun i _ => hOrd x (hCN hx) i)).mp hEq i (Finset.mem_univ i)
  have hUnitJ (i : Fin E.length) (hi : profile i=0) {x : Y} (hx : x ∈ A.N) : (J i).mem x 1 := by
    apply unit_of_order_zero hRecorded.1 (hcJ i) (hnzJ i) hx
    have h := hOrd x hx i
    rw [hi] at h
    exact Nat.eq_zero_of_le_zero h
  have hDUnitOfNotProper (i : Fin E.length) {x : Y} (hx : x ∈ A.N)
      (hi : i ∉ properRows (factorMatrix W E T x)) : (D i).mem x 1 := by
    have hzero : rowOrder (factorMatrix W E T x) i=0 := by
      by_contra hne
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩)
    exact factor_unit_of_zero_row hn hRecorded.1 hBorn hRecorded.2.2.1
      (hcD i) (hnzD i) (hmD i) hx hzero
  have hAtC (x : Y) (hx : x ∈ C) : inactiveRows profile (factorMatrix W E T x)=P := by
    have hSub : P ⊆ inactiveRows profile (factorMatrix W E T x) := by
      intro i hi
      refine Finset.mem_filter.mpr ⟨?_,hP i hi⟩
      by_contra hnproper
      have hu := hDUnitOfNotProper i (hCN hx) hnproper
      have hc := (hEach.2 i hi).2.1 hx
      change x ∈ cosupport n A.N (D i) 1 at hc
      rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcD i) hg)] at hc
      exact one_ne_zero (hc.2 1 hu)
    exact (Finset.eq_of_subset_of_card_le hSub (hBound x (hCN hx) (hOnC x hx).1)).symm
  have hHi (i : Fin E.length) : IsClosedSubmanifold n (strictAlong T (E.get i)) := by
    let j : Fin (E.map (strictAlong T)).length := ⟨i.val,by simp⟩
    have hGet : (E.map (strictAlong T)).get j=strictAlong T (E.get i) := by simp [j]
    rw [←hGet]
    exact MonomialPart.isClosedSubmanifold_get hn hOld j
  have hOldOfCos (i : Fin E.length) {x : Y} (hx : x ∈ A.N)
      (hc : x ∈ cosupport n A.N (D i) 1 ∨ x ∈ cosupport n A.N (J i) 1) :
      x ∈ strictAlong T (E.get i) := by
    have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal (hHi i)
    have hZero : x ∈ (I i).zeroLocus := by
      rcases hc with hc | hc
      · rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcD i) hg)] at hc
        exact fun g hg => hc.2 g (le_monomialPartAlong hn hBorn hRecorded.2.2.1 (hRecorded.2.2.2.2 i).1 x g hg)
      · rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcJ i) hg)] at hc
        intro g hg
        apply hc.2 g
        have hNm : nonmonomialPartAlong n A.N (I i) A.E=J i := (hRecorded.2.2.2.2 i).2.2.1
        rw [←hNm]
        exact NonmonomialTransformAlong.le_nonmonomialPartAlong_self (hRecorded.2.2.2.2 i).1 x g hg
    have hRaw := (zeroLocus_restrictOn_iff hcH hx).mp hZero
    rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (hHi i).1] at hRaw
  have hContained (i : Fin E.length) (hi : 0 < profile i ∨ i ∈ P) : C ⊆ strictAlong T (E.get i) := by
    intro x hx
    apply hOldOfCos i (hCN hx)
    rcases hi with hi | hi
    · apply Or.inr
      apply (ordinaryTraceOrder_cosupport_iff hRecorded.1 (hcJ i) (hnzJ i) (hCN hx) 1).mpr
      rw [(hOnC x hx).2 i]
      omega
    · exact Or.inl ((hEach.2 i hi).2.1 hx)
  have hAbsent (i : Fin E.length) (hi : profile i=0) (hiP : i ∉ P)
      {x : Y} (hx : x ∈ C) : x ∉ strictAlong T (E.get i) := by
    have hiProper : i ∉ properRows (factorMatrix W E T x) := by
      intro hh
      have hMem : i ∈ inactiveRows profile (factorMatrix W E T x) := Finset.mem_filter.mpr ⟨hh,hi⟩
      rw [hAtC x hx] at hMem
      exact hiP hMem
    have huD := hDUnitOfNotProper i (hCN hx) hiProper
    have huJ := hUnitJ i hi (hCN hx)
    have huMul : ((D i).mul (J i)).mem x 1 := by
      change IsInSpanAt (n := n) (fun f => ∃ a b,(D i).mem x a ∧ (J i).mem x b ∧ f=a*b) x 1
      exact InvertibleIdealQuotient.isInSpanAt_self ⟨1,1,huD,huJ,by simp⟩ (holomorphicAt_const 1)
    have huI : (I i).mem x 1 := by
      have hFac : I i=restrictOn n A.N ((D i).mul (J i)) := (hRecorded.2.2.2.2 i).2.2.2
      rw [hFac]
      exact le_restrictOn (IdealWeightPowers.isCoherent_mul (hcD i) (hcJ i)) x 1 huMul
    intro hxH
    have hz : x ∈ (I i).zeroLocus := (zeroLocus_restrictOn_iff
      (VanishingIdealCoherent.isCoherent_vanishingIdeal (hHi i)) (hCN hx)).mpr
      (by rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (hHi i).1])
    exact one_ne_zero (hz 1 huI)
  have hNC : HasNormalCrossings n C (E.map (strictAlong T) ++ A.E) := by
    intro x hx
    apply actual_incident_old_normalCrossingsAt hRecorded.2.1 hEach.1.2.2 hx
    intro j hj
    let i : Fin E.length := ⟨j.val,by simpa using j.isLt⟩
    have hGet : (E.map (strictAlong T)).get j=strictAlong T (E.get i) := by simp [i]
    rw [hGet] at hj ⊢
    by_cases hi : 0 < profile i
    · exact Eventually.of_forall fun _ hy => hContained i (Or.inl hi) hy
    · by_cases hiP : i ∈ P
      · exact Eventually.of_forall fun _ hy => hContained i (Or.inr hiP) hy
      · exact False.elim (hAbsent i (by omega) hiP hx hj)
  have hCarrier : A.IsAdmissibleCentre C := by
    refine ⟨hEach.1.1,?_,hEach.1.2.2⟩
    change C ⊆ (geoTransformAlong (geometricTemplate W []) T).cosupp
    rw [template_current W [] T]
    change C ⊆ cosupport n (strictAlong T W) (IdealWeightPowers.unitIdeal n Y) 0
    rw [cosupport_zero (fun _ _ hg => hg)]
    have hN : A.N=strictAlong T W := N_geoTransformAlong _ _
    rw [←hN]
    exact hCN
  refine ⟨hCarrier,hNC,hOnC,?_⟩
  intro i hi
  have hDadm := hEach.2 i hi
  have hIadm : (⟨A.N,A.E,I i,1⟩ : MarkedIdeal n Y).IsAdmissibleCentre C := by
    refine ⟨hDadm.1,?_,hDadm.2.2⟩
    intro x hx
    have hCos := hDadm.2.1 hx
    change x ∈ cosupport n A.N (D i) 1 at hCos
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcD i) hg)] at hCos
    change x ∈ cosupport n A.N (I i) 1
    have hcI : (I i).IsCoherent := (hRecorded.2.2.2.2 i).1
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcI hg)]
    exact ⟨hCN hx,fun g hg => hCos.2 g (le_monomialPartAlong hn hBorn hRecorded.2.2.1
      (hRecorded.2.2.2.2 i).1 x g hg)⟩
  exact ⟨hDadm,hIadm,hContained i (Or.inr hi),fun x hx => hUnitJ i (hP i hi) (hCN hx)⟩


/-- A genuine joint residual-product/inactive-factor step: every needed unit,
old-member containment, full boundary NC, actual controlled factor and next row
bound is DERIVED. No processed-support or preparedness hypothesis is present. -/
theorem actual_joint_residual_mask_step (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (profile : Fin E.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,∀ i : Fin E.length,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ profile i)
    (P : Finset (Fin E.length)) (hP : ∀ i ∈ P,profile i=0)
    (hBound : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMemberProduct W E T) x=q →
      (inactiveRows profile (factorMatrix W E T x)).card ≤ P.card) :
    ResolutionInvariantSpec.IsInvDomain (n+1) (jointMarked W E q T P) ∧
      ∀ (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
        (jointMarked W E q T P).IsAdmissibleCentre C →
        (∀ x ∈ C,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMemberProduct W E T) x=q ∧
          ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x=profile i) ∧
        HasNormalCrossings n C (E.map (strictAlong T) ++
          (geoTransformAlong (geometricTemplate W []) T).E) ∧
        IsGeoTestTower (geometricTemplate W []) (.step T C π hπ) ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) (.step T C π hπ) ∧
        MarkedIdeal.RestrictEquiv ((residualMarked W E q T).geoTransform C π)
          (residualMarked W E q (.step T C π hπ)) ∧
        (∀ i ∈ P,C ⊆ strictAlong T (E.get i) ∧
          (∀ x ∈ C,(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.mem x 1) ∧
          (oldFactorMarked W E T i).geoTransform C π=oldFactorMarked W E (.step T C π hπ) i) ∧
        ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (.step T C π hπ)).N,
          ∀ i : Fin E.length,ordinaryTraceOrder
            (geoTransformAlong (geometricTemplate W []) (.step T C π hπ)).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (.step T C π hπ)).ideal z ≤ profile i := by
  have hG := joint_centre_geometry hn hW hE hdense T hT hFull profile q hq hsum hOrd P hP hBound
  refine ⟨hG.1,?_⟩
  intro C π hπ hAdm
  obtain ⟨hCarrier,hNC,hLevel,hSelected⟩ := hG.2 C hAdm
  let A := geoTransformAlong (geometricTemplate W []) T
  have hTest : IsGeoTestTower (geometricTemplate W []) (.step T C π hπ) := ⟨hT,hCarrier⟩
  have hFullAdm : (geoTransformAlong (geometricTemplate (univ : Set X) E) T).IsAdmissibleCentre C := by
    refine ⟨hCarrier.1,?_,?_⟩
    · have hCos : (geoTransformAlong (geometricTemplate (univ : Set X) E) T).cosupp=univ := by
        rw [template_current,strict_univ]
        change cosupport n (univ : Set Y) (IdealWeightPowers.unitIdeal n Y) 0=univ
        rw [cosupport_zero (fun _ _ hg => hg)]
      rw [hCos]
      exact subset_univ C
    · rw [HironakaSharpActualCurveWholeBoundaryTransversality.actual_whole_ambient_boundary_ordered_dictionary W E T]
      exact hNC
  have hTestFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) (.step T C π hπ) := ⟨hFull,hFullAdm⟩
  have hRecorded := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  have hBorn := isSNCDivisor_of_sublist hRecorded.2.1 (List.sublist_append_right _ _)
  have hOld := isSNCDivisor_of_sublist hRecorded.2.1 (List.sublist_append_left _ _)
  have hResidual := (original_equimultiple_residual_step hn hW hE hdense q T hT hπ hCarrier
    (fun x hx => (hLevel x hx).1)).2
  refine ⟨hLevel,hNC,hTest,hTestFull,hResidual,?_,?_⟩
  · intro i hi
    let j : Fin (E.map (strictAlong T)).length := ⟨i.val,by simp⟩
    have hGet : (E.map (strictAlong T)).get j=strictAlong T (E.get i) := by simp [j]
    have hHi : IsClosedSubmanifold n (strictAlong T (E.get i)) := by
      rw [←hGet]
      exact MonomialPart.isClosedSubmanifold_get hn hOld j
    have hUnit : ∀ x ∈ C,(nonmonomialPartAlong n A.N
        (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E).mem x 1 := by
      intro x hx
      have hNm : nonmonomialPartAlong n A.N
          (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E=
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal :=
        (hRecorded.2.2.2.2 i).2.2.1
      rw [hNm]
      exact (hSelected i hi).2.2.2 x hx
    have hFactor := HironakaActualProcessedMaskControlledSum.actual_controlled_old_monomial_part
      hn hRecorded.1 hHi hBorn hRecorded.2.2.1 (hRecorded.2.2.2.2 i).2.1
      (hSelected i hi).2.1 (hSelected i hi).1 (hSelected i hi).2.2.1 hUnit hπ
    refine ⟨(hSelected i hi).2.2.1,(hSelected i hi).2.2.2,?_⟩
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · exact hFactor.symm
    · rfl
  · intro z hz i
    let J := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
    obtain ⟨hNi,_hEi,_hdi,hwi,hnzi,hpri⟩ := original_members_actual_finite_chronological_geometry
      hn hW hE hdense i T hT
    change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=A.N at hNi
    rw [hNi] at hnzi hpri
    have hLoc : ∀ x ∈ C,∀ᶠ y in 𝓝 x,y ∈ C → ordinaryTraceOrder A.N J y=ordinaryTraceOrder A.N J x := by
      intro x hx
      exact Eventually.of_forall fun y hy => ((hLevel y hy).2 i).trans ((hLevel x hx).2 i).symm
    have hStep := nextRelativeStrict_order_le_of_locally_constant_on_centre hn
      hRecorded.1 hwi.isCoherent hnzi hpri hπ hCarrier.subset_N hLoc (z := z) hz
    have hImage : π z ∈ A.N := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage
      hπ.contMDiff.continuous hRecorded.1.1 hz
    change ordinaryTraceOrder _ (nextRelativeStrict
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N J C π) z ≤ profile i
    rw [hNi]
    exact hStep.trans (hOrd (π z) hImage i)

end
end Hironaka.HironakaActualJointResidualMaskStep
