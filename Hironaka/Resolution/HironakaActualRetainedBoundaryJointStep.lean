import Hironaka.Resolution.HironakaActualJointResidualMaskStep
import Hironaka.Resolution.HironakaG4DistinctResidualCountTransform
import Hironaka.Resolution.HironakaG4ResidualInductionInputs
import Hironaka.Resolution.HironakaActualChronologicalDefectSharpBad

/-! Actual canonical joint profile steps with an ENTIRE retained initial born
boundary. This is the local operational core for genuine target-open profile
windows, not a restart on raw traces or a supplied future-state certificate.
Source-first proof: `hironaka-actual-retained-boundary-joint-step-20261101.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualRetainedBoundaryJointStep
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  NormalCrossings NormalCrossingsComparison SimultaneousNormalCrossings
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  HironakaG4PreparedCentreCoordinates HironakaG4MixedOldResidualStep
  HironakaActualFiniteMarkedSumHistories HironakaActualProcessedMaskControlledSum
  HironakaSharpActualFiniteMemberProduct HironakaSharpActualFiniteProductResidual
  HironakaSharpActualProductRelativeStrict HironakaSharpActualEquimultipleResidualHistory
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalFirstMemberResidualPrincipal
  HironakaSharpActualTraceIncidence HironakaSharpActualRelativeProductOrder
  HironakaG4IncidentOldBornStratumCentre HironakaG4EquimultipleRelativeOrder
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualChronologicalStrictStep
  HironakaSharpActualFiniteChronologicalHistory
  DivisorExponentAlong GermIdealOrder MonomialPartAlong

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual canonical residual rows with the retained born list, as a list in
exact original old order; no raw trace is substituted. -/
def canonicalResidualFamily (N : Set X) (old born : List (Set X)) : List (GermIdeal n X) :=
  old.map fun H => nonmonomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) born

/-- Actual normalized product, SAME retained born list, genuine mark q. -/
def canonicalProductMarked (N : Set X) (old born : List (Set X)) (q : ℕ) : MarkedIdeal n X :=
  ⟨N,born,relativeIdealListProduct N (canonicalResidualFamily N old born),q⟩

/-- Whole actual canonical old factor, with unchanged mark one. -/
def canonicalFactorMarked (N : Set X) (old born : List (Set X)) (i : Fin old.length) : MarkedIdeal n X :=
  ⟨N,born,oldMonomialPart N old born i,1⟩

/-- Actual NONUNIT old-factor positions among inactive original residual rows. -/
def inactiveCanonicalRows (N : Set X) (old born : List (Set X))
    (profile : Fin old.length → ℕ) (x : X) : Finset (Fin old.length) := by
  classical
  exact Finset.univ.filter fun i => profile i=0 ∧ ¬(oldMonomialPart N old born i).mem x 1

/-- Genuine finite marked SUM, including the bare product at the empty mask. -/
def jointProfileMarked (N : Set X) (old born : List (Set X)) (q : ℕ)
    (P : Finset (Fin old.length)) : MarkedIdeal n X :=
  finiteSum (canonicalProductMarked N old born q) (P.toList.map (canonicalFactorMarked N old born))

private theorem canonical_row_principal (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length)
    {x : X} (hx : x ∈ N) : ∃ c : X → ℂ,HolomorphicAt n c x ∧
      ∀ g,(oldResidualPart N old born i).mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=c) x g :=
  HironakaG4ResidualInductionInputs.actual_residual_principal_native hn hN hE hTr hdense i hx

private theorem canonical_product_geometry (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (q : ℕ) :
    let M := canonicalProductMarked N old born q
    M.IsWellFormed ∧ (∀ x ∈ N,IsNonzeroAlongAt N M.ideal x) ∧
      (∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,M.ideal.mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g) ∧
      (∀ x ∈ N,ordinaryTraceOrder N M.ideal x=
        ∑ i : Fin old.length,ordinaryTraceOrder N (oldResidualPart N old born i) x) ∧
      ∀ x ∈ N,∀ j : Fin born.length,x ∈ born.get j → ∃ f,M.ideal.mem x f ∧
        ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (born.get j)).mem x) x f := by
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hE hTr hdense i
  have hNParts (i : Fin old.length) := NonmonomialTransformAlong.parts_hypotheses hn
    (⟨N,born,oldTraceIdeal N old i,0⟩ : MarkedIdeal n X)
    ⟨hN,(hParts i).1,hBorn,hTr⟩ (hParts i).2.1
  have hRows : ∀ I ∈ canonicalResidualFamily N old born,
      I.IsCoherent ∧ (∀ x ∈ N,IsNonzeroAlongAt N I x) ∧
        (∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,I.mem x g ↔
          HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g) ∧
        ∀ x ∈ N,∀ j : Fin born.length,x ∈ born.get j → ∃ f,I.mem x f ∧
          ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (born.get j)).mem x) x f := by
    intro I hI
    obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hI
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    exact ⟨(hParts i).2.2.1,(hParts i).2.2.2.1,
      (fun _ hx => canonical_row_principal hn hN hE hTr hdense i hx),(hNParts i).2.2.2.2.1⟩
  have hp := relativeIdealListProduct_actual_geometry hN (canonicalResidualFamily N old born)
    (fun I hI => (hRows I hI).1) (fun I hI => (hRows I hI).2.1) (fun I hI => (hRows I hI).2.2.1)
  refine ⟨⟨hN,hp.1,hBorn,hTr⟩,hp.2.1,hp.2.2.1,?_,?_⟩
  · intro x hx
    have h := hp.2.2.2 x hx
    have hL : canonicalResidualFamily N old born=List.ofFn (oldResidualPart N old born) := by
      unfold canonicalResidualFamily
      conv_lhs => rw [←List.ofFn_get old,List.map_ofFn]
      rfl
    change ordinaryTraceOrder N (relativeIdealListProduct N (canonicalResidualFamily N old born)) x=_
    simpa only [hL,List.map_ofFn,List.sum_ofFn,Function.comp_apply] using h
  · exact relativeIdealListProduct_no_member_factor hn hBorn hTr (canonicalResidualFamily N old born)
      (fun I hI => (hRows I hI).1) (fun I hI => (hRows I hI).2.2.2)

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

private theorem joint_centre_geometry (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (P : Finset (Fin old.length)) (hP : ∀ i ∈ P,profile i=0)
    (hBound : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      (inactiveCanonicalRows N old born profile x).card ≤ P.card) :
    ResolutionInvariantSpec.IsInvDomain (n+1) (jointProfileMarked N old born q P) ∧
      ∀ C,(jointProfileMarked N old born q P).IsAdmissibleCentre C →
      (geometricTemplate N born).IsAdmissibleCentre C ∧
      HasNormalCrossings n C (old ++ born) ∧
      (∀ x ∈ C,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q ∧
        ∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x=profile i) ∧
      ∀ i ∈ P,(canonicalFactorMarked N old born i).IsAdmissibleCentre C ∧
        (⟨N,born,oldTraceIdeal N old i,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
        C ⊆ old.get i ∧ ∀ x ∈ C,(oldResidualPart N old born i).mem x 1 := by
  classical
  let R := canonicalProductMarked N old born q
  let L := P.toList.map (canonicalFactorMarked N old born)
  let D := oldMonomialPart N old born
  let J := oldResidualPart N old born
  let I := oldTraceIdeal N old
  have hp := canonical_product_geometry hn hN hE hTr hdense q
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  have hOld := isSNCDivisor_of_sublist hE (List.sublist_append_left _ _)
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hE hTr hdense i
  have hcI (i : Fin old.length) : (I i).IsCoherent := (hParts i).1
  have hcJ (i : Fin old.length) : (J i).IsCoherent := (hParts i).2.2.1
  have hnzJ (i : Fin old.length) : ∀ x ∈ N,IsNonzeroAlongAt N (J i) x := (hParts i).2.2.2.1
  have hcD (i : Fin old.length) : (D i).IsCoherent := (hParts i).2.2.2.2.1
  have hFac (i : Fin old.length) : I i=restrictOn n N ((D i).mul (J i)) := (hParts i).2.2.2.2.2.2.2
  have hHead : ResolutionInvariantSpec.IsInvDomain (n+1) R := by
    refine ⟨hp.1,?_,hq,hp.2.1⟩
    intro x hx
    obtain ⟨k,hk⟩ := hN.2 x hx
    exact ⟨k,hk.1.trans (Nat.le_succ n),hk⟩
  have hTail : ∀ M ∈ L,M.N=R.N ∧ M.E=R.E ∧ M.ideal.IsCoherent ∧ 1 ≤ M.d := by
    intro M hM
    obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hM
    exact ⟨rfl,rfl,hcD i,le_rfl⟩
  refine ⟨finiteSum_isInvDomain R L hHead hTail,?_⟩
  intro C hC
  have hEach : R.IsAdmissibleCentre C ∧ ∀ i ∈ P,(canonicalFactorMarked N old born i).IsAdmissibleCentre C := by
    have hCos := (finiteSum_history R L hN hp.1.isCoherent hq hTail
      (.refl : BlowupTower X X)).2 trivial |>.1
    have hAllCos : ∀ x ∈ C,∀ M ∈ R::L,x ∈ M.cosupp := by
      intro x hx
      have h := hC.2.1 hx
      change x ∈ (finiteSum R L).cosupp at h
      rw [←geoTransformAlong_refl (finiteSum R L),hCos] at h
      simp only [geoTransformAlong_refl] at h
      exact h
    have hEB : (finiteSum R L).E=R.E := (finiteSum_geometry R L hp.1.isCoherent hq hTail).2.1
    have hNC : HasNormalCrossings n C R.E := hEB ▸ hC.2.2
    refine ⟨⟨hC.1,fun x hx => hAllCos x hx R (by simp),hNC⟩,?_⟩
    intro i hi
    exact ⟨hC.1,fun x hx => hAllCos x hx _
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,Finset.mem_toList.mpr hi,rfl⟩)),hNC⟩
  have hCN : C ⊆ N := hEach.1.subset_N
  have hLevels : ∀ x ∈ C,ordinaryTraceOrder N R.ideal x=q ∧
      ∀ i,ordinaryTraceOrder N (J i) x=profile i := by
    intro x hx
    have hSum := hp.2.2.2.1 x (hCN hx)
    have hGe := (ordinaryTraceOrder_cosupport_iff hN hp.1.isCoherent hp.2.1 (hCN hx) q).mp
      (hEach.1.2.1 hx)
    change q ≤ ordinaryTraceOrder N R.ideal x at hGe
    have hLe : (∑ i,ordinaryTraceOrder N (J i) x) ≤ ∑ i,profile i :=
      Finset.sum_le_sum (fun i _ => hOrd x (hCN hx) i)
    have hEq : (∑ i,ordinaryTraceOrder N (J i) x)=∑ i,profile i := by
      change ordinaryTraceOrder N R.ideal x=∑ i,ordinaryTraceOrder N (J i) x at hSum
      omega
    refine ⟨hSum.trans (hEq.trans hsum),?_⟩
    exact fun i => (Finset.sum_eq_sum_iff_of_le (fun i _ => hOrd x (hCN hx) i)).mp hEq i (Finset.mem_univ i)
  have hUnitJ (i : Fin old.length) (hi : profile i=0) {x : X} (hx : x ∈ N) : (J i).mem x 1 := by
    apply unit_of_order_zero hN (hcJ i) (hnzJ i) hx
    have h := hOrd x hx i
    rw [hi] at h
    exact Nat.eq_zero_of_le_zero h
  have hAtC (x : X) (hx : x ∈ C) : inactiveCanonicalRows N old born profile x=P := by
    have hSub : P ⊆ inactiveCanonicalRows N old born profile x := by
      intro i hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hP i hi,?_⟩
      intro hu
      have hCos := (hEach.2 i hi).2.1 hx
      change x ∈ cosupport n N (D i) 1 at hCos
      rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcD i) hg)] at hCos
      exact one_ne_zero (hCos.2 1 hu)
    exact (Finset.eq_of_subset_of_card_le hSub (hBound x (hCN hx) (hLevels x hx).1)).symm
  have hHi (i : Fin old.length) : IsClosedSubmanifold n (old.get i) :=
    MonomialPart.isClosedSubmanifold_get hn hOld i
  have hOldOfCos (i : Fin old.length) {x : X} (hx : x ∈ N)
      (hCos : x ∈ cosupport n N (D i) 1 ∨ x ∈ cosupport n N (J i) 1) : x ∈ old.get i := by
    have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal (hHi i)
    have hZero : x ∈ (I i).zeroLocus := by
      rcases hCos with hCos | hCos
      · rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcD i) hg)] at hCos
        exact fun g hg => hCos.2 g (le_monomialPartAlong hn hBorn hTr (hcI i) x g hg)
      · rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcJ i) hg)] at hCos
        exact fun g hg => hCos.2 g (NonmonomialTransformAlong.le_nonmonomialPartAlong_self (hcI i) x g hg)
    have hRaw := (zeroLocus_restrictOn_iff hcH hx).mp hZero
    rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (hHi i).1] at hRaw
  have hContained (i : Fin old.length) (hi : 0 < profile i ∨ i ∈ P) : C ⊆ old.get i := by
    intro x hx
    apply hOldOfCos i (hCN hx)
    rcases hi with hi | hi
    · apply Or.inr
      apply (ordinaryTraceOrder_cosupport_iff hN (hcJ i) (hnzJ i) (hCN hx) 1).mpr
      rw [(hLevels x hx).2 i]
      omega
    · exact Or.inl ((hEach.2 i hi).2.1 hx)
  have hAbsent (i : Fin old.length) (hi : profile i=0) (hiP : i ∉ P)
      {x : X} (hx : x ∈ C) : x ∉ old.get i := by
    have huD : (D i).mem x 1 := by
      by_contra hu
      have hMem : i ∈ inactiveCanonicalRows N old born profile x :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hu⟩
      rw [hAtC x hx] at hMem
      exact hiP hMem
    have huJ := hUnitJ i hi (hCN hx)
    have huMul : ((D i).mul (J i)).mem x 1 := by
      change IsInSpanAt (n := n) (fun f => ∃ a b,(D i).mem x a ∧ (J i).mem x b ∧ f=a*b) x 1
      exact InvertibleIdealQuotient.isInSpanAt_self ⟨1,1,huD,huJ,by simp⟩ (holomorphicAt_const 1)
    have huI : (I i).mem x 1 := by
      rw [hFac]
      exact le_restrictOn (IdealWeightPowers.isCoherent_mul (hcD i) (hcJ i)) x 1 huMul
    intro hxH
    have hz : x ∈ (I i).zeroLocus := (zeroLocus_restrictOn_iff
      (VanishingIdealCoherent.isCoherent_vanishingIdeal (hHi i)) (hCN hx)).mpr
      (by rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (hHi i).1])
    exact one_ne_zero (hz 1 huI)
  have hNC : HasNormalCrossings n C (old ++ born) := by
    intro x hx
    apply actual_incident_old_normalCrossingsAt hE hEach.1.2.2 hx
    intro i hi
    by_cases hpos : 0 < profile i
    · exact Eventually.of_forall fun _ hy => hContained i (Or.inl hpos) hy
    · by_cases hiP : i ∈ P
      · exact Eventually.of_forall fun _ hy => hContained i (Or.inr hiP) hy
      · exact False.elim (hAbsent i (by omega) hiP hx hi)
  have hCarrier : (geometricTemplate N born).IsAdmissibleCentre C := by
    refine ⟨hC.1,?_,hEach.1.2.2⟩
    change C ⊆ cosupport n N (IdealWeightPowers.unitIdeal n X) 0
    rw [cosupport_zero (fun _ _ hg => hg)]
    exact hCN
  refine ⟨hCarrier,hNC,hLevels,?_⟩
  intro i hi
  have hDadm := hEach.2 i hi
  have hIadm : (⟨N,born,I i,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C := by
    refine ⟨hDadm.1,?_,hDadm.2.2⟩
    intro x hx
    have hCos := hDadm.2.1 hx
    change x ∈ cosupport n N (D i) 1 at hCos
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcD i) hg)] at hCos
    change x ∈ cosupport n N (I i) 1
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcI i) hg)]
    exact ⟨hCN hx,fun g hg => hCos.2 g (le_monomialPartAlong hn hBorn hTr (hcI i) x g hg)⟩
  exact ⟨hDadm,hIadm,hContained i (Or.inr hi),fun x hx => hUnitJ i (hP i hi) (hCN hx)⟩

private theorem canonical_product_next_relative (hn : 0 < n) {N C : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    (hCNC : HasNormalCrossings n C (old ++ born)) (q : ℕ) :
    (canonicalProductMarked (geoStrictTransform π C N) (old.map (geoStrictTransform π C))
      (born.map (geoStrictTransform π C) ++ [π ⁻¹' C]) q).ideal=
        nextRelativeStrict N (canonicalProductMarked N old born q).ideal C π := by
  let N' := geoStrictTransform π C N
  let B' := born.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  have hRows : ∀ I ∈ canonicalResidualFamily N old born,
      I.IsCoherent ∧ (∀ x ∈ N,IsNonzeroAlongAt N I x) ∧
        ∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,I.mem x g ↔
          HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g := by
    intro I hI
    obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hI
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    have h := actual_old_parts_geometry hn hN hE hTr hdense i
    exact ⟨h.2.2.1,h.2.2.2.1,fun _ hx => canonical_row_principal hn hN hE hTr hdense i hx⟩
  have hList : canonicalResidualFamily N' (old.map (geoStrictTransform π C)) B'=
      (canonicalResidualFamily N old born).map (fun I => nextRelativeStrict N I C π) := by
    unfold canonicalResidualFamily
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro H hH
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    exact (actual_mixed_old_residual_step hn hN hE hTr hdense i hπ hCN hCNC).2.2
  change relativeIdealListProduct N' (canonicalResidualFamily N' (old.map (geoStrictTransform π C)) B')=_
  rw [hList]
  exact (nextRelativeStrict_relative_product_eq hn hN hπ hCN (canonicalResidualFamily N old born)
    (fun I hI => (hRows I hI).1) (fun I hI => (hRows I hI).2.1) (fun I hI => (hRows I hI).2.2)).symm

/-- Genuine actual joint step with ENTIRE retained initial born boundary.
Selected residual units/full old legality/whole factor records and all-point
actual row/count nonincrease are derived; no future comparison is an input. -/
theorem actual_retained_boundary_joint_step (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (P : Finset (Fin old.length)) (hP : ∀ i ∈ P,profile i=0)
    (hBound : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      (inactiveCanonicalRows N old born profile x).card ≤ P.card) :
    ResolutionInvariantSpec.IsInvDomain (n+1) (jointProfileMarked N old born q P) ∧
      ∀ (C : Set X) (π : Y → X) (hπ : IsBlowupAlong n C π),
        (jointProfileMarked N old born q P).IsAdmissibleCentre C →
      let N' := geoStrictTransform π C N
      let B' := born.map (geoStrictTransform π C) ++ [π ⁻¹' C]
      (∀ x ∈ C,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q ∧
        ∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x=profile i) ∧
      HasNormalCrossings n C (old ++ born) ∧
      IsGeoTestTower (geometricTemplate N born) (.step .refl C π hπ) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) (.step .refl C π hπ) ∧
      MarkedIdeal.RestrictEquiv ((canonicalProductMarked N old born q).geoTransform C π)
        (canonicalProductMarked N' (old.map (geoStrictTransform π C)) B' q) ∧
      (∀ i ∈ P,C ⊆ old.get i ∧ (∀ x ∈ C,(oldResidualPart N old born i).mem x 1) ∧
        (canonicalFactorMarked N old born i).geoTransform C π=
          (⟨N',B',monomialPartAlong n N'
            (restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform π C (old.get i)))) B',1⟩ :
            MarkedIdeal n Y)) ∧
      (∀ i : Fin old.length,nonmonomialPartAlong n N'
        (restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform π C (old.get i)))) B'=
          nextRelativeStrict N (oldResidualPart N old born i) C π) ∧
      (∀ z ∈ N',∀ i : Fin old.length,ordinaryTraceOrder N'
        (nonmonomialPartAlong n N'
          (restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform π C (old.get i)))) B') z ≤
            ordinaryTraceOrder N (oldResidualPart N old born i) (π z)) ∧
      ∀ z : Y,actualDistinctProperCount (fun i : Fin old.length => nonmonomialPartAlong n N'
        (restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform π C (old.get i)))) B') z ≤
          actualDistinctProperCount (oldResidualPart N old born) (π z) := by
  have hG := joint_centre_geometry hn hN hE hTr hdense profile q hq hsum hOrd P hP hBound
  refine ⟨hG.1,?_⟩
  intro C π hπ hAdm
  dsimp only
  obtain ⟨hCarrier,hNC,hLevels,hSelected⟩ := hG.2 C hAdm
  let N' := geoStrictTransform π C N
  let B' := born.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  let R := canonicalProductMarked N old born q
  have hp := canonical_product_geometry hn hN hE hTr hdense q
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  have hOld := isSNCDivisor_of_sublist hE (List.sublist_append_left _ _)
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hE hTr hdense i
  have hFullAdm : (geometricTemplate (univ : Set X) (old ++ born)).IsAdmissibleCentre C := by
    refine ⟨hCarrier.1,?_,hNC⟩
    change C ⊆ cosupport n (univ : Set X) (IdealWeightPowers.unitIdeal n X) 0
    rw [cosupport_zero (fun _ _ hg => hg)]
    exact subset_univ C
  have hProdAdm : R.IsAdmissibleCentre C := by
    refine ⟨hCarrier.1,?_,hCarrier.2.2⟩
    intro x hx
    exact (ordinaryTraceOrder_cosupport_iff hN hp.1.isCoherent hp.2.1 (hCarrier.subset_N hx) q).mpr
      (hLevels x hx).1.ge
  have hUpper : ∀ x ∈ C,x ∉ cosupport n N R.ideal (R.d+1) := by
    intro x hx hh
    have h := (ordinaryTraceOrder_cosupport_iff hN hp.1.isCoherent hp.2.1
      (hCarrier.subset_N hx) (q+1)).mp hh
    rw [(hLevels x hx).1] at h
    omega
  have hProduct := equimultiple_geoTransform_restrictEquiv_nextRelativeStrict hn R hp.1 hp.2.1 hp.2.2.1
    hProdAdm hπ hUpper hp.2.2.2.2
  have hNextProduct : (canonicalProductMarked N' (old.map (geoStrictTransform π C)) B' q).ideal=
      nextRelativeStrict N R.ideal C π := canonical_product_next_relative hn hN hE hTr hdense hπ hCarrier.subset_N hNC q
  change MarkedIdeal.RestrictEquiv (R.geoTransform C π)
    (⟨N',B',nextRelativeStrict N R.ideal C π,q⟩ : MarkedIdeal n Y) at hProduct
  rw [←hNextProduct] at hProduct
  have hNextRow (i : Fin old.length) : nonmonomialPartAlong n N'
      (restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform π C (old.get i)))) B'=
        nextRelativeStrict N (oldResidualPart N old born i) C π :=
    (actual_mixed_old_residual_step hn hN hE hTr hdense i hπ hCarrier.subset_N hNC).2.2
  refine ⟨hLevels,hNC,⟨trivial,hCarrier⟩,⟨trivial,hFullAdm⟩,hProduct,?_,hNextRow,?_,?_⟩
  · intro i hi
    have hFactor := actual_controlled_old_monomial_part hn hN
      (MonomialPart.isClosedSubmanifold_get hn hOld i) hBorn hTr (hParts i).2.1
      (hSelected i hi).2.1 (hSelected i hi).1 (hSelected i hi).2.2.1 (hSelected i hi).2.2.2 hπ
    refine ⟨(hSelected i hi).2.2.1,(hSelected i hi).2.2.2,?_⟩
    exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hFactor.symm rfl
  · intro z hz i
    rw [hNextRow]
    have hLoc : ∀ x ∈ C,∀ᶠ y in 𝓝 x,y ∈ C →
        ordinaryTraceOrder N (oldResidualPart N old born i) y=
          ordinaryTraceOrder N (oldResidualPart N old born i) x :=
      fun x hx => Eventually.of_forall fun y hy => ((hLevels y hy).2 i).trans ((hLevels x hx).2 i).symm
    exact nextRelativeStrict_order_le_of_locally_constant_on_centre hn hN
      (hParts i).2.2.1 (hParts i).2.2.2.1 (fun _ hx => canonical_row_principal hn hN hE hTr hdense i hx)
      hπ hCarrier.subset_N hLoc (z := z) hz
  · intro z
    have hFamily : (fun i : Fin old.length => nonmonomialPartAlong n (geoStrictTransform π C N)
        (restrictOn n (geoStrictTransform π C N)
          (vanishingIdeal (n := n) (geoStrictTransform π C (old.get i))))
        (born.map (geoStrictTransform π C) ++ [π ⁻¹' C]))=
          (fun i => nextRelativeStrict N (oldResidualPart N old born i) C π) := by
      funext i
      exact hNextRow i
    rw [hFamily]
    exact HironakaG4DistinctResidualCountTransform.actual_distinct_proper_count_nextRelativeStrict_le
      N C π (oldResidualPart N old born) z

end
end Hironaka.HironakaActualRetainedBoundaryJointStep
