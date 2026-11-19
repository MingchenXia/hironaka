import Hironaka.Resolution.HironakaG4PreparedResidualTotalNoFactor
import Hironaka.Resolution.HironakaG4SelectedBornCanonicalColumns
import Hironaka.Resolution.HironakaG4CanonicalZeroRowUnit
import Hironaka.Resolution.HironakaG4MixedOldResidualStep
import Hironaka.Resolution.HironakaG4ActiveMonomialSharpBad
import Hironaka.Resolution.HironakaG4MonomialActiveCleanup
import Hironaka.Resolution.HironakaG4RecordedTowerResidualCompatibility

set_option autoImplicit false

/-! Genuine prepared mixed selected step: actual whole old strict traces,
canonical D/J readback and the all-slot canonical D matrix. Complete source-first
chapter: hironaka-g4-prepared-mixed-selected-step.tex. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG4PreparedMixedSelectedStep

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance SimultaneousNormalCrossings
  BoundaryCount MemberInterAlong MonomialPart MonomialPartAlong
  BlowupStrictSubmanifold HironakaG4CommonMonomialChart
  HironakaG4PreparedCentreCoordinates HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4MonomialFamilyInvariant HironakaG4MonomialMaximalContact
  HironakaG4MonomialCoefficientDeletion DivisorExponentAlong GermIdealOrder
  RelativePrincipalizationSpan InvertibleIdealQuotient RestrictedIdealWeight
  HironakaSharpActualStrictTraceOpenNonmonomial HironakaMonomialBlowup MonomialPartEtale
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupRestrictOpen
  DerivativeIdealAlongEtale BlowupSNCTransform
  HironakaSharpActualControlledRelativeSaturation HironakaSharpOriginalFirstMemberExceptionalFactor
  IdealWeightPowers NonmonomialStepAlong NonmonomialTransformAlong
  HironakaSharpActualTraceIncidence
  RestrictedIdealExtension MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong

variable {n : ℕ} {X : CMfd.{u} n}

private theorem restrictOn_monomialPartAlong (N : Set X)
    (I : GermIdeal n X) (E : List (Set X)) :
    restrictOn n N (monomialPartAlong n N I E) = monomialPartAlong n N I E := by
  ext y g
  constructor
  · rintro ⟨hg,hspan⟩
    exact ⟨hg,fun i hyN hyi => IsInSpanOnAt.trans (fun a ha => ha.2 i hyN hyi) hspan⟩
  · intro hg
    exact ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩

private theorem open_parts_pullback (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (U : Opens X) (i : Fin old.length) :
    let NU := (Subtype.val : U → X) ⁻¹' N
    let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    let IU := restrictOn n NU (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' old.get i))
    monomialPartAlong n NU IU bornU = GermIdeal.pullback (m := n) (Subtype.val : U → X)
      (oldMonomialPart N old born i) ∧
    nonmonomialPartAlong n NU IU bornU = GermIdeal.pullback (m := n) (Subtype.val : U → X)
      (oldResidualPart N old born i) := by
  have hOld := isSNCDivisor_of_sublist hE (List.sublist_append_left old born)
  obtain ⟨hcI,_hnzI,hcJ,_hnzJ,hcD,_hnzD,_hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  have hIU := actual_normalized_trace_whole_open_pullback hN
    (MonomialPart.isClosedSubmanifold_get hn hOld i) U
  dsimp only
  rw [hIU]
  exact ⟨(pullback_monomialPartAlong
    (fun y : U => ⟨openInv U y,isLocalInverseAt_val U y⟩)
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcI hg)).symm,
    (pullback_nonmonomialPartAlong
      (fun y : U => ⟨openInv U y,isLocalInverseAt_val U y⟩) hcI hcD hcJ).symm⟩

private theorem open_full_density {N : Set X} {E : List (Set X)}
    (hdense : N ⊆ closure (N \ ⋃ H ∈ E,H)) (U : Opens X) :
    (Subtype.val : U → X) ⁻¹' N ⊆ closure ((Subtype.val : U → X) ⁻¹' N \
      ⋃ H ∈ E.map ((Subtype.val : U → X) ⁻¹' ·),H) := by
  intro y hy
  have hp : y ∈ (Subtype.val : U → X) ⁻¹' closure (N \ ⋃ H ∈ E,H) := hdense hy
  erw [U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    continuous_subtype_val (N \ ⋃ H ∈ E,H)] at hp
  convert hp using 1
  congr 1
  ext z
  simp

private theorem current_prepared_open (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ y ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) y ≤ 1)
    (hPrepared : ∀ y ∈ N,IsPreparedResidualSNCAt N old born y) (U : Opens X) :
    let NU := (Subtype.val : U → X) ⁻¹' N
    let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
    let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    (∀ y ∈ NU,∀ i,ordinaryTraceOrder NU
      (oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU i) y ≤ 1) ∧
    ∀ y ∈ NU,IsPreparedResidualSNCAt (X := CMfd.of (n := n) U) NU oldU bornU y := by
  let NU := (Subtype.val : U → X) ⁻¹' N
  let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let cO : Fin oldU.length → Fin old.length := Fin.cast (by simp [oldU])
  let cB : Fin bornU.length → Fin born.length := Fin.cast (by simp [bornU])
  let c : Fin oldU.length ⊕ Fin bornU.length → Fin old.length ⊕ Fin born.length := Sum.map cO cB
  have hO (i : Fin oldU.length) : oldU.get i = (Subtype.val : U → X) ⁻¹' old.get (cO i) :=
    get_map_preimage old i
  have hB (i : Fin bornU.length) : bornU.get i = (Subtype.val : U → X) ⁻¹' born.get (cB i) :=
    get_map_preimage born i
  have hJ (i : Fin oldU.length) :
      oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU i =
        GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born (cO i)) := by
    change nonmonomialPartAlong n NU (restrictOn n NU (vanishingIdeal (n := n) (oldU.get i))) bornU = _
    rw [hO]
    exact (open_parts_pullback hn hN hE hTr hdense U (cO i)).2
  have hNU := isClosedSubmanifold_preimage_val hN U
  have hFullU : IsSNCDivisor n (oldU ++ bornU) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hTrU : IsTransverse n NU bornU := isTransverse_preimage (pullsBackCoordinates_val U) hTr
  have hDenseU : NU ⊆ closure (NU \ ⋃ H ∈ oldU ++ bornU,H) := by
    simpa only [List.map_append] using open_full_density hdense U
  have hPartsU := fun i => actual_old_parts_geometry (X := CMfd.of (n := n) U)
    hn hNU hFullU hTrU hDenseU i
  have hParts := fun i => actual_old_parts_geometry hn hN hE hTr hdense i
  refine ⟨?_,?_⟩
  · intro y hy i
    by_contra ho
    have hTwo : 2 ≤ ordinaryTraceOrder NU
        (oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU i) y :=
      Nat.succ_le_of_lt (Nat.lt_of_not_ge ho)
    have hMem := (ordinaryTraceOrder_cosupport_iff hNU (hPartsU i).2.2.1
      (hPartsU i).2.2.2.1 hy 2).mpr hTwo
    rw [hJ,cosupport_pullback_of_local
      (fun z : U => ⟨openInv U z,isLocalInverseAt_val U z⟩)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hParts (cO i)).2.2.1 hg)] at hMem
    have hLower := (ordinaryTraceOrder_cosupport_iff hN (hParts (cO i)).2.2.1
      (hParts (cO i)).2.2.2.1 hy 2).mp hMem
    have hUpper := hOrd y.val hy (cO i)
    omega
  · intro y hy
    have hSupport (a : Fin oldU.length ⊕ Fin bornU.length) :
        preparedSupport (X := CMfd.of (n := n) U) NU oldU bornU a =
          (Subtype.val : U → X) ⁻¹' preparedSupport N old born (c a) := by
      cases a with
      | inl i =>
        simp only [preparedSupport,Sum.elim_inl,c,Sum.map_inl]
        rw [hJ,BlowupExceptionalDivisor.zeroLocus_pullback
          contMDiff_subtype_val (hParts (cO i)).2.2.1]
        rfl
      | inr i =>
        simp only [preparedSupport,Sum.elim_inr,c,Sum.map_inr]
        rw [hB]
        rfl
    have hcInj : Function.Injective c := by
      intro a b hab
      cases a <;> cases b <;> simp_all [c,cO,cB,Fin.ext_iff]
    obtain ⟨S₀,p,hFam,hFree,hInj⟩ := hPrepared y.val hy
    refine ⟨S₀,p ∘ c,?_,?_,?_⟩
    · apply IsCoordinateFamilyAt.reindex (isCoordinateFamilyAt_preimage_val_iff.mpr hFam)
        (Option.map c)
      · rintro (_ | a)
        · rfl
        · exact hSupport a
      · rintro (_ | a) <;> rfl
    · intro a ha
      apply hFree (c a)
      exact show y ∈ (Subtype.val : U → X) ⁻¹' preparedSupport N old born (c a) from
        (hSupport a) ▸ ha
    · intro a ha b hb hab
      apply hcInj
      have ha' : (y : X) ∈ preparedSupport N old born (c a) := by
        change y ∈ (Subtype.val : U → X) ⁻¹' preparedSupport N old born (c a)
        rw [←hSupport]
        exact ha
      have hb' : (y : X) ∈ preparedSupport N old born (c b) := by
        change y ∈ (Subtype.val : U → X) ⁻¹' preparedSupport N old born (c b)
        rw [←hSupport]
        exact hb
      exact hInj ha' hb' hab

private theorem trace_eq_residual_of_monomial_unit (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length)
    (hOne : ∀ y,(oldMonomialPart N old born i).mem y (fun _ => (1 : ℂ))) :
    oldTraceIdeal N old i = oldResidualPart N old born i := by
  obtain ⟨_hcI,_hnzI,hcJ,_hnzJ,hcD,_hnzD,_hmD,hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  have hD : oldMonomialPart N old born i = unitIdeal n X := by
    ext y g
    change (oldMonomialPart N old born i).mem y g ↔ HolomorphicAt n g y
    constructor
    · exact fun hg => hg.1
    · intro hg
      exact HomogenizedIdeal.mem_of_isInSpanAt hcD (isInSpanAt_of_eq_mul
        (hOne y) hg hg (Eventually.of_forall fun _ => by simp))
  have hNorm : restrictOn n N (oldResidualPart N old born i) = oldResidualPart N old born i := by
    ext y g
    exact restrictOn_colonAlong_mem_iff N (oldTraceIdeal N old i)
      (oldMonomialPart N old born i) (fun _ ha => ha.1) g
  rw [hD,BlowupControlledTransform.unitIdeal_mul hcJ,hNorm] at hWhole
  exact hWhole

private theorem inactive_old_centre_transverse (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ y ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) y ≤ 1)
    (hPrepared : ∀ y ∈ N,IsPreparedResidualSNCAt N old born y)
    (S : Finset (Fin born.length)) (hCNC : HasNormalCrossings n (N ∩ memberInter born S) (old ++ born))
    (i : Fin old.length) (hOne : ∀ y,(oldMonomialPart N old born i).mem y (fun _ => (1 : ℂ))) :
    IsTransverse n (N ∩ memberInter born S) [old.get i] := by
  have hIJ := trace_eq_residual_of_monomial_unit hn hN hE hTr hdense i hOne
  have hcI := (actual_old_parts_geometry hn hN hE hTr hdense i).1
  have hOld := isSNCDivisor_of_sublist hE (List.sublist_append_left old born)
  have hH := MonomialPart.isClosedSubmanifold_get hn hOld i
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hH
  have hCSingle : HasNormalCrossings n (N ∩ memberInter born S) [old.get i] := by
    apply hasNormalCrossings_of_forall_mem hCNC
    intro H hH
    rw [List.mem_singleton.mp hH]
    exact List.mem_append_left born (List.get_mem old i)
  intro y hy
  apply HironakaSharpNestedNormalCrossingsInheritance.exists_actual_free_family_of_germ_noncontainment
    hy (hCSingle y hy)
  intro k _hk hContains
  have hGet : [old.get i].get k = old.get i := by
    simpa only [List.mem_singleton] using List.get_mem [old.get i] k
  obtain ⟨c,hc,hFreq⟩ :=
    HironakaG4PreparedResidualTotalNoFactor.exists_residual_nonzero_on_selected_born_centre
      hn hN hE hTr hdense S hy (hOrd y hy.1) (hPrepared y hy.1) i
  rw [←hIJ] at hc
  have hZero : ∀ᶠ q in 𝓝 y,q ∈ N ∩ memberInter born S → c q=0 := by
    filter_upwards [hContains,HadamardBridge.eventually_mem_of_isCoherent hcI hc] with q hqH hqc hq
    have hqH' : q ∈ old.get i := by simpa only [hGet] using hqH hq
    have hRaw : q ∈ (vanishingIdeal (n := n) (old.get i)).zeroLocus := by
      rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hH.1]
    exact ((zeroLocus_restrictOn_iff hcH hq.1).mpr hRaw) c hqc
  obtain ⟨q,hq,hZeroq⟩ := (hFreq.and_eventually hZero).exists
  exact hq.2 (hZeroq hq.1)

private theorem masked_whole_strict_trace (hn : 0 < n) {N H C : Set X}
    (hN : IsClosedSubmanifold n N) (hH : IsClosedSubmanifold n H)
    {E : List (Set X)} {d : ℕ} {Y : CMfd.{u} n} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    (hCases : (d=1 ∧ C ⊆ H) ∨ (d=0 ∧ IsSNCDivisor n [H] ∧ IsTransverse n C [H])) :
    ((markedRow N E (restrictOn n N (vanishingIdeal (n := n) H)) d).geoTransform C π).ideal =
      restrictOn n (geoStrictTransform π C N)
        (vanishingIdeal (n := n) (geoStrictTransform π C H)) := by
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hH
  have hcI := isCoherent_restrictOn_of_isClosedSubmanifold hcH hN
  have hNorm : MarkedIdeal.RestrictEquiv
      (markedRow N E (restrictOn n N (vanishingIdeal (n := n) H)) d)
      (markedRow N E (vanishingIdeal (n := n) H) d) :=
    ⟨rfl,rfl,rfl,restrictLe_restrictOn,restrictLe_self_restrictOn hcH⟩
  have hEq := congrArg MarkedIdeal.ideal (hNorm.geoTransform_eq (C := C) hN.1 hcI hcH hπ.contMDiff)
  rw [hEq]
  rcases hCases with ⟨rfl,hCH⟩ | ⟨rfl,hSingle,hFree⟩
  · exact HironakaSharpActualFirstAmbientStrictTraceFactor.actual_first_controlled_ambient_strict_trace
      hN hH hπ hCN hCH
  · rw [geoTransform_zeroMark_ideal_eq_restricted_total _ rfl C π]
    change restrictOn n (geoStrictTransform π C N)
      (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)) = _
    rw [HironakaG4TransverseBoundaryStrictPullback.pullback_vanishingIdeal_eq_strict_of_transverse
      hn hSingle hFree hπ]

private theorem controlled_normalized (M : MarkedIdeal n X) {C : Set X}
    {Y : CMfd.{u} n} {π : Y → X} (hπ : IsBlowupAlong n C π) :
    restrictOn n (geoStrictTransform π C M.N) (M.geoTransform C π).ideal =
      (M.geoTransform C π).ideal := by
  have hcDen := GermIdealPullbackCalculus.isCoherent_idealPow
    (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff
      (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ)) M.d
  ext z g
  exact restrictOn_colonAlong_mem_iff _ _ _
    (fun _ ha => GermIdeal.IsCoherent.holomorphicAt_mem hcDen ha) g

private theorem controlled_canonical_parts_factor (hn : 0 < n)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hne : ∀ y ∈ M.N,IsNonzeroAlongAt M.N M.ideal y) {C : Set X}
    (hC : M.IsAdmissibleCentre C)
    (hD : (markedRow (X := X) M.N M.E (monomialPartAlong n M.N M.ideal M.E) M.d).IsAdmissibleCentre C)
    {Y : CMfd.{u} n} {π : Y → X} (hπ : IsBlowupAlong n C π) :
    let J := nonmonomialPartAlong n M.N M.ideal M.E
    let D := monomialPartAlong n M.N M.ideal M.E
    (M.geoTransform C π).ideal = restrictOn n (geoStrictTransform π C M.N)
      ((nextTotalMarked M.N J C π).ideal.mul
        ((markedRow (X := X) M.N M.E D M.d).geoTransform C π).ideal) := by
  let J := nonmonomialPartAlong n M.N M.ideal M.E
  let D := monomialPartAlong n M.N M.ideal M.E
  obtain ⟨hcJ,hcD,_hnzD,_hmD,_hNo,_hnzJ,hEquiv⟩ := parts_hypotheses hn M hM hne
  have hProduct := hEquiv.isAdmissibleCentre_iff.mp hC
  have hJ : (markedRow (X := X) M.N M.E J 0).IsAdmissibleCentre C := by
    refine ⟨hπ.1,?_,hC.2.2⟩
    change C ⊆ cosupport n M.N J 0
    rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcJ hg)]
    exact hC.subset_N
  have hcG := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre
    (𝔪 := markedRow (X := X) M.N M.E D M.d) hM.isClosedSubmanifold_N hcD hD hπ
  have hFactor : monomialFactor n π C M.N M.E D 0 M.d =
      ((markedRow (X := X) M.N M.E D M.d).geoTransform C π).ideal := by
    unfold monomialFactor
    simp only [Nat.zero_sub,Nat.sub_zero,idealPow_zero]
    exact BlowupControlledTransform.unitIdeal_mul hcG
  have hTransform := congrArg MarkedIdeal.ideal
    (hEquiv.geoTransform_eq hM.isClosedSubmanifold_N.1 hM.isCoherent
      (IdealWeightPowers.isCoherent_mul hcJ hcD) (C := C) hπ.contMDiff)
  obtain ⟨hf,hb⟩ := restrictLe_geoTransform_mul hπ hM.isClosedSubmanifold_N M.E hcJ hcD
    (o := 0) (d := M.d) hJ (by simpa only [Nat.sub_zero,markedRow] using hD) hProduct
  rw [hFactor] at hf hb
  change RestrictLe (geoStrictTransform π C M.N)
    ((⟨M.N,M.E,J.mul D,M.d⟩ : MarkedIdeal n X).geoTransform C π).ideal
    ((nextTotalMarked M.N J C π).ideal.mul
      ((markedRow (X := X) M.N M.E D M.d).geoTransform C π).ideal) at hf
  change RestrictLe (geoStrictTransform π C M.N)
    ((nextTotalMarked M.N J C π).ideal.mul
      ((markedRow (X := X) M.N M.E D M.d).geoTransform C π).ideal)
    ((⟨M.N,M.E,J.mul D,M.d⟩ : MarkedIdeal n X).geoTransform C π).ideal at hb
  rw [←hTransform] at hf hb
  have hWhole := restrictOn_eq_of_restrictLe isClosed_closure hf hb
  exact (controlled_normalized M hπ).symm.trans hWhole

private theorem exists_prepared_window (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ y ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) y ≤ 1)
    (hPrepared : ∀ y ∈ N,IsPreparedResidualSNCAt N old born y)
    {x : X} (hxN : x ∈ N) (S : Finset (Fin born.length)) (hS : S.Nonempty)
    (hSJ : S ⊆ Finset.univ.filter (fun j => x ∈ born.get j))
    (hFeasible : ∀ i ∈ properRows (fun (i : Fin old.length) (j : Fin born.length) =>
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) x),
      1 ≤ ∑ j ∈ S,divExpAlong n N (oldMonomialPart N old born i) (born.get j) x) :
    let A := fun (i : Fin old.length) (j : Fin born.length) =>
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) x
    ∃ (U : Opens X) (hxU : x ∈ U),
      let NU := (Subtype.val : U → X) ⁻¹' N
      let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
      let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
      let e : Fin born.length ↪ Fin bornU.length := (finCongr (by simp [bornU])).toEmbedding
      let CU := NU ∩ memberInter bornU (S.map e)
      let IU := fun i : Fin old.length => restrictOn n NU
        (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' old.get i))
      let DU := fun i => monomialPartAlong n NU (IU i) bornU
      let d := fun i => if i ∈ properRows A then 1 else 0
      CU=(Subtype.val : U → X) ⁻¹' (N ∩ memberInter born S) ∧
      (⟨x,hxU⟩ : U) ∈ CU ∧ IsClosedSubmanifold n CU ∧ interior CU=∅ ∧
      HasNormalCrossings n CU (oldU ++ bornU) ∧
      (∀ y ∈ NU,∀ i,ordinaryTraceOrder NU
        (oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU i) y ≤ 1) ∧
      (∀ y ∈ NU,IsPreparedResidualSNCAt (X := CMfd.of (n := n) U) NU oldU bornU y) ∧
      ∀ i,
        (i ∈ properRows A → CU ⊆ (Subtype.val : U → X) ⁻¹' old.get i) ∧
        (i ∉ properRows A → (∀ y : U,(DU i).mem y (fun _ => (1 : ℂ))) ∧
          IsTransverse n CU [((Subtype.val : U → X) ⁻¹' old.get i)]) ∧
        (markedRow (X := CMfd.of (n := n) U) NU bornU (IU i) (d i)).IsAdmissibleCentre CU ∧
        (markedRow (X := CMfd.of (n := n) U) NU bornU (DU i) (d i)).IsAdmissibleCentre CU := by
  let A := fun (i : Fin old.length) (j : Fin born.length) =>
    divExpAlong n N (oldMonomialPart N old born i) (born.get j) x
  let C := N ∩ memberInter born S
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hParts := fun i => actual_old_parts_geometry hn hN hE hTr hdense i
  have hWF : ∀ i : Fin old.length,
      (markedRow (X := X) N born (oldMonomialPart N old born i) 1).IsWellFormed :=
    fun i => ⟨hN,(hParts i).2.2.2.2.1,hBorn,hTr⟩
  have hNearActive : ∀ᶠ y in 𝓝 x,∀ i : Fin old.length,
      i ∈ properRows A → y ∈ C → y ∈ cosupport n N (oldMonomialPart N old born i) 1 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i ∈ properRows A
    · exact (eventually_mem_cosupp_of_le_sum hn (hWF i) (hParts i).2.2.2.2.2.1
        (hParts i).2.2.2.2.2.2.1 hxN (fun j hj => (Finset.mem_filter.mp (hSJ hj)).2)
        (hFeasible i hi)).mono fun _ hy _ => hy
    · exact Eventually.of_forall fun _ h => (hi h).elim
  have hNearUnit : ∀ᶠ y in 𝓝 x,∀ i : Fin old.length,
      i ∉ properRows A → (oldMonomialPart N old born i).mem y (fun _ => (1 : ℂ)) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i ∈ properRows A
    · exact Eventually.of_forall fun _ h => (h hi).elim
    · have hOrder : rowOrder A i=0 := by
        have : ¬0<rowOrder A i := by simpa only [properRows,Finset.mem_filter,
          Finset.mem_univ,true_and] using hi
        omega
      have hZero : ∀ j : Fin born.length,A i j=0 := by
        intro j
        have hle : A i j ≤ rowOrder A i := Finset.single_le_sum
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        omega
      have hOne := HironakaG4CanonicalZeroRowUnit.one_mem_of_zero_canonical_row hn hN hBorn hTr
        (hParts i).2.2.2.2.1 (hParts i).2.2.2.2.2.1 (hParts i).2.2.2.2.2.2.1 hxN hZero
      exact (HadamardBridge.eventually_mem_of_isCoherent (hParts i).2.2.2.2.1 hOne).mono
        fun _ hy _ => hy
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp (hNearActive.and hNearUnit)
  let U : Opens X := ⟨V,hVo⟩
  let NU := (Subtype.val : U → X) ⁻¹' N
  let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let e : Fin born.length ↪ Fin bornU.length := (finCongr (by simp [bornU])).toEmbedding
  let eO : Fin old.length ↪ Fin oldU.length := (finCongr (by simp [oldU])).toEmbedding
  let SU := S.map e
  let CU := NU ∩ memberInter bornU SU
  let IU := fun i : Fin old.length => restrictOn n NU
    (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' old.get i))
  let DU := fun i => monomialPartAlong n NU (IU i) bornU
  let d := fun i => if i ∈ properRows A then 1 else 0
  have hOldGet (i : Fin old.length) : oldU.get (eO i)=(Subtype.val : U → X) ⁻¹' old.get i := by
    simp [oldU,eO]
  have hBornGet (j : Fin born.length) : bornU.get (e j)=(Subtype.val : U → X) ⁻¹' born.get j := by
    simp [bornU,e]
  have hMem : memberInter bornU SU=(Subtype.val : U → X) ⁻¹' memberInter born S := by
    ext y
    simp only [memberInter,Set.mem_ofPred_eq,mem_preimage,SU,Finset.mem_map]
    constructor
    · intro h j hj
      have hh := h (e j) ⟨j,hj,rfl⟩
      rwa [hBornGet] at hh
    · rintro h _ ⟨j,hj,rfl⟩
      rw [hBornGet]
      exact h j hj
  have hCeq : CU=(Subtype.val : U → X) ⁻¹' C := by rw [show CU=NU ∩ memberInter bornU SU from rfl,hMem]; rfl
  have hNU := isClosedSubmanifold_preimage_val hN U
  have hFullU : IsSNCDivisor n (oldU ++ bornU) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hBornU := isSNCDivisor_of_sublist hFullU (List.sublist_append_right oldU bornU)
  have hTrU : IsTransverse n NU bornU := isTransverse_preimage (pullsBackCoordinates_val U) hTr
  have hDenseU : NU ⊆ closure (NU \ ⋃ H ∈ oldU ++ bornU,H) := by
    simpa only [List.map_append] using open_full_density hdense U
  have hPartU := fun i : Fin old.length => actual_old_parts_geometry (X := CMfd.of (n := n) U)
    hn hNU hFullU hTrU hDenseU (eO i)
  have hID (i : Fin old.length) : oldTraceIdeal (X := CMfd.of (n := n) U) NU oldU (eO i)=IU i := by
    change restrictOn n NU (vanishingIdeal (n := n) (oldU.get (eO i))) = IU i
    rw [hOldGet]
  have hDD (i : Fin old.length) : oldMonomialPart (X := CMfd.of (n := n) U) NU oldU bornU (eO i)=DU i := by
    change monomialPartAlong n NU (oldTraceIdeal (X := CMfd.of (n := n) U) NU oldU (eO i)) bornU = DU i
    rw [hID]
  have hcI (i : Fin old.length) : (IU i).IsCoherent := by
    have h := (hPartU i).1
    change (oldTraceIdeal (X := CMfd.of (n := n) U) NU oldU (eO i)).IsCoherent at h
    rwa [hID] at h
  have hcD (i : Fin old.length) : (DU i).IsCoherent := by
    have h := (hPartU i).2.2.2.2.1
    change (oldMonomialPart (X := CMfd.of (n := n) U) NU oldU bornU (eO i)).IsCoherent at h
    rwa [hDD] at h
  have hnzD (i : Fin old.length) : ∀ y ∈ NU,IsNonzeroAlongAt NU (DU i) y := by
    have h := (hPartU i).2.2.2.2.2.1
    change ∀ y ∈ NU,IsNonzeroAlongAt NU
      (oldMonomialPart (X := CMfd.of (n := n) U) NU oldU bornU (eO i)) y at h
    rwa [hDD] at h
  have hmD (i : Fin old.length) : IsMonomialAlong n NU (DU i) bornU := by
    have h := (hPartU i).2.2.2.2.2.2.1
    change IsMonomialAlong n NU
      (oldMonomialPart (X := CMfd.of (n := n) U) NU oldU bornU (eO i)) bornU at h
    rwa [hDD] at h
  have hDOpen (i : Fin old.length) : DU i=GermIdeal.pullback (m := n) (Subtype.val : U → X)
      (oldMonomialPart N old born i) := (open_parts_pullback hn hN hE hTr hdense U i).1
  have hCU : IsClosedSubmanifold n CU := isClosedSubmanifold_inter_memberInter hn hNU.1 hBornU hTrU SU
  have hCN : CU ⊆ NU := inter_subset_left
  have hCB : HasNormalCrossings n CU bornU := hasNormalCrossings_inter_memberInter hTrU SU
  have hOne : ∀ i ∉ properRows A,∀ y : U,(DU i).mem y (fun _ => (1 : ℂ)) := by
    intro i hi y
    rw [hDOpen]
    apply GermIdeal.mem_pullback_iff.mpr
    exact isInSpanAt_self ⟨(fun _ : X => (1 : ℂ)),(hV y.property).2 i hi,rfl⟩ (holomorphicAt_const 1)
  have hAdmD : ∀ i,(markedRow (X := CMfd.of (n := n) U) NU bornU (DU i) (d i)).IsAdmissibleCentre CU := by
    intro i
    refine ⟨hCU,?_,hCB⟩
    by_cases hi : i ∈ properRows A
    · change CU ⊆ cosupport n NU (DU i) (d i)
      rw [show d i=1 by simp only [d,if_pos hi],hDOpen]
      change CU ⊆ (MarkedIdeal.pullback (Subtype.val : U → X)
        (markedRow (X := X) N born (oldMonomialPart N old born i) 1)).cosupp
      rw [cosupp_pullback_val _ (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem
        (hParts i).2.2.2.2.1 hg) U]
      intro y hy
      have hyC : (y : X) ∈ C := by
        change y ∈ (Subtype.val : U → X) ⁻¹' C
        rw [←hCeq]
        exact hy
      exact (hV y.property).1 i hi hyC
    · change CU ⊆ cosupport n NU (DU i) (d i)
      rw [show d i=0 by simp only [d,if_neg hi],cosupport_zero
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcD i) hg)]
      exact hCN
  obtain ⟨hOrdU,hPreparedU⟩ := current_prepared_open hn hN hE hTr hdense hOrd hPrepared U
  have hHit : ∀ y ∈ CU,∀ i : Fin oldU.length,
      ¬(oldMonomialPart (X := CMfd.of (n := n) U) NU oldU bornU i).mem y 1 →
      1 ≤ ∑ j ∈ SU,divExpAlong n NU
        (oldMonomialPart (X := CMfd.of (n := n) U) NU oldU bornU i) (bornU.get j) y := by
    intro y hy i hnot
    obtain ⟨k,rfl⟩ := (finCongr (show old.length=oldU.length by simp [oldU])).surjective i
    change ¬(oldMonomialPart (X := CMfd.of (n := n) U) NU oldU bornU (eO k)).mem y 1 at hnot
    change 1 ≤ ∑ j ∈ SU,divExpAlong n NU
      (oldMonomialPart (X := CMfd.of (n := n) U) NU oldU bornU (eO k)) (bornU.get j) y
    rw [hDD] at hnot ⊢
    have hk : k ∈ properRows A := by
      by_contra hk
      exact hnot (hOne k hk y)
    have hCos : CU ⊆ cosupport n NU (DU k) 1 := by
      have h := (hAdmD k).2.1
      change CU ⊆ cosupport n NU (DU k) (d k) at h
      simpa only [d,if_pos hk] using h
    have hBound := le_sum_divExpAlong_of_subset_cosupport hn hNU hBornU hTrU
      (hcD k) (hnzD k) (hmD k) hCB hCN hCos hy
    rwa [filter_eventually_subset_inter_memberInter_eq hn hBornU hTrU hy.1
      (fun j hj => hy.2 j hj)] at hBound
  have hCFull := (prepared_selected_born_centre_geometry (X := CMfd.of (n := n) U)
    hn hNU hFullU hTrU hDenseU hOrdU hPreparedU SU hHit).2
  have hCosI : ∀ i ∈ properRows A,CU ⊆ cosupport n NU (IU i) 1 := by
    intro i hi y hy
    have hyD : y ∈ cosupport n NU (DU i) 1 := by
      have h := (hAdmD i).2.1 hy
      change y ∈ cosupport n NU (DU i) (d i) at h
      simpa only [d,if_pos hi] using h
    exact ⟨hy.1,fun g hg => hyD.2 g (le_monomialPartAlong hn hBornU hTrU (hcI i) y g hg)⟩
  have hContains : ∀ i ∈ properRows A,CU ⊆ (Subtype.val : U → X) ⁻¹' old.get i := by
    intro i hi y hy
    have hH := isClosedSubmanifold_preimage_val (MonomialPart.isClosedSubmanifold_get hn
      (isSNCDivisor_of_sublist hE (List.sublist_append_left old born)) i) U
    have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hH
    have hCos := hCosI i hi hy
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcI i) hg)] at hCos
    have hRaw := (zeroLocus_restrictOn_iff (X := CMfd.of (n := n) U) (N := NU) hcH hy.1).mp hCos.2
    rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hH.1] at hRaw
  have hThin : interior CU=∅ := by
    obtain ⟨j,hj⟩ := hS
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hh := interior_mono (show CU ⊆ bornU.get (e j) from fun _ hz =>
      hz.2 _ (Finset.mem_map.mpr ⟨j,hj,rfl⟩)) hy
    rw [MonomialCase.interior_get_eq_empty hn hBornU (e j)] at hh
    exact hh.elim
  refine ⟨U,hxV,hCeq,?_,hCU,hThin,hCFull,hOrdU,hPreparedU,?_⟩
  · change (⟨x,hxV⟩ : U) ∈ CU
    rw [hCeq]
    exact ⟨hxN,fun j hj => (Finset.mem_filter.mp (hSJ hj)).2⟩
  · intro i
    refine ⟨hContains i,?_,?_,hAdmD i⟩
    · intro hi
      refine ⟨hOne i hi,?_⟩
      have hTrOld := inactive_old_centre_transverse (X := CMfd.of (n := n) U)
        hn hNU hFullU hTrU hDenseU hOrdU hPreparedU SU hCFull (eO i)
        (by rw [hDD]; exact hOne i hi)
      change IsTransverse n CU [oldU.get (eO i)] at hTrOld
      rwa [hOldGet] at hTrOld
    · refine ⟨hCU,?_,hCB⟩
      change CU ⊆ cosupport n NU (IU i) (d i)
      by_cases hi : i ∈ properRows A
      · simpa only [d,if_pos hi] using hCosI i hi
      · rw [show d i=0 by simp only [d,if_neg hi],cosupport_zero
          (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcI i) hg)]
        exact hCN

open HironakaSharpActualFiniteChronologicalHistory HomogenizedGlueingTower

/-- A real prepared mixed selected step produces independent WHOLE old strict
ideals, actual canonical D/J and all original-slot canonical D columns. -/
theorem exists_prepared_mixed_selected_strict_trace_step (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H))
    (hOrd : ∀ y ∈ N, ∀ i, ordinaryTraceOrder N (oldResidualPart N old born i) y ≤ 1)
    (hPrepared : ∀ y ∈ N, IsPreparedResidualSNCAt N old born y)
    {x : X} (hxN : x ∈ N)
    (hActive : (properRows (fun (i : Fin old.length) (j : Fin born.length) =>
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) x)).Nonempty)
    (S : Finset (Fin born.length)) (hS : S.Nonempty)
    (hSJ : S ⊆ Finset.univ.filter (fun j => x ∈ born.get j))
    (hFeasible : ∀ i ∈ properRows
      (fun (i : Fin old.length) (j : Fin born.length) =>
        divExpAlong n N (oldMonomialPart N old born i) (born.get j) x),
      1 ≤ ∑ j ∈ S, divExpAlong n N (oldMonomialPart N old born i) (born.get j) x) :
    let A := fun (i : Fin old.length) (j : Fin born.length) =>
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) x
    ∃ (U : Opens X) (hxU : x ∈ U),
      let NU := (Subtype.val : U → X) ⁻¹' N
      let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
      let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
      let e : Fin born.length ↪ Fin bornU.length := (finCongr (by simp [bornU])).toEmbedding
      let SU := S.map e
      let CU := NU ∩ memberInter bornU SU
      let IU : Fin old.length → GermIdeal n U := fun i => restrictOn n NU
        (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' old.get i))
      let DU := fun i => monomialPartAlong n NU (IU i) bornU
      let JU := fun i => nonmonomialPartAlong n NU (IU i) bornU
      let AU := fun (i : Fin old.length) (j : Fin bornU.length) =>
        divExpAlong n NU (DU i) (bornU.get j) (⟨x, hxU⟩ : U)
      let d := fun i => if i ∈ properRows A then 1 else 0
      let MI := fun i => markedRow (X := CMfd.of (n := n) U) NU bornU (IU i) (d i)
      let MD := fun i => markedRow (X := CMfd.of (n := n) U) NU bornU (DU i) (d i)
      ∃ (Y : CMfd.{u} n) (π : Y → U),
        let N' := geoStrictTransform π CU NU
        let old' := oldU.map (geoStrictTransform π CU)
        let born' := bornU.map (geoStrictTransform π CU) ++ [π ⁻¹' CU]
        let I' := fun i => restrictOn n N' (vanishingIdeal (n := n)
          (geoStrictTransform π CU ((Subtype.val : U → X) ⁻¹' old.get i)))
        let D' := fun i => monomialPartAlong n N' (I' i) born'
        let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
        let G := fun i => ((MD i).geoTransform CU π).ideal
        let T := fun i => (nextTotalMarked (X := CMfd.of (n := n) U) (Y := Y) NU (JU i) CU π).ideal
        IsBlowupAlong n CU π ∧
        CU = (Subtype.val : U → X) ⁻¹' (N ∩ memberInter born S) ∧
        (⟨x, hxU⟩ : U) ∈ CU ∧ IsClosedSubmanifold n CU ∧ interior CU = ∅ ∧
        HasNormalCrossings n CU (oldU ++ bornU) ∧
        CU ⊆ originalSharpBadLocus (n := n) NU (oldU ++ bornU) ∧
        (∀ y ∈ NU, ∀ i, ordinaryTraceOrder NU (oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU i) y ≤ 1) ∧
        (∀ y ∈ NU, IsPreparedResidualSNCAt (X := CMfd.of (n := n) U) NU oldU bornU y) ∧
        IsClosedSubmanifold n N' ∧ IsSNCDivisor n (old' ++ born') ∧ IsTransverse n N' born' ∧
        N' ⊆ closure (N' \ ⋃ H ∈ old' ++ born', H) ∧
        (∀ i j, AU i (e j) = A i j) ∧
        (∀ i,
          (i ∈ properRows A → CU ⊆ (Subtype.val : U → X) ⁻¹' old.get i) ∧
          (i ∉ properRows A → (∀ y : U, (DU i).mem y (fun _ => (1 : ℂ))) ∧
            IsTransverse n CU [((Subtype.val : U → X) ⁻¹' old.get i)]) ∧
          (MI i).IsAdmissibleCentre CU ∧ (MD i).IsAdmissibleCentre CU ∧
          ((MI i).geoTransform CU π).ideal = I' i ∧ D' i = G i ∧ J' i = T i ∧
          I' i = restrictOn n N' ((D' i).mul (J' i)) ∧
          (I' i).IsCoherent ∧ (∀ z ∈ N', IsNonzeroAlongAt N' (I' i) z) ∧
          (D' i).IsCoherent ∧ (∀ z ∈ N', IsNonzeroAlongAt N' (D' i) z) ∧
          IsMonomialAlong n N' (D' i) born' ∧
          (J' i).IsCoherent ∧ (∀ z ∈ N', IsNonzeroAlongAt N' (J' i) z) ∧
          monomialPartAlong n N' (J' i) born' = IdealWeightPowers.unitIdeal n Y) ∧
        (∀ z ∈ N', π z = (⟨x, hxU⟩ : U) →
          let R := Finset.univ.filter (fun j => z ∈ geoStrictTransform π CU (bornU.get j))
          R ⊆ Finset.univ.filter (fun j => (⟨x, hxU⟩ : U) ∈ bornU.get j) ∧
          (∃ p, p ∈ SU ∧ p ∉ R) ∧
          ∀ i (j : Fin born'.length),
            divExpAlong n N' (D' i) (born'.get j) z =
              transformMarkedRows d SU R AU i (Fin.cast (by simp [born']) j) ∧
            divExpAlong n N' (D' i) (born'.get j) z =
              transformFamily 1 SU R AU i (Fin.cast (by simp [born']) j)) ∧
        ∀ z ∈ N', π z ∉ CU → ∀ i (j : Fin born'.length),
          divExpAlong n N' (D' i) (born'.get j) z =
            appendAbsentRow (fun k => divExpAlong n NU (DU i) (bornU.get k) (π z))
              (Fin.cast (by simp [born']) j) := by
  let A := fun (i : Fin old.length) (j : Fin born.length) =>
    divExpAlong n N (oldMonomialPart N old born i) (born.get j) x
  obtain ⟨U,hxU,hCeq,hxC,hCU,hThin,hCFull,hOrdU,hPreparedU,hRows⟩ :=
    exists_prepared_window hn hN hE hTr hdense hOrd hPrepared hxN S hS hSJ hFeasible
  let NU := (Subtype.val : U → X) ⁻¹' N
  let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let e : Fin born.length ↪ Fin bornU.length := (finCongr (by simp [bornU])).toEmbedding
  let eO : Fin old.length ↪ Fin oldU.length := (finCongr (by simp [oldU])).toEmbedding
  let SU := S.map e
  let CU := NU ∩ memberInter bornU SU
  let IU := fun i : Fin old.length => restrictOn n NU
    (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' old.get i))
  let DU := fun i => monomialPartAlong n NU (IU i) bornU
  let JU := fun i => nonmonomialPartAlong n NU (IU i) bornU
  let AU := fun (i : Fin old.length) (j : Fin bornU.length) =>
    divExpAlong n NU (DU i) (bornU.get j) (⟨x,hxU⟩ : U)
  let d := fun i => if i ∈ properRows A then 1 else 0
  let MI := fun i => markedRow (X := CMfd.of (n := n) U) NU bornU (IU i) (d i)
  let MD := fun i => markedRow (X := CMfd.of (n := n) U) NU bornU (DU i) (d i)
  have hNU := isClosedSubmanifold_preimage_val hN U
  have hFullU : IsSNCDivisor n (oldU ++ bornU) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hOldU := isSNCDivisor_of_sublist hFullU (List.sublist_append_left oldU bornU)
  have hBornU := isSNCDivisor_of_sublist hFullU (List.sublist_append_right oldU bornU)
  have hTrU : IsTransverse n NU bornU := isTransverse_preimage (pullsBackCoordinates_val U) hTr
  have hDenseU : NU ⊆ closure (NU \ ⋃ H ∈ oldU ++ bornU,H) := by
    simpa only [List.map_append] using open_full_density hdense U
  have hOldGet (i : Fin old.length) : oldU.get (eO i)=(Subtype.val : U → X) ⁻¹' old.get i := by
    simp [oldU,eO]
  have hPartU (i : Fin old.length) := actual_old_parts_geometry (X := CMfd.of (n := n) U)
    (N := NU) hn hNU hFullU hTrU hDenseU (eO i)
  have hcI (i : Fin old.length) : (IU i).IsCoherent := by
    simpa only [oldTraceIdeal,hOldGet] using (hPartU i).1
  have hnzI (i : Fin old.length) : ∀ y ∈ NU,IsNonzeroAlongAt NU (IU i) y := by
    simpa only [oldTraceIdeal,hOldGet] using (hPartU i).2.1
  have hcD (i : Fin old.length) : (DU i).IsCoherent := by
    simpa only [oldMonomialPart,oldTraceIdeal,hOldGet] using (hPartU i).2.2.2.2.1
  have hnzD (i : Fin old.length) : ∀ y ∈ NU,IsNonzeroAlongAt NU (DU i) y := by
    simpa only [oldMonomialPart,oldTraceIdeal,hOldGet] using (hPartU i).2.2.2.2.2.1
  have hmD (i : Fin old.length) : IsMonomialAlong n NU (DU i) bornU := by
    simpa only [oldMonomialPart,oldTraceIdeal,hOldGet] using (hPartU i).2.2.2.2.2.2.1
  have hWFI : ∀ i,(MI i).IsWellFormed := fun i => ⟨hNU,hcI i,hBornU,hTrU⟩
  have hWFD : ∀ i,(MD i).IsWellFormed := fun i => ⟨hNU,hcD i,hBornU,hTrU⟩
  have hAdmI : ∀ i,(MI i).IsAdmissibleCentre CU := fun i => (hRows i).2.2.1
  have hAdmD : ∀ i,(MD i).IsAdmissibleCentre CU := fun i => (hRows i).2.2.2
  have hCN : CU ⊆ NU := inter_subset_left
  have hCB : HasNormalCrossings n CU bornU := hasNormalCrossings_inter_memberInter hTrU SU
  have hSU : SU.Nonempty := by
    obtain ⟨j,hj⟩ := hS
    exact ⟨e j,Finset.mem_map.mpr ⟨j,hj,rfl⟩⟩
  obtain ⟨Y,π,hπ⟩ := ResolutionDriver.exists_blowup (Y := CMfd.of (n := n) U) CU hCU hThin
  let N' := geoStrictTransform π CU NU
  let old' := oldU.map (geoStrictTransform π CU)
  let born' := bornU.map (geoStrictTransform π CU) ++ [π ⁻¹' CU]
  let I' := fun i : Fin old.length => restrictOn n N' (vanishingIdeal (n := n)
    (geoStrictTransform π CU ((Subtype.val : U → X) ⁻¹' old.get i)))
  let D' := fun i => monomialPartAlong n N' (I' i) born'
  let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
  let G := fun i => ((MD i).geoTransform CU π).ideal
  let T := fun i => (nextTotalMarked (X := CMfd.of (n := n) U) (Y := Y) NU (JU i) CU π).ideal
  have hN' : IsClosedSubmanifold n N' :=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hNU hCN
  have hFull' : IsSNCDivisor n (old' ++ born') := by
    simpa only [List.map_append,List.append_assoc] using
      isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hFullU hCFull
  have hBorn' := isSNCDivisor_of_sublist hFull' (List.sublist_append_right old' born')
  have hTr' : IsTransverse n N' born' :=
    isTransverse_geoTransformE_of_hasNormalCrossings hπ hNU.1 hCN hBornU hTrU hCB
  have hDict (i : Fin old.length) : ((MI i).geoTransform CU π).ideal=I' i := by
    apply masked_whole_strict_trace (X := CMfd.of (n := n) U) hn hNU
      (isClosedSubmanifold_preimage_val (MonomialPart.isClosedSubmanifold_get hn
        (isSNCDivisor_of_sublist hE (List.sublist_append_left old born)) i) U) hπ hCN
    by_cases hi : i ∈ properRows A
    · exact Or.inl ⟨by simp only [d,if_pos hi],(hRows i).1 hi⟩
    · have hSingle : IsSNCDivisor n [((Subtype.val : U → X) ⁻¹' old.get i)] := by
        have h := isSNCDivisor_of_sublist hOldU (show [oldU.get (eO i)].Sublist oldU by simp)
        rwa [hOldGet] at h
      exact Or.inr ⟨by simp only [d,if_neg hi],hSingle,((hRows i).2.1 hi).2⟩
  have hGInputs (i : Fin old.length) :=
    HironakaG4SelectedBornCanonicalColumns.geoTransform_monomial_inputs (X := CMfd.of (n := n) U)
      hn (hWFD i) (hnzD i) (hmD i) (hAdmD i) hπ
  have hcG (i : Fin old.length) : (G i).IsCoherent := (hGInputs i).1.isCoherent
  have hnzG (i : Fin old.length) : ∀ z ∈ N',IsNonzeroAlongAt N' (G i) z := (hGInputs i).2.1
  have hmG (i : Fin old.length) : IsMonomialAlong n N' (G i) born' := (hGInputs i).2.2
  obtain ⟨_hCoreSmooth,_hCoreThin,hCore⟩ :=
    HironakaG4PreparedResidualTotalNoFactor.prepared_residual_total_no_member_factor
      (X := CMfd.of (n := n) U) (N := NU) hn hNU hFullU hTrU hDenseU SU hSU
      (fun y hy => hOrdU y hy.1) (fun y hy => hPreparedU y hy.1)
  have hTotal (i : Fin old.length) :
      (T i).IsCoherent ∧ (∀ z ∈ N',IsNonzeroAlongAt N' (T i) z) ∧
      (∀ z ∈ N',∀ j : Fin born'.length,z ∈ born'.get j → ∃ g : Y → ℂ,
        (T i).mem z g ∧ ¬IsInSpanOnAt (n := n) N'
          ((vanishingIdeal (n := n) (born'.get j)).mem z) z g) ∧
      monomialPartAlong n N' (T i) born'=unitIdeal n Y ∧
      nonmonomialPartAlong n N' (T i) born'=T i ∧
      nextRelativeStrict (X := CMfd.of (n := n) U) (Y := Y) NU (JU i) CU π=T i := by
    simpa only [oldResidualPart,oldTraceIdeal,hOldGet] using hCore (Y := Y) π hπ (eO i)
  have hMixed (i : Fin old.length) :
      (I' i).IsCoherent ∧ (∀ z ∈ N',IsNonzeroAlongAt N' (I' i) z) ∧
      J' i=nextRelativeStrict (X := CMfd.of (n := n) U) (Y := Y) NU (JU i) CU π := by
    simpa only [oldResidualPart,oldTraceIdeal,hOldGet] using
      HironakaG4MixedOldResidualStep.actual_mixed_old_residual_step (X := CMfd.of (n := n) U)
        (N := NU) hn hNU hFullU hTrU hDenseU (eO i) hπ hCN hCFull
  have hJT (i : Fin old.length) : J' i=T i := (hMixed i).2.2.trans (hTotal i).2.2.2.2.2
  have hFactor (i : Fin old.length) : I' i=restrictOn n N' ((T i).mul (G i)) := by
    have h := controlled_canonical_parts_factor (X := CMfd.of (n := n) U)
      hn (MI i) (hWFI i) (hnzI i) (hAdmI i) (hAdmD i) hπ
    change ((MI i).geoTransform CU π).ideal=restrictOn n N' ((T i).mul (G i)) at h
    rwa [hDict] at h
  have hDG (i : Fin old.length) : D' i=G i := by
    have hFwd : RestrictLe N' (I' i) ((T i).mul (G i)) := by
      rw [hFactor]
      exact restrictLe_restrictOn
    have hBwd : RestrictLe N' ((T i).mul (G i)) (I' i) := by
      rw [hFactor]
      exact restrictLe_self_restrictOn (IdealWeightPowers.isCoherent_mul (hTotal i).1 (hcG i))
    have hMP := monomialPartAlong_eq_of_factor hn hN' hBorn' hTr' (hTotal i).1 (hcG i)
      (hTotal i).2.2.1 hFwd hBwd
    have hLe := le_monomialPartAlong hn hBorn' hTr' (hcG i)
    have hLeR : RestrictLe N' (G i) (monomialPartAlong n N' (G i) born') := by
      intro z _hz g hg
      exact IsInSpanAt.restrict (isInSpanAt_self (hLe z g hg)
        (GermIdeal.IsCoherent.holomorphicAt_mem (hcG i) hg))
    have hRestrict := restrictOn_eq_of_restrictLe hN'.1 (hmG i) hLeR
    have hMPG : monomialPartAlong n N' (G i) born'=G i :=
      (restrictOn_monomialPartAlong N' (G i) born').symm.trans
        (hRestrict.trans (controlled_normalized (MD i) hπ))
    exact hMP.trans hMPG
  let Q : BlowupTower (CMfd.of (n := n) U) Y := .step .refl CU π hπ
  have hGeo : IsGeoTestTower (geometricTemplate (X := CMfd.of (n := n) U) NU []) Q := by
    refine ⟨trivial,hCU,?_,hasNormalCrossings_nil_of_isClosedSubmanifold hCU⟩
    change CU ⊆ cosupport n NU (unitIdeal n U) 0
    rw [cosupport_zero (fun _ _ hg => hg)]
    exact hCN
  have hAll : IsGeoTestTower
      (geometricTemplate (X := CMfd.of (n := n) U) (univ : Set U) (oldU ++ bornU)) Q := by
    refine ⟨trivial,hCU,?_,hCFull⟩
    change CU ⊆ cosupport n univ (unitIdeal n U) 0
    rw [cosupport_zero (fun _ _ hg => hg)]
    exact subset_univ CU
  have hRecorded := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    (X := CMfd.of (n := n) U) hn hNU hFullU hDenseU Q hGeo hAll
  have hDense' : N' ⊆ closure (N' \ ⋃ H ∈ old' ++ born',H) := by
    have h := hRecorded.2.2.2.1
    change N' ⊆ closure (N' \ ⋃ H ∈ (oldU ++ bornU).map (geoStrictTransform π CU) ++ [π ⁻¹' CU],H) at h
    simpa only [old',born',List.map_append,List.append_assoc] using h
  have hSharp : CU ⊆ originalSharpBadLocus (n := n) NU (oldU ++ bornU) := by
    obtain ⟨i,hi⟩ := hActive
    change i ∈ properRows A at hi
    let oi : Fin (oldU ++ bornU).length := ⟨(eO i).val,by simp only [List.length_append]; omega⟩
    let bornIndex : Fin bornU.length → Fin (oldU ++ bornU).length :=
      fun j => ⟨oldU.length+j.val,by simp only [List.length_append]; omega⟩
    let L : List (Fin (oldU ++ bornU).length) := List.ofFn bornIndex
    have hOld : (oldU ++ bornU).get oi=(Subtype.val : U → X) ⁻¹' old.get i := by
      rw [show (oldU ++ bornU).get oi=oldU.get (eO i) by simp [oi,List.get_eq_getElem],hOldGet]
    have hBorn (j) : (oldU ++ bornU).get (bornIndex j)=bornU.get j := by
      simp [bornIndex,List.get_eq_getElem]
    have hLmap : L.map (oldU ++ bornU).get=bornU := by
      rw [show L=List.ofFn bornIndex from rfl,List.map_ofFn]
      convert List.ofFn_get bornU using 1
      congr 1
      funext j
      exact hBorn j
    have hApart : ∀ j ∈ L,oi ≠ j := by
      intro j hj
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hj
      intro heq
      have hv := congrArg Fin.val heq
      dsimp [oi,bornIndex] at hv
      have hb := (eO i).isLt
      omega
    have hBad := HironakaG4ActiveMonomialSharpBad.active_old_monomial_subset_originalSharpBadLocus
      (X := CMfd.of (n := n) U) (N := NU) (E := oldU ++ bornU)
      hn hNU hFullU hDenseU oi L hApart
    intro y hy
    apply hBad
    refine ⟨hy.1,?_⟩
    rw [hOld,hLmap]
    intro hOne
    have hCos := (hAdmD i).2.1 hy
    change y ∈ cosupport n NU (DU i) (d i) at hCos
    rw [show d i=1 by simp only [d,if_pos hi],cosupport_one
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcD i) hg)] at hCos
    exact one_ne_zero (hCos.2 _ hOne)
  have hAU : ∀ i j,AU i (e j)=A i j := by
    intro i j
    have hOpen : DU i=GermIdeal.pullback (m := n) (Subtype.val : U → X)
        (oldMonomialPart N old born i) := (open_parts_pullback hn hN hE hTr hdense U i).1
    change divExpAlong n NU (DU i) (bornU.get (e j)) (⟨x,hxU⟩ : U)=A i j
    rw [hOpen]
    exact HironakaMonomialBlowup.divExpAlong_pullback_val_get
      (markedRow (X := X) N born (oldMonomialPart N old born i) 1)
      (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.2.2.1
      U (⟨x,hxU⟩ : U) (e j).isLt j.isLt
  have hUniv : (Finset.univ : Finset (Fin born.length)).map e=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    obtain ⟨k,hk⟩ := (finCongr (show born.length=bornU.length by simp [bornU])).surjective j
    exact Finset.mem_map.mpr ⟨k,Finset.mem_univ k,hk⟩
  have hOrders (i) : rowOrder AU i=rowOrder A i := by
    calc
      rowOrder AU i=∑ j ∈ (Finset.univ : Finset (Fin born.length)).map e,AU i j := by rw [hUniv]; rfl
      _=∑ j : Fin born.length,AU i (e j) := by rw [Finset.sum_map]
      _=rowOrder A i := Finset.sum_congr rfl fun j _ => hAU i j
  have hProper : properRows AU=properRows A := by
    ext i
    simp only [properRows,Finset.mem_filter,Finset.mem_univ,true_and,hOrders]
  have hLen : born'.length=bornU.length+1 := by simp only [born',List.length_append,List.length_map,List.length_singleton]
  refine ⟨U,hxU,Y,π,hπ,hCeq,hxC,hCU,hThin,hCFull,hSharp,hOrdU,hPreparedU,
    hN',hFull',hTr',hDense',hAU,?_,?_,?_⟩
  · intro i
    refine ⟨(hRows i).1,(hRows i).2.1,hAdmI i,hAdmD i,hDict i,hDG i,hJT i,?_,
      (hMixed i).1,(hMixed i).2.1,?_,?_,?_,?_,?_,?_⟩
    · change I' i=restrictOn n N' ((D' i).mul (J' i))
      rw [hDG i,hJT i,RestrictLeCalculus.mul_comm' (G i) (T i)]
      exact hFactor i
    · change (D' i).IsCoherent
      rw [hDG i]
      exact hcG i
    · change ∀ z ∈ N',IsNonzeroAlongAt N' (D' i) z
      rw [hDG i]
      exact hnzG i
    · change IsMonomialAlong n N' (D' i) born'
      rw [hDG i]
      exact hmG i
    · change (J' i).IsCoherent
      rw [hJT i]
      exact (hTotal i).1
    · change ∀ z ∈ N',IsNonzeroAlongAt N' (J' i) z
      rw [hJT i]
      exact (hTotal i).2.1
    · change monomialPartAlong n N' (J' i) born'=unitIdeal n Y
      rw [hJT i]
      exact (hTotal i).2.2.2.1
  · intro z hz hzx
    let R := Finset.univ.filter (fun j => z ∈ geoStrictTransform π CU (bornU.get j))
    have hzC : π z ∈ CU := hzx ▸ hxC
    have hR : R ⊆ Finset.univ.filter (fun j => (⟨x,hxU⟩ : U) ∈ bornU.get j) := by
      intro j hj
      have hzj := (Finset.mem_filter.mp hj).2
      have h := geoStrictTransform_subset_preimage hπ.contMDiff.continuous
        (hBornU.1 _ (List.get_mem bornU j)) hzj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,hzx ▸ h⟩
    obtain ⟨p,hpS,hpR,_hCosupp⟩ :=
      HironakaG4SelectedBornAdmissibility.exists_canonical_selected_born_chart_step
        (X := CMfd.of (n := n) U) hNU hBornU hTrU SU hπ DU d hcD hnzD hmD hAdmD hz hzC
    have hMask : transformMarkedRows d SU R AU=transformFamily 1 SU R AU := by
      change transformMarkedRows (fun i => if i ∈ properRows A then 1 else 0) SU R AU = _
      rw [←hProper]
      exact HironakaG4MonomialActiveCleanup.current_mark_mask_transform_eq_native AU SU R
    refine ⟨hR,⟨p,hpS,hpR⟩,?_⟩
    intro i j
    have hCol := HironakaG4SelectedBornCanonicalColumns.canonical_columns_selected_born_geoTransform
      (X := CMfd.of (n := n) U) (hWFD i) (hnzD i) (hmD i) SU (hAdmD i) hπ hz hzC j
    change divExpAlong n N' (G i) (born'.get j) z =
      transformRow (d i) SU R (fun k => divExpAlong n NU (DU i) (bornU.get k) (π z))
        (Fin.cast hLen j) at hCol
    rw [←hDG i,hzx] at hCol
    exact ⟨hCol,hCol.trans (congrFun (congrFun hMask i) (Fin.cast hLen j))⟩
  · intro z hz hzC i j
    have hCol := HironakaG4SelectedBornCanonicalColumns.canonical_columns_geoTransform_of_notMem
      (X := CMfd.of (n := n) U) hn (hWFD i) (hnzD i) (hmD i) (hAdmD i) hπ hz hzC j
    change divExpAlong n N' (G i) (born'.get j) z =
      appendAbsentRow (fun k => divExpAlong n NU (DU i) (bornU.get k) (π z))
        (Fin.cast hLen j) at hCol
    rwa [←hDG i] at hCol

end
end Hironaka.HironakaG4PreparedMixedSelectedStep


namespace Hironaka.HironakaG4PreparedMixedSelectedStep

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower NormalCrossings MonomialPartAlong HironakaG4PreparedCentreCoordinates
  RelativePrincipalizationSpan RestrictedIdealExtension

variable {n : ℕ} {X : CMfd.{u} n}

/-- Public exact native whole-parts open readback; no order or preparation premise. -/
theorem open_parts_pullback_native (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (U : Opens X) (i : Fin old.length) :
    let NU := (Subtype.val : U → X) ⁻¹' N
    let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    let IU := restrictOn n NU (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' old.get i))
    monomialPartAlong n NU IU bornU = GermIdeal.pullback (m := n) (Subtype.val : U → X)
      (oldMonomialPart N old born i) ∧
    nonmonomialPartAlong n NU IU bornU = GermIdeal.pullback (m := n) (Subtype.val : U → X)
      (oldResidualPart N old born i) :=
  open_parts_pullback hn hN hE hTr hdense U i

end Hironaka.HironakaG4PreparedMixedSelectedStep
