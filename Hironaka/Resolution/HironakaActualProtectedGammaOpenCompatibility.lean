import Hironaka.Resolution.HironakaActualProtectedGammaPrefixHistory
import Hironaka.Resolution.HironakaSharpActualChronologicalOpenNaturality
import Hironaka.Resolution.HironakaSharpOriginalAllBoundaryCentre

/-! SAME native Gamma driver under arbitrary actual source opens. Literal
empty years and original old/born clocks are retained. Source-first proof:
hironaka-actual-protected-gamma-open-compatibility.tex. No full recursive
lower sharp-driver comparison, upper-family factor or global K1 claim. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualProtectedGammaOpenCompatibility
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedGlueingTower HironakaSharpActualFiniteChronologicalHistory
  HironakaG4RecordedTowerResidualCompatibility HironakaG4CompactWholeMonomialMaskPhase
  HironakaSharpActualOriginalControlledHistory NormalCrossings NormalCrossingsComparison
  SimultaneousNormalCrossings NormalCrossingsInvariance
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4OriginalSelectedResidualTail HironakaG4PreparedCentreCoordinates
  HironakaSharpActualChronologicalResidualDictionary HironakaSharpActualFirstAmbientStrictExponent
  RelativePrincipalizationSpan RestrictedIdealExtension GermIdealOrder IdealWeightPowers
  BlowupStrictSubmanifold MonomialStepAlong MonomialCaseAlong HironakaMarkOneGammaBoundedMaxima
  HironakaActualProtectedGammaPrefixHistory MonomialPartAlong DivisorExponentAlong
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionDriver
  HironakaSharpActualChronologicalOpenNaturality HironakaSharpOriginalProductTraceOrder
  HironakaG4ResidualInductionInputs HironakaSharpActualTraceIncidence
  GermIdealPullbackCalculus BlowupRestrictOpen MonomialInvariant MonomialInvariantFunctorialAlong
  DerivativeIdealAlongEtale HironakaSharpActualMixedCentreWholeStrictTraceGeometry
  MonomialPartEtale HironakaCoherentTransformExtension
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Whole native Gamma canonicality under the literal source restriction.
A missing global maximum produces an actual EMPTY raw canonical step. -/
theorem native_gamma_canonical_restrict (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent) (O : Opens X) :
    ∀ {Y : CMfd.{u} n} (R : BlowupTower X Y),IsGeoTestTower M R →
      IsCanonicalSegment M (fun {Q} S => towerInvAlong M (Y := Q) S) R →
      ResolutionInvariantSpec.IsCanonical (MarkedIdeal.pullback (Subtype.val : O → X) M)
        (fun {Q} S => towerInvAlong (MarkedIdeal.pullback (Subtype.val : O → X) M) (Y := Q) S)
        (restrict O R)
  | _,.refl,_hTest,_hCan => trivial
  | _,.step R C π hπ,hTest,hCan => by
      refine ⟨native_gamma_canonical_restrict M hN hI O R hTest.1 hCan.1,?_⟩
      rcases hCan with ⟨_hOld,_hNonempty,rfl⟩
      by_cases hTrace : ((Subtype.val : openPreimage R O → _) ⁻¹'
          maxLocus (towerInvAlong M R) (geoTransformAlong M R).cosupp).Nonempty
      · right
        rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hN hI O R hTest.1]
        exact (ResolutionInvariantSegments.maxLocus_preimage _
          (fun p _hp => MonomialInvariantFunctorialAlong.towerInvAlong_restrict M hN hI O R hTest.1 p)
          hTrace).symm
      · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hTrace)


-- Reused ordinary open/coordinate arguments; zero separate mathematical credit.
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
    exact (HironakaG4PreparedMixedSelectedStep.open_parts_pullback_native hn hN hE hTr hdense U (cO i)).2
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


private theorem actual_vanishingIdeal_open (Z : Set X)
    (hZ : IsClosedSubmanifold n Z) (U : Opens X) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (vanishingIdeal (n := n) Z)=
      vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' Z) := by
  have hZU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hZ U
  have h := BlowupRestrictOpen.pullback_vanishingIdeal_opens (n := n) (m := n) U (id : U → U) Z
  rw [BlowupControlledTransform.pullback_id
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hZU)] at h
  exact h.symm

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

private theorem native_segment_head (M : MarkedIdeal n X) :
    ∀ {Y : CMfd.{u} n} (R : BlowupTower X Y),
      IsCanonicalSegment M (fun {Q} S => towerInvAlong M (Y := Q) S) R →
      ∀ k,IsCanonicalSegment M (fun {Q} S => towerInvAlong M (Y := Q) S) (BlowupTowerSplit.head R k)
  | _,.refl,_,0 => trivial
  | _,.refl,_,_+1 => trivial
  | _,.step _ _ _ _,h,0 => h
  | _,.step R _ _ _,h,k+1 => native_segment_head M R h.1 k

theorem native_gamma_restricted_length (O : Opens X) :
    ∀ {Y : CMfd.{u} n} (R : BlowupTower X Y),(restrict O R).length=R.length
  | _,.refl => rfl
  | _,.step R _ _ _ => congrArg Nat.succ (native_gamma_restricted_length O R)

private theorem canonical_parts_open (hn : 0<n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hd : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (O : Opens X) (a : Fin old.length) :
    let NU := (Subtype.val : O → X) ⁻¹' N
    let oldU := old.map ((Subtype.val : O → X) ⁻¹' ·)
    let bornU := born.map ((Subtype.val : O → X) ⁻¹' ·)
    let aU : Fin oldU.length := ⟨a.val,by simpa only [oldU,List.length_map] using a.isLt⟩
    oldTraceIdeal (X := CMfd.of (n := n) O) NU oldU aU=GermIdeal.pullback (m := n) (Subtype.val : O → X) (oldTraceIdeal N old a) ∧
      oldMonomialPart (X := CMfd.of (n := n) O) NU oldU bornU aU=GermIdeal.pullback (m := n) (Subtype.val : O → X) (oldMonomialPart N old born a) ∧
      oldResidualPart (X := CMfd.of (n := n) O) NU oldU bornU aU=GermIdeal.pullback (m := n) (Subtype.val : O → X) (oldResidualPart N old born a) := by
  dsimp only
  have hGet : (old.map ((Subtype.val : O → X) ⁻¹' ·)).get
      ⟨a.val,by simpa only [List.length_map] using a.isLt⟩=(Subtype.val : O → X) ⁻¹' old.get a := by simp
  have hParts := HironakaG4PreparedMixedSelectedStep.open_parts_pullback_native hn hN hE hTr hd O a
  refine ⟨?_,?_,?_⟩
  · change restrictOn n ((Subtype.val : O → X) ⁻¹' N) (vanishingIdeal (n := n) _) = _
    rw [hGet]
    have hH := MonomialPart.isClosedSubmanifold_get hn
      (isSNCDivisor_of_sublist hE (List.sublist_append_left old born)) a
    have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hH
    have hcI := (actual_old_parts_geometry hn hN hE hTr hd a).1
    apply GermIdeal.ext
    funext x g
    apply propext
    rw [mem_pullback_val_iff O hcI]
    have hh := restrictOn_pullback_val_iff O (W := N) (x := x) (F := g) hcH
    rw [actual_vanishingIdeal_open _ hH O] at hh
    exact hh
  · change monomialPartAlong n _ (restrictOn n _ (vanishingIdeal (n := n) _)) _ = _
    rw [hGet]
    exact hParts.1
  · change nonmonomialPartAlong n _ (restrictOn n _ (vanishingIdeal (n := n) _)) _ = _
    rw [hGet]
    exact hParts.2

private theorem row_records_open (hn : 0<n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hd : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (O : Opens X) (a : Fin old.length) (d : ℕ) :
    let NU := (Subtype.val : O → X) ⁻¹' N
    let oldU := old.map ((Subtype.val : O → X) ⁻¹' ·)
    let bornU := born.map ((Subtype.val : O → X) ⁻¹' ·)
    let aU : Fin oldU.length := ⟨a.val,by simpa only [oldU,List.length_map] using a.isLt⟩
    (⟨NU,bornU,oldTraceIdeal (X := CMfd.of (n := n) O) NU oldU aU,d⟩ : MarkedIdeal n O)=
        MarkedIdeal.pullback (Subtype.val : O → X) (⟨N,born,oldTraceIdeal N old a,d⟩ : MarkedIdeal n X) ∧
      (⟨NU,bornU,oldMonomialPart (X := CMfd.of (n := n) O) NU oldU bornU aU,d⟩ : MarkedIdeal n O)=
        MarkedIdeal.pullback (Subtype.val : O → X) (⟨N,born,oldMonomialPart N old born a,d⟩ : MarkedIdeal n X) ∧
      (⟨NU,bornU,oldResidualPart (X := CMfd.of (n := n) O) NU oldU bornU aU,0⟩ : MarkedIdeal n O)=
        MarkedIdeal.pullback (Subtype.val : O → X) (⟨N,born,oldResidualPart N old born a,0⟩ : MarkedIdeal n X) := by
  obtain ⟨hI,hD,hJ⟩ := canonical_parts_open hn hN hE hTr hd O a
  exact ⟨MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hI rfl,
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hD rfl,
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hJ rfl⟩

private theorem strict_old_open (O : Opens X) (R : BlowupTower X Y) (old : List (Set X)) :
    (old.map ((Subtype.val : O → X) ⁻¹' ·)).map (strictAlong (restrict O R))=
      (old.map (strictAlong R)).map ((Subtype.val : openPreimage R O → Y) ⁻¹' ·) := by
  simp only [List.map_map]
  congr 1
  funext H
  exact strictAlong_restrict O R H

private theorem canonical_parts_cast {N : Set X} {lo₀ lo₁ born : List (Set X)}
    (a₀ : Fin lo₀.length) (a₁ : Fin lo₁.length) (hlo : lo₀=lo₁) (ha : a₀.val=a₁.val) :
    oldTraceIdeal N lo₀ a₀=oldTraceIdeal N lo₁ a₁ ∧
      oldMonomialPart N lo₀ born a₀=oldMonomialPart N lo₁ born a₁ ∧
      oldResidualPart N lo₀ born a₀=oldResidualPart N lo₁ born a₁ := by
  subst lo₁
  have he : a₀=a₁ := Fin.ext ha
  subst a₁
  exact ⟨rfl,rfl,rfl⟩

private theorem lower_parts_restrict (hn : 0<n) {L : Set X} {lo born : List (Set X)}
    (hL : IsClosedSubmanifold n L) (hFull : IsSNCDivisor n (lo ++ born))
    (hTr : IsTransverse n L born) (hd : L ⊆ closure (L \ ⋃ H ∈ lo ++ born,H))
    (a : Fin lo.length) (R : BlowupTower X Y)
    (hState : canonicalLowerGammaPrefixData L lo born a R) (O : Opens X) :
    let LU := (Subtype.val : O → X) ⁻¹' L
    let loU := lo.map ((Subtype.val : O → X) ⁻¹' ·)
    let bornU := born.map ((Subtype.val : O → X) ⁻¹' ·)
    let aU : Fin loU.length := ⟨a.val,by simpa only [loU,List.length_map] using a.isLt⟩
    canonicalLowerGammaPrefixData (X := CMfd.of (n := n) O) LU loU bornU aU (restrict O R) := by
  let LU := (Subtype.val : O → X) ⁻¹' L
  let loU := lo.map ((Subtype.val : O → X) ⁻¹' ·)
  let bornU := born.map ((Subtype.val : O → X) ⁻¹' ·)
  let aU : Fin loU.length := ⟨a.val,by simpa only [loU,List.length_map] using a.isLt⟩
  let LQ := strictAlong R L
  let loQ := lo.map (strictAlong R)
  let BQ := (geoTransformAlong (geometricTemplate L born) R).E
  let V := openPreimage R O
  let eQ : Fin lo.length ≃ Fin loQ.length := finCongr (by simp [loQ])
  obtain ⟨hPhase,hLQ,hFullQ,hTrQ,hDenseQ,hOrdQ,hPrepQ,hRows⟩ := hState
  have hParts a := actual_old_parts_geometry hn hL hFull hTr hd a
  have hPhaseWF : (⟨L,born,oldMonomialPart L lo born a,1⟩ : MarkedIdeal n X).IsWellFormed :=
    ⟨hL,(hParts a).2.2.2.2.1,
      isSNCDivisor_of_sublist hFull (List.sublist_append_right lo born),hTr⟩
  have hPhaseTest : IsGeoTestTower (⟨L,born,oldMonomialPart L lo born a,1⟩ : MarkedIdeal n X) R := by
    simpa only [ite_true] using (hRows a).2.1
  have hGeomTest := actual_original_test_history_template _ hPhaseWF R hPhaseTest
  have hBorn : (geoTransformAlong (geometricTemplate LU bornU) (restrict O R)).E=
      BQ.map ((Subtype.val : V → Y) ⁻¹' ·) := by
    have hh := congrArg MarkedIdeal.E
      (geoTransformAlong_restrict O hL (isCoherent_unitIdeal (n := n) (M := X)) R hGeomTest)
    have hE0 := geoTransformAlong_E_eq_of_E_eq
      (𝔍 := geometricTemplate LU bornU)
      (𝔪 := MarkedIdeal.pullback (Subtype.val : O → X) (geometricTemplate L born)) rfl (restrict O R)
    exact hE0.trans hh
  have hCurrentPrepared := current_prepared_open hn hLQ hFullQ hTrQ hDenseQ hOrdQ hPrepQ V
  have hLO : strictAlong (restrict O R) LU=(Subtype.val : V → Y) ⁻¹' LQ :=
    strictAlong_restrict O R L
  have hOldO : loU.map (strictAlong (restrict O R))=loQ.map ((Subtype.val : V → Y) ⁻¹' ·) :=
    strict_old_open O R lo
  have hFullO : IsSNCDivisor n
      (loQ.map ((Subtype.val : V → Y) ⁻¹' ·) ++ BQ.map ((Subtype.val : V → Y) ⁻¹' ·)) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val V) continuous_subtype_val hFullQ
  have hDenseO := open_full_density hDenseQ V
  have hRowOpen (b : Fin lo.length) :
      let bU : Fin loU.length := ⟨b.val,by simpa only [loU,List.length_map] using b.isLt⟩
      let bQ := eQ b
      let bQU : Fin (loQ.map ((Subtype.val : V → Y) ⁻¹' ·)).length :=
        ⟨bQ.val,by simp only [List.length_map];exact bQ.isLt⟩
      let d := if b=a then 1 else 0
      IsGeoTestTower (⟨LU,bornU,oldTraceIdeal (X := CMfd.of (n := n) O) LU loU bU,d⟩ : MarkedIdeal n O) (restrict O R) ∧
      IsGeoTestTower (⟨LU,bornU,oldMonomialPart (X := CMfd.of (n := n) O) LU loU bornU bU,d⟩ : MarkedIdeal n O) (restrict O R) ∧
      IsGeoTestTower (⟨LU,bornU,oldResidualPart (X := CMfd.of (n := n) O) LU loU bornU bU,0⟩ : MarkedIdeal n O) (restrict O R) ∧
      geoTransformAlong (⟨LU,bornU,oldTraceIdeal (X := CMfd.of (n := n) O) LU loU bU,d⟩ : MarkedIdeal n O) (restrict O R)=
        (⟨(Subtype.val : V → Y) ⁻¹' LQ,BQ.map ((Subtype.val : V → Y) ⁻¹' ·),
          oldTraceIdeal (X := CMfd.of (n := n) V) ((Subtype.val : V → Y) ⁻¹' LQ)
            (loQ.map ((Subtype.val : V → Y) ⁻¹' ·)) bQU,d⟩ : MarkedIdeal n V) ∧
      geoTransformAlong (⟨LU,bornU,oldMonomialPart (X := CMfd.of (n := n) O) LU loU bornU bU,d⟩ : MarkedIdeal n O) (restrict O R)=
        (⟨(Subtype.val : V → Y) ⁻¹' LQ,BQ.map ((Subtype.val : V → Y) ⁻¹' ·),
          oldMonomialPart (X := CMfd.of (n := n) V) ((Subtype.val : V → Y) ⁻¹' LQ)
            (loQ.map ((Subtype.val : V → Y) ⁻¹' ·)) (BQ.map ((Subtype.val : V → Y) ⁻¹' ·)) bQU,d⟩ : MarkedIdeal n V) ∧
      geoTransformAlong (⟨LU,bornU,oldResidualPart (X := CMfd.of (n := n) O) LU loU bornU bU,0⟩ : MarkedIdeal n O) (restrict O R)=
        (⟨(Subtype.val : V → Y) ⁻¹' LQ,BQ.map ((Subtype.val : V → Y) ⁻¹' ·),
          oldResidualPart (X := CMfd.of (n := n) V) ((Subtype.val : V → Y) ⁻¹' LQ)
            (loQ.map ((Subtype.val : V → Y) ⁻¹' ·)) (BQ.map ((Subtype.val : V → Y) ⁻¹' ·)) bQU,0⟩ : MarkedIdeal n V) := by
    dsimp only
    obtain ⟨hI0,hD0,hJ0⟩ := row_records_open hn hL hFull hTr hd O b (if b=a then 1 else 0)
    obtain ⟨hI1,hD1,hJ1⟩ := row_records_open hn hLQ hFullQ hTrQ hDenseQ V (eQ b) (if b=a then 1 else 0)
    obtain ⟨htI,htD,htJ,hrI,hrD,hrJ⟩ := hRows b
    rw [hI0,hD0,hJ0]
    refine ⟨isGeoTestTower_restrict O hL (hParts b).1 R htI,
      isGeoTestTower_restrict O hL (hParts b).2.2.2.2.1 R htD,
      isGeoTestTower_restrict O hL (hParts b).2.2.1 R htJ,?_,?_,?_⟩
    · rw [geoTransformAlong_restrict O hL (hParts b).1 R htI,hrI]
      exact hI1.symm
    · rw [geoTransformAlong_restrict O hL (hParts b).2.2.2.2.1 R htD,hrD]
      exact hD1.symm
    · rw [geoTransformAlong_restrict O hL (hParts b).2.2.1 R htJ,hrJ]
      exact hJ1.symm
  have hCast (bU : Fin loU.length) :
      let bT : Fin (loU.map (strictAlong (restrict O R))).length :=
        ⟨bU.val,by simpa only [List.length_map] using bU.isLt⟩
      let bQ : Fin (loQ.map ((Subtype.val : V → Y) ⁻¹' ·)).length :=
        ⟨bU.val,by simpa only [loU,loQ,List.length_map] using bU.isLt⟩
      oldTraceIdeal (X := CMfd.of (n := n) V) ((Subtype.val : V → Y) ⁻¹' LQ)
          (loU.map (strictAlong (restrict O R))) bT=
        oldTraceIdeal (X := CMfd.of (n := n) V) ((Subtype.val : V → Y) ⁻¹' LQ)
          (loQ.map ((Subtype.val : V → Y) ⁻¹' ·)) bQ ∧
      oldMonomialPart (X := CMfd.of (n := n) V) ((Subtype.val : V → Y) ⁻¹' LQ)
          (loU.map (strictAlong (restrict O R))) (BQ.map ((Subtype.val : V → Y) ⁻¹' ·)) bT=
        oldMonomialPart (X := CMfd.of (n := n) V) ((Subtype.val : V → Y) ⁻¹' LQ)
          (loQ.map ((Subtype.val : V → Y) ⁻¹' ·)) (BQ.map ((Subtype.val : V → Y) ⁻¹' ·)) bQ ∧
      oldResidualPart (X := CMfd.of (n := n) V) ((Subtype.val : V → Y) ⁻¹' LQ)
          (loU.map (strictAlong (restrict O R))) (BQ.map ((Subtype.val : V → Y) ⁻¹' ·)) bT=
        oldResidualPart (X := CMfd.of (n := n) V) ((Subtype.val : V → Y) ⁻¹' LQ)
          (loQ.map ((Subtype.val : V → Y) ⁻¹' ·)) (BQ.map ((Subtype.val : V → Y) ⁻¹' ·)) bQ :=
    canonical_parts_cast _ _ hOldO rfl
  dsimp only [canonicalLowerGammaPrefixData]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := (hRowOpen a).2.2.2.2.1
    rw [hLO,hBorn]
    simp only [finCongr,Equiv.coe_fn_mk,Fin.cast]
    rw [(hCast aU).2.1]
    simpa only [ite_true,LU,loU,bornU,aU,eQ,finCongr,Equiv.coe_fn_mk,Fin.cast] using hh
  · rw [hLO]
    exact isClosedSubmanifold_preimage_val hLQ V
  · rw [hOldO,hBorn]
    exact hFullO
  · rw [hLO,hBorn]
    exact isTransverse_preimage (pullsBackCoordinates_val V) hTrQ
  · rw [hLO,hOldO,hBorn]
    simpa only [List.map_append] using hDenseO
  · rw [hLO,hOldO,hBorn]
    exact hCurrentPrepared.1
  · rw [hLO,hOldO,hBorn]
    exact hCurrentPrepared.2
  · intro bU
    let b : Fin lo.length := ⟨bU.val,by simpa only [loU,List.length_map] using bU.isLt⟩
    have hb : b=a ↔ bU=aU := by simp only [Fin.ext_iff];rfl
    have hh := hRowOpen b
    rw [hLO,hBorn]
    simp only [finCongr,Equiv.coe_fn_mk,Fin.cast]
    rw [(hCast bU).1,(hCast bU).2.1,(hCast bU).2.2]
    simpa only [hb,LU,loU,bornU,aU,b,eQ,finCongr,Equiv.coe_fn_mk,Fin.cast] using hh
theorem currentSharp_restrict {N : Set X} {E : List (Set X)} (O : Opens X) :
    ∀ {Y : CMfd.{u} n} (R : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate (univ : Set X) E) R → CurrentSharpCentres N E R →
      CurrentSharpCentres (X := CMfd.of (n := n) O) ((Subtype.val : O → X) ⁻¹' N)
        (E.map ((Subtype.val : O → X) ⁻¹' ·)) (restrict O R)
  | _,.refl,_hTest,_hSharp => trivial
  | _,.step R C π hπ,hTest,hSharp => by
      refine ⟨currentSharp_restrict O R hTest.1 hSharp.1,?_⟩
      let V := openPreimage R O
      have hUniv : IsClosedSubmanifold n (univ : Set X) :=
        ⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩
      have hE0 := geoTransformAlong_E_eq_of_E_eq
        (𝔍 := geometricTemplate (univ : Set O) (E.map ((Subtype.val : O → X) ⁻¹' ·)))
        (𝔪 := MarkedIdeal.pullback (Subtype.val : O → X) (geometricTemplate (univ : Set X) E)) rfl (restrict O R)
      have hE1 := congrArg MarkedIdeal.E (geoTransformAlong_restrict O hUniv
        (isCoherent_unitIdeal (n := n) (M := X)) R hTest.1)
      have hE : (geoTransformAlong
          (geometricTemplate (univ : Set O) (E.map ((Subtype.val : O → X) ⁻¹' ·))) (restrict O R)).E=
          ((geoTransformAlong (geometricTemplate (univ : Set X) E) R).E).map
            ((Subtype.val : V → _) ⁻¹' ·) := hE0.trans hE1
      intro y hy
      have hBad := hSharp.2 hy
      rw [strictAlong_restrict O R N,hE]
      refine ⟨hBad.1,fun hNC => hBad.2 ?_⟩
      exact HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff.mp hNC

private theorem upper_protection_restrict (hn : 0<n) {N H L : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hBorn : IsSNCDivisor n born) (hTrBorn : IsTransverse n N born)
    (i j : Fin old.length)
    (hAux : IsSNCDivisor n (H :: (old.eraseIdx i.val ++ born)))
    (hAuxTr : IsTransverse n N (H :: (old.eraseIdx i.val ++ born)))
    (R : BlowupTower X Y) (hState : protectedGammaPrefixData N H L old born i j R) (O : Opens X) :
    let NU := (Subtype.val : O → X) ⁻¹' N
    let HU := (Subtype.val : O → X) ⁻¹' H
    let LU := (Subtype.val : O → X) ⁻¹' L
    let oldU := old.map ((Subtype.val : O → X) ⁻¹' ·)
    let bornU := born.map ((Subtype.val : O → X) ⁻¹' ·)
    let iU : Fin oldU.length := ⟨i.val,by simpa only [oldU,List.length_map] using i.isLt⟩
    let jU : Fin oldU.length := ⟨j.val,by simpa only [oldU,List.length_map] using j.isLt⟩
    protectedGammaPrefixData (X := CMfd.of (n := n) O) NU HU LU oldU bornU iU jU (restrict O R) ∧
      MarkedIdeal.pullback (Subtype.val : openPreimage R O → Y)
        (chronologicalMarked (⟨N,born,vanishingIdeal (n := n) (N ∩ H),0⟩ : MarkedIdeal n X) R)=
      chronologicalMarked (⟨NU,bornU,vanishingIdeal (n := n) (NU ∩ HU),0⟩ : MarkedIdeal n O) (restrict O R) := by
  let NU := (Subtype.val : O → X) ⁻¹' N
  let HU := (Subtype.val : O → X) ⁻¹' H
  let LU := (Subtype.val : O → X) ⁻¹' L
  let oldU := old.map ((Subtype.val : O → X) ⁻¹' ·)
  let bornU := born.map ((Subtype.val : O → X) ⁻¹' ·)
  let iU : Fin oldU.length := ⟨i.val,by simpa only [oldU,List.length_map] using i.isLt⟩
  let jU : Fin oldU.length := ⟨j.val,by simpa only [oldU,List.length_map] using j.isLt⟩
  let V := openPreimage R O
  let NQ := strictAlong R N
  let oldQ := old.map (strictAlong R)
  let BQ := (geoTransformAlong (geometricTemplate N born) R).E
  let FQ := oldQ.eraseIdx i.val ++ BQ
  let SiQ := strictAlong R (N ∩ H)
  let M : MarkedIdeal n X := ⟨N,born,vanishingIdeal (n := n) (N ∩ H),0⟩
  obtain ⟨hUpper,hAmbient,hSharp,hAuxQ,hAuxTrQ,hLQ,hMN,hME,hMd,hMI,hSi,hNC,hDense,hSiTrace⟩ := hState
  have hSingle : IsSNCDivisor n [H] := isSNCDivisor_of_sublist hAux (by simp)
  have hTrSingle : IsTransverse n N [H] := isTransverse_of_forall_mem hAuxTr
    (fun K hK => by rw [List.mem_singleton.mp hK];simp)
  obtain ⟨hSiSource,hNormalized⟩ := transverse_trace_reduced hn hN hSingle hTrSingle
  obtain ⟨_hcTrace,hNZ,hPrincipal,_hOrder⟩ := actual_normalized_transverse_member_geometry hn hN hSingle hTrSingle
  rw [hNormalized] at hNZ hPrincipal
  have hMwf : M.IsWellFormed := ⟨hN,VanishingIdealCoherent.isCoherent_vanishingIdeal hSiSource,hBorn,hTrBorn⟩
  have hMOpen : MarkedIdeal.pullback (Subtype.val : O → X) M=
      (⟨NU,bornU,vanishingIdeal (n := n) (NU ∩ HU),0⟩ : MarkedIdeal n O) :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl (actual_vanishingIdeal_open _ hSiSource O) rfl
  have hChron := chronologicalMarked_open hn M hMwf rfl hNZ hPrincipal R hUpper O
  rw [hMOpen] at hChron
  have hNO : strictAlong (restrict O R) NU=(Subtype.val : V → Y) ⁻¹' NQ := strictAlong_restrict O R N
  have hHO : strictAlong (restrict O R) HU=(Subtype.val : V → Y) ⁻¹' strictAlong R H := strictAlong_restrict O R H
  have hLO : strictAlong (restrict O R) LU=(Subtype.val : V → Y) ⁻¹' strictAlong R L := strictAlong_restrict O R L
  have hSiO : strictAlong (restrict O R) (NU ∩ HU)=(Subtype.val : V → Y) ⁻¹' SiQ :=
    strictAlong_restrict O R (N ∩ H)
  have hOldO : oldU.map (strictAlong (restrict O R))=oldQ.map ((Subtype.val : V → Y) ⁻¹' ·) :=
    strict_old_open O R old
  have hBornO : (geoTransformAlong (geometricTemplate NU bornU) (restrict O R)).E=
      BQ.map ((Subtype.val : V → Y) ⁻¹' ·) := by
    have hE0 := geoTransformAlong_E_eq_of_E_eq
      (𝔍 := geometricTemplate NU bornU)
      (𝔪 := MarkedIdeal.pullback (Subtype.val : O → X) (geometricTemplate N born)) rfl (restrict O R)
    exact hE0.trans (congrArg MarkedIdeal.E
      (geoTransformAlong_restrict O hN (isCoherent_unitIdeal (n := n) (M := X)) R hUpper))
  have hF : (oldU.map (strictAlong (restrict O R))).eraseIdx iU.val ++
      (geoTransformAlong (geometricTemplate NU bornU) (restrict O R)).E=
      FQ.map ((Subtype.val : V → Y) ⁻¹' ·) := by
    rw [hOldO,hBornO]
    simp only [FQ,iU,List.eraseIdx_map,List.map_append]
  have hGetj : oldU.get jU=(Subtype.val : O → X) ⁻¹' old.get j := by simp [oldU,jU]
  have hOldJ : strictAlong (restrict O R) (oldU.get jU)=
      (Subtype.val : V → Y) ⁻¹' strictAlong R (old.get j) := by
    rw [hGetj]
    exact strictAlong_restrict O R _
  have hRecord : chronologicalMarked M R=(⟨NQ,BQ,vanishingIdeal (n := n) SiQ,0⟩ : MarkedIdeal n Y) :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of hMN hME hMI hMd
  have hTargetRecord : chronologicalMarked
      (⟨NU,bornU,vanishingIdeal (n := n) (NU ∩ HU),0⟩ : MarkedIdeal n O) (restrict O R)=
      (⟨(Subtype.val : V → Y) ⁻¹' NQ,BQ.map ((Subtype.val : V → Y) ⁻¹' ·),
        vanishingIdeal (n := n) ((Subtype.val : V → Y) ⁻¹' SiQ),0⟩ : MarkedIdeal n V) := by
    rw [←hChron,hRecord]
    exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl (actual_vanishingIdeal_open _ hSi V) rfl
  refine ⟨?_,hChron⟩
  dsimp only [protectedGammaPrefixData]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := isGeoTestTower_restrict O hN (isCoherent_unitIdeal (n := n) (M := X)) R hUpper
    simpa only [geometricTemplate,MarkedIdeal.pullback,BlowupExceptionalDivisor.pullback_unitIdeal] using hh
  · have hUniv : IsClosedSubmanifold n (univ : Set X) :=
      ⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩
    have hh := isGeoTestTower_restrict O hUniv (isCoherent_unitIdeal (n := n) (M := X)) R hAmbient
    simpa only [geometricTemplate,MarkedIdeal.pullback,preimage_univ,List.map_append,
      BlowupExceptionalDivisor.pullback_unitIdeal] using hh
  · simpa only [List.map_append] using currentSharp_restrict O R hAmbient hSharp
  · rw [hHO,hF]
    exact isSNCDivisor_map_preimage (pullsBackCoordinates_val V) continuous_subtype_val hAuxQ
  · rw [hNO,hHO,hF]
    exact isTransverse_preimage (pullsBackCoordinates_val V) hAuxTrQ
  · rw [hLO,hNO,hOldJ,hLQ]
    rfl
  · rw [hNO]
    exact congrArg MarkedIdeal.N hTargetRecord
  · rw [hBornO]
    exact congrArg MarkedIdeal.E hTargetRecord
  · exact congrArg MarkedIdeal.d hTargetRecord
  · rw [hSiO]
    exact congrArg MarkedIdeal.ideal hTargetRecord
  · rw [hSiO]
    exact isClosedSubmanifold_preimage_val hSi V
  · rw [hSiO,hF]
    exact hasNormalCrossings_preimage (pullsBackCoordinates_val V) hNC
  · rw [hSiO,hF]
    exact open_full_density hDense V
  · rw [hSiO,hNO,hHO]
    exact congrArg (fun Z : Set Y => (Subtype.val : V → Y) ⁻¹' Z) hSiTrace

/-- Ordinary CURRENT prepared source data internally derive raw local CAN,
all lower WHOLE parts, SAME protected whole chronology/tests/NC/density and
every original empty year on EVERY literal restricted native prefix. -/
theorem actual_prepared_singleton_gamma_open_compatibility (hn : 0<n) {N H L : Set X}
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
    (R : BlowupTower X Y)
    (hCan : ResolutionDriver.IsCanonicalSegment (⟨L,born,oldMonomialPart L (old.eraseIdx j.val) born a,1⟩ : MarkedIdeal n X)
      (fun {Q} S => towerInvAlong (⟨L,born,oldMonomialPart L (old.eraseIdx j.val) born a,1⟩ : MarkedIdeal n X) (Y := Q) S) R) (O : Opens X) :
    let NU := (Subtype.val : O → X) ⁻¹' N
    let HU := (Subtype.val : O → X) ⁻¹' H
    let LU := (Subtype.val : O → X) ⁻¹' L
    let oldU := old.map ((Subtype.val : O → X) ⁻¹' ·)
    let bornU := born.map ((Subtype.val : O → X) ⁻¹' ·)
    let loU := (old.eraseIdx j.val).map ((Subtype.val : O → X) ⁻¹' ·)
    let iU : Fin oldU.length := ⟨i.val,by simpa only [oldU,List.length_map] using i.isLt⟩
    let jU : Fin oldU.length := ⟨j.val,by simpa only [oldU,List.length_map] using j.isLt⟩
    let aU : Fin loU.length := ⟨a.val,by simpa only [loU,List.length_map] using a.isLt⟩
    let Phase : MarkedIdeal n X := ⟨L,born,oldMonomialPart L (old.eraseIdx j.val) born a,1⟩
    let PhaseU : MarkedIdeal n O := ⟨LU,bornU,oldMonomialPart (X := CMfd.of (n := n) O) LU loU bornU aU,1⟩
    oldU.eraseIdx jU.val=loU ∧
      (IsGeoResolution Phase R → IsGeoResolution PhaseU (restrict O R)) ∧
      ∀ k : ℕ,
        let S := BlowupTowerSplit.head R k
        let V := openPreimage S O
        (restrict O S).length=S.length ∧
        ResolutionInvariantSpec.IsCanonical PhaseU
          (fun {Q} P => towerInvAlong PhaseU (Y := Q) P) (restrict O S) ∧
        (∀ y : V,towerInvAlong PhaseU (restrict O S) y=towerInvAlong Phase S y.val) ∧
        protectedGammaPrefixData (X := CMfd.of (n := n) O) NU HU LU oldU bornU iU jU (restrict O S) ∧
        canonicalLowerGammaPrefixData (X := CMfd.of (n := n) O) LU loU bornU aU (restrict O S) ∧
        MarkedIdeal.pullback (Subtype.val : V → _) (chronologicalMarked
          (⟨N,born,vanishingIdeal (n := n) (N ∩ H),0⟩ : MarkedIdeal n X) S)=
        chronologicalMarked (⟨NU,bornU,vanishingIdeal (n := n) (NU ∩ HU),0⟩ : MarkedIdeal n O) (restrict O S) := by
  let Phase : MarkedIdeal n X := ⟨L,born,oldMonomialPart L (old.eraseIdx j.val) born a,1⟩
  have hLowerFull : IsSNCDivisor n (old.eraseIdx j.val ++ born) := isSNCDivisor_of_sublist hFull
    ((List.eraseIdx_sublist old j.val).append (List.Sublist.refl born))
  have hParts := actual_old_parts_geometry hn hL hLowerFull hLTr hLDense a
  have hPhaseOpen := (row_records_open hn hL hLowerFull hLTr hLDense O a 1).2.1
  dsimp only
  refine ⟨by simp only [List.eraseIdx_map],?_,?_⟩
  · intro hResolution
    rw [hPhaseOpen]
    exact isGeoResolution_restrict O hL hParts.2.2.2.2.1 hResolution
  · intro k
    let S := BlowupTowerSplit.head R k
    have hCanS := native_segment_head Phase R hCan k
    obtain ⟨hUpperS,hLowerS⟩ := actual_prepared_singleton_gamma_prefix_protection hn hN hFull hTr hDense
      i j hne hAux hAuxTr hLTrace hL hLTr hLDense hOrd hPrep a ha hOther v hFirst hBound S hCanS
    have hPhaseTest : IsGeoTestTower Phase S := by
      simpa only [ite_true] using (hLowerS.2.2.2.2.2.2.2 a).2.1
    have hUpperO := upper_protection_restrict hn hN
      (isSNCDivisor_of_sublist hFull (List.sublist_append_right old born)) hTr
      i j hAux hAuxTr S hUpperS O
    have hLowerO := lower_parts_restrict hn hL hLowerFull hLTr hLDense a S hLowerS O
    refine ⟨native_gamma_restricted_length O S,?_,?_,hUpperO.1,hLowerO,hUpperO.2⟩
    · rw [hPhaseOpen]
      exact native_gamma_canonical_restrict Phase hL hParts.2.2.2.2.1 O S hPhaseTest hCanS
    · intro y
      rw [hPhaseOpen]
      exact MonomialInvariantFunctorialAlong.towerInvAlong_restrict Phase hL hParts.2.2.2.2.1 O S hPhaseTest y

end
end Hironaka.HironakaActualProtectedGammaOpenCompatibility
