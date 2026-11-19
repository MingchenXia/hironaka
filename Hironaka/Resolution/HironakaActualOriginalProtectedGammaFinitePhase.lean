import Hironaka.Resolution.HironakaActualProtectedGammaPrefixHistory
import Hironaka.Resolution.HironakaMarkOneNoncompactNativePhase
import Hironaka.Invariant.MonomialInvariantFunctorialAlong

/-! ORIGINAL current mixed data internally produce the finite protected
native lower monomial phase. Source-first mathematics:
hironaka-actual-original-protected-gamma-finite-phase.tex.
No complete lower sharp driver/gluing/global K1 closure is claimed.
Reused private source-coordinate/open/label arguments carry zero extra credit. -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualOriginalProtectedGammaFinitePhase
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms NormalCrossings NormalCrossingsComparison
  NormalCrossingsInvariance SimultaneousNormalCrossings BlowupStrictSubmanifold
  HironakaActualProtectedOtherRowLocalStep HironakaG4PreparedCentreCoordinates
  HironakaG4ProtectedResidualEndpoint HironakaG4OriginalSelectedResidualTail
  HironakaG4RecordedTowerResidualCompatibility HironakaG4LowerPreparedNeighborhood
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpActualTraceIncidence HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4ResidualInductionInputs
  HironakaG4ActiveMonomialSharpBad HomogenizedGlueingTower
  RelativePrincipalizationSpan RestrictedIdealExtension GermIdealPullbackCalculus InvertibleIdealQuotient
  MonomialPartAlong MonomialCaseAlong MonomialInvariant MonomialCase MonomialStepAlong
  MonomialInvariantFunctorialAlong MonomialCaseLocal BoundaryCount
  DivisorExponentAlong GermIdealOrder ResolutionInvariantSpec ResolutionDriver
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen
  MarkedIdealBiholomorphism MarkedIdealTowerTransport DerivativeIdealAlongEtale
  HironakaSharpActualStrictTraceOpenNonmonomial MonomialPartEtale BlowupFlatCoordinates
  HironakaSharpActualChronologicalStrictStep MemberInterAlong BlowupRestrictOpen IdealWeightPowers
  HironakaActualProtectedGammaPrefixHistory HironakaMarkOneGammaBoundedMaxima
  HironakaMarkOneNoncompactNativePhase

variable {n : ℕ} {X Y : CMfd.{u} n}

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


private def innerOpen (U V : Opens X) : Opens U :=
  ⟨(Subtype.val : U → X) ⁻¹' V,V.isOpen.preimage continuous_subtype_val⟩

private def innerOpenEquiv (U V : Opens X) (hVU : (V : Set X) ⊆ U) :
    innerOpen U V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V where
  toFun a := ⟨a.val.val,a.property⟩
  invFun a := ⟨⟨a.val,hVU a.property⟩,a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff V _).mp
    change ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      ((Subtype.val : U → X) ∘ (Subtype.val : innerOpen U V → U))
    exact contMDiff_subtype_val.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (innerOpen U V) _).mp
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact contMDiff_subtype_val

private theorem actual_vanishingIdeal_open (Z : Set X)
    (hZ : IsClosedSubmanifold n Z) (U : Opens X) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (vanishingIdeal (n := n) Z)=
      vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' Z) := by
  have hZU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hZ U
  have h := BlowupRestrictOpen.pullback_vanishingIdeal_opens (n := n) (m := n) U (id : U → U) Z
  rw [BlowupControlledTransform.pullback_id
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hZU)] at h
  exact h.symm

private theorem nonunit_pullback_restrict {Z : CMfd.{u} n} {I : GermIdeal n X}
    (hI : I.IsCoherent) {f : Z → X}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    {L : Set Z} {z : Z} (hz : z ∈ L) (hnot : ¬I.mem (f z) 1) :
    ¬(restrictOn n L (GermIdeal.pullback (m := n) f I)).mem z 1 := by
  have hzI : f z ∈ I.zeroLocus := by
    intro g hg
    by_contra hne
    exact hnot (CompanionReduction.one_mem_of_apply_ne_zero hI hg hne)
  have hPull := BlowupExceptionalDivisor.zeroLocus_pullback hf hI
  have hzPull : z ∈ (GermIdeal.pullback (m := n) f I).zeroLocus := by
    rw [hPull]
    exact hzI
  have hzRes := (zeroLocus_restrictOn_iff (isCoherent_pullback hf hI) hz).mpr hzPull
  exact fun hunit => one_ne_zero (hzRes 1 hunit)

private theorem nonunit_pullback {Z : CMfd.{u} n} {I : GermIdeal n X}
    (hI : I.IsCoherent) {f : Z → X}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    {z : Z} (hnot : ¬I.mem (f z) 1) : ¬(GermIdeal.pullback (m := n) f I).mem z 1 := by
  have hzI : f z ∈ I.zeroLocus := by
    intro g hg
    by_contra hne
    exact hnot (CompanionReduction.one_mem_of_apply_ne_zero hI hg hne)
  have hzPull : z ∈ (GermIdeal.pullback (m := n) f I).zeroLocus := by
    rw [BlowupExceptionalDivisor.zeroLocus_pullback hf hI]
    exact hzI
  exact fun hunit => one_ne_zero (hzPull 1 hunit)

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


private theorem other_rows_unit_of_original_labels {r : ℕ} {L : Set X}
    {lo born : List (Set X)} (labels : Fin r → Set X) (i j : Fin r)
    (a : Fin lo.length) (ha : lo.get a=labels i) (hOld : IsSNCDivisor n lo)
    {x : X} (hx : x ∈ lo.get a)
    (hCover : ∀ b : Fin lo.length,∃ h : Fin r,h ≠ j ∧ lo.get b=labels h)
    (hRows : ∀ h : Fin r,h ≠ j → h ≠ i → ∃ b : Fin lo.length,
      lo.get b=labels h ∧ ∀ y ∈ L,(oldMonomialPart L lo born b).mem y 1) :
    ∀ y ∈ L,∀ b : Fin lo.length,b ≠ a → (oldMonomialPart L lo born b).mem y 1 := by
  intro y hy b hba
  obtain ⟨h,hhj,hb⟩ := hCover b
  have hhi : h ≠ i := by
    intro he
    have hSame : lo.get b=lo.get a := by rw [hb,he,←ha]
    have hxB : x ∈ lo.get b := by rw [hSame];exact hx
    exact hba (SimultaneousNormalCrossings.eq_of_eventually_mem_iff hOld hxB hx
      (Eventually.of_forall fun z => by rw [hSame]))
  obtain ⟨c,hc,hUnit⟩ := hRows h hhj hhi
  have hGet : lo.get b=lo.get c := hb.trans hc.symm
  change (monomialPartAlong n L (restrictOn n L (vanishingIdeal (n := n) (lo.get b))) born).mem y 1
  rw [hGet]
  exact hUnit y hy

private theorem other_units_open (hn : 0<n) {L : Set X} {lo born : List (Set X)}
    (hL : IsClosedSubmanifold n L) (hFull : IsSNCDivisor n (lo ++ born))
    (hTr : IsTransverse n L born) (hDense : L ⊆ closure (L \ ⋃ K ∈ lo ++ born,K))
    (a : Fin lo.length)
    (hOther : ∀ x ∈ L,∀ b : Fin lo.length,b ≠ a → (oldMonomialPart L lo born b).mem x 1)
    (U : Opens X) :
    let LU := (Subtype.val : U → X) ⁻¹' L
    let loU := lo.map ((Subtype.val : U → X) ⁻¹' ·)
    let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    let aU : Fin loU.length := ⟨a.val,by simpa only [loU,List.length_map] using a.isLt⟩
    ∀ y ∈ LU,∀ b : Fin loU.length,b ≠ aU →
      (oldMonomialPart (X := CMfd.of (n := n) U) LU loU BU b).mem y 1 := by
  let LU := (Subtype.val : U → X) ⁻¹' L
  let loU := lo.map ((Subtype.val : U → X) ⁻¹' ·)
  let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let aU : Fin loU.length := ⟨a.val,by simpa only [loU,List.length_map] using a.isLt⟩
  change ∀ y ∈ LU,∀ b : Fin loU.length,b ≠ aU →
    (oldMonomialPart (X := CMfd.of (n := n) U) LU loU BU b).mem y 1
  intro y hy b hba
  let b₀ : Fin lo.length := ⟨b.val,by simpa only [loU,List.length_map] using b.isLt⟩
  have hb₀ : b₀ ≠ a := by
    intro he
    apply hba
    have hv : b₀.val=a.val := congrArg (fun t : Fin lo.length => t.val) he
    exact Fin.ext hv
  have hGet : loU.get b=(Subtype.val : U → X) ⁻¹' lo.get b₀ := by
    simp [loU,b₀,List.get_eq_getElem]
  have hD : oldMonomialPart (X := CMfd.of (n := n) U) LU loU BU b=
      GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldMonomialPart L lo born b₀) := by
    change monomialPartAlong n LU (restrictOn n LU (vanishingIdeal (n := n) (loU.get b))) BU=_
    rw [hGet]
    exact (HironakaG4PreparedMixedSelectedStep.open_parts_pullback_native hn hL hFull hTr hDense U b₀).1
  rw [hD]
  exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self
    ⟨(fun _ => (1 : ℂ)),hOther y.val hy b₀ hb₀,rfl⟩ (holomorphicAt_const 1))

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

theorem exists_actual_original_local_protected_gamma_phase (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i j : Fin E.length) (hne : j ≠ i) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n Si ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      Si ⊆ closure (Si \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    {x : Y}
    (hxi : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)
    (hxj : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
    (hNonunit : let A := geoTransformAlong (geometricTemplate W []) T
      ¬(monomialPartAlong n A.N
        (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E).mem x 1) :
    ∃ (U₀ : Opens Y) (U₁ : Opens U₀) (U₂ : Opens U₁),
      let A := geoTransformAlong (geometricTemplate W []) T
      let N := (Subtype.val : U₂ → U₁) ⁻¹' ((Subtype.val : U₁ → U₀) ⁻¹' ((Subtype.val : U₀ → Y) ⁻¹' A.N))
      let old := (((E.map (strictAlong T)).map ((Subtype.val : U₀ → Y) ⁻¹' ·)).map
        ((Subtype.val : U₁ → U₀) ⁻¹' ·)).map ((Subtype.val : U₂ → U₁) ⁻¹' ·)
      let born := ((A.E.map ((Subtype.val : U₀ → Y) ⁻¹' ·)).map
        ((Subtype.val : U₁ → U₀) ⁻¹' ·)).map ((Subtype.val : U₂ → U₁) ⁻¹' ·)
      let Si := (Subtype.val : U₂ → U₁) ⁻¹' ((Subtype.val : U₁ → U₀) ⁻¹' ((Subtype.val : U₀ → Y) ⁻¹'
        (A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)))
      let L := (Subtype.val : U₂ → U₁) ⁻¹' ((Subtype.val : U₁ → U₀) ⁻¹' ((Subtype.val : U₀ → Y) ⁻¹'
        (A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)))
      let i₂ : Fin old.length := ⟨i.val,by simpa only [old,List.length_map] using i.isLt⟩
      let j₂ : Fin old.length := ⟨j.val,by simpa only [old,List.length_map] using j.isLt⟩
      let M := MarkedIdeal.pullback (Subtype.val : U₂ → U₁)
        (MarkedIdeal.pullback (Subtype.val : U₁ → U₀) (MarkedIdeal.pullback (Subtype.val : U₀ → Y)
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T)))
      ∃ (H : Set U₂) (a : Fin (old.eraseIdx j₂.val).length),
        (old.eraseIdx j₂.val).get a=old.get i₂ ∧ Si=N ∩ H ∧
        M=(⟨N,born,vanishingIdeal (n := n) (N ∩ H),0⟩ : MarkedIdeal n U₂) ∧
        let Phase : MarkedIdeal n U₂ := ⟨L,born,
          oldMonomialPart (X := CMfd.of (n := n) U₂) L (old.eraseIdx j₂.val) born a,1⟩
        ∃ v : MonomialInvariant.Val,(ofLex v).1=n-1 ∧
          (∀ y ∈ Phase.cosupp,gammaAlong n Phase.N Phase.ideal Phase.E Phase.d y ≤ (v : WithBot MonomialInvariant.Val)) ∧
          ∃ x₂ : U₂,x₂.val.val.val=x ∧ x₂ ∈ Phase.cosupp ∧
            gammaAlong n Phase.N Phase.ideal Phase.E Phase.d x₂=(v : WithBot MonomialInvariant.Val) ∧
            ∃ (Z : CMfd.{u} n) (R : BlowupTower (CMfd.of (n := n) U₂) Z),
              IsCanonicalSegment Phase (fun {Q} R => towerInvAlong Phase (Y := Q) R) R ∧ IsGeoResolution Phase R ∧
              ∀ k : ℕ,
                protectedGammaPrefixData (X := CMfd.of (n := n) U₂) N H L old born i₂ j₂ (BlowupTowerSplit.head R k) ∧
                canonicalLowerGammaPrefixData (X := CMfd.of (n := n) U₂) L (old.eraseIdx j₂.val) born a
                  (BlowupTowerSplit.head R k) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let born := A.E
  let J := fun h : Fin E.length =>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).ideal
  let Si := A.N ∩ (J i).zeroLocus
  let Sj := A.N ∩ (J j).zeroLocus
  let Di := monomialPartAlong n A.N
    (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) born
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hN : IsClosedSubmanifold n A.N := hRecorded.1
  have hFullCurrent : IsSNCDivisor n (old ++ born) := hRecorded.2.1
  have hTrCurrent : IsTransverse n A.N born := hRecorded.2.2.1
  have hDenseCurrent : A.N ⊆ closure (A.N \ ⋃ H ∈ old ++ born,H) := hRecorded.2.2.2.1
  have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=A.N at hNi
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N=A.N at hNj
  have hxiA : x ∈ Si := by simpa only [hNi] using hxi
  have hxjA : x ∈ Sj := by simpa only [hNj] using hxj
  have hOrdA : ∀ y ∈ A.N,ordinaryTraceOrder A.N (J i) y ≤ 1 := by simpa only [hNi] using hOrd
  have hProtect := actual_original_selected_endpoint_protection hn hW hE hdense i T hT hFull
    hOrdA hNC hDenseS
  have hSi : IsClosedSubmanifold n Si := hProtect.1
  have hWholeSi : J i=vanishingIdeal (n := n) Si := hProtect.2.1
  have hLower := actual_original_lower_prepared_neighborhood hn hW hE hdense i T hT hFull
    hOrd hNC hDenseS j hne hxi hxj
  obtain ⟨U₀,hx₀,hLN,hLE,hLT,hLD,hLRows,hLP⟩ := hLower
  let N₀ := (Subtype.val : U₀ → Y) ⁻¹' A.N
  let old₀ := old.map ((Subtype.val : U₀ → Y) ⁻¹' ·)
  let born₀ := born.map ((Subtype.val : U₀ → Y) ⁻¹' ·)
  let L₀ := (Subtype.val : U₀ → Y) ⁻¹' Sj
  let lo₀ := (old.eraseIdx j.val).map ((Subtype.val : U₀ → Y) ⁻¹' ·)
  change IsClosedSubmanifold n L₀ at hLN
  change IsSNCDivisor n (lo₀ ++ born₀) at hLE
  change IsTransverse n L₀ born₀ at hLT
  change L₀ ⊆ closure (L₀ \ ⋃ H ∈ lo₀ ++ born₀,H) at hLD
  change ∀ y ∈ L₀,(∀ a,ordinaryTraceOrder L₀ (oldResidualPart (X := CMfd.of (n := n) U₀) L₀ lo₀ born₀ a) y ≤ 1) ∧
    IsPreparedResidualSNCAt (X := CMfd.of (n := n) U₀) L₀ lo₀ born₀ y at hLP
  obtain ⟨V,hxV,hVU₀,H,hAux,hAuxTr,hSiV,hJiV,hOtherV⟩ :=
    protected_slice_window hn hW hE hdense i T hT hFull hOrd hNC hDenseS hxi U₀ hx₀
  let U₁ := innerOpen U₀ V
  let e := innerOpenEquiv U₀ V hVU₀
  let x₁ : U₁ := ⟨⟨x,hx₀⟩,hxV⟩
  let N₁ := (Subtype.val : U₁ → U₀) ⁻¹' N₀
  let old₁ := old₀.map ((Subtype.val : U₁ → U₀) ⁻¹' ·)
  let born₁ := born₀.map ((Subtype.val : U₁ → U₀) ⁻¹' ·)
  let L₁ := (Subtype.val : U₁ → U₀) ⁻¹' L₀
  let lo₁ := lo₀.map ((Subtype.val : U₁ → U₀) ⁻¹' ·)
  let Si₁ := (Subtype.val : U₁ → U₀) ⁻¹' ((Subtype.val : U₀ → Y) ⁻¹' Si)
  let H₁ := e ⁻¹' H
  let i₁ : Fin old₁.length := ⟨i.val,by simpa only [old₁,old₀,old,List.length_map] using i.isLt⟩
  let j₁ : Fin old₁.length := ⟨j.val,by simpa only [old₁,old₀,old,List.length_map] using j.isLt⟩
  have hne₁ : j₁ ≠ i₁ := by
    intro he
    have hv : j₁.val=i₁.val := congrArg (fun a : Fin old₁.length => a.val) he
    exact hne (Fin.ext hv)
  have hLo₁ : lo₁=old₁.eraseIdx j.val := by
    simp only [lo₁,lo₀,old₁,old₀,List.eraseIdx_map]
  have hN₀ : IsClosedSubmanifold n N₀ := isClosedSubmanifold_preimage_val hN U₀
  have hFull₀ : IsSNCDivisor n (old₀ ++ born₀) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val U₀) continuous_subtype_val hFullCurrent
  have hTr₀ : IsTransverse n N₀ born₀ := isTransverse_preimage (pullsBackCoordinates_val U₀) hTrCurrent
  have hDense₀ : N₀ ⊆ closure (N₀ \ ⋃ H ∈ old₀ ++ born₀,H) := by
    simpa only [List.map_append] using open_full_density hDenseCurrent U₀
  have hN₁ : IsClosedSubmanifold n N₁ := isClosedSubmanifold_preimage_val hN₀ U₁
  have hFull₁ : IsSNCDivisor n (old₁ ++ born₁) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val U₁) continuous_subtype_val hFull₀
  have hTr₁ : IsTransverse n N₁ born₁ := isTransverse_preimage (pullsBackCoordinates_val U₁) hTr₀
  have hDense₁ : N₁ ⊆ closure (N₁ \ ⋃ H ∈ old₁ ++ born₁,H) := by
    simpa only [List.map_append] using open_full_density (X := CMfd.of (n := n) U₀) hDense₀ U₁
  have hFpull : ((old.eraseIdx i.val ++ born).map ((Subtype.val : V → Y) ⁻¹' ·)).map
      (e ⁻¹' ·)=old₁.eraseIdx i.val ++ born₁ := by
    dsimp only [old₁,old₀,born₁,born₀]
    simp only [List.map_append,List.eraseIdx_map,List.map_map]
    rfl
  have hAux₁ : IsSNCDivisor n (H₁ :: (old₁.eraseIdx i.val ++ born₁)) := by
    have hh := isSNCDivisor_map_preimage (pullsBackCoordinates e) e.continuous hAux
    change IsSNCDivisor n ((H :: (old.eraseIdx i.val ++ born).map
      ((Subtype.val : V → Y) ⁻¹' ·)).map (e ⁻¹' ·)) at hh
    rw [List.map_cons,hFpull] at hh
    exact hh
  have hAuxTr₁ : IsTransverse n N₁ (H₁ :: (old₁.eraseIdx i.val ++ born₁)) := by
    have hh := isTransverse_preimage (pullsBackCoordinates e) hAuxTr
    change IsTransverse n N₁ ((H :: (old.eraseIdx i.val ++ born).map
      ((Subtype.val : V → Y) ⁻¹' ·)).map (e ⁻¹' ·)) at hh
    rw [List.map_cons,hFpull] at hh
    exact hh
  have hSi₁ : Si₁=N₁ ∩ H₁ := by
    have hh := congrArg (fun S : Set V => e ⁻¹' S) hSiV
    exact hh
  have hGetj₁ : old₁.get j₁=(Subtype.val : U₁ → U₀) ⁻¹'
      ((Subtype.val : U₀ → Y) ⁻¹' strictAlong T (E.get j)) := by
    simp [old₁,old₀,old,j₁,List.get_eq_getElem]
  have hSjTrace₁ : L₁=N₁ ∩ old₁.get j₁ := by
    rw [hGetj₁]
    exact congrArg (fun S : Set V => e ⁻¹' S) (hOtherV j hne).2
  have hLN₁ : IsClosedSubmanifold n L₁ := isClosedSubmanifold_preimage_val hLN U₁
  have hLE₁ : IsSNCDivisor n (lo₁ ++ born₁) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val U₁) continuous_subtype_val hLE
  have hLT₁ : IsTransverse n L₁ born₁ := isTransverse_preimage (pullsBackCoordinates_val U₁) hLT
  have hLD₁ : L₁ ⊆ closure (L₁ \ ⋃ H ∈ lo₁ ++ born₁,H) := by
    simpa only [List.map_append] using open_full_density (X := CMfd.of (n := n) U₀) hLD U₁
  have hLowerOpen := current_prepared_open (X := CMfd.of (n := n) U₀) hn hLN hLE hLT hLD
    (fun y hy => (hLP y hy).1) (fun y hy => (hLP y hy).2) U₁
  change (∀ y ∈ L₁,∀ a,ordinaryTraceOrder L₁ (oldResidualPart (X := CMfd.of (n := n) U₁) L₁ lo₁ born₁ a) y ≤ 1) ∧
    (∀ y ∈ L₁,IsPreparedResidualSNCAt (X := CMfd.of (n := n) U₁) L₁ lo₁ born₁ y) at hLowerOpen
  obtain ⟨a₀,ha₀,hRowI⟩ := hLRows i (Ne.symm hne)
  rw [if_pos rfl] at hRowI
  have hD₀ : oldMonomialPart (X := CMfd.of (n := n) U₀) L₀ lo₀ born₀ a₀=
      restrictOn n L₀ (GermIdeal.pullback (m := n) (Subtype.val : U₀ → Y) Di) := hRowI.1
  have hBornCurrent : IsSNCDivisor n born := isSNCDivisor_of_sublist hFullCurrent (List.sublist_append_right old born)
  have hIRow := hRecorded.2.2.2.2 i
  have hcDi : Di.IsCoherent := isCoherent_monomialPartAlong hn hN hBornCurrent hTrCurrent hIRow.1 hIRow.2.1
  have hD₀not : ¬(oldMonomialPart (X := CMfd.of (n := n) U₀) L₀ lo₀ born₀ a₀).mem (⟨x,hx₀⟩ : U₀) 1 := by
    rw [hD₀]
    exact nonunit_pullback_restrict (Z := CMfd.of (n := n) U₀) hcDi contMDiff_subtype_val hxjA hNonunit
  have hOldLower₀ : IsSNCDivisor n lo₀ := isSNCDivisor_of_sublist hLE (List.sublist_append_left lo₀ born₀)
  have hxL₀ : (⟨x,hx₀⟩ : U₀) ∈ L₀ := hxjA
  have hxOld₀ : (⟨x,hx₀⟩ : U₀) ∈ lo₀.get a₀ :=
    canonical_monomial_proper_subset_member (X := CMfd.of (n := n) U₀) hn hLN hLE hLT hLD a₀ ⟨hxL₀,hD₀not⟩
  let labels₀ : Fin E.length → Set U₀ := fun h => (Subtype.val : U₀ → Y) ⁻¹' strictAlong T (E.get h)
  have hCover₀ : ∀ b : Fin lo₀.length,∃ h : Fin E.length,h ≠ j ∧ lo₀.get b=labels₀ h := by
    intro b
    let b₀ : Fin (old.eraseIdx j.val).length := ⟨b.val,by simpa only [lo₀,List.length_map] using b.isLt⟩
    have hGet : lo₀.get b=(Subtype.val : U₀ → Y) ⁻¹' (old.eraseIdx j.val).get b₀ := by
      simp [lo₀,b₀,List.get_eq_getElem]
    obtain ⟨h,hlt,hneJ,hOldGet⟩ := List.mem_eraseIdx_iff_getElem.mp (List.get_mem (old.eraseIdx j.val) b₀)
    let hOrig : Fin E.length := ⟨h,by simpa only [old,List.length_map] using hlt⟩
    have hhj : hOrig ≠ j := by
      intro he
      exact hneJ (congrArg (fun t : Fin E.length => t.val) he)
    refine ⟨hOrig,hhj,?_⟩
    rw [hGet,←hOldGet]
    simp only [labels₀,old,List.getElem_map,List.get_eq_getElem,hOrig]
  have hRowsOther₀ : ∀ h : Fin E.length,h ≠ j → h ≠ i → ∃ b : Fin lo₀.length,
      lo₀.get b=labels₀ h ∧ ∀ y ∈ L₀,(oldMonomialPart (X := CMfd.of (n := n) U₀) L₀ lo₀ born₀ b).mem y 1 := by
    intro h hhj hhi
    obtain ⟨b,hb,hRow⟩ := hLRows h hhj
    rw [if_neg hhi] at hRow
    exact ⟨b,hb,hRow.1⟩
  have hOther₀ := other_rows_unit_of_original_labels (X := CMfd.of (n := n) U₀)
    labels₀ i j a₀ ha₀ hOldLower₀ hxOld₀ hCover₀ hRowsOther₀
  let a₁ : Fin lo₁.length := ⟨a₀.val,by simpa only [lo₁,lo₀,List.length_map] using a₀.isLt⟩
  have hGeta : lo₁.get a₁=(Subtype.val : U₁ → U₀) ⁻¹' lo₀.get a₀ := by simp [lo₁,a₁,List.get_eq_getElem]
  have hD₁ : oldMonomialPart (X := CMfd.of (n := n) U₁) L₁ lo₁ born₁ a₁=
      GermIdeal.pullback (m := n) (Subtype.val : U₁ → U₀) (oldMonomialPart (X := CMfd.of (n := n) U₀) L₀ lo₀ born₀ a₀) := by
    change monomialPartAlong n L₁ (restrictOn n L₁ (vanishingIdeal (n := n) (lo₁.get a₁))) born₁=_
    rw [hGeta]
    exact (HironakaG4PreparedMixedSelectedStep.open_parts_pullback_native (X := CMfd.of (n := n) U₀) hn hLN hLE hLT hLD U₁ a₀).1
  obtain ⟨_hcI₀,_hnzI₀,_hcJ₀,_hnzJ₀,hcD₀,_hnzD₀,_hmD₀,_hw₀⟩ :=
    actual_old_parts_geometry (X := CMfd.of (n := n) U₀) hn hLN hLE hLT hLD a₀
  have hD₁not : ¬(oldMonomialPart (X := CMfd.of (n := n) U₁) L₁ lo₁ born₁ a₁).mem x₁ 1 := by
    rw [hD₁]
    exact nonunit_pullback (X := CMfd.of (n := n) U₀) (Z := CMfd.of (n := n) U₁) hcD₀ contMDiff_subtype_val hD₀not
  have hxL₁ : x₁ ∈ L₁ := hxjA
  have hOther₁ := other_units_open (X := CMfd.of (n := n) U₀) hn hLN hLE hLT hLD a₀ hOther₀ U₁
  change ∀ y ∈ L₁,∀ b : Fin lo₁.length,b ≠ a₁ →
    (oldMonomialPart (X := CMfd.of (n := n) U₁) L₁ lo₁ born₁ b).mem y 1 at hOther₁
  have ha₁ : lo₁.get a₁=old₁.get i₁ := by
    rw [hGeta,ha₀]
    simp [old₁,old₀,old,i₁,List.get_eq_getElem]
  have hRetained₁ : ∃ a : Fin (old₁.eraseIdx j₁.val).length,
      (old₁.eraseIdx j₁.val).get a=old₁.get i₁ ∧
      ¬(oldMonomialPart (X := CMfd.of (n := n) U₁) L₁ (old₁.eraseIdx j₁.val) born₁ a).mem x₁ 1 ∧
      (∀ y ∈ L₁,∀ b : Fin (old₁.eraseIdx j₁.val).length,b ≠ a →
        (oldMonomialPart (X := CMfd.of (n := n) U₁) L₁ (old₁.eraseIdx j₁.val) born₁ b).mem y 1) := by
    rw [←hLo₁]
    exact ⟨a₁,ha₁,hD₁not,hOther₁⟩
  obtain ⟨a,ha,hNot,hOther⟩ := hRetained₁
  rw [hLo₁] at hLE₁ hLD₁ hLowerOpen
  let Phase₁ : MarkedIdeal n U₁ := ⟨L₁,born₁,
    oldMonomialPart (X := CMfd.of (n := n) U₁) L₁ (old₁.eraseIdx j₁.val) born₁ a,1⟩
  obtain ⟨_hcI₁,_hnzI₁,_hcJ₁,_hnzJ₁,hcD₁,hnzD₁,hmD₁,_hWhole₁⟩ :=
    actual_old_parts_geometry (X := CMfd.of (n := n) U₁) hn hLN₁ hLE₁ hLT₁ hLD₁ a
  have hPhase₁ : Phase₁.IsWellFormed := ⟨hLN₁,hcD₁,
    isSNCDivisor_of_sublist hLE₁ (List.sublist_append_right _ born₁),hLT₁⟩
  have hxZero₁ : x₁ ∈ Phase₁.ideal.zeroLocus := by
    intro g hg
    by_contra hneG
    exact hNot (CompanionReduction.one_mem_of_apply_ne_zero hcD₁ hg hneG)
  have hxCos₁ : x₁ ∈ Phase₁.cosupp := by
    change x₁ ∈ cosupport n L₁ Phase₁.ideal 1
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcD₁ hg)]
    exact ⟨hxL₁,hxZero₁⟩
  obtain ⟨U₂,hx₂,_hAllowed,v,hValue,hFirst,hdU,hMU,hNZ,hMono,hxCosU,hGammaU,hBoundU,_hPrefixes⟩ :=
    exists_open_all_canonical_markOne_prefix_maxima (X := CMfd.of (n := n) U₁)
      hn Phase₁ hPhase₁ hnzD₁ hmD₁ rfl hxCos₁ ⊤ (by trivial)
  let N₂ := (Subtype.val : U₂ → U₁) ⁻¹' N₁
  let old₂ := old₁.map ((Subtype.val : U₂ → U₁) ⁻¹' ·)
  let born₂ := born₁.map ((Subtype.val : U₂ → U₁) ⁻¹' ·)
  let L₂ := (Subtype.val : U₂ → U₁) ⁻¹' L₁
  let Si₂ := (Subtype.val : U₂ → U₁) ⁻¹' Si₁
  let H₂ := (Subtype.val : U₂ → U₁) ⁻¹' H₁
  let lo₂ := (old₁.eraseIdx j₁.val).map ((Subtype.val : U₂ → U₁) ⁻¹' ·)
  let a₂ : Fin lo₂.length := ⟨a.val,by simpa only [lo₂,List.length_map] using a.isLt⟩
  let i₂ : Fin old₂.length := ⟨i.val,by simpa only [old₂,old₁,old₀,old,List.length_map] using i.isLt⟩
  let j₂ : Fin old₂.length := ⟨j.val,by simpa only [old₂,old₁,old₀,old,List.length_map] using j.isLt⟩
  let MU := MarkedIdeal.pullback (Subtype.val : U₂ → U₁) Phase₁
  let x₂ : U₂ := ⟨x₁,hx₂⟩
  have hne₂ : j₂ ≠ i₂ := by
    intro he
    have hv : j₂.val=i₂.val := congrArg (fun t : Fin old₂.length => t.val) he
    exact hne (Fin.ext hv)
  have hLo₂ : lo₂=old₂.eraseIdx j₂.val := by simp only [lo₂,old₂,List.eraseIdx_map,j₁,j₂]
  have hGeta₂ : lo₂.get a₂=(Subtype.val : U₂ → U₁) ⁻¹' (old₁.eraseIdx j₁.val).get a := by
    simp [lo₂,a₂,List.get_eq_getElem]
  have hGeti₂ : old₂.get i₂=(Subtype.val : U₂ → U₁) ⁻¹' old₁.get i₁ := by
    simp [old₂,i₂,i₁,List.get_eq_getElem]
  have hGetj₂ : old₂.get j₂=(Subtype.val : U₂ → U₁) ⁻¹' old₁.get j₁ := by
    simp [old₂,j₂,j₁,List.get_eq_getElem]
  have ha₂ : lo₂.get a₂=old₂.get i₂ := by rw [hGeta₂,ha,hGeti₂]
  have hD₂ : oldMonomialPart (X := CMfd.of (n := n) U₂) L₂ lo₂ born₂ a₂=MU.ideal := by
    change monomialPartAlong n L₂ (restrictOn n L₂ (vanishingIdeal (n := n) (lo₂.get a₂))) born₂=
      GermIdeal.pullback (m := n) (Subtype.val : U₂ → U₁)
        (oldMonomialPart (X := CMfd.of (n := n) U₁) L₁ (old₁.eraseIdx j₁.val) born₁ a)
    rw [hGeta₂]
    exact (HironakaG4PreparedMixedSelectedStep.open_parts_pullback_native
      (X := CMfd.of (n := n) U₁) hn hLN₁ hLE₁ hLT₁ hLD₁ U₂ a).1
  have hMUModel : MU=(⟨L₂,born₂,oldMonomialPart (X := CMfd.of (n := n) U₂) L₂ lo₂ born₂ a₂,1⟩ : MarkedIdeal n U₂) :=
    congrArg (fun I : GermIdeal n U₂ => (⟨L₂,born₂,I,1⟩ : MarkedIdeal n U₂)) hD₂.symm
  have hOther₂ := other_units_open (X := CMfd.of (n := n) U₁) hn hLN₁ hLE₁ hLT₁ hLD₁ a hOther U₂
  change ∀ y ∈ L₂,∀ b : Fin lo₂.length,b ≠ a₂ →
    (oldMonomialPart (X := CMfd.of (n := n) U₂) L₂ lo₂ born₂ b).mem y 1 at hOther₂
  have hRetained₂ : ∃ a : Fin (old₂.eraseIdx j₂.val).length,
      (old₂.eraseIdx j₂.val).get a=old₂.get i₂ ∧
      MU=(⟨L₂,born₂,oldMonomialPart (X := CMfd.of (n := n) U₂) L₂ (old₂.eraseIdx j₂.val) born₂ a,1⟩ : MarkedIdeal n U₂) ∧
      (∀ y ∈ L₂,∀ b : Fin (old₂.eraseIdx j₂.val).length,b ≠ a →
        (oldMonomialPart (X := CMfd.of (n := n) U₂) L₂ (old₂.eraseIdx j₂.val) born₂ b).mem y 1) := by
    rw [←hLo₂]
    exact ⟨a₂,ha₂,hMUModel,hOther₂⟩
  obtain ⟨aFinal,haFinal,hPhaseModel,hOtherFinal⟩ := hRetained₂
  let Phase : MarkedIdeal n U₂ := ⟨L₂,born₂,
    oldMonomialPart (X := CMfd.of (n := n) U₂) L₂ (old₂.eraseIdx j₂.val) born₂ aFinal,1⟩
  change MU=Phase at hPhaseModel
  have hN₂ : IsClosedSubmanifold n N₂ := isClosedSubmanifold_preimage_val hN₁ U₂
  have hFull₂ : IsSNCDivisor n (old₂ ++ born₂) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val U₂) continuous_subtype_val hFull₁
  have hTr₂ : IsTransverse n N₂ born₂ := isTransverse_preimage (pullsBackCoordinates_val U₂) hTr₁
  have hDense₂ : N₂ ⊆ closure (N₂ \ ⋃ K ∈ old₂ ++ born₂,K) := by
    simpa only [List.map_append] using open_full_density (X := CMfd.of (n := n) U₁) hDense₁ U₂
  have hLN₂ : IsClosedSubmanifold n L₂ := isClosedSubmanifold_preimage_val hLN₁ U₂
  have hLE₂ : IsSNCDivisor n (lo₂ ++ born₂) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val U₂) continuous_subtype_val hLE₁
  have hLT₂ : IsTransverse n L₂ born₂ := isTransverse_preimage (pullsBackCoordinates_val U₂) hLT₁
  have hLD₂ : L₂ ⊆ closure (L₂ \ ⋃ K ∈ lo₂ ++ born₂,K) := by
    simpa only [List.map_append] using open_full_density (X := CMfd.of (n := n) U₁) hLD₁ U₂
  have hPrepared₂ := current_prepared_open (X := CMfd.of (n := n) U₁) hn hLN₁ hLE₁ hLT₁ hLD₁
    hLowerOpen.1 hLowerOpen.2 U₂
  change (∀ y ∈ L₂,∀ b,ordinaryTraceOrder L₂
    (oldResidualPart (X := CMfd.of (n := n) U₂) L₂ lo₂ born₂ b) y ≤ 1) ∧
    (∀ y ∈ L₂,IsPreparedResidualSNCAt (X := CMfd.of (n := n) U₂) L₂ lo₂ born₂ y) at hPrepared₂
  rw [hLo₂] at hLE₂ hLD₂ hPrepared₂
  have hFpull₂ : (old₁.eraseIdx i.val ++ born₁).map ((Subtype.val : U₂ → U₁) ⁻¹' ·)=
      old₂.eraseIdx i.val ++ born₂ := by rw [List.map_append,←List.eraseIdx_map]
  have hAux₂ : IsSNCDivisor n (H₂ :: (old₂.eraseIdx i₂.val ++ born₂)) := by
    simpa only [List.map_cons,hFpull₂] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val U₂) continuous_subtype_val hAux₁
  have hAuxTr₂ : IsTransverse n N₂ (H₂ :: (old₂.eraseIdx i₂.val ++ born₂)) := by
    simpa only [List.map_cons,hFpull₂] using isTransverse_preimage (pullsBackCoordinates_val U₂) hAuxTr₁
  have hLTrace₂ : L₂=N₂ ∩ old₂.get j₂ := by
    rw [hGetj₂]
    change (Subtype.val : U₂ → U₁) ⁻¹' L₁=(Subtype.val : U₂ → U₁) ⁻¹' (N₁ ∩ old₁.get j₁)
    rw [hSjTrace₁]
  have hSi₂ : Si₂=N₂ ∩ H₂ := by
    change (Subtype.val : U₂ → U₁) ⁻¹' Si₁=(Subtype.val : U₂ → U₁) ⁻¹' (N₁ ∩ H₁)
    rw [hSi₁]
  have hBound : ∀ y ∈ Phase.cosupp,gammaAlong n Phase.N Phase.ideal Phase.E Phase.d y ≤ (v : WithBot MonomialInvariant.Val) := by
    rw [←hPhaseModel]
    exact hBoundU
  have hxCos : x₂ ∈ Phase.cosupp := by rw [←hPhaseModel];exact hxCosU
  have hInitialValue : gammaAlong n Phase.N Phase.ideal Phase.E Phase.d x₂=(v : WithBot MonomialInvariant.Val) := by
    rw [←hPhaseModel]
    exact (hGammaU x₂).trans hValue
  obtain ⟨Z,R,hCan,hRes⟩ := exists_markOne_native_resolution_of_bound
    (X := CMfd.of (n := n) U₂) hn MU hMU hNZ hMono hdU v hFirst hBoundU
  have hCanFinal : IsCanonicalSegment Phase (fun {Q} R => towerInvAlong Phase (Y := Q) R) R := by
    rw [←hPhaseModel]
    exact hCan
  have hResFinal : IsGeoResolution Phase R := by rw [←hPhaseModel];exact hRes
  have hPrefixes : ∀ k : ℕ,
      protectedGammaPrefixData (X := CMfd.of (n := n) U₂) N₂ H₂ L₂ old₂ born₂ i₂ j₂ (BlowupTowerSplit.head R k) ∧
      canonicalLowerGammaPrefixData (X := CMfd.of (n := n) U₂) L₂ (old₂.eraseIdx j₂.val) born₂ aFinal
        (BlowupTowerSplit.head R k) := by
    intro k
    exact actual_prepared_singleton_gamma_prefix_protection (X := CMfd.of (n := n) U₂)
      hn hN₂ hFull₂ hTr₂ hDense₂ i₂ j₂ hne₂ hAux₂ hAuxTr₂ hLTrace₂ hLN₂ hLT₂ hLD₂
      hPrepared₂.1 hPrepared₂.2 aFinal haFinal hOtherFinal v hFirst hBound
      (BlowupTowerSplit.head R k) (segment_head (X := CMfd.of (n := n) U₂) Phase R hCanFinal k)
  let M₀ := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
  let M := MarkedIdeal.pullback (Subtype.val : U₂ → U₁)
    (MarkedIdeal.pullback (Subtype.val : U₁ → U₀) (MarkedIdeal.pullback (Subtype.val : U₀ → Y) M₀))
  have hMN : M.N=(Subtype.val : U₂ → U₁) ⁻¹' N₁ := by
    change (Subtype.val : U₂ → U₁) ⁻¹' ((Subtype.val : U₁ → U₀) ⁻¹' ((Subtype.val : U₀ → Y) ⁻¹' M₀.N))=_
    rw [hNi]
  have hME : M.E=born₁.map ((Subtype.val : U₂ → U₁) ⁻¹' ·) := by
    have hEi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).2
    change M₀.E=born at hEi
    change ((M₀.E.map ((Subtype.val : U₀ → Y) ⁻¹' ·)).map ((Subtype.val : U₁ → U₀) ⁻¹' ·)).map
      ((Subtype.val : U₂ → U₁) ⁻¹' ·)=_
    rw [hEi]
  have hMD : M.d=0 := chronologicalMarked_zero_mark (originalRelativeMemberMarked W (E.get i)) rfl T
  have hSi₀ : IsClosedSubmanifold n ((Subtype.val : U₀ → Y) ⁻¹' Si) := isClosedSubmanifold_preimage_val hSi U₀
  have hSi₁smooth : IsClosedSubmanifold n Si₁ := isClosedSubmanifold_preimage_val hSi₀ U₁
  have hMI : M.ideal=vanishingIdeal (n := n) ((Subtype.val : U₂ → U₁) ⁻¹' Si₁) := by
    change GermIdeal.pullback (m := n) (Subtype.val : U₂ → U₁)
      (GermIdeal.pullback (m := n) (Subtype.val : U₁ → U₀)
        (GermIdeal.pullback (m := n) (Subtype.val : U₀ → Y) (J i)))=_
    rw [hWholeSi,actual_vanishingIdeal_open Si hSi U₀,
      actual_vanishingIdeal_open (X := CMfd.of (n := n) U₀) _ hSi₀ U₁,
      actual_vanishingIdeal_open (X := CMfd.of (n := n) U₁) _ hSi₁smooth U₂]
  have hMSource : M=(⟨N₂,born₂,vanishingIdeal (n := n) (N₂ ∩ H₂),0⟩ : MarkedIdeal n U₂) := by
    change (⟨M.N,M.E,M.ideal,M.d⟩ : MarkedIdeal n U₂)=_
    rw [hMN,hME,hMD,hMI]
    change (⟨N₂,born₂,vanishingIdeal (n := n) Si₂,0⟩ : MarkedIdeal n U₂)=_
    rw [hSi₂]
  refine ⟨U₀,U₁,U₂,?_⟩
  dsimp only
  exact ⟨H₂,aFinal,haFinal,hSi₂,hMSource,v,hFirst,hBound,x₂,rfl,hxCos,hInitialValue,Z,R,hCanFinal,hResFinal,hPrefixes⟩

end
end Hironaka.HironakaActualOriginalProtectedGammaFinitePhase
