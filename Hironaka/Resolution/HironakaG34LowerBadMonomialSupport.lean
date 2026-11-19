import Hironaka.Resolution.HironakaG34PreparedRowLowerGammaOrEmpty
import Hironaka.Resolution.HironakaG4ActiveMonomialSharpBad

/-! # Near a prepared row, the lower sharp bad locus is the zero set of its monomial part

Lane G34 (run 0080, round 2).  Blueprint: `hironaka-g34-resume-lower-bad-monomial-support.tex`.
First piece of obligation O2 of `G4K1B-CONTROL-FLOW.md` (see `O2-ROUTE.md` in the lane folder).

Let row `i` of an actual original mixed prefix be prepared and `j ≠ i`.  The lower sharp problem of
row `j` lives on `S_j` with boundary `F_j = old.eraseIdx j ++ born`; its bad locus is
`B_j = originalSharpBadLocus S_j F_j`.  Let `D_i` be the actual monomial part (along `born`) of the
trace of the old member `H_i` on the carrier.

* `actual_prepared_row_lower_bad_eq_monomial_support`: every point `x ∈ S_i ∩ S_j` has an open
  neighbourhood `U` on which `B_j` is EXACTLY the set of points of `S_j` where `D_i` is not a unit.
  (`⊆`: where `D_i` is a unit, all lower monomial parts are units and the lower rows are prepared,
  so `S_j` has normal crossings with `F_j`; `⊇`: normal crossings force every old monomial part on
  `S_j` to be a unit, and the lower monomial part of `H_i` on `S_j` is the restriction of `D_i`.)

At a Gamma point (`D_i` not a unit at `x`) this identifies the restricted lower bad locus with the
cosupport of the mark-one monomial phase of the held protected Gamma phase; at the other points it
re-proves the empty alternative.  No lower driver is constructed or assumed. -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG34LowerBadMonomialSupport
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
  HironakaMarkOneNoncompactNativePhase HironakaActualOriginalProtectedGammaFinitePhase
  RestrictEmptyTower HironakaG4ActiveMonomialSharpBad
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Private copy of the accepted all-units normal-crossings step
(`HironakaProcessedWindowSharpBadOldContainment`, private there). -/
private theorem prepared_all_units_nc {N : Set Y} {old born : List (Set Y)}
    (hn : 0<n) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old++born)) (hTr : IsTransverse n N born)
    (hdense : N⊆closure (N \ ⋃H∈old++born,H)) {x : Y} (hx : x∈N)
    (hOrd : ∀a,ordinaryTraceOrder N (oldResidualPart N old born a) x≤1)
    (hPrep : IsPreparedResidualSNCAt N old born x)
    (hUnit : ∀a,(oldMonomialPart N old born a).mem x 1) :
    normalCrossingsAt (n:=n) N (old++born) x := by
  have h := normalCrossingsAt_prepared_selected_born_intersection hn hN hE hTr hdense
    (∅ : Finset (Fin born.length)) (by simpa [BoundaryCount.memberInter] using hx)
    hOrd hPrep (List.Sublist.refl _) (fun H hH => ?_) (fun _ h => List.mem_append_right _ h)
  · simpa [BoundaryCount.memberInter] using h
  · rcases List.mem_append.mp hH with hOld | hBorn
    · obtain ⟨a,rfl⟩ := List.mem_iff_get.mp hOld
      exact Or.inr ⟨a,rfl,hUnit a⟩
    · exact Or.inl hBorn

/-- Private copy (`HironakaProcessedWindowSharpBadOldContainment`). -/
private theorem pullback_one_mem {U : Opens Y} {I : GermIdeal n Y} {x : U}
    (h : I.mem x.val (1 : Y→ℂ)) :
    (GermIdeal.pullback (m:=n) (Subtype.val : U→Y) I).mem x (1 : U→ℂ) := by
  apply GermIdeal.mem_pullback_iff.mpr
  exact InvertibleIdealQuotient.isInSpanAt_self ⟨1,h,rfl⟩ (holomorphicAt_const 1)

/-- Private copy (`HironakaActualOriginalProtectedGammaFinitePhase`, private there). -/
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

/-- Private copy (`HironakaActualRetainedBoundaryMaskBlock`, private there). -/
private theorem old_factor_unit_at_full_nc (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born))
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    {x : X} (hx : x ∈ N) (hNC : normalCrossingsAt (n := n) N (old ++ born) x)
    (i : Fin old.length) :
    (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) (old.get i))) born).mem x 1 := by
  let k : Fin (old ++ born).length := ⟨i.val,by simp only [List.length_append]; omega⟩
  let L : List (Fin (old ++ born).length) := List.ofFn fun j : Fin born.length =>
    ⟨old.length+j.val,by simp only [List.length_append]; omega⟩
  have hOld : (old ++ born).get k=old.get i := by
    simp only [k,List.get_eq_getElem,List.getElem_append_left i.isLt]
  have hBorn : L.map (old ++ born).get=born := by
    calc
      L.map (old ++ born).get=List.ofFn (fun j : Fin born.length => born.get j) := by
        dsimp only [L]
        rw [List.map_ofFn]
        congr 1
        funext j
        simp only [Function.comp_apply,List.get_eq_getElem]
        rw [List.getElem_append_right (Nat.le_add_right old.length j.val)]
        simp only [Nat.add_sub_cancel_left]
      _=born := List.ofFn_get born
  have hL : ∀ j ∈ L,k ≠ j := by
    intro j hj
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hj
    intro h
    have hval := congrArg Fin.val h
    change i.val=old.length+a.val at hval
    omega
  simpa only [hOld,hBorn] using
    one_mem_old_monomialPartAlong_at_normalCrossings hn hN hE hdense hx hNC k L hL

/-- **Near a prepared row the lower sharp bad locus is the zero set of the monomial part.** -/
theorem actual_prepared_row_lower_bad_eq_monomial_support
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    (j : Fin E.length) (hne : j ≠ i) {x : Y}
    (hxi : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)
    (hxj : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let Sj := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
    let Bj := originalSharpBadLocus (n := n) Sj (old.eraseIdx j.val ++ A.E)
    let Di := monomialPartAlong n A.N
      (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E
    ∃ U : Opens Y,x ∈ U ∧ ∀ y ∈ U,(y ∈ Bj ↔ y ∈ Sj ∧ ¬Di.mem y 1) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let J := fun a : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
  let L := A.N ∩ (J j).zeroLocus
  let Bj := originalSharpBadLocus (n := n) L (old.eraseIdx j.val ++ A.E)
  let I := restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))
  let Di := monomialPartAlong n A.N I A.E
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  obtain ⟨U,hxU,hLc,hEc,hTc,hDc,hRows,hPrep⟩ :=
    actual_original_lower_prepared_neighborhood hn hW hE hdense i T hT hFull hOrd hNC hDenseS j hne hxi hxj
  let LU : Set U := (Subtype.val : U → Y) ⁻¹' L
  let oldU := (old.eraseIdx j.val).map ((Subtype.val : U → Y) ⁻¹' ·)
  let bornU := A.E.map ((Subtype.val : U → Y) ⁻¹' ·)
  have hDiC : Di.IsCoherent := by
    let oi : Fin old.length := ⟨i.val,by simp [old]⟩
    have hGet : old.get oi = strictAlong T (E.get i) := by simp [old,oi]
    have h := (actual_old_parts_geometry hn hRecorded.1 hRecorded.2.1 hRecorded.2.2.1
      hRecorded.2.2.2.1 oi).2.2.2.2.1
    change (monomialPartAlong n A.N (restrictOn n A.N
      (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E).IsCoherent
    rw [←hGet]
    exact h
  obtain ⟨ai,_hai,hRowI⟩ := hRows i (fun h => hne h.symm)
  rw [if_pos rfl] at hRowI
  refine ⟨U,hxU,fun y hyU => ⟨fun hyBad => ⟨hyBad.1,fun hOneD => ?_⟩,fun ⟨hyS,hNon⟩ => ⟨hyS,fun hNCy => ?_⟩⟩⟩
  · -- a unit monomial part gives normal crossings
    let yU : U := ⟨y,hyU⟩
    have hMi : (restrictOn n LU (GermIdeal.pullback (m := n) (Subtype.val : U → Y) Di)).mem yU 1 :=
      le_restrictOn (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hDiC)
        yU 1 (pullback_one_mem hOneD)
    have hAll : ∀ a : Fin oldU.length,
        (oldMonomialPart (X := CMfd.of (n := n) U) LU oldU bornU a).mem yU 1 := by
      intro a
      obtain ⟨H,hH,hHa⟩ := List.mem_map.mp (List.get_mem oldU a)
      obtain ⟨v,hv,hvj,hvH⟩ := List.mem_eraseIdx_iff_getElem.mp hH
      let k : Fin E.length := ⟨v,by simpa only [old,List.length_map] using hv⟩
      have hkj : k ≠ j := fun heq => hvj (congrArg Fin.val heq)
      obtain ⟨b,hb,hbRow⟩ := hRows k hkj
      have hkget : old.get ⟨v,hv⟩ = strictAlong T (E.get k) := by simp [old,k]
      have hab : oldU.get a = oldU.get b := by
        rw [hb,←hHa,←hkget]
        exact congrArg ((Subtype.val : U → Y) ⁻¹' ·) hvH.symm
      have hparts : oldMonomialPart (X := CMfd.of (n := n) U) LU oldU bornU a =
          oldMonomialPart (X := CMfd.of (n := n) U) LU oldU bornU b := by
        simp only [oldMonomialPart,oldTraceIdeal,hab]
      rw [hparts]
      by_cases hki : k = i
      · rw [if_pos hki] at hbRow
        rw [hbRow.1]
        exact hMi
      · rw [if_neg hki] at hbRow
        exact hbRow.1 yU hyBad.1
    have hNCU := prepared_all_units_nc hn hLc hEc hTc hDc
      (show yU ∈ LU from hyBad.1) (hPrep yU hyBad.1).1 (hPrep yU hyBad.1).2 hAll
    have hNCY : normalCrossingsAt (n := n) L (old.eraseIdx j.val ++ A.E) y := by
      apply (HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff
        (C := L) (E := old.eraseIdx j.val ++ A.E) (U := U) (x := yU)).mp
      simpa only [List.map_append] using hNCU
    exact hyBad.2 hNCY
  · -- normal crossings force the lower monomial part of `H_i`, i.e. the restriction of `D_i`, to be a unit
    let yU : U := ⟨y,hyU⟩
    have hyL : yU ∈ LU := hyS
    have hNCU : normalCrossingsAt (n := n) LU (oldU ++ bornU) yU := by
      have h := (HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff
        (C := L) (E := old.eraseIdx j.val ++ A.E) (U := U) (x := yU)).mpr hNCy
      simpa only [List.map_append] using h
    have hUnit := old_factor_unit_at_full_nc (X := CMfd.of (n := n) U) (old := oldU) (born := bornU)
      hn hLc hEc hDc hyL hNCU ai
    have hUnit' : (oldMonomialPart (X := CMfd.of (n := n) U) LU oldU bornU ai).mem yU 1 := hUnit
    rw [hRowI.1] at hUnit'
    exact nonunit_pullback_restrict hDiC contMDiff_subtype_val hyL hNon hUnit'

end
end Hironaka.HironakaG34LowerBadMonomialSupport
