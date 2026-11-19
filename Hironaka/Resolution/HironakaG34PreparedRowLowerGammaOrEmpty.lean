import Hironaka.Resolution.HironakaActualOriginalProtectedGammaFinitePhase
import Hironaka.Resolution.HironakaProcessedWindowSharpBadOldContainment
import Hironaka.Invariant.RestrictEmptyTower

/-! # Protection near a prepared row: protected Gamma phase or literal empty phase

Lane G34 (run 0079).  Blueprint: `hironaka-g34-resume-prepared-row-gamma-or-empty.tex`.

Let row `i` of an actual original mixed prefix be prepared (order `≤ 1`, normal crossings of its
support `S_i` with `F_i`, density off `F_i`) and let `j ≠ i`.  The LOWER sharp problem of row `j`
lives on `S_j` with the literal boundary `old.eraseIdx j ++ born`, and its original sharp bad locus
is `B_j = originalSharpBadLocus S_j (old.eraseIdx j ++ born)`.

* `actual_prepared_row_lower_bad_disjoint_of_unit`: at a point `x ∈ S_i ∩ S_j` where the actual
  monomial part `D_i` of row `i` is a unit, a whole neighbourhood of `x` misses `B_j`.
* `actual_prepared_row_lower_disjoint_of_not_mem`: at a point of `S_i` off `S_j`, a whole
  neighbourhood misses `S_j`, hence `B_j`.
* `actual_prepared_row_lower_gamma_or_empty` (the local protection dichotomy): at EVERY point of
  `S_i`, either a neighbourhood misses `B_j` and EVERY tower with centres over `B_j` restricts to a
  literal empty tower there, or `x ∈ S_j`, `D_i` is not a unit at `x` and the held protected native
  Gamma phase (`exists_actual_original_local_protected_gamma_phase`) exists at `x`.

No lower sharp driver, carrier-preparation history or global K1 theorem is constructed or assumed. -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG34PreparedRowLowerGammaOrEmpty
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
  RestrictEmptyTower
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

/-- **Empty alternative.** At a point of `S_i ∩ S_j` (row `i` prepared, `j ≠ i`) where the actual
monomial part `D_i` of row `i` is a unit, a whole neighbourhood misses the lower sharp bad locus
`B_j` of row `j`. -/
theorem actual_prepared_row_lower_bad_disjoint_of_unit
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
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
    (hUnit : let A := geoTransformAlong (geometricTemplate W []) T
      (monomialPartAlong n A.N
        (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E).mem x 1) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let Sj := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
    let Bj := originalSharpBadLocus (n := n) Sj (old.eraseIdx j.val ++ A.E)
    ∃ U : Opens Y, x ∈ U ∧ Disjoint (U : Set Y) Bj := by
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
  have hEv : ∀ᶠ y in 𝓝 x, Di.mem y 1 := HomogenizedGlueing.eventually_mem hDiC hUnit
  obtain ⟨V,hVsub,hVo,hxV⟩ := mem_nhds_iff.mp hEv
  have hGood : ∀ y ∈ U, y ∈ V → y ∉ Bj := by
    intro y hyU hyV hyBad
    let yU : U := ⟨y,hyU⟩
    have hOneD : Di.mem y 1 := hVsub hyV
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
  refine ⟨U ⊓ ⟨V,hVo⟩,⟨hxU,hxV⟩,?_⟩
  refine Set.disjoint_left.mpr fun y hy hyBad => ?_
  exact hGood y hy.1 hy.2 hyBad

/-- **Off the lower support.** A point of `S_i` off `S_j` has a neighbourhood missing `S_j`, hence the
lower sharp bad locus `B_j ⊆ S_j`. -/
theorem actual_prepared_row_lower_disjoint_of_not_mem
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (j : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T) {x : Y}
    (hxj : x ∉ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let Sj := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
    let Bj := originalSharpBadLocus (n := n) Sj (old.eraseIdx j.val ++ A.E)
    ∃ U : Opens Y, x ∈ U ∧ Disjoint (U : Set Y) Sj ∧ Disjoint (U : Set Y) Bj := by
  obtain ⟨hNj,_hEj,_hdj,hwj,_hnzj,_hprj⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense j T hT
  let Mj := chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T
  have hClosed : IsClosed (Mj.N ∩ Mj.ideal.zeroLocus) :=
    hwj.isClosedSubmanifold_N.1.inter (OrderTaylor.isClosed_zeroLocus_of_isCoherent hwj.isCoherent)
  have hSj : (geoTransformAlong (geometricTemplate W []) T).N ∩ Mj.ideal.zeroLocus =
      Mj.N ∩ Mj.ideal.zeroLocus := by
    rw [hNj]
  refine ⟨⟨(Mj.N ∩ Mj.ideal.zeroLocus)ᶜ,hClosed.isOpen_compl⟩,hxj,?_,?_⟩
  · change Disjoint (Mj.N ∩ Mj.ideal.zeroLocus)ᶜ
      ((geoTransformAlong (geometricTemplate W []) T).N ∩ Mj.ideal.zeroLocus)
    rw [hSj]
    exact disjoint_compl_left
  · change Disjoint (Mj.N ∩ Mj.ideal.zeroLocus)ᶜ (originalSharpBadLocus (n := n)
      ((geoTransformAlong (geometricTemplate W []) T).N ∩ Mj.ideal.zeroLocus) _)
    rw [hSj]
    exact disjoint_compl_left.mono_right fun y hy => hy.1

/-- **Local protection dichotomy near a prepared row.** Row `i` prepared, `j ≠ i`: at EVERY point
`x ∈ S_i`, either a neighbourhood `U` of `x` misses the lower sharp bad locus `B_j` and every tower
whose centres lie over `B_j` restricts to a literal empty tower on `U`, or `x ∈ S_j` and the actual
monomial part `D_i` is not a unit at `x` -- exactly the hypotheses `hxj`, `hNonunit` of the held
protected Gamma phase `exists_actual_original_local_protected_gamma_phase`. -/
theorem actual_prepared_row_lower_gamma_or_empty
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
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let Sj := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
    let Bj := originalSharpBadLocus (n := n) Sj (old.eraseIdx j.val ++ A.E)
    (∃ U : Opens Y, x ∈ U ∧ Disjoint (U : Set Y) Bj ∧
      ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q), CentresOver Bj R → IsEmptyTower (restrict U R)) ∨
    (x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus ∧
      ¬(monomialPartAlong n A.N
        (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E).mem x 1) := by
  intro A old Sj Bj
  have hEmpty : ∀ U : Opens Y, x ∈ U → Disjoint (U : Set Y) Bj →
      (∃ U : Opens Y, x ∈ U ∧ Disjoint (U : Set Y) Bj ∧
        ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q), CentresOver Bj R → IsEmptyTower (restrict U R)) :=
    fun U hxU hUB => ⟨U,hxU,hUB,fun R hR => isEmptyTower_restrict_of_centresOver U hUB R hR⟩
  by_cases hxj : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
  · by_cases hU : (monomialPartAlong n A.N
        (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E).mem x 1
    · obtain ⟨U,hxU,hUB⟩ := actual_prepared_row_lower_bad_disjoint_of_unit hn hW hE hdense i T hT
        hFull hOrd hNC hDenseS j hne hxi hxj hU
      exact Or.inl (hEmpty U hxU hUB)
    · exact Or.inr ⟨hxj,hU⟩
  · obtain ⟨U,hxU,_hUS,hUB⟩ := actual_prepared_row_lower_disjoint_of_not_mem hn hW hE hdense j T hT hxj
    exact Or.inl (hEmpty U hxU hUB)

end
end Hironaka.HironakaG34PreparedRowLowerGammaOrEmpty
