import Hironaka.Resolution.HironakaActualProtectedOtherRowLocalStep
import Hironaka.Resolution.HironakaG4LowerPreparedNeighborhood
import Hironaka.Resolution.HironakaG4LocalLowerTrace
import Hironaka.Resolution.HironakaOriginalNCMarkedStratumNativeFields
import Hironaka.Resolution.HironakaSharpOriginalAllBoundaryCentre

/-!
# The actual processed-window sharp-bad geometry

Pure current geometry supplies the smooth highest-count bad fibre and its
whole auxiliary marked ideal. Native invariant calibration is a separate
consumer. Blueprint-first contract and independent route peer precede source.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpBadProcessedWindowGeometry
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  Hironaka.RegularLocusDense BlowupTowers BlowupTowerTransforms
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance SimultaneousNormalCrossings BlowupFlatCoordinates
  MarkedIdeals MarkedIdeals.MarkedIdeal RelativePrincipalizationSpan
  RestrictedIdealExtension GermIdealOrder HironakaG4PreparedCentreCoordinates
  InvertibleIdealQuotient MonomialPartAlong DivisorExponentAlong GiraudAlong
  HironakaSharpOriginalProductTraceOrder
  HironakaG4RecordedTowerResidualCompatibility
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualTraceIncidence
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsSNCBlockCarrier
  HironakaOriginalNCMarkedStratumHistoryValue HironakaOriginalNCMarkedStratumNativeFields
  HironakaActualProtectedOtherRowLocalStep HironakaG4LowerPreparedNeighborhood
open HironakaSharpNormalCrossingsOpenLocus MarkedIdealRestrictOpen HironakaOriginalNCCountHistory
  HironakaOriginalNCMarkedStratum MarkedIdealBiholomorphism
open HomogenizedGlueingTower (strictAlong)
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem pullback_one_mem {U : Opens Y} {I : GermIdeal n Y} {x : U}
    (h : I.mem x.val (1 : Y→ℂ)) :
    (GermIdeal.pullback (m:=n) (Subtype.val : U→Y) I).mem x (1 : U→ℂ) := by
  apply GermIdeal.mem_pullback_iff.mpr
  exact InvertibleIdealQuotient.isInSpanAt_self ⟨1,h,rfl⟩ (holomorphicAt_const 1)

private theorem actual_upper_monomial_nonunit
    (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃H∈E,H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀x∈(geoTransformAlong (geometricTemplate W []) T).N,
      ∀a : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x≤1)
    (i j : Fin E.length) (hne : j≠i)
    (hNCi : let A:=geoTransformAlong (geometricTemplate W []) T
      let Si:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n Si ((E.map (strictAlong T)).eraseIdx i.val++A.E))
    (hDensei : let A:=geoTransformAlong (geometricTemplate W []) T
      let Si:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      Si⊆closure (Si \ ⋃H∈(E.map (strictAlong T)).eraseIdx i.val++A.E,H))
    {x : Y}
    (hx : let A:=geoTransformAlong (geometricTemplate W []) T
      let L:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
      x∈originalSharpBadLocus (n:=n) L ((E.map (strictAlong T)).eraseIdx j.val++A.E) ∩
        (A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)) :
    let A:=geoTransformAlong (geometricTemplate W []) T
    ¬(monomialPartAlong n A.N
      (restrictOn n A.N (vanishingIdeal (n:=n) (strictAlong T (E.get i)))) A.E).mem x 1 := by
  let A:=geoTransformAlong (geometricTemplate W []) T
  let old:=E.map (strictAlong T)
  let J:=fun a : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
  let L:=A.N∩(J j).zeroLocus
  let Di:=monomialPartAlong n A.N
    (restrictOn n A.N (vanishingIdeal (n:=n) (strictAlong T (E.get i)))) A.E
  have hRecorded:=actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  let oi : Fin old.length:=⟨i.val,by simp [old]⟩
  have hGeti : old.get oi=strictAlong T (E.get i) := by simp [old,oi]
  have hDi : Di.IsCoherent := by
    have h := (actual_old_parts_geometry hn hRecorded.1 hRecorded.2.1 hRecorded.2.2.1
      hRecorded.2.2.2.1 oi).2.2.2.2.1
    change (monomialPartAlong n A.N (restrictOn n A.N
      (vanishingIdeal (n:=n) (strictAlong T (E.get i)))) A.E).IsCoherent
    rw [←hGeti]
    exact h
  have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=A.N at hNi
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N=A.N at hNj
  have hOrdI : ∀y∈(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N (J i) y≤1 := by
    simpa only [hNi] using fun y hy => hOrd y hy i
  obtain ⟨U,hxU,hLc,hEc,hTc,hDc,hRows,hPrep⟩ :=
    actual_original_lower_prepared_neighborhood hn hW hE hdense i T hT hFull hOrdI hNCi hDensei
      j hne (by simpa only [hNi] using hx.2) (by simpa only [hNj] using hx.1.1)
  let xU : U:=⟨x,hxU⟩
  let LU : Set U:=(Subtype.val : U→Y) ⁻¹' L
  let oldU:=(old.eraseIdx j.val).map ((Subtype.val : U→Y) ⁻¹' ·)
  let bornU:=A.E.map ((Subtype.val : U→Y) ⁻¹' ·)
  change ¬Di.mem x 1
  intro hOne
  have hMi : (restrictOn n LU (GermIdeal.pullback (m:=n) (Subtype.val : U→Y) Di)).mem xU 1 :=
    le_restrictOn (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hDi) xU 1 (pullback_one_mem hOne)
  have hAll : ∀a : Fin oldU.length,(oldMonomialPart (X:=CMfd.of (n:=n) U) LU oldU bornU a).mem xU 1 := by
    intro a
    obtain ⟨H,hH,hHa⟩ := List.mem_map.mp (List.get_mem oldU a)
    obtain ⟨v,hv,hvj,hvH⟩ := List.mem_eraseIdx_iff_getElem.mp hH
    let k : Fin E.length:=⟨v,by simpa only [old,List.length_map] using hv⟩
    have hkj : k≠j := fun heq => hvj (congrArg Fin.val heq)
    obtain ⟨b,hb,hbRow⟩ := hRows k hkj
    have hkget : old.get ⟨v,hv⟩=strictAlong T (E.get k) := by simp [old,k]
    have hab : oldU.get a=oldU.get b := by
      rw [hb,←hHa,←hkget]
      exact congrArg ((Subtype.val : U→Y) ⁻¹' ·) hvH.symm
    have hparts : oldMonomialPart (X:=CMfd.of (n:=n) U) LU oldU bornU a=
        oldMonomialPart (X:=CMfd.of (n:=n) U) LU oldU bornU b := by
      simp only [oldMonomialPart,oldTraceIdeal,hab]
    rw [hparts]
    by_cases hki : k=i
    · rw [if_pos hki] at hbRow
      rw [hbRow.1]
      exact hMi
    · rw [if_neg hki] at hbRow
      exact hbRow.1 xU hx.1.1
  have hNC := normalCrossingsAt_of_prepared_all_units hn hLc hEc hTc hDc
    (show xU∈LU from hx.1.1) (hPrep xU hx.1.1).1 (hPrep xU hx.1.1).2 hAll
  have hNC' : normalCrossingsAt (n:=n) L (old.eraseIdx j.val++A.E) x := by
    apply (HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff
      (C:=L) (E:=old.eraseIdx j.val++A.E) (U:=U) (x:=xU)).mp
    simpa only [List.map_append] using hNC
  exact hx.1.2 hNC'

/-- Genuine nearby trace containment forces badness along a distinct retained
boundary member. The finite exponent criterion is used on the smooth carrier;
point order alone would not imply the required divisibility. -/
private theorem bad_near_of_trace_containment
    (hn : 0<n) {L : Set Y} {F : List (Set Y)}
    (hL : IsClosedSubmanifold n L) (hF : IsSNCDivisor n F)
    (hdense : L⊆closure (L \ ⋃D∈F,D))
    (a b : Fin F.length) (hne : a≠b) {x : Y}
    (hcontain : ∀ᶠy in 𝓝 x,y∈L→y∈F.get b→y∈F.get a) :
    ∀ᶠy in 𝓝 x,y∈L→y∈F.get b→y∈originalSharpBadLocus (n:=n) L F := by
  let I:=restrictOn n L (vanishingIdeal (n:=n) (F.get a))
  have hcH:=VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hF a)
  have hparts:=actual_old_parts_geometry hn hL
    (show IsSNCDivisor n (F++[]) by simpa only [List.append_nil] using hF)
    (isTransverse_nil_of_isClosedSubmanifold hL)
    (by simpa only [List.append_nil] using hdense) a
  have hcI : I.IsCoherent:=hparts.1
  have hnz : ∀y∈L,IsNonzeroAlongAt L I y:=hparts.2.1
  have hhol : ∀y g,I.mem y g→HolomorphicAt n g y:=
    fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hcI hg
  have hdiv : IsDivNearAlong n L I (F.get b) 1 x := by
    filter_upwards [hcontain] with y hy hyL hyB
    rw [cosupport_one hhol]
    refine ⟨hyL,?_⟩
    apply (zeroLocus_restrictOn_iff hcH hyL).mpr
    rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (hF.1 _ (List.get_mem F a))]
    exact hy hyL hyB
  filter_upwards [hdiv.eventually_nhds] with y hy hyL hyB
  refine ⟨hyL,?_⟩
  intro hNC
  have heq:=HironakaG4ActiveMonomialSharpBad.divExpAlong_restricted_member_eq_zero_at_normalCrossings
    hn hL hF hdense hyL hNC a b hne hyB
  obtain ⟨k,hk⟩:=hL.2 y hyL
  obtain ⟨r,hr⟩:=exists_isLocalRetraction hk
  have hpos:=(isDivNearAlong_iff_le_divExpAlong hr hyB (hnz y hyL) hhol).mp hy
  change 1≤divExpAlong n L (restrictOn n L (vanishingIdeal (n:=n) (F.get a))) (F.get b) y at hpos
  rw [heq] at hpos
  omega

private theorem near_trace_containment_of_positive_exponent
    {N H B : Set Y} (hH : IsClosed H)
    (hcH : (vanishingIdeal (n:=n) H).IsCoherent)
    (hcI : (restrictOn n N (vanishingIdeal (n:=n) H)).IsCoherent)
    {x : Y} (hpos : 1≤divExpAlong n N
      (restrictOn n N (vanishingIdeal (n:=n) H)) B x) :
    ∀ᶠy in 𝓝 x,y∈N→y∈B→y∈H := by
  let I:=restrictOn n N (vanishingIdeal (n:=n) H)
  have hhol : ∀y g,I.mem y g→HolomorphicAt n g y:=
    fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hcI hg
  have hdiv:=(isDivNearAlong_divExpAlong hhol x).mono hpos
  filter_upwards [hdiv] with y hy hyN hyB
  have hz : y∈I.zeroLocus:=fun g hg=>
    (vanishesToOrderOn_one_iff hyN (hhol y g hg)).mp ((hy hyN hyB).2 g hg)
  have hz':=(zeroLocus_restrictOn_iff hcH hyN).mp hz
  rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hH] at hz'

private theorem old_born_ne_at {old born : List (Set Y)}
    (hE : IsSNCDivisor n (old++born)) (a : Fin old.length) (b : Fin born.length)
    {x : Y} (hxb : x∈born.get b) : old.get a≠born.get b := by
  intro heq
  let i : Fin (old++born).length:=⟨a.val,by simp only [List.length_append]; omega⟩
  let j : Fin (old++born).length:=⟨old.length+b.val,by simp only [List.length_append]; omega⟩
  have hi : (old++born).get i=old.get a := by
    simp only [List.get_eq_getElem,i,List.getElem_append_left a.isLt]
  have hj : (old++born).get j=born.get b := by
    simp only [List.get_eq_getElem,j,List.getElem_append_right (by omega : old.length≤old.length+b.val),
      Nat.add_sub_cancel_left]
  have hij:=eq_of_eventually_mem_iff hE
    (show x∈(old++born).get i from by rw [hi,heq]; exact hxb)
    (show x∈(old++born).get j from by rw [hj]; exact hxb)
    (Eventually.of_forall fun _=>by rw [hi,hj,heq])
  have hv:=congrArg Fin.val hij
  change a.val=old.length+b.val at hv
  omega

/-- A nonunit native born factor produces one incident born divisor.
Its trace on the upper carrier lies in the selected old divisor near
the point. On the lower carrier the same born trace lies in the lower
sharp bad locus. -/
theorem born_bad_germ_of_nonunit (hn : 0 < n) {N L : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hFull : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born, D))
    (hL : IsClosedSubmanifold n L) (hLN : L ⊆ N)
    (i j : Fin old.length) (hne : j ≠ i)
    (hLowerDense : L ⊆ closure (L \ ⋃ D ∈ old.eraseIdx j.val ++ born, D))
    {x : X} (hx : x ∈ N) (hNonunit : ¬ (oldMonomialPart N old born i).mem x 1) :
    ∃ b : Fin born.length, x ∈ born.get b ∧
      1 ≤ divExpAlong n N (oldTraceIdeal N old i) (born.get b) x ∧
      (∀ᶠ y in 𝓝 x, y ∈ N → y ∈ born.get b → y ∈ old.get i) ∧
      (∀ᶠ y in 𝓝 x, y ∈ L → y ∈ born.get b →
        y ∈ originalSharpBadLocus (n := n) L (old.eraseIdx j.val ++ born)) := by
  let I := oldTraceIdeal N old i
  let F := old.eraseIdx j.val ++ born
  have hb : ∃ b : Fin born.length, x ∈ born.get b ∧ divExpAlong n N I (born.get b) x ≠ 0 := by
    by_contra! hZero
    exact hNonunit ((one_mem_monomialPartAlong_iff I born hx).mpr hZero)
  obtain ⟨b,hxb,hbpos⟩ := hb
  have hOld := isSNCDivisor_of_sublist hFull (List.sublist_append_left old born)
  have hOldi := MonomialPart.isClosedSubmanifold_get hn hOld i
  have hcI := (actual_old_parts_geometry hn hN hFull hTr hDense i).1
  have hPos := Nat.one_le_iff_ne_zero.mpr hbpos
  have hcont := near_trace_containment_of_positive_exponent hOldi.1
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hOldi) hcI hPos
  have hF : IsSNCDivisor n F := isSNCDivisor_of_sublist hFull
    ((List.eraseIdx_sublist old j.val).append (List.Sublist.refl born))
  have hiF : old.get i ∈ F := by
    apply List.mem_append_left
    exact List.mem_eraseIdx_iff_getElem.mpr ⟨i.val,i.isLt,fun he => hne (Fin.ext he.symm),rfl⟩
  have hbF : born.get b ∈ F := List.mem_append_right _ (List.get_mem born b)
  obtain ⟨a,ha⟩ := List.mem_iff_get.mp hiF
  obtain ⟨c,hc⟩ := List.mem_iff_get.mp hbF
  have hac : a ≠ c := by
    intro he
    exact old_born_ne_at hFull i b hxb (ha.symm.trans ((congrArg F.get he).trans hc))
  have hcontL : ∀ᶠ y in 𝓝 x, y ∈ L → y ∈ F.get c → y ∈ F.get a := by
    filter_upwards [hcont] with y hy hyL hyc
    rw [ha]
    exact hy (hLN hyL) (hc ▸ hyc)
  have hBad := bad_near_of_trace_containment hn hL hF hLowerDense a c hac hcontL
  refine ⟨b,hxb,hPos,hcont,?_⟩
  simpa only [hc] using hBad

theorem actual_born_bad_germ
    (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃H∈E,H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀x∈(geoTransformAlong (geometricTemplate W []) T).N,
      ∀a : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x≤1)
    (i j : Fin E.length) (hne : j≠i)
    (hNCi : let A:=geoTransformAlong (geometricTemplate W []) T
      let Si:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n Si ((E.map (strictAlong T)).eraseIdx i.val++A.E))
    (hDensei : let A:=geoTransformAlong (geometricTemplate W []) T
      let Si:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      Si⊆closure (Si \ ⋃H∈(E.map (strictAlong T)).eraseIdx i.val++A.E,H))
    (hLowerDense : let A:=geoTransformAlong (geometricTemplate W []) T
      let L:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
      L⊆closure (L \ ⋃D∈(E.map (strictAlong T)).eraseIdx j.val++A.E,D))
    {x : Y}
    (hx : let A:=geoTransformAlong (geometricTemplate W []) T
      let L:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
      x∈originalSharpBadLocus (n:=n) L ((E.map (strictAlong T)).eraseIdx j.val++A.E) ∩
        (A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)) :
    let A:=geoTransformAlong (geometricTemplate W []) T
    let L:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
    let Fj:=(E.map (strictAlong T)).eraseIdx j.val++A.E
    ∃b : Fin A.E.length,x∈A.E.get b ∧
      (∀ᶠy in 𝓝 x,y∈A.N→y∈A.E.get b→y∈strictAlong T (E.get i)) ∧
      (∀ᶠy in 𝓝 x,y∈L→y∈A.E.get b→y∈originalSharpBadLocus (n:=n) L Fj) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let J := fun a : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
  let L := A.N ∩ (J j).zeroLocus
  let oi : Fin old.length := ⟨i.val,by simp [old]⟩
  let oj : Fin old.length := ⟨j.val,by simp [old]⟩
  have hGeti : old.get oi = strictAlong T (E.get i) := by simp [old,oi]
  have hne' : oj ≠ oi := fun he => hne (Fin.ext (congrArg (fun v : Fin old.length => v.val) he))
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hNonunit : ¬ (oldMonomialPart A.N old A.E oi).mem x 1 := by
    simpa only [oldMonomialPart,oldTraceIdeal,hGeti] using
      actual_upper_monomial_nonunit hn hW hE hdense T hT hFull hOrd i j hne hNCi hDensei hx
  have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N = A.N at hNi
  have hOrdJ : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N (J j) y ≤ 1 := by
    simpa only [hNi] using fun y hy => hOrd y hy j
  have hL : IsClosedSubmanifold n L := by
    have hh := (HironakaG4OriginalSelectedResidualTail.actual_original_selected_residual_tail
      hn hW hE hdense j T hT hOrdJ).1
    simpa only [hNi] using hh
  obtain ⟨b,hb,_,hCont,hBad⟩ := born_bad_germ_of_nonunit hn hRecorded.1 hRecorded.2.1
    hRecorded.2.2.1 hRecorded.2.2.2.1 hL (show L ⊆ A.N from inter_subset_left)
    oi oj hne' hLowerDense hx.2.1 hNonunit
  change ∀ᶠ y in 𝓝 x, y ∈ A.N → y ∈ A.E.get b → y ∈ old.get oi at hCont
  rw [hGeti] at hCont
  exact ⟨b,hb,hCont,hBad⟩

/-- An actual finite SNC list has one genuine source window with no new
incident positions. The intrinsic prescribed-carrier count is the TRUE count. -/
private theorem actual_snc_count_window (F : List (Set Y))
    (hF : IsSNCDivisor n F) (x : Y) :
    let H := ⋃ D ∈ F, D
    let q := oldCount H (BlowupTower.refl : BlowupTower Y Y) x
    ∃ U : Opens Y, x ∈ U ∧
      (∀ y ∈ U, oldCount H (BlowupTower.refl : BlowupTower Y Y) y ≤ q) ∧
      ∀ y ∈ U, (q ≤ oldCount H (BlowupTower.refl : BlowupTower Y Y) y ↔
        ∀ a : Fin F.length, x ∈ F.get a → y ∈ F.get a) := by
  let H := ⋃ D ∈ F, D
  let c := fun y : Y => oldCount H (BlowupTower.refl : BlowupTower Y Y) y
  let S := fun y : Y => Finset.univ.filter (fun a : Fin F.length => y ∈ F.get a)
  have hF' : IsSNCDivisor n (F ++ []) := by simpa only [List.append_nil] using hF
  have hc (y : Y) : c y = (S y).card := by
    exact (oldCount_eq BlowupTower.refl
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_snc_append F [] hF')) y).trans
      (branchMultiplicity_union_eq_count F [] hF' y).1
  have hSeen : ∀ᶠ y in 𝓝 x, ∀ a : Fin F.length, y ∈ F.get a → x ∈ F.get a := by
    apply Filter.eventually_all.mpr
    intro a
    by_cases ha : x ∈ F.get a
    · exact Filter.Eventually.of_forall (fun _ _ => ha)
    · exact Filter.Eventually.mono
        ((hF.1 (F.get a) (List.get_mem F a)).isOpen_compl.mem_nhds ha)
        (fun _ hy hyF => False.elim (hy hyF))
  obtain ⟨O, hO, hOo, hxO⟩ := mem_nhds_iff.mp hSeen
  have hSub (y : Y) (hy : y ∈ O) : S y ⊆ S x := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hO hy a (Finset.mem_filter.mp ha).2⟩
  refine ⟨⟨O, hOo⟩, hxO, ?_, ?_⟩
  · intro y hy
    change c y ≤ c x
    rw [hc y, hc x]
    exact Finset.card_le_card (hSub y hy)
  · intro y hy
    change c x ≤ c y ↔ _
    rw [hc x, hc y]
    constructor
    · intro hcard a hxa
      have heq : S y = S x := Finset.eq_of_subset_of_card_le (hSub y hy) hcard
      have ha : a ∈ S y := heq.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxa⟩
      exact (Finset.mem_filter.mp ha).2
    · intro hAll
      apply Finset.card_le_card
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAll a (Finset.mem_filter.mp ha).2⟩


/-- The auxiliary ideal calculation uses geometric containments and the
whole coordinate dictionary; no radical-product generator is assumed. -/
private theorem coordinate_vanishing_sum_eq_at
    {B Q Z : Set Y} {x : Y}
    (hZB : Z ⊆ B) (hZQ : Z ⊆ Q)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (S : Finset (Fin n))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hzero : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (hflat : ∀ {y : Y}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ Z ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace S))
    (hgen : ∀ a ∈ S,
      (vanishingIdeal (n := n) B).mem x (flatCoord Φ a) ∨
      (vanishingIdeal (n := n) Q).mem x (flatCoord Φ a)) :
    ∀ g, (RestrictedIdealExtension.sumIdeal
      (vanishingIdeal (n := n) B) (vanishingIdeal (n := n) Q)).mem x g ↔
      (vanishingIdeal (n := n) Z).mem x g := by
  intro g
  constructor
  · intro hg
    obtain ⟨hgHol, k, t, c, ht, hc, he⟩ := hg
    refine ⟨hgHol, ?_⟩
    have hv (a : Fin k) : ∀ᶠ y in 𝓝 x, y ∈ Z → t a y = 0 := by
      rcases ht a with hB | hQ
      · exact hB.2.mono (fun _ hy hyZ => hy (hZB hyZ))
      · exact hQ.2.mono (fun _ hy hyZ => hy (hZQ hyZ))
    filter_upwards [he, Filter.eventually_all.mpr hv] with y hy hyv hyZ
    rw [hy]
    exact Finset.sum_eq_zero (fun a _ => by rw [hyv a hyZ]; simp)
  · intro hg
    have hspan := (HironakaSmoothSubmersionRelativeRestriction.vanishingIdeal_mem_iff_coordinate_family
      Φ S hsrc hzero hflat g).mp hg
    change IsInSpanAt (n := n) (fun f =>
      (vanishingIdeal (n := n) B).mem x f ∨ (vanishingIdeal (n := n) Q).mem x f) x g
    apply IsInSpanAt.trans ?_ hspan
    intro t ht
    obtain ⟨a, rfl⟩ := ht
    change IsInSpanAt (n := n) (fun f =>
      (vanishingIdeal (n := n) B).mem x f ∨
        (vanishingIdeal (n := n) Q).mem x f) x
      (if a ∈ S then flatCoord Φ a else fun _ => 0)
    by_cases ha : a ∈ S
    · rw [if_pos ha]
      exact InvertibleIdealQuotient.isInSpanAt_self (hgen a ha)
        (holomorphicAt_flatCoord Φ a (mem_flatDomain_self Φ))
    · rw [if_neg ha]
      exact InvertibleIdealQuotient.isInSpanAt_self
        (Or.inl (show (vanishingIdeal (n := n) B).mem x (fun _ => 0) from
          ⟨holomorphicAt_const 0, Filter.Eventually.of_forall (fun _ _ => rfl)⟩))
        (holomorphicAt_const 0)


private theorem member_inter_flat {N : Set Y} {E : List (Set Y)}
    {x : Y} {S₀ : Finset (Fin n)} {T : Fin E.length→Finset (Fin n)}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (hFam : ∀o : Option (Fin E.length), x∈o.elim N E.get→
      ∀y∈flatDomain Φ,y∈o.elim N E.get↔
        Φ.toFun (chartAt (ComplexModel n) x y)∈coordSubspace (o.elim S₀ T))
    (S : Finset (Fin E.length)) (hx : x∈N∩BoundaryCount.memberInter E S) :
    ∀y∈flatDomain Φ,y∈N∩BoundaryCount.memberInter E S↔
      Φ.toFun (chartAt (ComplexModel n) x y)∈coordSubspace (S₀∪S.biUnion T) := by
  intro y hy
  change (y∈N∧∀a∈S,y∈E.get a)↔_
  have hunion (w : ComplexModel n) : w∈coordSubspace (S₀∪S.biUnion T)↔
      w∈coordSubspace S₀∧w∈coordSubspace (S.biUnion T) := by
    simp only [coordSubspace,Finset.mem_union,mem_ofPred_eq]
    exact ⟨fun h=>⟨fun a ha=>h a (Or.inl ha),fun a ha=>h a (Or.inr ha)⟩,
      fun h a ha=>ha.elim (h.1 a) (h.2 a)⟩
  rw [hunion,BoundaryCount.mem_coordSubspace_biUnion]
  exact and_congr (hFam none hx.1 y hy)
    (forall₂_congr fun a ha=>hFam (some a) (hx.2 a ha) y hy)

/-- A whole ideal equality from actual coordinate cuts. At every point of the
intersection the native simultaneous chart is selected again. Thus there is
no passage from one stalk equality to an unsupported global equality. -/
private theorem sum_vanishing_coordinate_intersection
    {N B Q : Set Y} {E : List (Set Y)}
    (hB : IsClosed B) (hQ : IsClosed Q)
    (hTr : IsTransverse n N E) (S : Finset (Fin E.length))
    (hBN : B⊆N)
    (hZB : N∩BoundaryCount.memberInter E S⊆B)
    (hZQ : N∩BoundaryCount.memberInter E S⊆Q)
    (hBQ : B∩Q⊆N∩BoundaryCount.memberInter E S)
    (hcuts : ∀a∈S,B⊆E.get a ∨ Q⊆E.get a) :
    RestrictedIdealExtension.sumIdeal (vanishingIdeal (n:=n) B) (vanishingIdeal (n:=n) Q)=
      vanishingIdeal (n:=n) (N∩BoundaryCount.memberInter E S) := by
  ext x g
  by_cases hx : x∈N∩BoundaryCount.memberInter E S
  · obtain ⟨S₀,T,⟨Φ,hsrc,hzero,hFam⟩,_hfree⟩:=hTr x hx.1
    have hFam' : ∀o : Option (Fin E.length),x∈o.elim N E.get→
        ∀y∈flatDomain Φ,y∈o.elim N E.get↔
          Φ.toFun (chartAt (ComplexModel n) x y)∈coordSubspace (o.elim S₀ T) :=
      fun o ho _ hy=>hFam o ho hy.1 hy.2
    have hflat:=member_inter_flat Φ hFam' S hx
    apply coordinate_vanishing_sum_eq_at hZB hZQ Φ (S₀∪S.biUnion T) hsrc hzero
      (fun hy hyΦ=>hflat _ ⟨hy,hyΦ⟩)
    intro a ha
    have hHol:=holomorphicAt_flatCoord Φ a (mem_flatDomain_self Φ)
    have hOpen:∀ᶠy in 𝓝 x,y∈flatDomain Φ:=(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)
    rcases Finset.mem_union.mp ha with ha | ha
    · left
      refine ⟨hHol,?_⟩
      filter_upwards [hOpen] with y hy hyB
      exact ((hFam' none hx.1 y hy).mp (hBN hyB)) a ha
    · obtain ⟨b,hbS,hab⟩:=Finset.mem_biUnion.mp ha
      rcases hcuts b hbS with hbB | hbQ
      · left
        refine ⟨hHol,?_⟩
        filter_upwards [hOpen] with y hy hyB
        exact ((hFam' (some b) (hx.2 b hbS) y hy).mp (hbB hyB)) a hab
      · right
        refine ⟨hHol,?_⟩
        filter_upwards [hOpen] with y hy hyQ
        exact ((hFam' (some b) (hx.2 b hbS) y hy).mp (hbQ hyQ)) a hab
  · have hoff : x∉B∨x∉Q:=by
      by_contra! h
      exact hx (hBQ h)
    constructor
    · intro hg
      refine ⟨hg.1,?_⟩
      have hZc:=hB.inter hQ
      have heq : B∩Q=N∩BoundaryCount.memberInter E S:=Subset.antisymm hBQ
        (fun _ h=>⟨hZB h,hZQ h⟩)
      rw [heq] at hZc
      filter_upwards [hZc.isOpen_compl.mem_nhds hx] with y hy hyZ
      exact (hy hyZ).elim
    · intro hg
      have hOne : (vanishingIdeal (n:=n) B).mem x (1 : Y→ℂ) ∨
          (vanishingIdeal (n:=n) Q).mem x (1 : Y→ℂ) := by
        rcases hoff with hxB | hxQ
        · left
          refine ⟨holomorphicAt_const 1,?_⟩
          filter_upwards [hB.isOpen_compl.mem_nhds hxB] with y hy hyB
          exact (hy hyB).elim
        · right
          refine ⟨holomorphicAt_const 1,?_⟩
          filter_upwards [hQ.isOpen_compl.mem_nhds hxQ] with y hy hyQ
          exact (hy hyQ).elim
      change IsInSpanAt (n:=n) (fun f=>(vanishingIdeal (n:=n) B).mem x f ∨
        (vanishingIdeal (n:=n) Q).mem x f) x g
      exact isInSpanAt_of_eq_mul hOne hg.1 hg.1
        (Eventually.of_forall fun _=>by simp)

private theorem mem_eraseIdx_of_mem_ne {α : Type u} {F : List α} {D : α}
    (i : Fin F.length) (hD : D∈F) (hne : D≠F.get i) : D∈F.eraseIdx i.val := by
  obtain ⟨a,ha⟩:=List.mem_iff_get.mp hD
  exact List.mem_eraseIdx_iff_getElem.mpr ⟨a.val,a.isLt,
    fun heq=>hne (ha.symm.trans (congrArg F.get (Fin.ext heq))),ha⟩

theorem incident_member_inter_iff (F : List (Set Y)) (x y : Y) :
    y∈BoundaryCount.memberInter F (Finset.univ.filter fun a : Fin F.length=>x∈F.get a) ↔
      ∀D∈F,x∈D→y∈D := by
  constructor
  · intro h D hD hx
    obtain ⟨a,rfl⟩:=List.mem_iff_get.mp hD
    exact h a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)
  · intro h a ha
    exact h _ (List.get_mem F a) (Finset.mem_filter.mp ha).2

theorem incident_preimage_iff (F : List (Set Y)) {U : Opens Y} (x y : U) :
    (∀D∈F.map ((Subtype.val : U→Y) ⁻¹' ·),x∈D→y∈D) ↔
      ∀D∈F,x.val∈D→y.val∈D := by
  constructor
  · intro h D hD hx
    exact h ((Subtype.val : U→Y) ⁻¹' D) (List.mem_map.mpr ⟨D,hD,rfl⟩) hx
  · intro h D hD hx
    obtain ⟨H,hH,rfl⟩:=List.mem_map.mp hD
    exact h H hH hx

/-- The sharp-bad critical fibre in a transverse auxiliary slice is exactly
the current upper carrier intersected with all incident remaining slots.
The local marked-stratum ideal is the whole vanishing ideal of that fibre. -/
theorem exists_sharp_bad_window_stratum_of_born (hn : 0 < n)
    {N L Si : Set Y} {old born : List (Set Y)}
    (hN : IsClosedSubmanifold n N) (hL : IsClosedSubmanifold n L)
    (hLN : L ⊆ N) (hFull : IsSNCDivisor n (old ++ born))
    (i j : Fin old.length) (hne : j ≠ i) {x : Y} (hxN : x ∈ N) (hxL : x ∈ L)
    (hRaw : ∀ᶠ y in 𝓝 x, y ∈ L ↔ y ∈ N ∩ old.get j)
    (hAux : ∀ (O : Opens Y), x ∈ O →
      ∃ U : Opens Y, x ∈ U ∧ U ≤ O ∧ ∃ H : Set U,
        IsSNCDivisor n (H :: (old.eraseIdx i.val ++ born).map ((Subtype.val : U → Y) ⁻¹' ·)) ∧
        IsTransverse n ((Subtype.val : U → Y) ⁻¹' N)
          (H :: (old.eraseIdx i.val ++ born).map ((Subtype.val : U → Y) ⁻¹' ·)) ∧
        (Subtype.val : U → Y) ⁻¹' Si = ((Subtype.val : U → Y) ⁻¹' N) ∩ H)
    (b : Fin born.length) (hxb : x ∈ born.get b)
    (hCont : ∀ᶠ y in 𝓝 x, y ∈ N → y ∈ born.get b → y ∈ old.get i)
    (hBad : ∀ᶠ y in 𝓝 x, y ∈ L → y ∈ born.get b →
      y ∈ originalSharpBadLocus (n := n) L (old.eraseIdx j.val ++ born))
    (hIbad : (vanishingIdeal (n := n) (originalSharpBadLocus (n := n) L
      (old.eraseIdx j.val ++ born))).IsCoherent) :
    let Fi := old.eraseIdx i.val ++ born
    let Fj := old.eraseIdx j.val ++ born
    let Bj := originalSharpBadLocus (n := n) L Fj
    let H := ⋃ D ∈ Fj, D
    let Mbad : MarkedIdeal n Y := ⟨L, [], vanishingIdeal (n := n) Bj, 1⟩
      let q:=oldCount H (BlowupTower.refl : BlowupTower Y Y) x
      ∃ (U : Opens Y) (hxU : x∈U) (Haux Z : Set U)
        (Φ : LocalHolomorphicEquivAt (n:=n)
          (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) ⟨x,hxU⟩))
        (SL SZ : Finset (Fin n)),
        let NU:=(Subtype.val : U→Y) ⁻¹' N
        let LU:=(Subtype.val : U→Y) ⁻¹' L
        let FiU:=Fi.map ((Subtype.val : U→Y) ⁻¹' ·)
        let MU:=MarkedIdeal.pullback (Subtype.val : U→Y) Mbad
        let QU : Set U:={p | q≤oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val}
        (∀p : U, oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val≤q) ∧
        IsClosedSubmanifold n Z ∧
        (∀p : U, p∈Z ↔ p.val∈N ∧ ∀D∈Fi,x∈D→p.val∈D) ∧
        Z⊆LU ∧ Z⊆(Subtype.val : U→Y) ⁻¹' Bj ∧
        (∀p : U, p∈Z ↔ p.val∈Bj ∧ oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val=q) ∧
        markedStratum (X:=CMfd.of (n:=n) U) MU QU=(⟨LU,[],vanishingIdeal (n:=n) Z,1⟩ : MarkedIdeal n U) ∧
        (Subtype.val : U→Y) ⁻¹' Si=NU∩Haux ∧
        IsSNCDivisor n (Haux::FiU) ∧ IsTransverse n NU (Haux::FiU) ∧
        HasNormalCrossings n Z (Haux::FiU) ∧
        SL⊆SZ ∧ Φ.source⊆(chartAt (ComplexModel n) (⟨x,hxU⟩ : U)).target ∧
        Φ.toFun (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) ⟨x,hxU⟩)=0 ∧
        (∀p∈flatDomain Φ, p∈LU ↔ Φ.toFun (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) p)∈coordSubspace SL) ∧
        (∀p∈flatDomain Φ, p∈Z ↔ Φ.toFun (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) p)∈coordSubspace SZ) := by
  let Fi := old.eraseIdx i.val ++ born
  let Fj := old.eraseIdx j.val ++ born
  let Bj := originalSharpBadLocus (n := n) L Fj
  let H := ⋃ D ∈ Fj, D
  let q := oldCount H (BlowupTower.refl : BlowupTower Y Y) x
  have hFj : IsSNCDivisor n Fj := isSNCDivisor_of_sublist hFull
    ((List.eraseIdx_sublist old j.val).append (List.Sublist.refl born))
  obtain ⟨Oc,hxOc,hCountLe,hCountIff⟩ := actual_snc_count_window Fj hFj x
  have hNear : ∀ᶠ y in 𝓝 x, y ∈ Oc ∧
      (y ∈ N → y ∈ born.get b → y ∈ old.get i) ∧
      (y ∈ L → y ∈ born.get b → y ∈ Bj) ∧
      (y ∈ L ↔ y ∈ N ∩ old.get j) := by
    filter_upwards [Oc.isOpen.mem_nhds hxOc,hCont,hBad,hRaw] with y hy hc hb hr
    exact ⟨hy,hc,hb,hr⟩
  obtain ⟨O,hO,hOo,hxO⟩ := mem_nhds_iff.mp hNear
  obtain ⟨U,hxU,hUO,Haux,hEU,hTU,hSiU⟩ := hAux ⟨O,hOo⟩ hxO
  let xU : U:=⟨x,hxU⟩
  let NU : Set U:=(Subtype.val : U→Y) ⁻¹' N
  let LU : Set U:=(Subtype.val : U→Y) ⁻¹' L
  let BU : Set U:=(Subtype.val : U→Y) ⁻¹' Bj
  let FiU:=Fi.map ((Subtype.val : U→Y) ⁻¹' ·)
  let FU:=Haux::FiU
  let QU : Set U:={p | q≤oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val}
  have hLU : LU = NU ∩ (Subtype.val : U → Y) ⁻¹' old.get j := by
    ext p
    exact (hO (hUO p.property)).2.2.2
  have hLe (p : U) : oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val≤q :=
    hCountLe p.val (hO (hUO p.property)).1
  have hQIff (p : U) : p∈QU↔∀D∈Fj,x∈D→p.val∈D := by
    have hh:=hCountIff p.val (hO (hUO p.property)).1
    constructor
    · intro hp D hD hxD
      obtain ⟨a,rfl⟩:=List.mem_iff_get.mp hD
      exact hh.mp hp a hxD
    · intro hp
      exact hh.mpr (fun a ha=>hp _ (List.get_mem Fj a) ha)
  let R : Finset (Fin FiU.length):=Finset.univ.filter fun a=>xU∈FiU.get a
  let S : Finset (Fin FU.length):=R.image Fin.succ
  let Z : Set U:=NU∩BoundaryCount.memberInter FU S
  have hZiff (p : U) : p∈Z↔p.val∈N∧∀D∈Fi,x∈D→p.val∈D := by
    have hTail : p∈Z↔p∈NU∧∀D∈FiU,xU∈D→p∈D := by
      change (p∈NU∧∀a∈S,p∈FU.get a)↔_
      constructor
      · rintro ⟨hp,hall⟩
        refine ⟨hp,?_⟩
        intro D hD hxD
        obtain ⟨a,rfl⟩:=List.mem_iff_get.mp hD
        have hsa : a.succ∈S:=Finset.mem_image.mpr ⟨a,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxD⟩,rfl⟩
        exact hall a.succ hsa
      · rintro ⟨hp,hall⟩
        refine ⟨hp,?_⟩
        intro a ha
        obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp ha
        exact hall _ (List.get_mem FiU c) (Finset.mem_filter.mp hc).2
    exact hTail.trans (and_congr Iff.rfl (incident_preimage_iff Fi xU p))
  have hjFi : old.get j ∈ Fi := by
    apply List.mem_append_left
    exact List.mem_eraseIdx_iff_getElem.mpr ⟨j.val,j.isLt,fun heq=>hne (Fin.ext heq),rfl⟩
  have hbFi : born.get b∈Fi:=List.mem_append_right _ (List.get_mem born b)
  have hxj : x∈old.get j := by
    have hh : xU∈LU:=hxL
    rw [hLU] at hh
    exact hh.2
  have hZL : Z⊆LU := by
    intro p hp
    rw [hLU]
    exact ⟨(hZiff p).mp hp |>.1,((hZiff p).mp hp).2 _ hjFi hxj⟩
  have hZB : Z⊆BU := by
    intro p hp
    exact (hO (hUO p.property)).2.2.1 (hZL hp)
      (((hZiff p).mp hp).2 _ hbFi hxb)
  have hFiOther (D : Set Y) (hD : D∈Fi) (hneD : D≠old.get j) : D∈Fj := by
    rcases List.mem_append.mp hD with hOld | hBorn
    · exact List.mem_append_left _ (mem_eraseIdx_of_mem_ne j
        ((List.eraseIdx_sublist old i.val).subset hOld) hneD)
    · exact List.mem_append_right _ hBorn
  have hFjOther (D : Set Y) (hD : D∈Fj) (hneD : D≠old.get i) : D∈Fi := by
    rcases List.mem_append.mp hD with hOld | hBorn
    · exact List.mem_append_left _ (mem_eraseIdx_of_mem_ne i
        ((List.eraseIdx_sublist old j.val).subset hOld) hneD)
    · exact List.mem_append_right _ hBorn
  have hZQ : Z⊆QU := by
    intro p hp
    apply (hQIff p).mpr
    intro D hD hxD
    by_cases hiD : D=old.get i
    · rw [hiD]
      exact (hO (hUO p.property)).2.1 ((hZiff p).mp hp).1
        (((hZiff p).mp hp).2 _ hbFi hxb)
    · exact ((hZiff p).mp hp).2 D (hFjOther D hD hiD) hxD
  have hBQ : BU∩QU⊆Z := by
    intro p hp
    apply (hZiff p).mpr
    refine ⟨hLN hp.1.1,?_⟩
    intro D hD hxD
    by_cases hjD : D=old.get j
    · rw [hjD]
      have hh : p∈LU:=hp.1.1
      rw [hLU] at hh
      exact hh.2
    · exact (hQIff p).mp hp.2 D (hFiOther D hD hjD) hxD
  have hZclosed : IsClosedSubmanifold n Z:=MemberInterAlong.isClosedSubmanifold_inter_memberInter hn
    (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U).1 hEU hTU S
  have hZNC : HasNormalCrossings n Z FU:=MemberInterAlong.hasNormalCrossings_inter_memberInter hTU S
  have hBclosed : IsClosed BU:=
    (isClosed_originalSharpBadLocus hL.1 hFj.1).preimage continuous_subtype_val
  let FjU:=Fj.map ((Subtype.val : U→Y) ⁻¹' ·)
  let SQ : Finset (Fin FjU.length):=Finset.univ.filter fun a=>xU∈FjU.get a
  have hQeq : QU=BoundaryCount.memberInter FjU SQ := by
    ext p
    exact (hQIff p).trans ((incident_preimage_iff Fj xU p).symm.trans
      (incident_member_inter_iff (Y:=CMfd.of (n:=n) U) FjU xU p).symm)
  have hQclosed : IsClosedSubmanifold n QU := by
    rw [hQeq]
    exact BoundaryCount.isClosedSubmanifold_memberInter hn
      (isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hFj) SQ
  have hcuts : ∀a∈S,BU⊆FU.get a ∨ QU⊆FU.get a := by
    intro a ha
    obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨D,hD,hDc⟩:=List.mem_map.mp (List.get_mem FiU c)
    have hxD : x∈D := by
      have hh:=(Finset.mem_filter.mp hc).2
      rwa [←hDc] at hh
    by_cases hjD : D=old.get j
    · left
      intro p hp
      change p∈FiU.get c
      rw [←hDc,hjD]
      have hh : p∈LU:=hp.1
      rw [hLU] at hh
      exact hh.2
    · right
      intro p hp
      change p∈FiU.get c
      rw [←hDc]
      exact (hQIff p).mp hp D (hFiOther D hD hjD) hxD
  have hWhole : RestrictedIdealExtension.sumIdeal (vanishingIdeal (n:=n) BU)
      (vanishingIdeal (n:=n) QU)=vanishingIdeal (n:=n) Z :=
    sum_vanishing_coordinate_intersection (Y:=CMfd.of (n:=n) U) hBclosed hQclosed.1 hTU S
      (fun _ hp=>hLN hp.1) hZB hZQ hBQ hcuts
  have hPullB : GermIdeal.pullback (m:=n) (Subtype.val : U→Y) (vanishingIdeal (n:=n) Bj)=
      vanishingIdeal (n:=n) BU := by
    ext p g
    exact (MarkedIdealRestrictOpen.mem_pullback_val_iff U hIbad).trans
      (BlowupRestrictOpen.vanishingIdeal_opens_mem_iff U).symm
  have hRecord : markedStratum (X:=CMfd.of (n:=n) U) (MarkedIdeal.pullback (Subtype.val : U→Y)
      (⟨L,[],vanishingIdeal (n:=n) Bj,1⟩ : MarkedIdeal n Y)) QU=
      (⟨LU,[],vanishingIdeal (n:=n) Z,1⟩ : MarkedIdeal n U) := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      (𝔪:=markedStratum (X:=CMfd.of (n:=n) U) (MarkedIdeal.pullback (Subtype.val : U→Y)
        (⟨L,[],vanishingIdeal (n:=n) Bj,1⟩ : MarkedIdeal n Y)) QU)
      (𝔫:=(⟨LU,[],vanishingIdeal (n:=n) Z,1⟩ : MarkedIdeal n U)) rfl rfl ?_ rfl
    change RestrictedIdealExtension.sumIdeal
      (IdealWeightPowers.idealPow (GermIdeal.pullback (m:=n) (Subtype.val : U→Y) (vanishingIdeal (n:=n) Bj)) 1)
      (IdealWeightPowers.idealPow (vanishingIdeal (n:=n) QU) 1)=_
    rw [hPullB]
    have hBI : (vanishingIdeal (n:=n) BU).IsCoherent:=by
      rw [←hPullB]
      exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hIbad
    have hQI:=VanishingIdealCoherent.isCoherent_vanishingIdeal hQclosed
    rw [IdealWeightPowers.idealPow_succ,IdealWeightPowers.idealPow_zero,
      BlowupControlledTransform.unitIdeal_mul hBI,
      IdealWeightPowers.idealPow_succ,IdealWeightPowers.idealPow_zero,
      BlowupControlledTransform.unitIdeal_mul hQI]
    exact hWhole
  have hxZ : xU∈Z := by
    apply (hZiff xU).mpr
    exact ⟨hxN,fun _ _ hh=>hh⟩
  obtain ⟨S₀,TF,⟨Φ,hsrc,hzero,hFam⟩,_hfree⟩:=hTU xU hxN
  have hFam' : ∀o : Option (Fin FU.length),xU∈o.elim NU FU.get→
      ∀p∈flatDomain Φ,p∈o.elim NU FU.get↔
        Φ.toFun (chartAt (ComplexModel n) xU p)∈coordSubspace (o.elim S₀ TF) :=
    fun o ho _ hp=>hFam o ho hp.1 hp.2
  obtain ⟨a,ha⟩:=List.mem_iff_get.mp
    (List.mem_map.mpr ⟨old.get j,hjFi,rfl⟩ :
      (Subtype.val : U→Y) ⁻¹' old.get j∈FiU)
  let aj : Fin FU.length:=a.succ
  have hgetaj : FU.get aj=(Subtype.val : U→Y) ⁻¹' old.get j := ha
  let SL:=S₀∪TF aj
  let SZ:=S₀∪S.biUnion TF
  have haj : aj∈S:=Finset.mem_image.mpr ⟨a,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [ha]; exact hxj⟩,rfl⟩
  have hSL : SL⊆SZ := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact Finset.mem_union_left _ hc
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨aj,haj,hc⟩)
  have hLflat : ∀p∈flatDomain Φ,p∈LU↔
      Φ.toFun (chartAt (ComplexModel n) xU p)∈coordSubspace SL := by
    have hh:=member_inter_flat (Y:=CMfd.of (n:=n) U) Φ hFam' ({aj} : Finset (Fin FU.length))
      (show xU∈NU∩BoundaryCount.memberInter FU {aj} from
        ⟨hxN,fun c hc=>by rw [Finset.mem_singleton.mp hc,hgetaj]; exact hxj⟩)
    intro p hp
    have heq : NU∩BoundaryCount.memberInter FU {aj}=LU := by
      rw [hLU]
      ext z
      simp only [BoundaryCount.memberInter,Finset.mem_singleton,forall_eq,hgetaj]
      rfl
    simpa only [heq,Finset.singleton_biUnion] using hh p hp
  refine ⟨U,hxU,Haux,Z,Φ,SL,SZ,hLe,hZclosed,hZiff,hZL,hZB,?_,hRecord,hSiU,hEU,hTU,hZNC,hSL,hsrc,hzero,hLflat,?_⟩
  · intro p
    constructor
    · intro hp
      exact ⟨hZB hp,(hLe p).antisymm (hZQ hp)⟩
    · rintro ⟨hp,hcount⟩
      exact hBQ ⟨hp,by change q≤_; rw [hcount]⟩
  · exact member_inter_flat (Y:=CMfd.of (n:=n) U) Φ hFam' S hxZ


/-- Ordinary current processed geometry, with every original boundary slot. -/
theorem exists_sharp_bad_processed_window_stratum_core
    (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀x∈(geoTransformAlong (geometricTemplate W []) T).N,
      ∀a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x≤1)
    (i j : Fin E.length) (hne : j≠i)
    (hNCi : let A:=geoTransformAlong (geometricTemplate W []) T
      let Si:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n Si ((E.map (strictAlong T)).eraseIdx i.val++A.E))
    (hDensei : let A:=geoTransformAlong (geometricTemplate W []) T
      let Si:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      Si⊆closure (Si \ ⋃ H∈(E.map (strictAlong T)).eraseIdx i.val++A.E,H)) :
    let A:=geoTransformAlong (geometricTemplate W []) T
    let old:=E.map (strictAlong T)
    let J:=fun a : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
    let Si:=A.N∩(J i).zeroLocus
    let L:=A.N∩(J j).zeroLocus
    let Fi:=old.eraseIdx i.val++A.E
    let Fj:=old.eraseIdx j.val++A.E
    let Bj:=originalSharpBadLocus (n:=n) L Fj
    let H:=⋃D∈Fj,D
    let Mbad : MarkedIdeal n Y:=⟨L,[],vanishingIdeal (n:=n) Bj,1⟩
    ∀ (_hIbad : (vanishingIdeal (n:=n) Bj).IsCoherent)
      (_hLowerDense : L⊆closure (L \ ⋃D∈Fj,D))
      (x : Y), x∈Bj∩Si →
      let q:=oldCount H (BlowupTower.refl : BlowupTower Y Y) x
      ∃ (U : Opens Y) (hxU : x∈U) (Haux Z : Set U)
        (Φ : LocalHolomorphicEquivAt (n:=n)
          (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) ⟨x,hxU⟩))
        (SL SZ : Finset (Fin n)),
        let NU:=(Subtype.val : U→Y) ⁻¹' A.N
        let LU:=(Subtype.val : U→Y) ⁻¹' L
        let FiU:=Fi.map ((Subtype.val : U→Y) ⁻¹' ·)
        let MU:=MarkedIdeal.pullback (Subtype.val : U→Y) Mbad
        let QU : Set U:={p | q≤oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val}
        (∀p : U, oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val≤q) ∧
        IsClosedSubmanifold n Z ∧
        (∀p : U, p∈Z ↔ p.val∈A.N ∧ ∀D∈Fi,x∈D→p.val∈D) ∧
        Z⊆LU ∧ Z⊆(Subtype.val : U→Y) ⁻¹' Bj ∧
        (∀p : U, p∈Z ↔ p.val∈Bj ∧ oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val=q) ∧
        markedStratum (X:=CMfd.of (n:=n) U) MU QU=(⟨LU,[],vanishingIdeal (n:=n) Z,1⟩ : MarkedIdeal n U) ∧
        (Subtype.val : U→Y) ⁻¹' Si=NU∩Haux ∧
        IsSNCDivisor n (Haux::FiU) ∧ IsTransverse n NU (Haux::FiU) ∧
        HasNormalCrossings n Z (Haux::FiU) ∧
        SL⊆SZ ∧ Φ.source⊆(chartAt (ComplexModel n) (⟨x,hxU⟩ : U)).target ∧
        Φ.toFun (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) ⟨x,hxU⟩)=0 ∧
        (∀p∈flatDomain Φ, p∈LU ↔ Φ.toFun (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) p)∈coordSubspace SL) ∧
        (∀p∈flatDomain Φ, p∈Z ↔ Φ.toFun (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) p)∈coordSubspace SZ) := by
  dsimp only
  intro hIbad hLowerDense x hx
  let A:=geoTransformAlong (geometricTemplate W []) T
  let old:=E.map (strictAlong T)
  let J:=fun a : Fin E.length=>(chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
  let Si:=A.N∩(J i).zeroLocus
  let L:=A.N∩(J j).zeroLocus
  let Fi:=old.eraseIdx i.val++A.E
  let Fj:=old.eraseIdx j.val++A.E
  let Bj:=originalSharpBadLocus (n:=n) L Fj
  have hRecorded:=actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hNi:=(chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  have hNj:=(chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=A.N at hNi
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N=A.N at hNj
  have hOrdI : ∀y∈(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N (J i) y≤1 := by
    simpa only [hNi] using fun y hy=>hOrd y hy i
  have hOrdJ : ∀y∈(chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N (J j) y≤1 := by
    simpa only [hNj] using fun y hy=>hOrd y hy j
  have hL : IsClosedSubmanifold n L := by
    have hh:=(HironakaG4OriginalSelectedResidualTail.actual_original_selected_residual_tail
      hn hW hE hdense j T hT hOrdJ).1
    simpa only [hNj] using hh
  obtain ⟨b,hxb,hcont,hbad⟩:=actual_born_bad_germ hn hW hE hdense T hT hFull hOrd
    i j hne hNCi hDensei hLowerDense hx
  let oi : Fin old.length := ⟨i.val, by simp [old]⟩
  let oj : Fin old.length := ⟨j.val, by simp [old]⟩
  have hGeti : old.get oi = strictAlong T (E.get i) := by simp [old, oi]
  have hGetj : old.get oj = strictAlong T (E.get j) := by simp [old, oj]
  have hne' : oj ≠ oi := fun he => hne (Fin.ext (congrArg (fun a : Fin old.length => a.val) he))
  have hxi : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (J i).zeroLocus := by simpa only [hNi] using hx.2
  have hRaw : ∀ᶠ y in 𝓝 x, y ∈ L ↔ y ∈ A.N ∩ old.get oj := by
    rw [hGetj]
    exact HironakaG4LocalLowerTrace.other_residual_support_eventually_old_member
      hn hW hE hdense i T hT hFull hOrdI hNCi hDensei j hne hxi
  have hCont : ∀ᶠ y in 𝓝 x, y ∈ A.N → y ∈ A.E.get b → y ∈ old.get oi := by
    rw [hGeti]
    exact hcont
  have hAux (O : Opens Y) (hxO : x ∈ O) :
      ∃ U : Opens Y, x ∈ U ∧ U ≤ O ∧ ∃ H : Set U,
        IsSNCDivisor n (H :: Fi.map ((Subtype.val : U → Y) ⁻¹' ·)) ∧
        IsTransverse n ((Subtype.val : U → Y) ⁻¹' A.N)
          (H :: Fi.map ((Subtype.val : U → Y) ⁻¹' ·)) ∧
        (Subtype.val : U → Y) ⁻¹' Si = ((Subtype.val : U → Y) ⁻¹' A.N) ∩ H := by
    obtain ⟨U,hxU,hUO,H,hEU,hTU,hSiU,_,_⟩ :=
      protected_slice_window hn hW hE hdense i T hT hFull hOrdI hNCi hDensei hxi O hxO
    exact ⟨U,hxU,hUO,H,hEU,hTU,hSiU⟩
  exact exists_sharp_bad_window_stratum_of_born hn hRecorded.1 hL (show L ⊆ A.N from inter_subset_left)
    hRecorded.2.1 oi oj hne' hx.2.1 hx.1.1 hRaw hAux b hxb hCont hbad hIbad

/-- Ordinary current processed geometry, with every original boundary slot. -/
theorem exists_sharp_bad_processed_window_geometry
    (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀x∈(geoTransformAlong (geometricTemplate W []) T).N,
      ∀a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x≤1)
    (i j : Fin E.length) (hne : j≠i)
    (hNCi : let A:=geoTransformAlong (geometricTemplate W []) T
      let Si:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n Si ((E.map (strictAlong T)).eraseIdx i.val++A.E))
    (hDensei : let A:=geoTransformAlong (geometricTemplate W []) T
      let Si:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      Si⊆closure (Si \ ⋃ H∈(E.map (strictAlong T)).eraseIdx i.val++A.E,H)) :
    let A:=geoTransformAlong (geometricTemplate W []) T
    let old:=E.map (strictAlong T)
    let J:=fun a : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
    let Si:=A.N∩(J i).zeroLocus
    let L:=A.N∩(J j).zeroLocus
    let Fi:=old.eraseIdx i.val++A.E
    let Fj:=old.eraseIdx j.val++A.E
    let Bj:=originalSharpBadLocus (n:=n) L Fj
    let H:=⋃D∈Fj,D
    let Mbad : MarkedIdeal n Y:=⟨L,[],vanishingIdeal (n:=n) Bj,1⟩
    ∀ (_hIbad : (vanishingIdeal (n:=n) Bj).IsCoherent)
      (_hLowerDense : L⊆closure (L \ ⋃D∈Fj,D))
      (x : Y), x∈Bj∩Si →
      let q:=oldCount H (BlowupTower.refl : BlowupTower Y Y) x
      ∃ (U : Opens Y) (hxU : x∈U) (Haux Z : Set U)
        (Φ : LocalHolomorphicEquivAt (n:=n)
          (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) ⟨x,hxU⟩))
        (SL SZ : Finset (Fin n)),
        let NU:=(Subtype.val : U→Y) ⁻¹' A.N
        let LU:=(Subtype.val : U→Y) ⁻¹' L
        let FiU:=Fi.map ((Subtype.val : U→Y) ⁻¹' ·)
        let MU:=MarkedIdeal.pullback (Subtype.val : U→Y) Mbad
        let QU : Set U:={p | q≤oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val}
        (∀p : U, oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val≤q) ∧
        IsClosedSubmanifold n Z ∧ Z⊆LU ∧ Z⊆(Subtype.val : U→Y) ⁻¹' Bj ∧
        (∀p : U, p∈Z ↔ p.val∈Bj ∧ oldCount H (BlowupTower.refl : BlowupTower Y Y) p.val=q) ∧
        markedStratum (X:=CMfd.of (n:=n) U) MU QU=(⟨LU,[],vanishingIdeal (n:=n) Z,1⟩ : MarkedIdeal n U) ∧
        (Subtype.val : U→Y) ⁻¹' Si=NU∩Haux ∧
        IsSNCDivisor n (Haux::FiU) ∧ IsTransverse n NU (Haux::FiU) ∧
        HasNormalCrossings n Z (Haux::FiU) ∧
        SL⊆SZ ∧ Φ.source⊆(chartAt (ComplexModel n) (⟨x,hxU⟩ : U)).target ∧
        Φ.toFun (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) ⟨x,hxU⟩)=0 ∧
        (∀p∈flatDomain Φ, p∈LU ↔ Φ.toFun (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) p)∈coordSubspace SL) ∧
        (∀p∈flatDomain Φ, p∈Z ↔ Φ.toFun (chartAt (ComplexModel n) (⟨x,hxU⟩ : U) p)∈coordSubspace SZ) := by
  dsimp only
  intro hIbad hLowerDense x hx
  obtain ⟨U,hxU,Haux,Z,Φ,SL,SZ,hLe,hZc,_,hZL,hZbad,hFibre,hRecord,hSlice,hSNC,
    hTr,hZNC,hMask,hSrc,hZero,hLflat,hZflat⟩ :=
      exists_sharp_bad_processed_window_stratum_core hn hW hE hdense T hT hFull
        hOrd i j hne hNCi hDensei hIbad hLowerDense x hx
  exact ⟨U,hxU,Haux,Z,Φ,SL,SZ,hLe,hZc,hZL,hZbad,hFibre,hRecord,hSlice,hSNC,
    hTr,hZNC,hMask,hSrc,hZero,hLflat,hZflat⟩

end
end Hironaka.HironakaSharpBadProcessedWindowGeometry
