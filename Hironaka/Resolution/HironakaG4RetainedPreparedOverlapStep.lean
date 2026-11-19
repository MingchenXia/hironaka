import Hironaka.Resolution.HironakaG4RetainedLowerCompactWindow
import Hironaka.Resolution.HironakaG4RetainedPreparedLocalSupport
import Hironaka.Resolution.HironakaActualSharpBadFirstMaximumBlowup
import Hironaka.Resolution.HironakaG34LowerCleanupLift
import Hironaka.Resolution.HironakaG4ProtectedResidualEndpoint
import Hironaka.Resolution.HironakaSharpBadProcessedWindowGeometry
import Hironaka.Resolution.HironakaActualSharpBadMaximumProcessedSlice

/-! Relative retained preparation across a single actual blowup. The
source-window hypothesis is confined to incident protected supports. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedPreparedOverlapStep
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsComparison
  HironakaG4PreparedCentreCoordinates HironakaActualRetainedBornResidualSeed
  HironakaG4ResidualInductionInputs HironakaG4OriginalSelectedResidualTail
  HironakaG4RetainedPreparedLocalSupport HironakaG4RetainedLowerCompactWindow
  HironakaActualSharpBadFirstMaximumBlowup HironakaActualProtectedOtherRowLocalStep
  HironakaG34LowerCleanupLift HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpOriginalProductTraceOrder BoundaryCount
  RelativePrincipalizationSpan RestrictedIdealExtension NonmonomialTransformAlong
  HironakaG4ProtectedResidualEndpoint NormalCrossingsInvariance SimultaneousNormalCrossings
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpBadProcessedWindowGeometry DivisorExponentAlong CanonicalCentres
  HironakaActualSharpBadMaximumProcessedSlice HironakaOriginalNCMarkedStratumHistoryValue
  HironakaOriginalNCCountHistory ResolutionDriver

variable {n : ℕ} {X Y : CMfd.{u} n}

theorem prepared_refl_nc_dense {N : Set X} {old born : List (Set X)}
    (i : Fin old.length) (hPrep : RetainedRowPrepared N old born i (.refl : BlowupTower X X)) :
    let S := N ∩ (oldResidualPart N old born i).zeroLocus
    let F := old.eraseIdx i.val ++ born
    HasNormalCrossings n S F ∧ S ⊆ closure (S \ ⋃ D ∈ F, D) := by
  let S := N ∩ (oldResidualPart N old born i).zeroLocus
  let F := old.eraseIdx i.val ++ born
  have hF₀ : retainedRowBoundary N old born i (.refl : BlowupTower X X) = F := by
    change (old.map (strictAlong (.refl : BlowupTower X X))).eraseIdx i.val ++ born = F
    rw [show old.map (strictAlong (.refl : BlowupTower X X)) = old from List.map_id old]
  obtain ⟨_,hNCS,hDenseS⟩ := hPrep
  change HasNormalCrossings n S (retainedRowBoundary N old born i .refl) at hNCS
  change S ⊆ closure (S \ ⋃ D ∈ retainedRowBoundary N old born i .refl, D) at hDenseS
  rw [hF₀] at hNCS hDenseS
  exact ⟨hNCS,hDenseS⟩

/-- The current true distinct defect misses every chosen prepared
retained support, with the original finite row labels intact. -/
theorem retained_prepared_support_disjoint_distinct_defect (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born, D))
    (i : Fin old.length) (hPrep : RetainedRowPrepared N old born i (.refl : BlowupTower X X)) :
    Disjoint (actualFamilyDistinctDefect N (oldResidualPart N old born))
      (retainedRowSupport N old born i (.refl : BlowupTower X X)) := by
  obtain ⟨hNC,hDenseS⟩ := prepared_refl_nc_dense i hPrep
  exact retained_prepared_support_disjoint_distinct_defect_native
    hn hN hFull hTr hDense i hPrep.1 hNC hDenseS

private theorem exists_retained_prepared_auxiliary_window (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born, D))
    (hOrd : ∀ x ∈ N, ∀ i, ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (i : Fin old.length) (hPrep : RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    {x : X} (hx : x ∈ retainedRowSupport N old born i (.refl : BlowupTower X X))
    (O : Opens X) (hxO : x ∈ O) :
    let S := N ∩ (oldResidualPart N old born i).zeroLocus
    let F := old.eraseIdx i.val ++ born
    ∃ U : Opens X, x ∈ U ∧ U ≤ O ∧ ∃ H : Set U,
      IsSNCDivisor n (H :: F.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U → X) ⁻¹' N) (H :: F.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      (Subtype.val : U → X) ⁻¹' S = ((Subtype.val : U → X) ⁻¹' N) ∩ H := by
  obtain ⟨hNC,hDenseS⟩ := prepared_refl_nc_dense i hPrep
  obtain ⟨U,hxU,hUO,H,hSNC,hTrans,hSlice,_⟩ :=
    native_prepared_source_slice_window hn hN hFull hTr hDense i (fun y hy => hOrd y hy i)
      hNC hDenseS hx O hxO
  exact ⟨U,hxU,hUO,H,hSNC,hTrans,hSlice⟩

/-- At a prepared retained support the actual residual supports of all rows
and the born traces have a common free coordinate frame on the carrier. -/
theorem retained_prepared_frame_at_support (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born, D))
    (hEmpty : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
    (i : Fin old.length) (hPrep : RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    {x : X} (hx : x ∈ retainedRowSupport N old born i (.refl : BlowupTower X X)) :
    IsPreparedResidualSNCAt N old born x := by
  classical
  let S := N ∩ (oldResidualPart N old born i).zeroLocus
  let F := old.eraseIdx i.val ++ born
  have hOrd := (retained_row_conditions_of_empty_distinct_defect hn hN hFull hTr hDense hEmpty).1
  obtain ⟨U,hxU,_,H,hGU,hTU,hHU⟩ :=
    exists_retained_prepared_auxiliary_window hn hN hFull hTr hDense hOrd i hPrep hx
      (⊤ : Opens X) (by trivial)
  obtain ⟨hNCS,hDenseS⟩ := prepared_refl_nc_dense i hPrep
  let v : U → X := Subtype.val
  let G := H :: F.map (v ⁻¹' ·)
  let z : U := ⟨x,hxU⟩
  let NU := v ⁻¹' N
  let tag : Fin old.length ⊕ Fin born.length → Fin (old ++ born).length :=
    Sum.elim (fun j => ⟨j.val,by simp only [List.length_append]; omega⟩)
      (fun b => ⟨old.length+b.val,by simp only [List.length_append]; omega⟩)
  have hTagLeft (j : Fin old.length) : (old ++ born).get (tag (.inl j)) = old.get j := by
    simp only [List.get_eq_getElem, tag, Sum.elim_inl, List.getElem_append_left j.isLt]
  have hTagRight (b : Fin born.length) : (old ++ born).get (tag (.inr b)) = born.get b := by
    simp only [List.get_eq_getElem, tag, Sum.elim_inr,
      List.getElem_append_right (by omega : old.length ≤ old.length+b.val),
      Nat.add_sub_cancel_left]
  have hTagInj : Function.Injective tag := by
    rintro (a | b) (c | d) he
    · have hval : a.val = c.val :=
        congrArg (fun f : Fin (old ++ born).length => f.val) he
      exact congrArg Sum.inl (Fin.ext hval)
    · have hval : a.val = old.length+d.val := congrArg Fin.val he
      omega
    · have hval : old.length+b.val = c.val := congrArg Fin.val he
      omega
    · have hval : old.length+b.val = old.length+d.val := congrArg Fin.val he
      exact congrArg Sum.inr (Fin.ext (by omega))
  have hFMem (t : Fin old.length ⊕ Fin born.length) (ht : t ≠ Sum.inl i) :
      (old ++ born).get (tag t) ∈ F := by
    rcases t with (j | b)
    · rw [hTagLeft]
      apply List.mem_append_left
      exact List.mem_eraseIdx_iff_getElem.mpr
        ⟨j.val,j.isLt,fun he => ht (congrArg Sum.inl (Fin.ext he)),rfl⟩
    · rw [hTagRight]
      exact List.mem_append_right _ (List.get_mem born b)
  have hIdx (t : Fin old.length ⊕ Fin born.length) (ht : t ≠ Sum.inl i) :
      ∃ a : Fin G.length, a.val ≠ 0 ∧ G.get a = v ⁻¹' (old ++ born).get (tag t) := by
    obtain ⟨a,ha⟩ := List.mem_iff_get.mp (hFMem t ht)
    let b : Fin (F.map (v ⁻¹' ·)).length := Fin.cast (List.length_map _).symm a
    refine ⟨b.succ,by simp,?_⟩
    simpa only [G,List.get_eq_getElem,List.getElem_cons_succ,List.getElem_map,b,Fin.val_cast,Fin.val_succ] using
      congrArg (fun D => v ⁻¹' D) ha
  let k (t : Fin old.length ⊕ Fin born.length) : Fin G.length :=
    if ht : t = Sum.inl i then ⟨0,by simp [G]⟩ else (hIdx t ht).choose
  have hKget (t : Fin old.length ⊕ Fin born.length) (ht : t ≠ Sum.inl i) :
      G.get (k t) = v ⁻¹' (old ++ born).get (tag t) := by
    simpa only [k,dif_neg ht] using (hIdx t ht).choose_spec.2
  have hKne (t : Fin old.length ⊕ Fin born.length) (ht : t ≠ Sum.inl i) : (k t).val ≠ 0 := by
    simpa only [k,dif_neg ht] using (hIdx t ht).choose_spec.1
  have hKzero : (k (Sum.inl i)).val = 0 := by simp [k]
  have hSrc (t : Fin old.length ⊕ Fin born.length) (ht : t ≠ Sum.inl i) :
      ∀ᶠ y in 𝓝 x, y ∈ preparedSupport N old born t ↔ y ∈ N ∩ (old ++ born).get (tag t) := by
    rcases t with (j | b)
    · rw [hTagLeft]
      have hne : j ≠ i := fun he => ht (congrArg Sum.inl he)
      exact (retained_prepared_other_row_trace_near hn hN hFull hTr hDense i j hne
        hx hNCS hDenseS).mono (fun _ hy => hy.2.2)
    · rw [hTagRight]
      exact Eventually.of_forall (fun _ => Iff.rfl)
  have hTrace (t : Fin old.length ⊕ Fin born.length) :
      ∀ᶠ y in 𝓝 z, y ∈ v ⁻¹' preparedSupport N old born t ↔ y ∈ NU ∩ G.get (k t) := by
    by_cases ht : t = Sum.inl i
    · subst t
      have he : G.get (k (Sum.inl i)) = H := by simp [k,G]
      rw [he]
      exact Eventually.of_forall (fun _ => Set.ext_iff.mp hHU _)
    · rw [hKget t ht]
      have hv : Tendsto v (𝓝 z) (𝓝 x) := (continuous_subtype_val : Continuous v).continuousAt
      exact hv.eventually (hSrc t ht)
  have hInc (t : Fin old.length ⊕ Fin born.length) (ht : x ∈ preparedSupport N old born t) :
      z ∈ NU ∩ G.get (k t) := (hTrace t).self_of_nhds.mp ht
  have hKInj : Set.InjOn k {t | x ∈ preparedSupport N old born t} := by
    intro a ha b hb he
    by_cases hai : a = Sum.inl i
    · subst a
      exact (by
        by_contra hbi
        exact hKne b (Ne.symm hbi) ((congrArg Fin.val he).symm.trans hKzero))
    by_cases hbi : b = Sum.inl i
    · subst b
      exact (hKne a hai ((congrArg Fin.val he).trans hKzero)).elim
    have hEq := congrArg G.get he
    rw [hKget a hai, hKget b hbi] at hEq
    have hEqNear : ∀ᶠ y in 𝓝 x,
        y ∈ (old ++ born).get (tag a) ↔ y ∈ (old ++ born).get (tag b) := by
      filter_upwards [U.isOpen.mem_nhds hxU] with y hy
      exact Set.ext_iff.mp hEq (⟨y,hy⟩ : U)
    exact hTagInj (eq_of_eventually_mem_iff hFull
      ((hSrc a hai).self_of_nhds.mp ha).2 ((hSrc b hbi).self_of_nhds.mp hb).2 hEqNear)
  obtain ⟨Q,p,hFrame,hFree,hInj⟩ :=
    actual_trace_family_frame (X := CMfd.of (n := n) U) hn hGU hTU (show z ∈ NU from hx.1)
  let Q' : Option (Fin old.length ⊕ Fin born.length) → Finset (Fin n) :=
    fun o => o.elim Q (fun t => Q ∪ {p (k t)})
  let R : Option (Fin old.length ⊕ Fin born.length) → Set U :=
    fun o => o.elim NU (fun t => NU ∩ G.get (k t))
  have hRaw : IsCoordinateFamilyAt n R Q' z := by
    apply IsCoordinateFamilyAt.reindex hFrame (Option.map k)
    · intro o; cases o <;> rfl
    · intro o; cases o <;> rfl
  have hFamily :
      ∀ᶠ y in 𝓝 z, ∀ o, y ∈
        v ⁻¹' (o.elim N (preparedSupport N old born)) ↔ y ∈ R o := by
    apply Filter.eventually_all.mpr
    rintro (_ | t)
    · exact Eventually.of_forall (fun _ => Iff.rfl)
    · exact hTrace t
  refine ⟨Q,p ∘ k,?_,fun t ht => hFree (k t) (hInc t ht),?_⟩
  · exact isCoordinateFamilyAt_preimage_val_iff.mp
      (CodimOneAdmissibleAlong.isCoordinateFamilyAt_congr hFamily hRaw)
  · intro a ha b hb he
    exact hKInj ha hb (hInj (hInc a ha) (hInc b hb) he)

/-- A lower sharp bad point on a prepared retained support forces that
prepared row's own born monomial part to be nonunit. -/
theorem retained_prepared_nonunit_on_lower_bad (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born, D))
    (hEmpty : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
    (i j : Fin old.length) (hPrep : RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    {x : X} (hx : x ∈ retainedRowSupport N old born i (.refl : BlowupTower X X))
    (hBad : x ∈ originalSharpBadLocus (n := n) (N ∩ (oldResidualPart N old born j).zeroLocus)
      (old.eraseIdx j.val ++ born)) :
    ¬ (oldMonomialPart N old born i).mem x 1 := by
  classical
  have hOrd := (retained_row_conditions_of_empty_distinct_defect hn hN hFull hTr hDense hEmpty).1
  have hFrame := retained_prepared_frame_at_support hn hN hFull hTr hDense hEmpty i hPrep hx
  obtain ⟨hNCS,hDenseS⟩ := prepared_refl_nc_dense i hPrep
  intro hOne
  have hUnits (a : Fin old.length) : (oldMonomialPart N old born a).mem x 1 := by
    by_cases ha : a = i
    · subst a; exact hOne
    exact ((retained_prepared_other_row_trace_near hn hN hFull hTr hDense i a ha
      hx hNCS hDenseS).self_of_nhds).1
  have hFullBad := originalSharpBadLocus_residual_subset hn hN hFull hTr hDense j hBad
  have hxN : x ∈ N := hx.1
  exact hFullBad.2 (normalCrossingsAt_of_prepared_all_units hn hN hFull hTr hDense
    hxN (hOrd x hxN) hFrame hUnits)

/-- At a lower bad point on a prepared support one actual incident born
slot witnesses both nearby old containment on the upper carrier and
nearby sharp badness on the lower carrier. -/
theorem retained_incident_born_bad_germ (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born, D))
    (hEmpty : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
    (i j : Fin old.length) (hne : j ≠ i)
    (hPrep : RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    {x : X} (hx : x ∈ retainedRowSupport N old born i (.refl : BlowupTower X X))
    (hBad : x ∈ originalSharpBadLocus (n := n) (N ∩ (oldResidualPart N old born j).zeroLocus)
      (old.eraseIdx j.val ++ born)) :
    let L := N ∩ (oldResidualPart N old born j).zeroLocus
    ∃ b : Fin born.length, x ∈ born.get b ∧
      1 ≤ divExpAlong n N (oldTraceIdeal N old i) (born.get b) x ∧
      (∀ᶠ y in 𝓝 x, y ∈ N → y ∈ born.get b → y ∈ old.get i) ∧
      (∀ᶠ y in 𝓝 x, y ∈ L → y ∈ born.get b →
        y ∈ originalSharpBadLocus (n := n) L (old.eraseIdx j.val ++ born)) := by
  obtain ⟨hOrd,hDistinct⟩ := retained_row_conditions_of_empty_distinct_defect hn hN hFull hTr hDense hEmpty
  have hL := (actual_residual_support_local_geometry hn hN hFull hTr hDense hOrd j).1
  have hLowerDense := residual_support_dense_off_remainingBoundary_of_local_dimension
    hn hN hFull hTr hDense hOrd hDistinct j
  exact born_bad_germ_of_nonunit hn hN hFull hTr hDense hL inter_subset_left i j hne
    hLowerDense hx.1 (retained_prepared_nonunit_on_lower_bad hn hN hFull hTr hDense hEmpty i j hPrep hx hBad)

/-- The actual native marked-stratum maximum has the incident remaining
boundary stratum as its germ at a prepared retained support. -/
theorem retained_lower_maximum_eventually_stratum (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born, D))
    (hEmpty : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
    (i j : Fin old.length) (hne : j ≠ i)
    (hPrep : RetainedRowPrepared N old born i (.refl : BlowupTower X X)) :
    let L := N ∩ (oldResidualPart N old born j).zeroLocus
    let Fi := old.eraseIdx i.val ++ born
    let Fj := old.eraseIdx j.val ++ born
    let B := originalSharpBadLocus (n := n) L Fj
    let M : MarkedIdeal n X := ⟨L, [], vanishingIdeal (n := n) B, 1⟩
    let H := ⋃ D ∈ Fj, D
    let C := maxLocus
      (markedStratumHistoryValue M H (.refl : BlowupTower X X)) M.cosupp
    ∀ x ∈ C ∩ retainedRowSupport N old born i .refl,
      ∀ᶠ y in 𝓝 x, y ∈ C ↔ y ∈ N ∧ ∀ D ∈ Fi, x ∈ D → y ∈ D := by
  intro L Fi Fj B M H C x hx
  obtain ⟨hOrd,hDistinct⟩ := retained_row_conditions_of_empty_distinct_defect hn hN hFull hTr hDense hEmpty
  obtain ⟨hL, _, _, _, _, hM, hCos, hH⟩ :=
    sharp_bad_native_domain_of_retained_rows hn hN hFull hTr hDense hOrd hDistinct j
  change M.cosupp = B at hCos
  have hxB : x ∈ B := hCos ▸ hx.1.1
  have hAux := exists_retained_prepared_auxiliary_window hn hN hFull hTr hDense hOrd i hPrep hx.2
  obtain ⟨hNC,hDenseS⟩ := prepared_refl_nc_dense i hPrep
  have hRaw := (retained_prepared_other_row_trace_near hn hN hFull hTr hDense i j hne
    hx.2 hNC hDenseS).mono (fun _ hy => hy.2.2)
  obtain ⟨b,hxb,_,hCont,hBad⟩ :=
    retained_incident_born_bad_germ hn hN hFull hTr hDense hEmpty i j hne hPrep hx.2 hxB
  obtain ⟨U,hxU,_Haux,Z,Φ,SL,SZ,hBound,hZ,hZiff,hZL,_hZB,hFibre,
    hRecord,_hSlice,_hSNC,_hTrans,_hZNC,hMask,hSrc,hZero,hLflat,hZflat⟩ :=
      exists_sharp_bad_window_stratum_of_born hn hN hL inter_subset_left hFull
        i j hne hxB.1.1 hxB.1 hRaw hAux b hxb hCont hBad hM.isWellFormed.isCoherent
  let q := oldCount H (.refl : BlowupTower X X) x
  have hUV : U ≤ HironakaOriginalNCCausalHistoryValue.oldCountLowOpen H
      (.refl : BlowupTower X X) q := fun y hy => hBound ⟨y,hy⟩
  have hpZ : (⟨x,hxU⟩ : U) ∈ Z := (hFibre _).mpr ⟨hxB,rfl⟩
  have hFibreM (z : U) : z ∈ Z ↔ z.val ∈ M.cosupp ∧
      oldCount H (.refl : BlowupTower X X) z.val = q := by
    rw [hCos]
    exact hFibre z
  obtain ⟨W,hWo,hxW,hEq⟩ := native_maximum_germ_of_flat_auxiliary
    M hM hH q U hUV Z hZ.1 hZL hFibreM hRecord (⟨x,hxU⟩ : U) hpZ hx.1
    Φ hSrc hZero SL SZ hMask hLflat hZflat
  have hOpen := U.isOpen.isOpenMap_subtype_val W hWo
  have hxImage : x ∈ (Subtype.val : U → X) '' W := ⟨⟨x,hxU⟩,hxW,rfl⟩
  filter_upwards [hOpen.mem_nhds hxImage] with y hy
  obtain ⟨p,hp,rfl⟩ := hy
  exact (hEq p hp).trans (hZiff p)

/-- A single prepared row is preserved by every actual step certified
at its centre incidence. It gives exact strict-transform support. -/
theorem retained_prepared_row_step_of_incident_protected_windows (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born, D))
    (i : Fin old.length)
    (hPrep : RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hCN : C ⊆ N)
    (hCert : ∀ x ∈ C ∩ retainedRowSupport N old born i .refl,
      ProtectedWindowAt N (retainedRowSupport N old born i .refl)
        (old.eraseIdx i.val ++ born) C x) :
    let R : BlowupTower X Y := .step .refl C π hπ
    RetainedRowPrepared N old born i R ∧
      retainedRowSupport N old born i R =
        geoStrictTransform π C (retainedRowSupport N old born i .refl) := by
  intro R
  let I := oldResidualPart N old born i
  let S := N ∩ I.zeroLocus
  let F := old.eraseIdx i.val ++ born
  let N' := geoStrictTransform π C N
  let S' := geoStrictTransform π C S
  let I' := HironakaSharpActualChronologicalStrictStep.nextRelativeStrict N I C π
  have hOrdI : ∀ x ∈ N, ordinaryTraceOrder N I x ≤ 1 := hPrep.1
  obtain ⟨hSeed,hNZ,hPr⟩ := retainedResidualMarked_geometry hn hN hFull hTr hDense i
  have hI : I.IsCoherent := hSeed.isCoherent
  obtain ⟨hS,hIS⟩ := native_row_globally_reduced hn hN hFull hTr hDense i hOrdI
  obtain ⟨hNCS,hDenseS⟩ := prepared_refl_nc_dense i hPrep
  have hWindows (x : X) (hx : x ∈ S) : ProtectedWindowAt N S F C x := by
    by_cases hxC : x ∈ C
    · exact hCert x ⟨hxC,hx⟩
    · let O : Opens X := ⟨Cᶜ,hπ.1.1.isOpen_compl⟩
      obtain ⟨U,hxU,hUO,H,hEU,hTU,hSlice,_⟩ :=
        native_prepared_source_slice_window hn hN hFull hTr hDense i hOrdI
          hNCS hDenseS hx O hxC
      refine ⟨U,hxU,H,hSlice,hEU,hTU,?_⟩
      intro y hy
      exact (hUO y.property hy).elim
  obtain ⟨hS',hI',hNC',hDense',hOrd'⟩ :=
    same_step_of_source_windows hn I hN hS hI hIS hNZ hPr F hπ hCN hWindows
  have hF' : retainedRowBoundary N old born i R =
      F.map (geoStrictTransform π C) ++ [π ⁻¹' C] := by
    change (old.map (geoStrictTransform π C)).eraseIdx i.val ++
      (born.map (geoStrictTransform π C) ++ [π ⁻¹' C]) = _
    rw [List.map_append,List.eraseIdx_map,List.append_assoc]
  have hSupport : retainedRowSupport N old born i R = S' := by
    change N' ∩ I'.zeroLocus = S'
    have hReduced : I' = vanishingIdeal (n := n) S' := hI'
    rw [hReduced,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hS'.1]
    exact inter_eq_right.mpr (geoStrictTransform_mono π C inter_subset_left)
  refine ⟨⟨hOrd',?_⟩,hSupport⟩
  change HasNormalCrossings n (retainedRowSupport N old born i R)
      (retainedRowBoundary N old born i R) ∧
    retainedRowSupport N old born i R ⊆
      closure (retainedRowSupport N old born i R \ ⋃ D ∈ retainedRowBoundary N old born i R,D)
  rw [hSupport,hF']
  exact ⟨hNC',hDense'⟩

/-- On the exact selected blowup, protected windows at the intersection
with the prepared supports suffice for simultaneous preparation and
exact strict-transform readback. All off-centre windows are constructed
from the native retained row geometry. -/
theorem retained_prepared_rows_of_incident_protected_windows (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born, D))
    (hEmpty : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
    (P : Finset (Fin old.length))
    (hPrep : ∀ i ∈ P, RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hUpper : IsGeoTestTower (geometricTemplate N born) (.step .refl C π hπ))
    (hCert : ∀ i ∈ P, ∀ x ∈ C ∩ retainedRowSupport N old born i .refl,
      ProtectedWindowAt N (retainedRowSupport N old born i .refl)
        (old.eraseIdx i.val ++ born) C x) :
    let R : BlowupTower X Y := .step .refl C π hπ
    ∀ i ∈ P, RetainedRowPrepared N old born i R ∧
      retainedRowSupport N old born i R =
        geoStrictTransform π C (retainedRowSupport N old born i .refl) := by
  intro R i hi
  have hOrd := (retained_row_conditions_of_empty_distinct_defect hn hN hFull hTr hDense hEmpty).1
  have hSelected : RetainedRowPrepared N old born i (.refl : BlowupTower X X) :=
    ⟨fun y hy => hOrd y hy i, (hPrep i hi).2⟩
  exact retained_prepared_row_step_of_incident_protected_windows hn hN hFull hTr hDense
    i hSelected hπ hUpper.2.subset_N (hCert i hi)

/-- A centre germ cut out by the incident remaining divisors on the
carrier supplies the protected windows at every incident prepared row. -/
theorem retained_prepared_rows_of_incident_strata (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born, D))
    (hEmpty : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
    (P : Finset (Fin old.length))
    (hPrep : ∀ i ∈ P, RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hUpper : IsGeoTestTower (geometricTemplate N born) (.step .refl C π hπ))
    (hStratum : ∀ i ∈ P, ∀ x ∈ C ∩ retainedRowSupport N old born i .refl,
      ∀ᶠ y in 𝓝 x, y ∈ C ↔ y ∈ N ∧ ∀ D ∈ old.eraseIdx i.val ++ born, x ∈ D → y ∈ D) :
    let R : BlowupTower X Y := .step .refl C π hπ
    ∀ i ∈ P, RetainedRowPrepared N old born i R ∧
      retainedRowSupport N old born i R =
        geoStrictTransform π C (retainedRowSupport N old born i .refl) := by
  classical
  apply retained_prepared_rows_of_incident_protected_windows hn hN hFull hTr hDense hEmpty
    P hPrep hπ hUpper
  intro i hi x hx
  let F := old.eraseIdx i.val ++ born
  have hOrd := (retained_row_conditions_of_empty_distinct_defect hn hN hFull hTr hDense hEmpty).1
  obtain ⟨O,hO,hOo,hxO⟩ := mem_nhds_iff.mp (hStratum i hi x hx)
  obtain ⟨U,hxU,hUO,H,hSNC,hTrU,hSlice⟩ :=
    exists_retained_prepared_auxiliary_window hn hN hFull hTr hDense hOrd
      i (hPrep i hi) hx.2 ⟨O,hOo⟩ hxO
  let v := (Subtype.val : U → X)
  let FU := F.map (v ⁻¹' ·)
  let xU : U := ⟨x,hxU⟩
  let Q : Finset (Fin FU.length) := Finset.univ.filter fun a => xU ∈ FU.get a
  let e : Fin F.length ≃ Fin FU.length := finCongr (List.length_map _).symm
  have hGet (a : Fin F.length) : FU.get (e a) = v ⁻¹' F.get a := by simp [FU,e]
  have hTrace (z : U) : z ∈ v ⁻¹' C ↔ z ∈ (v ⁻¹' N) ∩ memberInter FU Q := by
    refine (hO (hUO z.property)).trans (and_congr Iff.rfl ?_)
    constructor
    · intro h a ha
      have hxA : xU ∈ FU.get a := (Finset.mem_filter.mp ha).2
      have ha' := e.apply_symm_apply a
      rw [← ha',hGet] at hxA ⊢
      exact h (F.get (e.symm a)) (List.get_mem _ _) hxA
    · intro h D hD hxD
      obtain ⟨a,rfl⟩ := List.mem_iff_get.mp hD
      have ha : e a ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hGet]; exact hxD⟩
      have hMem := h (e a) ha
      rw [hGet] at hMem
      exact hMem
  exact protectedWindowAt_of_window_strata hn U hxU H hSlice hSNC hTrU
    (fun z hz => ⟨Q,(hTrace z).mp hz,Eventually.of_forall hTrace⟩)

end
end Hironaka.HironakaG4RetainedPreparedOverlapStep
