import Hironaka.Resolution.HironakaG4OriginalSelectedResidualTail
import Hironaka.Resolution.HironakaG4ResidualInductionInputs
import Hironaka.Resolution.HironakaG4RecordedTowerResidualCompatibility
import Hironaka.Resolution.HironakaG4PreparedCentreCoordinates

/-! Actual CURRENT protection of one processed original residual support.
Source-first complete proof: hironaka-g4-protected-residual-endpoint.tex.
No global other-row bound, further history, phase exit or terminal reflection. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4ProtectedResidualEndpoint

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower NormalCrossings NormalCrossingsComparison
  SimultaneousNormalCrossings HironakaSharpNormalCrossingsOpenLocus
  HironakaG4OriginalSelectedResidualTail HironakaG4RecordedTowerResidualCompatibility
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpOriginalDistinctTraceUSC
  HironakaSharpNestedNormalCrossingsInheritance HironakaG4ActiveMonomialSharpBad
  HironakaG4OrderOneTransverseCoordinates HironakaSharpActualTraceIncidence
  HironakaG4PreparedCentreCoordinates HironakaG4ResidualInductionInputs
  HironakaNormalCrossingsTransversality RelativePrincipalizationSpan RestrictedIdealExtension
  NonmonomialTransformAlong MonomialPartAlong DivisorExponentAlong GermIdealOrder
  InvertibleIdealQuotient MarkedIdeals MarkedIdeals.MarkedIdeal

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem mem_remaining (old born : List (Set X)) (i h : Fin old.length) (hne : h ≠ i) :
    old.get h ∈ old.eraseIdx i.val ++ born := by
  apply List.mem_append_left
  exact List.mem_eraseIdx_iff_getElem.mpr
    ⟨h.val,h.isLt,fun heq => hne (Fin.ext heq),rfl⟩

private theorem incident_get_ne {E : List (Set X)} (hE : IsSNCDivisor n E)
    {x : X} {i j : Fin E.length} (hi : x ∈ E.get i) (hj : x ∈ E.get j) (hne : i ≠ j) :
    E.get i ≠ E.get j := by
  intro heq
  exact hne (eq_of_eventually_mem_iff hE hi hj (Eventually.of_forall fun _ => by rw [heq]))

private theorem singleton_nc_of_get {N : Set X} {E : List (Set X)} {x : X}
    (hNC : normalCrossingsAt (n := n) N E x) (j : Fin E.length) :
    normalCrossingsAt (n := n) N [E.get j] x := by
  obtain ⟨S₀,S,hfam,hcard⟩ := hNC
  refine ⟨S₀,fun _ => S j,?_,fun a ha => hcard j (by simpa using ha)⟩
  apply NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hfam
    (Option.map fun _ : Fin [E.get j].length => j)
  · rintro (_ | a) <;> simp
  · rintro (_ | a) <;> rfl

/-- A unit monomial factor identifies the whole normalized trace and residual germ. -/
theorem normalized_residual_mem_iff_at_unit {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {N : Set M} {I : GermIdeal n M}
    {B : List (Set M)} (hc : (restrictOn n N I).IsCoherent) {x : M}
    (hunit : (monomialPartAlong n N (restrictOn n N I) B).mem x 1) (g : M → ℂ) :
    (restrictOn n N I).mem x g ↔
      (nonmonomialPartAlong n N (restrictOn n N I) B).mem x g := by
  constructor
  · exact le_nonmonomialPartAlong_self hc x g
  · intro hg
    have hnorm : (restrictOn n N (restrictOn n N I)).mem x g := by
      simpa only [Pi.one_apply,one_mul] using hg.2 1 hunit
    exact ⟨hnorm.1,IsInSpanOnAt.trans (fun a ha => ha.2) hnorm.2⟩

private theorem ordinary_order_eq_of_germ {N : Set X} (hN : IsClosedSubmanifold n N)
    {I J : GermIdeal n X} (hcI : I.IsCoherent) (hcJ : J.IsCoherent)
    (hnzI : ∀ y ∈ N,IsNonzeroAlongAt N I y)
    (hnzJ : ∀ y ∈ N,IsNonzeroAlongAt N J y) {x : X} (hx : x ∈ N)
    (heq : ∀ g,I.mem x g ↔ J.mem x g) :
    ordinaryTraceOrder N I x=ordinaryTraceOrder N J x := by
  have hcos (q : ℕ) : x ∈ cosupport n N I q ↔ x ∈ cosupport n N J q := by
    constructor
    · rintro ⟨hxN,horder⟩
      exact ⟨hxN,fun g hg => horder g ((heq g).mpr hg)⟩
    · rintro ⟨hxN,horder⟩
      exact ⟨hxN,fun g hg => horder g ((heq g).mp hg)⟩
  apply Nat.le_antisymm
  · exact (ordinaryTraceOrder_cosupport_iff hN hcJ hnzJ hx _).mp
      ((hcos _).mp ((ordinaryTraceOrder_cosupport_iff hN hcI hnzI hx _).mpr le_rfl))
  · exact (ordinaryTraceOrder_cosupport_iff hN hcI hnzI hx _).mp
      ((hcos _).mpr ((ordinaryTraceOrder_cosupport_iff hN hcJ hnzJ hx _).mpr le_rfl))

private theorem old_born_ne_at {old born : List (Set X)}
    (hE : IsSNCDivisor n (old ++ born)) (h : Fin old.length) (b : Fin born.length)
    {x : X} (hxb : x ∈ born.get b) : old.get h ≠ born.get b := by
  intro heq
  let a : Fin (old ++ born).length := ⟨h.val,by simp only [List.length_append]; omega⟩
  let c : Fin (old ++ born).length := ⟨old.length+b.val,by simp only [List.length_append]; omega⟩
  have ha : (old ++ born).get a=old.get h := by
    simp only [List.get_eq_getElem,a,List.getElem_append_left h.isLt]
  have hc : (old ++ born).get c=born.get b := by
    simp only [List.get_eq_getElem,c,List.getElem_append_right (by omega : old.length ≤ old.length+b.val),
      Nat.add_sub_cancel_left]
  have hac := eq_of_eventually_mem_iff hE
    (show x ∈ (old ++ born).get a from by rw [ha,heq]; exact hxb)
    (show x ∈ (old ++ born).get c from by rw [hc]; exact hxb)
    (Eventually.of_forall fun _ => by rw [ha,hc,heq])
  have hv := congrArg Fin.val hac
  change h.val=old.length+b.val at hv
  omega

/-- An old trace other than the selected row has unit born part near a
point where the remaining actual boundary is transverse to the carrier.
Its whole residual germ equals its whole normalized old trace there. -/
theorem other_row_trace_near_at_remaining_nc (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hFull : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H))
    (i j : Fin old.length) (hne : j ≠ i) {x : X} (hx : x ∈ N)
    (hNC : normalCrossingsAt (n := n) N (old.eraseIdx i.val ++ born) x) :
    ∀ᶠ y in 𝓝 x, (oldMonomialPart N old born j).mem y 1 ∧
      ∀ g, (oldTraceIdeal N old j).mem y g ↔ (oldResidualPart N old born j).mem y g := by
  let F := old.eraseIdx i.val ++ born
  have hFsub : F.Sublist (old ++ born) :=
    (List.eraseIdx_sublist old i.val).append (List.Sublist.refl born)
  have hF : IsSNCDivisor n F := isSNCDivisor_of_sublist hFull hFsub
  have hDenseF : N ⊆ closure (N \ ⋃ H ∈ F, H) := by
    apply hDense.trans (closure_mono ?_)
    rintro y ⟨hyN, hy⟩
    refine ⟨hyN, fun hyF => ?_⟩
    obtain ⟨H, hHF, hyH⟩ := mem_iUnion₂.mp hyF
    exact hy (mem_iUnion₂.mpr ⟨H, hFsub.subset hHF, hyH⟩)
  have hjF : old.get j ∈ F := mem_remaining old born i j hne
  obtain ⟨a, ha⟩ := List.mem_iff_get.mp hjF
  have hUnit : (oldMonomialPart N old born j).mem x 1 := by
    apply (one_mem_monomialPartAlong_iff (oldTraceIdeal N old j) born hx).mpr
    intro b hxb
    have hbF : born.get b ∈ F := List.mem_append_right (old.eraseIdx i.val) (List.get_mem born b)
    obtain ⟨c, hc⟩ := List.mem_iff_get.mp hbF
    have hac : a ≠ c := by
      intro heq
      exact old_born_ne_at hFull j b hxb
        (ha.symm.trans ((congrArg (fun z : Fin F.length => F.get z) heq).trans hc))
    have hexp := divExpAlong_restricted_member_eq_zero_at_normalCrossings hn hN hF hDenseF
      hx hNC a c hac (by rw [hc]; exact hxb)
    simpa only [oldTraceIdeal, ha, hc] using hexp
  obtain ⟨hcI, _, hcJ, _, hcD, _, _, _⟩ := actual_old_parts_geometry hn hN hFull hTr hDense j
  have hEq (g : X → ℂ) :
      (oldTraceIdeal N old j).mem x g ↔ (oldResidualPart N old born j).mem x g :=
    normalized_residual_mem_iff_at_unit hcI hUnit g
  filter_upwards [HadamardBridge.eventually_mem_of_isCoherent hcD hUnit,
    eventually_coherent_germ_eq hcI hcJ hEq] with y hyD hyEq
  exact ⟨hyD, hyEq⟩

/-- Agreement with the whole normalized trace gives exact local support
readback on the carrier. -/
theorem support_near_of_whole_trace_germ {N H : Set X} {J : GermIdeal n X}
    (hH : IsClosedSubmanifold n H) {x : X}
    (hEq : ∀ᶠ y in 𝓝 x, ∀ g,
      (restrictOn n N (vanishingIdeal (n := n) H)).mem y g ↔ J.mem y g) :
    ∀ᶠ y in 𝓝 x, y ∈ N ∩ J.zeroLocus ↔ y ∈ N ∩ H := by
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hH
  filter_upwards [hEq] with y hy
  apply and_congr_right
  intro hyN
  have hZero : y ∈ J.zeroLocus ↔
      y ∈ (restrictOn n N (vanishingIdeal (n := n) H)).zeroLocus := by
    constructor
    · intro hz g hg
      exact hz g ((hy g).mp hg)
    · intro hz g hg
      exact hz g ((hy g).mpr hg)
  exact hZero.trans ((zeroLocus_restrictOn_iff hcH hyN).trans
    (by rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hH.1]))

/-- At a point of a retained prepared row, every other row has unit born
part, its whole residual equals the normalized trace, and its residual
support equals the trace of the actual old member, all on one neighborhood. -/
theorem retained_prepared_other_row_trace_near (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hFull : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H))
    (i j : Fin old.length) (hne : j ≠ i) {x : X}
    (hx : x ∈ N ∩ (oldResidualPart N old born i).zeroLocus)
    (hNC : HasNormalCrossings n (N ∩ (oldResidualPart N old born i).zeroLocus)
      (old.eraseIdx i.val ++ born))
    (hDenseS : N ∩ (oldResidualPart N old born i).zeroLocus ⊆
      closure ((N ∩ (oldResidualPart N old born i).zeroLocus) \
        ⋃ H ∈ old.eraseIdx i.val ++ born, H)) :
    ∀ᶠ y in 𝓝 x, (oldMonomialPart N old born j).mem y 1 ∧
      (∀ g, (oldTraceIdeal N old j).mem y g ↔ (oldResidualPart N old born j).mem y g) ∧
      (y ∈ N ∩ (oldResidualPart N old born j).zeroLocus ↔ y ∈ N ∩ old.get j) := by
  have hPointNC := actual_normalCrossingsAt_of_nested_density hn inter_subset_left hN hDenseS hx
    (hNC x hx)
  have hTrace := other_row_trace_near_at_remaining_nc hn hN hFull hTr hDense i j hne hx.1 hPointNC
  have hOld : IsSNCDivisor n old := isSNCDivisor_of_sublist hFull (List.sublist_append_left _ _)
  have hH := MonomialPart.isClosedSubmanifold_get hn hOld j
  have hSupport := support_near_of_whole_trace_germ hH (hTrace.mono (fun _ hy => hy.2))
  filter_upwards [hTrace, hSupport] with y hy hyS
  exact ⟨hy.1, hy.2, hyS⟩

private theorem prepared_endpoint_protection_of_indexed_rows (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born,D))
    {m : ℕ} (o : Fin m ≃ Fin old.length) (J : Fin m → GermIdeal n X)
    (hResidual : ∀ h, oldResidualPart N old born (o h) = J h) (i : Fin m)
    (hOrd : ∀ y ∈ N, ordinaryTraceOrder N (J i) y ≤ 1)
    (hNC : HasNormalCrossings n (N ∩ (J i).zeroLocus) (old.eraseIdx (o i).val ++ born))
    (hDenseS : N ∩ (J i).zeroLocus ⊆
      closure ((N ∩ (J i).zeroLocus) \ ⋃ D ∈ old.eraseIdx (o i).val ++ born,D)) :
    let S := N ∩ (J i).zeroLocus
    let F := old.eraseIdx (o i).val ++ born
    IsClosedSubmanifold n S ∧
      J i = vanishingIdeal (n := n) S ∧
      (∀ x ∈ S, ∃ U : Opens X, x ∈ U ∧
        IsSNCDivisor n (F.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
        IsTransverse n ((Subtype.val : U → X) ⁻¹' N) (F.map ((Subtype.val : U → X) ⁻¹' ·))) ∧
      (∀ h : Fin m, h ≠ i → ∀ x ∈ S,
        let I := oldTraceIdeal N old (o h)
        ∀ᶠ y in 𝓝 x, (monomialPartAlong n N I born).mem y 1 ∧
          ∀ g, I.mem y g ↔ (J h).mem y g) ∧
      Disjoint (actualFamilyDistinctDefect N J) S := by
  let F := old.eraseIdx (o i).val ++ born
  let I := fun h : Fin m => oldTraceIdeal N old (o h)
  let D := fun h : Fin m => monomialPartAlong n N (I h) born
  let S := N ∩ (J i).zeroLocus
  have hRows (h : Fin m) : (I h).IsCoherent ∧
      (∀ y ∈ N, IsNonzeroAlongAt N (I h) y) ∧
      nonmonomialPartAlong n N (I h) born = J h := by
    have hPart := actual_old_parts_geometry hn hN hFull hTr hDense (o h)
    exact ⟨hPart.1, hPart.2.1, hResidual h⟩
  have hFamily (h : Fin m) : (J h).IsCoherent ∧
      (∀ y ∈ N, IsNonzeroAlongAt N (J h) y) ∧
      ∀ y ∈ N, ∃ f : X → ℂ, HolomorphicAt n f y ∧
        ∀ g, (J h).mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (· = f) y g := by
    rw [← hResidual h]
    have hPart := actual_old_parts_geometry hn hN hFull hTr hDense (o h)
    exact ⟨hPart.2.2.1, hPart.2.2.2.1,
      fun y hy => actual_residual_principal_native hn hN hFull hTr hDense (o h) hy⟩
  have hNorm : (vanishingIdeal (n := n) N).Le (J i) := by
    intro x g hg
    rw [← hResidual i]
    exact le_nonmonomialPartAlong_self (hRows i).1 x g (vanishingIdeal_le_restrictOn x g hg)
  obtain ⟨hS,hWhole⟩ := actual_relative_row_globally_reduced hN (J i) (hFamily i).1
    (hFamily i).2.1 (hFamily i).2.2 hNorm hOrd
  have hFsub : F.Sublist (old ++ born) :=
    (List.eraseIdx_sublist old (o i).val).append (List.Sublist.refl born)
  have hFE : IsSNCDivisor n F := isSNCDivisor_of_sublist hFull hFsub
  have hOldE : IsSNCDivisor n old :=
    isSNCDivisor_of_sublist hFull (List.sublist_append_left old born)
  have hDenseNF : N ⊆ closure (N \ ⋃ H ∈ F,H) := by
    apply hDense.trans (closure_mono ?_)
    intro y hy
    refine ⟨hy.1,fun hyF => ?_⟩
    obtain ⟨H,hHF,hyH⟩ := mem_iUnion₂.mp hyF
    exact hy.2 (mem_iUnion₂.mpr ⟨H,hFsub.subset hHF,hyH⟩)
  have hTransS : IsTransverse n S F :=
    isTransverse_of_hasNormalCrossings_of_subset_closure_diff hNC hDenseS
  have hPointNC (x : X) (hx : x ∈ S) : normalCrossingsAt (n := n) N F x :=
    actual_normalCrossingsAt_of_nested_density hn inter_subset_left hN hDenseS hx (hNC x hx)
  have hWindows (x : X) (hx : x ∈ S) : ∃ U : Opens X,x ∈ U ∧
      IsSNCDivisor n (F.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U → X) ⁻¹' N) (F.map ((Subtype.val : U → X) ⁻¹' ·)) :=
    exists_actual_original_transverse_neighborhood hN.1 hFE hDenseNF (hPointNC x hx)
  have hOne (h : Fin m) : IsClosedSubmanifold n (old.get (o h)) :=
    MonomialPart.isClosedSubmanifold_get hn hOldE (o h)
  have hIndex (h : Fin m) (hne : h ≠ i) : ∃ j : Fin F.length,F.get j = old.get (o h) :=
    List.mem_iff_get.mp (mem_remaining old born (o i) (o h) (fun he => hne (o.injective he)))
  have hLocal (h : Fin m) (hne : h ≠ i) (x : X) (hx : x ∈ S) :
      ∀ᶠ y in 𝓝 x, (D h).mem y 1 ∧ ∀ g, (I h).mem y g ↔ (J h).mem y g := by
    have hTrace := other_row_trace_near_at_remaining_nc hn hN hFull hTr hDense
      (o i) (o h) (fun he => hne (o.injective he)) hx.1 (hPointNC x hx)
    simpa only [oldMonomialPart,hResidual,D,I] using hTrace
  have hEqIJ (h : Fin m) (hne : h ≠ i) (x : X) (hx : x ∈ S) (g : X → ℂ) :
      (I h).mem x g ↔ (J h).mem x g :=
    ((hLocal h hne x hx).self_of_nhds).2 g
  have hLe (h : Fin m) : (I h).Le (J h) := by
    rw [←(hRows h).2.2]
    exact le_nonmonomialPartAlong_self (hRows h).1
  have hHit (h : Fin m) {x : X} (hxN : x ∈ N)
      (hp : h ∈ actualProperPositions J x) : x ∈ old.get (o h) := by
    by_contra hnot
    have hIone : (I h).mem x 1 :=
      ⟨holomorphicAt_const 1,(traceSpan_unit_iff_notMem (hOne h).1 hxN).mpr hnot⟩
    have hJone := hLe h x 1 hIone
    exact (Finset.mem_filter.mp hp).2 hJone
  have hOrder (x : X) (hx : x ∈ S) (h : Fin m) (hp : h ∈ actualProperPositions J x) :
      ordinaryTraceOrder N (J h) x=1 := by
    have hcos : x ∈ cosupport n N (J h) 1 := by
      rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hFamily h).1 hg)]
      exact ⟨hx.1,(actual_proper_iff_zeroLocus (fun a => (hFamily a).1) h x).mp hp⟩
    have hLower := (ordinaryTraceOrder_cosupport_iff hN (hFamily h).1 (hFamily h).2.1 hx.1 1).mp hcos
    by_cases hhi : h=i
    · subst h
      exact (hOrd x hx.1).antisymm hLower
    · obtain ⟨j,hj⟩ := hIndex h hhi
      have hSingle : IsSNCDivisor n [old.get (o h)] := by
        rw [←hj]
        exact isSNCDivisor_of_sublist hFE (by simp)
      have hDenseH : N ⊆ closure (N \ old.get (o h)) := by
        apply hDenseNF.trans (closure_mono ?_)
        intro y hy
        exact ⟨hy.1,fun hyH => hy.2 (mem_iUnion₂.mpr
          ⟨old.get (o h),by rw [←hj]; exact List.get_mem F j,hyH⟩)⟩
      have hNCSingle : normalCrossingsAt (n := n) N [old.get (o h)] x := by
        rw [←hj]
        exact singleton_nc_of_get (hPointNC x hx) j
      have hRawOrder := (normalCrossingsAt_singleton_iff_order_one hn hN hSingle hDenseH
        hx.1 (hHit h hx.1 hp)).mp hNCSingle
      have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal (hOne h)
      have hnzH : ∀ y ∈ N,IsNonzeroAlongAt N
          (vanishingIdeal (n := n) (old.get (o h))) y := fun y hy =>
        HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hSingle hDenseH hy
      have hNormOrder : ordinaryTraceOrder N (I h) x=1 := by
        change ordinaryTraceOrder N (restrictOn n N (vanishingIdeal (n := n) (old.get (o h)))) x=1
        rw [ordinaryTraceOrder_restrictOn_eq hN hcH hnzH hx.1]
        exact hRawOrder
      exact (ordinary_order_eq_of_germ hN (hRows h).1 (hFamily h).1
        (hRows h).2.1 (hFamily h).2.1 hx.1 (hEqIJ h hhi x hx)).symm.trans hNormOrder
  have hSelectedNe (h : Fin m) (hne : h ≠ i) (x : X) (hx : x ∈ S) :
      ¬∀ g,(J i).mem x g ↔ (J h).mem x g := by
    intro heq
    have hNear := eventually_coherent_germ_eq (hFamily i).1 (hFamily h).1 heq
    have hFreq := mem_closure_iff_frequently.mp (hDenseS hx)
    obtain ⟨y,⟨hyS,hyF⟩,hyEq⟩ := (hFreq.and_eventually hNear).exists
    obtain ⟨j,hj⟩ := hIndex h hne
    have hyNotH : y ∉ old.get (o h) := fun hyH =>
      hyF (mem_iUnion₂.mpr ⟨old.get (o h),by rw [←hj]; exact List.get_mem F j,hyH⟩)
    have hIone : (I h).mem y 1 :=
      ⟨holomorphicAt_const 1,(traceSpan_unit_iff_notMem (hOne h).1 hyS.1).mpr hyNotH⟩
    have hJione := (hyEq 1).mpr (hLe h y 1 hIone)
    rw [hWhole] at hJione
    exact one_ne_zero (hJione.2.self_of_nhds hyS)
  have hGermNe (x : X) (hx : x ∈ S) (h k : Fin m)
      (hp : h ∈ actualProperPositions J x) (kp : k ∈ actualProperPositions J x) (hne : h ≠ k) :
      ¬∀ g,(J h).mem x g ↔ (J k).mem x g := by
    intro heq
    by_cases hhi : h=i
    · subst h
      exact hSelectedNe k (Ne.symm hne) x hx heq
    by_cases hki : k=i
    · subst k
      exact hSelectedNe h hhi x hx (fun g => (heq g).symm)
    obtain ⟨j,hj⟩ := hIndex h hhi
    obtain ⟨l,hl⟩ := hIndex k hki
    have hOldNe : old.get (o h) ≠ old.get (o k) :=
      incident_get_ne hOldE (hHit h hx.1 hp) (hHit k hx.1 kp)
        (fun ho => hne (o.injective ho))
    have hjl : j ≠ l := by
      intro he
      exact hOldNe (hj.symm.trans ((congrArg F.get he).trans hl))
    obtain ⟨g,hg,hgh,hgk⟩ := exists_traceSpan_separator hn hFE hTransS hx j l
      (by rw [hj]; exact hHit h hx.1 hp) (by rw [hl]; exact hHit k hx.1 kp) hjl
    rw [hj] at hgh
    rw [hl] at hgk
    apply hgk
    apply IsInSpanOnAt.trans (S := (vanishingIdeal (n := n) (old.get (o h))).mem x) ?_ hgh
    intro a ha
    have hIh : (I h).mem x a :=
      le_restrictOn (VanishingIdealCoherent.isCoherent_vanishingIdeal (hOne h)) x a ha
    have hJh := (hEqIJ h hhi x hx a).mp hIh
    have hJk := (heq a).mp hJh
    have hIk := (hEqIJ k hki x hx a).mpr hJk
    exact CodimOneCentreAlong.isInSpanOnAt_subset inter_subset_left hIk.2
  refine ⟨hS,hWhole,hWindows,hLocal,?_⟩
  apply Set.disjoint_left.mpr
  intro x hxZ hxS
  have hRigidity := (actual_productOrder_eq_distinct_iff hN (fun h => (hFamily h).1)
    (fun h => (hFamily h).2.1) (fun h => (hFamily h).2.2) hxS.1).mpr
    ⟨fun h hp => hOrder x hxS h hp,?_⟩
  · have hlt := hxZ.2
    change actualDistinctProperCount J x < ordinaryTraceOrder N
      (relativeIdealListProduct N (List.ofFn J)) x at hlt
    rw [hRigidity] at hlt
    omega
  · intro h hp k kp heq
    by_contra hne
    exact hGermNe x hxS h k hp kp hne (Quotient.exact heq)


/-- Actual retained preparation of one row excludes the true first
distinct defect along that row's support. The other rows can still
have defects elsewhere. -/
theorem retained_prepared_support_disjoint_distinct_defect_native (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born,D))
    (i : Fin old.length)
    (hOrd : ∀ y ∈ N, ordinaryTraceOrder N (oldResidualPart N old born i) y ≤ 1)
    (hNC : HasNormalCrossings n (N ∩ (oldResidualPart N old born i).zeroLocus)
      (old.eraseIdx i.val ++ born))
    (hDenseS : N ∩ (oldResidualPart N old born i).zeroLocus ⊆
      closure ((N ∩ (oldResidualPart N old born i).zeroLocus) \ ⋃ D ∈ old.eraseIdx i.val ++ born,D)) :
    Disjoint (actualFamilyDistinctDefect N (oldResidualPart N old born))
      (N ∩ (oldResidualPart N old born i).zeroLocus) :=
  (prepared_endpoint_protection_of_indexed_rows hn hN hFull hTr hDense
    (Equiv.refl _) (oldResidualPart N old born) (fun _ => rfl) i hOrd hNC hDenseS).2.2.2.2

/-- Actual CURRENT selected NC/density produces genuine protected original
row geometry and excludes the TRUE first distinct defect along that support.
There is no global other-row bound, future-history or phase-exit hypothesis. -/
theorem actual_original_selected_endpoint_protection (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i : Fin E.length)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H)) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
    let F := (E.map (strictAlong T)).eraseIdx i.val ++ A.E
    IsClosedSubmanifold n S ∧
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal=
        vanishingIdeal (n := n) S ∧
      (∀ x ∈ S,∃ U : Opens Y,x ∈ U ∧
        IsSNCDivisor n (F.map ((Subtype.val : U → Y) ⁻¹' ·)) ∧
        IsTransverse n ((Subtype.val : U → Y) ⁻¹' A.N)
          (F.map ((Subtype.val : U → Y) ⁻¹' ·))) ∧
      (∀ h : Fin E.length,h ≠ i → ∀ x ∈ S,
        let I := restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get h)))
        ∀ᶠ y in 𝓝 x,(monomialPartAlong n A.N I A.E).mem y 1 ∧
          ∀ g,I.mem y g ↔
            (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).ideal.mem y g) ∧
      Disjoint (chronologicalDistinctDefect W E T) S := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let J := fun h : Fin E.length =>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).ideal
  let o : Fin E.length ≃ Fin old.length := finCongr (List.length_map _).symm
  have hGetOld (h : Fin E.length) : old.get (o h) = strictAlong T (E.get h) := by simp [old,o]
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hRows (h : Fin E.length) : oldResidualPart A.N old A.E (o h) = J h := by
    change nonmonomialPartAlong n A.N
      (restrictOn n A.N (vanishingIdeal (n := n) (old.get (o h)))) A.E = J h
    rw [hGetOld h]
    exact (hRecorded.2.2.2.2 h).2.2.1
  obtain ⟨hS,hWhole,hWindows,hLocal,hDisjoint⟩ :=
    prepared_endpoint_protection_of_indexed_rows hn hRecorded.1 hRecorded.2.1
      hRecorded.2.2.1 hRecorded.2.2.2.1 o J hRows i hOrd hNC hDenseS
  refine ⟨hS,hWhole,hWindows,?_,hDisjoint⟩
  intro h hne x hx
  have hEq := hLocal h hne x hx
  let I := restrictOn n A.N (vanishingIdeal (n := n) (old.get (o h)))
  change ∀ᶠ y in 𝓝 x, (monomialPartAlong n A.N I A.E).mem y 1 ∧
    ∀ g, I.mem y g ↔ (J h).mem y g at hEq
  dsimp only [I] at hEq
  rw [hGetOld h] at hEq
  exact hEq

end
end Hironaka.HironakaG4ProtectedResidualEndpoint
