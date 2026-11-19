import Hironaka.Resolution.HironakaActualRetainedBoundaryJointStep
import Hironaka.Resolution.HironakaActualRetainedBornResidualHistory
import Hironaka.Resolution.HironakaOriginalCompactCosupportGlobalScheduler
import Hironaka.Invariant.StepOneEmptyPrefix

/-! ONE internally selected genuine joint terminal tower with an ENTIRE
retained initial born boundary. Its TRUE distinct-count cut is derived from
real defect target-opens in the final consumer; no future sharpness, record
comparison or terminal history is supplied. The empty mask is allowed only
because actual count persistence supplies genuine current-bad containment.
Source-first proof: `hironaka-actual-retained-boundary-mask-block-20261101.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualRetainedBoundaryMaskBlock
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  NormalCrossings NormalCrossingsComparison SimultaneousNormalCrossings
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  HironakaActualRetainedBoundaryJointStep HironakaActualRetainedBornResidualSeed
  HironakaActualRetainedBornResidualHistory HironakaActualFiniteMarkedSumHistories
  HironakaG4PreparedCentreCoordinates HironakaG4ActiveMonomialSharpBad
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualInitialFullCompatibility
  HironakaSharpOriginalProductTraceOrder HironakaSharpActualTraceIncidence
  HironakaG4CompactWholeMonomialMaskPhase HironakaG4SharpBadFootprint
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalMultiBoundaryBadLocus
  DivisorExponentAlong GermIdealOrder MonomialPartAlong

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Same chronological canonical seeds, actual carrier and ENTIRE current born
list; the product is normalized at every factor. -/
def retainedProductMarked (N : Set X) (old born : List (Set X)) (q : ℕ)
    (S : BlowupTower X Y) : MarkedIdeal n Y :=
  let A := geoTransformAlong (geometricTemplate N born) S
  ⟨A.N,A.E,relativeIdealListProduct A.N (old.map fun H =>
    (chronologicalMarked (⟨N,born,nonmonomialPartAlong n N
      (restrictOn n N (vanishingIdeal (n := n) H)) born,0⟩ : MarkedIdeal n X) S).ideal),q⟩

/-- Actual canonical old factor at the original unchanged index. -/
def retainedFactorMarked (N : Set X) (old born : List (Set X))
    (S : BlowupTower X Y) (i : Fin old.length) : MarkedIdeal n Y :=
  let A := geoTransformAlong (geometricTemplate N born) S
  ⟨A.N,A.E,monomialPartAlong n A.N
    (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong S (old.get i)))) A.E,1⟩

/-- The actual inactive NONUNIT canonical factors, fixed original positions. -/
def retainedInactiveRows (N : Set X) (old born : List (Set X))
    (profile : Fin old.length → ℕ) (S : BlowupTower X Y) (x : Y) : Finset (Fin old.length) := by
  classical
  exact Finset.univ.filter fun i => profile i=0 ∧ ¬(retainedFactorMarked N old born S i).ideal.mem x 1

/-- TRUE distinct germ-quotient defect of the SAME retained chronological seeds. -/
def retainedDistinctDefect (N : Set X) (old born : List (Set X)) (S : BlowupTower X Y) : Set Y :=
  actualFamilyDistinctDefect (geoTransformAlong (geometricTemplate N born) S).N
    (fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) S).ideal)

private theorem retained_family_geometry (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S) :
    let A := geoTransformAlong (geometricTemplate N born) S
    ∀ i : Fin old.length,
      let J := (chronologicalMarked (retainedResidualMarked N old born i) S).ideal
      J.IsCoherent ∧ (∀ x ∈ A.N,IsNonzeroAlongAt A.N J x) ∧
        ∀ x ∈ A.N,∃ f : Y → ℂ,HolomorphicAt n f x ∧ ∀ g,J.mem x g ↔
          HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) A.N (·=f) x g := by
  dsimp only
  intro i
  have hSeed := retainedResidualMarked_geometry hn hN hE hTr hdense i
  obtain ⟨hw,hnz,hpr⟩ := chronologicalMarked_actual_geometry hn
    (retainedResidualMarked N old born i) hSeed.1 rfl hSeed.2.1 hSeed.2.2 S hS
  have hCurrentN := (chronologicalMarked_geometric_fields (retainedResidualMarked N old born i) S).1
  rw [hCurrentN] at hnz hpr
  exact ⟨hw.isCoherent,hnz,hpr⟩

private theorem initial_family_geometry (hn : 0 < n) {N : Set X}
    {old : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n old)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old,H)) :
    ∀ i : Fin old.length,
      let I := (originalRelativeMemberMarked N (old.get i)).ideal
      I.IsCoherent ∧ (∀ x ∈ N,IsNonzeroAlongAt N I x) ∧
        ∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,I.mem x g ↔
          HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g := by
  intro i
  have h := original_members_actual_finite_chronological_geometry hn hN hE hdense i
    (.refl : BlowupTower X X) trivial
  exact ⟨h.2.2.2.1.isCoherent,h.2.2.2.2.1,h.2.2.2.2.2⟩

private theorem normalCrossingsAt_subfamily {N : Set X} {E F : List (Set X)}
    {x : X} (h : normalCrossingsAt (n := n) N E x)
    (hsub : ∀ H ∈ F,H ∈ E) : normalCrossingsAt (n := n) N F x := by
  obtain ⟨S₀,S,⟨Φ,ht,h0,hfam⟩,hcard⟩ := h
  have hidx : ∀ j : Fin F.length,∃ i : Fin E.length,E.get i=F.get j :=
    fun j => List.mem_iff_get.mp (hsub _ (List.get_mem _ _))
  choose idx hidx using hidx
  refine ⟨S₀,fun j => S (idx j),⟨Φ,ht,h0,?_⟩,
    fun j hj => hcard (idx j) (by rw [hidx]; exact hj)⟩
  rintro (_ | j) hj y hy hyΦ
  · exact hfam none hj hy hyΦ
  · have h := hfam (some (idx j)) (by simp only [Option.elim]; rw [hidx]; exact hj) hy hyΦ
    simp only [Option.elim] at h ⊢
    rwa [hidx] at h

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

private theorem ordinary_order_eq_of_stalk {N : Set X} (hN : IsClosedSubmanifold n N)
    {I J : GermIdeal n X} (hcI : I.IsCoherent) (hcJ : J.IsCoherent)
    (hnzI : ∀ y ∈ N,IsNonzeroAlongAt N I y) (hnzJ : ∀ y ∈ N,IsNonzeroAlongAt N J y)
    {x : X} (hx : x ∈ N) (hMem : ∀ g,I.mem x g ↔ J.mem x g) :
    ordinaryTraceOrder N I x=ordinaryTraceOrder N J x := by
  apply Nat.le_antisymm
  · apply (ordinaryTraceOrder_cosupport_iff hN hcJ hnzJ hx _).mp
    have h := (ordinaryTraceOrder_cosupport_iff hN hcI hnzI hx (ordinaryTraceOrder N I x)).mpr le_rfl
    exact ⟨hx,fun g hg => h.2 g ((hMem g).mpr hg)⟩
  · apply (ordinaryTraceOrder_cosupport_iff hN hcI hnzI hx _).mp
    have h := (ordinaryTraceOrder_cosupport_iff hN hcJ hnzJ hx (ordinaryTraceOrder N J x)).mpr le_rfl
    exact ⟨hx,fun g hg => h.2 g ((hMem g).mp hg)⟩


/-- Arbitrary retained INITIAL born slots stay present. Full-NC forces the
same true seed germs to be initial old-trace germs only for a pointwise
contradiction; no real native history is restarted on those traces. -/
theorem retained_distinct_defect_subset_current_sharp_bad (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S) :
    retainedDistinctDefect N old born S ⊆ originalSharpBadLocus (n := n)
      (geoTransformAlong (geometricTemplate N born) S).N
      (old.map (strictAlong S) ++ (geoTransformAlong (geometricTemplate N born) S).E) := by
  let A := geoTransformAlong (geometricTemplate N born) S
  let O := old.map (strictAlong S)
  let F := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) S).ideal
  let G := fun j : Fin O.length => (originalRelativeMemberMarked A.N (O.get j)).ideal
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense S hS hFull
  have hOld : IsSNCDivisor n O := isSNCDivisor_of_sublist hRec.2.1 (List.sublist_append_left _ _)
  have hDenseOld : A.N ⊆ closure (A.N \ ⋃ H ∈ O,H) := by
    apply hRec.2.2.2.1.trans (closure_mono ?_)
    intro x hx
    exact ⟨hx.1,fun h => hx.2 (by
      obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp h
      exact mem_iUnion₂.mpr ⟨H,List.mem_append_left _ hH,hxH⟩)⟩
  have hGeomF := retained_family_geometry hn hN hE hTr hdense S hS
  have hFC : ∀ i,(F i).IsCoherent := fun i => (hGeomF i).1
  have hFN : ∀ i,∀ y ∈ A.N,IsNonzeroAlongAt A.N (F i) y := fun i => (hGeomF i).2.1
  have hFP : ∀ i,∀ y ∈ A.N,∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,(F i).mem y g ↔
      HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) A.N (·=f) y g := fun i => (hGeomF i).2.2
  have hGeomG := initial_family_geometry hn hRec.1 hOld hDenseOld
  have hGC : ∀ j,(G j).IsCoherent := fun j => (hGeomG j).1
  have hGN : ∀ j,∀ y ∈ A.N,IsNonzeroAlongAt A.N (G j) y := fun j => (hGeomG j).2.1
  have hGP : ∀ j,∀ y ∈ A.N,∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,(G j).mem y g ↔
      HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) A.N (·=f) y g := fun j => (hGeomG j).2.2
  let e : Fin old.length ≃ Fin O.length := finCongr (List.length_map _).symm
  have hGet (i : Fin old.length) : O.get (e i)=strictAlong S (old.get i) := by simp [O,e]
  intro x hx
  have hxN : x ∈ A.N := hx.1
  refine ⟨hxN,fun hNC => ?_⟩
  have hNCOld : normalCrossingsAt (n := n) A.N O x :=
    normalCrossingsAt_subfamily hNC (fun H hH => List.mem_append_left _ hH)
  have hMem (i : Fin old.length) (g : Y → ℂ) : (F i).mem x g ↔ (G (e i)).mem x g := by
    let I := restrictOn n A.N (vanishingIdeal (n := n) (strictAlong S (old.get i)))
    let D := monomialPartAlong n A.N I A.E
    have hUnit : D.mem x 1 := by
      have h := old_factor_unit_at_full_nc hn hRec.1 hRec.2.1 hRec.2.2.2.1 hxN hNC (e i)
      rw [hGet] at h
      exact h
    have hcI : I.IsCoherent := (hRec.2.2.2.2 i).1
    have hNm : nonmonomialPartAlong n A.N I A.E=F i := (hRec.2.2.2.2 i).2.2.1
    have hFac : I=restrictOn n A.N (D.mul (F i)) := (hRec.2.2.2.2 i).2.2.2
    have hIncl : I.Le (F i) := by
      rw [←hNm]
      exact NonmonomialTransformAlong.le_nonmonomialPartAlong_self hcI
    change (F i).mem x g ↔ (restrictOn n A.N (vanishingIdeal (n := n) (O.get (e i)))).mem x g
    rw [hGet]
    change (F i).mem x g ↔ I.mem x g
    refine ⟨?_,hIncl x g⟩
    intro hg
    have hgHol := GermIdeal.IsCoherent.holomorphicAt_mem (hFC i) hg
    have hMul : (D.mul (F i)).mem x g := by
      change IsInSpanAt (n := n) (fun f => ∃ a b,D.mem x a ∧ (F i).mem x b ∧ f=a*b) x g
      exact InvertibleIdealQuotient.isInSpanAt_self ⟨1,g,hUnit,hg,by simp⟩ hgHol
    rw [hFac]
    exact ⟨hgHol,IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hMul hgHol)⟩
  have hOrder (i : Fin old.length) : ordinaryTraceOrder A.N (F i) x=ordinaryTraceOrder A.N (G (e i)) x :=
    ordinary_order_eq_of_stalk hRec.1 (hFC i) (hGC (e i)) (hFN i) (hGN (e i)) hxN (hMem i)
  have hProper (i : Fin old.length) : i ∈ actualProperPositions F x ↔ e i ∈ actualProperPositions G x := by
    simp only [actualProperPositions,Finset.mem_filter,Finset.mem_univ,true_and]
    exact not_congr (hMem i 1)
  have hWitness := (actual_distinct_defect_iff_witness hRec.1 hFC hFN hFP hxN).mp hx
  have hWitnessG : (∃ j,2 ≤ ordinaryTraceOrder A.N (G j) x) ∨
      ∃ i j,i ≠ j ∧ i ∈ actualProperPositions G x ∧ j ∈ actualProperPositions G x ∧
        (actualIdealGermSetoid G x).r i j := by
    rcases hWitness with ⟨i,hi⟩ | ⟨i,j,hne,hpi,hpj,hrel⟩
    · exact Or.inl ⟨e i,by rwa [←hOrder]⟩
    · refine Or.inr ⟨e i,e j,fun h => hne (e.injective h),(hProper i).mp hpi,(hProper j).mp hpj,?_⟩
      intro g
      exact (hMem i g).symm.trans ((hrel g).trans (hMem j g))
  have hDefG := (actual_distinct_defect_iff_witness hRec.1 hGC hGN hGP hxN).mpr hWitnessG
  change x ∈ chronologicalDistinctDefect A.N O (.refl : BlowupTower Y Y) at hDefG
  exact (initial_actual_defect_subset_sharp_bad hn hRec.1 hOld hDenseOld hDefG).2 hNCOld

theorem retainedProductMarked_eq_canonical (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (q : ℕ)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S) :
    retainedProductMarked N old born q S=
      canonicalProductMarked (geoTransformAlong (geometricTemplate N born) S).N
        (old.map (strictAlong S)) (geoTransformAlong (geometricTemplate N born) S).E q := by
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense S hS hFull
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change relativeIdealListProduct _ (old.map _)=relativeIdealListProduct _ (canonicalResidualFamily _ _ _)
  congr 1
  unfold canonicalResidualFamily
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro H hH
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
  exact (hRec.2.2.2.2 i).2.2.1.symm

private theorem retained_product_ideal (N : Set X) (old born : List (Set X))
    (q : ℕ) (S : BlowupTower X Y) :
    (retainedProductMarked N old born q S).ideal=
      relativeIdealListProduct (geoTransformAlong (geometricTemplate N born) S).N
        (List.ofFn fun i : Fin old.length =>
          (chronologicalMarked (retainedResidualMarked N old born i) S).ideal) := by
  unfold retainedProductMarked
  dsimp only
  congr 1
  conv_lhs => rw [←List.ofFn_get old,List.map_ofFn]
  rfl

theorem retained_product_geometry (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (q : ℕ)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S) :
    let A := geoTransformAlong (geometricTemplate N born) S
    (retainedProductMarked N old born q S).ideal.IsCoherent ∧
      (∀ y ∈ A.N,IsNonzeroAlongAt A.N (retainedProductMarked N old born q S).ideal y) ∧
      (∀ y ∈ A.N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
        ∀ g,(retainedProductMarked N old born q S).ideal.mem y g ↔
          HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) A.N (·=f) y g) ∧
      ∀ y ∈ A.N,ordinaryTraceOrder A.N (retainedProductMarked N old born q S).ideal y=
        ∑ i : Fin old.length,ordinaryTraceOrder A.N
          (chronologicalMarked (retainedResidualMarked N old born i) S).ideal y := by
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  have hWF : (geometricTemplate N born).IsWellFormed := ⟨hN,IdealWeightPowers.isCoherent_unitIdeal,hBorn,hTr⟩
  have hCurrent := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWF S hS
  let F := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) S).ideal
  have hFam := retained_family_geometry hn hN hE hTr hdense S hS
  have hList : ∀ I ∈ List.ofFn F,I.IsCoherent ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate N born) S).N,
        IsNonzeroAlongAt (geoTransformAlong (geometricTemplate N born) S).N I y) ∧
      ∀ y ∈ (geoTransformAlong (geometricTemplate N born) S).N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
        ∀ g,I.mem y g ↔ HolomorphicAt n g y ∧
          IsInSpanOnAt (n := n) (geoTransformAlong (geometricTemplate N born) S).N (·=f) y g := by
    intro I hI
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hI
    exact hFam i
  have hp := relativeIdealListProduct_actual_geometry hCurrent.isClosedSubmanifold_N (List.ofFn F)
    (fun I hI => (hList I hI).1) (fun I hI => (hList I hI).2.1) (fun I hI => (hList I hI).2.2)
  dsimp only
  rw [retained_product_ideal]
  refine ⟨hp.1,hp.2.1,hp.2.2.1,?_⟩
  intro y hy
  simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply] using hp.2.2.2 y hy

private theorem retained_distinct_count_le (N : Set X) (old born : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower X Y) (z : Y),
      actualDistinctProperCount (fun i : Fin old.length =>
        (chronologicalMarked (retainedResidualMarked N old born i) S).ideal) z ≤
          actualDistinctProperCount (oldResidualPart N old born) (S.proj z)
  | _,.refl,_ => le_rfl
  | _,.step S C π hπ,z => by
    let A := geoTransformAlong (geometricTemplate N born) S
    let F := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) S).ideal
    have hCurrentN (i : Fin old.length) :
        (chronologicalMarked (retainedResidualMarked N old born i) S).N=A.N :=
      (chronologicalMarked_geometric_fields (retainedResidualMarked N old born i) S).1
    have hFamily : (fun i : Fin old.length =>
        (chronologicalMarked (retainedResidualMarked N old born i) (.step S C π hπ)).ideal)=
          (fun i => HironakaSharpActualChronologicalStrictStep.nextRelativeStrict A.N (F i) C π) := by
      funext i
      change HironakaSharpActualChronologicalStrictStep.nextRelativeStrict
        (chronologicalMarked (retainedResidualMarked N old born i) S).N (F i) C π=_
      rw [hCurrentN]
    rw [hFamily]
    exact (HironakaG4DistinctResidualCountTransform.actual_distinct_proper_count_nextRelativeStrict_le
      A.N C π F z).trans (retained_distinct_count_le N old born S (π z))

private theorem carrier_projects {N : Set X} (hN : IsClosed N) (born : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower X Y),
      (geoTransformAlong (geometricTemplate N born) S).N ⊆ S.proj ⁻¹' N
  | _,.refl => Set.Subset.rfl
  | _,.step S C π hπ => by
    intro z hz
    have hClosed : IsClosed (geoTransformAlong (geometricTemplate N born) S).N := by
      rw [N_geoTransformAlong]
      exact MemberInterTowerAlong.isClosed_strictAlong S hN
    exact carrier_projects hN born S
      (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hClosed hz)

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

private theorem retained_inactive_activity (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ)
    (hZero : ∀ x ∈ N,∀ i,profile i=0 → ordinaryTraceOrder N (oldResidualPart N old born i) x=0)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S) :
    ∀ z ∈ (geoTransformAlong (geometricTemplate N born) S).N,
      retainedInactiveRows N old born profile S z ⊆ inactiveCanonicalRows N old born profile (S.proj z) := by
  classical
  let A := geoTransformAlong (geometricTemplate N born) S
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense S hS hFull
  have hOld0 := isSNCDivisor_of_sublist hE (List.sublist_append_left _ _)
  have hOld1 := isSNCDivisor_of_sublist hRec.2.1 (List.sublist_append_left _ _)
  have hB1 := isSNCDivisor_of_sublist hRec.2.1 (List.sublist_append_right _ _)
  intro z hz i hi
  obtain ⟨_hiUniv,hiZero,hiNotUnit⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hiZero,?_⟩
  let I1 := restrictOn n A.N (vanishingIdeal (n := n) (strictAlong S (old.get i)))
  let D1 := (retainedFactorMarked N old born S i).ideal
  have hHi0 : IsClosedSubmanifold n (old.get i) := MonomialPart.isClosedSubmanifold_get hn hOld0 i
  have hHi1 : IsClosedSubmanifold n (strictAlong S (old.get i)) := by
    let j : Fin (old.map (strictAlong S)).length := ⟨i.val,by simp⟩
    have hGet : (old.map (strictAlong S)).get j=strictAlong S (old.get i) := by simp [j]
    rw [←hGet]
    exact MonomialPart.isClosedSubmanifold_get hn hOld1 j
  have hcD1 : D1.IsCoherent := isCoherent_monomialPartAlong hn hRec.1 hB1 hRec.2.2.1
    (hRec.2.2.2.2 i).1 (hRec.2.2.2.2 i).2.1
  have hzD : z ∈ D1.zeroLocus := by
    intro f hf
    by_contra hne
    exact hiNotUnit (CompanionReduction.one_mem_of_apply_ne_zero hcD1 hf hne)
  have hzI : z ∈ I1.zeroLocus :=
    fun f hf => hzD f (le_monomialPartAlong hn hB1 hRec.2.2.1 (hRec.2.2.2.2 i).1 z f hf)
  have hzH : z ∈ strictAlong S (old.get i) := by
    have h := (zeroLocus_restrictOn_iff (VanishingIdealCoherent.isCoherent_vanishingIdeal hHi1) hz).mp hzI
    rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHi1.1] at h
  have hpH : S.proj z ∈ old.get i := MemberInterTowerAlong.strictAlong_subset_preimage S hHi0.1 hzH
  have hpN : S.proj z ∈ N := carrier_projects hN.1 born S hz
  obtain ⟨hcI0,_hnzI0,hcJ0,hnzJ0,hcD0,_hnzD0,_hmD0,hFac⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  have huJ : (oldResidualPart N old born i).mem (S.proj z) 1 :=
    unit_of_order_zero hN hcJ0 hnzJ0 hpN (hZero _ hpN i hiZero)
  intro huD
  have huMul : ((oldMonomialPart N old born i).mul (oldResidualPart N old born i)).mem (S.proj z) 1 := by
    change IsInSpanAt (n := n) (fun f => ∃ a b,
      (oldMonomialPart N old born i).mem (S.proj z) a ∧
      (oldResidualPart N old born i).mem (S.proj z) b ∧ f=a*b) (S.proj z) 1
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨1,1,huD,huJ,by simp⟩ (holomorphicAt_const 1)
  have huI : (oldTraceIdeal N old i).mem (S.proj z) 1 := by
    rw [hFac]
    exact le_restrictOn (IdealWeightPowers.isCoherent_mul hcD0 hcJ0) _ 1 huMul
  have hzI0 : S.proj z ∈ (oldTraceIdeal N old i).zeroLocus :=
    (zeroLocus_restrictOn_iff (VanishingIdealCoherent.isCoherent_vanishingIdeal hHi0) hpN).mpr
      (by rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHi0.1])
  exact one_ne_zero (hzI0 1 huI)

private theorem source_qtop_of_actual_qtop (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q : ℕ) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    (hProdTest : IsGeoTestTower (canonicalProductMarked N old born q) S)
    (hEq : MarkedIdeal.RestrictEquiv (geoTransformAlong (canonicalProductMarked N old born q) S)
      (retainedProductMarked N old born q S))
    {z : Y} (hz : z ∈ (geoTransformAlong (geometricTemplate N born) S).N)
    (hzq : ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) S).N
      (retainedProductMarked N old born q S).ideal z=q) :
    S.proj z ∈ N ∧ ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal (S.proj z)=q := by
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense S hS hFull
  have h0 := retained_product_geometry hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial
  have h1 := retained_product_geometry hn hN hE hTr hdense q S hS
  let M := canonicalProductMarked N old born q
  have hc0 : M.ideal.IsCoherent := h0.1
  have hnz0 : ∀ y ∈ N,IsNonzeroAlongAt N M.ideal y := h0.2.1
  have hzActual : z ∈ (retainedProductMarked N old born q S).cosupp :=
    (ordinaryTraceOrder_cosupport_iff hRec.1 h1.1 h1.2.1 hz q).mpr hzq.ge
  have hzNative : z ∈ (geoTransformAlong M S).cosupp := hEq.cosupp_eq.symm ▸ hzActual
  have hp := TransformOffCentre.cosupp_geoTransformAlong_subset M hN hc0 S hProdTest hzNative
  have hGe := (ordinaryTraceOrder_cosupport_iff hN hc0 hnz0 hp.1 q).mp hp
  have hSum := h0.2.2.2 (S.proj z) hp.1
  change ordinaryTraceOrder N M.ideal (S.proj z)=
    ∑ i : Fin old.length,ordinaryTraceOrder N (oldResidualPart N old born i) (S.proj z) at hSum
  have hUp : ordinaryTraceOrder N M.ideal (S.proj z) ≤ q :=
    hSum.trans_le ((Finset.sum_le_sum (fun i _ => hOrd _ hp.1 i)).trans_eq hsum)
  exact ⟨hp.1,hUp.antisymm hGe⟩

private def oldIndex (old : List (Set X)) (S : BlowupTower X Y) :
    Fin old.length ≃ Fin (old.map (strictAlong S)).length := finCongr (List.length_map _).symm

private theorem oldIndex_get (old : List (Set X)) (S : BlowupTower X Y) (i : Fin old.length) :
    (old.map (strictAlong S)).get (oldIndex old S i)=strictAlong S (old.get i) := by
  simp [oldIndex]

private theorem current_factor_eq (N : Set X) (old born : List (Set X))
    (S : BlowupTower X Y) (i : Fin old.length) :
    canonicalFactorMarked (geoTransformAlong (geometricTemplate N born) S).N
      (old.map (strictAlong S)) (geoTransformAlong (geometricTemplate N born) S).E (oldIndex old S i)=
        retainedFactorMarked N old born S i := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change monomialPartAlong n _ (restrictOn n _ (vanishingIdeal (n := n)
    ((old.map (strictAlong S)).get (oldIndex old S i)))) _=_
  rw [oldIndex_get]
  rfl

private theorem current_row_eq (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    (i : Fin old.length) :
    oldResidualPart (geoTransformAlong (geometricTemplate N born) S).N
      (old.map (strictAlong S)) (geoTransformAlong (geometricTemplate N born) S).E (oldIndex old S i)=
        (chronologicalMarked (retainedResidualMarked N old born i) S).ideal := by
  have h := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense S hS hFull
  unfold oldResidualPart oldTraceIdeal
  rw [oldIndex_get]
  exact (h.2.2.2.2 i).2.2.1

private theorem current_inactive_eq (N : Set X) (old born : List (Set X))
    (profile : Fin old.length → ℕ) (S : BlowupTower X Y) (z : Y) :
    let A := geoTransformAlong (geometricTemplate N born) S
    let e := oldIndex old S
    inactiveCanonicalRows A.N (old.map (strictAlong S)) A.E (fun j => profile (e.symm j)) z=
      (retainedInactiveRows N old born profile S z).map e.toEmbedding := by
  classical
  let A := geoTransformAlong (geometricTemplate N born) S
  let O := old.map (strictAlong S)
  let e := oldIndex old S
  change inactiveCanonicalRows A.N O A.E (fun j => profile (e.symm j)) z=
    (retainedInactiveRows N old born profile S z).map e.toEmbedding
  have hD (j : Fin O.length) : oldMonomialPart A.N O A.E j=
      (retainedFactorMarked N old born S (e.symm j)).ideal := by
    have h := congrArg MarkedIdeal.ideal (current_factor_eq N old born S (e.symm j))
    change (canonicalFactorMarked A.N O A.E (e (e.symm j))).ideal=_ at h
    simpa only [e.apply_symm_apply,canonicalFactorMarked] using h
  ext j
  constructor
  · intro hj
    obtain ⟨_hj,heZero,heNotUnit⟩ := Finset.mem_filter.mp hj
    refine Finset.mem_map.mpr ⟨e.symm j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,heZero,?_⟩,e.apply_symm_apply j⟩
    intro hu
    exact heNotUnit ((hD j).symm ▸ hu)
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    obtain ⟨_hi,hiZero,hiNotUnit⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,by change profile (e.symm (e i))=0;simpa only [e.symm_apply_apply] using hiZero,?_⟩
    intro hu
    have hFactor : oldMonomialPart A.N O A.E (e i)=(retainedFactorMarked N old born S i).ideal :=
      congrArg MarkedIdeal.ideal (current_factor_eq N old born S i)
    exact hiNotUnit (hFactor ▸ hu)

private theorem joint_admissible_of_components (hn : 0 < n) {N C : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (q : ℕ) (hq : 1 ≤ q)
    (P : Finset (Fin old.length))
    (hProd : (canonicalProductMarked N old born q).IsAdmissibleCentre C)
    (hFactors : ∀ i ∈ P,(canonicalFactorMarked N old born i).IsAdmissibleCentre C) :
    (jointProfileMarked N old born q P).IsAdmissibleCentre C := by
  let R := canonicalProductMarked N old born q
  let L := P.toList.map (canonicalFactorMarked N old born)
  have hp := retained_product_geometry hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial
  have hTail : ∀ M ∈ L,M.N=R.N ∧ M.E=R.E ∧ M.ideal.IsCoherent ∧ 1 ≤ M.d := by
    intro M hM
    obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hM
    exact ⟨rfl,rfl,(actual_old_parts_geometry hn hN hE hTr hdense i).2.2.2.2.1,le_rfl⟩
  have hCos := (finiteSum_history R L hN hp.1 hq hTail (.refl : BlowupTower X X)).2 trivial |>.1
  have hEB : (finiteSum R L).E=R.E := (finiteSum_geometry R L hp.1 hq hTail).2.1
  refine ⟨hProd.1,?_,?_⟩
  · intro x hx
    change x ∈ (finiteSum R L).cosupp
    rw [←geoTransformAlong_refl (finiteSum R L),hCos]
    simp only [geoTransformAlong_refl]
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact hProd.2.1 hx
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hM
      exact (hFactors i (Finset.mem_toList.mp hi)).2.1 hx
  · change HasNormalCrossings n C (finiteSum R L).E
    rw [hEB]
    exact hProd.2.2

private theorem joint_component_tests (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (q : ℕ) (hq : 1 ≤ q)
    (P : Finset (Fin old.length)) (S : BlowupTower X Y)
    (hTest : IsGeoTestTower (jointProfileMarked N old born q P) S) :
    IsGeoTestTower (geometricTemplate N born) S ∧
      IsGeoTestTower (canonicalProductMarked N old born q) S ∧
      ∀ i ∈ P,IsGeoTestTower (canonicalFactorMarked N old born i) S := by
  let R := canonicalProductMarked N old born q
  let L := P.toList.map (canonicalFactorMarked N old born)
  have hp := retained_product_geometry hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial
  have hTail : ∀ M ∈ L,M.N=R.N ∧ M.E=R.E ∧ M.ideal.IsCoherent ∧ 1 ≤ M.d := by
    intro M hM
    obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hM
    exact ⟨rfl,rfl,(actual_old_parts_geometry hn hN hE hTr hdense i).2.2.2.2.1,le_rfl⟩
  have hAll := (finiteSum_history R L hN hp.1 hq hTail S).1.mp hTest
  have hProd : IsGeoTestTower R S := hAll R List.mem_cons_self
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  have hWF : R.IsWellFormed := ⟨hN,hp.1,hBorn,hTr⟩
  have hCarrier : IsGeoTestTower (geometricTemplate N born) S :=
    HironakaSharpActualOriginalControlledHistory.actual_original_test_history_template R hWF S hProd
  refine ⟨hCarrier,hProd,?_⟩
  intro i hi
  exact hAll _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,Finset.mem_toList.mpr hi,rfl⟩))

/-- The actual q level at EVERY real chronological centre, not a supplied
rank or a terminal-history certificate. -/
def IsRetainedProductEquimultiple (N : Set X) (old born : List (Set X)) (q : ℕ) :
    {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _,.refl => True
  | _,.step S C _ _ => IsRetainedProductEquimultiple N old born q S ∧
      ∀ x ∈ C,ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) S).N
        (retainedProductMarked N old born q S).ideal x=q

private def NativePrefix (N : Set X) (old born : List (Set X))
    (q : ℕ) (P : Finset (Fin old.length)) (S : BlowupTower X Y) : Prop :=
  let A := geoTransformAlong (geometricTemplate N born) S
  IsGeoTestTower (geometricTemplate N born) S ∧
    IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S ∧
    CurrentSharpCentres N (old ++ born) S ∧
    (∀ z ∈ A.N,∀ i : Fin old.length,ordinaryTraceOrder A.N
      (chronologicalMarked (retainedResidualMarked N old born i) S).ideal z ≤
        ordinaryTraceOrder N (oldResidualPart N old born i) (S.proj z)) ∧
    IsRetainedProductEquimultiple N old born q S ∧
    MarkedIdeal.RestrictEquiv (geoTransformAlong (canonicalProductMarked N old born q) S)
      (retainedProductMarked N old born q S) ∧
    ∀ i ∈ P,geoTransformAlong (canonicalFactorMarked N old born i) S=retainedFactorMarked N old born S i

private theorem joint_native_prefix (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (hCount : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      actualDistinctProperCount (oldResidualPart N old born) x < q)
    (P : Finset (Fin old.length)) (hP : ∀ i ∈ P,profile i=0)
    (hBound : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      (inactiveCanonicalRows N old born profile x).card ≤ P.card) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower X Y),
      IsGeoTestTower (jointProfileMarked N old born q P) S → NativePrefix N old born q P S
  | _,.refl,_hTest => by
    have hp := retained_product_geometry hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial
    refine ⟨trivial,trivial,trivial,(fun _ _ _ => le_rfl),trivial,?_,?_⟩
    · exact MarkedIdeal.RestrictEquiv.refl hp.1
    · intro i _hi
      rfl
  | _,.step S C π hπ,hTest => by
    classical
    obtain ⟨hCarrier,hFull,hSharp,hRows,hEqui,hProductEq,hFactorsEq⟩ :=
      joint_native_prefix hn hN hE hTr hdense profile q hq hsum hOrd hCount P hP hBound S hTest.1
    let A := geoTransformAlong (geometricTemplate N born) S
    let O := old.map (strictAlong S)
    let e := oldIndex old S
    let pCur : Fin O.length → ℕ := fun j => profile (e.symm j)
    let PCur := P.map e.toEmbedding
    let N' := geoStrictTransform π C A.N
    let B' := A.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    let R0 := canonicalProductMarked N old born q
    have hTests := joint_component_tests hn hN hE hTr hdense q hq P S hTest.1
    have hTestsNext := joint_component_tests hn hN hE hTr hdense q hq P (.step S C π hπ) hTest
    have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense S hCarrier hFull
    have hGet (i : Fin old.length) : O.get (e i)=strictAlong S (old.get i) := oldIndex_get old S i
    have hRowEq (j : Fin O.length) : oldResidualPart A.N O A.E j=
        (chronologicalMarked (retainedResidualMarked N old born (e.symm j)) S).ideal := by
      have h := current_row_eq hn hN hE hTr hdense S hCarrier hFull (e.symm j)
      change oldResidualPart A.N O A.E (e (e.symm j))=_ at h
      simpa only [e.apply_symm_apply] using h
    have hCurOrd : ∀ z ∈ A.N,∀ j,ordinaryTraceOrder A.N (oldResidualPart A.N O A.E j) z ≤ pCur j := by
      intro z hz j
      rw [hRowEq]
      exact (hRows z hz (e.symm j)).trans (hOrd _ (carrier_projects hN.1 born S hz) (e.symm j))
    have hCurSum : ∑ j,pCur j=q := (Fintype.sum_equiv e.symm pCur profile (fun _ => rfl)).trans hsum
    have hCurP : ∀ j ∈ PCur,pCur j=0 := by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
      change profile (e.symm (e i))=0
      rw [e.symm_apply_apply]
      exact hP i hi
    have hZero : ∀ z ∈ N,∀ i,profile i=0 → ordinaryTraceOrder N (oldResidualPart N old born i) z=0 := by
      intro z hz i hi
      have h := hOrd z hz i
      rw [hi] at h
      exact Nat.eq_zero_of_le_zero h
    have hProdCanonical : retainedProductMarked N old born q S=canonicalProductMarked A.N O A.E q :=
      retainedProductMarked_eq_canonical hn hN hE hTr hdense q S hCarrier hFull
    have hCurBound : ∀ z ∈ A.N,ordinaryTraceOrder A.N (canonicalProductMarked A.N O A.E q).ideal z=q →
        (inactiveCanonicalRows A.N O A.E pCur z).card ≤ PCur.card := by
      intro z hz hzq
      have hzRet : ordinaryTraceOrder A.N (retainedProductMarked N old born q S).ideal z=q := by
        rw [hProdCanonical]
        exact hzq
      have hSource := source_qtop_of_actual_qtop hn hN hE hTr hdense profile q hsum hOrd
        S hCarrier hFull hTests.2.1 hProductEq hz hzRet
      have hAct := retained_inactive_activity hn hN hE hTr hdense profile hZero S hCarrier hFull z hz
      have hIC : inactiveCanonicalRows A.N O A.E pCur z=
          (retainedInactiveRows N old born profile S z).map e.toEmbedding :=
        current_inactive_eq N old born profile S z
      change (inactiveCanonicalRows A.N O A.E pCur z).card ≤ (P.map e.toEmbedding).card
      rw [hIC,Finset.card_map,Finset.card_map]
      exact (Finset.card_le_card hAct).trans (hBound _ hSource.1 hSource.2)
    have hProdActualAdm : (retainedProductMarked N old born q S).IsAdmissibleCentre C :=
      hProductEq.isAdmissibleCentre_iff.mp hTestsNext.2.1.2
    have hProdCurAdm : (canonicalProductMarked A.N O A.E q).IsAdmissibleCentre C := hProdCanonical ▸ hProdActualAdm
    have hFactorCurAdm : ∀ j ∈ PCur,(canonicalFactorMarked A.N O A.E j).IsAdmissibleCentre C := by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
      have hNative := (hTestsNext.2.2 i hi).2
      have hActual : (retainedFactorMarked N old born S i).IsAdmissibleCentre C := hFactorsEq i hi ▸ hNative
      exact (current_factor_eq N old born S i).symm ▸ hActual
    have hJointCurAdm := joint_admissible_of_components hn hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1
      q hq PCur hProdCurAdm hFactorCurAdm
    obtain ⟨hLevel,hNC,hLocalCarrier,hLocalFull,hProductStep,hFactorStep,hRowStep,hOrdStep,_hCountStep⟩ :=
      (actual_retained_boundary_joint_step hn hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1
        pCur q hq hCurSum hCurOrd PCur hCurP hCurBound).2 C π hπ hJointCurAdm
    have hLevelRet : ∀ z ∈ C,ordinaryTraceOrder A.N (retainedProductMarked N old born q S).ideal z=q := by
      intro z hz
      rw [hProdCanonical]
      exact (hLevel z hz).1
    have hCBad : C ⊆ originalSharpBadLocus (n := n) A.N (O ++ A.E) := by
      intro z hz
      have hzN : z ∈ A.N := hProdActualAdm.subset_N hz
      have hSource := source_qtop_of_actual_qtop hn hN hE hTr hdense profile q hsum hOrd
        S hCarrier hFull hTests.2.1 hProductEq hzN (hLevelRet z hz)
      have hCt := (retained_distinct_count_le N old born S z).trans_lt (hCount _ hSource.1 hSource.2)
      apply retained_distinct_defect_subset_current_sharp_bad hn hN hE hTr hdense S hCarrier hFull
      refine ⟨hzN,?_⟩
      rw [←retained_product_ideal N old born q S]
      exact hCt.trans_eq (hLevelRet z hz).symm
    have hNCurrent : A.N=strictAlong S N := N_geoTransformAlong _ _
    have hFullBoundary : (geoTransformAlong (geometricTemplate (univ : Set X) (old ++ born)) S).E=O ++ A.E :=
      retained_born_full_boundary_ordered_dictionary N old born S
    have hSharpNext : CurrentSharpCentres N (old ++ born) (.step S C π hπ) := by
      refine ⟨hSharp,?_⟩
      rw [hNCurrent,←hFullBoundary] at hCBad
      exact hCBad
    have hFullRecord : geoTransformAlong (geometricTemplate (univ : Set X) (old ++ born)) S=
        geometricTemplate univ (O ++ A.E) := by
      rw [template_current,strict_univ,hFullBoundary]
    have hFullAdm : (geoTransformAlong (geometricTemplate (univ : Set X) (old ++ born)) S).IsAdmissibleCentre C := by
      rw [hFullRecord]
      exact hLocalFull.2
    have hFullNext : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) (.step S C π hπ) :=
      ⟨hFull,hFullAdm⟩
    have hCarrierNext := hTestsNext.1
    have hOldNext : old.map (strictAlong (.step S C π hπ))=O.map (geoStrictTransform π C) := by
      dsimp only [O]
      rw [List.map_map]
      rfl
    have hProductNextCanonical : retainedProductMarked N old born q (.step S C π hπ)=
        canonicalProductMarked N' (O.map (geoStrictTransform π C)) B' q := by
      rw [retainedProductMarked_eq_canonical hn hN hE hTr hdense q (.step S C π hπ) hCarrierNext hFullNext]
      change canonicalProductMarked N' (old.map (strictAlong (.step S C π hπ))) B' q=_
      rw [hOldNext]
    have hp0 := retained_product_geometry hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial
    have hpS := retained_product_geometry hn hN hE hTr hdense q S hCarrier
    have hBorn0 := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
    have hWF0 : R0.IsWellFormed := ⟨hN,hp0.1,hBorn0,hTr⟩
    have hNativeWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWF0 S hTests.2.1
    have hNativeProductTransform := hProductEq.geoTransform_eq hNativeWF.isClosedSubmanifold_N.1
      hNativeWF.isCoherent hpS.1 (C := C) hπ.contMDiff
    change MarkedIdeal.RestrictEquiv ((canonicalProductMarked A.N O A.E q).geoTransform C π)
      (canonicalProductMarked N' (O.map (geoStrictTransform π C)) B' q) at hProductStep
    rw [←hProdCanonical,←hProductNextCanonical] at hProductStep
    have hProductNext : MarkedIdeal.RestrictEquiv (geoTransformAlong R0 (.step S C π hπ))
        (retainedProductMarked N old born q (.step S C π hπ)) := by
      change MarkedIdeal.RestrictEquiv ((geoTransformAlong R0 S).geoTransform C π) _
      rw [hNativeProductTransform]
      exact hProductStep
    refine ⟨hCarrierNext,hFullNext,hSharpNext,?_,⟨hEqui,hLevelRet⟩,hProductNext,?_⟩
    · intro z hz i
      let j := e i
      have hBefore : oldResidualPart A.N O A.E j=(chronologicalMarked (retainedResidualMarked N old born i) S).ideal :=
        current_row_eq hn hN hE hTr hdense S hCarrier hFull i
      have hSeedN : (chronologicalMarked (retainedResidualMarked N old born i) S).N=A.N :=
        (chronologicalMarked_geometric_fields (retainedResidualMarked N old born i) S).1
      have hAfter : nonmonomialPartAlong n N'
          (restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform π C (O.get j)))) B'=
            (chronologicalMarked (retainedResidualMarked N old born i) (.step S C π hπ)).ideal := by
        rw [hRowStep,hBefore]
        change HironakaSharpActualChronologicalStrictStep.nextRelativeStrict A.N _ C π=
          HironakaSharpActualChronologicalStrictStep.nextRelativeStrict
            (chronologicalMarked (retainedResidualMarked N old born i) S).N _ C π
        rw [hSeedN]
      have h := hOrdStep z hz j
      rw [hAfter,hBefore] at h
      have hImage : π z ∈ A.N := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hRec.1.1 hz
      exact h.trans (hRows (π z) hImage i)
    · intro i hi
      have hiCur : e i ∈ PCur := Finset.mem_map.mpr ⟨i,hi,rfl⟩
      have hBefore : canonicalFactorMarked A.N O A.E (e i)=retainedFactorMarked N old born S i :=
        current_factor_eq N old born S i
      have h := (hFactorStep (e i) hiCur).2.2
      rw [hBefore] at h
      have hAfter : (⟨N',B',monomialPartAlong n N'
          (restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform π C (O.get (e i))))) B',1⟩ : MarkedIdeal n _)=
            retainedFactorMarked N old born (.step S C π hπ) i := by
        rw [hGet]
        rfl
      change (geoTransformAlong (canonicalFactorMarked N old born i) S).geoTransform C π=_
      rw [hFactorsEq i hi]
      exact h.trans hAfter

/-- WHOLE marked seed readback for reusing a current tuple, with all initial
and later born positions. This derived identity prevents any raw-row reset. -/
theorem retained_seed_eq_chronological_current (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S) (i : Fin old.length) :
    let A := geoTransformAlong (geometricTemplate N born) S
    let j : Fin (old.map (strictAlong S)).length := Fin.cast (List.length_map _).symm i
    retainedResidualMarked A.N (old.map (strictAlong S)) A.E j=
      chronologicalMarked (retainedResidualMarked N old born i) S := by
  have hFields := chronologicalMarked_geometric_fields (retainedResidualMarked N old born i) S
  have hMark := chronologicalMarked_zero_mark (retainedResidualMarked N old born i) rfl S
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of hFields.1.symm hFields.2.symm ?_ hMark.symm
  exact current_row_eq hn hN hE hTr hdense S hS hFull i

/-- Every actual retained chronological defect is closed on its current
carrier, including when that carrier has locally varying dimension. -/
theorem isClosed_retainedDistinctDefect (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S) :
    IsClosed (retainedDistinctDefect N old born S) := by
  have hBorn : IsSNCDivisor n born :=
    NormalCrossingsComparison.isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hWf : (geometricTemplate N born).IsWellFormed :=
    ⟨hN, IdealWeightPowers.isCoherent_unitIdeal, hBorn, hTr⟩
  have hCurrentN := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWf S hS).isClosedSubmanifold_N
  have hRows := retained_family_geometry hn hN hE hTr hdense S hS
  exact isClosed_actualFamilyDistinctDefect hCurrentN (fun i => (hRows i).1)
    (fun i => (hRows i).2.1) (fun i => (hRows i).2.2)

/-- The native reindexed current tuple has a closed true defect. Its
current carrier, full boundary, transversality and density come from the
original data and the actual tests. -/
theorem isClosed_current_retained_distinct_defect (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S) :
    let A := geoTransformAlong (geometricTemplate N born) S
    IsClosed (actualFamilyDistinctDefect A.N (oldResidualPart A.N (old.map (strictAlong S)) A.E)) := by
  obtain ⟨hN', hE', hTr', hdense', _⟩ :=
    actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense S hS hFull
  exact isClosed_retainedDistinctDefect hn hN' hE' hTr' hdense' (.refl : BlowupTower Y Y) trivial

/-- Geometry and row readout of a terminal tower with its actual joint mask. -/
def RetainedJointMaskResult (N : Set X) (old born : List (Set X))
    (profile : Fin old.length → ℕ) (q : ℕ) (P : Finset (Fin old.length))
    (R : BlowupTower X Z) : Prop :=
  IsRetainedProductEquimultiple N old born q R ∧
  RestrictEmptyTower.CentresOver (canonicalProductMarked N old born q).cosupp R ∧
  (∀ k : ℕ,
    let Q := BlowupTowerSplit.head R k
    let A := geoTransformAlong (geometricTemplate N born) Q
    IsGeoTestTower (geometricTemplate N born) Q ∧
    IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) Q ∧
    CurrentSharpCentres N (old ++ born) Q ∧
    RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) N (old ++ born)) Q ∧
    (∀ z ∈ A.N,∀ i : Fin old.length,ordinaryTraceOrder A.N
      (chronologicalMarked (retainedResidualMarked N old born i) Q).ideal z ≤
        ordinaryTraceOrder N (oldResidualPart N old born i) (Q.proj z)) ∧
    (∀ z,actualDistinctProperCount (fun i : Fin old.length =>
      (chronologicalMarked (retainedResidualMarked N old born i) Q).ideal) z ≤
        actualDistinctProperCount (oldResidualPart N old born) (Q.proj z)) ∧
    IsRetainedProductEquimultiple N old born q Q ∧
    IsGeoTestTower (canonicalProductMarked N old born q) Q ∧
    MarkedIdeal.RestrictEquiv (geoTransformAlong (canonicalProductMarked N old born q) Q)
      (retainedProductMarked N old born q Q) ∧
    (∀ i ∈ P,geoTransformAlong (canonicalFactorMarked N old born i) Q=retainedFactorMarked N old born Q i) ∧
    (∀ z ∈ A.N,ordinaryTraceOrder A.N (retainedProductMarked N old born q Q).ideal z=q →
      Q.proj z ∈ N ∧ ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal (Q.proj z)=q ∧
      actualDistinctProperCount (fun i : Fin old.length =>
        (chronologicalMarked (retainedResidualMarked N old born i) Q).ideal) z < q ∧
      (retainedInactiveRows N old born profile Q z).card ≤ P.card) ∧
    ∀ z ∈ A.N,retainedInactiveRows N old born profile Q z ⊆
      inactiveCanonicalRows N old born profile (Q.proj z)) ∧
  ∀ z ∈ (geoTransformAlong (geometricTemplate N born) R).N,
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) R).N
      (retainedProductMarked N old born q R).ideal z=q →
    ∃ i ∈ P,(retainedFactorMarked N old born R i).ideal.mem z 1

/-- Every actual resolution of the joint marked input supplies the sharp
centres, literal row histories and terminal mask erasure. -/
theorem retained_boundary_joint_mask_terminal_readout (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (hCount : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      actualDistinctProperCount (oldResidualPart N old born) x < q)
    (P : Finset (Fin old.length)) (hP : ∀ i ∈ P,profile i=0)
    (hBound : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      (inactiveCanonicalRows N old born profile x).card ≤ P.card)
    (R : BlowupTower X Z) (hResolution : IsGeoResolution (jointProfileMarked N old born q P) R) :
    RetainedJointMaskResult N old born profile q P R := by
  classical
  let M := jointProfileMarked N old born q P
  let R0 := canonicalProductMarked N old born q
  let L := P.toList.map (canonicalFactorMarked N old born)
  have h0 := retained_product_geometry hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial
  have hTail : ∀ B ∈ L,B.N=R0.N ∧ B.E=R0.E ∧ B.ideal.IsCoherent ∧ 1 ≤ B.d := by
    intro B hB
    obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hB
    exact ⟨rfl,rfl,(actual_old_parts_geometry hn hN hE hTr hdense i).2.2.2.2.1,le_rfl⟩
  have hEnd := joint_native_prefix hn hN hE hTr hdense profile q hq hsum hOrd hCount P hP hBound R hResolution.1
  have hEndTests := joint_component_tests hn hN hE hTr hdense q hq P R hResolution.1
  have hFootprint := HironakaAdmissibleSequence.centresOver_cosupp R0 hN h0.1 R hEndTests.2.1
  have hZero : ∀ z ∈ N,∀ i,profile i=0 → ordinaryTraceOrder N (oldResidualPart N old born i) z=0 := by
    intro z hz i hi
    have h := hOrd z hz i
    rw [hi] at h
    exact Nat.eq_zero_of_le_zero h
  refine ⟨hEnd.2.2.2.2.1,hFootprint,?_,?_⟩
  · intro k
    let Q := BlowupTowerSplit.head R k
    have hQ : IsGeoTestTower M Q :=
      ((BlowupTowerSplit.isGeoTestTower_iff_head_tail M R k).mp hResolution.1).1
    obtain ⟨hCarrier,hFull,hSharp,hRows,hEqui,hProdEq,hFactorsEq⟩ :=
      joint_native_prefix hn hN hE hTr hdense profile q hq hsum hOrd hCount P hP hBound Q hQ
    have hTests := joint_component_tests hn hN hE hTr hdense q hq P Q hQ
    have hOver := (currentSharpCentres_original_footprint hN.1 hE.1 Q hSharp).2
    have hActivity := retained_inactive_activity hn hN hE hTr hdense profile hZero Q hCarrier hFull
    refine ⟨hCarrier,hFull,hSharp,hOver,hRows,(fun z => retained_distinct_count_le N old born Q z),
      hEqui,hTests.2.1,hProdEq,hFactorsEq,?_,hActivity⟩
    intro z hz hzq
    have hSource := source_qtop_of_actual_qtop hn hN hE hTr hdense profile q hsum hOrd
      Q hCarrier hFull hTests.2.1 hProdEq hz hzq
    have hCt := (retained_distinct_count_le N old born Q z).trans_lt (hCount _ hSource.1 hSource.2)
    have hCap := (Finset.card_le_card (hActivity z hz)).trans (hBound _ hSource.1 hSource.2)
    exact ⟨hSource.1,hSource.2,hCt,hCap⟩
  · intro z hz hzq
    by_contra hNoUnit
    push Not at hNoUnit
    obtain ⟨hCarrier,hFull,_hSharp,_hRows,_hEqui,hProdEq,hFactorsEq⟩ := hEnd
    have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense R hCarrier hFull
    have hp := retained_product_geometry hn hN hE hTr hdense q R hCarrier
    have hB := isSNCDivisor_of_sublist hRec.2.1 (List.sublist_append_right _ _)
    have hzProduct : z ∈ (geoTransformAlong R0 R).cosupp := hProdEq.cosupp_eq.symm ▸
      (ordinaryTraceOrder_cosupport_iff hRec.1 hp.1 hp.2.1 hz q).mpr hzq.ge
    have hzFactors : ∀ i ∈ P,z ∈ (geoTransformAlong (canonicalFactorMarked N old born i) R).cosupp := by
      intro i hi
      have hcD : (retainedFactorMarked N old born R i).ideal.IsCoherent := isCoherent_monomialPartAlong
        hn hRec.1 hB hRec.2.2.1 (hRec.2.2.2.2 i).1 (hRec.2.2.2.2 i).2.1
      have hzD : z ∈ (retainedFactorMarked N old born R i).ideal.zeroLocus := by
        intro f hf
        by_contra hne
        exact hNoUnit i hi (CompanionReduction.one_mem_of_apply_ne_zero hcD hf hne)
      rw [hFactorsEq i hi]
      change z ∈ cosupport n (geoTransformAlong (geometricTemplate N born) R).N
        (retainedFactorMarked N old born R i).ideal 1
      rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcD hg)]
      exact ⟨hz,hzD⟩
    have hCos := (finiteSum_history R0 L hN h0.1 hq hTail R).2 hResolution.1 |>.1
    have hzM : z ∈ (geoTransformAlong M R).cosupp := by
      change z ∈ (geoTransformAlong (finiteSum R0 L) R).cosupp
      rw [hCos]
      intro B hB
      rcases List.mem_cons.mp hB with rfl | hB
      · exact hzProduct
      · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hB
        exact hzFactors i (Finset.mem_toList.mp hi)
    rw [hResolution.2] at hzM
    exact hzM

/-- ONE internally selected native tower on the real retained initial born
boundary. Nonempty P erases its true mask; EMPTY P gives an actual q exit
because the present DISTINCT-count cut is propagated internally. -/
theorem exists_actual_retained_boundary_joint_mask_block (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (hCompact : IsCompact (canonicalProductMarked N old born q).cosupp)
    (hCount : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      actualDistinctProperCount (oldResidualPart N old born) x < q)
    (P : Finset (Fin old.length)) (hP : ∀ i ∈ P,profile i=0)
    (hBound : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      (inactiveCanonicalRows N old born profile x).card ≤ P.card) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower X Z),
      ResolutionInvariantSpec.IsCanonical (jointProfileMarked N old born q P)
        ((CanonicalCentres.invFamily hn (n+1)).inv (jointProfileMarked N old born q P)) R ∧
      IsGeoResolution (jointProfileMarked N old born q P) R ∧
      IsRetainedProductEquimultiple N old born q R ∧
      RestrictEmptyTower.CentresOver (canonicalProductMarked N old born q).cosupp R ∧
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head R k
        let A := geoTransformAlong (geometricTemplate N born) Q
        IsGeoTestTower (geometricTemplate N born) Q ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) Q ∧
        CurrentSharpCentres N (old ++ born) Q ∧
        RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) N (old ++ born)) Q ∧
        (∀ z ∈ A.N,∀ i : Fin old.length,ordinaryTraceOrder A.N
          (chronologicalMarked (retainedResidualMarked N old born i) Q).ideal z ≤
            ordinaryTraceOrder N (oldResidualPart N old born i) (Q.proj z)) ∧
        (∀ z,actualDistinctProperCount (fun i : Fin old.length =>
          (chronologicalMarked (retainedResidualMarked N old born i) Q).ideal) z ≤
            actualDistinctProperCount (oldResidualPart N old born) (Q.proj z)) ∧
        IsRetainedProductEquimultiple N old born q Q ∧
        IsGeoTestTower (canonicalProductMarked N old born q) Q ∧
        MarkedIdeal.RestrictEquiv (geoTransformAlong (canonicalProductMarked N old born q) Q)
          (retainedProductMarked N old born q Q) ∧
        (∀ i ∈ P,geoTransformAlong (canonicalFactorMarked N old born i) Q=retainedFactorMarked N old born Q i) ∧
        (∀ z ∈ A.N,ordinaryTraceOrder A.N (retainedProductMarked N old born q Q).ideal z=q →
          Q.proj z ∈ N ∧ ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal (Q.proj z)=q ∧
          actualDistinctProperCount (fun i : Fin old.length =>
            (chronologicalMarked (retainedResidualMarked N old born i) Q).ideal) z < q ∧
          (retainedInactiveRows N old born profile Q z).card ≤ P.card) ∧
        ∀ z ∈ A.N,retainedInactiveRows N old born profile Q z ⊆
          inactiveCanonicalRows N old born profile (Q.proj z)) ∧
      ∀ z ∈ (geoTransformAlong (geometricTemplate N born) R).N,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate N born) R).N
          (retainedProductMarked N old born q R).ideal z=q →
        ∃ i ∈ P,(retainedFactorMarked N old born R i).ideal.mem z 1 := by
  classical
  let M := jointProfileMarked N old born q P
  let R0 := canonicalProductMarked N old born q
  let L := P.toList.map (canonicalFactorMarked N old born)
  have hDom := (actual_retained_boundary_joint_step (Y := X) hn hN hE hTr hdense
    profile q hq hsum hOrd P hP hBound).1
  have h0 := retained_product_geometry hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial
  have hTail : ∀ B ∈ L,B.N=R0.N ∧ B.E=R0.E ∧ B.ideal.IsCoherent ∧ 1 ≤ B.d := by
    intro B hB
    obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hB
    exact ⟨rfl,rfl,(actual_old_parts_geometry hn hN hE hTr hdense i).2.2.2.2.1,le_rfl⟩
  have hSubset : M.cosupp ⊆ R0.cosupp := by
    intro x hx
    have hCos := (finiteSum_history R0 L hN h0.1 hq hTail (.refl : BlowupTower X X)).2 trivial |>.1
    change x ∈ (finiteSum R0 L).cosupp at hx
    rw [←geoTransformAlong_refl (finiteSum R0 L),hCos] at hx
    simp only [geoTransformAlong_refl] at hx
    exact hx R0 List.mem_cons_self
  have hMCompact : IsCompact M.cosupp := hCompact.of_isClosed_subset
    (GiraudAlong.isClosed_cosupport_along hDom.isWellFormed.isCoherent hDom.isWellFormed.isClosedSubmanifold_N _) hSubset
  obtain ⟨Z,R,hCanonical,hResolution⟩ :=
    HironakaOriginalCompactCosupportGlobalScheduler.exists_original_compact_cosupport_terminal_tower
      hn (n+1) M hDom hMCompact
  exact ⟨Z, R, hCanonical, hResolution,
    retained_boundary_joint_mask_terminal_readout hn hN hE hTr hdense profile q hq hsum
      hOrd hCount P hP hBound R hResolution⟩

end
end Hironaka.HironakaActualRetainedBoundaryMaskBlock
