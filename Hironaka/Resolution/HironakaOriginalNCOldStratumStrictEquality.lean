import Hironaka.Resolution.HironakaOriginalNCCountHistoryGeometry

set_option autoImplicit false

/-!
# Pure old-stratum geometry on the SAME native test history

The geometry-only record (univ,E,unitIdeal,0) inherits the SAME actual test
tower and ALL original branch histories. It does not replace the native
marked ideal or supply a positive-mark invariant domain. Whole finite-index
intersection identities then give BOTH directions of the old-stratum
dictionary, for every count, without a global finite branch enumeration.

The final highest-stratum wrapper derives closed smoothness from an INITIAL
bound and also derives the current bound; it assumes no desired current
count or stratum certificate. A future natural new-value joint interpreter
must internally produce its ordinary test and original branch histories.

Blueprint support: hironaka-original-nc-old-stratum-strict-equality-support.tex.
Initial full source-only draft. No Lean execution, node or binding credit.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCOldStratumStrictEquality

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealEquivalence
  GermIdealOrder GermIdealPullbackCalculus IdealWeightPowers
  NormalCrossings HomogenizedGlueingTower MemberInterTowerAlong BoundaryCount
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsSNCBlockCarrier HironakaOriginalOldBranchOpenHistory
  HironakaOriginalNCCountHistory

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- This independent unit ideal is used ONLY for ambient branch geometry.
The positive-mark native datum M is never replaced in a lower invariant. -/
def boundaryGeometry (E : List (Set X)) : MarkedIdeal n X :=
  ⟨univ, E, unitIdeal n X, 0⟩

private theorem current_carrier_univ (D : MarkedIdeal n X) (hN : D.N = univ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), (geoTransformAlong D T).N = univ
  | _, .refl => hN
  | _, .step T _C _π hπ => geoTransform_N_eq_univ (current_carrier_univ D hN T) hπ

/- The only centre fields needed by the geometry-only record are the actual
closed smooth centre and its normal crossings with the SAME whole E. -/
private theorem mark_zero_test_of_same_boundary
    (M D : MarkedIdeal n X) (hD : D.IsWellFormed)
    (hN : D.N = univ) (hd : D.d = 0) (hE : D.E = M.E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower M T → IsGeoTestTower D T
  | _, .refl, _hT => trivial
  | _, .step T C π hπ, hT => by
      have hDT := mark_zero_test_of_same_boundary M D hD hN hd hE T hT.1
      have hCurrent := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hD T hDT
      have hCos : (geoTransformAlong D T).cosupp = univ := by
        change cosupport n (geoTransformAlong D T).N (geoTransformAlong D T).ideal
          (geoTransformAlong D T).d = univ
        rw [d_geoTransformAlong, hd,
          cosupport_zero (fun x g hg =>
            RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hCurrent.isCoherent hg)]
        exact current_carrier_univ D hN T
      refine ⟨hDT, hT.2.1, ?_, ?_⟩
      · rw [hCos]
        exact subset_univ C
      · rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hE T]
        exact hT.2.2.2

/-- SAME actual tower, centre maps, chronological years and whole ordered
boundary. No native ideal or carrier field enters the dummy geometry ideal. -/
theorem boundaryGeometry_test (M : MarkedIdeal n X) (hE : IsSNCDivisor n M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    IsGeoTestTower (boundaryGeometry M.E) T := by
  have hD : (boundaryGeometry (X := X) M.E).IsWellFormed :=
    ⟨isClosedSubmanifold_univ, isCoherent_unitIdeal, hE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  exact mark_zero_test_of_same_boundary M (boundaryGeometry M.E) hD rfl rfl rfl T hT

/-- EVERY original local augmented history is preserved on the SAME literal
tower. No single global branch presentation is assumed or selected. -/
theorem boundaryGeometry_original_history (M : MarkedIdeal n X) (H : Set X)
    (T : BlowupTower X Y) (hHistory : IsOriginalBranchTestTower M H T) :
    IsOriginalBranchTestTower (boundaryGeometry M.E) H T := by
  intro U B hSNC hUnion
  let DU := MarkedIdeal.pullback (Subtype.val : U → X) (boundaryGeometry M.E)
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  let DB : MarkedIdeal n U := { DU with E := B ++ DU.E }
  let MB : MarkedIdeal n U := { MU with E := B ++ MU.E }
  have hDBN : DB.N = univ := by
    change (Subtype.val : U → X) ⁻¹' (univ : Set X) = univ
    exact preimage_univ
  have hDBI : DB.ideal.IsCoherent :=
    isCoherent_pullback contMDiff_subtype_val isCoherent_unitIdeal
  have hDB : DB.IsWellFormed := by
    refine ⟨?_, hDBI, hSNC, ?_⟩
    · rw [hDBN]
      exact isClosedSubmanifold_univ
    · rw [hDBN]
      exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hSNC
  have hMB : IsGeoTestTower MB (restrict U T) := hHistory U B hSNC hUnion
  exact mark_zero_test_of_same_boundary (X := CMfd.of (n := n) U)
    MB DB hDB hDBN rfl rfl (restrict U T) hMB

private theorem strictAlong_finset_union {ι : Type*}
    (T : BlowupTower X Y) (s : Finset ι) (F : ι → Set X) :
    strictAlong T (⋃ i ∈ s, F i) = ⋃ i ∈ s, strictAlong T (F i) := by
  induction s using Finset.induction_on with
  | empty => simpa using StepOneEmptyPrefix.strictAlong_empty T
  | @insert i s hi ih =>
      have hLeft : (⋃ j ∈ insert i s, F j) = F i ∪ ⋃ j ∈ s, F j := by
        ext x
        simp
      have hRight : (⋃ j ∈ insert i s, strictAlong T (F j)) =
          strictAlong T (F i) ∪ ⋃ j ∈ s, strictAlong T (F j) := by
        ext y
        simp
      calc
        strictAlong T (⋃ j ∈ insert i s, F j) = strictAlong T (F i ∪ ⋃ j ∈ s, F j) :=
          congrArg (strictAlong T) hLeft
        _ = strictAlong T (F i) ∪ strictAlong T (⋃ j ∈ s, F j) := strictAlong_union T _ _
        _ = strictAlong T (F i) ∪ ⋃ j ∈ s, strictAlong T (F j) :=
          congrArg (fun A => strictAlong T (F i) ∪ A) ih
        _ = ⋃ j ∈ insert i s, strictAlong T (F j) := hRight.symm

/- ALL subsets are used. The empty subset gives q=0 correctly, and empty
member slots retain their literal indices without creating through-members. -/
private theorem indexed_superlevel_eq_union {A : Type*} {m : ℕ}
    (F : Fin m → Set A) (q : ℕ) :
    {x | q ≤ (Finset.univ.filter (fun i : Fin m => x ∈ F i)).card} =
      ⋃ S ∈ (Finset.univ.filter (fun S : Finset (Fin m) => q ≤ S.card)),
        {x | ∀ i ∈ S, x ∈ F i} := by
  ext x
  constructor
  · intro hx
    let S := Finset.univ.filter (fun i : Fin m => x ∈ F i)
    have hS : S ∈ Finset.univ.filter (fun K : Finset (Fin m) => q ≤ K.card) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    exact mem_iUnion.mpr ⟨S, mem_iUnion.mpr ⟨hS,
      fun i hi => (Finset.mem_filter.mp hi).2⟩⟩
  · intro hx
    obtain ⟨S, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hS, hx⟩ := mem_iUnion.mp hx
    have hSub : S ⊆ Finset.univ.filter (fun i : Fin m => x ∈ F i) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx i hi⟩
    exact (Finset.mem_filter.mp hS).2.trans (Finset.card_le_card hSub)

/- The genuine original member-intersection theorem is applied to the old
INITIAL indices in B++E. Nothing is dropped from the actual tower boundary. -/
private theorem strict_old_memberInter
    (B E : List (Set X)) (hBE : IsSNCDivisor n (B ++ E))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ, B ++ E, unitIdeal n X, 0⟩ : MarkedIdeal n X) T)
    (S : Finset (Fin B.length)) :
    strictAlong T (memberInter B S) = {y | ∀ i ∈ S, y ∈ strictAlong T (B.get i)} := by
  let MB : MarkedIdeal n X := ⟨univ, B ++ E, unitIdeal n X, 0⟩
  have hMB : MB.IsWellFormed :=
    ⟨isClosedSubmanifold_univ, isCoherent_unitIdeal, hBE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hBE⟩
  let old : Fin B.length ↪ Fin MB.E.length := Fin.castLEEmb (by
    change B.length ≤ (B ++ E).length
    rw [List.length_append]
    omega)
  have hGet (i : Fin B.length) : MB.E.get (old i) = B.get i := by
    change (B ++ E).get ⟨i.val, _⟩ = B.get i
    simp [List.get_eq_getElem]
  have hSource : MB.N ∩ memberInter MB.E (S.map old) = memberInter B S := by
    ext x
    constructor
    · intro hx i hi
      have hh := hx.2 (old i) (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
      rw [hGet] at hh
      exact hh
    · intro hx
      refine ⟨mem_univ _, ?_⟩
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
      rw [hGet]
      exact hx i hi
  have hTarget : (geoTransformAlong MB T).N ∩
      {y | ∀ j ∈ S.map old, y ∈ strictAlong T (MB.E.get j)} =
      {y | ∀ i ∈ S, y ∈ strictAlong T (B.get i)} := by
    rw [current_carrier_univ MB rfl T]
    ext y
    constructor
    · intro hy i hi
      have hh := hy.2 (old i) (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
      rw [hGet] at hh
      exact hh
    · intro hy
      refine ⟨mem_univ _, ?_⟩
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
      rw [hGet]
      exact hy i hi
  have hExact := strictAlong_inter_memberInter MB hMB (S.map old) T hT
  rw [hSource, hTarget] at hExact
  exact hExact

private theorem local_old_superlevel_eq_strict
    (B E : List (Set X)) (hBE : IsSNCDivisor n (B ++ E))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ, B ++ E, unitIdeal n X, 0⟩ : MarkedIdeal n X) T)
    (q : ℕ) :
    strictAlong T {x | q ≤ boundaryCount B x} =
      {y | q ≤ boundaryCount (B.map (strictAlong T)) y} := by
  let s := Finset.univ.filter (fun S : Finset (Fin B.length) => q ≤ S.card)
  have hInitial : {x | q ≤ boundaryCount B x} = ⋃ S ∈ s, memberInter B S :=
    indexed_superlevel_eq_union (fun i : Fin B.length => B.get i) q
  have hCurrent : {y | q ≤ (Finset.univ.filter
      (fun i : Fin B.length => y ∈ strictAlong T (B.get i))).card} =
      ⋃ S ∈ s, {y | ∀ i ∈ S, y ∈ strictAlong T (B.get i)} :=
    indexed_superlevel_eq_union (fun i : Fin B.length => strictAlong T (B.get i)) q
  have hMap : {y | q ≤ boundaryCount (B.map (strictAlong T)) y} =
      {y | q ≤ (Finset.univ.filter (fun i : Fin B.length => y ∈ strictAlong T (B.get i))).card} := by
    ext y
    change (q ≤ boundaryCount (B.map (strictAlong T)) y) ↔
      q ≤ (Finset.univ.filter (fun i : Fin B.length => y ∈ strictAlong T (B.get i))).card
    rw [boundaryCount_map]
  calc
    strictAlong T {x | q ≤ boundaryCount B x} = strictAlong T (⋃ S ∈ s, memberInter B S) :=
      congrArg (strictAlong T) hInitial
    _ = ⋃ S ∈ s, strictAlong T (memberInter B S) := strictAlong_finset_union T s _
    _ = ⋃ S ∈ s, {y | ∀ i ∈ S, y ∈ strictAlong T (B.get i)} := by
      apply congrArg (fun F : Finset (Fin B.length) → Set Y => ⋃ S ∈ s, F S)
      funext S
      exact strict_old_memberInter B E hBE T hT S
    _ = {y | q ≤ (Finset.univ.filter
        (fun i : Fin B.length => y ∈ strictAlong T (B.get i))).card} := hCurrent.symm
    _ = {y | q ≤ boundaryCount (B.map (strictAlong T)) y} := hMap.symm

/-- BOTH directions for EVERY intrinsic old stratum, on the whole ambient
space. Native N/ideal are unrestricted; current NC geometry is an output. -/
theorem current_old_strata_eq_strict (M : MarkedIdeal n X)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) :
    IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E ∧
      ∀ q : ℕ,
        strictAlong T {x | q ≤ oldCount H (BlowupTower.refl : BlowupTower X X) x} =
          {y | q ≤ oldCount H T y} := by
  let D := boundaryGeometry (X := X) M.E
  have hDI : D.ideal.IsCoherent := isCoherent_unitIdeal
  have hDT : IsGeoTestTower D T := boundaryGeometry_test M (isSNCDivisor_of_boundaryAdapted h) T hT
  have hDH : IsOriginalBranchTestTower D H T := boundaryGeometry_original_history M H T hHistory
  have hPairD := exists_current_pair_of_original_branch_history D rfl hDI h T hDT hDH
  have hE : (geoTransformAlong D T).E = (geoTransformAlong M T).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := D) (𝔫 := M) rfl T
  refine ⟨hE ▸ hPairD, ?_⟩
  intro q
  let Z := {x : X | q ≤ oldCount H (BlowupTower.refl : BlowupTower X X) x}
  ext y
  obtain ⟨U, B, hxU, hSNC, hUnion⟩ := exists_original_joint_branch_chart h (T.proj y)
  let TU := restrict U T
  let p : openPreimage T U := ⟨y, hxU⟩
  let EU := (MarkedIdeal.pullback (Subtype.val : U → X) D).E
  let IU := GermIdeal.pullback (m := n) (Subtype.val : U → X) (unitIdeal n X)
  have hInitial (x : U) : oldCount H (BlowupTower.refl : BlowupTower X X) x.val =
      boundaryCount B x := by
    have hh := oldCount_eq_boundaryCount_chart D rfl hDI h
      (BlowupTower.refl : BlowupTower X X) trivial (fun _ _ _ _ => trivial) U B hSNC hUnion x
    change oldCount H (BlowupTower.refl : BlowupTower X X) x.val =
      boundaryCount (B.map id) x at hh
    simpa only [List.map_id] using hh
  have hCurrent : oldCount H T y = boundaryCount (B.map (strictAlong TU)) p :=
    oldCount_eq_boundaryCount_chart D rfl hDI h T hDT hDH U B hSNC hUnion p
  have hDU : IsGeoTestTower (⟨univ, B ++ EU, IU, 0⟩ : MarkedIdeal n U) TU := by
    have hh := hDH U B hSNC hUnion
    have hRecord :
        ({ MarkedIdeal.pullback (Subtype.val : U → X) D with
          E := B ++ (MarkedIdeal.pullback (Subtype.val : U → X) D).E } : MarkedIdeal n U) =
          ⟨univ, B ++ EU, IU, 0⟩ := by
      apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      · exact preimage_univ
      · rfl
      · rfl
      · rfl
    rw [hRecord] at hh
    exact hh
  have hLocalTest : IsGeoTestTower
      (⟨univ, B ++ EU, unitIdeal n U, 0⟩ : MarkedIdeal n U) TU := by
    let R : MarkedIdeal n U := ⟨univ, B ++ EU, unitIdeal n U, 0⟩
    have hR : R.IsWellFormed := ⟨isClosedSubmanifold_univ, isCoherent_unitIdeal,
      hSNC, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hSNC⟩
    exact mark_zero_test_of_same_boundary (X := CMfd.of (n := n) U)
      (⟨univ, B ++ EU, IU, 0⟩ : MarkedIdeal n U) R hR rfl rfl rfl TU hDU
  have hTrace : (Subtype.val : U → X) ⁻¹' Z = {x : U | q ≤ boundaryCount B x} := by
    ext x
    change (q ≤ oldCount H (BlowupTower.refl : BlowupTower X X) x.val) ↔ q ≤ boundaryCount B x
    rw [hInitial x]
  have hLocal := local_old_superlevel_eq_strict (X := CMfd.of (n := n) U) B EU hSNC TU hLocalTest q
  change y ∈ strictAlong T Z ↔ q ≤ oldCount H T y
  calc
    y ∈ strictAlong T Z ↔ p ∈ strictAlong TU ((Subtype.val : U → X) ⁻¹' Z) := by
      rw [strictAlong_restrict]
      rfl
    _ ↔ p ∈ strictAlong TU {x : U | q ≤ boundaryCount B x} := by rw [hTrace]
    _ ↔ q ≤ boundaryCount (B.map (strictAlong TU)) p := by
      rw [hLocal]
      rfl
    _ ↔ q ≤ oldCount H T y := by rw [hCurrent]

/-- INITIAL highest-count bound internally gives the smooth ambient source
stratum, WHOLE strict/current equality and the actual current count bound. -/
theorem highest_old_stratum_geometry (M : MarkedIdeal n X)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) {q : ℕ}
    (hBound : ∀ x : X, oldCount H (BlowupTower.refl : BlowupTower X X) x ≤ q) :
    let Z := {x : X | q ≤ oldCount H (BlowupTower.refl : BlowupTower X X) x}
    IsClosedSubmanifold n Z ∧
      IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E ∧
      {y | q ≤ oldCount H T y} = strictAlong T Z ∧
      ∀ y : Y, oldCount H T y ≤ q := by
  dsimp only
  obtain ⟨hCurrent, hEq⟩ := current_old_strata_eq_strict M h T hT hHistory
  let hH := isNormalCrossingsCarrier_of_boundaryAdapted h
  have hOld (x : X) : oldCount H (BlowupTower.refl : BlowupTower X X) x = branchMultiplicity hH x :=
    oldCount_eq (BlowupTower.refl : BlowupTower X X) hH x
  have hBound' : ∀ x : X, branchMultiplicity hH x ≤ q :=
    fun x => (hOld x).symm.trans_le (hBound x)
  have hZ : {x : X | q ≤ oldCount H (BlowupTower.refl : BlowupTower X X) x} =
      {x : X | q ≤ branchMultiplicity hH x} := by
    ext x
    change (q ≤ oldCount H (BlowupTower.refl : BlowupTower X X) x) ↔ q ≤ branchMultiplicity hH x
    rw [hOld x]
  have hSmooth : IsClosedSubmanifold n
      {x : X | q ≤ oldCount H (BlowupTower.refl : BlowupTower X X) x} := by
    rw [hZ]
    exact isClosedSubmanifold_highest_superlevel hH hBound'
  refine ⟨hSmooth, hCurrent, (hEq q).symm, ?_⟩
  have hEmpty : {x : X | q + 1 ≤ oldCount H (BlowupTower.refl : BlowupTower X X) x} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hh := hBound x
    change q + 1 ≤ oldCount H (BlowupTower.refl : BlowupTower X X) x at hx
    omega
  have hCurrentEmpty := hEq (q + 1)
  rw [hEmpty, StepOneEmptyPrefix.strictAlong_empty] at hCurrentEmpty
  intro y
  by_contra hn
  have hy : y ∈ {y | q + 1 ≤ oldCount H T y} := by
    change q + 1 ≤ oldCount H T y
    omega
  rw [← hCurrentEmpty] at hy
  exact hy

end
end Hironaka.HironakaOriginalNCOldStratumStrictEquality
