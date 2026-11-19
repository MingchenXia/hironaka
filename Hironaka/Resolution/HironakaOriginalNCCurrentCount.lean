import Hironaka.Resolution.HironakaOriginalNCPhaseLex
import Hironaka.Resolution.HironakaOriginalOldBranchCountDrop

set_option autoImplicit false

/-!
# Actual current old-count geometry along a highest-stratum history

Universal original-branch history is derived from ordinary original testness
and actual centres in the highest stratum. Genuine whole-member-intersection
control bounds the current old count. Strict monotonicity proves the reverse
bound on the strict highest stratum. Outside that stratum the SAME tower is
empty and its actual projection preserves the intrinsic count.

Blueprint: hironaka-original-nc-all-prefix-phase-lex-extension.tex.
Source-only proof-body draft; no kernel-check claim.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCAllPrefixPhaseLex

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings GermIdealOrder CoefficientIdealRestriction
  HomogenizedGlueingTower MemberInterTowerAlong BoundaryCount RestrictEmptyTower
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsSNCBlockCarrier HironakaNormalCrossingsJointBranchCharts
  HironakaNormalCrossingsOldBlockSuperlevels HironakaNormalCrossingsGlobalPhaseCarrier
  HironakaOriginalOldBranchOpenHistory HironakaOriginalOldBranchCountDrop
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem count_congr {W : Type u} [TopologicalSpace W]
    [ChartedSpace (ComplexModel n) W] {H K : Set W}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hK : IsNormalCrossingsCarrier (n := n) K)
    (hEq : H = K) (x : W) : branchMultiplicity hH x = branchMultiplicity hK x := by
  subst K
  rfl

private theorem strict_list_union (T : BlowupTower X Y) (B : List (Set X)) :
    strictAlong T (⋃ A ∈ B, A) = ⋃ A ∈ B.map (strictAlong T), A := by
  have hcons {W : Type u} (A : Set W) (L : List (Set W)) :
      (⋃ C ∈ A :: L, C) = A ∪ (⋃ C ∈ L, C) := by ext x; simp
  induction B with
  | nil => simpa using StepOneEmptyPrefix.strictAlong_empty T
  | cons A B ih => rw [hcons, strictAlong_union, ih, List.map_cons, hcons]

private theorem centresOver_of_centresIn {S : Set X} (hS : IsClosed S) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresIn S T → CentresOver S T
  | _, .refl, _ => trivial
  | _, .step T _ _ _, hT =>
    ⟨centresOver_of_centresIn hS T hT.1,
      fun _ hp => strictAlong_subset_preimage T hS (hT.2 hp)⟩

private theorem highest_current_trace
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ)
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hBound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ, E, I, d⟩ : MarkedIdeal n X) T)
    (hHistory : IsOriginalBranchTestTower (⟨univ, E, I, d⟩ : MarkedIdeal n X) H T)
    {x : X} (hx : r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x) :
    let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
    let Z := {z | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) z}
    ∃ U : Opens X, x ∈ U ∧
      ∃ hc : IsBoundaryAdaptedCarrier (n := n)
        ((Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T H)
        ((geoTransformAlong M T).E.map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·)),
        (∀ p : openPreimage T U,
          branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) p ≤ r) ∧
        (∀ p : openPreimage T U, p.val ∈ strictAlong T Z →
          branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) p = r) ∧
        (∀ p : openPreimage T U,
          r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) p →
          p.val ∈ strictAlong T Z) := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let hH := isNormalCrossingsCarrier_of_boundaryAdapted h
  let Z := {z | r ≤ branchMultiplicity hH z}
  obtain ⟨U, B, hxU, hBE, hUnion, hContain⟩ := exists_highest_joint_branch_chart h hBound hx
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let IU := GermIdeal.pullback (m := n) (Subtype.val : U → X) I
  let MU : MarkedIdeal n U := ⟨univ, EU, IU, d⟩
  let TU := restrict U T
  have hIU : IU.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI
  have hMU : MU = MarkedIdeal.pullback (Subtype.val : U → X) M := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · simp only [MU, M, MarkedIdeal.pullback, preimage_univ]
    · rfl
    · rfl
    · rfl
  have hBT : IsGeoTestTower ({ MU with E := B ++ EU } : MarkedIdeal n U) TU := by
    exact (congrArg (fun K : MarkedIdeal n U =>
      IsGeoTestTower ({ K with E := B ++ K.E } : MarkedIdeal n U) TU) hMU).mpr
        (hHistory U B hBE hUnion)
  have hWF : ({ MU with E := B ++ EU } : MarkedIdeal n U).IsWellFormed :=
    ⟨isClosedSubmanifold_univ, hIU, hBE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hBE⟩
  have hCurrentSNC : IsSNCDivisor n
      (B.map (strictAlong TU) ++ (geoTransformAlong MU TU).E) := by
    rw [← entire_original_old_retained_boundary (X := CMfd.of (n := n) U) MU B TU]
    exact (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWF TU hBT).isSNCDivisor
  obtain ⟨hCB, hControl⟩ := exists_current_old_carrier_superlevel_control
    B EU hBE IU hIU d TU hBT
  let hInitial := isNormalCrossingsCarrier_of_boundaryAdapted
    (boundaryAdapted_union_of_snc_append B EU hBE)
  let hInitialTrace := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open U h)
  have hInitialCount (p : U) : branchMultiplicity hInitial p = branchMultiplicity hH p.val :=
    (count_congr hInitial hInitialTrace hUnion.symm p).trans
      (branchMultiplicity_open U hH hInitialTrace p)
  have hEmptyHigh : {p : U | r + 1 ≤ branchMultiplicity hInitial p} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    change r + 1 ≤ branchMultiplicity hInitial p at hp
    rw [hInitialCount] at hp
    have hb := hBound p.val
    omega
  have hCurrentBound (p : openPreimage T U) :
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hCB) p ≤ r := by
    by_contra hn
    have hHigh : r + 1 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hCB) p := by omega
    have hh := hControl (r + 1) hHigh
    rw [hEmptyHigh, StepOneEmptyPrefix.strictAlong_empty] at hh
    exact hh
  have hCurrentHigh (p : openPreimage T U)
      (hp : r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hCB) p) :
      p.val ∈ strictAlong T Z := by
    have hCut : {q : U | r ≤ branchMultiplicity hInitial q} =
        (Subtype.val : U → X) ⁻¹' Z := by
      ext q
      change (r ≤ branchMultiplicity hInitial q) ↔ r ≤ branchMultiplicity hH q.val
      rw [hInitialCount]
    have hh := hControl r hp
    rw [hCut, strictAlong_restrict] at hh
    exact hh
  have hCurrentTop (p : openPreimage T U) (hp : p.val ∈ strictAlong T Z) :
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hCB) p = r := by
    have hpZ : p ∈ strictAlong TU ((Subtype.val : U → X) ⁻¹' Z) := by
      rw [strictAlong_restrict]
      exact hp
    have hAll : ∀ D ∈ B, p ∈ strictAlong TU D := fun D hD =>
      strictAlong_mono TU (hContain D hD) hpZ
    have hLength : branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hCB) p = B.length := by
      have hLiteralCount : branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hCB) p =
          boundaryCount (B.map (strictAlong TU)) p :=
        (branchMultiplicity_union_eq_count (B.map (strictAlong TU))
          (geoTransformAlong MU TU).E hCurrentSNC p).1
      rw [hLiteralCount, boundaryCount_map]
      have hFilter : Finset.univ.filter
          (fun i : Fin B.length => p ∈ strictAlong TU (B.get i)) = Finset.univ := by
        apply Finset.filter_eq_self.mpr
        intro i _hi
        exact hAll _ (List.get_mem B i)
      rw [hFilter, Finset.card_fin]
    let p0 : U := ⟨x, hxU⟩
    have hInitialLength := (branchMultiplicity_union_eq_count B EU hBE p0).2
    have hxCount : branchMultiplicity hH x = r := le_antisymm (hBound x) hx
    rw [hInitialCount, hxCount] at hInitialLength
    exact le_antisymm (hCurrentBound p) (hInitialLength.trans_eq hLength.symm)
  have hSet : (⋃ D ∈ B.map (strictAlong TU), D) =
      (Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T H := by
    rw [← strict_list_union, ← hUnion, strictAlong_restrict]
  have hE : (geoTransformAlong MU TU).E =
      (geoTransformAlong M T).E.map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·) := by
    rw [hMU, geoTransformAlong_restrict U isClosedSubmanifold_univ hI T hT]
    rfl
  have hc : IsBoundaryAdaptedCarrier (n := n)
      ((Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T H)
      ((geoTransformAlong M T).E.map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·)) := by
    rw [← hSet, ← hE]
    exact hCB
  have hCount (p : openPreimage T U) :
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) p =
        branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hCB) p :=
    count_congr _ _ hSet.symm p
  exact ⟨U, hxU, hc, fun p => (hCount p).trans_le (hCurrentBound p),
    (fun p hp => (hCount p).trans (hCurrentTop p hp)),
    fun p hp => hCurrentHigh p (hp.trans_eq (hCount p))⟩

/-- Actual M-testness and centres in the highest old stratum produce GLOBAL
current adapted geometry, the global count bound, and count=r on strict Z. -/
theorem exists_highest_history_current_pair_high_locus
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ)
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ, E, I, d⟩ : MarkedIdeal n X) T)
    (hTZ : CentresIn
      {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} T) :
    ∃ hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong T H)
        (geoTransformAlong (⟨univ, E, I, d⟩ : MarkedIdeal n X) T).E,
      (∀ y : Y, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y ≤ r) ∧
      (∀ y ∈ strictAlong T
        {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x},
        branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y = r) ∧
      {y | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y} =
        strictAlong T
          {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} := by
  classical
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let hH := isNormalCrossingsCarrier_of_boundaryAdapted h
  let Z := {x | r ≤ branchMultiplicity hH x}
  have hZ : IsClosed Z := isClosed_branchMultiplicity_superlevel hH r
  have hHistory := isOriginalBranchTestTower_of_centresIn_highest_stratum
    I hI d h hr hBound T hT hTZ
  have hWF : M.IsWellFormed := ⟨isClosedSubmanifold_univ, hI,
    isSNCDivisor_of_boundaryAdapted h,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor
      (isSNCDivisor_of_boundaryAdapted h)⟩
  have hCurrentWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWF T hT
  have hTraces : ∀ y : Y, ∃ V : Opens Y, y ∈ V ∧
      ∃ hc : IsBoundaryAdaptedCarrier (n := n)
        ((Subtype.val : V → Y) ⁻¹' strictAlong T H)
        ((geoTransformAlong M T).E.map ((Subtype.val : V → Y) ⁻¹' ·)),
        (∀ p : V, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) p ≤ r) ∧
        (∀ p : V, p.val ∈ strictAlong T Z →
          branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) p = r) ∧
        (∀ p : V, r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) p →
          p.val ∈ strictAlong T Z) := by
    intro y
    by_cases hy : T.proj y ∈ Z
    · obtain ⟨U, hyU, hc, hb, ht, hh⟩ :=
        highest_current_trace I hI d h hBound T hT hHistory hy
      exact ⟨openPreimage T U, hyU, hc, hb, ht, hh⟩
    · let U : Opens X := ⟨Zᶜ, hZ.isOpen_compl⟩
      let V := openPreimage T U
      have hEmpty : IsEmptyTower (restrict U T) :=
        isEmptyTower_restrict_of_centresOver U disjoint_compl_left T
          (centresOver_of_centresIn hZ T hTZ)
      let hInitial := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open U h)
      have hRaw := boundaryAdapted_empty_tower
        (MarkedIdeal.pullback (Subtype.val : U → X) M) (boundaryAdapted_open U h)
        (restrict U T) hEmpty
      have hc : IsBoundaryAdaptedCarrier (n := n)
          ((Subtype.val : V → Y) ⁻¹' strictAlong T H)
          ((geoTransformAlong M T).E.map ((Subtype.val : V → Y) ⁻¹' ·)) := by
        rw [strictAlong_restrict, geoTransformAlong_restrict U isClosedSubmanifold_univ hI T hT]
          at hRaw
        exact hRaw
      have hCount (p : V) :
          branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) p =
            branchMultiplicity hH (T.proj p.val) := by
        calc
          _ = branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hRaw) p :=
            count_congr _ _ (strictAlong_restrict U T H).symm p
          _ = branchMultiplicity hInitial ((restrict U T).proj p) :=
            branchMultiplicity_empty_tower hInitial (restrict U T) hEmpty
              (isNormalCrossingsCarrier_of_boundaryAdapted hRaw) p
          _ = branchMultiplicity hH (((restrict U T).proj p).val) :=
            branchMultiplicity_open U hH hInitial _
          _ = branchMultiplicity hH (T.proj p.val) := by rw [proj_restrict]
      refine ⟨V, hy, hc, fun p => (hCount p).trans_le (hBound _), ?_, ?_⟩
      · intro p hp
        exact False.elim (p.property (strictAlong_subset_preimage T hZ hp))
      · intro p hp
        exact False.elim (p.property (hp.trans_eq (hCount p)))
  have hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E :=
    boundaryAdapted_of_open_traces (isClosed_strictAlong T h.1) hCurrentWF.isSNCDivisor.1
      (fun y => by
        obtain ⟨V, hyV, hp, _hb, _ht, _hh⟩ := hTraces y
        exact ⟨V, hyV, hp⟩)
  have hUpper : ∀ y : Y,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y ≤ r := by
    intro y
    obtain ⟨V, hyV, hp, hb, _ht, _hh⟩ := hTraces y
    exact (branchMultiplicity_open V (isNormalCrossingsCarrier_of_boundaryAdapted hc)
      (isNormalCrossingsCarrier_of_boundaryAdapted hp) ⟨y, hyV⟩).symm.trans_le (hb ⟨y, hyV⟩)
  have hTop : ∀ y ∈ strictAlong T Z,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y = r := by
    intro y hy
    obtain ⟨V, hyV, hp, _hb, ht, _hh⟩ := hTraces y
    exact (branchMultiplicity_open V (isNormalCrossingsCarrier_of_boundaryAdapted hc)
      (isNormalCrossingsCarrier_of_boundaryAdapted hp) ⟨y, hyV⟩).symm.trans (ht ⟨y, hyV⟩ hy)
  refine ⟨hc, hUpper, hTop, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨V, hyV, hp, _hb, _ht, hh⟩ := hTraces y
    have he := branchMultiplicity_open V (isNormalCrossingsCarrier_of_boundaryAdapted hc)
      (isNormalCrossingsCarrier_of_boundaryAdapted hp) ⟨y, hyV⟩
    exact hh ⟨y, hyV⟩ (hy.trans_eq he.symm)
  · intro hy
    exact (hTop y hy).ge

/-- Compatibility count interface; every assertion still comes from the
stronger actual high-locus producer, with no caller current-count certificate. -/
theorem exists_highest_history_current_pair_counts
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ)
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ, E, I, d⟩ : MarkedIdeal n X) T)
    (hTZ : CentresIn
      {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} T) :
    ∃ hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong T H)
        (geoTransformAlong (⟨univ, E, I, d⟩ : MarkedIdeal n X) T).E,
      (∀ y : Y, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y ≤ r) ∧
      (∀ y ∈ strictAlong T
        {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x},
        branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y = r) := by
  obtain ⟨hc, hb, ht, _hh⟩ :=
    exists_highest_history_current_pair_high_locus I hI d h hr hBound T hT hTZ
  exact ⟨hc, hb, ht⟩

end
end Hironaka.HironakaOriginalNCAllPrefixPhaseLex

