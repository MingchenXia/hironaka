import Hironaka.Resolution.HironakaG4SmoothSubcarrierRecordedHistory
import Hironaka.Resolution.HironakaSharpActualPrincipalOrderOneTrace
import Hironaka.Resolution.HironakaSharpActualChronologicalDistinctDefect

/-! Current actual order-one reduction and the SAME original selected tail.
Source-first complete chapter: hironaka-g4-original-selected-residual-tail.tex.
No all-row preservation or original full-boundary tail test is inferred. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4OriginalSelectedResidualTail

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower NormalCrossings GermIdealOrder Hironaka.RegularLocusDense
  HironakaG4SmoothSubcarrierRecordedHistory HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalFirstMemberRelativeStrict
  HironakaSharpActualPrincipalOrderOneTrace HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualChronologicalDistinctDefect
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient DivisorExponentAlong
  IdealWeightPowers MarkedIdeals MarkedIdeals.MarkedIdeal

variable {n : ℕ} {X Y : CMfd.{u} n}


private theorem chronological_append (M : MarkedIdeal n X) (T : BlowupTower X Y) :
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),
      chronologicalMarked M (T.append R)=chronologicalMarked (chronologicalMarked M T) R
  | _,.refl => rfl
  | _,.step R C π hπ => by
    simp only [BlowupTower.append_step,chronologicalMarked]
    rw [chronological_append M T R]

theorem chronological_carrier_ideal_congr {M M' : MarkedIdeal n X}
    (hN : M.N=M'.N) (hI : M.ideal=M'.ideal) :
    ∀ {Q : CMfd.{u} n} (R : BlowupTower X Q),
      (chronologicalMarked M R).N=(chronologicalMarked M' R).N ∧
        (chronologicalMarked M R).ideal=(chronologicalMarked M' R).ideal
  | _,.refl => ⟨hN,hI⟩
  | _,.step R C π hπ => by
    obtain ⟨hRN,hRI⟩ := chronological_carrier_ideal_congr hN hI R
    constructor
    · change BlowupStrictSubmanifold.geoStrictTransform π C (chronologicalMarked M R).N=
        BlowupStrictSubmanifold.geoStrictTransform π C (chronologicalMarked M' R).N
      rw [hRN]
    · change nextRelativeStrict (chronologicalMarked M R).N (chronologicalMarked M R).ideal C π=
        nextRelativeStrict (chronologicalMarked M' R).N (chronologicalMarked M' R).ideal C π
      rw [hRN,hRI]

private theorem original_chronological_normal_inclusion (W H : Set X) :
    ∀ {Q : CMfd.{u} n} (T : BlowupTower X Q),
      (vanishingIdeal (n := n) (chronologicalMarked (originalRelativeMemberMarked W H) T).N).Le
        (chronologicalMarked (originalRelativeMemberMarked W H) T).ideal
  | _,.refl => vanishingIdeal_le_restrictOn
  | _,.step T C π hπ => by
    intro y g hg
    refine ⟨0,hg.1,fun a ha => ?_⟩
    change HolomorphicAt n a y at ha
    apply vanishingIdeal_le_restrictOn y (a*g)
    refine ⟨ha.mul hg.1,?_⟩
    filter_upwards [hg.2] with z hz hzN
    change a z*g z=0
    rw [hz hzN,mul_zero]


/-- A coherent reduced germ description on a closed support determines
the whole ideal, including the unit germs away from its support. -/
theorem coherent_ideal_eq_vanishingIdeal_of_local_reduced {Z : Set Y} {J : GermIdeal n Y}
    (hJ : J.IsCoherent) (hZ : IsClosed Z) (hSupp : J.zeroLocus ⊆ Z)
    (hPoint : ∀ y ∈ Z,∀ g,J.mem y g ↔ (vanishingIdeal (n := n) Z).mem y g) :
    J = vanishingIdeal (n := n) Z := by
  ext y g
  by_cases hy : y ∈ Z
  · exact hPoint y hy g
  · have hyZero : y ∉ J.zeroLocus := fun h => hy (hSupp h)
    have hUnitIff : ¬J.mem y 1 ↔ y ∈ J.zeroLocus := by
      simpa only [actualProperPositions,Finset.mem_filter,Finset.mem_univ,true_and] using
        (actual_proper_iff_zeroLocus (F := fun _ : Fin 1 => J) (fun _ => hJ) 0 y)
    have hUnit : J.mem y 1 := by
      by_contra hnot
      exact hyZero (hUnitIff.mp hnot)
    constructor
    · intro hg
      refine ⟨GermIdeal.IsCoherent.holomorphicAt_mem hJ hg,?_⟩
      filter_upwards [hZ.isOpen_compl.mem_nhds hy] with z hz hzZ
      exact False.elim (hz hzZ)
    · intro hg
      exact HomogenizedIdeal.mem_of_isInSpanAt hJ
        (isInSpanAt_of_eq_mul hUnit hg.1 hg.1 (Eventually.of_forall fun _ => by simp))

/-- A relative row with order at most one is exactly the vanishing
ideal of its closed smooth support. Normal germs are included in the
ambient row, so the equality also holds outside the carrier. -/
theorem actual_relative_row_globally_reduced {N : Set X} (hN : IsClosedSubmanifold n N)
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hnz : ∀ y ∈ N, IsNonzeroAlongAt N I y)
    (hpr : ∀ y ∈ N, ∃ f : X → ℂ, HolomorphicAt n f y ∧ ∀ g,
      I.mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (· = f) y g)
    (hnormal : (vanishingIdeal (n := n) N).Le I)
    (hOrd : ∀ y ∈ N, ordinaryTraceOrder N I y ≤ 1) :
    let Z := N ∩ I.zeroLocus
    IsClosedSubmanifold n Z ∧ I = vanishingIdeal (n := n) Z := by
  let Z := N ∩ I.zeroLocus
  have hZeroSub : I.zeroLocus ⊆ N := by
    intro y hy
    have hyN : y ∈ (vanishingIdeal (n := n) N).zeroLocus :=
      fun g hg => hy g (hnormal y g hg)
    rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hN.1] at hyN
  have hZclosed : IsClosed Z := hN.1.inter
    (CodimOneSupport.isComplexAnalyticSubset_zeroLocus hI).isClosed
  have hPoint (y : X) (hy : y ∈ Z) :
      (∀ g,I.mem y g ↔ (vanishingIdeal (n := n) Z).mem y g) ∧
      ∃ k,RegularAtDim (n := n) N y k ∧ RegularAtDim (n := n) Z y (k-1) := by
    have hhol := fun x g (hg : I.mem x g) =>
      GermIdeal.IsCoherent.holomorphicAt_mem hI hg
    have hcos : y ∈ cosupport n N I 1 := by
      rw [cosupport_one hhol]
      exact hy
    have hLower := (ordinaryTraceOrder_cosupport_iff hN
      hI hnz hy.1 1).mp hcos
    have hOne : ordinaryTraceOrder N I y=1 := (hOrd y hy.1).antisymm hLower
    obtain ⟨f,hf,hGen⟩ := hpr y hy.1
    obtain ⟨_,_,_,_,_,_,hRed,hDim⟩ := actual_orderOne_relative_reduced_trace hN hI hnz hy.1 f hf hGen hOne
    exact ⟨hRed,hDim⟩
  have hZsmooth : IsClosedSubmanifold n Z := by
    refine ⟨hZclosed,fun y hy => ?_⟩
    obtain ⟨k,_hNk,hZk⟩ := (hPoint y hy).2
    exact ⟨k-1,hZk⟩
  exact ⟨hZsmooth, coherent_ideal_eq_vanishingIdeal_of_local_reduced hI hZclosed
    (fun y hy => ⟨hZeroSub hy,hy⟩) (fun y hy => (hPoint y hy).1)⟩


private theorem actual_current_row_globally_reduced (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i : Fin E.length)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
    let Z := A.N ∩ A.ideal.zeroLocus
    IsClosedSubmanifold n Z ∧ A.ideal=vanishingIdeal (n := n) Z := by
  let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
  obtain ⟨_hAN,_hAE,_hMark,hwA,hnzA,hprA⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  exact actual_relative_row_globally_reduced hwA.isClosedSubmanifold_N A.ideal hwA.isCoherent hnzA hprA
    (original_chronological_normal_inclusion W (E.get i) T) hOrd

/-- True CURRENT order<=1 internally reduces the selected ORIGINAL row, then
ONE actual selected-carrier test tail tracks that SAME original whole ideal. -/
theorem actual_original_selected_residual_tail (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i : Fin E.length)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
    let Z := A.N ∩ A.ideal.zeroLocus
    IsClosedSubmanifold n Z ∧ A.ideal=vanishingIdeal (n := n) Z ∧
      ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),IsGeoTestTower (geometricTemplate Z []) R →
        IsClosedSubmanifold n (strictAlong R A.N) ∧ IsClosedSubmanifold n (strictAlong R Z) ∧
          strictAlong R Z ⊆ strictAlong R A.N ∧
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).N=strictAlong R A.N ∧
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal=
            vanishingIdeal (n := n) (strictAlong R Z) := by
  let M := originalRelativeMemberMarked W (E.get i)
  let A := chronologicalMarked M T
  let Z := A.N ∩ A.ideal.zeroLocus
  obtain ⟨_hAN,_hAE,_hMark,hwA,_hnzA,_hprA⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  obtain ⟨hZ,hWhole⟩ := actual_current_row_globally_reduced hn hW hE hdense i T hT hOrd
  refine ⟨hZ,hWhole,?_⟩
  intro Q R hR
  obtain ⟨hNR,hZR,hSub,hTailN,hTailI⟩ :=
    actual_recorded_smooth_subcarrier_dictionary hn hwA.isClosedSubmanifold_N hZ inter_subset_left R hR
  have hBase := actual_recorded_smooth_subcarrier_dictionary hn hwA.isClosedSubmanifold_N hZ
    inter_subset_left (.refl : BlowupTower Y Y) (by trivial)
  have hNorm : (originalRelativeMemberMarked A.N Z).ideal=vanishingIdeal (n := n) Z := hBase.2.2.2.2
  have hInitial : A.ideal=(originalRelativeMemberMarked A.N Z).ideal := hWhole.trans hNorm.symm
  have hCompare := chronological_carrier_ideal_congr
    (M := A) (M' := originalRelativeMemberMarked A.N Z) rfl hInitial R
  have hAppend := chronological_append M T R
  refine ⟨hNR,hZR,hSub,?_,?_⟩
  · rw [hAppend]
    exact hCompare.1.trans hTailN
  · rw [hAppend]
    exact hCompare.2.trans hTailI

end
end Hironaka.HironakaG4OriginalSelectedResidualTail


/-! Append-only public interface for the existing private chronological
composition proof. The whole previous source is retained; no new producer credit. -/
namespace Hironaka.HironakaG4OriginalSelectedResidualTail

open Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  HironakaSharpActualFiniteChronologicalHistory

variable {n : ℕ} {X Y : CMfd.{u} n}

theorem chronological_append_native (M : MarkedIdeal n X) (T : BlowupTower X Y) :
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),
      chronologicalMarked M (T.append R) = chronologicalMarked (chronologicalMarked M T) R :=
  chronological_append M T

end Hironaka.HironakaG4OriginalSelectedResidualTail
