import Hironaka.Resolution.HironakaActualGlobalDefectProfileFold

/-! Actual internally initialized Nat descent erases the TRUE chronological
multiplicity/shared-germ defect on ONE original global finite history.
Empty true defect is NOT asserted to imply prepared supports or full NC.
Source-first proof: `hironaka-actual-global-distinct-defect-exit-20261102.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualGlobalDistinctDefectExit
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  NormalCrossings RelativePrincipalizationSpan
  HironakaActualGlobalDefectProfileFold HironakaActualDefectProfileWindows
  HironakaG4CompactWholeMonomialMaskPhase HironakaG4SharpBadFootprint
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualFiniteMemberProduct HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder DivisorExponentAlong GermIdealOrder
variable {n : ℕ} {X Y Z V : CMfd.{u} n}

private def KeptEndpoint (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) (S : BlowupTower Y Z) : Prop :=
  IsGeoTestTower (geometricTemplate W []) (T.append S) ∧
  IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append S) ∧
  CurrentSharpCentres W E (T.append S) ∧
  (∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append S)).N,
    ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append S)).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append S)).ideal y ≤
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (S.proj y)) ∧
  chronologicalDistinctDefect W E (T.append S) ⊆ S.proj ⁻¹' chronologicalDistinctDefect W E T

private theorem keptEndpoint_refl {W : Set X} {E : List (Set X)} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) : KeptEndpoint W E T (.refl : BlowupTower Y Y) := by
  exact ⟨hT,hFull,hSharp,(fun _ _ _ => le_rfl),(fun _ h => h)⟩

private theorem keptEndpoint_append {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (T : BlowupTower X Y) (Q : BlowupTower Y Z) (R : BlowupTower Z V)
    (hQ : KeptEndpoint W E T Q) (hR : KeptEndpoint W E (T.append Q) R) :
    KeptEndpoint W E T (Q.append R) := by
  have hN : IsClosedSubmanifold n (geoTransformAlong (geometricTemplate W []) (T.append Q)).N :=
    (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      (𝔪 := geometricTemplate W []) hW IdealWeightPowers.isCoherent_unitIdeal (T.append Q) hQ.1).1
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [BlowupTower.append_assoc] using hR.1
  · simpa only [BlowupTower.append_assoc] using hR.2.1
  · simpa only [BlowupTower.append_assoc] using hR.2.2.1
  · intro y hy i
    have hyR : y ∈ (geoTransformAlong (geometricTemplate W []) ((T.append Q).append R)).N := by
      simpa only [BlowupTower.append_assoc] using hy
    have hyQ : R.proj y ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N := by
      apply MemberInterTowerAlong.strictAlong_subset_preimage R hN.1
      have hStrict := N_geoTransformAlong (geoTransformAlong (geometricTemplate W []) (T.append Q)) R
      rw [geoTransformAlong_append,hStrict] at hyR
      exact hyR
    have hh := (hR.2.2.2.1 y hyR i).trans (hQ.2.2.2.1 (R.proj y) hyQ i)
    simpa only [BlowupTower.append_assoc,BlowupTower.proj_append,Function.comp_apply] using hh
  · intro y hy
    have hyR : y ∈ chronologicalDistinctDefect W E ((T.append Q).append R) := by
      simpa only [BlowupTower.append_assoc] using hy
    have hh := hQ.2.2.2.2 (hR.2.2.2.2 hyR)
    simpa only [BlowupTower.proj_append,Set.mem_preimage,Function.comp_apply] using hh


private theorem product_order_positive_on_true_defect (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) {y : Y} (hy : y ∈ chronologicalDistinctDefect W E T) :
    1 ≤ ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) y := by
  rw [chronological_product_eq_actual_family_product]
  exact Nat.succ_le_of_lt ((Nat.zero_le _).trans_lt hy.2)

private theorem true_defect_exit_by_bound (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) (q : ℕ) :
    ∀ (Y₀ : CMfd.{u} n) (T : BlowupTower X Y₀),
      IsGeoTestTower (geometricTemplate W []) T →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T →
      CurrentSharpCentres W E T →
      (∀ x ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) x ≤ q) →
      ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y₀ Z),KeptEndpoint W E T Q ∧
        chronologicalDistinctDefect W E (T.append Q)=∅ := by
  induction q with
  | zero =>
    intro Y₀ T hT hFull hSharp hBound
    refine ⟨Y₀,BlowupTower.refl,keptEndpoint_refl T hT hFull hSharp,?_⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    change y ∈ chronologicalDistinctDefect W E T at hy
    have hPositive := product_order_positive_on_true_defect W E T hy
    have hUpper := hBound y hy
    omega
  | succ q ih =>
    intro Y₀ T hT hFull hSharp hBound
    obtain ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,hRowsQ,hFootQ,hExitQ⟩ :=
      exists_actual_global_original_fixed_q_exit hn hW hE hdense d hReg hK T hT hFull hSharp (q+1) hBound
    have hBoundQ : ∀ y ∈ chronologicalDistinctDefect W E (T.append Q),
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
          (chronologicalMemberProduct W E (T.append Q)) y ≤ q := by
      intro y hy
      exact Nat.le_of_lt_succ (hExitQ y hy)
    obtain ⟨V,R,hKeptR,hEmptyR⟩ := ih Z (T.append Q) hTQ hFullTQ hSharpTQ hBoundQ
    have hKeptQ : KeptEndpoint W E T Q := ⟨hTQ,hFullTQ,hSharpTQ,hRowsQ,hFootQ⟩
    refine ⟨V,Q.append R,keptEndpoint_append hW T Q R hKeptQ hKeptR,?_⟩
    simpa only [BlowupTower.append_assoc] using hEmptyR

/-- ORIGINAL geometry internally chooses the actual compact TRUE-defect
maximum, then constructs an actual finite SAME-original sharp history with
empty TRUE chronological distinct defect.  No numerical bound, terminal
tower, future comparison or desired prepared/NC state is supplied. -/
theorem exists_actual_global_original_distinct_defect_exit (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),
      IsGeoTestTower (geometricTemplate W []) (T.append Q) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) ∧
      CurrentSharpCentres W E (T.append Q) ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N,
        ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append Q)).ideal y ≤
            ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
              (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (Q.proj y)) ∧
      chronologicalDistinctDefect W E (T.append Q) ⊆ Q.proj ⁻¹' chronologicalDistinctDefect W E T ∧
      chronologicalDistinctDefect W E (T.append Q)=∅ := by
  classical
  have hExists : ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),KeptEndpoint W E T Q ∧
      chronologicalDistinctDefect W E (T.append Q)=∅ := by
    by_cases hne : (chronologicalDistinctDefect W E T).Nonempty
    · obtain ⟨q,_hq,_hAttain,hBound,_hCover,_hWindows⟩ :=
        exists_actual_distinct_defect_profile_windows hn hW hE hdense d hReg hK T hT hFull hSharp hne
      exact true_defect_exit_by_bound hn hW hE hdense d hReg hK q Y T hT hFull hSharp hBound
    · have hEmpty := Set.not_nonempty_iff_eq_empty.mp hne
      exact ⟨Y,BlowupTower.refl,keptEndpoint_refl T hT hFull hSharp,hEmpty⟩
  simpa only [KeptEndpoint,and_assoc] using hExists

end
end Hironaka.HironakaActualGlobalDistinctDefectExit
