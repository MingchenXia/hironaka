import Hironaka.Resolution.HironakaG8PowerLowerGeometry
import Hironaka.Invariant.MemberRestrictAdmissible
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8MemberWeakEquiv
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealEquivalence.MarkedIdeal ResolutionInvariantSpec
  InvDomainMemberRestriction InvDomainRebase CoefficientIdealRestriction HomogenizedGlueingTower CoefficientIdealAlongRestrictionDrop
  MemberRestrictAdmissible

/-- Controlled tests of a native member restriction are precisely tests of
the original record whose centres stay in the restricted carrier. -/
theorem memberRestrict_test_dictionary {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hd : 1 ≤ M.d)
    (I : Finset (Fin M.E.length)) (T : BlowupTower X Y) :
    (IsGeoTestTower (memberRestrict M I) T ↔
      IsGeoTestTower M T ∧ CentresIn (memberRestrict M I).N T) ∧
    (IsGeoTestTower (memberRestrict M I) T →
      (geoTransformAlong (memberRestrict M I) T).cosupp =
        (geoTransformAlong M T).cosupp ∩ strictAlong T (memberRestrict M I).N) := by
  have hS := (isWellFormed_memberRestrict hn hM I).isClosedSubmanifold_N
  have hsub : ∀ H ∈ (memberRestrict M I).E, H ∈ M.E := by
    intro H hH
    rw [memberRestrict_E] at hH
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hH
    exact List.get_mem _ _
  have hdel : ∀ H ∈ M.E, H ∉ (memberRestrict M I).E → (memberRestrict M I).N ⊆ H := by
    intro H hH hH' x hx
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    by_cases hi : i ∈ I
    · exact hx.2 i hi
    · exfalso
      apply hH'
      rw [memberRestrict_E]
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true hi⟩)
  exact coeffAlong_restrict_withE_iff M hM hd hS inter_subset_left hsub hdel T

/-- Weakly equivalent same-carrier records induce weakly equivalent member
restrictions for the same selected literal original boundary members. -/
theorem memberRestrict_membersThrough_wEquiv {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {A B : MarkedIdeal n X} (hA : A.IsWellFormed) (hB : B.IsWellFormed)
    (hdA : 1 ≤ A.d) (hdB : 1 ≤ B.d) (hN : A.N = B.N) (hE : A.E = B.E)
    (hW : WEquiv A B) (E₀ : List (Set X)) (x : X) :
    WEquiv (memberRestrict A (membersThrough A.E E₀ x))
      (memberRestrict B (membersThrough B.E E₀ x)) := by
  let P := memberRestrict A (membersThrough A.E E₀ x)
  let Q := memberRestrict B (membersThrough B.E E₀ x)
  have hPN : P.N = Q.N := by
    simp only [P,Q,memberRestrict_membersThrough_N,hN,hE]
  have hPE : P.E = Q.E := by
    simp only [P,Q,memberRestrict_membersThrough_E,hE]
  refine ⟨hPE,fun T => ⟨?_,?_⟩⟩
  · have hPA := (memberRestrict_test_dictionary hn A hA hdA (membersThrough A.E E₀ x) T).1
    have hQB := (memberRestrict_test_dictionary hn B hB hdB (membersThrough B.E E₀ x) T).1
    rw [hPA,hQB,hPN]
    exact and_congr_left fun _ => (hW.2 T).1
  · intro hT
    have hPA := (memberRestrict_test_dictionary hn A hA hdA (membersThrough A.E E₀ x) T).1.mp hT
    have hQB := (memberRestrict_test_dictionary hn B hB hdB (membersThrough B.E E₀ x) T).1.mpr ⟨(hW.2 T).1.mp hPA.1,hPN ▸ hPA.2⟩
    rw [(memberRestrict_test_dictionary hn A hA hdA (membersThrough A.E E₀ x) T).2 hT,
      (memberRestrict_test_dictionary hn B hB hdB (membersThrough B.E E₀ x) T).2 hQB,
      (hW.2 T).2 hPA.1,hPN]

end
end Hironaka.HironakaG8MemberWeakEquiv
