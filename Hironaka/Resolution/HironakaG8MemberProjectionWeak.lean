import Hironaka.Resolution.HironakaG8MemberWeakEquiv
import Hironaka.Resolution.HironakaActualOriginalLowerHeadProjectionTests
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold
namespace Hironaka.HironakaG8MemberProjectionWeak
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal ResolutionInvariantSpec
  HomogenizedIdealAlong HomogenizedGlueingTower CoefficientIdealRestriction CoefficientIdealAlongRestrictionDrop
  InvDomainMemberRestriction InvDomainRebase HironakaG8MemberWeakEquiv
  HironakaActualProjectionTestRecord HironakaAuxiliaryGraphGeometry HironakaSmoothSubmersionRelativeGeometry

/-- Projecting a native member restriction preserves the same controlled-test
and cosupport dictionary relative to the projected ambient record. -/
theorem projection_memberRestrict_test_dictionary {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n} {k : ℕ}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (I : Finset (Fin M.E.length))
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (projectionAmbient X) Y) :
    (IsGeoTestTower (projectionTest (memberRestrict M I)) T ↔
      IsGeoTestTower (projectionTest M) T ∧ CentresIn (projectionTest (memberRestrict M I)).N T) ∧
    (IsGeoTestTower (projectionTest (memberRestrict M I)) T →
      (geoTransformAlong (projectionTest (memberRestrict M I)) T).cosupp =
        (geoTransformAlong (projectionTest M) T).cosupp ∩ strictAlong T (projectionTest (memberRestrict M I)).N) := by
  let R := memberRestrict M I
  let P := projectionTest M
  let L := projectionTest R
  have hRwf := isWellFormed_memberRestrict hn hM.isWellFormed I
  have hP := projection_test_isInvDomain M hM
  have hsub0 : ∀ H ∈ R.E, H ∈ M.E := by
    intro H hH
    rw [memberRestrict_E] at hH
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hH
    exact List.get_mem _ _
  have hdel0 : ∀ H ∈ M.E, H ∉ R.E → R.N ⊆ H := by
    intro H hH hH' x hx
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    by_cases hi : i ∈ I
    · exact hx.2 i hi
    · exfalso
      apply hH'
      rw [memberRestrict_E]
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true hi⟩)
  have hS : IsClosedSubmanifold (n+1) L.N := by
    change IsClosedSubmanifold (n+1) ((Prod.fst : projectionAmbient X → X) ⁻¹' R.N)
    exact isClosedSubmanifold_preimage_submersion
      (isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) hRwf.isClosedSubmanifold_N
  have hSN : L.N ⊆ P.N := by
    intro p hp
    exact hp.1
  have hsub : ∀ H ∈ L.E, H ∈ P.E := by
    intro H hH
    change H ∈ R.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X] at hH
    change H ∈ M.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]
    rcases List.mem_append.mp hH with hOld | hNew
    · obtain ⟨H₀,hH₀,rfl⟩ := List.mem_map.mp hOld
      exact List.mem_append_left _ (List.mem_map_of_mem (hsub0 H₀ hH₀))
    · exact List.mem_append_right _ hNew
  have hdel : ∀ H ∈ P.E, H ∉ L.E → L.N ⊆ H := by
    intro H hH hH' p hp
    change H ∈ M.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X] at hH
    rcases List.mem_append.mp hH with hOld | hNew
    · obtain ⟨H₀,hH₀,rfl⟩ := List.mem_map.mp hOld
      have hnot : H₀ ∉ R.E := by
        intro hR
        apply hH'
        change (Prod.fst : projectionAmbient X → X) ⁻¹' H₀ ∈
          R.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]
        exact List.mem_append_left _ (List.mem_map_of_mem hR)
      exact hdel0 H₀ hH₀ hnot hp
    · exfalso
      apply hH'
      change H ∈ R.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]
      exact List.mem_append_right _ hNew
  have hcoeff : projectionTest (coeffMarkedAlong M) = coeffMarkedAlong (projectionTest M) := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
    exact congrArg (fun A => A.ideal)
      (HironakaSmoothSubmersionRelativeDifferentialIdeals.pullback_coeffMarkedAlong (X := X) (Y := projectionAmbient X)
        (isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) M
        hM.isWellFormed.isCoherent hM.isWellFormed.isClosedSubmanifold_N)
  have hrec : L = ({ withN (coeffMarkedAlong P) L.N with E := L.E } : MarkedIdeal (n+1) (projectionAmbient X)) := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of (𝔪 := L)
      (𝔫 := { withN (coeffMarkedAlong P) L.N with E := L.E }) rfl rfl ?_ ?_
    · exact congrArg (fun J => J.ideal) hcoeff
    · exact congrArg (fun J => J.d) hcoeff
  have hiff := coeffAlong_restrict_withE_iff P hP.isWellFormed hP.one_le_d hS hSN hsub hdel T
  rw [← hrec] at hiff
  exact hiff

/-- The line-projection weak equivalence of same-carrier records descends to
their member restrictions, with the genuinely new horizontal member kept. -/
theorem projection_memberRestrict_membersThrough_wEquiv {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {A B : MarkedIdeal n X} {k k' : ℕ} (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hN : A.N = B.N) (hE : A.E = B.E) (hW : WEquiv (projectionTest A) (projectionTest B))
    (E₀ : List (Set X)) (x : X) :
    WEquiv (projectionTest (memberRestrict A (membersThrough A.E E₀ x)))
      (projectionTest (memberRestrict B (membersThrough B.E E₀ x))) := by
  let R := memberRestrict A (membersThrough A.E E₀ x)
  let S := memberRestrict B (membersThrough B.E E₀ x)
  let P := projectionTest R
  let Q := projectionTest S
  have hRN : R.N = S.N := by simp only [R,S,memberRestrict_membersThrough_N,hN,hE]
  have hRE : R.E = S.E := by simp only [R,S,memberRestrict_membersThrough_E,hE]
  have hPN : P.N = Q.N := by
    change (Prod.fst : projectionAmbient X → X) ⁻¹' R.N = (Prod.fst : projectionAmbient X → X) ⁻¹' S.N
    rw [hRN]
  have hPE : P.E = Q.E := by
    change R.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X] =
      S.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]
    rw [hRE]
  refine ⟨hPE,fun T => ⟨?_,?_⟩⟩
  · have hPA := (projection_memberRestrict_test_dictionary hn A hA (membersThrough A.E E₀ x) T).1
    have hQB := (projection_memberRestrict_test_dictionary hn B hB (membersThrough B.E E₀ x) T).1
    rw [hPA,hQB,hPN]
    exact and_congr_left fun _ => (hW.2 T).1
  · intro hT
    have hPA := (projection_memberRestrict_test_dictionary hn A hA (membersThrough A.E E₀ x) T).1.mp hT
    have hQB := (projection_memberRestrict_test_dictionary hn B hB (membersThrough B.E E₀ x) T).1.mpr
      ⟨(hW.2 T).1.mp hPA.1,hPN ▸ hPA.2⟩
    rw [(projection_memberRestrict_test_dictionary hn A hA (membersThrough A.E E₀ x) T).2 hT,
      (projection_memberRestrict_test_dictionary hn B hB (membersThrough B.E E₀ x) T).2 hQB,
      (hW.2 T).2 hPA.1,hPN]

end
end Hironaka.HironakaG8MemberProjectionWeak
