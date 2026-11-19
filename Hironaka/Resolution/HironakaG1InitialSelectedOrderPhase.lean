import Hironaka.Resolution.HironakaG1InitialSelectedNormalOrder
import Hironaka.Resolution.HironakaG1PositiveNormalRepairCentres
import Hironaka.Resolution.HironakaSharpActualChronologicalResidualDictionary

/-! The full nonmonomial order run of the initial positive selected record. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialSelectedOrderPhase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec InvDomainTowerAlong
  RelativePrincipalizationSpan GermIdealOrder HomogenizedIdealAlong InvDomainMemberRestriction InvDomainRebase
  StepOneValue StepOneValueMasked StepOneRegime
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  MonomialPartAlong DivisorExponentAlong CompanionReductionAlong CompanionRebase
  RestrictedIdealExtension HironakaSharpActualChronologicalResidualDictionary
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  ResolutionInvariantExt CanonicalCentres CompanionOpen
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaActualOpenZeroSectionDifferentials
  HironakaG1InitialSelectedNormalOrder HironakaG1PositiveNormalRepairCentres

private theorem full_order_run_of_test_order {n k : ℕ} {X : CMfd.{0} n}
    (L : MarkedIdeal n X) (hL : IsInvDomain k L)
    (hOrder : ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower L T →
      ∀ z ∈ (geoTransformAlong L T).cosupp, nmOrd (geoTransformAlong L T) z = L.d)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower L T)
    (z : Y) (hz : z ∈ (geoTransformAlong L T).cosupp) :
    regimeRun (OrdRegime L L.d) T z = T.length := by
  induction T with
  | refl => rfl
  | @step Y Z S C π hπ ih =>
    have hSD := isInvDomain_geoTransformAlong hL S hT.1
    have hPrefix : π z ∈ (geoTransformAlong L S).cosupp :=
      mem_cosupp_of_mem_cosupp_geoTransform_along hSD.isWellFormed.isClosedSubmanifold_N.1
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hSD.isWellFormed.isCoherent hg) hT.2 hπ hz
    have hRegime : OrdRegime L L.d S (π z) := ⟨hPrefix, hOrder S hT.1 _ hPrefix⟩
    rw [regimeRun_step_of (OrdRegime L L.d) S C π hπ hRegime, ih hT.1 (π z) hPrefix,
      BlowupTower.length_step]

/-- The literal initial selected lower record has no incident boundary on
its mask. Its true-mark companion is the literal carrier-restricted record. -/
theorem original_initial_positive_lower_companion_eq {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hLevel : level (properNormalMarked Q)
      (.refl : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) _) p = s + 1) :
    let H := BlowupTower.refl (X := CMfd.of (n := n + 1) (productOpen U))
    let O := maskA (properNormalMarked Q) H p
    let L : MarkedIdeal (n + 1) (CMfd.of (n := n + 1) O) :=
      lowerMarkedM (X := CMfd.of (n := n + 1) (productOpen U)) (properNormalMarked Q) (s + 1) H p
    (∀ B ∈ L.E, B = ∅) ∧ companionOf (n + 1) L L.d =
      (⟨L.N, L.E, restrictOn (n + 1) L.N L.ideal, L.d⟩ : MarkedIdeal (n + 1) O) := by
  intro H O L
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let B := geoTransformAlong (barMarked P) H
  let K := memberRestrict B (membersThrough B.E (origMembers P H) p)
  have hH : IsGeoTestTower P H := trivial
  have hL : IsInvDomain k L := padded_lower_isInvDomain Q hQ H hH p hLevel
  have hOld : origMembers P H = B.E := by
    change B.E.take B.E.length = B.E
    exact List.take_length
  have hE : ∀ D ∈ L.E, D = ∅ := by
    intro D hD
    change D ∈ K.E.map ((Subtype.val : O → X) ⁻¹' ·) at hD
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hD
    have hFilter := hF
    dsimp only [K] at hFilter
    rw [memberRestrict_membersThrough_E] at hFilter
    have hMem : F ∈ origMembers P H := hOld ▸ (List.mem_filter.mp hFilter).1
    have hAvoid : p ∉ F := by
      intro hp
      have h := (List.mem_filter.mp hFilter).2
      simp [hMem, hp] at h
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hAvoid ((interior_subset z.property).1 F hMem hz)
  have hPart : nmPart L = restrictOn (n + 1) L.N L.ideal :=
    nonmonomialPartAlong_eq_restrictOn_of_no_member_factor
      hL.isWellFormed.isClosedSubmanifold_N hL.isWellFormed.isSNCDivisor hL.isWellFormed.isTransverse
      hL.isWellFormed.isCoherent (fun z _ i hi =>
        (show z ∈ (∅ : Set O) from hE _ (List.get_mem L.E i) ▸ hi).elim)
  exact ⟨hE, by simp only [companionOf, companionAlong, lt_self_iff_false, if_false, ← hPart]⟩

/-- On the initial positive selected phase, the order mask is the whole lower
base, and any actual tested continuation on it stays in the true order run at
each endpoint of its cosupport. -/
theorem original_initial_positive_lower_order_phase {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hLevel : level (properNormalMarked Q)
      (.refl : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) _) p = s + 1) :
    let H := BlowupTower.refl (X := CMfd.of (n := n + 1) (productOpen U))
    let O := maskA (properNormalMarked Q) H p
    let L : MarkedIdeal (n + 1) (CMfd.of (n := n + 1) O) :=
      lowerMarkedM (X := CMfd.of (n := n + 1) (productOpen U)) (properNormalMarked Q) (s + 1) H p
    ordMask (M := CMfd.of (n := n + 1) O) L L.d = ⊤ ∧ companionOf (n + 1) L L.d =
      (⟨L.N, L.E, restrictOn (n + 1) L.N L.ideal, L.d⟩ : MarkedIdeal (n + 1) O) ∧
      ∀ {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) O) Y),
        IsGeoTestTower L T → ∀ z ∈ (geoTransformAlong L T).cosupp,
          OrdRegime L L.d T z ∧ regimeRun (OrdRegime L L.d) T z = T.length := by
  intro H O L
  have hL : IsInvDomain k L := padded_lower_isInvDomain Q hQ H trivial p hLevel
  have hOrder : ∀ {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) O) Y),
      IsGeoTestTower L T → ∀ z ∈ (geoTransformAlong L T).cosupp,
        nmOrd (geoTransformAlong L T) z = L.d :=
    fun T => original_initial_positive_lower_test_order Q hQ p hLevel T
  obtain ⟨_, hComp⟩ := original_initial_positive_lower_companion_eq Q hQ p hLevel
  have hCompL : companionOf (n + 1) L L.d =
      (⟨L.N, L.E, restrictOn (n + 1) L.N L.ideal, L.d⟩ : MarkedIdeal (n + 1) O) := hComp
  have hPart : nmPart L = restrictOn (n + 1) L.N L.ideal := by
    simpa only [companionOf, companionAlong, lt_self_iff_false, if_false] using
      congrArg MarkedIdeal.ideal hCompL
  have hEmpty : ordGe L (L.d + 1) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hz' : z ∈ L.cosupp := by
      change z ∈ cosupport (n + 1) L.N (nmPart L) (L.d + 1) at hz
      rw [hPart] at hz
      have hOrderMem := cosupport_anti (Nat.le_succ L.d) hz
      exact ⟨hOrderMem.1, fun g hg => hOrderMem.2 g (le_restrictOn hL.isWellFormed.isCoherent z g hg)⟩
    have hFinite := exists_notMem_ordGe hL.isWellFormed hL.isNonzeroAlongAt
      (ordGe_subset_N L _ hz)
    have hOrd := hOrder (.refl : BlowupTower (CMfd.of (n := n + 1) O) _) trivial z hz'
    have hLe := succ_le_nmOrd_of_mem hFinite hz
    rw [show nmOrd L z = L.d from hOrd] at hLe
    exact (Nat.not_succ_le_self L.d) hLe
  refine ⟨?_, hComp, ?_⟩
  · apply Opens.ext
    change (closure (ordGe L (L.d + 1)))ᶜ = univ
    rw [hEmpty, closure_empty, compl_empty]
  · intro Y T hT z hz
    exact ⟨⟨hz, hOrder T hT z hz⟩, full_order_run_of_test_order L hL hOrder T hT z hz⟩

/-- The actual same-mark companion is a maximal-order input. The two
records have the same canonical tested histories and recursive values on
cosupport, by exact carrier restriction. -/
theorem original_initial_positive_lower_companion_recursion {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hLevel : level (properNormalMarked Q)
      (.refl : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) _) p = s + 1) :
    let H := BlowupTower.refl (X := CMfd.of (n := n + 1) (productOpen U))
    let O := maskA (properNormalMarked Q) H p
    let L : MarkedIdeal (n + 1) (CMfd.of (n := n + 1) O) :=
      lowerMarkedM (X := CMfd.of (n := n + 1) (productOpen U)) (properNormalMarked Q) (s + 1) H p
    let C := companionOf (n + 1) L L.d
    let R := invFamily (Nat.succ_pos n) k
    IsInvDomain k C ∧ IsMaximalOrderAlong C.N C.ideal C.d ∧
      ∀ {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) O) Y),
        (IsCanonical L (R.inv L) T ↔ IsCanonical C (R.inv C) T) ∧
        (IsCanonical L (R.inv L) T → ∀ z ∈ (geoTransformAlong L T).cosupp,
          R.inv L T z = R.inv C T z) := by
  intro H O L C R
  have hL : IsInvDomain k L := padded_lower_isInvDomain Q hQ H trivial p hLevel
  obtain ⟨hMask, hComp, _⟩ := original_initial_positive_lower_order_phase Q hQ p hLevel
  have hCompL : C =
      (⟨L.N, L.E, restrictOn (n + 1) L.N L.ideal, L.d⟩ : MarkedIdeal (n + 1) O) := hComp
  have hEq : RestrictEquiv L C := by
    rw [hCompL]
    exact ⟨rfl, rfl, rfl, restrictLe_self_restrictOn hL.isWellFormed.isCoherent, restrictLe_restrictOn⟩
  have hC : IsInvDomain k C := isInvDomain_of_restrictEquiv hL hEq (by
    rw [hCompL]
    exact isCoherent_restrictOn hL.isWellFormed.isCoherent
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hL.isWellFormed.isClosedSubmanifold_N))
  have hBound : ∀ x ∈ L.cosupp, x ∉ ordGe L (L.d + 1) := by
    intro x _
    apply notMem_ordGe_of_mem_ordMask
    have hTop : ordMask (M := CMfd.of (n := n + 1) O) L L.d = ⊤ := hMask
    rw [hTop]
    trivial
  have hMax := isMaximalOrderAlong_companionOf (Nat.succ_pos n)
    hL.isWellFormed hL.isNonzeroAlongAt hBound
  refine ⟨hC, ?_, fun {Y} T => ?_⟩
  · rw [← hEq.N_eq]
    exact hMax
  · exact ⟨⟨Seq.InvDomainRebase.isCanonical_of_restrictEquiv R hL hC hEq T,
      Seq.InvDomainRebase.isCanonical_of_restrictEquiv R hC hL (restrictEquiv_symm hEq) T⟩,
      fun hCan => R.isInvValue.representative L C hL hC hEq T hCan⟩

end Hironaka.HironakaG1InitialSelectedOrderPhase
