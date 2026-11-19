import Hironaka.Resolution.HironakaG8PrincipalRetainedEpochFinite
import Hironaka.Resolution.HironakaOriginalEmptyHeadPrefix
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyFilterComparison
import Hironaka.Resolution.HironakaActualOpenEmbeddingVanishingIdeal
import Hironaka.Invariant.RestrictEmptyTower

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8RestartedEmptyEpoch
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  CanonicalCentres ResolutionDriver ResolutionInvariantSpec
  HironakaOriginalInvariantEmptyInsertion HironakaOriginalBoundaryEmptyFilterComparison
  MonomialInvariantEmptyMember IdealWeightPowers BlowupControlledTransform
  HironakaOriginalBoundaryCanonicalPrincipalization HironakaActualOpenEmbeddingVanishingIdeal
  HironakaOriginalEmptyHeadPrefix HomogenizedIdealAlong

open ResolutionInvariantExt (IsEmptyTower isCanonical_of_isEmptyTower isGeoTestTower_of_isEmptyTower)

variable {n : ℕ} {X D Y : CMfd.{0} (n+1)}

private abbrev R (n : ℕ) := canonicalInvariant (n+1)
private abbrev original (W : Set X) : MarkedIdeal (n+1) X := ⟨univ,[],vanishingIdeal (n := n+1) W,1⟩

/-- These are the actual empty slots installed by the empty prefix. -/
def padded (M : MarkedIdeal (n+1) X) (r : ℕ) : MarkedIdeal (n+1) X :=
  { M with E := List.replicate r ∅ }

/-- All genuine empty prefix steps act by this single increasing map on
the entire original value. -/
def emptyPrefixShift (n r : ℕ) : ValTy (n+1) → ValTy (n+1) :=
  (shiftFamily (n+1) 0)^[r]

theorem emptyPrefixShift_strictMono (n r : ℕ) : StrictMono (emptyPrefixShift n r) :=
  (strictMono_shiftFamily (n+1) 0).iterate r

theorem padded_value (M : MarkedIdeal (n+1) X) (hE : M.E = [])
    (S : BlowupTower X Y) (z : Y) (r : ℕ) :
    (R n).inv (padded M r) S z = emptyPrefixShift n r ((R n).inv M S z) := by
  induction r with
  | zero =>
    have hz : padded M 0 = M := by
      rcases M with ⟨N,E,J,d⟩
      change E = [] at hE
      subst E
      rfl
    rw [hz]
    rfl
  | succ r ih =>
    have hrec : padded M (r+1) = insertEmpty 0 (padded M r) := rfl
    rw [hrec]
    change (invFamily (Nat.succ_pos n) (n+1)).inv (insertEmpty 0 (padded M r)) S z = _
    rw [invFamily_insertEmpty (Nat.succ_pos n) (n+1) _ 0 (Nat.zero_le _) S z]
    change shiftFamily (n+1) 0 ((R n).inv (padded M r) S z) = _
    rw [ih]
    exact (Function.iterate_succ_apply' (shiftFamily (n+1) 0) r ((R n).inv M S z)).symm

theorem nonemptyBoundary_padded (M : MarkedIdeal (n+1) X) (hE : M.E = []) (r : ℕ) :
    nonemptyBoundary (padded M r) = M := by
  classical
  rcases M with ⟨N,E,J,d⟩
  change E = [] at hE
  subst E
  change (⟨N,(List.replicate r (∅ : Set X)).filter (fun H => decide H.Nonempty),J,d⟩ :
    MarkedIdeal (n+1) X) = _
  simp

private theorem exceptional_ideal_eq_unit_of_empty :
    ∀ {D : CMfd.{0} (n+1)} (T : BlowupTower X D), IsEmptyTower T →
      (BlowupTowerTransforms.exceptionalDivisor T).ideal = unitIdeal (n+1) D
  | _, .refl, _ => rfl
  | _, .step T C π hπ, he => by
    obtain ⟨heT,rfl⟩ := he
    rw [exceptionalDivisor_step_ideal,exceptional_ideal_eq_unit_of_empty T heT,
      HironakaNormalCrossingsOrderedMonomialTail.vanishingIdeal_empty_eq_unit,
      BlowupExceptionalDivisor.pullback_unitIdeal,unitIdeal_mul isCoherent_unitIdeal]

private theorem whole_empty_prefix_record (W : Set X)
    (hM : IsInvDomain (n+1) (original W)) (H : BlowupTower X D) (he : IsEmptyTower H)
    (β : D ≃ₘ⟮𝓘(ℂ,ComplexModel (n+1)),𝓘(ℂ,ComplexModel (n+1))⟯ X)
    (hβ : ∀ x, β x = H.proj x) :
    geoTransformAlong (original W) H =
      padded (original (β ⁻¹' W)) H.length := by
  let M := original W
  have hT : IsGeoTestTower M H := isGeoTestTower_of_isEmptyTower M H he
  obtain ⟨hN,hCoh,hIdeal⟩ := pullback_eq_mul_geoTransformAlong (𝔪 := M) rfl hM.isWellFormed.isCoherent H hT
  have hE := boundary_of_all_empty_tower M (fun _ h => by change _ ∈ ([] : List (Set X)) at h; simp at h) H he
  change (geoTransformAlong M H).E = List.replicate H.length ∅ at hE
  have hMark : (geoTransformAlong M H).d = 1 := d_geoTransformAlong M H
  have hUnit := exceptional_ideal_eq_unit_of_empty H he
  rw [hUnit,idealPow_unitIdeal,unitIdeal_mul hCoh] at hIdeal
  have hI : (geoTransformAlong M H).ideal = vanishingIdeal (n := n+1) (β ⁻¹' W) := by
    rw [← hIdeal,← funext hβ]
    exact pullback_vanishingIdeal_of_biholomorphism β W
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN hE hI hMark

/-- Along an already canonical chronological prefix the native read after
rebasing has literally the same maximum. Its support is the same actual
controlled support by append composition. -/
theorem canonical_maximum_empty_prefix_rebase
    (M : MarkedIdeal (n+1) X) (hM : IsInvDomain (n+1) M)
    (H : BlowupTower X D) (he : IsEmptyTower H) (S : BlowupTower D Y)
    (hCan : IsCanonical M ((R n).inv M) (H.append S)) :
    let B := geoTransformAlong M H
    maxLocus ((R n).inv M (H.append S)) (geoTransformAlong M (H.append S)).cosupp =
      maxLocus ((R n).inv B S) (geoTransformAlong B S).cosupp := by
  let B := geoTransformAlong M H
  have hVal (z : Y) (hz : z ∈ (geoTransformAlong M (H.append S)).cosupp) :
      (R n).inv M (H.append S) z = (R n).inv B S z :=
    (R n).isInvValue.emptyPrefix M hM H S he hCan z hz
  have hCos : (geoTransformAlong M (H.append S)).cosupp = (geoTransformAlong B S).cosupp := by
    rw [geoTransformAlong_append]
  change maxLocus ((R n).inv M (H.append S)) (geoTransformAlong M (H.append S)).cosupp =
    maxLocus ((R n).inv B S) (geoTransformAlong B S).cosupp
  ext z
  constructor
  · intro hz
    have hz' := hz.1
    rw [hCos] at hz'
    refine ⟨hz',fun y hy => ?_⟩
    have hy' := hy
    rw [← hCos] at hy'
    rw [← hVal y hy',← hVal z hz.1]
    exact hz.2 y hy'
  · intro hz
    have hz' := hz.1
    rw [← hCos] at hz'
    refine ⟨hz',fun y hy => ?_⟩
    have hy' := hy
    rw [hCos] at hy'
    rw [hVal y hy,hVal z hz']
    exact hz.2 y hy'

/-- Reattaching the chronological empty prefix neither loses nor creates
canonical tails for the actual transformed record. -/
theorem canonical_empty_prefix_append_iff
    (M : MarkedIdeal (n+1) X) (hM : IsInvDomain (n+1) M)
    (H : BlowupTower X D) (he : IsEmptyTower H) (S : BlowupTower D Y) :
    let B := geoTransformAlong M H
    IsCanonical M ((R n).inv M) (H.append S) ↔ IsCanonical B ((R n).inv B) S := by
  let B := geoTransformAlong M H
  change IsCanonical M ((R n).inv M) (H.append S) ↔ IsCanonical B ((R n).inv B) S
  induction S with
  | refl =>
    exact ⟨fun _ => trivial,fun _ => isCanonical_of_isEmptyTower M ((R n).inv M) H he⟩
  | step S C π hπ ih =>
    change (_ ∧ (C = ∅ ∨ C = maxLocus ((R n).inv M (H.append S))
      (geoTransformAlong M (H.append S)).cosupp)) ↔
      (_ ∧ (C = ∅ ∨ C = maxLocus ((R n).inv B S) (geoTransformAlong B S).cosupp))
    constructor
    · rintro ⟨hBefore,hc⟩
      refine ⟨ih.mp hBefore,?_⟩
      have hMax := canonical_maximum_empty_prefix_rebase M hM H he S hBefore
      exact hc.imp id (fun h => h.trans hMax)
    · rintro ⟨hBefore,hc⟩
      have hOld := ih.mpr hBefore
      refine ⟨hOld,?_⟩
      have hMax := canonical_maximum_empty_prefix_rebase M hM H he S hOld
      exact hc.imp id (fun h => h.trans hMax.symm)

/-- The actual strict transform on an all-empty history is the whole
closed carrier pulled back by its genuine projection biholomorphism. -/
theorem whole_record_on_empty_prefix (W : Set X) (hW : IsClosed W)
    (hM : IsInvDomain (n+1) (original W)) (H : BlowupTower X D) (he : IsEmptyTower H) :
    geoTransformAlong (original W) H =
      padded (original (strictTransform (n+1) H.proj W)) H.length := by
  obtain ⟨β,hβ⟩ := exists_empty_tower_projection H he
  have hfun : (β : D → X) = H.proj := funext hβ
  have hExc : exceptionalLocus (n+1) β = ∅ := by
    ext z
    simp only [mem_empty_iff_false,iff_false]
    exact MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
      β.contMDiff β.symm.contMDiff β.apply_symm_apply β.symm_apply_apply z
  have hStrict : strictTransform (n+1) H.proj W = β ⁻¹' W := by
    rw [← hfun,strictTransform,hExc,sdiff_empty,(hW.preimage β.continuous).closure_eq]
  rw [hStrict]
  exact whole_empty_prefix_record W hM H he β hβ

/-- A restarted, whole native top-mark record on a missed window gives the
same physical canonical tail for the original mark-one ideal. The exact
old value includes the strictly increasing shift for every empty slot. -/
theorem restarted_native_empty_epoch
    (W : Set X) (hW : IsClosed W) (hM : IsInvDomain (n+1) (original W))
    (H : BlowupTower X D) (he : IsEmptyTower H) (q : ℕ) (S : BlowupTower D Y) :
    let W' := strictTransform (n+1) H.proj W
    let A := original W'
    let Q : MarkedIdeal (n+1) D := ⟨univ,[],vanishingIdeal (n := n+1) W',q⟩
    IsInvDomain (n+1) Q →
    IsMaximalOrderAlong Q.N Q.ideal q →
    IsCanonical Q ((R n).inv Q) S →
    IsCanonical (original W) ((R n).inv (original W)) (H.append S) ∧
    (∀ z ∈ (geoTransformAlong (original W) (H.append S)).cosupp,
      (R n).inv (original W) (H.append S) z = emptyPrefixShift n H.length ((R n).inv A S z)) ∧
    (∀ z ∈ (geoTransformAlong Q S).cosupp,
      (R n).inv (original W) (H.append S) z = emptyPrefixShift n H.length ((R n).inv Q S z)) ∧
    ((geoTransformAlong Q S).cosupp.Nonempty →
      maxLocus ((R n).inv (original W) (H.append S))
          (geoTransformAlong (original W) (H.append S)).cosupp =
        maxLocus ((R n).inv Q S) (geoTransformAlong Q S).cosupp) := by
  dsimp only
  intro hQ hCap hNative
  let W' := strictTransform (n+1) H.proj W
  let J := vanishingIdeal (n := n+1) W'
  let A := original W'
  let Q : MarkedIdeal (n+1) D := ⟨univ,[],J,q⟩
  let B := geoTransformAlong (original W) H
  have hRec : B = padded A H.length := whole_record_on_empty_prefix W hW hM H he
  have hFilter : nonemptyBoundary B = A := by rw [hRec,nonemptyBoundary_padded A rfl]
  have hFresh : IsCanonical A ((R n).inv A) S :=
    HironakaG8PrincipalRetainedEpochFinite.finite_native_retained_epoch_whole_markOne_canonical (X := D)
      J q hQ hCap S hNative
  have hRebase : IsCanonical B ((R n).inv B) S := by
    apply (isCanonical_nonemptyBoundary_iff B S).mp
    rwa [hFilter]
  have hOld : IsCanonical (original W) ((R n).inv (original W)) (H.append S) :=
    (canonical_empty_prefix_append_iff (original W) hM H he S).mpr hRebase
  have hClock (z : Y) (hz : z ∈ (geoTransformAlong (original W) (H.append S)).cosupp) :
      (R n).inv (original W) (H.append S) z = emptyPrefixShift n H.length ((R n).inv A S z) := by
    have hv := (R n).isInvValue.emptyPrefix (original W) hM H S he hOld z hz
    change (R n).inv (original W) (H.append S) z = (R n).inv B S z at hv
    rw [hv,hRec]
    exact padded_value A rfl S z H.length
  refine ⟨hOld,hClock,?_,?_⟩
  · intro z hz
    have hRead := HironakaG8PrincipalRetainedEpochFinite.finite_retained_support_and_values (X := D)
      J q hQ hCap S hFresh hNative
    dsimp only at hRead
    have hzA := ((hRead.1 z).mp hz).1
    change z ∈ (geoTransformAlong A S).cosupp at hzA
    have hzOld : z ∈ (geoTransformAlong (original W) (H.append S)).cosupp := by
      rw [geoTransformAlong_append]
      change z ∈ (geoTransformAlong B S).cosupp
      rw [← cosupp_nonemptyBoundary_along B S,hFilter]
      exact hzA
    rw [hClock z hzOld]
    exact congrArg (emptyPrefixShift n H.length) (hRead.2.1 z hz)
  · intro hSurvive
    have hRaw := HironakaG8PrincipalRetainedEpochFinite.finite_retained_maximum_eq (X := D)
      J q hQ hCap S hFresh hNative hSurvive
    dsimp only at hRaw
    have hMax := canonical_maximum_empty_prefix_rebase (original W) hM H he S hOld
    change maxLocus ((R n).inv (original W) (H.append S))
      (geoTransformAlong (original W) (H.append S)).cosupp =
      maxLocus ((R n).inv B S) (geoTransformAlong B S).cosupp at hMax
    rw [hMax,← maxLocus_nonemptyBoundary B S,
      ← cosupp_nonemptyBoundary_along B S,hFilter]
    exact hRaw

/-- On a literal window missed by all the old centres, keep the physical
restricted prefix and append the actual lower native tower. The current
carrier is the trace of the global strict transform and the clock counts
every actual old slot, including the restricted empty ones. -/
theorem restarted_native_epoch_on_missed_window
    (W : Set X) (hW : IsClosed W) (H : BlowupTower X D)
    (O : Opens X) (hAvoid : RestrictEmptyTower.CentresAvoid O H)
    (q : ℕ) (S : BlowupTower (CMfd.of (n := n+1) (openPreimage H O)) Y) :
    let U := openPreimage H O
    let Hₒ := restrict O H
    let Wₒ := (Subtype.val : O → X) ⁻¹' W
    let W' := (Subtype.val : U → D) ⁻¹' strictTransform (n+1) H.proj W
    let A := original (X := CMfd.of (n := n+1) U) W'
    let Q : MarkedIdeal (n+1) (CMfd.of (n := n+1) U) := ⟨univ,[],vanishingIdeal (n := n+1) W',q⟩
    let M := original (X := CMfd.of (n := n+1) O) Wₒ
    IsInvDomain (n+1) M →
    IsInvDomain (n+1) Q →
    IsMaximalOrderAlong Q.N Q.ideal q →
    IsCanonical Q ((R n).inv Q) S →
    IsCanonical M ((R n).inv M) (Hₒ.append S) ∧
    (∀ z ∈ (geoTransformAlong M (Hₒ.append S)).cosupp,
      (R n).inv M (Hₒ.append S) z = emptyPrefixShift n H.length ((R n).inv A S z)) ∧
    (∀ z ∈ (geoTransformAlong Q S).cosupp,
      (R n).inv M (Hₒ.append S) z = emptyPrefixShift n H.length ((R n).inv Q S z)) ∧
    ((geoTransformAlong Q S).cosupp.Nonempty →
      maxLocus ((R n).inv M (Hₒ.append S)) (geoTransformAlong M (Hₒ.append S)).cosupp =
        maxLocus ((R n).inv Q S) (geoTransformAlong Q S).cosupp) := by
  dsimp only
  intro hM hQ hCap hCan
  let Hₒ := restrict O H
  let Wₒ := (Subtype.val : O → X) ⁻¹' W
  have hEmpty : IsEmptyTower Hₒ := (RestrictEmptyTower.isEmptyTower_restrict_iff O H).mpr hAvoid
  have hTrace : strictTransform (n+1) Hₒ.proj Wₒ =
      (Subtype.val : openPreimage H O → D) ⁻¹' strictTransform (n+1) H.proj W :=
    HironakaNormalCrossingsOpenRestrictionSeparation.strictTransform_restricted_tower O H W
  have hRestart := restarted_native_empty_epoch Wₒ (hW.preimage continuous_subtype_val) hM Hₒ hEmpty q S
  dsimp only at hRestart
  rw [hTrace,length_restrict] at hRestart
  exact hRestart hQ hCap hCan

end
end Hironaka.HironakaG8RestartedEmptyEpoch
