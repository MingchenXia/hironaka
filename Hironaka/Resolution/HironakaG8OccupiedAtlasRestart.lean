import Hironaka.Resolution.HironakaG8OccupiedMixedRestart
import Hironaka.Resolution.HironakaG11InvCommonMark

/-! Reflect canonicality from a simultaneous atlas of literal restrictions
of one whole marked record, then consume that atlas at an occupied cut. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8OccupiedAtlasRestart
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  NormalCrossings HironakaEmbeddedAnalytic ResolutionInvariantSpec GermIdealOrder
  CanonicalCentres ResolutionDriver HironakaG8NativeSimultaneousCentre
  HironakaG8NativeRelativeClearing HironakaG8NativePhaseCertificate
  HironakaG11InvCommonMark HironakaG1OriginalUnequalMarkCanonical HironakaActualPowerBoundaryExponents
  HironakaG8OccupiedMixedRestart HironakaG8OccupiedPrincipalResidual
  HironakaG8PrincipalRetainedEpochFinite HomogenizedIdealAlong

variable {n : ℕ} {X D Y : CMfd.{0} (n+1)} {I : Type}

private abbrev whole (W : Set X) (E : List (Set X)) (d : ℕ) : MarkedIdeal (n+1) X :=
  ⟨univ,E,vanishingIdeal (n := n+1) W,d⟩

/-- Literal chartwise simultaneous maxima of one whole record determine
the same ambient physical centre at every finite prefix. The atlas need
only cover the initial cosupport, and each prefix supplies its own TEST
and locality before the next centre is compared. -/
theorem canonical_of_simultaneous_pullback_atlas
    {Λ : Type} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} (n+1) (n+1) Λ)
    (F : MarkedIdeal (n+1) D) (hF : IsInvDomain (n+1) F)
    (U : I → Opens D) (hCover : ∀ x ∈ F.cosupp, ∃ i, x ∈ U i)
    (T : BlowupTower D Y)
    (hSync : NativeSimultaneousStages R U
      (fun i => MarkedIdeal.pullback (Subtype.val : U i → D) F) T) :
    IsCanonical F (R.inv F) T := by
  induction T with
  | refl => trivial
  | @step A B T C π hπ ih =>
    have hCan := ih hSync.1
    refine ⟨hCan,?_⟩
    rcases hSync.2 with he | ⟨m,hm⟩
    · exact Or.inl he
    by_cases hC : C.Nonempty
    · right
      let G := geoTransformAlong F T
      let v := R.inv F T
      have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hF T hCan
      have hWindow (y : A) (hy : y ∈ G.cosupp) : ∃ i, y ∈ openPreimage T (U i) :=
        hCover (T.proj y) (TransformOffCentre.cosupp_geoTransformAlong_subset F
          hF.isWellFormed.isClosedSubmanifold_N hF.isWellFormed.isCoherent T hTest hy)
      have hCos (i : I) :
          (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U i → D) F) (restrict (U i) T)).cosupp =
            (Subtype.val : openPreimage T (U i) → A) ⁻¹' G.cosupp :=
        ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hF.isWellFormed.isClosedSubmanifold_N
          hF.isWellFormed.isCoherent (U i) T hTest
      have hUpper (y : A) (hy : y ∈ G.cosupp) : v y ≤ m := by
        obtain ⟨i,hi⟩ := hWindow y hy
        let z : openPreimage T (U i) := ⟨y,hi⟩
        have hz : z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U i → D) F) (restrict (U i) T)).cosupp := by
          rw [hCos i]
          exact hy
        have hzVal := hm.upper i z hz
        rw [R.isInvValue.restrictOpen F hF (U i) T hCan z hy] at hzVal
        exact hzVal
      have hTrace (y : A) : y ∈ C ↔ y ∈ G.cosupp ∧ v y = m := by
        constructor
        · intro hy
          obtain ⟨i,hi⟩ := hm.covered y hy
          let z : openPreimage T (U i) := ⟨y,hi⟩
          have hz : z ∈ (Subtype.val : openPreimage T (U i) → A) ⁻¹' C := hy
          rw [hm.trace i,hCos i] at hz
          have hzCos : y ∈ G.cosupp := hz.1
          have hv := hz.2
          rw [R.isInvValue.restrictOpen F hF (U i) T hCan z hzCos] at hv
          exact ⟨hzCos,hv⟩
        · rintro ⟨hy,hv⟩
          obtain ⟨i,hi⟩ := hWindow y hy
          let z : openPreimage T (U i) := ⟨y,hi⟩
          have hz : z ∈ (Subtype.val : openPreimage T (U i) → A) ⁻¹' C := by
            rw [hm.trace i,hCos i]
            exact ⟨hy,(R.isInvValue.restrictOpen F hF (U i) T hCan z hy).trans hv⟩
          exact hz
      obtain ⟨a,ha⟩ := hC
      obtain ⟨haG,haVal⟩ := (hTrace a).mp ha
      change C = maxLocus v G.cosupp
      ext y
      constructor
      · intro hy
        obtain ⟨hyG,hyVal⟩ := (hTrace y).mp hy
        exact ⟨hyG,fun z hz => hyVal.symm ▸ hUpper z hz⟩
      · intro hy
        apply (hTrace y).mpr
        refine ⟨hy.1,le_antisymm (hUpper y hy.1) ?_⟩
        rw [← haVal]
        exact hy.2 a haG
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hC)

/-- A simultaneous native atlas whose raw records are all exact
restrictions of the same whole record has one common powering exponent.
Its simultaneous maxima certify whole raw CAN whenever its literal
windows cover the initial active locus. -/
theorem canonical_of_exact_simultaneous_native_atlas
    {W : Set D} {E : List (Set D)} {H : ℕ → ℕ}
    (A : NativeWindows D I W E H (phaseLevel W H))
    (F : MarkedIdeal (n+1) D) (hF : IsInvDomain (n+1) F)
    (hCover : ∀ x ∈ F.cosupp, ∃ i, x ∈ A.openSet i)
    (hRaw : ∀ i, A.record i = MarkedIdeal.pullback (Subtype.val : A.openSet i → D) F)
    (T : BlowupTower D Y)
    (hSync : NativeSimultaneousStages (canonicalInvariant (n+1)) A.openSet A.powered T) :
    IsCanonical F ((canonicalInvariant (n+1)).inv F) T := by
  by_cases hi : Nonempty I
  · obtain ⟨i₀⟩ := hi
    let e := A.exponent i₀
    have he : 1 ≤ e := A.positive i₀
    have hMark (i : I) : (A.record i).d = F.d := by rw [hRaw i]; rfl
    have hExp (i : I) : A.exponent i = e := by
      apply Nat.eq_of_mul_eq_mul_left (by have h := hF.one_le_d; omega : 0 < F.d)
      have hi := A.commonMark i
      have hj := A.commonMark i₀
      change (A.record i).d * A.exponent i = A.mark at hi
      change (A.record i₀).d * A.exponent i₀ = A.mark at hj
      rw [hMark i] at hi
      rw [hMark i₀] at hj
      exact hi.trans hj.symm
    let Q := powerMarked F e
    have hQ := powerMarked_isInvDomain F hF he
    have hRecords : A.powered = (fun i => MarkedIdeal.pullback (Subtype.val : A.openSet i → D) Q) := by
      funext i
      change powerMarked (A.record i) (A.exponent i) = MarkedIdeal.pullback (Subtype.val : A.openSet i → D) (powerMarked F e)
      rw [hExp i,hRaw i]
      exact (HironakaG11InvCommonMark.pullback_powerMarked contMDiff_subtype_val F hF.isWellFormed.isCoherent e).symm
    have hCoverQ (x : D) (hx : x ∈ Q.cosupp) : ∃ i, x ∈ A.openSet i :=
      hCover x ((powerMarked_cosupp F hF he) ▸ hx)
    rw [hRecords] at hSync
    have hCanon := canonical_of_simultaneous_pullback_atlas (canonicalInvariant (n+1)) Q hQ
      A.openSet hCoverQ T hSync
    exact (canonicalInvariant_isCanonical_power_iff F hF e he T).mpr hCanon
  · have hEmpty : ResolutionInvariantExt.IsEmptyTower T := by
      induction T with
      | refl => trivial
      | step T C π hπ ih =>
        refine ⟨ih hSync.1,?_⟩
        rcases hSync.2 with he | ⟨m,hm⟩
        · exact he
        · apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          obtain ⟨i,_⟩ := hm.covered x hx
          exact hi ⟨i⟩
    exact ResolutionInvariantExt.isCanonical_of_isEmptyTower F ((canonicalInvariant (n+1)).inv F) T hEmpty

/-- A selected atlas of the genuine lower epoch with exact chartwise
whole records. Coverage may come from many windows. -/
def HasExactCoveredNativeAtlas
    (W : Set D) (E : List (Set D)) (H : ℕ → ℕ)
    (S : BlowupTower D Y) (F : MarkedIdeal (n+1) D) : Prop :=
  ∃ (I : Type) (A : NativeWindows D I W E H (phaseLevel W H)),
    NativeSimultaneousStages (canonicalInvariant (n+1)) A.openSet A.powered S ∧
    (∀ i, A.record i = MarkedIdeal.pullback (Subtype.val : A.openSet i → D) F) ∧
    (∀ x ∈ F.cosupp, ∃ i, x ∈ A.openSet i)

/-- An actual simultaneous atlas, with no single ambient chart required,
certifies the raw canonical history of the whole record. -/
theorem canonical_of_exact_covered_native_atlas
    (W : Set D) (E : List (Set D)) (H : ℕ → ℕ)
    (S : BlowupTower D Y) (F : MarkedIdeal (n+1) D) (hF : IsInvDomain (n+1) F)
    (hAtlas : HasExactCoveredNativeAtlas W E H S F) :
    IsCanonical F ((canonicalInvariant (n+1)).inv F) S := by
  obtain ⟨I,A,hSync,hExact,hCover⟩ := hAtlas
  exact canonical_of_exact_simultaneous_native_atlas A F hF hCover hExact S hSync

/-- The actual profile cover already covers the whole record if all of
its active points have the selected Hilbert–Samuel profile. -/
theorem exact_covered_atlas_of_profile_support
    {W : Set D} {E : List (Set D)} {H : ℕ → ℕ}
    (A : NativeWindows D I W E H (phaseLevel W H))
    (F : MarkedIdeal (n+1) D) (S : BlowupTower D Y)
    (hLevel : F.cosupp ⊆ phaseLevel W H)
    (hRaw : ∀ i, A.record i = MarkedIdeal.pullback (Subtype.val : A.openSet i → D) F)
    (hSync : NativeSimultaneousStages (canonicalInvariant (n+1)) A.openSet A.powered S) :
    HasExactCoveredNativeAtlas W E H S F :=
  ⟨I,A,hSync,hRaw,fun x hx => A.covers x (hLevel hx)⟩

/-- The occupied principal lower epoch is canonical on the original
physical history when its whole active locus is covered by simultaneous
native windows with the exact strict record. The initial higher step
and every inherited boundary entry remain literal. -/
theorem occupied_principal_restart_canonical_of_native_atlas
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hI : (vanishingIdeal (n := n+1) W).IsInvertible)
    (hPure : W ⊆ closure (regularLocus (n := n+1) W n))
    (E : List (Set X)) (μ : ℕ) (hμ : 2 ≤ μ)
    (hDom : IsInvDomain (n+1) (whole W E 1))
    (hOld : HasNoBoundaryFactor (whole W E 1))
    (hBound : ∀ x ∈ W, order (n+1) univ (vanishingIdeal (n := n+1) W) x ≤ (μ : ℕ∞))
    (C : Set X) (π : D → X) (hπ : IsBlowupAlong (n+1) C π)
    (hHigh : (whole W E μ).IsAdmissibleCentre C) (q : ℕ) (hq : 1 ≤ q) (hqμ : q < μ)
    (Hlower : ℕ → ℕ) (S : BlowupTower D Y) :
    let M := whole W E 1
    let H : BlowupTower X D := .step .refl C π hπ
    let A := geoTransformAlong M H
    let W' := strictTransform (n+1) π W
    let F := whole W' A.E q
    let R := canonicalInvariant.{0} (n+1)
    IsMaximalOrderAlong F.N F.ideal q →
    IsCanonical M (R.inv M) H →
    HasExactCoveredNativeAtlas W' A.E Hlower S F →
    IsCanonical M (R.inv M) (H.append S) ∧ IsCanonical A (R.inv A) S := by
  dsimp only
  intro hCap hCan hAtlas
  obtain ⟨hF,_hNo,_hMask,_hComp⟩ := occupied_hypersurface_companion_eq_fresh_companion
    W hW hI hPure E μ hμ hDom hOld hBound C π hπ hHigh q hq
  have hNative := canonical_of_exact_covered_native_atlas _ _ Hlower S _ hF hAtlas
  exact occupied_principal_mixed_restart_finite_canonical W hW hI hPure E μ hμ hDom hOld hBound
    C π hπ hHigh q hq hqμ S hCap hCan hNative

end
end Hironaka.HironakaG8OccupiedAtlasRestart
