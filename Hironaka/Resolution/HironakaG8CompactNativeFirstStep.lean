import Hironaka.Resolution.HironakaG8NativeGlobalSuccessor
import Hironaka.Resolution.HironakaG8NativeNumericalOverlap
import Hironaka.Resolution.HironakaUniformHistoricalSuccessorCompactSingular
import Hironaka.Resolution.HironakaG11PresNativeStateWindow
import Hironaka.Resolution.HironakaG8OpenHoloEmbeddingComposition
import Hironaka.Resolution.HironakaG1OriginalInvariantClassFunctorial

/-! A compact singular Hilbert–Samuel stratum produces one actual blowup
whose restrictions are the common maximum of genuine native records. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators

namespace Hironaka.HironakaG8CompactNativeFirstStep

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance NormalCrossings
  NormalCrossingsInvariance HironakaG11PresLineState HironakaG8NativeBoundaryComparison
  HironakaG8NativeNumericalOverlap HironakaG8NativeGlobalSuccessor
  HironakaUniformHistoricalSuccessorCompactSingular HironakaG11PresNativeStateWindow
  HironakaG8OpenHoloEmbeddingComposition HironakaBaseChange MarkedIdealTowerTransport
  HironakaG11PresNativePhase MarkedIdealBiholomorphism
  HironakaActualVanishingIntrinsicHSTransport HironakaActualPowerBoundaryExponents
  HironakaG11InvCommonMark CanonicalCentres HironakaG1OriginalInvariantClassFunctorial

variable {n : ℕ} {X : CMfd.{0} n} {Λ : Type} [LinearOrder Λ]

/-- A singular point admits a genuine native record directly on an actual
ambient open inside the prescribed neighbourhood. -/
theorem exists_native_state_on_ambient_open
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (a : X) (ha : a ∈ singularSet (n := n) W) (U₀ : Opens X) (haU : a ∈ U₀) :
    ∃ (D : Opens X), a ∈ D ∧ (D : Set X) ⊆ U₀ ∧
      ∃ (P : MarkedIdeal n (CMfd.of (n := n) D)), IsInvDomain n P ∧ P.E = [] ∧
        NativeHSState P ((Subtype.val : D → X) ⁻¹' W)
          (hilbertSamuelAt (vanishingIdeal (n := n) W) a) := by
  obtain ⟨U, V, η, O, hOU, z, Q, hz, hInside, hQ, hQE, hState⟩ :=
    exists_native_state_phase_window W hW a ha U₀ U₀.isOpen haU
  let f : opensIn U O → X := fun x => (η x.val : X)
  have hf : IsOpenHoloEmbedding n f :=
    isOpenHoloEmbedding_comp (A := X) (B := CMfd.of (n := n) U) (C := CMfd.of (n := n) (opensIn U O))
      (⟨V, η, fun _ => rfl⟩ : IsOpenHoloEmbedding n (fun x : U => (η x : X)))
      (isOpenHoloEmbedding_val (opensIn U O))
  obtain ⟨D, e, he⟩ := hf
  let z₁ : opensIn U O := ⟨Opens.inclusion hOU z, z.property⟩
  have hfa : f z₁ = a := hz
  have haD : a ∈ D := by
    rw [← hfa, he]
    exact (e z₁).property
  have hDU : (D : Set X) ⊆ U₀ := by
    intro x hx
    let y := e.symm ⟨x, hx⟩
    have hfy : f y = x := by rw [he, e.apply_symm_apply]
    rw [← hfy]
    exact hInside ⟨(y.val : U).val, y.property⟩
  let P := MarkedIdeal.pullback e.symm Q
  have hP : IsInvDomain n P := InvDomainTowerAlong.isInvDomain_pullback e.symm hQ
  have hPE : P.E = [] := by
    change Q.E.map (e.symm ⁻¹' ·) = []
    rw [hQE]
    rfl
  have hSet : e.symm ⁻¹' (f ⁻¹' W) = (Subtype.val : D → X) ⁻¹' W := by
    ext x
    change f (e.symm x) ∈ W ↔ x.val ∈ W
    rw [he, e.apply_symm_apply]
  refine ⟨D, haD, hDU, P, hP, hPE, ?_⟩
  rw [← hSet]
  exact NativeHSState.pullback (X := CMfd.of (n := n) (opensIn U O))
    (X' := CMfd.of (n := n) D) e.symm hState

/-- The genuine native records on a finite ambient cover of the entire
compact maximal singular profile, normalized at one positive mark, supply
a global centre on the full boundary. Every local trace is the cut of the
same attained numerical maximum. -/
theorem exists_compact_native_first_step_of_compact_singular (hn : 0 < n)
    (R : BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) n Λ)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact (singularSet (n := n) W))
    (hns : ¬ IsClosedSubmanifold n W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hNot : ∀ D ∈ E, ∀ x ∈ singularSet (n := n) W, x ∈ D →
      ¬ ∀ᶠ z in 𝓝 x, z ∈ D → z ∈ W) :
    ∃ (a : X) (ι : Type) (U : ι → Opens X)
      (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i))) (e : ι → ℕ) (d : ℕ)
      (m : Λ) (C : Set X) (Y : CMfd.{0} n) (π : Y → X) (hπ : IsBlowupAlong n C π),
      a ∈ singularSet (n := n) W ∧
      (∀ x ∈ singularSet (n := n) W, toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) x) ≤
        toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) a)) ∧
      Finite ι ∧
      let H := hilbertSamuelAt (vanishingIdeal (n := n) W) a
      (∀ i, IsInvDomain n (P i) ∧
        NativeHSState (P i) ((Subtype.val : U i → X) ⁻¹' W) H ∧
        (P i).E = E.map ((Subtype.val : U i → X) ⁻¹' ·) ∧
        1 ≤ e i ∧ (powerMarked (P i) (e i)).d = d) ∧
      (∀ x : X, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ) →
        ∃ i, x ∈ U i) ∧
      (∀ i (x : U i), x ∈ (powerMarked (P i) (e i)).cosupp →
        R.toResolutionInvariant.inv (powerMarked (P i) (e i)) .refl x ≤ m) ∧
      C.Nonempty ∧ C ⊆ singularSet (n := n) W ∧ IsProperMap π ∧
      IsGeoTestTower (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)
        (.step .refl C π hπ) ∧
      (∀ i, (Subtype.val : U i → X) ⁻¹' C =
        {x | x ∈ (powerMarked (P i) (e i)).cosupp ∧
          R.toResolutionInvariant.inv (powerMarked (P i) (e i)) .refl x = m}) ∧
      (∀ x ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ) ∧
      (∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) z ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (π z) ℓ) := by
  classical
  obtain ⟨a, ha, hTop, hNe, _hAnalytic, hCompact, _hThin, hExact, U₀, hDWindow, _hUpper, _hSuper⟩ :=
    exists_compact_singular_maximal_stratum_of_compact_singular hW hK hns
  let H := hilbertSamuelAt (vanishingIdeal (n := n) W) a
  let F : Set X := {x | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ}
  have hFNe : F.Nonempty := by
    dsimp only [F, H]
    rw [← hExact]
    exact hNe
  have hFCompact : IsCompact F := by
    dsimp only [F, H]
    rw [← hExact]
    exact hCompact
  have hFSing : F ⊆ singularSet (n := n) W :=
    HironakaActualHistoricalOriginalSingularReference.actual_original_singular_profile_locus_subset_current_singular
      W hW a ha W hW
  have hWindows (x : F) : ∃ (U : Opens X), x.val ∈ U ∧
      ∃ (P : MarkedIdeal n (CMfd.of (n := n) U)), IsInvDomain n P ∧
        NativeHSState P ((Subtype.val : U → X) ⁻¹' W) H ∧
        P.E = E.map ((Subtype.val : U → X) ⁻¹' ·) := by
    have hx0 : x.val ∈ U₀ := (hExact ▸ hDWindow) x.property
    obtain ⟨U, hxU, _, P, hP, _, hS⟩ :=
      exists_native_state_on_ambient_open W hW x.val (hFSing x.property) U₀ hx0
    have hxH : hilbertSamuelAt (vanishingIdeal (n := n) W) x.val = H :=
      funext x.property
    rw [hxH] at hS
    have hUE : IsSNCDivisor n (E.map ((Subtype.val : U → X) ⁻¹' ·)) :=
      isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
    exact ⟨U, hxU, { P with E := E.map ((Subtype.val : U → X) ⁻¹' ·) },
      (native_state_with_snc_boundary P hP hS _ hUE).1,
      (native_state_with_snc_boundary P hP hS _ hUE).2.1, rfl⟩
  choose O hHere P₀ hP₀ hS₀ hE₀ using hWindows
  have hBigCover : F ⊆ ⋃ x : F, (O x : Set X) := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, hHere ⟨x, hx⟩⟩
  obtain ⟨s, hSmallCover⟩ :=
    hFCompact.elim_finite_subcover (fun x : F => (O x : Set X)) (fun x => (O x).isOpen) hBigCover
  let ι := {x : F // x ∈ s}
  let U : ι → Opens X := fun i => O i.val
  let P (i : ι) : MarkedIdeal n (CMfd.of (n := n) (U i)) := P₀ i.val
  have hP (i : ι) : IsInvDomain n (P i) := hP₀ i.val
  have hS (i : ι) : NativeHSState (P i) ((Subtype.val : U i → X) ⁻¹' W) H := hS₀ i.val
  have hPE (i : ι) : (P i).E = E.map ((Subtype.val : U i → X) ⁻¹' ·) := hE₀ i.val
  have hCover : ∀ x ∈ F, ∃ i : ι, x ∈ U i := by
    intro x hx
    obtain ⟨i, hi, hxI⟩ := mem_iUnion₂.mp (hSmallCover hx)
    exact ⟨⟨i, hi⟩, hxI⟩
  let d := ∏ i : ι, (P i).d
  let e (i : ι) := d / (P i).d
  have hd : 0 < d := prodMark_pos (fun i : ι => (P i).d) (fun i => (hP i).one_le_d)
  have hDiv (i : ι) : (P i).d ∣ d := dvd_prodMark (fun j : ι => (P j).d) i
  have he (i : ι) : 1 ≤ e i := one_le_div_of_dvd hd (hDiv i)
  let Q (i : ι) := powerMarked (P i) (e i)
  have hMark (i : ι) : (Q i).d = d := powerMarked_div_d (P i) (hDiv i)
  have hQ (i : ι) : IsInvDomain n (Q i) := powerMarked_isInvDomain (P i) (hP i) (he i)
  have hCos (i : ι) : (Q i).cosupp = (Subtype.val : U i → X) ⁻¹' F := by
    rw [show (Q i).cosupp = (P i).cosupp from powerMarked_cosupp (P i) (hP i) (he i), (hS i).cosupp_eq]
    ext x
    constructor
    · intro hx ℓ
      exact (hilbertSamuelAt_vanishing_actual_open_any (n := n) (U i) W x ℓ).symm.trans (hx ℓ)
    · intro hx ℓ
      exact (hilbertSamuelAt_vanishing_actual_open_any (n := n) (U i) W x ℓ).trans (hx ℓ)
  have hCoverCos : ∀ x ∈ F, ∃ (i : ι) (hx : x ∈ U i), (⟨x, hx⟩ : U i) ∈ (Q i).cosupp := by
    intro x hx
    obtain ⟨i, hxI⟩ := hCover x hx
    exact ⟨i, hxI, (hCos i).symm ▸ hx⟩
  have hFoot (i : ι) (x : U i) (hx : x ∈ (Q i).cosupp) : x.val ∈ F := by
    rw [hCos i] at hx
    exact hx
  have hOverlap (i j : ι) (x : X) (hi : x ∈ U i) (hj : x ∈ U j)
      (hx : (⟨x, hi⟩ : U i) ∈ (Q i).cosupp) :
      (⟨x, hj⟩ : U j) ∈ (Q j).cosupp ∧
      R.toResolutionInvariant.inv (Q i) .refl ⟨x, hi⟩ =
        R.toResolutionInvariant.inv (Q j) .refl ⟨x, hj⟩ := by
    have hxP : (⟨x, hi⟩ : U i) ∈ (P i).cosupp :=
      powerMarked_cosupp (P i) (hP i) (he i) ▸ hx
    have hNotI (D : Set X) (hD : D ∈ E) (y : U i) (hy : y ∈ (P i).cosupp) (hyD : y.val ∈ D) :=
      hNot D hD y.val (hFSing (hFoot i y ((powerMarked_cosupp (P i) (hP i) (he i)).symm ▸ hy))) hyD
    obtain ⟨hxJ, hVal⟩ := native_window_initial_values_agree hn R (U i) (U j) (P i) (P j)
      (hP i) (hP j) W H (hS i) (hS j) E (hPE i) (hPE j) (e i) (e j)
      (he i) (he j) ((hMark i).trans (hMark j).symm) hNotI hi hj hxP
    exact ⟨(powerMarked_cosupp (P j) (hP j) (he j)).symm ▸ hxJ, hVal⟩
  obtain ⟨m, hM, hAttain⟩ := exists_actual_native_compact_maximum
    R.toResolutionInvariant U F hFCompact hFNe Q hQ hCoverCos hFoot hOverlap
  obtain ⟨C, Y, π, hπ, hCne, _hCF, hCS, hProper, hT, hTrace, hHS, hLe⟩ :=
    exists_actual_native_global_maximum_blowup R.toResolutionInvariant hW E U F hFCompact.isClosed
      hCover Q hQ hPE H (fun i x hx => ⟨hFSing (hFoot i x hx), hFoot i x hx⟩) hFoot
      hOverlap m hM hAttain
  exact ⟨a, ι, U, P, e, d, m, C, Y, π, hπ, ha, hTop, inferInstance,
    fun i => ⟨hP i, hS i, hPE i, he i, hMark i⟩, hCover, hM, hCne, hCS, hProper, hT, hTrace, hHS, hLe⟩

/-- The first simultaneous native step for a compact analytic carrier. -/
theorem exists_compact_native_first_step (hn : 0 < n)
    (R : BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) n Λ)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W)
    (hns : ¬ IsClosedSubmanifold n W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hNot : ∀ D ∈ E, ∀ x ∈ singularSet (n := n) W, x ∈ D →
      ¬ ∀ᶠ z in 𝓝 x, z ∈ D → z ∈ W) :
    ∃ (a : X) (ι : Type) (U : ι → Opens X)
      (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i))) (e : ι → ℕ) (d : ℕ)
      (m : Λ) (C : Set X) (Y : CMfd.{0} n) (π : Y → X) (hπ : IsBlowupAlong n C π),
      a ∈ singularSet (n := n) W ∧
      (∀ x ∈ singularSet (n := n) W, toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) x) ≤
        toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) a)) ∧
      Finite ι ∧
      let H := hilbertSamuelAt (vanishingIdeal (n := n) W) a
      (∀ i, IsInvDomain n (P i) ∧
        NativeHSState (P i) ((Subtype.val : U i → X) ⁻¹' W) H ∧
        (P i).E = E.map ((Subtype.val : U i → X) ⁻¹' ·) ∧
        1 ≤ e i ∧ (powerMarked (P i) (e i)).d = d) ∧
      (∀ x : X, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ) →
        ∃ i, x ∈ U i) ∧
      (∀ i (x : U i), x ∈ (powerMarked (P i) (e i)).cosupp →
        R.toResolutionInvariant.inv (powerMarked (P i) (e i)) .refl x ≤ m) ∧
      C.Nonempty ∧ C ⊆ singularSet (n := n) W ∧ IsProperMap π ∧
      IsGeoTestTower (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)
        (.step .refl C π hπ) ∧
      (∀ i, (Subtype.val : U i → X) ⁻¹' C =
        {x | x ∈ (powerMarked (P i) (e i)).cosupp ∧
          R.toResolutionInvariant.inv (powerMarked (P i) (e i)) .refl x = m}) ∧
      (∀ x ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ) ∧
      (∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) z ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (π z) ℓ) := by
  exact exists_compact_native_first_step_of_compact_singular hn R hW
    (hK.of_isClosed_subset (isClosed_singularSet hW.isClosed) (singularSet_subset _)) hns E hE hNot

/-- For a compact singular analytic set with empty initial boundary, the
literal original invariant produces the first simultaneous native step. -/
theorem exists_compact_native_first_step_empty_boundary (hn : 0 < n)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W)
    (hns : ¬ IsClosedSubmanifold n W) :
    ∃ (a : X) (ι : Type) (U : ι → Opens X)
      (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i))) (e : ι → ℕ) (d : ℕ)
      (m : ValTy n) (C : Set X) (Y : CMfd.{0} n) (π : Y → X) (hπ : IsBlowupAlong n C π),
      a ∈ singularSet (n := n) W ∧
      (∀ x ∈ singularSet (n := n) W, toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) x) ≤
        toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) a)) ∧
      Finite ι ∧
      let H := hilbertSamuelAt (vanishingIdeal (n := n) W) a
      (∀ i, IsInvDomain n (P i) ∧
        NativeHSState (P i) ((Subtype.val : U i → X) ⁻¹' W) H ∧
        (P i).E = [] ∧
        1 ≤ e i ∧ (powerMarked (P i) (e i)).d = d) ∧
      (∀ x : X, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ) →
        ∃ i, x ∈ U i) ∧
      (∀ i (x : U i), x ∈ (powerMarked (P i) (e i)).cosupp →
        (canonicalInvariant.{0} n).inv (powerMarked (P i) (e i)) .refl x ≤ m) ∧
      C.Nonempty ∧ C ⊆ singularSet (n := n) W ∧ IsProperMap π ∧
      IsGeoTestTower (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)
        (.step .refl C π hπ) ∧
      (∀ i, (Subtype.val : U i → X) ⁻¹' C =
        {x | x ∈ (powerMarked (P i) (e i)).cosupp ∧
          (canonicalInvariant.{0} n).inv (powerMarked (P i) (e i)) .refl x = m}) ∧
      (∀ x ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ) ∧
      (∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) z ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (π z) ℓ) := by
  let R : BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) n (ValTy n) :=
    ⟨canonicalInvariant n, classFunctorialFor_canonicalInvariant n⟩
  exact exists_compact_native_first_step hn R hW hK hns [] isSNCDivisor_nil
    (fun _ hD => False.elim (List.not_mem_nil hD))

end
end Hironaka.HironakaG8CompactNativeFirstStep
