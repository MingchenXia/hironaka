import Hironaka.Resolution.HironakaG8NativeRelativeClearing
import Hironaka.Resolution.HironakaG8ProfileOpenProtection
import Hironaka.Resolution.HironakaG8CompactNativeFirstStep
import Hironaka.Resolution.HironakaG8DenseBoundaryRestart
import Hironaka.Resolution.HironakaG8RelativeLexInduction

/-! Produce the finite native phase at the attained highest singular
profile over any compact base task. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators

namespace Hironaka.HironakaG8NativeRelativePhase

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaG8NativeRelativeClearing HironakaG8ProfileOpenProtection
  HironakaG8CompactNativeFirstStep HironakaG8NativeBoundaryComparison HironakaG8DenseBoundaryRestart
  HironakaActualVanishingIntrinsicHSTransport HironakaActualWholeAmbientHSSuperlevel
  HironakaActualHistoricalOriginalSingularReference
  NormalCrossings NormalCrossingsInvariance HironakaHolomorphicJetChartInvariance
  HironakaStageCenters ResolutionInvariantSpec HironakaG11PresLineState HironakaG11PresTowerState
  HironakaG11InvBMClass HironakaG8LocalHistory HironakaG11InvCommonMark
  HironakaActualPowerBoundaryExponents CanonicalCentres HironakaG1OriginalInvariantClassFunctorial
  RestrictEmptyTower StrictTransformComposition HironakaG8RelativeLexInduction

variable {n : ℕ} {X : CMfd.{0} n}

local notation "HS[" A "]" => hilbertSamuelAt (vanishingIdeal (n := n) A)
private abbrev original {A : CMfd.{0} n} (W : Set A) (E : List (Set A)) : MarkedIdeal n A :=
  ⟨univ,E,vanishingIdeal (n := n) W,1⟩

/-- The highest actual singular profile over a compact set can be cleared
by a finite full-boundary native tower on a single neighborhood. The
retained native charts are terminal and the centres are supported over
the actual original profile. -/
theorem exists_finite_relative_native_phase_with_maximal_stages (hn : 0 < n)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    (K : Set X) (hK : IsCompact K) (a : X) (ha : a ∈ K ∩ singularSet (n := n) W)
    (hHighest : ∀ x ∈ K ∩ singularSet (n := n) W, toLex (HS[W] x) ≤ toLex (HS[W] a)) :
    ∃ (I : Type) (U : Opens X), K ⊆ U ∧ ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      let W₀ := (Subtype.val : U → X) ⁻¹' W
      let E₀ := E.map ((Subtype.val : U → X) ⁻¹' ·)
      let W₁ := strictTransform n T.proj W₀
      let D₀ : Set U := {x | HS[W₀] x = HS[W] a}
      IsGeoTestTower (original W₀ E₀) T ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W₀)) T ∧
      (∀ z ℓ, HS[W₁] z ℓ ≤ HS[W₀] (T.proj z) ℓ) ∧
      (∀ z, HS[W₀] (T.proj z) = HS[W] a → toLex (HS[W₁] z) < toLex (HS[W] a)) ∧
      CentresOver D₀ T ∧ TerminalWindowsRemembering True I (canonicalInvariant n) T W₀ D₀ E₀ (HS[W] a) := by
  classical
  let H := HS[W] a
  let D : Set X := {x | ∀ ℓ, HS[W] x ℓ = H ℓ}
  let C := singularSet (n := n) W ∩ actualWholeAmbientHSSuperlevel (vanishingIdeal (n := n) W) H
  let F := K ∩ D
  have hDS : D ⊆ singularSet (n := n) W :=
    actual_original_singular_profile_locus_subset_current_singular W hW a ha.2 W hW
  have hDC : D ⊆ C := fun x hx => ⟨hDS hx, fun ℓ => (hx ℓ).ge⟩
  have hC : IsClosed C := (isClosed_singularSet hW.isClosed).inter
    (isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel _
      (CartanIrreducible.cartanCoherence W hW) H).isClosed
  have hCD (x : X) (hx : x ∈ C) (hBound : toLex (HS[W] x) ≤ toLex H) : x ∈ D :=
    fun ℓ => congrFun (congrArg ofLex (le_antisymm hBound (Pi.toLex_monotone hx.2))) ℓ
  have hF : IsCompact F := by
    have hEq : F = K ∩ C := by
      ext x
      exact ⟨fun hx => ⟨hx.1,hDC hx.2⟩, fun hx => ⟨hx.1,hCD x hx.2 (hHighest x ⟨hx.1,hx.2.1⟩)⟩⟩
    rw [hEq]
    exact hK.inter_right hC
  have hWindows (x : F) : ∃ (U : Opens X), x.val ∈ U ∧
      ∃ (P : MarkedIdeal n (CMfd.of (n := n) U)), IsInvDomain n P ∧
        NativeHSState P ((Subtype.val : U → X) ⁻¹' W) H ∧
        P.E = E.map ((Subtype.val : U → X) ⁻¹' ·) := by
    obtain ⟨U,hxU,_,P,hP,_,hS⟩ :=
      exists_native_state_on_ambient_open W hW x.val (hDS x.property.2) ⊤ (mem_univ _)
    have hxH : HS[W] x.val = H := funext x.property.2
    rw [hxH] at hS
    have hUE : IsSNCDivisor n (E.map ((Subtype.val : U → X) ⁻¹' ·)) :=
      isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
    exact ⟨U,hxU,{P with E := E.map ((Subtype.val : U → X) ⁻¹' ·)},
      (native_state_with_snc_boundary P hP hS _ hUE).1,
      (native_state_with_snc_boundary P hP hS _ hUE).2.1,rfl⟩
  choose V hHere P₀ hP₀ hS₀ hP₀E using hWindows
  have hBigCover : F ⊆ ⋃ x : F, (V x : Set X) := fun x hx =>
    mem_iUnion.mpr ⟨⟨x,hx⟩,hHere ⟨x,hx⟩⟩
  obtain ⟨s,hSmallCover⟩ :=
    hF.elim_finite_subcover (fun x : F => (V x : Set X)) (fun x => (V x).isOpen) hBigCover
  let I := {x : F // x ∈ s}
  let U : I → Opens X := fun i => V i.val
  let P (i : I) := P₀ i.val
  let V₀ : Set X := ⋃ i : I, (U i : Set X)
  have hV : IsOpen V₀ := isOpen_iUnion (fun i : I => (U i).isOpen)
  have hFCover : F ⊆ V₀ := by
    intro x hx
    obtain ⟨i,hi,hix⟩ := mem_iUnion₂.mp (hSmallCover hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,hix⟩
  obtain ⟨L,hKL,_,hL⟩ := exists_open_singular_hs_profile_upper_bound
    (p := (id : X → X)) isProperMap_id hW H K ⊤ (subset_univ K) hHighest
  let O : Opens X := L ⊓ ⟨(C \ V₀)ᶜ,(hC.inter hV.isClosed_compl).isOpen_compl⟩
  have hKO : K ⊆ O := by
    intro x hx
    refine ⟨hKL hx,?_⟩
    rintro ⟨hCx,hnV⟩
    exact hnV (hFCover ⟨hx,hCD x hCx (hHighest x ⟨hx,hCx.1⟩)⟩)
  have hOD : ∀ x ∈ D ∩ (O : Set X), ∃ i, x ∈ U i := by
    intro x hx
    apply mem_iUnion.mp
    by_contra hnV
    exact hx.2.2 ⟨hDC hx.1,hnV⟩
  let d := ∏ i : I, (P i).d
  let e (i : I) := d / (P i).d
  have hd : 0 < d := prodMark_pos (fun i : I => (P i).d) (fun i => (hP₀ i.val).one_le_d)
  have hDiv (i : I) : (P i).d ∣ d := dvd_prodMark (fun i : I => (P i).d) i
  let A : NativeWindows X I W E H (D ∩ (O : Set X)) :=
    ⟨U,P,fun i => hP₀ i.val, fun i => hS₀ i.val, fun i => hP₀E i.val,
      e,fun i => one_le_div_of_dvd hd (hDiv i),d,fun i => powerMarked_div_d (P i) (hDiv i),hOD⟩
  let W₀ := (Subtype.val : O → X) ⁻¹' W
  let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
  let D₀ := (Subtype.val : O → X) ⁻¹' D
  let K₀ := (Subtype.val : O → X) ⁻¹' K
  have hBase : (Subtype.val : O → X) ⁻¹' (D ∩ (O : Set X)) = D₀ := by
    ext x
    change x.val ∈ D ∧ x.val ∈ O ↔ x.val ∈ D
    exact ⟨And.left,fun hx => ⟨hx,x.property⟩⟩
  let A₀ : NativeWindows (CMfd.of (n := n) O) I W₀ E₀ H D₀ :=
    hBase ▸ A.restrictAmbient O
  have hW₀ : IsComplexAnalyticSubset (n := n) W₀ :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hW
  have hE₀ : IsSNCDivisor n E₀ :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hE
  have hK₀ : IsCompact K₀ :=
    (Topology.IsInducing.subtypeVal.isCompact_preimage_iff (fun x hx => ⟨⟨x,hKO hx⟩,rfl⟩)).mpr hK
  have hD₀ : IsClosed D₀ := by
    have hEq : D₀ = (Subtype.val : O → X) ⁻¹' C := by
      ext x
      change x.val ∈ D ↔ x.val ∈ C
      exact ⟨fun hx => hDC hx,fun hx => hCD x.val hx (hL x.val ⟨x.property.1,hx.1⟩)⟩
    rw [hEq]
    exact hC.preimage continuous_subtype_val
  have hExact₀ : D₀ = {x | ∀ ℓ, HS[W₀] x ℓ = H ℓ} := by
    ext x
    change (∀ ℓ, HS[W] x.val ℓ = H ℓ) ↔ ∀ ℓ, HS[(Subtype.val : O → X) ⁻¹' W] x ℓ = H ℓ
    rw [funext (hilbertSamuelAt_vanishing_actual_open_any O W x)]
  have hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W := by
    have hOrig := boundary_noncontainment_at_current_singular_of_dense_complement hn hW E hE hDense
      (BlowupTower.refl : BlowupTower X X) trivial trivial
    have hSing : ∀ B ∈ E, ∀ x ∈ singularSet (n := n) W, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W := by
      simpa only [geoTransformAlong_refl, BlowupTower.proj_refl, strictTransform_id hW.isClosed] using hOrig
    exact fun B hB x hx => hSing B hB x (hDS hx)
  have hNot₀ : ∀ B ∈ E₀, ∀ x ∈ D₀, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W₀ := by
    intro B hB x hx hxB hNear
    obtain ⟨B₁,hB₁,rfl⟩ := List.mem_map.mp hB
    apply hNot B₁ hB₁ x.val hx hxB
    rw [← O.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq x, Filter.eventually_map]
    exact hNear
  let R : BMInvariant.{0,0} n (fun {A} P Q => LocWPEquiv (X := A) P Q) n (ValTy n) :=
    ⟨canonicalInvariant n, classFunctorialFor_canonicalInvariant n⟩
  have hA := exists_finite_native_clearing_remembering hn R hW₀ hE₀ hD₀ hExact₀ hK₀ hNot₀ A₀
  have hClearing := ClearedOverRemembering.of_restrict R.toResolutionInvariant O hKO hA
  obtain ⟨U,hKU,Y,T,hTest,hStage,hBound,hDrop,hOver,hNative⟩ := hClearing.exists_literal_open hW
  have hD' : (Subtype.val : U → X) ⁻¹' D =
      {x | HS[(Subtype.val : U → X) ⁻¹' W] x = H} := by
    ext x
    change (∀ ℓ, HS[W] x.val ℓ = H ℓ) ↔ HS[(Subtype.val : U → X) ⁻¹' W] x = H
    rw [funext (hilbertSamuelAt_vanishing_actual_open_any U W x)]
    exact ⟨funext,fun h ℓ => congrFun h ℓ⟩
  rw [hD'] at hDrop hOver hNative
  exact ⟨I,U,hKU,Y,T,hTest,hStage,hBound,fun z hz => hDrop z hz,hOver,hNative⟩

/-- The geometric phase interface also retains the literal terminal native
records. The simultaneous stage data are available in the stronger form. -/
theorem exists_finite_relative_native_phase (hn : 0 < n)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    (K : Set X) (hK : IsCompact K) (a : X) (ha : a ∈ K ∩ singularSet (n := n) W)
    (hHighest : ∀ x ∈ K ∩ singularSet (n := n) W, toLex (HS[W] x) ≤ toLex (HS[W] a)) :
    ∃ (I : Type) (U : Opens X), K ⊆ U ∧ ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      let W₀ := (Subtype.val : U → X) ⁻¹' W
      let E₀ := E.map ((Subtype.val : U → X) ⁻¹' ·)
      let W₁ := strictTransform n T.proj W₀
      let D₀ : Set U := {x | HS[W₀] x = HS[W] a}
      IsGeoTestTower (original W₀ E₀) T ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W₀)) T ∧
      (∀ z ℓ, HS[W₁] z ℓ ≤ HS[W₀] (T.proj z) ℓ) ∧
      (∀ z, HS[W₀] (T.proj z) = HS[W] a → toLex (HS[W₁] z) < toLex (HS[W] a)) ∧
      CentresOver D₀ T ∧ TerminalWindows I (canonicalInvariant n) T W₀ D₀ E₀ (HS[W] a) := by
  obtain ⟨I,U,hKU,Y,T,hTest,hStage,hBound,hDrop,hOver,S,hS,_⟩ :=
    exists_finite_relative_native_phase_with_maximal_stages hn hW E hE hDense K hK a ha hHighest
  exact ⟨I,U,hKU,Y,T,hTest,hStage,hBound,hDrop,hOver,S,hS⟩

/-- Supply the relative singular phase service used by lexicographic
induction on the actual singular Hilbert--Samuel profile. -/
theorem has_relative_singular_phases (hn : 0 < n) : HasRelativeSingularPhases n := by
  intro X W hW E hE hDense K hK a ha hHighest
  obtain ⟨I,U,hKU,Y,T,hTest,hStage,hBound,hDrop,_,_⟩ :=
    exists_finite_relative_native_phase hn hW E hE hDense K hK a ha hHighest
  exact ⟨U,hKU,Y,T,hTest,hStage,hBound,hDrop⟩

/-- One finite physical tower on a neighborhood of any compact base set
smooths the strict transform, with the original full boundary retained
and every centre in the current intrinsic singular locus. -/
theorem exists_native_singular_resolution_near_compact (hn : 0 < n)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) O) Y),
      let W₀ := (Subtype.val : O → X) ⁻¹' W
      let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
      IsGeoTestTower (original W₀ E₀) T ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W₀)) T ∧
      IsClosedSubmanifold n (strictTransform n T.proj W₀) :=
  exists_singular_resolution_near_compact_of_relative_phases
    (has_relative_singular_phases hn) hW E hE hDense K hK

end
end Hironaka.HironakaG8NativeRelativePhase
