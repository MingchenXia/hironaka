import Hironaka.Resolution.HironakaG8NativeCompactShrink
import Hironaka.Resolution.HironakaG8NativePrefixWindowRestriction
import Hironaka.Resolution.HironakaG8FiniteSingularTowerMerge
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport

/-! The actual one-step native successor after a shrink around a compact
base task. All comparisons retain the same restricted ambient prefix. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativeRelativeSuccessor

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance
  NormalCrossings HironakaStageCenters MaxLocusLocal HironakaOriginalTerminalOverlapComparison
  HironakaG8NativeCompactShrink HironakaG8NativePrefixWindowRestriction HironakaG8FiniteSingularTowerMerge
  HironakaActualVanishingIntrinsicHSTransport HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaResolutionSpaceLocal HironakaEmbeddedBoundary NormalCrossingsInvariance HironakaBaseChange
  HironakaG8NativeSimultaneousCentre

variable {n k : ℕ} {X Y : CMfd.{0} n} {I Λ : Type} [LinearOrder Λ]

/-- If actual native windows along a canonical prefix agree on the closed
active support, a compact task meeting that support determines an actual
canonical next step over a shrunk base open. The same restricted prefix and
every original boundary slot are retained. -/
theorem exists_relative_native_successor_with_cut
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T)
    (hStage : StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T)
    (U : I → Opens X) (F : Set Y) (hF : IsClosed F)
    {K : Set X} (hK : IsCompact K) (hNe : (F ∩ T.proj ⁻¹' K).Nonempty)
    (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i))) (hP : ∀ i, IsInvDomain k (P i))
    (hCan : ∀ i, IsCanonical (P i) (R.inv (P i)) (restrict (U i) T))
    (hETrace : ∀ i, (geoTransformAlong (P i) (restrict (U i) T)).E =
      (geoTransformAlong (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T).E.map
        ((Subtype.val : openPreimage T (U i) → Y) ⁻¹' ·))
    (H : ℕ → ℕ)
    (hCut : ∀ i (y : openPreimage T (U i)), y ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp →
      y.val ∈ singularSet (n := n) (strictTransform n T.proj W) ∧
        ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) y.val ℓ = H ℓ)
    (hCover : ∀ y ∈ F, ∃ (i : I) (hy : y ∈ openPreimage T (U i)),
      (⟨y, hy⟩ : openPreimage T (U i)) ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp)
    (hFoot : ∀ i (y : openPreimage T (U i)), y ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp → y.val ∈ F)
    (hOverlap : ∀ i j (y : Y) (hi : y ∈ openPreimage T (U i)) (hj : y ∈ openPreimage T (U j)),
      (⟨y, hi⟩ : openPreimage T (U i)) ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp →
      (⟨y, hj⟩ : openPreimage T (U j)) ∈ (geoTransformAlong (P j) (restrict (U j) T)).cosupp ∧
        R.inv (P i) (restrict (U i) T) ⟨y, hi⟩ = R.inv (P j) (restrict (U j) T) ⟨y, hj⟩) :
    ∃ (m : Λ) (O : Opens X), K ⊆ O ∧
      (∃ (i : I) (y : openPreimage T (U i)), y ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp ∧
        T.proj y.val ∈ K ∧ R.inv (P i) (restrict (U i) T) y = m) ∧
      let W₀ := (Subtype.val : O → X) ⁻¹' W
      let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
      let T₀ := restrict O T
      let L (i : I) := O ⊓ U i
      let U₀ (i : I) := nestedOpens O (L i)
      let P₀ (i : I) : MarkedIdeal n (CMfd.of (n := n) (U₀ i)) :=
        MarkedIdeal.pullback
          (overlapBaseEquiv (n := n) (show L i ≤ O from inf_le_left) (show L i ≤ U i from inf_le_right))
          (MarkedIdeal.pullback (Subtype.val : nestedOpens (U i) (L i) → U i) (P i))
      ∃ (C : Set (openPreimage T O)) (Z : CMfd.{0} n) (π : Z → openPreimage T O)
        (hπ : IsBlowupAlong n C π),
        let S := BlowupTower.step T₀ C π hπ
        C.Nonempty ∧ C ⊆ (Subtype.val : openPreimage T O → Y) ⁻¹' F ∧ IsProperMap π ∧
        IsGeoTestTower (⟨univ,E₀,vanishingIdeal (n := n) W₀,1⟩ : MarkedIdeal n (CMfd.of (n := n) O)) S ∧
        StageCentres (fun B D => D ⊆ singularSet (n := n) (strictTransform n B.proj W₀)) S ∧
        (∀ i, IsInvDomain k (P₀ i) ∧ IsCanonical (P₀ i) (R.inv (P₀ i)) (restrict (U₀ i) S) ∧
          ∀ z ∈ (geoTransformAlong (P₀ i) (restrict (U₀ i) S)).cosupp,
            R.inv (P₀ i) (restrict (U₀ i) S) z < m) ∧
        (∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π (strictTransform n T₀.proj W₀))) z ℓ ≤
          hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T₀.proj W₀)) (π z) ℓ) ∧ NativeSimultaneousCentre R U₀ P₀ T₀ C m := by
  classical
  let S (i : I) := restrict (U i) T
  let g (i : I) := R.inv (P i) (S i)
  let B (i : I) := (geoTransformAlong (P i) (S i)).cosupp
  obtain ⟨m, O, hKO, hBound, i₀, y₀, hy₀, hProj₀, hVal₀⟩ :=
    exists_saturated_maximum_window (HironakaLocalPrincipalization.isProperMap_proj T)
      hK (openPreimage T ∘ U) F hF hNe B g
      (fun i => R.isInvValue.usc (P i) (hP i) (S i) (hCan i))
      hCover hFoot hOverlap
  refine ⟨m, O, hKO, ⟨i₀, y₀, hy₀, hProj₀, hVal₀⟩, ?_⟩
  let W₀ := (Subtype.val : O → X) ⁻¹' W
  let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
  let T₀ := restrict O T
  let L (i : I) := O ⊓ U i
  let U₀ (i : I) := nestedOpens O (L i)
  let P₀ (i : I) : MarkedIdeal n (CMfd.of (n := n) (U₀ i)) :=
    MarkedIdeal.pullback
      (overlapBaseEquiv (n := n) (show L i ≤ O from inf_le_left) (show L i ≤ U i from inf_le_right))
      (MarkedIdeal.pullback (Subtype.val : nestedOpens (U i) (L i) → U i) (P i))
  let S₀ (i : I) := restrict (U₀ i) T₀
  let B₀ (i : I) := (geoTransformAlong (P₀ i) (S₀ i)).cosupp
  let g₀ (i : I) := R.inv (P₀ i) (S₀ i)
  have hR (i : I) := native_prefix_values_on_shrunk_ambient R (U i) O (P i) (hP i) T (hCan i)
  have hDom (i : I) : IsInvDomain k (P₀ i) := (hR i).1
  have hCan₀ (i : I) : IsCanonical (P₀ i) (R.inv (P₀ i)) (S₀ i) := (hR i).2.1
  choose f hPoint hB hLocalE hValue using fun i => (hR i).2.2
  have hValue₀ (i : I) (z : openPreimage T₀ (U₀ i)) (hz : z ∈ B₀ i) :
      g₀ i z = g i (f i z) := hValue i z hz
  have hOpen (i : I) (z : openPreimage T O) :
      z ∈ openPreimage T₀ (U₀ i) ↔ z.val ∈ openPreimage T (U i) := by
    rw [mem_openPreimage_restrict_nestedOpens O (L i) T]
    exact ⟨fun hz => hz.2, fun hz => ⟨z.property, hz⟩⟩
  have hMem (i : I) (z : openPreimage T₀ (U₀ i)) : f i z ∈ B i ↔ z ∈ B₀ i := by
    change z ∈ f i ⁻¹' B i ↔ _
    rw [← hB i]
  let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
  let M₀ : MarkedIdeal n (CMfd.of (n := n) O) := ⟨univ, E₀, vanishingIdeal (n := n) W₀, 1⟩
  have hM : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hW, hE,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hMPull : MarkedIdeal.pullback (Subtype.val : O → X) M = M₀ :=
    pullback_val_mk_vanishingIdeal O E W
  have hW₀ : IsComplexAnalyticSubset (n := n) W₀ :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hW
  have hE₀ : IsSNCDivisor n E₀ :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hE
  have hT₀ : IsGeoTestTower M₀ T₀ := by
    rw [← hMPull]
    exact MarkedIdealRestrictOpen.isGeoTestTower_restrict O
      hM.isClosedSubmanifold_N hM.isCoherent T hT
  have hGeo : geoTransformAlong M₀ T₀ =
      MarkedIdeal.pullback (Subtype.val : openPreimage T O → Y) (geoTransformAlong M T) := by
    rw [← hMPull]
    exact MarkedIdealRestrictOpen.geoTransformAlong_restrict O
      hM.isClosedSubmanifold_N hM.isCoherent T hT
  have hStage₀ := singular_stages_restrict W O T hStage
  let F₀ := (Subtype.val : openPreimage T O → Y) ⁻¹' F
  have hF₀ : IsClosed F₀ := hF.preimage continuous_subtype_val
  have hCover₀ : ∀ y ∈ F₀, ∃ i, y ∈ openPreimage T₀ (U₀ i) := by
    intro y hy
    obtain ⟨i, hi, _⟩ := hCover y.val hy
    exact ⟨i, (hOpen i y).mpr hi⟩
  have hFoot₀ (i : I) (z : openPreimage T₀ (U₀ i)) (hz : z ∈ B₀ i) :
      z.val ∈ F₀ := by
    change z.val.val ∈ F
    rw [← hPoint i z]
    exact hFoot i (f i z) ((hMem i z).mpr hz)
  have hETrace₀ (i : I) : (geoTransformAlong (P₀ i) (S₀ i)).E =
      (geoTransformAlong M₀ T₀).E.map ((Subtype.val : openPreimage T₀ (U₀ i) → openPreimage T O) ⁻¹' ·) := by
    rw [hLocalE i, hETrace i, hGeo]
    change ((geoTransformAlong M T).E.map ((Subtype.val : openPreimage T (U i) → Y) ⁻¹' ·)).map
        (f i ⁻¹' ·) =
      ((geoTransformAlong M T).E.map ((Subtype.val : openPreimage T O → Y) ⁻¹' ·)).map
        ((Subtype.val : openPreimage T₀ (U₀ i) → openPreimage T O) ⁻¹' ·)
    rw [List.map_map, List.map_map]
    apply congrArg ((geoTransformAlong M T).E.map)
    funext D
    ext z
    change (f i z).val ∈ D ↔ z.val.val ∈ D
    rw [hPoint i z]
  have hCut₀ (i : I) (z : openPreimage T₀ (U₀ i)) (hz : z ∈ B₀ i) :
      z.val ∈ singularSet (n := n) (strictTransform n T₀.proj W₀) ∧
      ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T₀.proj W₀)) z.val ℓ = H ℓ := by
    have h := hCut i (f i z) ((hMem i z).mpr hz)
    rw [hPoint i z] at h
    rw [strictTransform_restricted_tower O T W, singularSet_preimage_val]
    exact ⟨h.1, fun ℓ =>
      (hilbertSamuelAt_vanishing_actual_open_any (openPreimage T O) (strictTransform n T.proj W) z.val ℓ).trans (h.2 ℓ)⟩
  have hOverlap₀ (i j : I) (y : openPreimage T O)
      (hi : y ∈ openPreimage T₀ (U₀ i)) (hj : y ∈ openPreimage T₀ (U₀ j))
      (hy : (⟨y, hi⟩ : openPreimage T₀ (U₀ i)) ∈ B₀ i) :
      (⟨y, hj⟩ : openPreimage T₀ (U₀ j)) ∈ B₀ j ∧
        g₀ i ⟨y, hi⟩ = g₀ j ⟨y, hj⟩ := by
    let zi : openPreimage T₀ (U₀ i) := ⟨y, hi⟩
    let zj : openPreimage T₀ (U₀ j) := ⟨y, hj⟩
    have hfi : f i zi = ⟨y.val, (hOpen i y).mp hi⟩ := Subtype.ext (hPoint i zi)
    have hfj : f j zj = ⟨y.val, (hOpen j y).mp hj⟩ := Subtype.ext (hPoint j zj)
    have hyi := (hMem i zi).mpr hy
    rw [hfi] at hyi
    obtain ⟨hyj, hVal⟩ := hOverlap i j y.val ((hOpen i y).mp hi) ((hOpen j y).mp hj) hyi
    have hj₀ : zj ∈ B₀ j := (hMem j zj).mp (hfj.symm ▸ hyj)
    refine ⟨hj₀, ?_⟩
    change g₀ i zi = g₀ j zj
    rw [hValue₀ i zi hy, hValue₀ j zj hj₀, hfi, hfj]
    exact hVal
  have hUpper₀ (i : I) (z : openPreimage T₀ (U₀ i)) (hz : z ∈ B₀ i) :
      g₀ i z ≤ m := by
    rw [hValue₀ i z hz]
    apply hBound i (f i z) ((hMem i z).mpr hz)
    rw [hPoint i z]
    exact z.val.property
  have hAttain₀ : ∃ (i : I) (z : openPreimage T₀ (U₀ i)), z ∈ B₀ i ∧ g₀ i z = m := by
    let y : openPreimage T O := ⟨y₀.val, hKO hProj₀⟩
    let z : openPreimage T₀ (U₀ i₀) := ⟨y, (hOpen i₀ y).mpr y₀.property⟩
    have hzEq : f i₀ z = y₀ := Subtype.ext (hPoint i₀ z)
    have hz : z ∈ B₀ i₀ := (hMem i₀ z).mp (hzEq.symm ▸ hy₀)
    exact ⟨i₀, z, hz, (hValue₀ i₀ z hz).trans (hzEq.symm ▸ hVal₀)⟩
  obtain ⟨C, Z, π, hπ, hC, hCF, hProper, hTest, hStage', hCan', hLe, hSync⟩ :=
    native_successor_at_common_maximum_with_cut R hW₀ E₀ hE₀ T₀ hT₀ hStage₀ U₀ F₀ hF₀
      hCover₀ P₀ hDom hCan₀ hETrace₀ H hCut₀ hFoot₀ hOverlap₀ m hUpper₀ hAttain₀
  exact ⟨C, Z, π, hπ, hC, hCF, hProper, hTest, hStage',
    fun i => ⟨hDom i, hCan' i⟩, hLe, hSync⟩

/-- The original shrinking successor interface. -/
theorem exists_relative_native_successor
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T)
    (hStage : StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T)
    (U : I → Opens X) (F : Set Y) (hF : IsClosed F)
    {K : Set X} (hK : IsCompact K) (hNe : (F ∩ T.proj ⁻¹' K).Nonempty)
    (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i))) (hP : ∀ i, IsInvDomain k (P i))
    (hCan : ∀ i, IsCanonical (P i) (R.inv (P i)) (restrict (U i) T))
    (hETrace : ∀ i, (geoTransformAlong (P i) (restrict (U i) T)).E =
      (geoTransformAlong (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T).E.map
        ((Subtype.val : openPreimage T (U i) → Y) ⁻¹' ·))
    (H : ℕ → ℕ)
    (hCut : ∀ i (y : openPreimage T (U i)), y ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp →
      y.val ∈ singularSet (n := n) (strictTransform n T.proj W) ∧
        ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) y.val ℓ = H ℓ)
    (hCover : ∀ y ∈ F, ∃ (i : I) (hy : y ∈ openPreimage T (U i)),
      (⟨y, hy⟩ : openPreimage T (U i)) ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp)
    (hFoot : ∀ i (y : openPreimage T (U i)), y ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp → y.val ∈ F)
    (hOverlap : ∀ i j (y : Y) (hi : y ∈ openPreimage T (U i)) (hj : y ∈ openPreimage T (U j)),
      (⟨y, hi⟩ : openPreimage T (U i)) ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp →
      (⟨y, hj⟩ : openPreimage T (U j)) ∈ (geoTransformAlong (P j) (restrict (U j) T)).cosupp ∧
        R.inv (P i) (restrict (U i) T) ⟨y, hi⟩ = R.inv (P j) (restrict (U j) T) ⟨y, hj⟩) :
    ∃ (m : Λ) (O : Opens X), K ⊆ O ∧
      (∃ (i : I) (y : openPreimage T (U i)), y ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp ∧
        T.proj y.val ∈ K ∧ R.inv (P i) (restrict (U i) T) y = m) ∧
      let W₀ := (Subtype.val : O → X) ⁻¹' W
      let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
      let T₀ := restrict O T
      let L (i : I) := O ⊓ U i
      let U₀ (i : I) := nestedOpens O (L i)
      let P₀ (i : I) : MarkedIdeal n (CMfd.of (n := n) (U₀ i)) :=
        MarkedIdeal.pullback
          (overlapBaseEquiv (n := n) (show L i ≤ O from inf_le_left) (show L i ≤ U i from inf_le_right))
          (MarkedIdeal.pullback (Subtype.val : nestedOpens (U i) (L i) → U i) (P i))
      ∃ (C : Set (openPreimage T O)) (Z : CMfd.{0} n) (π : Z → openPreimage T O)
        (hπ : IsBlowupAlong n C π),
        let S := BlowupTower.step T₀ C π hπ
        C.Nonempty ∧ C ⊆ (Subtype.val : openPreimage T O → Y) ⁻¹' F ∧ IsProperMap π ∧
        IsGeoTestTower (⟨univ,E₀,vanishingIdeal (n := n) W₀,1⟩ : MarkedIdeal n (CMfd.of (n := n) O)) S ∧
        StageCentres (fun B D => D ⊆ singularSet (n := n) (strictTransform n B.proj W₀)) S ∧
        (∀ i, IsInvDomain k (P₀ i) ∧ IsCanonical (P₀ i) (R.inv (P₀ i)) (restrict (U₀ i) S) ∧
          ∀ z ∈ (geoTransformAlong (P₀ i) (restrict (U₀ i) S)).cosupp,
            R.inv (P₀ i) (restrict (U₀ i) S) z < m) ∧
        ∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π (strictTransform n T₀.proj W₀))) z ℓ ≤
          hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T₀.proj W₀)) (π z) ℓ := by
  obtain ⟨m,O,hKO,hAt,hNext⟩ := exists_relative_native_successor_with_cut R hW E hE T hT hStage
    U F hF hK hNe P hP hCan hETrace H hCut hCover hFoot hOverlap
  refine ⟨m,O,hKO,hAt,?_⟩
  dsimp only at hNext
  obtain ⟨C,Z,π,hπ,hC,hF,hProper,hTest,hStage',hCan',hLe,_⟩ := hNext
  exact ⟨C,Z,π,hπ,hC,hF,hProper,hTest,hStage',hCan',hLe⟩

end

end Hironaka.HironakaG8NativeRelativeSuccessor

#print axioms Hironaka.HironakaG8NativeRelativeSuccessor.exists_relative_native_successor
