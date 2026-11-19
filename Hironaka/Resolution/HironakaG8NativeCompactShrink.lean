import Hironaka.Resolution.HironakaG8NativeSimultaneousCentre
import Hironaka.Resolution.HironakaLocalPrincipalization
import Hironaka.Resolution.HironakaG8NativeGlobalSuccessor
import Hironaka.Resolution.HironakaG8IntrinsicSingularBlockSchedule
import Hironaka.Resolution.HironakaCurrentStrictTransformIdeal
import Hironaka.Analytic.TowerPreimageCompact

/-! A relative compact task selects a common native maximum and an open
saturated region where that same maximum gives a compatible canonical step. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativeCompactShrink

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  ResolutionInvariantOrder ResolutionDriver

/-- Compatible upper semicontinuous values of a closed support patch give an
attained maximum over a compact base task and a saturated open of bounded
values. The support away from the task may be noncompact. -/
theorem exists_saturated_maximum_window
    {X Y I Λ : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LinearOrder Λ]
    {p : Y → X} (hp : IsProperMap p) {K : Set X} (hK : IsCompact K)
    (U : I → Opens Y) (F : Set Y) (hF : IsClosed F)
    (hNe : (F ∩ p ⁻¹' K).Nonempty)
    (S : (i : I) → Set (U i)) (v : (i : I) → U i → Λ)
    (hUSC : ∀ i, IsInvUSCOn (v i) (S i))
    (hCover : ∀ y ∈ F, ∃ (i : I) (hy : y ∈ U i), (⟨y, hy⟩ : U i) ∈ S i)
    (hFoot : ∀ i (y : U i), y ∈ S i → y.val ∈ F)
    (hOverlap : ∀ (i j : I) (y : Y) (hi : y ∈ U i) (hj : y ∈ U j),
      (⟨y, hi⟩ : U i) ∈ S i → (⟨y, hj⟩ : U j) ∈ S j ∧
        v i ⟨y, hi⟩ = v j ⟨y, hj⟩) :
    ∃ (m : Λ) (O : Opens X), K ⊆ O ∧
      (∀ i (y : U i), y ∈ S i → p y.val ∈ O → v i y ≤ m) ∧
      ∃ (i : I) (y : U i), y ∈ S i ∧ p y.val ∈ K ∧ v i y = m := by
  classical
  choose index hOpen hLocal using hCover
  have hSample := hNe
  obtain ⟨a, haF, _⟩ := hSample
  let f (y : Y) : Λ :=
    if hy : y ∈ F then v (index y hy) ⟨y, hOpen y hy⟩
    else v (index a haF) ⟨a, hOpen a haF⟩
  have hVal (i : I) (y : U i) (hy : y ∈ S i) : f y.val = v i y := by
    have hyF := hFoot i y hy
    rw [show f y.val = v (index y.val hyF) ⟨y.val, hOpen y.val hyF⟩ from dif_pos hyF]
    exact (hOverlap i (index y.val hyF) y.val y.property (hOpen y.val hyF) hy).2.symm
  have hGlobal : IsInvUSCOn f F := by
    intro y hy
    let i := index y hy
    let z : U i := ⟨y, hOpen y hy⟩
    have hz : z ∈ S i := hLocal y hy
    rw [← (U i).isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq z, Filter.eventually_map]
    filter_upwards [hUSC i z hz] with t ht htF
    have htS := (hOverlap (index t.val htF) i t.val (hOpen t.val htF) t.property
      (hLocal t.val htF)).1
    rw [hVal i t htS, hVal i z hz]
    exact ht htS
  have hCompact : IsCompact (F ∩ p ⁻¹' K) := (hp.isCompact_preimage hK).inter_left hF
  obtain ⟨b, hb, hMax⟩ := (hGlobal.mono inter_subset_left).exists_isMaxOn hCompact hNe
  let m := f b
  let A : Set Y := {y | y ∈ F → f y ≤ m}
  have hA : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    by_cases hyF : y ∈ F
    · filter_upwards [hGlobal y hyF] with z hz
      exact fun hzF => (hz hzF).trans (hy hyF)
    · filter_upwards [hF.isOpen_compl.mem_nhds hyF] with z hz hzF
      exact False.elim (hz hzF)
  let O : Opens X := ⟨(p '' Aᶜ)ᶜ, (hp.isClosedMap _ hA.isClosed_compl).isOpen_compl⟩
  have hKO : K ⊆ O := by
    intro x hx
    rintro ⟨y, hy, rfl⟩
    exact hy fun hyF => hMax y ⟨hyF, hx⟩
  refine ⟨m, O, hKO, ?_, index b hb.1, ⟨b, hOpen b hb.1⟩, hLocal b hb.1, hb.2, ?_⟩
  · intro i y hy hyO
    have hyA : y.val ∈ A := by
      by_contra h
      exact hyO ⟨y.val, h, rfl⟩
    exact (hVal i y hy).symm.trans_le (hyA (hFoot i y hy))
  · exact (hVal (index b hb.1) ⟨b, hOpen b hb.1⟩ (hLocal b hb.1)).symm

variable {n k : ℕ} {Λ : Type*} [LinearOrder Λ] {X Y Z : CMfd.{0} n}

/-- A literal next blowup at the common numerical cut, including the empty
restriction case, remains canonical in the same marked record. Every value in
its actual surviving cosupport is strictly below the selected cut value. -/
theorem canonical_step_and_values_lt_of_value_cut
    (R : ResolutionInvariantSeq.ResolutionInvariant n k Λ)
    (P : MarkedIdeal n X) (hP : IsInvDomain k P)
    (T : BlowupTower X Y) (hCan : IsCanonical P (R.inv P) T)
    (m : Λ) (hUpper : ∀ y ∈ (geoTransformAlong P T).cosupp, R.inv P T y ≤ m)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCut : C = {y | y ∈ (geoTransformAlong P T).cosupp ∧ R.inv P T y = m}) :
    IsCanonical P (R.inv P) (.step T C π hπ) ∧
      ∀ z ∈ (geoTransformAlong P (.step T C π hπ)).cosupp,
        R.inv P (.step T C π hπ) z < m := by
  let Q := geoTransformAlong P T
  have hCT : C ⊆ Q.cosupp := by
    rw [hCut]
    exact fun _ hy => hy.1
  have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hP T hCan
  have hQ := InvDomainTowerAlong.isInvDomain_geoTransformAlong hP T hTest
  have hPre {z : Z} (hz : z ∈ (geoTransformAlong P (.step T C π hπ)).cosupp) :
      π z ∈ Q.cosupp :=
    TransformOffCentre.cosupp_geoTransform_subset_preimage Q hQ.isWellFormed.isClosedSubmanifold_N.1
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hQ.isWellFormed.isCoherent hg) hπ hCT hz
  have hBelow {y : Y} (hy : y ∈ Q.cosupp) (hyC : y ∉ C) : R.inv P T y < m :=
    lt_of_le_of_ne (hUpper y hy) fun he => hyC (hCut.symm ▸ ⟨hy, he⟩)
  by_cases hNe : C.Nonempty
  · have hMax : C = maxLocus (R.inv P T) Q.cosupp := by
      obtain ⟨x, hx⟩ := hNe
      have hx' : x ∈ Q.cosupp ∧ R.inv P T x = m := by
        rw [hCut] at hx
        exact hx
      rw [hCut]
      ext y
      constructor
      · rintro ⟨hy, hval⟩
        exact ⟨hy, fun w hw => (hUpper w hw).trans_eq hval.symm⟩
      · rintro ⟨hy, hyMax⟩
        exact ⟨hy, le_antisymm (hUpper y hy) (hx'.2.symm.trans_le (hyMax x hx'.1))⟩
    refine ⟨⟨hCan, Or.inr hMax⟩, fun z hz => ?_⟩
    obtain ⟨hDrop, hEqual⟩ := R.isInvValue.decrease P hP T C π hπ hCan hNe hMax z hz
    by_cases hzC : π z ∈ C
    · exact (hDrop hzC).trans_le (hUpper _ (hPre hz))
    · rw [hEqual hzC]
      exact hBelow (hPre hz) hzC
  · have hEmpty : C = ∅ := not_nonempty_iff_eq_empty.mp hNe
    refine ⟨⟨hCan, Or.inl hEmpty⟩, fun z hz => ?_⟩
    rw [R.isInvValue.emptyStep P hP T C π hπ hEmpty hCan z hz]
    exact hBelow (hPre hz) (hEmpty.symm ▸ notMem_empty _)

section CommonMaximum

open BlowupTowerTransforms NormalCrossings HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance
  HironakaStageCenters HomogenizedGlueingTower HironakaG8NativeGlobalSuccessor
  HironakaG8IntrinsicSingularBlockSchedule HironakaUniformHistoricalSuccessorOriginalRegular
  TowerPreimageCompact RestrictEmptyTower HironakaG8NativeSimultaneousCentre

/-- On an actual original prefix with a bounded common numerical maximum,
the original test and intrinsic singular positions extend by one actual
blowup. Every literal native restriction is canonical, and its values
on the actual surviving cosupport lie strictly below the common cut. -/
theorem native_successor_at_common_maximum_with_cut
    {I Λ : Type} [LinearOrder Λ] (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T)
    (hStage : StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T)
    (U : I → Opens X) (F : Set Y) (hF : IsClosed F)
    (hCover : ∀ y ∈ F, ∃ i, y ∈ openPreimage T (U i))
    (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (hP : ∀ i, IsInvDomain k (P i))
    (hCan : ∀ i, IsCanonical (P i) (R.inv (P i)) (restrict (U i) T))
    (hETrace : ∀ i, (geoTransformAlong (P i) (restrict (U i) T)).E =
      (geoTransformAlong (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T).E.map
        ((Subtype.val : openPreimage T (U i) → Y) ⁻¹' ·))
    (H : ℕ → ℕ)
    (hCut : ∀ i (y : openPreimage T (U i)), y ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp →
      y.val ∈ singularSet (n := n) (strictTransform n T.proj W) ∧
        ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) y.val ℓ = H ℓ)
    (hFoot : ∀ i (y : openPreimage T (U i)), y ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp → y.val ∈ F)
    (hOverlap : ∀ i j (y : Y) (hi : y ∈ openPreimage T (U i)) (hj : y ∈ openPreimage T (U j)),
      (⟨y, hi⟩ : openPreimage T (U i)) ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp →
      (⟨y, hj⟩ : openPreimage T (U j)) ∈ (geoTransformAlong (P j) (restrict (U j) T)).cosupp ∧
        R.inv (P i) (restrict (U i) T) ⟨y, hi⟩ = R.inv (P j) (restrict (U j) T) ⟨y, hj⟩)
    (m : Λ)
    (hUpper : ∀ i (y : openPreimage T (U i)), y ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp →
      R.inv (P i) (restrict (U i) T) y ≤ m)
    (hAttain : ∃ (i : I) (y : openPreimage T (U i)),
      y ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp ∧ R.inv (P i) (restrict (U i) T) y = m) :
    ∃ (C : Set Y) (Z : CMfd.{0} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      let S := BlowupTower.step T C π hπ
      C.Nonempty ∧ C ⊆ F ∧ IsProperMap π ∧
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) S ∧
      StageCentres (fun B D => D ⊆ singularSet (n := n) (strictTransform n B.proj W)) S ∧
      (∀ i, IsCanonical (P i) (R.inv (P i)) (restrict (U i) S) ∧
        ∀ z ∈ (geoTransformAlong (P i) (restrict (U i) S)).cosupp,
          R.inv (P i) (restrict (U i) S) z < m) ∧
      (∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π (strictTransform n T.proj W))) z ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) (π z) ℓ) ∧ NativeSimultaneousCentre R U P T C m := by
  let M : MarkedIdeal n X := ⟨univ,E,vanishingIdeal (n := n) W,1⟩
  let A := strictTransform n T.proj W
  have hM : M.IsWellFormed := ⟨isClosedSubmanifold_univ, CartanIrreducible.cartanCoherence W hW,
    hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hGeo := actual_singular_history_original_regular_protection W hW T
    (intrinsic_stage_native_history W T hStage)
  obtain ⟨C, Z, π, hπ, hCne, hCF, hCS, hProper, hNext, hTrace, _, hLe⟩ :=
    exists_actual_native_global_maximum_blowup_along R hGeo.2.2.2.1 (geoTransformAlong M T).E
      (openPreimage T ∘ U) F hF hCover P (fun i => restrict (U i) T)
      hP hCan hETrace H hCut hFoot hOverlap m hUpper hAttain
  let O : Opens X := ⟨(singularSet (n := n) W)ᶜ,(isClosed_singularSet hW.isClosed).isOpen_compl⟩
  have hDense : W ⊆ closure (W ∩ (O : Set X)) := by
    change W ⊆ closure (W ∩ (singularSet (n := n) W)ᶜ)
    simpa only [Set.sdiff_eq] using HironakaResolutionSpace.subset_closure_diff_singularSet hW
  have hStay : A ⊆ (geoTransformAlong M T).cosupp :=
    HironakaCurrentStrictTransformIdeal.strictTransform_subset_cosupp_of_centresAvoid_wellFormed
      hW.isClosed hM O hDense T hT hGeo.1
  have hAdm : (geoTransformAlong M T).IsAdmissibleCentre C :=
    ⟨hNext.2.1, hCS.trans ((singularSet_subset A).trans hStay), hNext.2.2.2⟩
  refine ⟨C, Z, π, hπ, hCne, hCF, hProper, ⟨hT,hAdm⟩, ⟨hStage,hCS⟩, ?_, hLe,
    ⟨fun y hy => hCover y (hCF hy),hUpper,hTrace⟩⟩
  intro i
  obtain ⟨f, hf, hStep⟩ := exists_restrict_step (U i) T C π hπ
  rw [hStep]
  exact canonical_step_and_values_lt_of_value_cut
    (X := CMfd.of (n := n) (U i))
    (Y := CMfd.of (n := n) (openPreimage T (U i)))
    (Z := CMfd.of (n := n) (openPreimage (.step T C π hπ) (U i)))
    R (P i) (hP i) (restrict (U i) T) (hCan i) m (hUpper i) _ f hf (hTrace i)

/-- The original successor interface, with its numeric witness
available from the stronger form. -/
theorem native_successor_at_common_maximum
    {I Λ : Type} [LinearOrder Λ] (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T)
    (hStage : StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T)
    (U : I → Opens X) (F : Set Y) (hF : IsClosed F)
    (hCover : ∀ y ∈ F, ∃ i, y ∈ openPreimage T (U i))
    (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (hP : ∀ i, IsInvDomain k (P i))
    (hCan : ∀ i, IsCanonical (P i) (R.inv (P i)) (restrict (U i) T))
    (hETrace : ∀ i, (geoTransformAlong (P i) (restrict (U i) T)).E =
      (geoTransformAlong (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T).E.map
        ((Subtype.val : openPreimage T (U i) → Y) ⁻¹' ·))
    (H : ℕ → ℕ)
    (hCut : ∀ i (y : openPreimage T (U i)), y ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp →
      y.val ∈ singularSet (n := n) (strictTransform n T.proj W) ∧
        ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) y.val ℓ = H ℓ)
    (hFoot : ∀ i (y : openPreimage T (U i)), y ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp → y.val ∈ F)
    (hOverlap : ∀ i j (y : Y) (hi : y ∈ openPreimage T (U i)) (hj : y ∈ openPreimage T (U j)),
      (⟨y, hi⟩ : openPreimage T (U i)) ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp →
      (⟨y, hj⟩ : openPreimage T (U j)) ∈ (geoTransformAlong (P j) (restrict (U j) T)).cosupp ∧
        R.inv (P i) (restrict (U i) T) ⟨y, hi⟩ = R.inv (P j) (restrict (U j) T) ⟨y, hj⟩)
    (m : Λ)
    (hUpper : ∀ i (y : openPreimage T (U i)), y ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp →
      R.inv (P i) (restrict (U i) T) y ≤ m)
    (hAttain : ∃ (i : I) (y : openPreimage T (U i)),
      y ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp ∧ R.inv (P i) (restrict (U i) T) y = m) :
    ∃ (C : Set Y) (Z : CMfd.{0} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      let S := BlowupTower.step T C π hπ
      C.Nonempty ∧ C ⊆ F ∧ IsProperMap π ∧
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) S ∧
      StageCentres (fun B D => D ⊆ singularSet (n := n) (strictTransform n B.proj W)) S ∧
      (∀ i, IsCanonical (P i) (R.inv (P i)) (restrict (U i) S) ∧
        ∀ z ∈ (geoTransformAlong (P i) (restrict (U i) S)).cosupp,
          R.inv (P i) (restrict (U i) S) z < m) ∧
      ∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π (strictTransform n T.proj W))) z ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) (π z) ℓ := by
  obtain ⟨C,Z,π,hπ,hC,hFoot,hProper,hTest,hStage',hCan',hHS,_⟩ :=
    native_successor_at_common_maximum_with_cut R hW E hE T hT hStage U F hF hCover
      P hP hCan hETrace H hCut hFoot hOverlap m hUpper hAttain
  exact ⟨C,Z,π,hπ,hC,hFoot,hProper,hTest,hStage',hCan',hHS⟩

end CommonMaximum

end

end Hironaka.HironakaG8NativeCompactShrink

#print axioms Hironaka.HironakaG8NativeCompactShrink.exists_saturated_maximum_window
#print axioms Hironaka.HironakaG8NativeCompactShrink.canonical_step_and_values_lt_of_value_cut
#print axioms Hironaka.HironakaG8NativeCompactShrink.native_successor_at_common_maximum
