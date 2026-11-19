import Hironaka.Resolution.HironakaG3CentresOverGenericFactor
import Hironaka.Resolution.HironakaMixedDimensionalBoundaryFiniteSeparation
import Hironaka.Resolution.HironakaMixedDimensionalBoundaryPure
import Hironaka.Resolution.HironakaMixedDimensionalBoundaryOriginalContexts

/-!
# A finite resolving history for the same mixed list and prescribed carrier

Actual total born support bounds imply actual centre-image bounds for the SAME
tower. A finite list induction then separates a head, resolves that pure head
with the full retained boundary, and resolves the remaining tail away from it.
Joint charts retain every original branch context through actual restriction-
concatenation isomorphisms. No all-current chart packet is assumed for the
already resolved head.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaMixedDimensionalBoundaryFiniteResolution

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen NormalCrossings
  RestrictEmptyTower HironakaAdmissibleSequence HironakaAdmissibleCalculus
  HironakaNormalCrossingsBoundaryTransform HironakaOriginalOldBranchOpenHistory
  HironakaOriginalNCOldStratumStrictEquality HironakaOriginalNCMarkedStratumBranchHistory
  HomogenizedGlueingTower MemberInterTowerAlong MemberInterLocusAlong
  HironakaMixedDimensionalBoundaryFiniteSeparation HironakaMixedDimensionalBoundaryPure
  HironakaMixedDimensionalBoundaryOriginalContexts GermIdealTotalTransform
  GermIdealPullbackCalculus HironakaNormalCrossingsOpenRestrictionSeparation

variable {n : ℕ}

/-- The literal total born support bounds every centre of this same actual history. -/
theorem centresOver_of_exceptionalDivisor_support_subset {X : CMfd.{u} n} (F : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (exceptionalDivisor T).support ⊆ T.proj ⁻¹' F → CentresOver F T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hSupport => by
      have hStep : (exceptionalDivisor (.step T C π hπ)).support =
          π ⁻¹' (exceptionalDivisor T).support ∪ π ⁻¹' C := by
        change (EffectiveDivisor.add
          (BlowupExceptionalDivisor.totalTransform hπ (exceptionalDivisor T))
          (BlowupExceptionalDivisor.exceptionalDivisor hπ)).support = _
        rw [HironakaPrincipalization.support_add, BlowupExceptionalDivisor.support_totalTransform,
          BlowupExceptionalDivisor.support_exceptionalDivisor]
      have hπsurj : Function.Surjective π :=
        HironakaLocalPrincipalization.IsBlowupSequence.surjective
          (IsBlowupSequence.step id C π IsBlowupSequence.refl hπ)
      have hPrefix : (exceptionalDivisor T).support ⊆ T.proj ⁻¹' F := by
        intro y hy
        obtain ⟨z, rfl⟩ := hπsurj y
        apply hSupport
        rw [hStep]
        exact Or.inl hy
      refine ⟨centresOver_of_exceptionalDivisor_support_subset F T hPrefix, ?_⟩
      intro y hy
      obtain ⟨z, rfl⟩ := hπsurj y
      apply hSupport
      rw [hStep]
      exact Or.inr hy

private theorem boundaryGeometry_wellFormed {X : CMfd.{u} n}
    {E : List (Set X)} (hE : IsSNCDivisor n E) :
    (boundaryGeometry (X := X) E).IsWellFormed :=
  ⟨isClosedSubmanifold_univ, IdealWeightPowers.isCoherent_unitIdeal, hE,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩

private theorem centresOver_mono {X : CMfd.{u} n} {F G : Set X} (hFG : F ⊆ G) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresOver F T → CentresOver G T
  | _, .refl, _ => trivial
  | _, .step T _ _ _, h => ⟨centresOver_mono hFG T h.1, fun _ hx => hFG (h.2 hx)⟩

private theorem centresOver_restrict {X : CMfd.{u} n} (U : Opens X) (F : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresOver F T →
      CentresOver ((Subtype.val : U → X) ⁻¹' F) (restrict U T) := fun T h => HironakaG3CentresOverGenericFactor.centresOver_restrict U F T h

private abbrev OriginalJointCharts {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (H : Set X) (T : BlowupTower X Y) (S : Set Y) : Prop :=
  ∀ (U : Opens X) (B : List (Set U)),
    IsSNCDivisor n (B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E) →
    (Subtype.val : U → X) ⁻¹' H = (⋃ A ∈ B, A) →
    HasNormalCrossings n ((Subtype.val : openPreimage T U → Y) ⁻¹' S)
      (B.map (strictAlong (restrict U T)) ++
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).E)

private theorem original_context_after_head {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (H : Set X) (P : BlowupTower X Y) (hP : IsGeoTestTower M P)
    (hHistoryP : IsOriginalBranchTestTower M H P) (U : Opens X) (B : List (Set U))
    (hB : IsSNCDivisor n (B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E))
    (hUnion : (Subtype.val : U → X) ⁻¹' H = (⋃ A ∈ B, A)) :
    let V := openPreimage P U
    let BP := B.map (strictAlong (restrict U P))
    IsSNCDivisor n (BP ++ (MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong M P)).E) ∧
    (Subtype.val : V → Y) ⁻¹' strictAlong P H = (⋃ C ∈ BP, C) := by
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  let A : MarkedIdeal n U := { MU with E := B ++ MU.E }
  let V := openPreimage P U
  let BP := B.map (strictAlong (restrict U P))
  have hAP : IsGeoTestTower A (restrict U P) := hHistoryP U B hB hUnion
  have hAN : A.N = univ := by
    change (Subtype.val : U → X) ⁻¹' M.N = univ
    rw [hN, preimage_univ]
  have hAI : A.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hM.isCoherent
  have hAWF : A.IsWellFormed := by
    refine ⟨?_, hAI, hB, ?_⟩
    · rw [hAN]
      exact isClosedSubmanifold_univ
    · rw [hAN]
      exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hB
  have hCurrent := original_branch_terminal_datum M hM.isClosedSubmanifold_N hM.isCoherent P hP U B
  constructor
  · have hSNC := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      hAWF (restrict U P) hAP).isSNCDivisor
    rw [hCurrent] at hSNC
    exact hSNC
  · rw [← strictAlong_restrict U P H, hUnion]
    exact strictAlong_original_branch_union (restrict U P) B

private theorem joint_append_from_tail {X Y Z : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (H : Set X) (P : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hP : IsGeoTestTower M P) (hHistoryP : IsOriginalBranchTestTower M H P)
    (hHistoryQ : IsOriginalBranchTestTower (geoTransformAlong M P) (strictAlong P H) Q)
    (S : Set Z) (hJoint : OriginalJointCharts (geoTransformAlong M P) (strictAlong P H) Q S) :
    OriginalJointCharts M H (P.append Q) S := by
  intro U B hB hUnion
  obtain ⟨hBP, hUnionP⟩ := original_context_after_head M hM hN H P hP hHistoryP U B hB hUnion
  exact original_branch_joint_chart_append M hM hN H P Q hP hHistoryP hHistoryQ U B hB hUnion S
    (hJoint (openPreimage P U) (B.map (strictAlong (restrict U P))) hBP hUnionP)

private theorem joint_append_of_disjoint_tail {X Y Z : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (H : Set X) (P : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hP : IsGeoTestTower M P) (hHistoryP : IsOriginalBranchTestTower M H P)
    (hHistoryQ : IsOriginalBranchTestTower (geoTransformAlong M P) (strictAlong P H) Q)
    (S F : Set Y) (hS : IsClosed S) (hF : IsClosed F) (hSF : Disjoint S F)
    (hOverQ : CentresOver F Q) (hJoint : OriginalJointCharts M H P S) :
    OriginalJointCharts M H (P.append Q) (strictTransform n Q.proj S) := by
  intro U B hB hUnion
  apply original_branch_joint_chart_append M hM hN H P Q hP hHistoryP hHistoryQ U B hB hUnion
    (strictTransform n Q.proj S)
  let V := openPreimage P U
  let BP := B.map (strictAlong (restrict U P))
  let MP := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong M P)
  let A : MarkedIdeal n V := { MP with E := BP ++ MP.E }
  let QV := restrict V Q
  obtain ⟨hBP, hUnionP⟩ := original_context_after_head M hM hN H P hP hHistoryP U B hB hUnion
  have hJointP := hJoint U B hB hUnion
  have hRec := geoTransformAlong_restrict U hM.isClosedSubmanifold_N hM.isCoherent P hP
  rw [hRec] at hJointP
  have hAT : IsGeoTestTower A QV := hHistoryQ V BP hBP hUnionP
  have hAdm := isAdmissibleBlowupSequence_proj A ((Subtype.val : V → Y) ⁻¹' F)
    QV hAT (centresOver_restrict V F Q hOverQ)
  have hDisjoint : Disjoint ((Subtype.val : V → Y) ⁻¹' S) ((Subtype.val : V → Y) ⁻¹' F) :=
    hSF.preimage (Subtype.val : V → Y)
  have hNC := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.hasNormalCrossings_preimage_of_disjoint
    hAdm hBP.1 (hF.preimage continuous_subtype_val) hDisjoint hJointP
  have hST : strictTransform n QV.proj ((Subtype.val : V → Y) ⁻¹' S) =
      QV.proj ⁻¹' ((Subtype.val : V → Y) ⁻¹' S) :=
    strictTransform_eq_preimage_of_disjoint QV.contMDiff_proj.continuous
      (HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.exceptionalLocus_subset hAdm)
      (hS.preimage continuous_subtype_val) hDisjoint
  rw [← hST, strictTransform_restricted_tower V Q S] at hNC
  rw [entire_original_old_retained_boundary MP BP QV] at hNC
  exact hNC

/-- A literal finite induction resolves every labelled part and retains one
joint coordinate family in every SAME original branch context. -/
theorem exists_retained_boundary_resolution_list (m : ℕ) :
    ∀ {X : CMfd.{u} n} (E₀ : List (Set X)) (_hE₀ : IsSNCDivisor n E₀)
      (H : Set X) (_hH : IsBoundaryAdaptedCarrier (n := n) H E₀)
      (G : Set X) (_hG : IsClosed G) (L : List (Set X × ℕ)),
      L.length = m →
      (∀ p ∈ L, IsRetainedGoodPart E₀ H G p.1 p.2) →
      L.Pairwise (fun p q => p.1 ∩ q.1 ⊆ G) →
      ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
        let D := boundaryGeometry (X := X) E₀
        let E := (geoTransformAlong D T).E
        IsGeoTestTower D T ∧ IsOriginalBranchTestTower D H T ∧
        CentresOver G T ∧ IsSNCDivisor n E ∧
        IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) E ∧
        (∀ p ∈ L,
          (∀ x ∈ strictTransform n T.proj p.1,
            RegularAtDim (n := n) (strictTransform n T.proj p.1) x p.2) ∧
          HasNormalCrossings n (strictTransform n T.proj p.1) E ∧
          ∀ (U : Opens X) (B : List (Set U)),
            IsSNCDivisor n (B ++ (MarkedIdeal.pullback (Subtype.val : U → X) D).E) →
            (Subtype.val : U → X) ⁻¹' H = (⋃ A ∈ B, A) →
            HasNormalCrossings n
              ((Subtype.val : openPreimage T U → Y) ⁻¹' strictTransform n T.proj p.1)
              (B.map (strictAlong (restrict U T)) ++
                (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) D)
                  (restrict U T)).E)) ∧
        L.Pairwise (fun p q =>
          Disjoint (strictTransform n T.proj p.1) (strictTransform n T.proj q.1)) := by
  induction m with
  | zero =>
      intro X E₀ hE₀ H hH G _hG L hL _hgood _hpair
      have hNil : L = [] := List.length_eq_zero_iff.mp hL
      subst L
      refine ⟨X, .refl, trivial, ?_, trivial, hE₀, hH, ?_, List.Pairwise.nil⟩
      · intro U B _hB _hUnion
        trivial
      · intro p hp
        exact False.elim (List.not_mem_nil hp)
  | succ m ih =>
      intro X E₀ hE₀ H hH G hG L hL hgood hpair
      obtain ⟨⟨A, d⟩, L', rfl⟩ := List.exists_cons_of_length_eq_add_one hL
      have hL' : L'.length = m := by simpa using hL
      rw [List.pairwise_cons] at hpair
      obtain ⟨hAsep, hpair'⟩ := hpair
      have hA := hgood (A, d) (List.mem_cons_self ..)
      have hgood' : ∀ p ∈ L', IsRetainedGoodPart E₀ H G p.1 p.2 :=
        fun p hp => hgood p (List.mem_cons_of_mem _ hp)
      let D₀ := boundaryGeometry (X := X) E₀
      have hD₀ := boundaryGeometry_wellFormed hE₀
      obtain ⟨Y₁, P, hDP, hHistoryP, hOverP, hE₁, hH₁, hSep⟩ :=
        exists_retained_boundary_sepOne L'.length E₀ hE₀ H hH G hG A d hA L' rfl hgood' hAsep
      let E₁ := (geoTransformAlong D₀ P).E
      let H₁ := strictAlong P H
      let A₁ := strictTransform n P.proj A
      let L₁ : List (Set Y₁ × ℕ) := L'.map fun p => (strictTransform n P.proj p.1, p.2)
      have hAdmP := isAdmissibleBlowupSequence_proj D₀ G P hDP hOverP
      have hA₁ : IsRetainedGoodPart E₁ H₁ (P.proj ⁻¹' G) A₁ d :=
        hA.strictTransform P hAdmP hE₀.1 hH.1
      have hgood₁ : ∀ p ∈ L₁, IsRetainedGoodPart E₁ H₁ (P.proj ⁻¹' G) p.1 p.2 := by
        intro p hp
        obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
        exact (hgood' p₀ hp₀).strictTransform P hAdmP hE₀.1 hH.1
      have hSep₁ : ∀ p ∈ L₁, Disjoint A₁ p.1 := by
        intro p hp
        obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
        exact hSep p₀ hp₀
      have hpair₁ : L₁.Pairwise (fun p q => p.1 ∩ q.1 ⊆ P.proj ⁻¹' G) := by
        simp only [L₁, List.pairwise_map]
        refine hpair'.imp_of_mem fun {p q} hp hq hpq z hz => hpq ?_
        exact ⟨strictTransform_subset_preimage P.contMDiff_proj.continuous (hgood' p hp).1.isClosed hz.1,
          strictTransform_subset_preimage P.contMDiff_proj.continuous (hgood' q hq).1.isClosed hz.2⟩
      let MA : MarkedIdeal n Y₁ := ⟨univ, E₁, vanishingIdeal (n := n) A₁, 1⟩
      obtain ⟨Y₂, R, _hCanR, hTestR, hHistoryR, hAdmR, hSNCR, _hExcR,
          hBornR, _hSingR, _hIsoR, hSmoothR, hRegR, hNCR, hAdaptR, hAllR⟩ :=
        exists_retained_boundary_pure_embedded_of_isCompact hA₁.1.1 hA₁.1.2.2.1 hA₁.1.pure
          hE₁ hH₁ hA₁.subset_closure_diff_boundary hA₁.1.2.1
      let D₁ := boundaryGeometry (X := Y₁) E₁
      let E₂ := (geoTransformAlong D₁ R).E
      let H₂ := strictAlong R H₁
      let A₂ := strictTransform n R.proj A₁
      let F₁ := A₁ \ regularLocus (n := n) A₁ d ∪ A₁ ∩ (H₁ ∪ ⋃ C ∈ E₁, C)
      have hF₁ : F₁ ⊆ P.proj ⁻¹' G := by
        rintro x (hx | ⟨hxA, hxH | hxE⟩)
        · exact hA₁.1.2.2.2.1 hx
        · exact hA₁.2 ⟨hxA, hxH⟩
        · exact hA₁.1.2.2.2.2.1 ⟨hxA, hxE⟩
      have hOverR : CentresOver F₁ R := by
        apply centresOver_of_exceptionalDivisor_support_subset F₁ R
        rw [HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop MA hE₁.1 R]
        exact hBornR
      have hOverR' := centresOver_mono hF₁ R hOverR
      have hAdmR' := HironakaAdmissibleSequence.IsAdmissibleBlowupSequence.mono hF₁ hAdmR
      have hDR : IsGeoTestTower D₁ R := boundaryGeometry_test MA hE₁ R hTestR
      have hDHistoryR : IsOriginalBranchTestTower D₁ H₁ R :=
        boundaryGeometry_original_history MA H₁ R hHistoryR
      have hEeqR : (geoTransformAlong MA R).E = E₂ :=
        MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := MA) (𝔫 := D₁) rfl R
      have hE₂ : IsSNCDivisor n E₂ := hEeqR ▸ hSNCR
      have hH₂ : IsBoundaryAdaptedCarrier (n := n) H₂ E₂ := hEeqR ▸ hAdaptR
      have hNC₂ : HasNormalCrossings n A₂ E₂ := hEeqR ▸ hNCR
      let L₂ : List (Set Y₂ × ℕ) := L₁.map fun p => (strictTransform n R.proj p.1, p.2)
      let K₂ : Set Y₂ := ⋃ C ∈ L₂.map Prod.fst, C
      have hK₂ : IsClosed K₂ := by
        refine HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed fun C hC => ?_
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hC
        obtain ⟨p₁, _hp₁, rfl⟩ := List.mem_map.mp hp
        exact isClosed_closure
      have hmemK₂ : ∀ p ∈ L₂, p.1 ⊆ K₂ := fun p hp x hx =>
        mem_iUnion₂.mpr ⟨p.1, List.mem_map_of_mem hp, hx⟩
      let G₂ : Set Y₂ := R.proj ⁻¹' (P.proj ⁻¹' G) ∩ K₂
      have hG₂ : IsClosed G₂ :=
        ((hG.preimage P.contMDiff_proj.continuous).preimage R.contMDiff_proj.continuous).inter hK₂
      have hgood₂ : ∀ p ∈ L₂, IsRetainedGoodPart E₂ H₂ G₂ p.1 p.2 := by
        intro p hp
        obtain ⟨p₁, hp₁, rfl⟩ := List.mem_map.mp hp
        have h := ((hgood₁ p₁ hp₁).strictTransform R hAdmR' hE₁.1 hH₁.1).inter (hmemK₂ _ hp)
        rw [hEeqR] at h
        exact h
      have hpair₂ : L₂.Pairwise (fun p q => p.1 ∩ q.1 ⊆ G₂) := by
        simp only [L₂, List.pairwise_map]
        refine hpair₁.imp_of_mem fun {p q} hp hq hpq z hz => ?_
        exact ⟨hpq ⟨strictTransform_subset_preimage R.contMDiff_proj.continuous (hgood₁ p hp).1.isClosed hz.1,
          strictTransform_subset_preimage R.contMDiff_proj.continuous (hgood₁ q hq).1.isClosed hz.2⟩,
          hmemK₂ _ (List.mem_map_of_mem hp) hz.1⟩
      have hA₂K₂ : Disjoint A₂ K₂ := by
        rw [disjoint_left]
        intro z hzA hzK
        obtain ⟨C, hC, hzC⟩ := mem_iUnion₂.mp hzK
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hC
        obtain ⟨p₁, hp₁, rfl⟩ := List.mem_map.mp hp
        exact disjoint_left.mp (hSep₁ p₁ hp₁)
          (strictTransform_subset_preimage R.contMDiff_proj.continuous isClosed_closure hzA)
          (strictTransform_subset_preimage R.contMDiff_proj.continuous (hgood₁ p₁ hp₁).1.isClosed hzC)
      have hA₂G₂ : Disjoint A₂ G₂ := hA₂K₂.mono_right inter_subset_right
      obtain ⟨Y₃, Q, hDQ, hDHistoryQ, hOverQ, hE₃, _hH₃, hResQ, hDisjQ⟩ :=
        ih E₂ hE₂ H₂ hH₂ G₂ hG₂ L₂ (by simp [L₂, L₁, hL']) hgood₂ hpair₂
      let D₂ := boundaryGeometry (X := Y₂) E₂
      let T₁₂ := P.append R
      let T := T₁₂.append Q
      have hD₀P : geoTransformAlong D₀ P = D₁ := boundaryGeometry_geoTransformAlong E₀ P
      have hD₀T₁₂ : geoTransformAlong D₀ T₁₂ = D₂ := by
        change geoTransformAlong D₀ (P.append R) = D₂
        rw [geoTransformAlong_append, hD₀P, boundaryGeometry_geoTransformAlong E₁ R]
      have hHT₁₂ : strictAlong T₁₂ H = H₂ := MemberInterLocusAlong.strictAlong_append P H R
      have hRCurrent : IsGeoTestTower (geoTransformAlong D₀ P) R := by
        rw [hD₀P]
        exact hDR
      have hHistRCurrent : IsOriginalBranchTestTower (geoTransformAlong D₀ P) (strictAlong P H) R := by
        rw [hD₀P]
        exact hDHistoryR
      have hDT₁₂ : IsGeoTestTower D₀ T₁₂ :=
        (isGeoTestTower_append_iff D₀ P R).mpr ⟨hDP, hRCurrent⟩
      have hHistT₁₂ : IsOriginalBranchTestTower D₀ H T₁₂ :=
        original_history_append_native D₀ hD₀ P R hDP hHistoryP hHistRCurrent
      have hQCurrent : IsGeoTestTower (geoTransformAlong D₀ T₁₂) Q := by
        rw [hD₀T₁₂]
        exact hDQ
      have hHistQCurrent : IsOriginalBranchTestTower (geoTransformAlong D₀ T₁₂) (strictAlong T₁₂ H) Q := by
        rw [hD₀T₁₂, hHT₁₂]
        exact hDHistoryQ
      have hDT : IsGeoTestTower D₀ T :=
        (isGeoTestTower_append_iff D₀ T₁₂ Q).mpr ⟨hDT₁₂, hQCurrent⟩
      have hHistT : IsOriginalBranchTestTower D₀ H T :=
        original_history_append_native D₀ hD₀ T₁₂ Q hDT₁₂ hHistT₁₂ hHistQCurrent
      have hG₂sub : G₂ ⊆ T₁₂.proj ⁻¹' G := by
        intro z hz
        change (P.append R).proj z ∈ G
        rw [BlowupTower.proj_append]
        exact hz.1
      have hOverT : CentresOver G T :=
        (centresOver_append_iff G T₁₂ Q).mpr
          ⟨(centresOver_append_iff G P R).mpr ⟨hOverP, hOverR'⟩,
            centresOver_mono hG₂sub Q hOverQ⟩
      have hFinalE : (geoTransformAlong D₀ T).E = (geoTransformAlong D₂ Q).E := by
        change (geoTransformAlong D₀ (T₁₂.append Q)).E = _
        rw [geoTransformAlong_append, hD₀T₁₂]
      have hST (C : Set X) : strictTransform n T.proj C =
          strictTransform n Q.proj (strictTransform n R.proj (strictTransform n P.proj C)) := by
        change strictTransform n ((P.append R).append Q).proj C = _
        rw [BlowupTower.proj_append,
          StrictTransformComposition.strictTransform_comp (P.append R).contMDiff_proj Q.contMDiff_proj,
          BlowupTower.proj_append,
          StrictTransformComposition.strictTransform_comp P.contMDiff_proj R.contMDiff_proj]
      have hAdmQ := isAdmissibleBlowupSequence_proj D₂ G₂ Q hDQ hOverQ
      have hExcQ := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.exceptionalLocus_subset hAdmQ
      have hHeadStrict : strictTransform n Q.proj A₂ = Q.proj ⁻¹' A₂ :=
        strictTransform_eq_preimage_of_disjoint Q.contMDiff_proj.continuous hExcQ hSmoothR.1 hA₂G₂
      have hHeadNC := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.hasNormalCrossings_preimage_of_disjoint
        hAdmQ hE₂.1 hG₂ hA₂G₂ hNC₂
      have hAllRD : OriginalJointCharts D₁ H₁ R A₂ := by
        intro U B hB hUnion
        have hNC := hAllR U B hB hUnion
        rw [strictTransform_restricted_tower U R A₁] at hNC
        have hLocalE : (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → Y₁) MA) (restrict U R)).E =
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → Y₁) D₁) (restrict U R)).E :=
          MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
            (𝔪 := MarkedIdeal.pullback (Subtype.val : U → Y₁) MA)
            (𝔫 := MarkedIdeal.pullback (Subtype.val : U → Y₁) D₁) rfl (restrict U R)
        rw [hLocalE] at hNC
        exact hNC
      have hAllRCurrent : OriginalJointCharts (geoTransformAlong D₀ P) (strictAlong P H) R A₂ := by
        rw [hD₀P]
        exact hAllRD
      have hHeadJointT₁₂ : OriginalJointCharts D₀ H T₁₂ A₂ :=
        joint_append_from_tail D₀ hD₀ rfl H P R hDP hHistoryP hHistRCurrent A₂ hAllRCurrent
      have hHeadJointT : OriginalJointCharts D₀ H T (strictTransform n Q.proj A₂) :=
        joint_append_of_disjoint_tail D₀ hD₀ rfl H T₁₂ Q hDT₁₂ hHistT₁₂ hHistQCurrent
          A₂ G₂ hSmoothR.1 hG₂ hA₂G₂ hOverQ hHeadJointT₁₂
      refine ⟨Y₃, T, hDT, hHistT, hOverT, ?_,
        (current_old_strata_eq_strict D₀ hH T hDT hHistT).1, ?_, ?_⟩
      · rw [hFinalE]
        exact hE₃
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · refine ⟨?_, ?_, ?_⟩
          · rw [hST A, hHeadStrict]
            exact fun z hz => regularAtDim_preimage_of_disjoint Q.contMDiff_proj hExcQ hA₂G₂
              (hRegR (Q.proj z) hz)
          · rw [hST A, hHeadStrict, hFinalE]
            exact hHeadNC
          · change OriginalJointCharts D₀ H T (strictTransform n T.proj A)
            rw [hST A]
            exact hHeadJointT
        · let p₁ : Set Y₁ × ℕ := (strictTransform n P.proj p.1, p.2)
          let p₂ : Set Y₂ × ℕ := (strictTransform n R.proj p₁.1, p₁.2)
          have hp₁ : p₁ ∈ L₁ := List.mem_map_of_mem hp'
          have hp₂ : p₂ ∈ L₂ := List.mem_map_of_mem hp₁
          obtain ⟨hReg, hNC, hJoint⟩ := hResQ p₂ hp₂
          refine ⟨?_, ?_, ?_⟩
          · rw [hST p.1]
            exact hReg
          · rw [hST p.1, hFinalE]
            exact hNC
          · change OriginalJointCharts D₀ H T (strictTransform n T.proj p.1)
            rw [hST p.1]
            apply joint_append_from_tail D₀ hD₀ rfl H T₁₂ Q hDT₁₂ hHistT₁₂ hHistQCurrent
            change OriginalJointCharts (geoTransformAlong D₀ T₁₂) (strictAlong T₁₂ H) Q
              (strictTransform n Q.proj p₂.1)
            rw [hD₀T₁₂, hHT₁₂]
            exact hJoint
      · rw [List.pairwise_cons]
        constructor
        · intro p hp
          have hProj : T.proj = P.proj ∘ (R.proj ∘ Q.proj) := by
            simp only [T, T₁₂, BlowupTower.proj_append, Function.comp_assoc]
          rw [hProj,
            StrictTransformComposition.strictTransform_comp P.contMDiff_proj (R.contMDiff_proj.comp Q.contMDiff_proj),
            StrictTransformComposition.strictTransform_comp P.contMDiff_proj (R.contMDiff_proj.comp Q.contMDiff_proj)]
          exact ((hSep p hp).preimage (R.proj ∘ Q.proj)).mono
            (strictTransform_subset_preimage (R.contMDiff_proj.comp Q.contMDiff_proj).continuous isClosed_closure)
            (strictTransform_subset_preimage (R.contMDiff_proj.comp Q.contMDiff_proj).continuous isClosed_closure)
        · have h := hDisjQ
          simp only [L₂, L₁, List.pairwise_map] at h
          refine h.imp fun {p q} hpq => ?_
          rw [hST p.1, hST q.1]
          exact hpq

end

end Hironaka.HironakaMixedDimensionalBoundaryFiniteResolution
