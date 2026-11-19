import Hironaka.Resolution.HironakaOriginalNCMarkedStratumNativeFields

/-!
# Prescribed-H open and given-tower-isomorphism naturality of NEW Psi

Whole marked sums retain proper N, the entire ordered E, mark and ideal.
Intrinsic H/T chronology alone reuses the actual same-E geometry donor;
no lower invariant or old coefficient/remainder value is evaluated on it.
Given raw NEW-Psi CAN internally supplies tests, ALLbranch histories, actual
birth domains and actual native canonical suffixes.

Mathematics/API first: work/hironaka-g9-new-marked-stratum-driver-fields-20261023/
open-iso-naturality-20261024/. SOURCE ONLY; no Lean or kernel check, empty
prefix field, invariant installation, noncompact driver, terminal NC,
Blueprint credit or original G9 closure is asserted.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCMarkedStratumNaturality

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerSplitIso
  BlowupTowerIsomorphism BlowupTowerIsoTail BlowupRestrictOpen MarkedIdealRestrictOpen
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  GermIdealPullbackCalculus NormalCrossings NormalCrossingsInvariance
  HomogenizedGlueingTower MaxLocusLocal StepOneTangentChange
  CoefficientIdealRestriction HironakaNormalCrossingsLocalBranches
  HironakaNormalCrossingsMultiplicityStrata HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsBiholomorphicMultiplicity
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaOriginalOldBranchOpenHistory
  HironakaOriginalNCCountHistory HironakaOriginalNCCausalHistoryValue
  HironakaOriginalNCOldStratumStrictEquality HironakaOriginalNCMarkedStratum
  HironakaOriginalNCMarkedStratumHistoryValue HironakaOriginalNCMarkedStratumBranchHistory
  HironakaOriginalNCMarkedStratumBirthFrame HironakaOriginalNCMarkedStratumCanonicalHistory
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem pullback_id (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) :
    MarkedIdeal.pullback (id : X → X) M = M := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
  · change M.E.map (fun C => (id : X → X) ⁻¹' C) = M.E
    simp
  · exact BlowupControlledTransform.pullback_id hI

private theorem pullback_comp {B C D : CMfd.{u} n} (M : MarkedIdeal n B)
    (hI : M.ideal.IsCoherent) (f : C → B) (g : D → C)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) :
    MarkedIdeal.pullback g (MarkedIdeal.pullback f M) = MarkedIdeal.pullback (f ∘ g) M := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
  · change (M.E.map (f ⁻¹' ·)).map (g ⁻¹' ·) = M.E.map ((f ∘ g) ⁻¹' ·)
    rw [List.map_map]
    rfl
  · exact (GermIdealTotalTransform.pullback_comp hf hg hI).symm

private def lowerMask (A : MarkedIdeal n X) (S : BlowupTower X Y) (y : Y) :
    WithBot (CanonicalCentres.ValTy n) :=
  if y ∈ (geoTransformAlong A S).cosupp then
    ((CanonicalCentres.canonicalInvariant n).inv A S y : WithBot (CanonicalCentres.ValTy n))
  else ⊥

/-- A total cut evaluation keeps the dependent marked record and point
together while their numerical cut indices are transported. The false
branch is never used at the genuine causal birth cut. -/
private def evaluateCut (M : MarkedIdeal n X) (H : Set X)
    (T : BlowupTower X Y) (y : Y) (a j : ℕ) : WithBot (CanonicalCentres.ValTy n) :=
  let W := oldCountLowOpen H (head T j) a
  let MW := MarkedIdeal.pullback (Subtype.val : W → (split T j).1)
    (geoTransformAlong M (head T j))
  let A := markedStratum MW {z : W | a ≤ oldCount H (head T j) z.val}
  if hy : y ∈ openPreimage (tail T j) W then lowerMask A (restrict W (tail T j)) ⟨y, hy⟩ else ⊥

private theorem markedStratumHistoryValue_eq_evaluateCut (M : MarkedIdeal n X) (H : Set X)
    (T : BlowupTower X Y) (y : Y) :
    markedStratumHistoryValue M H T y = toLex (oldCount H T y,
      evaluateCut M H T y (oldCount H T y) (T.length - birthYear H T y)) := by
  unfold evaluateCut
  dsimp only
  have hMem : y ∈ openPreimage (tail T (T.length - birthYear H T y))
      (oldCountLowOpen H (head T (T.length - birthYear H T y)) (oldCount H T y)) :=
    (causalBirthPoint H T y).property
  rw [dif_pos hMem]
  rfl

private theorem lowerMask_restrict (A : MarkedIdeal n X) (hA : IsInvDomain n A)
    (S : BlowupTower X Y)
    (hCan : IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) S)
    (U : Opens X) (p : openPreimage S U) :
    lowerMask (MarkedIdeal.pullback (Subtype.val : U → X) A) (restrict U S) p =
      lowerMask A S p.val := by
  let R := CanonicalCentres.canonicalInvariant n
  have hTest := Seq.ResolutionInvariantExt.isGeoTestTower_of_isCanonical R hA S hCan
  have hSI := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent S hTest).2
  have hCos : (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) A)
      (restrict U S)).cosupp = (Subtype.val : openPreimage S U → Y) ⁻¹'
        (geoTransformAlong A S).cosupp := by
    rw [geoTransformAlong_restrict U hA.isWellFormed.isClosedSubmanifold_N
      hA.isWellFormed.isCoherent S hTest]
    exact cosupp_pullback_val _
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hSI hg) _
  unfold lowerMask
  by_cases hp : p.val ∈ (geoTransformAlong A S).cosupp
  · have hp' : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) A)
        (restrict U S)).cosupp := by rw [hCos]; exact hp
    rw [if_pos hp', if_pos hp]
    exact congrArg (fun v : CanonicalCentres.ValTy n => (v : WithBot (CanonicalCentres.ValTy n)))
      (R.isInvValue.restrictOpen A hA U S hCan p hp)
  · have hp' : p ∉ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) A)
        (restrict U S)).cosupp := by rw [hCos]; exact hp
    rw [if_neg hp', if_neg hp]

private theorem lowerMask_towerIso {B D : CMfd.{u} n}
    (A : MarkedIdeal n X) (hA : IsInvDomain n A)
    (S : BlowupTower X Y)
    (hCan : IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) S)
    (φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (S' : BlowupTower B D)
    (χ : D ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (hIso : IsTowerIso φ S' S χ) (p : D) :
    lowerMask (MarkedIdeal.pullback φ A) S' p = lowerMask A S (χ p) := by
  let R := CanonicalCentres.canonicalInvariant n
  have hTest := Seq.ResolutionInvariantExt.isGeoTestTower_of_isCanonical R hA S hCan
  have hCos := IsTowerIso.cosupp_geoTransformAlong φ
    hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent hIso hTest
  unfold lowerMask
  by_cases hp : χ p ∈ (geoTransformAlong A S).cosupp
  · have hp' : p ∈ (geoTransformAlong (MarkedIdeal.pullback φ A) S').cosupp := by
      rw [hCos]; exact hp
    rw [if_pos hp', if_pos hp]
    exact congrArg (fun v : CanonicalCentres.ValTy n => (v : WithBot (CanonicalCentres.ValTy n)))
      (R.isInvValue.towerIso φ A hA S' S χ hIso hCan p hp)
  · have hp' : p ∉ (geoTransformAlong (MarkedIdeal.pullback φ A) S').cosupp := by
      rw [hCos]; exact hp
    rw [if_neg hp', if_neg hp]

/- Pure H/T chronology only. The same-E geometry donor is never used
as a native lower marked ideal or as an R numerical input. -/
private theorem oldCount_towerIso_native
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    {X' Y' : CMfd.{u} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (y : Y') :
    oldCount (Φ ⁻¹' H) T' y = oldCount H T (χ y) :=
  oldCount_towerIso (boundaryGeometry (X := X) M.E) rfl IdealWeightPowers.isCoherent_unitIdeal h
    hIso (boundaryGeometry_test M hM.isSNCDivisor T hT)
    (boundaryGeometry_original_history M H T hHistory) y

private theorem countAt_restrict_native
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (U : Opens X)
    (p : openPreimage T U) (j : ℕ) :
    countAt ((Subtype.val : U → X) ⁻¹' H) (restrict U T) p j = countAt H T p.val j :=
  countAt_restrict (boundaryGeometry (X := X) M.E) rfl IdealWeightPowers.isCoherent_unitIdeal h
    T (boundaryGeometry_test M hM.isSNCDivisor T hT)
    (boundaryGeometry_original_history M H T hHistory) U p j

private theorem countAt_towerIso_native
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    {X' Y' : CMfd.{u} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (y : Y') (j : ℕ) :
    countAt (Φ ⁻¹' H) T' y j = countAt H T (χ y) j :=
  countAt_towerIso (boundaryGeometry (X := X) M.E) rfl IdealWeightPowers.isCoherent_unitIdeal h
    hIso (boundaryGeometry_test M hM.isSNCDivisor T hT)
    (boundaryGeometry_original_history M H T hHistory) y j

private theorem birthYear_restrict_native
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (U : Opens X) (p : openPreimage T U) :
    birthYear ((Subtype.val : U → X) ⁻¹' H) (restrict U T) p = birthYear H T p.val :=
  birthYear_restrict (boundaryGeometry (X := X) M.E) rfl IdealWeightPowers.isCoherent_unitIdeal h
    T (boundaryGeometry_test M hM.isSNCDivisor T hT)
    (boundaryGeometry_original_history M H T hHistory) U p

private theorem birthYear_towerIso_native
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    {X' Y' : CMfd.{u} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (y : Y') :
    birthYear (Φ ⁻¹' H) T' y = birthYear H T (χ y) :=
  birthYear_towerIso (boundaryGeometry (X := X) M.E) rfl IdealWeightPowers.isCoherent_unitIdeal h
    hIso (boundaryGeometry_test M hM.isSNCDivisor T hT)
    (boundaryGeometry_original_history M H T hHistory) y

private theorem count_congr {B : CMfd.{u} n} {F G : Set B}
    (hF : IsNormalCrossingsCarrier (n := n) F) (hG : IsNormalCrossingsCarrier (n := n) G)
    (hEq : F = G) (p : B) : branchMultiplicity hF p = branchMultiplicity hG p := by
  subst G
  rfl

/-- Actual intrinsic counts at EVERY point of a restricted split head. The
whole head isomorphism, rather than a caller count equality, supplies its map. -/
private theorem oldCount_restricted_head
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (U : Opens X) (k : ℕ)
    (χ₀ : (split (restrict U T) k).1 ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage (head T k) U))
    (hHead : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (head (restrict U T) k) (restrict U (head T k)) χ₀)
    (z : (split (restrict U T) k).1) :
    oldCount ((Subtype.val : U → X) ⁻¹' H) (head (restrict U T) k) z =
      oldCount H (head T k) (χ₀ z).val := by
  let K := head T k
  let V := openPreimage K U
  let KTest := ((isGeoTestTower_iff_head_tail M T k).mp hT).1
  let KHistory := originalBranchHistory_head M T hHistory k
  let hc := (current_old_strata_eq_strict (boundaryGeometry (X := X) M.E) h K
    (boundaryGeometry_test M hM.isSNCDivisor K KTest)
    (boundaryGeometry_original_history M H K KHistory)).1
  let hv := boundaryAdapted_open V hc
  have hNCV := isNormalCrossingsCarrier_of_boundaryAdapted hv
  have hNoExc (p : (split (restrict U T) k).1) : p ∉ exceptionalLocus n χ₀ :=
    MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
      χ₀.contMDiff χ₀.symm.contMDiff χ₀.apply_symm_apply χ₀.symm_apply_apply p
  have hNC' := isNormalCrossingsCarrier_preimage χ₀.contMDiff hNoExc hNCV
  have hCarrier : strictAlong (head (restrict U T) k) ((Subtype.val : U → X) ⁻¹' H) =
      χ₀ ⁻¹' ((Subtype.val : V → (split T k).1) ⁻¹' strictAlong K H) := by
    have hs := hHead.strictAlong_eq ((Subtype.val : U → X) ⁻¹' H)
    change strictAlong (head (restrict U T) k) ((Subtype.val : U → X) ⁻¹' H) =
      χ₀ ⁻¹' strictAlong (restrict U K) ((Subtype.val : U → X) ⁻¹' H) at hs
    rw [strictAlong_restrict] at hs
    exact hs
  have hNC : IsNormalCrossingsCarrier (n := n)
      (strictAlong (head (restrict U T) k) ((Subtype.val : U → X) ⁻¹' H)) := by
    rw [hCarrier]
    exact hNC'
  rw [oldCount_eq _ hNC, oldCount_eq _ (isNormalCrossingsCarrier_of_boundaryAdapted hc)]
  exact (count_congr hNC hNC' hCarrier z).trans
    ((branchMultiplicity_diffeomorph χ₀ hNCV hNC' z).trans
      (branchMultiplicity_open V (isNormalCrossingsCarrier_of_boundaryAdapted hc) hNCV (χ₀ z)))

/-- The exact H-enriched open-restriction field for the SAME NEW value.
All actual history, birth-domain, whole-record and lower-canonical data are
produced internally from the original natural inputs and the given canonical T. -/
theorem markedStratum_history_value_restrictOpen
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (U : Opens X) (T : BlowupTower X Y)
    (hCan : IsCanonical M (markedStratumHistoryValue M H) T)
    (p : openPreimage T U) (hp : p.val ∈ (geoTransformAlong M T).cosupp) :
    markedStratumHistoryValue (MarkedIdeal.pullback (Subtype.val : U → X) M)
        ((Subtype.val : U → X) ⁻¹' H) (restrict U T) p = markedStratumHistoryValue M H T p.val := by
  obtain ⟨hT, hHistory, hBirths, _hFrame⟩ :=
    markedStratum_canonical_history_joint_interpretation M hM h T hCan
  obtain ⟨hA, hBirthCan, _hBirthMem⟩ := hBirths p.val hp
  have hCount := oldCount_restrict_native M hM.isWellFormed h T hT hHistory U p
  have hβ := birthYear_restrict_native M hM.isWellFormed h T hT hHistory U p
  let q := oldCount H T p.val
  let k := T.length - birthYear H T p.val
  have hIndex : (restrict U T).length -
      birthYear ((Subtype.val : U → X) ⁻¹' H) (restrict U T) p = k := by
    rw [length_restrict, hβ]
  let K := head T k
  let D := tail T k
  let TU := restrict U T
  let KU := head TU k
  let DU := tail TU k
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  let HU := (Subtype.val : U → X) ⁻¹' H
  let V := openPreimage K U
  let W := oldCountLowOpen H K q
  let W' := oldCountLowOpen HU KU q
  let I := W ⊓ V
  let O := nestedOpens W I
  let O₂ := nestedOpens V I
  obtain ⟨χ₀, hHead, hTail⟩ := exists_isTowerIso_split_restrict U T k
  have hCounts := oldCount_restricted_head M hM.isWellFormed h T hT hHistory U k χ₀ hHead
  have hMatch : ∀ z : (split TU k).1, z ∈ W' ↔ χ₀ z ∈ O₂ := by
    intro z
    change oldCount HU KU z ≤ q ↔
      (oldCount H K (χ₀ z).val ≤ q ∧ (χ₀ z).val ∈ V)
    rw [hCounts z]
    exact ⟨fun hz => ⟨hz, (χ₀ z).property⟩, fun hz => hz.1⟩
  let α := diffeoOpens χ₀ W' O₂ hMatch
  let η := α.trans ((nestedOpensDiffeo (n := n) (show I ≤ V from inf_le_right)).trans
    (nestedOpensDiffeo (n := n) (show I ≤ W from inf_le_left)).symm)
  have hηval (z : W') : ((η z).val : W).val = (χ₀ z.val).val := rfl
  let S := restrict W D
  let S' := restrict W' DU
  let S₀ := restrict O S
  have hLast := isTowerIso_mem_openPreimage_iff hTail hMatch
  have hIso₁ := isTowerIso_restrictOpens hMatch hTail hLast
  have hIso₂ := isTowerIso_restrict_nestedOpens (X := (split T k).1)
    (show I ≤ V from inf_le_right) D
  have hIso₃ := isTowerIso_restrict_nestedOpens (X := (split T k).1)
    (show I ≤ W from inf_le_left) D
  have hIso := hIso₁.trans (hIso₂.trans hIso₃.symm)
  let ξ := (diffeoOpens (opensCongr (openPreimage_head_tail U T k))
    (openPreimage DU W') (openPreimage (restrict V D) O₂) hLast).trans
      ((nestedDiffeo (n := n) (openPreimage D V)
        (openPreimage (restrict V D) O₂) (openPreimage D I)
        (mem_openPreimage_restrict_nestedOpens V I D) (openPreimage_mono D inf_le_right)).trans
      (nestedDiffeo (n := n) (openPreimage D W)
        (openPreimage (restrict W D) O) (openPreimage D I)
        (mem_openPreimage_restrict_nestedOpens W I D) (openPreimage_mono D inf_le_left)).symm)
  have hActualIso : IsTowerIso η S' S₀ ξ := hIso
  have hKTest := ((isGeoTestTower_iff_head_tail M T k).mp hT).1
  have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hKTest
  have hKI : (geoTransformAlong M K).ideal.IsCoherent := hKD.isWellFormed.isCoherent
  have hMUD := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hMUcoh : MU.ideal.IsCoherent := hMUD.isWellFormed.isCoherent
  have hMUN : IsClosedSubmanifold n MU.N := hMUD.isWellFormed.isClosedSubmanifold_N
  have hKUtest := isGeoTestTower_restrict U hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent K hKTest
  have hParentHead : geoTransformAlong MU KU =
      MarkedIdeal.pullback χ₀ (MarkedIdeal.pullback (Subtype.val : V → (split T k).1)
        (geoTransformAlong M K)) := by
    have hh := IsTowerIso.geoTransformAlong_eq
      (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      hMUN hMUcoh hHead hKUtest
    change geoTransformAlong (MarkedIdeal.pullback (id : U → U) MU) KU = _ at hh
    have hId : MarkedIdeal.pullback (id : U → U) MU = MU :=
      pullback_id (X := CMfd.of (n := n) U) MU hMUcoh
    rw [hId] at hh
    have hRU : geoTransformAlong MU (restrict U K) =
        MarkedIdeal.pullback (Subtype.val : V → (split T k).1) (geoTransformAlong M K) :=
      geoTransformAlong_restrict U hM.isWellFormed.isClosedSubmanifold_N
        hM.isWellFormed.isCoherent K hKTest
    change geoTransformAlong MU KU = MarkedIdeal.pullback χ₀
      (geoTransformAlong MU (restrict U K)) at hh
    rw [hRU] at hh
    exact hh
  let MW := MarkedIdeal.pullback (Subtype.val : W → (split T k).1) (geoTransformAlong M K)
  let MW' := MarkedIdeal.pullback (Subtype.val : W' → (split TU k).1) (geoTransformAlong MU KU)
  have hMWI : MW.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hKI
  have hParent : MW' = MarkedIdeal.pullback η
      (MarkedIdeal.pullback (Subtype.val : O → W) MW) := by
    change MarkedIdeal.pullback (Subtype.val : W' → (split TU k).1)
      (geoTransformAlong MU KU) = _
    rw [hParentHead]
    rw [pullback_comp (B := CMfd.of (n := n) V) (C := (split TU k).1)
        (D := CMfd.of (n := n) W')
        (MarkedIdeal.pullback (Subtype.val : V → (split T k).1) (geoTransformAlong M K))
        (isCoherent_pullback contMDiff_subtype_val hKI) χ₀
        (Subtype.val : W' → (split TU k).1) χ₀.contMDiff contMDiff_subtype_val]
    rw [pullback_comp (B := (split T k).1) (C := CMfd.of (n := n) V)
        (D := CMfd.of (n := n) W') (geoTransformAlong M K) hKI
        (Subtype.val : V → (split T k).1)
        (χ₀ ∘ (Subtype.val : W' → (split TU k).1)) contMDiff_subtype_val
        (χ₀.contMDiff.comp contMDiff_subtype_val)]
    rw [pullback_comp (B := CMfd.of (n := n) W) (C := CMfd.of (n := n) O)
        (D := CMfd.of (n := n) W') MW hMWI (Subtype.val : O → W) η
        contMDiff_subtype_val η.contMDiff]
    rw [pullback_comp (B := (split T k).1) (C := CMfd.of (n := n) W)
        (D := CMfd.of (n := n) W') (geoTransformAlong M K) hKI
        (Subtype.val : W → (split T k).1)
        ((Subtype.val : O → W) ∘ η) contMDiff_subtype_val
        (contMDiff_subtype_val.comp η.contMDiff)]
    rfl
  let ZW : Set W := {z | q ≤ oldCount H K z.val}
  let ZW' : Set W' := {z | q ≤ oldCount HU KU z.val}
  have hStratum : ZW' = η ⁻¹' ((Subtype.val : O → W) ⁻¹' ZW) := by
    ext z
    change (q ≤ oldCount HU KU z.val) ↔ q ≤ oldCount H K ((η z).val : W).val
    rw [hCounts z.val, hηval]
  have hKHistory := originalBranchHistory_head M T hHistory k
  have hZW : IsClosedSubmanifold n ZW :=
    (phaseAuxiliary_domain M hM h K hKTest hKHistory q).2
  let A := markedStratum (X := CMfd.of (n := n) W) MW ZW
  let A' := markedStratum (X := CMfd.of (n := n) W') MW' ZW'
  have hAeq : A' = MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : O → W) A) := by
    change markedStratum (X := CMfd.of (n := n) W') MW' ZW' = _
    rw [hParent, hStratum]
    have hOI : (MarkedIdeal.pullback (Subtype.val : O → W) MW).ideal.IsCoherent :=
      isCoherent_pullback contMDiff_subtype_val hMWI
    have hOZ : IsClosedSubmanifold n ((Subtype.val : O → W) ⁻¹' ZW) :=
      isClosedSubmanifold_preimage_val hZW O
    rw [markedStratum_pullback_diffeo η
      (MarkedIdeal.pullback (Subtype.val : O → W) MW) hOI hOZ]
    rw [markedStratum_pullback_val (X := CMfd.of (n := n) W) MW hMWI hZW O]
  have hp' : DU.proj p ∈ W' := by
    change oldCount HU KU (DU.proj p) ≤ q
    have hh := birthYear_spec HU TU p
    rw [countAt_eq_prefix_count] at hh
    have hCutU : TU.length - birthYear HU TU p = k := hIndex
    have hqU : oldCount HU TU p = q := hCount
    rw [hCutU, hqU] at hh
    exact hh.le
  let ps : openPreimage DU W' := ⟨p, hp'⟩
  have hξval : ((ξ ps).val : openPreimage D W).val = p.val := rfl
  have hA₀ : IsInvDomain n A := hA
  have hCan₀ : IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) S := hBirthCan
  let AO := MarkedIdeal.pullback (Subtype.val : O → W) A
  have hAO := InvDomainTowerAlong.isInvDomain_pullback_val O hA₀
  have hCanO := Seq.ResolutionInvariantExt.isCanonical_restrict
    (CanonicalCentres.canonicalInvariant n) hA₀ O S hCan₀
  have hMask : lowerMask A' S' ps = lowerMask A S (ξ ps).val := by
    rw [hAeq]
    have hIsoMask : lowerMask (MarkedIdeal.pullback η AO) S' ps =
        lowerMask AO S₀ (ξ ps) :=
      lowerMask_towerIso (X := CMfd.of (n := n) O)
        (Y := CMfd.of (n := n) (openPreimage S O))
        (B := CMfd.of (n := n) W') (D := CMfd.of (n := n) (openPreimage DU W'))
        AO hAO S₀ hCanO η S' ξ hActualIso ps
    have hOpenMask : lowerMask AO S₀ (ξ ps) = lowerMask A S (ξ ps).val :=
      lowerMask_restrict (X := CMfd.of (n := n) W)
        (Y := CMfd.of (n := n) (openPreimage D W)) A hA₀ S hCan₀ O (ξ ps)
    exact hIsoMask.trans hOpenMask
  have hPoint : (ξ ps).val = causalBirthPoint H T p.val := Subtype.ext hξval
  rw [hPoint] at hMask
  have hLex := congrArg (fun b : WithBot (CanonicalCentres.ValTy n) => toLex (q, b)) hMask
  have hEvalCut : evaluateCut (X := CMfd.of (n := n) U)
      (Y := CMfd.of (n := n) (openPreimage T U)) MU HU TU p q k = lowerMask A' S' ps := by
    change (if hz : p ∈ openPreimage DU W' then lowerMask A' S' ⟨p, hz⟩ else ⊥) = lowerMask A' S' ps
    have hMem : p ∈ openPreimage DU W' := hp'
    rw [dif_pos hMem]
  change markedStratumHistoryValue MU HU TU p = markedStratumHistoryValue M H T p.val
  rw [markedStratumHistoryValue_eq_evaluateCut (X := CMfd.of (n := n) U)
    (Y := CMfd.of (n := n) (openPreimage T U)) MU HU TU p]
  have hqU : oldCount HU TU p = q := hCount
  have hCutU : TU.length - birthYear HU TU p = k := hIndex
  rw [hqU, hCutU, hEvalCut]
  exact hLex

/-- Every map and history is the GIVEN actual one. The natural original
data and original canonicality internally produce the true whole birth
record and lower canonical tail; no T' canonical/history certificate occurs. -/
theorem markedStratum_history_value_towerIso
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    {X' Y' : CMfd.{u} n}
    (φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (T' : BlowupTower X' Y') (T : BlowupTower X Y)
    (χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (hIso : IsTowerIso φ T' T χ)
    (hCan : ResolutionInvariantSpec.IsCanonical M (markedStratumHistoryValue M H) T)
    (p : Y') (hp : χ p ∈ (geoTransformAlong M T).cosupp) :
    markedStratumHistoryValue (MarkedIdeal.pullback φ M) (φ ⁻¹' H) T' p =
      markedStratumHistoryValue M H T (χ p) := by
  obtain ⟨hT, hHistory, hBirths, _hFrame⟩ :=
    markedStratum_canonical_history_joint_interpretation M hM h T hCan
  obtain ⟨hA, hBirthCan, _hBirthMem⟩ := hBirths (χ p) hp
  have hCount := oldCount_towerIso_native M hM.isWellFormed h hIso hT hHistory p
  have hβ := birthYear_towerIso_native M hM.isWellFormed h hIso hT hHistory p
  let q := oldCount H T (χ p)
  let k := T.length - birthYear H T (χ p)
  let M' := MarkedIdeal.pullback φ M
  let H' := φ ⁻¹' H
  have hIndex : T'.length - birthYear H' T' p = k := by
    rw [hIso.length_eq, hβ]
  let K := head T k
  let D := tail T k
  let K' := head T' k
  let D' := tail T' k
  let W := oldCountLowOpen H K q
  let W' := oldCountLowOpen H' K' q
  obtain ⟨χ₀, hHead, hTail⟩ := BlowupTowerSplitIso.IsTowerIso.exists_split hIso k
  have hKTest := ((isGeoTestTower_iff_head_tail M T k).mp hT).1
  have hKHistory := originalBranchHistory_head M T hHistory k
  have hCounts (z : (split T' k).1) : oldCount H' K' z = oldCount H K (χ₀ z) :=
    oldCount_towerIso_native M hM.isWellFormed h hHead hKTest hKHistory z
  have hMatch : ∀ z : (split T' k).1, z ∈ W' ↔ χ₀ z ∈ W := by
    intro z
    change oldCount H' K' z ≤ q ↔ oldCount H K (χ₀ z) ≤ q
    rw [hCounts z]
  let η := diffeoOpens χ₀ W' W hMatch
  have hLast := isTowerIso_mem_openPreimage_iff hTail hMatch
  let ξ := diffeoOpens χ (openPreimage D' W') (openPreimage D W) hLast
  let S := restrict W D
  let S' := restrict W' D'
  have hActualIso : IsTowerIso η S' S ξ := isTowerIso_restrictOpens hMatch hTail hLast
  have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hKTest
  have hKI : (geoTransformAlong M K).ideal.IsCoherent := hKD.isWellFormed.isCoherent
  have hParentHead : geoTransformAlong M' K' = MarkedIdeal.pullback χ₀ (geoTransformAlong M K) :=
    IsTowerIso.geoTransformAlong_eq φ hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hHead hKTest
  let MW := MarkedIdeal.pullback (Subtype.val : W → (split T k).1) (geoTransformAlong M K)
  let MW' := MarkedIdeal.pullback (Subtype.val : W' → (split T' k).1) (geoTransformAlong M' K')
  have hParent : MW' = MarkedIdeal.pullback η MW := by
    change MarkedIdeal.pullback (Subtype.val : W' → (split T' k).1) (geoTransformAlong M' K') = _
    rw [hParentHead]
    exact ContactMarkedCanonical.pullback_pullback_of_comp_eq
      (𝔫 := geoTransformAlong M K) hKI (a := χ₀) (b := (Subtype.val : W' → (split T' k).1))
      (c := η) (d := (Subtype.val : W → (split T k).1))
      χ₀.contMDiff contMDiff_subtype_val η.contMDiff contMDiff_subtype_val (fun _ => rfl)
  have hMWI : MW.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hKI
  let ZW : Set W := {z | q ≤ oldCount H K z.val}
  let ZW' : Set W' := {z | q ≤ oldCount H' K' z.val}
  have hStratum : ZW' = η ⁻¹' ZW := by
    ext z
    change (q ≤ oldCount H' K' z.val) ↔ q ≤ oldCount H K (χ₀ z.val)
    rw [hCounts z.val]
  have hZW : IsClosedSubmanifold n ZW :=
    (phaseAuxiliary_domain M hM h K hKTest hKHistory q).2
  let A := markedStratum (X := CMfd.of (n := n) W) MW ZW
  let A' := markedStratum (X := CMfd.of (n := n) W') MW' ZW'
  have hAeq : A' = MarkedIdeal.pullback η A := by
    change markedStratum (X := CMfd.of (n := n) W') MW' ZW' = _
    rw [hParent, hStratum]
    exact markedStratum_pullback_diffeo (X := CMfd.of (n := n) W)
      (X' := CMfd.of (n := n) W') η MW hMWI hZW
  have hpOld : χ p ∈ openPreimage D W := (causalBirthPoint H T (χ p)).property
  have hp' : p ∈ openPreimage D' W' := (hLast p).mpr hpOld
  let ps : openPreimage D' W' := ⟨p, hp'⟩
  have hPoint : ξ ps = causalBirthPoint H T (χ p) := Subtype.ext rfl
  have hA₀ : IsInvDomain n A := hA
  have hCan₀ : IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) S := hBirthCan
  have hMask : lowerMask A' S' ps = lowerMask A S (causalBirthPoint H T (χ p)) := by
    rw [hAeq]
    have he := lowerMask_towerIso (X := CMfd.of (n := n) W)
      (Y := CMfd.of (n := n) (openPreimage D W))
      (B := CMfd.of (n := n) W') (D := CMfd.of (n := n) (openPreimage D' W'))
      A hA₀ S hCan₀ η S' ξ hActualIso ps
    rw [hPoint] at he
    exact he
  have hEvalCut : evaluateCut (X := X') (Y := Y') M' H' T' p q k = lowerMask A' S' ps := by
    change (if hz : p ∈ openPreimage D' W' then lowerMask A' S' ⟨p, hz⟩ else ⊥) = lowerMask A' S' ps
    rw [dif_pos hp']
  change markedStratumHistoryValue M' H' T' p = markedStratumHistoryValue M H T (χ p)
  rw [markedStratumHistoryValue_eq_evaluateCut (X := X') (Y := Y') M' H' T' p]
  have hq' : oldCount H' T' p = q := hCount
  rw [hq', hIndex, hEvalCut]
  exact congrArg (fun b : WithBot (CanonicalCentres.ValTy n) => toLex (q, b)) hMask


end
end Hironaka.HironakaOriginalNCMarkedStratumNaturality
