/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsOrderedMonomialTail
import Hironaka.Invariant.NonmonomialOrderLocal

/-!
# The genuine whole residual along general normal-crossings separation

The actual intrinsic nonmonomial ideal of the same original controlled
marking-one ideal is the genuine strict original ideal at every separation
prefix. Its actual nonmonomial order is the intrinsic original branch count.
Local branches and self-intersections need no global choice of branches.

This proves the first general-invariant entry. It does not identify its lower
history-sensitive entries or assert admissibility for an unrelated ideal.
Blueprint: `hironaka-normal-crossings-actual-residual-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsActualResidual
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaNormalCrossingsOrderedMonomialTail HironakaNormalCrossingsFiniteMarkedCompletion
  HironakaNormalCrossingsOriginalExponents HironakaNormalCrossingsMarkedAdmissibility
  HironakaNormalCrossingsTotalIdeal HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsBoundarySeparation HironakaNormalCrossingsLocalBranches
  HironakaNormalCrossingsMultiplicityStrata HironakaStageCenters
  HironakaSNCSupportedMonomialIdeal HironakaDivisorResidual
  NormalCrossings BlowupTowers BlowupTowerTransforms BlowupFlatCoordinates
  MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers GermIdealOrder
  MonomialPart MonomialPartAlong NonmonomialOrderLocal RelativePrincipalizationSpan
  GermIdealTotalTransform InvertibleIdealQuotient DivisorExponent
noncomputable section
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem indexedProduct_invertible (F : List (Set M × ℕ))
    (hF : ∀ p ∈ F, (vanishingIdeal (n := n) p.1).IsInvertible) :
    (componentPowerProduct (n := n) F).IsInvertible := by
  induction F with
  | nil => exact BlowupExceptionalDivisor.isInvertible_unitIdeal
  | cons p F ih =>
    exact isInvertible_mul
      (BlowupExceptionalDivisor.isInvertible_idealPow (hF p (by simp)) p.2)
      (ih fun q hq => hF q (List.mem_cons_of_mem p hq))

private theorem jointFactor_invertible (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (componentPowerProduct (n := n) F).IsInvertible := by
  apply indexedProduct_invertible
  intro p hp
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (List.mem_map.mpr ⟨p,hp,rfl⟩ : p.1 ∈ F.map Prod.fst)
  exact hi ▸ isInvertible_vanishingIdeal_snc_member hF i

private theorem indexedProduct_support_subset (hn : 0 < n) (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (componentPowerProduct (n := n) F).zeroLocus ⊆ ⋃ W ∈ F.map Prod.fst, W := by
  intro x hx
  have hcoh := DivisorMetric.isCoherent_of_isInvertible (jointFactor_invertible F hF)
  have hc : x ∈ (monomialMarkedIdeal (n := n) (F.map Prod.fst) F).cosupp := by
    change x ∈ cosupport n univ (componentPowerProduct (n := n) F) 1
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg),univ_inter]
    exact hx
  obtain ⟨i,hi,_⟩ := (mem_cosupp_indexed_product_iff hn F hF x).mp hc
  exact mem_iUnion₂.mpr ⟨(F.get i).1,List.mem_map.mpr ⟨F.get i,List.get_mem _ _,rfl⟩,hi⟩

/-- The actual whole joint ideal has exactly the actual weighted SNC monomial factor. -/
theorem monomialPart_joint_eq_componentPowerProduct (hn : 0 < n)
    {H : Set M} (F : List (Set M × ℕ))
    (h : IsBoundaryAdaptedCarrier (n := n) H (F.map Prod.fst)) :
    monomialPart n ((componentPowerProduct (n := n) F).mul (vanishingIdeal (n := n) H))
      (F.map Prod.fst) = componentPowerProduct (n := n) F := by
  have hE := isSNCDivisor_of_boundaryAdapted h
  have hF : ∀ p ∈ F, (vanishingIdeal (n := n) p.1).IsInvertible := by
    intro p hp
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp (List.mem_map.mpr ⟨p,hp,rfl⟩ : p.1 ∈ F.map Prod.fst)
    exact hi ▸ isInvertible_vanishingIdeal_snc_member hE i
  have hsame : monomialPart n
      ((componentPowerProduct (n := n) F).mul (vanishingIdeal (n := n) H)) (F.map Prod.fst) =
      monomialPart n (componentPowerProduct (n := n) F) (F.map Prod.fst) := by
    apply GermIdeal.ext
    funext x g
    have he : ∀ i : Fin (F.map Prod.fst).length, x ∈ (F.map Prod.fst).get i →
        divExp n ((componentPowerProduct (n := n) F).mul (vanishingIdeal (n := n) H))
          ((F.map Prod.fst).get i) x =
        divExp n (componentPowerProduct (n := n) F) ((F.map Prod.fst).get i) x := by
      intro i hi
      let j : Fin F.length := ⟨i.val,by simpa only [List.length_map] using i.isLt⟩
      have hj : (F.map Prod.fst).get i = (F.get j).1 := by
        simp only [j,List.get_eq_getElem,List.getElem_map]
      rw [hj] at hi ⊢
      obtain ⟨_,_,_,_,_,_,hd,_⟩ := exists_joint_whole_weighted_exponents hn F h hF x
      exact (hd j hi).trans (indexed_product_divExp hn F hE x j hi).symm
    apply propext
    constructor
    · rintro ⟨hg,hm⟩
      exact ⟨hg,fun i hi => he i hi ▸ hm i hi⟩
    · rintro ⟨hg,hm⟩
      exact ⟨hg,fun i hi => (he i hi).symm ▸ hm i hi⟩
  rw [hsame]
  exact (ideal_eq_monomialPart_of_support_subset
    (⟨_,jointFactor_invertible F hE⟩ : EffectiveDivisor n M) _ hE
    (indexedProduct_support_subset hn F hE)).symm

/-- The genuine intrinsic WHOLE residual is the actual original NC vanishing ideal. -/
theorem nonmonomialPart_joint_eq_original (hn : 0 < n)
    {H : Set M} (F : List (Set M × ℕ))
    (h : IsBoundaryAdaptedCarrier (n := n) H (F.map Prod.fst)) :
    nonmonomialPart n ((componentPowerProduct (n := n) F).mul (vanishingIdeal (n := n) H))
      (F.map Prod.fst) = vanishingIdeal (n := n) H := by
  let P := componentPowerProduct (n := n) F
  let J := vanishingIdeal (n := n) H
  let I := P.mul J
  have hE := isSNCDivisor_of_boundaryAdapted h
  have hP : P.IsInvertible := jointFactor_invertible F hE
  have hJ : J.IsInvertible := isInvertible_vanishingIdeal_normalCrossingsCarrier
    (isNormalCrossingsCarrier_of_boundaryAdapted h)
  have hI : I.IsInvertible := isInvertible_mul hP hJ
  have hIc := DivisorMetric.isCoherent_of_isInvertible hI
  have hN := isInvertible_nonmonomialPart hn (⟨I,hI⟩ : EffectiveDivisor n M) _ hE
  apply eq_of_invertible_mul_left_eq hN hJ hP
  have hf := eq_mul_monomialPart hn hE hIc
    (fun x => HironakaDivisorPowers.isNonzeroAt_of_isInvertible hI x)
  rw [monomialPart_joint_eq_componentPowerProduct hn F h] at hf
  exact (RestrictLeCalculus.mul_comm' P (nonmonomialPart n I (F.map Prod.fst))).trans hf.symm

private theorem mem_of_spanOn_univ {I : GermIdeal n M} (hI : I.IsCoherent)
    {x : M} {g : M → ℂ} (hg : HolomorphicAt n g x)
    (hs : IsInSpanOnAt (n := n) univ (I.mem x) x g) : I.mem x g := by
  obtain ⟨N,s,a,hs,ha,heq⟩ := hs
  exact mem_of_isInSpanAt_mem hI
    ⟨hg,N,s,a,hs,ha,heq.mono fun y hy => hy (mem_univ y)⟩

private theorem restrictOn_univ_eq {I : GermIdeal n M} (hI : I.IsCoherent) :
    RestrictedIdealExtension.restrictOn n univ I = I := by
  apply GermIdeal.ext
  funext x g
  apply propext
  exact ⟨fun hg => mem_of_spanOn_univ hI hg.1 hg.2,
    fun hg => ⟨GermIdeal.IsCoherent.holomorphicAt_mem hI hg,
      IsInSpanAt.restrict (isInSpanAt_self hg (GermIdeal.IsCoherent.holomorphicAt_mem hI hg))⟩⟩

/-- Along the whole actual manifold, the intrinsic monomial ideal is the ambient one. -/
theorem monomialPartAlong_univ_eq (_hn : 0 < n) {E : List (Set M)}
    (hE : IsSNCDivisor n E) (I : GermIdeal n M) :
    monomialPartAlong n univ I E = monomialPart n I E := by
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · rintro ⟨hg,hm⟩
    refine ⟨hg,fun i hi => ?_⟩
    have hs := hm i (mem_univ x) hi
    rw [DivisorExponentAlong.divExpAlong_univ] at hs
    have hc := GermIdealPullbackCalculus.isCoherent_idealPow
      (DivisorMetric.isCoherent_of_isInvertible (isInvertible_vanishingIdeal_snc_member hE i))
      (divExp n I (E.get i) x)
    exact mem_of_spanOn_univ hc hg hs
  · rintro ⟨hg,hm⟩
    refine ⟨hg,fun i _ hi => ?_⟩
    rw [DivisorExponentAlong.divExpAlong_univ]
    exact IsInSpanAt.restrict (isInSpanAt_self (hm i hi) hg)

/-- Along-univ and ambient residuals agree as COMPLETE actual germ ideals. -/
theorem nonmonomialPartAlong_univ_eq (hn : 0 < n) {E : List (Set M)}
    (hE : IsSNCDivisor n E) {I : GermIdeal n M} (hI : I.IsCoherent) :
    nonmonomialPartAlong n univ I E = nonmonomialPart n I E := by
  unfold nonmonomialPartAlong RestrictedIdealQuotient.colonAlong
  rw [restrictOn_univ_eq hI,monomialPartAlong_univ_eq hn hE I]
  exact (nonmonomialPart_eq_colon I E).symm

/-- The WHOLE along-univ residual of the actual joint ideal is the original NC ideal. -/
theorem nonmonomialPartAlong_joint_eq_original (hn : 0 < n)
    {H : Set M} (F : List (Set M × ℕ))
    (h : IsBoundaryAdaptedCarrier (n := n) H (F.map Prod.fst)) :
    nonmonomialPartAlong n univ
      ((componentPowerProduct (n := n) F).mul (vanishingIdeal (n := n) H))
      (F.map Prod.fst) = vanishingIdeal (n := n) H := by
  have hE := isSNCDivisor_of_boundaryAdapted h
  have hIc := DivisorMetric.isCoherent_of_isInvertible (isInvertible_mul
    (jointFactor_invertible F hE)
    (isInvertible_vanishingIdeal_normalCrossingsCarrier (isNormalCrossingsCarrier_of_boundaryAdapted h)))
  rw [nonmonomialPartAlong_univ_eq hn hE hIc]
  exact nonmonomialPart_joint_eq_original hn F h

variable {A D : CMfd.{u} n}

/-- Every actual separation prefix has the SAME whole residual as its actual strict original. -/
theorem higherSeparationCentres_nonmonomialPartAlong (hn : 0 < n)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H)
    (T : BlowupTower A D)
    (hc : StageCentres (fun R C => IsHigherSeparationCentre (n := n)
      (strictTransform n R.proj H) (geoTransformAlong (originalMarkedIdeal H) R).E C) T) :
    nmPart (geoTransformAlong (originalMarkedIdeal H) T) =
      vanishingIdeal (n := n) (strictTransform n T.proj H) := by
  have htest := (higherSeparationCentres_isGeoTestTower_and_strict_subset_cosupp hH T hc).1
  have hcoh := (isInvDomain_originalMarkedIdeal hH).isWellFormed.isCoherent
  have hN := (pullback_eq_mul_geoTransformAlong
    (originalMarkedIdeal H) rfl hcoh T htest).1
  have hpair := higherSeparationCentres_pair hH T hc
  let F := recordedOriginalWeights H 1 T hc
  have hcar : F.map Prod.fst = (geoTransformAlong (originalMarkedIdeal H) T).E :=
    recordedOriginalWeights_carriers H 1 T hc
  have hpairF : IsBoundaryAdaptedCarrier (n := n) (strictTransform n T.proj H) (F.map Prod.fst) :=
    hcar.symm ▸ hpair
  change nonmonomialPartAlong n (geoTransformAlong (originalMarkedIdeal H) T).N
    (geoTransformAlong (originalMarkedIdeal H) T).ideal
    (geoTransformAlong (originalMarkedIdeal H) T).E = _
  rw [hN,higherSeparationCentres_controlled_dictionary hH T hc,← hcar]
  exact nonmonomialPartAlong_joint_eq_original hn F hpairF

/-- The ACTUAL first general-invariant entry is the number of genuine strict original branches. -/
theorem higherSeparationCentres_nmOrd (hn : 0 < n)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H)
    (T : BlowupTower A D)
    (hc : StageCentres (fun R C => IsHigherSeparationCentre (n := n)
      (strictTransform n R.proj H) (geoTransformAlong (originalMarkedIdeal H) R).E C) T)
    (x : D) :
    nmOrd (geoTransformAlong (originalMarkedIdeal H) T) x =
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted
        (higherSeparationCentres_pair hH T hc)) x := by
  let r := branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted
    (higherSeparationCentres_pair hH T hc)) x
  have htest := (higherSeparationCentres_isGeoTestTower_and_strict_subset_cosupp hH T hc).1
  have hcoh := (isInvDomain_originalMarkedIdeal hH).isWellFormed.isCoherent
  have hN := (pullback_eq_mul_geoTransformAlong
    (originalMarkedIdeal H) rfl hcoh T htest).1
  have hm (q : ℕ) : x ∈ ordGe (geoTransformAlong (originalMarkedIdeal H) T) q ↔ q ≤ r := by
    change x ∈ cosupport n (geoTransformAlong (originalMarkedIdeal H) T).N
      (nmPart (geoTransformAlong (originalMarkedIdeal H) T)) q ↔ _
    rw [hN,higherSeparationCentres_nonmonomialPartAlong hn hH T hc]
    exact mem_original_order_cosupport_iff
      (isNormalCrossingsCarrier_of_boundaryAdapted (higherSeparationCentres_pair hH T hc)) x q
  have hnot : x ∉ ordGe (geoTransformAlong (originalMarkedIdeal H) T) (r+1) := by
    rw [hm]
    omega
  apply Nat.le_antisymm (nmOrd_le_of_notMem hnot)
  cases hr : r with
  | zero => omega
  | succ s =>
    have hs := succ_le_nmOrd_of_mem ⟨r,hnot⟩ ((hm (s+1)).mpr (by omega))
    omega

/-- A genuine next separation centre is the WHOLE maximum of the actual first invariant entry. -/
theorem higherSeparationCentre_eq_nmOrd_maxLocus (hn : 0 < n)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H)
    (T : BlowupTower A D)
    (hc : StageCentres (fun R C => IsHigherSeparationCentre (n := n)
      (strictTransform n R.proj H) (geoTransformAlong (originalMarkedIdeal H) R).E C) T)
    {C : Set D} (hC : IsHigherSeparationCentre (n := n)
      (strictTransform n T.proj H) (geoTransformAlong (originalMarkedIdeal H) T).E C) :
    C = ResolutionDriver.maxLocus (nmOrd (geoTransformAlong (originalMarkedIdeal H) T))
      (geoTransformAlong (originalMarkedIdeal H) T).cosupp := by
  have hsub := (higherSeparationCentres_isGeoTestTower_and_strict_subset_cosupp hH T hc).2
  have hCC : C ⊆ (geoTransformAlong (originalMarkedIdeal H) T).cosupp :=
    (higherSeparationCentre_subset hC).trans hsub
  obtain ⟨hpair,r,_,hbound,hceq,hne⟩ := hC
  have hord (x : D) : nmOrd (geoTransformAlong (originalMarkedIdeal H) T) x =
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hpair) x :=
    higherSeparationCentres_nmOrd hn hH T hc x
  apply Set.ext
  intro x
  constructor
  · intro hx
    refine ⟨hCC hx,fun y _ => ?_⟩
    rw [hord y,hord x]
    rw [hceq] at hx
    exact (hbound y).trans hx
  · rintro ⟨_,hmax⟩
    obtain ⟨c,hcC⟩ := hne
    have hcx := hmax c (hCC hcC)
    rw [hord c,hord x] at hcx
    rw [hceq]
    rw [hceq] at hcC
    exact hcC.trans hcx

end
end Hironaka.HironakaNormalCrossingsActualResidual
