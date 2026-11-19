import Hironaka.Resolution.HironakaG8RankedGlobalTest
import Hironaka.Resolution.HironakaSharpActualCurveGlobalPrefixLocalHistories
import Hironaka.Resolution.HironakaSharpActualCurveUniformPrefixSuccessors

/-! Finite physical gluing on disjoint sheet opens with one common clock. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8DisjointClockAtlas

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  HironakaG8RankedGlobalTest HironakaSharpActualCurveChosenOverlapCocycle
  HironakaSharpActualCurveCommonOpenCocycle HironakaG8StageRankCoherence
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveOverlapMaps
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveGlobalPrefixLocalHistories
  HironakaSharpActualCurveGlobalPrefixTowers HironakaSharpActualCurveGlobalPrefixTests
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformPrefixSuccessors MaxLocusLocal
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal

variable {n : ℕ} {X : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

private noncomputable def emptyDiffeomorph (A B : CMfd.{0} n) [IsEmpty A] [IsEmpty B] :
    A ≃ₘ⟮𝓘c,𝓘c⟯ B where
  toEquiv := Equiv.equivOfIsEmpty _ _
  contMDiff_toFun := fun x => isEmptyElim x
  contMDiff_invFun := fun x => isEmptyElim x

/-- Any two towers over empty bases with equal raw lengths have a strict
comparison over the prescribed base map. -/
theorem strict_comparison_of_empty_base {A B Y Z : CMfd.{0} n} [IsEmpty A] [IsEmpty B]
    (f : A ≃ₘ⟮𝓘c,𝓘c⟯ B) (S : BlowupTower A Y) (T : BlowupTower B Z)
    (hLen : S.length = T.length) :
    ∃ e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z, IsTowerIso f S T e := by
  induction S generalizing Z with
  | refl =>
    cases T with
    | refl => exact ⟨f,.refl⟩
    | step => simp [BlowupTower.length_step] at hLen
  | @step C Y S H π hπ ih =>
    cases T with
    | refl => simp [BlowupTower.length_step] at hLen
    | @step D Z T J ρ hρ =>
      obtain ⟨g,hg⟩ := ih T (Nat.succ.inj hLen)
      let _ : IsEmpty Y := ⟨fun y => isEmptyElim (S.proj (π y))⟩
      let _ : IsEmpty Z := ⟨fun z => isEmptyElim (T.proj (ρ z))⟩
      exact ⟨emptyDiffeomorph Y Z,.step hg hπ hρ _ (fun y => isEmptyElim y)
        (Set.ext fun y => isEmptyElim (S.proj y))⟩

/-- Literal disjoint open sheets need pairwise comparisons only on empty
overlaps. One common raw clock suffices, including padded identity stages. -/
theorem strictPairwiseComparisons_of_disjoint
    {I : Type} (U : I → Opens X)
    (hDisj : Pairwise fun i j => Disjoint (U i : Set X) (U j : Set X))
    {Y : I → CMfd.{0} n} (T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i))
    (clock : ℕ) (hLen : ∀ i, (T i).length = clock) :
    StrictPairwiseComparisons U T := by
  classical
  intro i j
  by_cases h : i = j
  · subst j
    let O := U i ⊓ U i
    let S := localPaddedHistory (U i) O .refl (T i) (max (T i).length (T i).length)
    refine ⟨Diffeomorph.refl 𝓘c (localEndpoint (U i) O .refl (T i)) ∞,?_⟩
    apply BlowupTowerSplitIso.IsTowerIso.congr_base (IsTowerIso.refl_self S)
    intro x
    rfl
  · let O := U i ⊓ U j
    let _ : IsEmpty (CMfd.of (n := n) (nestedOpens (U i) O)) :=
      ⟨fun x => Set.disjoint_left.mp (hDisj h) x.property.1 x.property.2⟩
    let _ : IsEmpty (CMfd.of (n := n) (nestedOpens (U j) O)) :=
      ⟨fun x => Set.disjoint_left.mp (hDisj h) x.property.1 x.property.2⟩
    apply strict_comparison_of_empty_base
    simp [localPaddedHistory,paddedHistory,length_restrict,BlowupTower.length_append,
      identityEmptyTail_length,hLen]


open HironakaSharpActualCurveOriginalGrowingHistory

/-- Glue a finite physical tower on disjoint sheets from one raw clock,
with every sheet comparison strict and with exact original TEST. -/
theorem exists_disjoint_clock_test_tower
    {I : Type} (U : I → Opens X) (hCover : ∀ x : X, ∃ i, x ∈ U i)
    (hDisj : Pairwise fun i j => Disjoint (U i : Set X) (U j : Set X))
    {Y : I → CMfd.{0} n} (T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i))
    (clock : ℕ) (hLen : ∀ i, (T i).length = clock+1)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U i → X) M) (T i)) :
    ∃ (Z : CMfd.{0} n) (R : BlowupTower X Z),
      R.length = clock+1 ∧ IsGeoTestTower M R ∧
      ∀ i, ∃ e : Y i ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (openPreimage R (U i)),
        IsTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) (U i)) ∞)
          (T i) (restrict (U i) R) e := by
  classical
  let A := actualEndpointHistories U T (strictPairwiseComparisons_of_disjoint U hDisj T (clock+1) hLen)
  let R := uniformOriginalPositiveTower A hCover clock
  have hTR : IsGeoTestTower M R := by
    apply uniform_growing_seq_original_test A hCover M hM.isClosedSubmanifold_N hM.isCoherent _ (clock+1)
    intro i
    change IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U i → X) M)
      ((BlowupTower.refl : BlowupTower (CMfd.of (n := n) (U i))
        (CMfd.of (n := n) (U i))).append (T i))
    rw [BlowupTower.refl_append]
    exact hTest i
  refine ⟨_,R,uniformOriginalPositiveTower_length A hCover clock,hTR,?_⟩
  intro i
  let Data (p : Σ V, BlowupTower (CMfd.of (n := n) (U i)) V) : Prop :=
    ∃ e : p.1 ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (openPreimage R (U i)),
      IsTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) (U i)) ∞) p.2 (restrict (U i) R) e
  have hData : Data (uniformPrefix ((A.prefixTower i).append (A.tail i)) (clock+1)) :=
    ⟨localOriginalPrefixBiholomorphism A hCover clock i,localOriginalPrefix_isTowerIso A hCover clock i⟩
  have hEq : uniformPrefix ((A.prefixTower i).append (A.tail i)) (clock+1) = ⟨Y i,T i⟩ := by
    change uniformPrefix ((BlowupTower.refl : BlowupTower (CMfd.of (n := n) (U i))
      (CMfd.of (n := n) (U i))).append (T i)) (clock+1) = _
    rw [BlowupTower.refl_append,uniformPrefix_of_length_le (T i) _ (hLen i).le]
    simp only [hLen i,Nat.sub_self,identityEmptyTail,BlowupTower.append_refl]
    rfl
  change Data ⟨Y i,T i⟩
  exact hEq ▸ hData

end Hironaka.HironakaG8DisjointClockAtlas
