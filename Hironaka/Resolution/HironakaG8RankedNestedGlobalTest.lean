import Hironaka.Resolution.HironakaG8RankedGlobalTest
import Hironaka.Resolution.HironakaG8PhysicalChartOccupiedLifts
import Hironaka.Resolution.HironakaG8CofinalEventLimit
import Hironaka.Resolution.HironakaSharpActualCurvePaddedComparisonRestriction

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8RankedNestedGlobalTest
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals HironakaG8RankedTestCompression HironakaG8RankedEmptyPadding
  HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison HironakaG3EmptyAwareHistory
  HironakaSharpActualCurveChosenOverlapCocycle HironakaSharpActualCurveOverlapMaps
  HironakaSharpActualCurvePaddedComparisonRestriction HironakaSharpActualCurveEmptyPadding
  HironakaSharpActualCurveCommonOpenCocycle BlowupTowerIsomorphism MaxLocusLocal HironakaG8RankedGlobalTest

variable {n : ℕ} {X : CMfd.{0} n}
private theorem full_open_equiv (A : CMfd.{0} n) (U : Opens A) (hU : ∀ x : A, x ∈ U) :
    ∃ e : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U,
      ∀ x : A, (e x).val = x := by
  let e : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U := {
    toFun x := ⟨x,hU x⟩
    invFun := Subtype.val
    left_inv _ := rfl
    right_inv _ := rfl
    contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk contMDiff_id hU
    contMDiff_invFun := contMDiff_subtype_val }
  exact ⟨e,fun _ => rfl⟩

private theorem full_restriction_iso {A B : CMfd.{0} n} (T : BlowupTower A B)
    (U : Opens A) (hU : ∀ x : A, x ∈ U) :
    ∃ e : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U,
      (∀ x : A, (e x).val = x) ∧
      ∃ η : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T U),
        (∀ y : B, (η y).val = y) ∧ IsTowerIso e T (restrict U T) η := by
  induction T with
  | refl =>
    obtain ⟨e,he⟩ := full_open_equiv A U hU
    exact ⟨e,he,e,he,.refl⟩
  | @step B D T C π hπ ih =>
    obtain ⟨e,he,χ,hχ,hIso⟩ := ih
    let V := openPreimage (.step T C π hπ) U
    obtain ⟨η,hη⟩ := full_open_equiv D V (fun z => hU (T.proj (π z)))
    refine ⟨e,he,η,hη,IsTowerIso.step hIso _ _ η ?_ ?_⟩
    · intro z
      apply Subtype.ext
      change π (η z).val = (χ (π z)).val
      rw [hη,hχ]
    · ext z
      change (χ z).val ∈ C ↔ z ∈ C
      rw [hχ]


/-- A nested comparison on the whole smaller chart yields strict histories
on the two literal presentations of the overlap. -/
theorem strict_common_open_of_nested
    {U V O : Opens X} (hOU : O ≤ U) (hOV : O ≤ V) (hUO : U ≤ O)
    {Y Z : CMfd.{0} n}
    {M : MarkedIdeal n (CMfd.of (n := n) U)} {N : MarkedIdeal n (CMfd.of (n := n) V)}
    {T : BlowupTower (CMfd.of (n := n) U) Y} {S : BlowupTower (CMfd.of (n := n) V) Z}
    {rankT : {k // Occupied T k} → ℕ} {rankS : {k // Occupied S k} → ℕ}
    (dT : RankedTestCompression M T rankT) (dS : RankedTestCompression N S rankS)
    {φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (nestedOpens V O)}
    (hφ : ∀ x : U, (φ x).val.val = x.val)
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage S (nestedOpens V O))}
    (h : EmptyAwareTowerIso φ T (restrict (nestedOpens V O) S) ψ)
    (hRank : ∀ p, rankT p = rankS (occupiedLiftOnOpen (nestedOpens V O) S h p))
    (k : ℕ) (hT : dT.clock ≤ k) (hS : dS.clock ≤ k) :
    ∃ χ : localEndpoint U O .refl dT.decoration.pad
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ localEndpoint V O .refl dS.decoration.pad,
      IsTowerIso (commonOpenBase U V O hOU hOV)
        (localPaddedHistory U O .refl dT.decoration.pad k)
        (localPaddedHistory V O .refl dS.decoration.pad k) χ := by
  have hThroughT : dT.decoration.through k = paddedHistory .refl dT.decoration.pad k := by
    simp [RankedTower.through, paddedHistory, dT.decoration.pad_length]
  have hThroughS : dS.decoration.through k = paddedHistory .refl dS.decoration.pad k := by
    simp [RankedTower.through, paddedHistory, dS.decoration.pad_length]
  have hχ := strict_nested_overlap_after_test_compression dT dS (nestedOpens V O) h hRank k hT hS
  rw [hThroughT, hThroughS] at hχ
  obtain ⟨χ,hχ⟩ := hχ
  have hβ := full_restriction_iso (paddedHistory .refl dT.decoration.pad k) (nestedOpens U O)
    (fun x => hUO x.property)
  obtain ⟨α,hα,β,_,hβ⟩ := hβ
  obtain ⟨eU,heU,_⟩ := exists_padded_history_open_flattening .refl dT.decoration.pad k (nestedOpens U O)
  obtain ⟨eV,heV,_⟩ := exists_padded_history_open_flattening .refl dS.decoration.pad k (nestedOpens V O)
  refine ⟨_, BlowupTowerSplitIso.IsTowerIso.congr_base
    (((heU.symm.trans hβ.symm).trans hχ).trans heV) ?_⟩
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change x.val.val = (φ (α.symm x)).val.val
  rw [hφ]
  have hPoint := hα (α.symm x)
  rw [α.apply_symm_apply] at hPoint
  exact congrArg Subtype.val hPoint

/-- The source atlas comparison and its rank agreement in the nested orientation. -/
def NestedRankComparison {U V O : Opens X}
    {Y Z : CMfd.{0} n}
    (T : BlowupTower (CMfd.of (n := n) U) Y) (S : BlowupTower (CMfd.of (n := n) V) Z)
    (rankT : {k // Occupied T k} → ℕ) (rankS : {k // Occupied S k} → ℕ) : Prop :=
  ∃ φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (nestedOpens V O),
    (∀ x : U, (φ x).val.val = x.val) ∧
    ∃ ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage S (nestedOpens V O)),
      ∃ h : EmptyAwareTowerIso φ T (restrict (nestedOpens V O) S) ψ,
        ∀ p, rankT p = rankS (occupiedLiftOnOpen (nestedOpens V O) S h p)

/-- A chain of nested physical chart comparisons preserving occupied ranks
supplies every strict common-open comparison required for globalization. -/
theorem strict_pairwise_of_nested (U : ℕ → Opens X)
    {Y : ℕ → CMfd.{0} n}
    {T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i)}
    {M : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i))}
    {rank : ∀ i, {k // Occupied (T i) k} → ℕ}
    (d : ∀ i, RankedTestCompression (M i) (T i) (rank i))
    (hMono : Monotone U)
    (hNested : ∀ i j, i ≤ j →
      NestedRankComparison (O := U i ⊓ U j) (T i) (T j) (rank i) (rank j)) :
    StrictPairwiseComparisons U (fun i => (d i).decoration.pad) := by
  intro i j
  rw [(d i).decoration.pad_length, (d j).decoration.pad_length]
  rcases le_total i j with hij | hji
  · obtain ⟨φ,hφ,ψ,h,hRank⟩ := hNested i j hij
    exact strict_common_open_of_nested inf_le_left inf_le_right (le_inf le_rfl (hMono hij))
      (d i) (d j) hφ h hRank _ (le_max_left _ _) (le_max_right _ _)
  · have hNest := hNested j i hji
    rw [inf_comm (U j) (U i)] at hNest
    obtain ⟨φ,hφ,ψ,h,hRank⟩ := hNest
    obtain ⟨e,he⟩ := strict_common_open_of_nested inf_le_right inf_le_left
      (le_inf (hMono hji) le_rfl) (d j) (d i) hφ h hRank (max (d i).clock (d j).clock)
      (le_max_right _ _) (le_max_left _ _)
    exact ⟨e.symm, BlowupTowerSplitIso.IsTowerIso.congr_base he.symm (fun _ => rfl)⟩

open HironakaG8PhysicalChartOccupiedLifts HironakaG3RTowerClass
  G3UniversePhysicalClassComparisons MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveOriginalGrowingHistory
  HironakaLocallyFiniteResolutionSequence MarkedIdeals.MarkedIdeal

/-- Finite predecessor sets of the represented physical events suffice for
a global locally finite sequence testing the original record at every stage. -/
theorem global_test_of_finite_physical_ancestry
    {Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
    (cmp : HasPhysicalComparisons K) (c : ℕ → TowerChart K Z P)
    (hMono : Monotone fun i => (c i).U) (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    {ι : Type} (E : CofinalEvents c ι)
    (hOccurs : ∀ a, ∃ i p, E.event i p = a)
    (hLift : ∀ (i j : ℕ) (h : i ≤ j) p,
      E.event j (chartOccupiedLift cmp (c i) (c j) (hMono h) p) = E.event i p)
    (hFinite : ∀ b, {a | E.Before a b}.Finite)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower
      (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M) (c i).T) :
    ∃ A : ActualEndpointHistories X ℕ,
      ∃ hCoverA : ∀ x : X, ∃ i, x ∈ A.openSet i,
        LocallyFinite (centreImage (uniformGrowingSeq A hCoverA)) ∧
          ∀ k, IsGeoTestTower M ((uniformGrowingSeq A hCoverA).stage k).2 := by
  classical
  obtain ⟨r,hr⟩ := (E.exists_rank_iff_finite_predecessors hOccurs).mpr hFinite
  let rank (i : ℕ) (p : {k // Occupied (c i).T k}) := r (E.event i p)
  have hs (i : ℕ) : StrictMono (rank i) :=
    fun _ _ h => hr ((E.before_iff_slot_lt i _ _).mpr h)
  let d (i : ℕ) := Classical.choice (exists_ranked_test_compression _
    (MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM (c i).U)
    (c i).T (hTest i) (rank i) (hs i))
  have hComparisons : StrictPairwiseComparisons (fun i => (c i).U)
      (fun i => (d i).decoration.pad) := by
    apply strict_pairwise_of_nested (fun i => (c i).U) d
    · exact hMono
    · intro i j hij
      let hc := physical_comparison_nested_chart cmp (c i) (c j) (hMono hij)
      refine ⟨hc.choose,hc.choose_spec.1,hc.choose_spec.2.choose,
        hc.choose_spec.2.choose_spec,?_⟩
      intro p
      change r (E.event i p) = r (E.event j (chartOccupiedLift cmp (c i) (c j) (hMono hij) p))
      rw [hLift i j hij p]
  refine ⟨actualEndpointHistories _ _ hComparisons,hCover,?_⟩
  exact ranked_test_compressions_globalize M hM _ hCover d hComparisons

open HironakaG8CofinalEventLimit

variable {Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  (cmp : HasPhysicalComparisons K) (c : ℕ → TowerChart K Z P)
  (hMono : Monotone fun i => (c i).U)

private def up {i j : ℕ} (h : i ≤ j) : Slots c i → Slots c j :=
  chartOccupiedLift cmp (c i) (c j) (hMono h)

private theorem up_id (i : ℕ) (p : Slots c i) : up cmp c hMono (le_refl i) p = p :=
  congrArg (fun e => e p) (chartOccupiedLift_id cmp (c i))

private theorem up_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (p : Slots c i) :
    up cmp c hMono hjk (up cmp c hMono hij p) = up cmp c hMono (hij.trans hjk) p :=
  congrArg (fun e => e p) (chartOccupiedLift_comp cmp (c i) (c j) (c k) (hMono hij) (hMono hjk))

private theorem up_strict {i j : ℕ} (h : i ≤ j) : StrictMono (up cmp c hMono h) :=
  (chartOccupiedLift cmp (c i) (c j) (hMono h)).strictMono

/-- The occurrence quotient of the actual chosen nested physical comparisons. -/
def physicalEvents :
    CofinalEvents c (Quotient (occurrenceSetoid c (up cmp c hMono) (up_comp cmp c hMono))) :=
  eventLimit c (up cmp c hMono) (up_id cmp c hMono) (up_comp cmp c hMono) (up_strict cmp c hMono)

/-- Finite ancestry in the actual occurrence quotient supplies the
strict comparisons and the original TEST on the global growing sequence. -/
theorem global_test_of_finite_chart_ancestry
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    (hFinite : ∀ b, {a | (physicalEvents cmp c hMono).Before a b}.Finite)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower
      (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M) (c i).T) :
    ∃ A : ActualEndpointHistories X ℕ,
      ∃ hCoverA : ∀ x : X, ∃ i, x ∈ A.openSet i,
        LocallyFinite (centreImage (uniformGrowingSeq A hCoverA)) ∧
          ∀ k, IsGeoTestTower M ((uniformGrowingSeq A hCoverA).stage k).2 := by
  apply global_test_of_finite_physical_ancestry cmp c hMono hCover (physicalEvents cmp c hMono)
    _ _ hFinite M hM hTest
  · exact eventLimit_occurs c (up cmp c hMono) (up_id cmp c hMono)
      (up_comp cmp c hMono) (up_strict cmp c hMono)
  · intro i j h p
    exact (physicalEvents cmp c hMono).lift_event h p

end
end Hironaka.HironakaG8RankedNestedGlobalTest

#print axioms Hironaka.HironakaG8RankedNestedGlobalTest.global_test_of_finite_physical_ancestry

#print axioms Hironaka.HironakaG8RankedNestedGlobalTest.global_test_of_finite_chart_ancestry
