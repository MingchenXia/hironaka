import Hironaka.Resolution.HironakaG8BoundedOpenTestEndpoint
import Hironaka.Resolution.HironakaG8RankedNestedGlobalTest
import Hironaka.Resolution.HironakaG8RankedSingularGeometry

/-! A finite global original TEST for finite cofinal event families. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8FiniteEventTestEndpoint
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealBiholomorphism.MarkedIdeal MarkedIdealRestrictOpen
  HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison
  HironakaG8RankOccupiedAnnotation HironakaG8RankedEmptyPadding
  HironakaG8RankedTestCompression HironakaG8RankedNestedGlobalTest
  HironakaG8RankedGlobalTest HironakaG8RankedSingularGeometry
  HironakaG8PhysicalChartOccupiedLifts HironakaG3RTowerClass
  G3UniversePhysicalClassComparisons HironakaG3EmptyAwareHistory
  HironakaStageCenters HironakaEmbeddedAnalytic
  HironakaG8BoundedOpenTestEndpoint HironakaSharpActualCurveEmptyPadding
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveOriginalGrowingHistory
  HironakaG8IntrinsicSingularBlockSchedule HironakaUniformHistoricalSuccessorOriginalRegular
  HironakaG8SurfaceLimitEndpoint HironakaNormalCrossingsSeparationChoiceComparison

variable {n : ℕ} {X Y : CMfd.{0} n}

private theorem clock_le_of_empty_free_assigned_bound
    {T : BlowupTower X Y} {k N : ℕ} (D : RankedTower X T k)
    (hOcc : StageCentres (fun _ C => C.Nonempty) T)
    (hN : ∀ p : {i // Occupied T i}, assignedSlot D p.val<N) : k≤N := by
  cases D with
  | refl => exact Nat.zero_le _
  | @step V Z T i r D hi C π hπ =>
    have hp : Occupied (.step T C π hπ) T.length := Or.inr ⟨rfl,hOcc.2⟩
    have hLast := hN ⟨T.length,hp⟩
    have hr : r<N := by simpa [assignedSlot] using hLast
    exact Nat.succ_le_of_lt hr

/-- Every actual assigned rank below a bound finishes the compressed clock within it. -/
theorem compression_clock_le_of_rank_bound
    {M : MarkedIdeal n X} {T : BlowupTower X Y}
    {rank : {i // Occupied T i}→ℕ} (d : RankedTestCompression M T rank)
    {N : ℕ} (hN : ∀ p, rank p<N) : d.clock≤N := by
  apply clock_le_of_empty_free_assigned_bound d.decoration d.occupied
  intro p
  rw [d.rank_eq p]
  exact hN _

variable {Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z→X}
  {c : ℕ→TowerChart K Z P} {ι : Type*}

theorem finite_endpoint_of_finite_cofinal_events [Finite ι]
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i≤j) p,
      E.lift h p=chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x∈(c i).U)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p=a)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U→X) M) (c i).T)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hSing : ∀ i, StageCentres (fun T C => C ⊆ singularSet (n := n)
      (strictTransform n T.proj ((Subtype.val : (c i).U→X) ⁻¹' W))) (c i).T)
    (hSmooth : ∀ i, IsClosedSubmanifold n
      (strictTransform n (c i).T.proj ((Subtype.val : (c i).U→X) ⁻¹' W))) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      IsGeoTestTower M T ∧
      StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) ∧
      IsProperMap T.proj ∧ Function.Surjective T.proj ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsIsomorphismOver n T.proj (singularSet (n := n) W)ᶜ := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨r,hr⟩ := (E.exists_rank_iff_finite_predecessors hOccurs).mpr
    (fun b => Set.finite_univ.subset (Set.subset_univ {a | E.Before a b}))
  let N := (Finset.univ : Finset ι).sup r+1
  have hCap (a : ι) : r a<N := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ a))
  let rank (i : ℕ) (p : {k // Occupied (c i).T k}) := r (E.event i p)
  have hs (i : ℕ) : StrictMono (rank i) :=
    fun _ _ h => hr ((E.before_iff_slot_lt i _ _).mpr h)
  let d (i : ℕ) := Classical.choice (exists_ranked_test_compression _
    (MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM (c i).U)
    (c i).T (hTest i) (rank i) (hs i))
  have hClock (i : ℕ) : (d i).clock≤N :=
    compression_clock_le_of_rank_bound (d i) (fun p => hCap (E.event i p))
  have hPair : StrictPairwiseComparisons (fun i => (c i).U)
      (fun i => (d i).decoration.pad) := by
    apply strict_pairwise_of_nested (fun i => (c i).U) d hMono
    intro i j hij
    let hc := physical_comparison_nested_chart cmp (c i) (c j) (hMono hij)
    refine ⟨hc.choose,hc.choose_spec.1,hc.choose_spec.2.choose,
      hc.choose_spec.2.choose_spec,?_⟩
    intro p
    change r (E.event i p)=r (E.event j (chartOccupiedLift cmp (c i) (c j) (hMono hij) p))
    rw [← hLift hij,E.lift_event]
  have hLen (i : ℕ) : (d i).decoration.pad.length≤N := by
    rw [(d i).decoration.pad_length]
    exact hClock i
  have hPTest (i : ℕ) :
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U→X) M)
        (d i).decoration.pad := by
    simpa [RankedTower.through,identityEmptyTail] using test_ranked_through _
      (MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM (c i).U)
      (d i).test (d i).decoration (d i).clock
  have hPSing (i : ℕ) : StageCentres (fun T C => C ⊆ singularSet (n := n)
      (strictTransform n T.proj ((Subtype.val : (c i).U→X) ⁻¹' W))) (d i).decoration.pad := by
    have h := (singular_stageCentres_ranked_compression_iff _ (d i)
      (hW.isClosed.preimage continuous_subtype_val) (d i).clock).mpr (hSing i)
    simpa [RankedTower.through,identityEmptyTail] using h
  have hPSmooth (i : ℕ) : IsClosedSubmanifold n
      (strictTransform n (d i).decoration.pad.proj ((Subtype.val : (c i).U→X) ⁻¹' W)) := by
    have h := isClosedSubmanifold_ranked_through _ (d i)
      (hW.isClosed.preimage continuous_subtype_val) (hSmooth i) (d i).clock
    simpa [RankedTower.through,identityEmptyTail] using h
  let A := actualEndpointHistories (fun i => (c i).U) (fun i => (d i).decoration.pad) hPair
  let T := ((uniformGrowingSeq A hCover).stage N).2
  obtain ⟨_hLength,hGlobalTest,hGlobalSing,hGlobalSmooth,hProper,hHolo⟩ :=
    bounded_endpoint_of_compatible_open_tests (fun i => (c i).U) hCover
      (fun i => (d i).decoration.pad) hPair N hLen M hM hPTest W hW hPSing hPSmooth
  have hProtect := actual_singular_history_original_regular_protection W hW T
    (intrinsic_stage_native_history W T hGlobalSing)
  have hIso : IsIsomorphismOver n T.proj (singularSet (n := n) W)ᶜ := hProtect.2.1
  exact ⟨_,T,hGlobalTest,hGlobalSing,hGlobalSmooth,hProper,
    proper_regular_open_iso_surjective W T.proj hProper hIso,hHolo,hIso⟩

theorem finite_endpoint_of_one_event_reference_chart
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i≤j) p,
      E.lift h p=chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x∈(c i).U)
    (i₀ : ℕ) (hReference : ∀ a, ∃ p : {k // Occupied (c i₀).T k}, E.event i₀ p=a)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U→X) M) (c i).T)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hSing : ∀ i, StageCentres (fun T C => C ⊆ singularSet (n := n)
      (strictTransform n T.proj ((Subtype.val : (c i).U→X) ⁻¹' W))) (c i).T)
    (hSmooth : ∀ i, IsClosedSubmanifold n
      (strictTransform n (c i).T.proj ((Subtype.val : (c i).U→X) ⁻¹' W))) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      IsGeoTestTower M T ∧
      StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) ∧
      IsProperMap T.proj ∧ Function.Surjective T.proj ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsIsomorphismOver n T.proj (singularSet (n := n) W)ᶜ := by
  let f : {k // Occupied (c i₀).T k}→Fin (c i₀).T.length :=
    fun p => ⟨p.val,occupied_lt_length _ p.property⟩
  have hf : Function.Injective f :=
    fun _ _ h => Subtype.ext (congrArg Fin.val h)
  let _ : Finite {k // Occupied (c i₀).T k} := Finite.of_injective f hf
  let _ : Finite ι := Finite.of_surjective (E.event i₀) hReference
  have hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p=a := by
    intro a
    obtain ⟨p,hp⟩ := hReference a
    exact ⟨i₀,p,hp⟩
  exact finite_endpoint_of_finite_cofinal_events E cmp hMono hLift hCover hOccurs
    M hM hTest W hW hSing hSmooth

end
end Hironaka.HironakaG8FiniteEventTestEndpoint
