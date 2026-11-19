import Hironaka.Resolution.HironakaG3CompositeTowerChart
import Hironaka.Resolution.HironakaG3EndpointRepresentableClass
import Hironaka.Resolution.HironakaG3GoodSmoothBoundarySupport
import Hironaka.Resolution.HironakaG3IndexedMixedCompactWindow
import Hironaka.Resolution.HironakaG3ProperFibreTowerIdentification
import Hironaka.Resolution.HironakaG3SeparatedCompositionExact
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3CompositeTerminalHistory

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdealTowerTransport HironakaG3RTowerClass HironakaG3RigidOverLocalGlue
  G3EndpointRepresentableClass HironakaG3IndexedMixedGluing
  HironakaG3IndexedMixedCompactWindow HironakaG3FiniteDisjointTowerMerge
  HironakaG3FiniteVisibleAtlas HironakaG3DisjointLocalTowerAtlas
  HironakaG3EmptyAwareHistory HironakaOriginalTerminalOverlapComparison
  HironakaG3ProperFibreTowerIdentification HironakaG3CompositeTowerChart MaxLocusLocal RestrictEmptyTower
  HironakaActualLocallyFiniteBoundary NormalCrossings BlowupTowerIsoTail
  HironakaActualIndexedBoundaryContinuation
  HironakaG3VaryingContactComponentClass HironakaG3SeparatedCompositionExact HironakaG3PhysicalClassComparisons
  HironakaG3GoodSmoothBoundarySupport HironakaG3IndexedSeparatedComponents
noncomputable section

/-- Each actual tail retains the finite visible component choices and a
physical comparison with each of its selected component histories. -/
def componentTailClass {n : ℕ} {Z Y : CMfd.{0} n} {ι : Type u} {κ : Type v}
    (C : ι → Set Z) (W : ι → Opens Z) (K : ι → LocalTowerClass Z)
    (D : κ → Set Z) (Q : Y → Z) : LocalTowerClass Z :=
  fun A B M => ∃ s : Finset ι,
    (∀ i, (C i ∩ (A : Set Z)).Nonempty → i ∈ s) ∧
    ∃ c : {j // j ∈ s} → TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Y Q,
    ∃ hc : ∀ i, (c i).U = W i.val ⊓ A,
      (∀ i, K i.val (c i).U (c i).Y (c i).T) ∧
      CentresOver (finiteSupport (fun i : {j // j ∈ s} => (Subtype.val : A → Z) ⁻¹' C i.val) s.attach) M ∧
      ∀ i, ∃ φ : CMfd.of (n := n) (openPreimage M (nestedOpens A (c i).U))
          ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (c i).Y,
        EmptyAwareTowerIso
          (nestedOpensDiffeo (n := n) (show (c i).U ≤ A by rw [hc i]; exact inf_le_right))
          (restrict (nestedOpens A (c i).U) M) (c i).T φ

/-- An actual composite tower appends the transported tail to the retained
first-phase chart, with the tail identified over the same saturated open. -/
inductive CompositeHistoryClass {n : ℕ} {X Z Y : CMfd.{u} n}
    {P : Z → X} {Q : Y → Z} (hQ : Continuous Q)
    (Head : LocalTowerClass X) (Tail : LocalTowerClass Z) : LocalTowerClass X where
  | join (c : TowerChart Head Z P) {B : CMfd.{u} n}
      (M : BlowupTower (CMfd.of (n := n) c.V) B) (hM : Tail c.V B M)
      (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (window Q hQ c.V))
      (hΦ : ∀ z, restrictedBaseMap Q hQ c.V (Φ z) = M.proj z) :
      CompositeHistoryClass (P := P) hQ Head Tail c.U
        (transport c.φ M).target (c.T.append (transport c.φ M).tower)

/-- The retained two-phase history determines an actual saturated chart. -/
theorem composite_history_has_chart {n : ℕ} {X Z Y B : CMfd.{u} n}
    {P : Z → X} {Q : Y → Z} (hQ : Continuous Q)
    {Head : LocalTowerClass X} {Tail : LocalTowerClass Z}
    {U : Opens X} {T : BlowupTower (CMfd.of (n := n) U) B}
    (hT : CompositeHistoryClass (P := P) hQ Head Tail U B T) :
    ∃ c : TowerChart (CompositeHistoryClass (P := P) hQ Head Tail) Y (P ∘ Q),
      c.U = U := by
  cases hT with
  | join c M hM Φ hΦ =>
    obtain ⟨hV,he⟩ := composite_tower_chart_literal hQ c M Φ hΦ
    exact ⟨⟨c.U,_,_,.join c M hM Φ hΦ,window Q hQ c.V,hV,
      (transport c.φ M).back.trans Φ,he⟩,rfl⟩

/-- The separator chart and the actual component tail can be chosen over any
one compact-enclosed base open, retaining their literal composition. -/
theorem exists_mixed_composite_chart_over_compact {n : ℕ} {X Z Y : CMfd.{0} n}
    {ι κ : Type} {ρ : Type v} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hV : LocallyFinite (fun i => (V i).carrier))
    (hDim : ∀ i, (V i).dim < n)
    (hDistinct : ∀ i j, i ≠ j → ¬ (V i).carrier ⊆ (V j).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    {P : Z → X} (hP : IsGluedFrom (indexedMixedClass V D) Z P)
    (C : ι → Set Z) (hClosed : ∀ i, IsClosed (C i)) (hLF : LocallyFinite C)
    (W : ι → Opens Z) (hCW : ∀ i, C i ⊆ W i)
    (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set Z))
    (K : ι → LocalTowerClass Z) (hCompare : ∀ i, HasComparisons (K i))
    (hCentres : ∀ (i : ι) (U : Opens Z) (B : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) B),
      K i U B T → CentresOver ((Subtype.val : U → Z) ⁻¹' C i) T)
    (hCompact : ∀ (i : ι) (U : Opens Z) (L : Set Z), IsCompact L → (U : Set Z) ⊆ L →
      ∃ (B : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) B), K i U B T)
    (E : ρ → Set Z) (hE : LocallyFinite E) {Q : Y → Z}
    (hQ : IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) E) Y Q)
    (U : Opens X) (L : Set X) (hL : IsCompact L) (hUL : (U : Set X) ⊆ L) :
    ∃ c : TowerChart
      (CompositeHistoryClass (P := P) hQ.1.continuous (indexedMixedClass V D) (componentTailClass C W K E Q))
      Y (P ∘ Q), c.U = U := by
  obtain ⟨c,hc⟩ := indexed_mixed_chart_over_compact_window V hV hDim hDistinct D hD hP U L hL hUL
  subst U
  have hVeq : c.V = window P hP.2.1.continuous c.U := Opens.ext c.V_eq
  have hTail :
      ∃ (B : CMfd.{0} n) (M : BlowupTower (CMfd.of (n := n) c.V) B),
        componentTailClass C W K E Q c.V B M ∧
        ∃ Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (window Q hQ.1.continuous c.V),
          ∀ z, restrictedBaseMap Q hQ.1.continuous c.V (Φ z) = M.proj z := by
    rw [hVeq]
    obtain ⟨s,hLabels,a,ha,hMem,B,M,hM,hPhysical,Φ,hΦ,-⟩ :=
      proper_fibre_tower_identification_with_provenance_over_compact
        C hClosed hLF W hCW hWindow K hCompare hCentres hCompact E hE hP.2.1 hQ c.U L hL hUL
    exact ⟨B,M,⟨s,hLabels,a,ha,hMem,hM,hPhysical⟩,Φ,hΦ⟩
  obtain ⟨B,M,hM,Φ,hΦ⟩ := hTail
  exact composite_history_has_chart hQ.1.continuous (.join c M hM Φ hΦ)

/-- The endpoint identifications of the retained histories give their
projection-compatible comparisons over actual overlaps. -/
theorem composite_history_has_comparisons {n : ℕ} {X Z Y : CMfd.{u} n}
    {P : Z → X} {Q : Y → Z} (hP : Continuous P) (hQ : Continuous Q)
    (Head : LocalTowerClass X) (Tail : LocalTowerClass Z) :
    HasComparisons (CompositeHistoryClass (P := P) hQ Head Tail) := by
  have hMem : ∀ (U : Opens X) (B : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) B),
      CompositeHistoryClass (P := P) hQ Head Tail U B T →
        endpointRepresentable (P ∘ Q) (hP.comp hQ) U B T := by
    intro U B T hT
    cases hT with
    | join c M hM Φ hΦ =>
      obtain ⟨hV,hProj⟩ := composite_tower_chart_literal hQ c M Φ hΦ
      have hV' : window Q hQ c.V = window (P ∘ Q) (hP.comp hQ) c.U := Opens.ext hV
      let e := ((transport c.φ M).back.trans Φ).trans (opensCongr (n := n) hV')
      refine ⟨e,?_⟩
      intro z
      apply Subtype.ext
      exact hProj z
  intro U₁ U₂ B₁ B₂ T₁ T₂ h₁ h₂
  exact endpointRepresentable_hasComparisons (P ∘ Q) (hP.comp hQ) U₁ U₂ B₁ B₂ T₁ T₂
    (hMem U₁ B₁ T₁ h₁) (hMem U₂ B₂ T₂ h₂)

/-- The mixed-boundary resolution admits a saturated two-phase history
over every compact-enclosed open on the same terminal map. -/
theorem exists_separator_composition_terminal_atlas_with_provenance {n d : ℕ} {X : CMfd.{0} n}
    {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hLF : LocallyFinite (fun i => (V i).carrier)) (hDim : ∀ i, (V i).dim < n)
    (hSameDim : ∀ i, (V i).dim = d)
    (hDistinct : ∀ i j, i ≠ j → ¬ (V i).carrier ⊆ (V j).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Z Y : CMfd.{0} n) (P : Z → X) (Q : Y → Z) (ρ₀ ρ : Type) (B₀ : ρ₀ → Set Z) (B : ρ → Set Y),
      ∃ (W : ι → Opens Z) (K : ι → LocalTowerClass Z) (hQ : Continuous Q),
      let Class := CompositeHistoryClass (P := P) hQ (indexedMixedClass V D)
        (componentTailClass (fun i => strictTransform n P (V i).carrier) W K B₀ Q)
      (letI : LinearOrder ρ₀ := WellOrderingRel.isWellOrder.linearOrder
       ∃ hB₀ : IsLocallyFiniteSNCDivisor n B₀,
         ∀ i, ∃ hCi : IsComplexAnalyticallyIrreducible (n := n) (strictTransform n P (V i).carrier),
           ActualComponentResolutionClass (V i).dim (strictTransform n P (V i).carrier)
             B₀ hCi hB₀ (K i)) ∧
      IsGluedFrom Class Y (P ∘ Q) ∧ HasComparisons Class ∧
      (∀ (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
        ∃ c : TowerChart Class Y (P ∘ Q), c.U = U) ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (P ∘ Q) ∧
      IsProperMap (P ∘ Q) ∧ Surjective (P ∘ Q) ∧
      (P ∘ Q) '' strictTransform n (P ∘ Q) (⋃ i, (V i).carrier) = ⋃ i, (V i).carrier ∧
      IsIsomorphismOver n (P ∘ Q) (((⋃ i, (V i).carrier) \ regularLocus (n := n) (⋃ i, (V i).carrier) d) ∪
        ((⋃ i, (V i).carrier) ∩ ⋃ j, D j))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) ∧
      (∀ z ∈ strictTransform n (P ∘ Q) (⋃ i, (V i).carrier),
        RegularAtDim (n := n) (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) z d) ∧
      (P ∘ Q) ⁻¹' ((⋃ i, (V i).carrier) \ regularLocus (n := n) (⋃ i, (V i).carrier) d) ⊆ exceptionalLocus n (P ∘ Q) ∧
      IsLocallyFiniteSNCDivisor n B₀ ∧ IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = (P ∘ Q) ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n (P ∘ Q) ∧
      (⋃ a, B a) = (P ∘ Q) ⁻¹' ((⋃ j, D j) ∪ (⋃ i, (V i).carrier) \ regularLocus (n := n) (⋃ i, (V i).carrier) d) ∧
      HasNormalCrossingsWithBoundary (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) B := by
  obtain ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,W,K,hCW,hWindow,hKind,hPhys,hCentres,hCompact,hGP,hGQ,hRest⟩ :=
    exists_separator_component_composition_with_branch_provenance V hLF hDim hSameDim hDistinct D hD
  have hClosed : ∀ i, IsClosed (strictTransform n P (V i).carrier) := fun _ => isClosed_closure
  have hSLF := locallyFinite_strictTransforms (fun i => (V i).carrier) (fun i => (V i).isClosed_carrier) hLF hGP.1.continuous
  have hCompare := fun i => physical_comparisons_to_comparisons (hPhys i)
  rcases hRest with ⟨hMD,hProper,hSurj,hProj,hIso,hSmooth,hRegular,hB₀,hB,hNE,hSupport,hNC⟩
  have hWClosed : IsClosed (⋃ i, (V i).carrier) := hLF.isClosed_iUnion (fun i => (V i).isClosed_carrier)
  have hSing := HironakaEmbeddedReducible.preimage_diff_regularLocus_subset_exceptionalLocus hMD hWClosed hRegular
  have hSupport' := hSupport.trans (good_smooth_boundary_support (⋃ i, (V i).carrier) (⋃ j, D j) hWClosed hMD hIso hRegular)
  let Class := CompositeHistoryClass (P := P) hGQ.1.continuous (indexedMixedClass V D)
    (componentTailClass (fun i => strictTransform n P (V i).carrier) W K B₀ Q)
  have hWindowChart : ∀ (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
      ∃ c : TowerChart Class Y (P ∘ Q), c.U = U := fun U L hL hUL =>
    exists_mixed_composite_chart_over_compact V hLF hDim hDistinct D hD hGP
      (fun i => strictTransform n P (V i).carrier) hClosed hSLF W hCW hWindow K hCompare
      hCentres hCompact B₀ hB₀.1 hGQ U L hL hUL
  have hAtlas : IsGluedFrom Class Y (P ∘ Q) := by
    refine ⟨hMD,hProper,hSurj,?_⟩
    let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
    intro x
    obtain ⟨L,hL,hxL⟩ := exists_compact_mem_nhds x
    let U : Opens X := ⟨interior L,isOpen_interior⟩
    obtain ⟨c,hc⟩ := hWindowChart U L hL interior_subset
    exact ⟨c,hc ▸ mem_interior_iff_mem_nhds.mpr hxL⟩
  have hCmp : HasComparisons Class :=
    composite_history_has_comparisons hGP.1.continuous hGQ.1.continuous _ _
  exact ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,W,K,hGQ.1.continuous,hKind,hAtlas,hCmp,hWindowChart,
    hMD,hProper,hSurj,hProj,hIso,hSmooth,hRegular,hSing,hB₀,hB,hNE,hSupport,hSupport',hNC⟩

theorem exists_separator_composition_terminal_atlas {n d : ℕ} {X : CMfd.{0} n}
    {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hLF : LocallyFinite (fun i => (V i).carrier)) (hDim : ∀ i, (V i).dim < n)
    (hSameDim : ∀ i, (V i).dim = d)
    (hDistinct : ∀ i j, i ≠ j → ¬ (V i).carrier ⊆ (V j).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Z Y : CMfd.{0} n) (P : Z → X) (Q : Y → Z) (ρ₀ ρ : Type) (B₀ : ρ₀ → Set Z) (B : ρ → Set Y),
      ∃ (W : ι → Opens Z) (K : ι → LocalTowerClass Z) (hQ : Continuous Q),
      let Class := CompositeHistoryClass (P := P) hQ (indexedMixedClass V D)
        (componentTailClass (fun i => strictTransform n P (V i).carrier) W K B₀ Q)
      IsGluedFrom Class Y (P ∘ Q) ∧ HasComparisons Class ∧
      (∀ (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
        ∃ c : TowerChart Class Y (P ∘ Q), c.U = U) ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (P ∘ Q) ∧
      IsProperMap (P ∘ Q) ∧ Surjective (P ∘ Q) ∧
      (P ∘ Q) '' strictTransform n (P ∘ Q) (⋃ i, (V i).carrier) = ⋃ i, (V i).carrier ∧
      IsIsomorphismOver n (P ∘ Q) (((⋃ i, (V i).carrier) \ regularLocus (n := n) (⋃ i, (V i).carrier) d) ∪
        ((⋃ i, (V i).carrier) ∩ ⋃ j, D j))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) ∧
      (∀ z ∈ strictTransform n (P ∘ Q) (⋃ i, (V i).carrier),
        RegularAtDim (n := n) (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) z d) ∧
      (P ∘ Q) ⁻¹' ((⋃ i, (V i).carrier) \ regularLocus (n := n) (⋃ i, (V i).carrier) d) ⊆ exceptionalLocus n (P ∘ Q) ∧
      IsLocallyFiniteSNCDivisor n B₀ ∧ IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = (P ∘ Q) ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n (P ∘ Q) ∧
      (⋃ a, B a) = (P ∘ Q) ⁻¹' ((⋃ j, D j) ∪ (⋃ i, (V i).carrier) \ regularLocus (n := n) (⋃ i, (V i).carrier) d) ∧
      HasNormalCrossingsWithBoundary (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) B := by
  obtain ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,W,K,hQ,_hKind,hRest⟩ :=
    exists_separator_composition_terminal_atlas_with_provenance V hLF hDim hSameDim hDistinct D hD
  exact ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,W,K,hQ,hRest⟩

end
end Hironaka.HironakaG3CompositeTerminalHistory
