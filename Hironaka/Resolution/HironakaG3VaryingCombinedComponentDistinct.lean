import Hironaka.Resolution.HironakaG3VaryingCombinedComponentSlots
import Hironaka.Resolution.HironakaG3VaryingActiveInheritedLabels
import Hironaka.Resolution.HironakaG3BornLabelsDistinct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3VaryingCombinedComponentDistinct
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaG3RTowerClass HironakaG3REmbeddedGlobalSNC
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary HironakaG3DisjointLocalTowerAtlas
  HironakaG3FiniteVisibleAtlas HironakaG3VaryingCombinedComponentSlots HironakaG3VaryingActiveInheritedLabels
  HironakaG3BornLabelsDistinct MaxLocusLocal

variable {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
  (C : ι → Set X) (D : κ → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
  {P : Z → X} (hG : IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Z P)

theorem varying_component_chart_combined_labels_distinct
    (r : ι → ℕ) (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (hD : IsLocallyFiniteSNCDivisor n D)
    (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
    (hExc : exceptionalLocus n P ⊆ P ⁻¹' (varyingActiveUnion C r D hC hD))
    (c : ι → ℕ → TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Z P)
    (Ex : ∀ i, SNCExhaustion (CMfd.of (n := n) (varyingComponentWindow C D W K hG i)))
    (hExW : ∀ i k, (Ex i).W k = nestedOpens (varyingComponentWindow C D W K hG i) (c i k).V)
    (hBorn : ∀ (p : Σ i, {H : Set (varyingComponentWindow C D W K hG i) // (Ex i).IsGlobalMember H}),
      ((Subtype.val : varyingComponentWindow C D W K hG p.1 → Z) '' p.2.1) ⊆ P ⁻¹' C p.1)
    (hBornActive : ∀ (p : Σ i, {H : Set (varyingComponentWindow C D W K hG i) // (Ex i).IsGlobalMember H}),
      ((Subtype.val : varyingComponentWindow C D W K hG p.1 → Z) '' p.2.1) ⊆ P ⁻¹' (varyingActiveUnion C r D hC hD))
    (i : ι) (k : ℕ) (x : Z) (hxV : x ∈ (c i k).V) (hxC : P x ∈ C i) :
    ∀ a b, x ∈ varyingCombinedBoundary C D W K hG Ex a → x ∈ varyingCombinedBoundary C D W K hG Ex b →
      (Subtype.val : (c i k).V → Z) ⁻¹' varyingCombinedBoundary C D W K hG Ex a =
      (Subtype.val : (c i k).V → Z) ⁻¹' varyingCombinedBoundary C D W K hG Ex b → a = b := by
  let Q := varyingComponentWindow C D W K hG
  let V := (c i k).V
  let F := varyingCombinedBoundary C D W K hG Ex
  intro a b ha hb heq
  have hTrace : F a ∩ V = F b ∩ V := by
    ext z
    constructor
    · rintro ⟨hz,hzV⟩
      have h : (⟨z,hzV⟩ : V) ∈ (Subtype.val : V → Z) ⁻¹' F b := heq ▸ hz
      exact ⟨h,hzV⟩
    · rintro ⟨hz,hzV⟩
      have h : (⟨z,hzV⟩ : V) ∈ (Subtype.val : V → Z) ⁻¹' F a := heq.symm ▸ hz
      exact ⟨h,hzV⟩
  cases a with
  | inl j =>
    cases b with
    | inl l =>
      have hNE : (strictTransform n P (D j) ∩ V).Nonempty := ⟨x,ha,hxV⟩
      have hjl := varying_inherited_trace_labels_eq C r D hC hLF hD hr hpure hG.1 hExc j l V hNE hTrace
      exact congrArg Sum.inl hjl
    | inr p =>
      have hNE : (strictTransform n P (D j) ∩ V).Nonempty := ⟨x,ha,hxV⟩
      have hNo := varying_inherited_trace_not_active_supported C r D hC hLF hD hr hpure hG.1 j V hNE _ (hBornActive p)
      exact False.elim (hNo (fun z hz => (Set.ext_iff.mp hTrace z).mp hz |>.1))
  | inr p =>
    cases b with
    | inl j =>
      have hNE : (strictTransform n P (D j) ∩ V).Nonempty := ⟨x,hb,hxV⟩
      have hNo := varying_inherited_trace_not_active_supported C r D hC hLF hD hr hpure hG.1 j V hNE _ (hBornActive p)
      exact False.elim (hNo (fun z hz => (Set.ext_iff.mp hTrace z).mpr hz |>.1))
    | inr q =>
      have hpC : P x ∈ C p.1 := hBorn p ha
      have hpi : p.1 = i := by
        by_contra hne
        exact Set.disjoint_left.mp (hDis p.1 i hne) hpC hxC
      have hNE : (((Subtype.val : Q p.1 → Z) '' p.2.1) ∩ V).Nonempty := ⟨x,ha,hxV⟩
      rcases p with ⟨pidx,pb⟩
      rcases q with ⟨qidx,qb⟩
      change pidx = i at hpi
      subst pidx
      obtain ⟨hidx,hval⟩ := born_trace_labels_eq P C Q Ex (fun a b h => hDis a b h)
        (fun j b => hBorn ⟨j,b⟩) V i qidx k (hExW i k) pb qb hNE hTrace
      have hpq : (⟨i,pb⟩ : Σ j, {H : Set (Q j) // (Ex j).IsGlobalMember H}) = ⟨qidx,qb⟩ := by
        cases hidx
        cases hval
        rfl
      exact congrArg Sum.inr hpq
end
end Hironaka.HironakaG3VaryingCombinedComponentDistinct
