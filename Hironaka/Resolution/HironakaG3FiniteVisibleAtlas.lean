import Hironaka.Resolution.HironakaG3DisjointLocalTowerAtlas
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3FiniteVisibleAtlas
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass HironakaG3DisjointLocalTowerAtlas RestrictEmptyTower

/-- Refine a tower class by a finite window containing every visible indexed boundary member. -/
def finiteVisibleClass {n : ℕ} {X : CMfd.{0} n} {κ : Type*}
    (𝒞 : LocalTowerClass X) (D : κ → Set X) : LocalTowerClass X :=
  fun U Y T => 𝒞 U Y T ∧ ∃ R : Finset κ, ∀ i, (D i ∩ (U : Set X)).Nonempty → i ∈ R

/-- A compact-bound window supplies an actual finite visible set. -/
theorem finite_visible_window {n : ℕ} {X : CMfd.{0} n} {κ : Type*}
    (D : κ → Set X) (hD : LocallyFinite D) (U : Opens X) (K : Set X)
    (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    ∃ R : Finset κ, ∀ i, (D i ∩ (U : Set X)).Nonempty → i ∈ R := by
  classical
  refine ⟨(hD.finite_nonempty_inter_compact hK).toFinset, ?_⟩
  intro i ⟨x,hxD,hxU⟩
  apply (hD.finite_nonempty_inter_compact hK).mem_toFinset.mpr
  exact ⟨x,hxD,hUK hxU⟩

/-- Finite-window witnesses do not alter any physical tower comparisons. -/
theorem finite_visible_comparisons {n : ℕ} {X : CMfd.{0} n} {κ : Type*}
    (𝒞 : LocalTowerClass X) (D : κ → Set X) (hCmp : HasComparisons 𝒞) :
    HasComparisons (finiteVisibleClass 𝒞 D) := by
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
  exact hCmp U₁ U₂ Y₁ Y₂ T₁ T₂ h₁.1 h₂.1

/-- Compact-window local members for each component give a finite-visible disjoint cover. -/
theorem finite_visible_disjoint_covers {n : ℕ} {X : CMfd.{0} n} {ι κ : Type*}
    (A : ι → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hClosed : ∀ i, IsClosed (A i)) (hLF : LocallyFinite A)
    (D : κ → Set X) (hD : LocallyFinite D)
    (hLocal : ∀ i x, x ∈ A i → ∃ (U : Opens X) (L : Set X), x ∈ U ∧ U ≤ W i ∧
      IsCompact L ∧ (U : Set X) ⊆ L ∧ ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K i U Y T) :
    Covers (finiteVisibleClass (disjointWindowClass A W K) D) := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  intro x
  by_cases hx : x ∈ ⋃ i, A i
  · obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
    obtain ⟨U,L,hxU,hUW,hL,hUL,Y,T,hT⟩ := hLocal i x hxi
    exact ⟨U,hxU,Y,T,⟨Or.inl ⟨i,hUW,hT⟩,finite_visible_window D hD U L hL hUL⟩⟩
  · obtain ⟨L,hL,hxL⟩ := exists_compact_mem_nhds x
    let O : Opens X := ⟨(⋃ i, A i)ᶜ,(hLF.isClosed_iUnion hClosed).isOpen_compl⟩
    let U : Opens X := ⟨interior L ∩ O, isOpen_interior.inter O.isOpen⟩
    have hxU : x ∈ U := ⟨mem_interior_iff_mem_nhds.mpr hxL,hx⟩
    have hUL : (U : Set X) ⊆ L := fun _ h => interior_subset h.1
    have hUO : (U : Set X) ⊆ (⋃ i, A i)ᶜ := fun _ h => h.2
    exact ⟨U,hxU,CMfd.of (n := n) U,.refl,⟨Or.inr ⟨hUO,trivial⟩,finite_visible_window D hD U L hL hUL⟩⟩

/-- A finite-visible atlas is an atlas of the original class for the same map. -/
theorem finite_visible_forget_glued {n : ℕ} {X Z : CMfd.{0} n} {κ : Type*}
    (𝒞 : LocalTowerClass X) (D : κ → Set X) {P : Z → X}
    (h : IsGluedFrom (finiteVisibleClass 𝒞 D) Z P) : IsGluedFrom 𝒞 Z P := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  intro x
  obtain ⟨c,hx⟩ := h.2.2.2 x
  let c' : TowerChart 𝒞 Z P := ⟨c.U,c.Y,c.T,c.mem.1,c.V,c.V_eq,c.φ,c.proj_φ⟩
  exact ⟨c',hx⟩

/-- The disjoint component classes admit an actual finite-visible glued atlas. -/
theorem exists_finite_visible_disjoint_atlas {n : ℕ} {X : CMfd.{0} n} {ι κ : Type*}
    (A : ι → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hClosed : ∀ i, IsClosed (A i)) (hLF : LocallyFinite A)
    (hWindow : ∀ i j, i ≠ j → Disjoint (A j) (W i : Set X))
    (hCompare : ∀ i, HasComparisons (K i))
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' A i) T)
    (D : κ → Set X) (hD : LocallyFinite D)
    (hLocal : ∀ i x, x ∈ A i → ∃ (U : Opens X) (L : Set X), x ∈ U ∧ U ≤ W i ∧
      IsCompact L ∧ (U : Set X) ⊆ L ∧ ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K i U Y T) :
    ∃ (Z : CMfd.{0} n) (P : Z → X), IsGluedFrom (finiteVisibleClass (disjointWindowClass A W K) D) Z P := by
  exact exists_isGluedFrom (finite_visible_disjoint_covers A W K hClosed hLF D hD hLocal)
    (finite_visible_comparisons _ D (disjoint_window_comparisons A W K hWindow hCompare hCentres))
end
end Hironaka.HironakaG3FiniteVisibleAtlas
