import Hironaka.Resolution.HironakaG3SeparatedInheritedBoundary
import Hironaka.Resolution.HironakaG3IndexedBoundaryDichotomy
import Hironaka.Resolution.HironakaG3IndexedCanonicalContact
import Hironaka.Analytic.SNCGlobalPrimeComponents
import Hironaka.Analytic.GlobalSmoothHypersurfacePrimeComponent
import Hironaka.Analytic.ThinDimensionDrop
import Hironaka.Analytic.AnalyticIrreducibleComponents
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3BoundaryDenseOffComponents
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings AnalyticDimensionBasics DimensionMonotone ThinDimensionDrop
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary HironakaG3IndexedCanonicalContact
  HironakaG3OrderedFiniteWindows HironakaG3IndexedBoundaryDichotomy

/-- An irreducible pure target is dimension-bounded by its witnessed pure dimension. -/
private theorem dimLE_of_irreducible_dense_regular {n r : ℕ} {X : CMfd.{0} n} (C : Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hr : r < n)
    (hpure : C ⊆ closure (regularLocus (n := n) C r)) : DimLE (n := n) C r := by
  obtain ⟨x,hx⟩ := hC.nonempty
  have hne : (regularLocus (n := n) C r).Nonempty := by
    by_contra h
    have he : regularLocus (n := n) C r = ∅ := not_nonempty_iff_eq_empty.mp h
    have hh := hpure hx
    rw [he,closure_empty] at hh
    exact hh
  let V : ClosedIrreducibleAnalyticSubvariety n X := ⟨C,hC.analytic.isClosed,hC,r,Nat.le_of_lt hr,hne⟩
  intro y k hy
  exact (AnalyticIrreducibleComponents.eq_dim_of_regularAtDim V hy).le

/-- Boundary members are dense off components that either have codimension at
least two or are contained in no boundary member. -/
theorem indexed_boundary_dense_off_small_or_avoiding_components {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hD : IsLocallyFiniteSNCDivisor n D)
    (hSmall : ∀ i, r i < n - 1 ∨ containingLabels (C i) D (hC i).nonempty hD.1 = ∅)
    (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i))) :
    ∀ j, D j ⊆ closure (D j \ ⋃ i, C i) := by
  intro j
  by_cases hn : n = 0
  · have hι : IsEmpty ι := ⟨fun i => (Nat.not_lt_zero _ (hn ▸ hr i))⟩
    have hF : (⋃ i, C i) = ∅ := iUnion_of_empty C
    rw [hF,sdiff_empty]
    exact subset_closure
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
  subst n
  have hSNC : IsSNCDivisor (m+1) [D j] := by
    simpa using sorted_boundary_snc D hD ({j} : Finset κ)
  have hReg : ∀ x ∈ D j, RegularAtDim (n := m+1) (D j) x m := by
    intro x hx
    have h := SNCGlobalPrimeComponents.regularAtDim_member hSNC ⟨0,by simp⟩ (x := x) (by simpa using hx)
    simpa using h
  have hDa : IsComplexAnalyticSubset (n := m+1) (D j) := isComplexAnalyticSubset_member D hD j
  have hThin : ∀ i, containingLabels (C i) D (hC i).nonempty hD.1 = ∅ → ∀ O : Set X, IsOpen O → O ∩ C i ⊆ C i ∩ D j → O ∩ C i = ∅ := by
    intro i hS O hO hSub
    have hjNot : j ∉ containingLabels (C i) D (hC i).nonempty hD.1 := by rw [hS]; simp
    have hDense : C i ⊆ closure (C i \ D j) := by
      apply (dense_off_residual_family (C i) D (hC i) hD).trans
      apply closure_mono
      intro x hx
      exact ⟨hx.1,fun hxj => hx.2 (mem_iUnion.mpr ⟨⟨j,hjNot⟩,hxj⟩)⟩
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxcl := hO.inter_closure ⟨hx.1,hDense hx.2⟩
    have hempty : O ∩ (C i \ D j) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hy.2.2 ((hSub ⟨hy.1,hy.2.1⟩).2)
    rw [hempty,closure_empty] at hxcl
    exact hxcl
  intro x hx
  obtain ⟨V,hVdim,_hVC,hxV,hVD,_hConn,hVreg,_⟩ :=
    GlobalSmoothHypersurfacePrimeComponent.exists_global_prime_component (hD.2.1 j) hReg hx
  have hNot : ∀ i, ¬ V.carrier ⊆ C i := by
    intro i hSub
    rcases hSmall i with hsmall | hS
    · have hdim := DimLE.anti (hC i).analytic hSub
        (dimLE_of_irreducible_dense_regular (C i) (hC i) (hr i) (hpure i))
      have hmle := hdim x m (hVreg x hxV)
      omega
    have hVsub : V.carrier ⊆ C i ∩ D j := fun _ hy => ⟨hSub hy,hVD hy⟩
    obtain ⟨y,_,k,hmk,hreg⟩ := DimensionMonotone.locDimGE_of_regularAtDim_subset
      ((hC i).analytic.inter hDa) hVsub (hVreg x hxV) univ univ_mem
    have hlt := lt_of_regularAtDim_of_thin (hC i).analytic inter_subset_left (hThin i hS)
      (dimLE_of_irreducible_dense_regular (C i) (hC i) (hr i) (hpure i)) hreg
    have hi := hr i
    omega
  have hDenseV := irreducible_dense_off_locally_finite V.irreducible_carrier C hLF
    (fun i => (hC i).analytic) hNot hxV
  apply closure_mono _ hDenseV
  intro y hy
  exact ⟨hVD hy.1,hy.2⟩

/-- Zero containing labels force every SNC boundary member to be dense away
from the whole locally finite family of pure components. -/
theorem indexed_boundary_dense_off_zero_containing_components {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : ∀ i, containingLabels (C i) D (hC i).nonempty hD.1 = ∅)
    (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i))) :
    ∀ j, D j ⊆ closure (D j \ ⋃ i, C i) :=
  indexed_boundary_dense_off_small_or_avoiding_components C r D hC hLF hD (fun i => Or.inr (hS i)) hr hpure

end
end Hironaka.HironakaG3BoundaryDenseOffComponents
