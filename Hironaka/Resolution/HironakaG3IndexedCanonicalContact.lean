import Hironaka.Resolution.HironakaG3IndexedContainingBoundary
import Hironaka.Resolution.HironakaG3ContainingSNCStratum
import Hironaka.Resolution.HironakaG3IndexedBoundaryDichotomy

/-!
# The actual contact of all globally containing original boundary labels

The finite containing-label set defines the actual intersection. Indexed SNC
coordinates imply its fixed smooth dimension, transversality to every finite
residual window, and density of the original component off the entire residual
locally finite family. This does not construct a full resolving class.

Blueprint: `hironaka-g3-indexed-canonical-contact.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG3IndexedCanonicalContact

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences BlowupTowers NormalCrossings BoundaryCount
  HironakaG3IndexedContainingBoundary HironakaG3OrderedFiniteWindows
  HironakaG3ContainingSNCStratum HironakaActualFullBoundaryContainmentPatterns
  HironakaActualLocallyFiniteBoundary

variable {n : ℕ} {X : CMfd.{0} n} {ι : Type*}

private theorem memberInter_all_sorted [LinearOrder ι] (D : ι → Set X) (s : Finset ι) :
    memberInter ((s.sort (· ≤ ·)).map D) Finset.univ = ⋂ i ∈ s, D i := by
  ext x
  constructor
  · intro hx
    simp only [mem_iInter]
    intro i hi
    have hmem : D i ∈ (s.sort (· ≤ ·)).map D :=
      List.mem_map.mpr ⟨i,by simpa using hi,rfl⟩
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hmem
    rw [← hj]
    exact hx j (Finset.mem_univ j)
  · intro hx j _
    obtain ⟨i,hi,hij⟩ := List.mem_map.mp (List.get_mem ((s.sort (· ≤ ·)).map D) j)
    rw [← hij]
    exact mem_iInter.mp (mem_iInter.mp hx i) (by simpa using hi)

/-- Every finite original-label intersection is closed and smooth of its
expected fixed dimension. Its SNC geometry is derived from indexed SNC. -/
theorem finite_intersection_geometry [LinearOrder ι] (D : ι → Set X)
    (hD : IsLocallyFiniteSNCDivisor n D) (s : Finset ι) :
    IsClosed (⋂ i ∈ s, D i) ∧
    (∀ x ∈ ⋂ i ∈ s, D i, RegularAtDim (n := n) (⋂ i ∈ s, D i) x (n - s.card)) ∧
    IsClosedSubmanifold n (⋂ i ∈ s, D i) := by
  have hE := sorted_boundary_snc D hD s
  have hclosed : IsClosed (⋂ i ∈ s, D i) := by
    rw [← memberInter_all_sorted D s]
    exact isClosed_memberInter hE.1 Finset.univ
  have hregular : ∀ x ∈ ⋂ i ∈ s, D i,
      RegularAtDim (n := n) (⋂ i ∈ s, D i) x (n - s.card) := by
    intro x hx
    have h := (memberInter_regularAtDim hE Finset.univ x
      (by rwa [memberInter_all_sorted D s])).1
    simpa only [memberInter_all_sorted,Finset.card_univ,Fintype.card_fin,
      List.length_map,Finset.length_sort] using h
  exact ⟨hclosed,hregular,hclosed,fun x hx => ⟨n - s.card,hregular x hx⟩⟩

/-- Analyticity of every indexed member follows from the original indexed
SNC geometry; no additional analytic-family input or dimension bound is used. -/
theorem isComplexAnalyticSubset_member [LinearOrder ι] (D : ι → Set X)
    (hD : IsLocallyFiniteSNCDivisor n D) (i : ι) :
    IsComplexAnalyticSubset (n := n) (D i) := by
  apply AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
  simpa using (finite_intersection_geometry D hD {i}).2.2

/-- The actual intersection of the entire original containing-label set. -/
def canonicalContact (C : Set X) (D : ι → Set X)
    (hC : C.Nonempty) (hD : LocallyFinite D) : Set X :=
  ⋂ i ∈ containingLabels C D hC hD, D i

/-- The empty containing-label set gives the entire ambient manifold. -/
theorem canonicalContact_eq_univ_of_empty (C : Set X) (D : ι → Set X)
    (hC : C.Nonempty) (hD : LocallyFinite D)
    (hS : containingLabels C D hC hD = ∅) :
    canonicalContact C D hC hD = univ := by
  simp only [canonicalContact,hS,Finset.notMem_empty,iInter_of_empty,iInter_univ]

/-- The canonical actual contact contains the original component and is
closed smooth of pure dimension `n - |S|`, with the actual bound `|S| ≤ n`. -/
theorem canonicalContact_geometry [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C)
    (hD : IsLocallyFiniteSNCDivisor n D) :
    let S := containingLabels C D hC.nonempty hD.1
    let N := canonicalContact C D hC.nonempty hD.1
    C ⊆ N ∧ N.Nonempty ∧ IsClosed N ∧
    (∀ x ∈ N, RegularAtDim (n := n) N x (n - S.card)) ∧
    S.card ≤ n ∧ IsClosedSubmanifold n N := by
  dsimp only
  let S := containingLabels C D hC.nonempty hD.1
  have hCN : C ⊆ canonicalContact C D hC.nonempty hD.1 := by
    intro x hx
    simp only [canonicalContact,mem_iInter]
    intro i hi
    exact (mem_containingLabels C D hC.nonempty hD.1 i).mp hi hx
  obtain ⟨x,hx⟩ := hC.nonempty
  obtain ⟨hc,hr,hsm⟩ := finite_intersection_geometry D hD S
  have hCard : S.card ≤ n := by
    have h := (memberInter_regularAtDim (sorted_boundary_snc D hD S) Finset.univ x
      (by rw [memberInter_all_sorted D S]; exact hCN hx)).2
    simpa only [Finset.card_univ,Fintype.card_fin,List.length_map,Finset.length_sort] using h
  exact ⟨hCN,⟨x,hCN hx⟩,hc,hr,hCard,hsm⟩

private theorem selected_inter_eq_contact [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : C.Nonempty) (hD : LocallyFinite D) (q : Finset ι)
    (hq : containingLabels C D hC hD ⊆ q) :
    let E := (q.sort (· ≤ ·)).map D
    memberInter E (Finset.univ.filter (fun j : Fin E.length => C ⊆ E.get j)) =
      canonicalContact C D hC hD := by
  dsimp only
  ext x
  constructor
  · intro hx
    simp only [canonicalContact,mem_iInter]
    intro i hi
    have hmem : D i ∈ (q.sort (· ≤ ·)).map D :=
      List.mem_map.mpr ⟨i,by simpa using hq hi,rfl⟩
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hmem
    have hsel : j ∈ Finset.univ.filter (fun j : Fin ((q.sort (· ≤ ·)).map D).length =>
        C ⊆ ((q.sort (· ≤ ·)).map D).get j) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [hj]
      exact (mem_containingLabels C D hC hD i).mp hi
    rw [← hj]
    exact hx j hsel
  · intro hx j hj
    obtain ⟨i,hi,hij⟩ := List.mem_map.mp (List.get_mem ((q.sort (· ≤ ·)).map D) j)
    have hCi : C ⊆ D i := by
      rw [hij]
      exact (Finset.mem_filter.mp hj).2
    have hiS := (mem_containingLabels C D hC hD i).mpr hCi
    rw [← hij]
    exact mem_iInter.mp (mem_iInter.mp hx i) hiS

/-- The actual contact is transverse to every sorted finite residual window
of original labels, including the empty contact and empty-window cases. -/
theorem isTransverse_residual_window [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C)
    (hD : IsLocallyFiniteSNCDivisor n D) (R : Finset ι)
    (hR : Disjoint (containingLabels C D hC.nonempty hD.1) R) :
    IsTransverse n (canonicalContact C D hC.nonempty hD.1)
      ((R.sort (· ≤ ·)).map D) := by
  let S := containingLabels C D hC.nonempty hD.1
  let q := S ∪ R
  let E := (q.sort (· ≤ ·)).map D
  let A := Finset.univ.filter (fun j : Fin E.length => C ⊆ E.get j)
  have hE := sorted_boundary_snc D hD q
  have hEq : memberInter E A = canonicalContact C D hC.nonempty hD.1 :=
    selected_inter_eq_contact C D hC.nonempty hD.1 q (Finset.subset_union_left)
  have hTrans : IsTransverse n (memberInter E A) (remainingBoundary E A) := by
    have h := BoundaryCountAlong.isTransverse_inter_memberInter_drop hE
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE) A
    simpa only [univ_inter,remainingBoundary] using h
  rw [← hEq]
  apply NormalCrossingsComparison.isTransverse_of_forall_mem hTrans
  intro H hH
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hH
  have hiR : i ∈ R := by simpa using hi
  have hiS : i ∉ S := fun his => Finset.disjoint_left.mp hR his hiR
  have hiq : i ∈ q := Finset.mem_union_right S hiR
  have hmem : D i ∈ E := List.mem_map.mpr ⟨i,by simpa using hiq,rfl⟩
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hmem
  apply (mem_remainingBoundary E A (D i)).mpr
  refine ⟨j,?_,hj⟩
  intro hjA
  apply hiS
  apply (mem_containingLabels C D hC.nonempty hD.1 i).mpr
  rw [← hj]
  exact (Finset.mem_filter.mp hjA).2

/-- Irreducible avoidance applies to the entire actual locally finite
residual family, with no separately assumed analyticity or density packet. -/
theorem dense_off_residual_family [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C)
    (hD : IsLocallyFiniteSNCDivisor n D) :
    C ⊆ closure (C \ ⋃ i : {i // i ∉ containingLabels C D hC.nonempty hD.1}, D i.val) := by
  let S := containingLabels C D hC.nonempty hD.1
  let R : {i // i ∉ S} → Set X := fun i => D i.val
  have hLF : LocallyFinite R := hD.1.comp_injective Subtype.val_injective
  apply HironakaG3IndexedBoundaryDichotomy.irreducible_dense_off_locally_finite hC R hLF
  · intro i
    exact isComplexAnalyticSubset_member D hD i.val
  · intro i hi
    exact i.property ((mem_containingLabels C D hC.nonempty hD.1 i.val).mpr hi)

end

end Hironaka.HironakaG3IndexedCanonicalContact
