import Hironaka.Resolution.HironakaG3InheritedBornNoCollision
import Hironaka.Resolution.HironakaG3DisjointAtlasFootprint
import Hironaka.Resolution.HironakaG3IndexedAvoidingCentresOver
import Hironaka.Resolution.HironakaG3RGlobalSNC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3InheritedLabelsDistinct
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaG3RTowerClass
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary HironakaG3IndexedCanonicalContact
  HironakaG3OrderedFiniteWindows HironakaG3IndexedAvoidingBoundaryClass HironakaG3IndexedAvoidingCentresOver
  HironakaG3DisjointLocalTowerAtlas HironakaG3DisjointAtlasFootprint HironakaG3InheritedBornNoCollision
  HironakaG3RGlobalSNC

/-- Equal nonempty inherited traces have the same label when the first
strict transform is dense off a closed exceptional footprint. -/
theorem inherited_trace_labels_eq_of_density_footprint {n : ℕ} {X Z : CMfd.{0} n}
    {κ : Type*} [LinearOrder κ] (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    (F : Set X) (hF : IsClosed F) {P : Z → X}
    (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (hExc : exceptionalLocus n P ⊆ P ⁻¹' F) (j k : κ)
    (hDense : strictTransform n P (D j) ⊆ closure (strictTransform n P (D j) ∩ P ⁻¹' Fᶜ))
    (O : Opens Z) (hNE : (strictTransform n P (D j) ∩ O).Nonempty)
    (hEq : strictTransform n P (D j) ∩ O = strictTransform n P (D k) ∩ O) : j = k := by
  by_contra hjk
  obtain ⟨z,hzD,hzO⟩ := hNE
  have hzDense := hDense hzD
  obtain ⟨y,hyO,hyD,hyF⟩ := mem_closure_iff_nhds.mp hzDense O (O.isOpen.mem_nhds hzO)
  have hyExc : y ∉ exceptionalLocus n P := fun he => hyF (hExc he)
  let N : Set Z := (O : Set Z) ∩ P ⁻¹' Fᶜ
  have hN : N ∈ 𝓝 y := inter_mem (O.isOpen.mem_nhds hyO) ((hF.isOpen_compl.preimage hP.continuous).mem_nhds hyF)
  have hImg : P '' N ∈ 𝓝 (P y) := by
    rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hP hyExc]
    exact image_mem_map hN
  obtain ⟨U,hUsub,hUopen,hyU⟩ := mem_nhds_iff.mp hImg
  have hLocal : D j ∩ U = D k ∩ U := by
    ext x
    constructor <;> intro hx
    · obtain ⟨a,haN,haP⟩ := hUsub hx.2
      have haExc : a ∉ exceptionalLocus n P := fun he => haN.2 (hExc he)
      have haJ0 : P a ∈ D j := by rw [haP]; exact hx.1
      have haJ : a ∈ strictTransform n P (D j) := subset_closure ⟨haJ0,haExc⟩
      have haK : a ∈ strictTransform n P (D k) := ((Set.ext_iff.mp hEq a).mp ⟨haJ,haN.1⟩).1
      have hpK := HironakaAdmissibleCalculus.strictTransform_subset_preimage hP.continuous (hD.2.1 k) haK
      exact ⟨haP ▸ hpK,hx.2⟩
    · obtain ⟨a,haN,haP⟩ := hUsub hx.2
      have haExc : a ∉ exceptionalLocus n P := fun he => haN.2 (hExc he)
      have haK0 : P a ∈ D k := by rw [haP]; exact hx.1
      have haK : a ∈ strictTransform n P (D k) := subset_closure ⟨haK0,haExc⟩
      have haJ : a ∈ strictTransform n P (D j) := ((Set.ext_iff.mp hEq a).mpr ⟨haK,haN.1⟩).1
      have hpJ := HironakaAdmissibleCalculus.strictTransform_subset_preimage hP.continuous (hD.2.1 j) haJ
      exact ⟨haP ▸ hpJ,hx.2⟩
  have hyDj : P y ∈ D j := HironakaAdmissibleCalculus.strictTransform_subset_preimage hP.continuous (hD.2.1 j) hyD
  let s : Finset κ := {j,k}
  let l := s.sort (· ≤ ·)
  have hj : j ∈ l := by simp [l,s]
  have hk : k ∈ l := by simp [l,s]
  obtain ⟨p,hp⟩ := List.mem_iff_get.mp hj
  obtain ⟨q,hq⟩ := List.mem_iff_get.mp hk
  have hpq : p ≠ q := fun he => hjk (hp.symm.trans (he ▸ hq))
  have hsnc := sorted_boundary_snc D hD s
  let E := l.map D
  let p' : Fin E.length := ⟨p.val,by simp [E,p.isLt]⟩
  let q' : Fin E.length := ⟨q.val,by simp [E,q.isLt]⟩
  have hpq' : p' ≠ q' := by
    intro he
    have hv : p.val = q.val := congrArg (fun z : Fin E.length => z.val) he
    exact hpq (Fin.ext hv)
  have hgetp : E.get p' = D j := by
    simp only [E,List.get_eq_getElem,List.getElem_map]
    change D (l.get p) = D j
    rw [hp]
  have hgetq : E.get q' = D k := by
    simp only [E,List.get_eq_getElem,List.getElem_map]
    change D (l.get q) = D k
    rw [hq]
  have hsnc' : IsSNCDivisor n E := hsnc
  exact not_eq_inter_of_isSNCDivisor (E := E) hsnc' (p := p') (q := q') hpq' hUopen hyU
    (by rw [hgetp]; exact hyDj) (by rw [hgetp,hgetq]; exact hLocal)
/-- Nonempty equal local traces of actual inherited strict transforms carry
the same original indexed boundary label. -/
theorem inherited_strict_trace_labels_eq {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X) (W : ι → Opens X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : ∀ i, containingLabels (C i) D (hC i).nonempty hD.1 = ∅)
    (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
    {P : Z → X} (hG : IsGluedFrom (disjointWindowClass C W
      (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)) Z P)
    (O : Opens Z) (j k : κ) (hNE : (strictTransform n P (D j) ∩ O).Nonempty)
    (hEq : strictTransform n P (D j) ∩ O = strictTransform n P (D k) ∩ O) : j = k := by
  have hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      indexedAvoidingBoundaryClass (C i) (r i) D U Y T →
      RestrictEmptyTower.CentresOver ((Subtype.val : U → X) ⁻¹' C i) T := by
    intro i U Y T hT
    exact indexed_avoiding_centres_over (C i) D (hC i).analytic hD (hr i) (hpure i) U Y T hT
  have hExc := (disjoint_atlas_footprint C W (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)
    (fun i => (hC i).analytic.isClosed) hLF hCentres hG).1
  exact inherited_trace_labels_eq_of_density_footprint D hD (⋃ i, C i)
    (hLF.isClosed_iUnion (fun i => (hC i).analytic.isClosed)) hG.1 hExc j k
    (inherited_strict_dense_off_component_preimage C r D hC hLF hD hS hr hpure hG.1 j) O hNE hEq

end
end Hironaka.HironakaG3InheritedLabelsDistinct
