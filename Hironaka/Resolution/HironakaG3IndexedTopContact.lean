import Hironaka.Resolution.HironakaG3SeparatorBoundaryDichotomy
import Hironaka.Resolution.HironakaG3TopContactBoundary
import Hironaka.Resolution.HironakaG3IndexedContactDimension
import Hironaka.Invariant.CodimOneAdmissibleAlong
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedTopContact
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings BoundaryCount
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation
  HironakaG3IndexedContainingBoundary HironakaG3IndexedCanonicalContact
  HironakaG3TopContactBoundary CodimOneAdmissibleAlong HironakaG3IndexedContactDimension
  HironakaG3RTowerClass HironakaG3IndexedMixedGluing HironakaG3IndexedSeparatedComponents
  HironakaG3ProperDenseIrreducible

/-- The actual intersection of all containing labels has normal crossings
with the entire indexed SNC boundary. -/
theorem canonical_contact_has_indexed_normal_crossings {n : ℕ} {X : CMfd.{0} n} {ι : Type*}
    (C : Set X) (D : ι → Set X) (hC : C.Nonempty) (hD : IsLocallyFiniteSNCDivisor n D) :
    HasNormalCrossingsWithBoundary (canonicalContact C D hC hD.1) D := by
  let S := containingLabels C D hC hD.1
  let N := canonicalContact C D hC hD.1
  intro x hx
  obtain ⟨T,⟨Φ,hsrc,hzero,hcoord⟩,hcard,_hinj⟩ := hD.2.2 x
  have hxS : ∀ i ∈ S, x ∈ D i := by
    simpa only [N,canonicalContact,mem_iInter,S] using hx
  refine ⟨S.biUnion T,T,⟨Φ,hsrc,hzero,?_⟩,?_⟩
  · intro o ho y hy hyΦ
    cases o with
    | none =>
      change y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S.biUnion T)
      rw [mem_coordSubspace_biUnion]
      simp only [N,canonicalContact,mem_iInter]
      exact forall₂_congr fun i hi => hcoord i (hxS i hi) hy hyΦ
    | some i =>
      exact hcoord i ho hy hyΦ
  · exact hcard

/-- In the equal-contact-dimension case, the target is already smooth and has
normal crossings with every member of the entire indexed boundary. -/
theorem indexed_top_contact_already_normal {n r : ℕ} {X : CMfd.{0} n} {ι : Type*}
    (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C)
    (hD : IsLocallyFiniteSNCDivisor n D)
    (hpure : C ⊆ closure (regularLocus (n := n) C r))
    (htop : n - (containingLabels C D hC.nonempty hD.1).card ≤ r) :
    let N := canonicalContact C D hC.nonempty hD.1
    ∃ O : Opens X, C = N ∩ (O : Set X) ∧ IsClosedSubmanifold n C ∧
      (∀ x ∈ C, RegularAtDim (n := n) C x r) ∧ HasNormalCrossingsWithBoundary C D := by
  let : LinearOrder ι := WellOrderingRel.isWellOrder.linearOrder
  let S := containingLabels C D hC.nonempty hD.1
  let N := canonicalContact C D hC.nonempty hD.1
  have hGeom := canonicalContact_geometry C D hC hD
  change C ⊆ N ∧ N.Nonempty ∧ IsClosed N ∧
    (∀ x ∈ N, RegularAtDim (n := n) N x (n - S.card)) ∧ S.card ≤ n ∧
    IsClosedSubmanifold n N at hGeom
  obtain ⟨hCN,hNne,hNc,hNr,hCard,hNsm⟩ := hGeom
  have hle : r ≤ n - S.card := indexed_component_dimension_le_contact C D hC hD hpure
  have heq : n - S.card = r := Nat.le_antisymm htop hle
  have hrn : r ≤ n := hle.trans (Nat.sub_le n S.card)
  obtain ⟨t,ht⟩ := Nat.exists_eq_add_of_le hrn
  have hn : n = r+t := by omega
  subst n
  have hNr' : ∀ x ∈ N, RegularAtDim (n := r+t) N x r := by simpa only [heq] using hNr
  obtain ⟨O,hCO,hReg⟩ := exists_open_eq_inter_contact N hNc hNr' C hC.analytic hCN hpure
  have hNCN : HasNormalCrossingsWithBoundary N D :=
    canonical_contact_has_indexed_normal_crossings C D hC.nonempty hD
  refine ⟨O,hCO,⟨hC.analytic.isClosed,fun x hx => ⟨r,hReg x hx⟩⟩,hReg,?_⟩
  intro x hx
  obtain ⟨T₀,T,hcoord,hcard⟩ := hNCN x (hCN hx)
  refine ⟨T₀,T,isCoordinateFamilyAt_congr ?_ hcoord,hcard⟩
  have hxO : x ∈ (O : Set X) := (hCO ▸ hx).2
  filter_upwards [O.isOpen.mem_nhds hxO] with y hy
  rintro (_ | i)
  · change y ∈ C ↔ y ∈ N
    rw [hCO]
    simp [hy]
  · rfl

/-- The equal-contact branch of an actual separated component is already
resolved against the entire current indexed boundary. -/
theorem separator_top_contact_already_normal {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ τ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) {P : Z → X} (h : IsGluedFrom (indexedMixedClass V D) Z P)
    (E : τ → Set Z) (hE : IsLocallyFiniteSNCDivisor n E) (a : ι) :
    let C := strictTransform n P (V a).carrier
    let hC := indexed_separator_strictTransform_irreducible V hDim hDistinct D h a
    let S := containingLabels C E hC.nonempty hE.1
    let N := canonicalContact C E hC.nonempty hE.1
    n - S.card ≤ (V a).dim →
      ∃ O : Opens Z, C = N ∩ (O : Set Z) ∧ IsClosedSubmanifold n C ∧
        (∀ x ∈ C, RegularAtDim (n := n) C x (V a).dim) ∧ HasNormalCrossingsWithBoundary C E := by
  let C := strictTransform n P (V a).carrier
  let hC := indexed_separator_strictTransform_irreducible V hDim hDistinct D h a
  have hpure : C ⊆ closure (regularLocus (n := n) C (V a).dim) :=
    strictTransform_subset_closure_regularLocus h.1 (V a).isClosed_carrier
      (HironakaEmbeddedReducible.subset_closure_regularLocus (V a))
  dsimp only
  intro htop
  exact indexed_top_contact_already_normal C E hC hE hpure htop
end
end Hironaka.HironakaG3IndexedTopContact
