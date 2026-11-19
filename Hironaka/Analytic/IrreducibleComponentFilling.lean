import Hironaka.Analytic.PositiveDimensionalComponent
import Hironaka.Analytic.StrictTransformLocus
import Hironaka.Analytic.AnalyticIrreducibleComponents

set_option autoImplicit false

/-!
# An irreducible component fills the analytic set near some of its points

Blueprint `ana:component-local-filling` and `ana:component-preimage-maximal` (Demailly,
*Complex analytic and differential geometry*, II.5.3–5.4).

Let `A` be an analytic subset of a complex manifold and `V` an irreducible component of `A`
(`IsIrreducibleComponent V A`: maximal among closed irreducible analytic subvarieties contained
in `A`).

* `exists_isOpen_subset_inter_subset_of_mem`: every neighbourhood `O` of every point `p ∈ V`
  contains an open `U` meeting `V` with `A ∩ U ⊆ V`.  Take the local statement (LS) with
  connected regular parts at `p` (`LocalStatementConnected.exists_connectedParts`), a point
  `cᵢ ∈ O` of each connected regular part `Gᵢ` (possible since `p ∈ closure Gᵢ`) and the
  closure `Cᵢ` of the connected component of the regular locus of `A` through `cᵢ`, a closed
  irreducible analytic subvariety of `A` (`componentSubvariety`).  Near `p`, `A` lies in
  `⋃ᵢ Cᵢ`, so the identity principle puts `V` inside one `Cᵢ`, maximality gives `Cᵢ = V`, and
  `A` agrees with `Cᵢ` near `cᵢ` (`RegularLocusComponent.exists_open_inter_subset_component`).
* `exists_isOpen_inter_subset` is the form without a prescribed point, and
  `exists_mem_regularLocus_isOpen_inter_subset` adds a regular point of `V` of dimension
  `dim V` in `U`.
* `isIrreducibleComponent_of_preimage`: maximality transported along a continuous map
  `μ : Y → M` without images.  If `S ⊆ μ⁻¹ A ∪ E` with `E` closed, `Ṽ ⊆ S` contains
  `μ⁻¹ V \ E` and lifts every top-dimensional regular point of `V` to a point off `E`, then
  `Ṽ` is an irreducible component of `S`.  This is the maximality half of Copy-4
  `lem:resolution` with no appeal to the analyticity of `μ(Z)`.
-/

open Set Filter
open scoped Topology

namespace Hironaka.IrreducibleComponentFilling

open Hironaka.NonKahlerLocus AnalyticLocalStatement LocalStatementConnected
  RegularLocusComponent

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The closure of the connected component of the regular locus of `A` through a regular
point `c`, as a closed irreducible analytic subvariety of dimension the dimension of `A`
at `c`. -/
def componentSubvariety {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) {c : M} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k) : ClosedIrreducibleAnalyticSubvariety n M where
  carrier := closure (component (n := n) A c)
  isClosed_carrier := isClosed_closure
  irreducible_carrier := isComplexAnalyticallyIrreducible_closure_component hA hc
  dim := k
  dim_le := hc.1
  regularLocus_nonempty := ⟨c, regularAtDim_closure_component hc (mem_component_self hc)⟩

@[simp] theorem componentSubvariety_carrier {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {c : M} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k) :
    (componentSubvariety hA hc).carrier = closure (component (n := n) A c) :=
  rfl

theorem componentSubvariety_subset {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    {c : M} {k : ℕ} (hc : RegularAtDim (n := n) A c k) :
    (componentSubvariety hA hc).carrier ⊆ A :=
  closure_minimal (component_subset (n := n) A c) hA.isClosed

/-- **An irreducible component fills the set near some of its points, in every neighbourhood
of every point.**  If `V` is an irreducible component of the analytic set `A`, `p ∈ V` and
`O` is an open neighbourhood of `p`, some open `U ⊆ O` meets `V` and satisfies
`A ∩ U ⊆ V`. -/
theorem exists_isOpen_subset_inter_subset_of_mem {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {V : ClosedIrreducibleAnalyticSubvariety n M}
    (hV : IsIrreducibleComponent V A) {p : M} (hp : p ∈ V.carrier) {O : Set M}
    (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ U : Set M, IsOpen U ∧ U ⊆ O ∧ (V.carrier ∩ U).Nonempty ∧ A ∩ U ⊆ V.carrier := by
  classical
  have hpA : p ∈ A := hV.1 hp
  obtain ⟨D, ⟨P⟩⟩ := exists_connectedParts hA hpA
  -- a regular point of every connected part, inside `O`
  have hc : ∀ i, ∃ c, c ∈ O ∧ c ∈ P.good i := fun i =>
    mem_closure_iff.mp (P.subset_closure_good i ⟨P.mem_piece i, P.mem_core i⟩) O hO hpO
  choose c hcO hcG using hc
  have hcreg : ∀ i, RegularAtDim (n := n) A (c i) (D.dim i) := fun i =>
    P.regularAtDim_of_mem_good i (c i) (hcG i)
  let C : Fin D.count → ClosedIrreducibleAnalyticSubvariety n M := fun i =>
    componentSubvariety hA (hcreg i)
  have hgoodC : ∀ i, P.good i ⊆ component (n := n) A (c i) := fun i =>
    (P.isPreconnected_good i).subset_connectedComponentIn (hcG i)
      (fun y hy => ⟨D.dim i, P.regularAtDim_of_mem_good i y hy⟩)
  have hpieceC : ∀ i, D.piece i ∩ P.core i ⊆ (C i).carrier := fun i =>
    (P.subset_closure_good i).trans (closure_mono (hgoodC i))
  -- near `p`, `A` lies in the union of the `C i`
  have hΩo : IsOpen (D.nbhd ∩ ⋂ i, P.core i) :=
    D.isOpen_nbhd.inter (isOpen_iInter_of_finite P.isOpen_core)
  have hpΩ : p ∈ D.nbhd ∩ ⋂ i, P.core i := ⟨D.mem_nbhd, mem_iInter.mpr P.mem_core⟩
  have hAΩ : A ∩ (D.nbhd ∩ ⋂ i, P.core i) ⊆ ⋃ i, (C i).carrier := by
    rintro y ⟨hyA, hyN, hyc⟩
    have hy : y ∈ A ∩ D.nbhd := ⟨hyA, hyN⟩
    rw [D.inter_nbhd_eq] at hy
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨i, hpieceC i ⟨hyi, mem_iInter.mp hyc i⟩⟩
  -- the pieces are indexed by a nonempty finite type; re-index them by `ℕ`
  have hcount : 0 < D.count := by
    have hp' : p ∈ A ∩ D.nbhd := ⟨hpA, D.mem_nbhd⟩
    rw [D.inter_nbhd_eq] at hp'
    obtain ⟨i, -⟩ := mem_iUnion.mp hp'
    exact Fin.pos i
  let idx : ℕ → Fin D.count := fun m =>
    if h : m < D.count then ⟨m, h⟩ else ⟨0, hcount⟩
  have hidx : ∀ i : Fin D.count, idx i.val = i := fun i => by
    simp [idx, i.isLt]
  have hcover : V.carrier ∩ (D.nbhd ∩ ⋂ i, P.core i) ⊆ ⋃ m, (C (idx m)).carrier := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hAΩ ⟨hV.1 hy.1, hy.2⟩)
    refine mem_iUnion.mpr ⟨i.val, ?_⟩
    rw [hidx i]
    exact hi
  -- the identity principle puts `V` inside one `C i`, and maximality gives equality
  obtain ⟨m, hVm⟩ := StrictTransformLocus.exists_subset_of_inter_isOpen_subset_iUnion V
    (fun m => (C (idx m)).analytic) hΩo ⟨p, hp, hpΩ⟩ hcover
  have hCV : (C (idx m)).carrier = V.carrier :=
    hV.2 (C (idx m)) hVm (componentSubvariety_subset hA (hcreg (idx m)))
  -- `A` agrees with the component near its regular point
  obtain ⟨W, hW, hcW, hAW⟩ :=
    exists_open_inter_subset_component (hcreg (idx m)) (mem_component_self (hcreg (idx m)))
  refine ⟨W ∩ O, hW.inter hO, inter_subset_right, ⟨c (idx m), ?_, hcW, hcO (idx m)⟩, ?_⟩
  · rw [← hCV]
    exact subset_closure (mem_component_self (hcreg (idx m)))
  · intro y hy
    rw [← hCV]
    exact subset_closure (hAW ⟨hy.1, hy.2.1⟩)

/-- **An irreducible component fills the set near one of its points.**  If `V` is an
irreducible component of the analytic set `A`, some open `U` meets `V` and satisfies
`A ∩ U ⊆ V`. -/
theorem exists_isOpen_inter_subset {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    {V : ClosedIrreducibleAnalyticSubvariety n M} (hV : IsIrreducibleComponent V A) :
    ∃ U : Set M, IsOpen U ∧ (V.carrier ∩ U).Nonempty ∧ A ∩ U ⊆ V.carrier := by
  obtain ⟨p, hp⟩ := V.nonempty
  obtain ⟨U, hU, -, hne, hsub⟩ :=
    exists_isOpen_subset_inter_subset_of_mem hA hV hp isOpen_univ (mem_univ p)
  exact ⟨U, hU, hne, hsub⟩

/-- **The filling open set can be centred at a top-dimensional regular point of the
component.**  Every open `O` meeting the irreducible component `V` of `A` contains an open `U`
with `A ∩ U ⊆ V` around a point at which `V` is regular of dimension `dim V`. -/
theorem exists_mem_regularLocus_isOpen_inter_subset {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {V : ClosedIrreducibleAnalyticSubvariety n M}
    (hV : IsIrreducibleComponent V A) {O : Set M} (hO : IsOpen O)
    (hVO : (V.carrier ∩ O).Nonempty) :
    ∃ x ∈ regularLocus (n := n) V.carrier V.dim, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧
      A ∩ U ⊆ V.carrier := by
  obtain ⟨p, hpV, hpO⟩ := hVO
  obtain ⟨U, hU, hUO, ⟨y, hyV, hyU⟩, hsub⟩ :=
    exists_isOpen_subset_inter_subset_of_mem hA hV hpV hO hpO
  obtain ⟨x, hxU, k, hx⟩ :=
    RegularLocusDense.exists_regularAtDim_mem_of_isOpen V.analytic hU hyV hyU
  have hk : k = V.dim := AnalyticIrreducibleComponents.eq_dim_of_regularAtDim V hx
  subst hk
  exact ⟨x, hx, U, hU, hxU, hUO, hsub⟩

section Preimage

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **Maximality transported along a map, without images.**  Let `μ : Y → M` be continuous,
`V` an irreducible component of the analytic set `A ⊆ M`, `E ⊆ Y` closed and `S ⊆ μ⁻¹ A ∪ E`.
If the closed irreducible analytic subvariety `Ṽ ⊆ S` contains `μ⁻¹ V \ E` and every
top-dimensional regular point of `V` is the image of a point of `Ṽ` off `E`, then `Ṽ` is an
irreducible component of `S`.

For a modification `μ` with exceptional set `E`, the strict transform `Ṽ` of `V` and
`S = E_nK(μ^* α) = μ⁻¹ E_nK(α) ∪ E`, this is the maximality half of Copy-4 `lem:resolution`;
the image `μ(Z)` of a competitor `Z` is never formed. -/
theorem isIrreducibleComponent_of_preimage {μ : Y → M} (hμ : Continuous μ) {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {V : ClosedIrreducibleAnalyticSubvariety n M}
    (hV : IsIrreducibleComponent V A) {E S : Set Y} (hE : IsClosed E)
    (hS : S ⊆ μ ⁻¹' A ∪ E) (Vt : ClosedIrreducibleAnalyticSubvariety n Y)
    (hVtS : Vt.carrier ⊆ S) (hpre : μ ⁻¹' V.carrier \ E ⊆ Vt.carrier)
    (hlift : ∀ x ∈ regularLocus (n := n) V.carrier V.dim,
      ∃ y ∈ Vt.carrier, y ∉ E ∧ μ y = x) :
    IsIrreducibleComponent Vt S := by
  refine ⟨hVtS, fun Z hVtZ hZS => ?_⟩
  obtain ⟨p, hp⟩ := V.nonempty
  obtain ⟨x, hx, U, hU, hxU, -, hAU⟩ :=
    exists_mem_regularLocus_isOpen_inter_subset hA hV isOpen_univ ⟨p, hp, mem_univ p⟩
  obtain ⟨y, hyVt, hyE, rfl⟩ := hlift x hx
  refine Subset.antisymm ?_ hVtZ
  refine StrictTransformLocus.subset_of_inter_isOpen_subset Z Vt.analytic
    ((hU.preimage hμ).inter hE.isOpen_compl) ⟨y, hVtZ hyVt, hxU, hyE⟩ ?_
  rintro z ⟨hzZ, hzU, hzE⟩
  have hzA : μ z ∈ A := (hS (hZS hzZ)).resolve_right hzE
  exact hpre ⟨hAU ⟨hzA, hzU⟩, hzE⟩

end Preimage

end Hironaka.IrreducibleComponentFilling
