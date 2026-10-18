/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Resolution.StrictTransformSubvariety
import Hironaka.Support.AnalyticIrreducibleUnivExact
import Mathlib.Topology.Baire.LocallyCompactRegular

set_option autoImplicit false

/-!
# Strict transforms leave analytic sets and non-nef loci

Source: CT22, Lemma 4.3 (the reduction to `W ⊄ E_nn(α)`); blueprint
`ana:rv-birational-blowup`.

Let `g : Z → Y` be the blowup of a compact complex manifold along a smooth centre and
`W ⊆ Y` a closed irreducible analytic subvariety with `W ⊄ g(Exc g)`.

* An irreducible subvariety that meets an open set `U` inside an analytic set `A` lies in
  `A`: the regular points of `W` off `A` are dense in `W`
  (`StrictTransformSubvariety.eq_closure_component` and `ComponentComplementConnected`).
* By Baire, the same holds when `W ∩ U` lies in a countable union of analytic sets: some
  member contains a nonempty relatively open part of `W ∩ U`.
* Since `g` is onto, `W \ g(Exc g) ⊆ g(W̃)`.  Hence `W̃ ⊆ g⁻¹ A` forces `W ⊆ A` for an
  analytic `A`, and `W̃ ⊆ E_nn(g^*α) = g⁻¹ E_nn(α)` (CT22, Lemma 4.2) forces
  `W ⊆ E_nn(α) = ⋃_m E_nK(α + ω/(m+1))`, a countable union of analytic sets for big `α`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StrictTransformLocus

open Hironaka

noncomputable section

section Density

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]


/-- An irreducible subvariety meeting an open set inside an analytic set lies in that set. -/
theorem subset_of_inter_isOpen_subset (V : ClosedIrreducibleAnalyticSubvariety n M)
    {A U : Set M} (hA : IsComplexAnalyticSubset (n := n) A) (hU : IsOpen U)
    (hVU : (V.carrier ∩ U).Nonempty) (hsub : V.carrier ∩ U ⊆ A) : V.carrier ⊆ A := by
  by_contra hVA
  obtain ⟨c, hc, hcA⟩ :=
    AnalyticIrreducibleComponents.exists_mem_regularLocus_not_mem_of_not_subset V hA hVA
  have hc' : RegularAtDim (n := n) V.carrier c V.dim := hc
  have hVeq := StrictTransformSubvariety.eq_closure_component V.irreducible_carrier hc'
  have hK : ¬ RegularLocusComponent.component (n := n) V.carrier c ⊆ A := fun h =>
    hcA (h (RegularLocusComponent.mem_component_self hc'))
  have hcl := (ComponentComplementConnected.isPreconnected_component_diff_and_subset_closure
    V.irreducible_carrier.analytic hA hc' hK).2
  obtain ⟨x, hxV, hxU⟩ := hVU
  have hx : x ∈ closure (RegularLocusComponent.component (n := n) V.carrier c \ A) :=
    closure_minimal hcl isClosed_closure (hVeq ▸ hxV)
  obtain ⟨y, hyU, hyK, hyA⟩ := mem_closure_iff.mp hx U hU hxU
  exact hyA (hsub ⟨RegularLocusComponent.component_subset (n := n) V.carrier c hyK, hyU⟩)

/-- **Baire.**  An irreducible subvariety meeting an open set inside a countable union of
analytic sets lies in one of them. -/
theorem exists_subset_of_inter_isOpen_subset_iUnion (V : ClosedIrreducibleAnalyticSubvariety n M)
    {A : ℕ → Set M} (hA : ∀ m, IsComplexAnalyticSubset (n := n) (A m)) {U : Set M}
    (hU : IsOpen U) (hVU : (V.carrier ∩ U).Nonempty) (hsub : V.carrier ∩ U ⊆ ⋃ m, A m) :
    ∃ m, V.carrier ⊆ A m := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel n) M
  set O : Set M := V.carrier ∩ U with hO
  have hOlc : IsLocallyClosed O := V.isClosed_carrier.isLocallyClosed.inter hU.isLocallyClosed
  have : LocallyCompactSpace O := hOlc.locallyCompactSpace
  have : BaireSpace O := BaireSpace.of_t2Space_locallyCompactSpace
  let B : ℕ → Set O := fun m => (Subtype.val : O → M) ⁻¹' A m
  have hBc : ∀ m, IsClosed (B m) := fun m =>
    (hA m).isClosed.preimage continuous_subtype_val
  have hBu : ⋃ m, B m = univ := by
    refine eq_univ_of_forall fun p => ?_
    simpa [B] using hsub p.2
  have : Nonempty O := hVU.to_subtype
  obtain ⟨m, p, hp⟩ := nonempty_interior_of_iUnion_of_closed hBc hBu
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp (isOpen_interior (s := B m))
  refine ⟨m, subset_of_inter_isOpen_subset V (hA m) (hW.inter hU) ?_ ?_⟩
  · refine ⟨p.1, p.2.1, ?_, p.2.2⟩
    have : p ∈ (Subtype.val : O → M) ⁻¹' W := hWeq ▸ hp
    exact this
  · rintro y ⟨hyV, hyW, hyU⟩
    have hy : (⟨y, hyV, hyU⟩ : O) ∈ interior (B m) := by
      rw [← hWeq]
      exact hyW
    exact (interior_subset hy : (⟨y, hyV, hyU⟩ : O) ∈ B m)

end Density
end
end Hironaka.StrictTransformLocus
