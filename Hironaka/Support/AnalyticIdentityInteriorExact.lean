/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Analytic.AnalyticSubsetTopology
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false

/-!
# Topology of complex analytic subsets

Source: the standard facts about analytic sets used in Copy-4, `sec:gluing`
(`transcendental-nakamaye-copy4-20260911`): "a connected complex manifold is
irreducible"; Grauert--Remmert, *Coherent analytic sheaves*, Ch. 5 and 9;
blueprint `ana:irreducible-components`.

* `eqOn_zero_of_isOpen_convex`: the identity theorem for a holomorphic function
  on an open convex subset of a complex normed space, proved by restricting to
  complex lines and applying the one-variable identity theorem.
* `IsComplexAnalyticSubset.isClosed`: an analytic subset is closed.
* `IsComplexAnalyticSubset.isClosed_interior`: the interior of an analytic subset
  is closed.  At a point of the closure of the interior, the local generators
  vanish on a nonempty open subset of a coordinate ball, hence on the whole ball.
* `isComplexAnalyticallyIrreducible_univ_of_connectedSpace`: a connected complex
  manifold is analytically irreducible.  An analytic subset with nonempty
  interior is clopen-interior, hence everything; two closed sets with empty
  interior cannot cover the manifold.
-/

open Set Filter Metric
open scoped Topology

namespace Hironaka

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The interior of an analytic subset is closed. -/
theorem IsComplexAnalyticSubset.isClosed_interior {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) : IsClosed (interior A) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨p⟩ := hA x
  set e := (complexChartAt (n := n) x).val with he
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp p.isOpen_coordinateNeighborhood (e x)
      p.center_mem_coordinateNeighborhood
  set S := e.source ∩ e ⁻¹' ball (e x) r with hSdef
  have hSo : IsOpen S := e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
  have hxS : x ∈ S := ⟨mem_complexChartAt_source (n := n) x, mem_ball_self hr⟩
  obtain ⟨y, hyS, hyint⟩ := mem_closure_iff.mp hx S hSo hxS
  have hUo : IsOpen (e '' (interior A ∩ S)) :=
    e.isOpen_image_of_subset_source (isOpen_interior.inter hSo) fun z hz => hz.2.1
  have hvanish : ∀ i, EqOn (p.generator i) 0 (ball (e x) r) := by
    intro i
    refine eqOn_zero_of_isOpen_convex isOpen_ball (convex_ball _ _)
      ((p.generator_holomorphic i).mono hball) hUo ?_ ⟨e y, y, ⟨hyint, hyS⟩, rfl⟩ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact hz.2.2
    · rintro _ ⟨z, hz, rfl⟩
      exact (p.zeroLocus hz.2.1 (hball hz.2.2)).mp (interior_subset hz.1) i
  have hSA : S ⊆ A := fun z hz =>
    (p.zeroLocus hz.1 (hball hz.2)).mpr fun i => hvanish i hz.2
  exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (hSo.mem_nhds hxS) hSA)

/-- An analytic subset of a connected manifold with nonempty interior is the
whole manifold. -/
theorem IsComplexAnalyticSubset.eq_univ_of_interior_nonempty [ConnectedSpace M]
    {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hint : (interior A).Nonempty) : A = univ :=
  eq_univ_of_univ_subset
    ((IsClopen.eq_univ ⟨hA.isClosed_interior, isOpen_interior⟩ hint).symm.subset.trans
      interior_subset)

/-- **A connected complex manifold is analytically irreducible.** -/
theorem isComplexAnalyticallyIrreducible_univ_of_connectedSpace [ConnectedSpace M] :
    IsComplexAnalyticallyIrreducible (n := n) (univ : Set M) := by
  refine ⟨isComplexAnalyticSubset_univ, univ_nonempty, fun B C hB hC _ _ hBC => ?_⟩
  by_cases hBi : (interior B).Nonempty
  · exact Or.inl (hB.eq_univ_of_interior_nonempty hBi).symm
  by_cases hCi : (interior C).Nonempty
  · exact Or.inr (hC.eq_univ_of_interior_nonempty hCi).symm
  exfalso
  rw [not_nonempty_iff_eq_empty] at hBi hCi
  have hBC' := interior_union_isClosed_of_interior_empty hB.isClosed hCi
  rw [← hBC, interior_univ, hBi] at hBC'
  exact univ_nonempty.ne_empty hBC'

end
end Hironaka
