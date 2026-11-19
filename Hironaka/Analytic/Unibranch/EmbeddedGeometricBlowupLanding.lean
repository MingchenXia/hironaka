import Hironaka.Analytic.Unibranch.EmbeddedBlowupUniversal

/-!
# Ordinary original source ideal invertibility derives pruned point landing

The accepted local source factorization INTERNALLY gives actual source
opens with dense good loci, without target density. Continuity globalizes
that density and derives actual point landing in closure(W minus C).
The FULL reduced quotient factorization is a separate consumer.
Blueprint FIRST: `embedded-geometric-blowup-landing.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowupLanding

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  BlowupStrictSubmanifold
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  SourceReducedComplexSpace EmbeddedBlowupUniversal

noncomputable section

variable {n : ℕ} {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C W : Set M} {π : Y → M}
  (hπ : IsBlowupAlong n C π) (hW : IsComplexAnalyticSubset (n := n) W)
  (A : SourceReducedComplexSpace) (F : A ⟶ ofClosedAnalytic W hW)
  (hInv : ∀ x : A.obj.left,
    Module.Invertible (A.obj.left.presheaf.stalk x).carrier
      (Ideal.map (F.hom.left.stalkMap x).hom
        (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (F.hom.left.base x)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (F.hom.left.base x).val))))

include hπ hInv

/-- Standard whole-ideal invertibility on an arbitrary ORIGINAL source
derives genuine global good-locus density, with NO target density/SC input. -/
theorem dense_compl_centre_of_module_invertible :
    Dense {x : A.obj.left | (F.hom.left.base x).val ∉ C} := by
  rw [dense_iff_closure_eq,eq_univ_iff_forall]
  intro x
  obtain ⟨P,j,_K,_hj,⟨u,hu⟩,_hP,_hKpoint,_hKproj,hd⟩ :=
    exists_local_source_factorization_of_module_invertible hπ hW A F hInv x
  have hucl : u ∈ closure {v : P | (F.hom.left.base (j.base v)).val ∉ C} := by
    rw [hd.closure_eq]
    trivial
  have hsub : j.base '' {v : P | (F.hom.left.base (j.base v)).val ∉ C} ⊆
      {a : A.obj.left | (F.hom.left.base a).val ∉ C} := by
    rintro _ ⟨v,hv,rfl⟩
    exact hv
  have hjcl := mem_closure_image j.base.hom.continuous.continuousAt hucl
  exact hu ▸ closure_mono hsub hjcl

/-- The literal original ambient point map lands in the actual pruned
carrier from ordinary invertibility, not an input landing certificate. -/
theorem point_lands_prunedCarrier_of_module_invertible (a : A.obj.left) :
    (F.hom.left.base a).val ∈ closure (W \ C) := by
  let f : A.obj.left → M := fun x => (F.hom.left.base x).val
  have hf : Continuous f := continuous_subtype_val.comp F.hom.left.base.hom.continuous
  have hd := dense_compl_centre_of_module_invertible hπ hW A F hInv
  have hacl : a ∈ closure {x : A.obj.left | (F.hom.left.base x).val ∉ C} := by
    rw [hd.closure_eq]
    trivial
  have hsub : f '' {x : A.obj.left | (F.hom.left.base x).val ∉ C} ⊆ W \ C := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨(F.hom.left.base x).property,hx⟩
  exact closure_mono hsub (mem_closure_image hf.continuousAt hacl)

/-- ANY actual continuous ambient lift of SAME F lands in the centre-relative
geometric transform. The final full UP internally supplies that old full lift;
no incoming geometric landing or target density is used here. -/
theorem continuous_lift_lands_geometricTransform (k : A.obj.left → Y) (hk : Continuous k)
    (hcomm : ∀ a, π (k a) = (F.hom.left.base a).val) (a : A.obj.left) :
    k a ∈ geoStrictTransform π C W := by
  have hd := dense_compl_centre_of_module_invertible hπ hW A F hInv
  have hclosed : IsClosed (k ⁻¹' geoStrictTransform π C W) := isClosed_closure.preimage hk
  have hsub : {x : A.obj.left | (F.hom.left.base x).val ∉ C} ⊆
      k ⁻¹' geoStrictTransform π C W := by
    intro x hx
    apply subset_closure
    change π (k x) ∈ W \ C
    rw [hcomm x]
    exact ⟨(F.hom.left.base x).property,hx⟩
  have hwhole : (univ : Set A.obj.left) ⊆ k ⁻¹' geoStrictTransform π C W := by
    rw [← hd.closure_eq]
    exact closure_minimal hsub hclosed
  exact hwhole (mem_univ a)

end
end Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowupLanding
