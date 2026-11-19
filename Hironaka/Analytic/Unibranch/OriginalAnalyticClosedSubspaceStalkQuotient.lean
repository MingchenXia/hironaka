import Hironaka.Analytic.Unibranch.OriginalClosedSubspaceFactorization
import Hironaka.Resolution.HironakaIntrinsicReducedCentreOpenPullback
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Literal intrinsic stalk quotients of original analytic closed inclusions

The SAME full contained inclusion has exactly the whole intrinsic ideal
as its native stalk kernel. Actual ambient quotient maps derive its stalk
surjectivity and a specified quotient equivalence commuting with that map.
No smoothness, density, tensor-ideal identification or section quotient.

Blueprint FIRST: `original-analytic-closed-subspace-stalk-quotient.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspaceStalkQuotient

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka
  HironakaActualAnalyticSubspace HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaIntrinsicReducedCentreIdealModel HironakaIntrinsicReducedCentreOpenPullback
  SourceReducedComplexSpace OriginalClosedSubspaceFactorization

noncomputable section

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {D W : Set M} (hD : IsComplexAnalyticSubset (n := n) D)
  (hW : IsComplexAnalyticSubset (n := n) W) (hDW : D ⊆ W)

/-- The actual contained inclusion stalk kernel is precisely the ENTIRE
intrinsic ideal inclusion image on the SAME original target and point. -/
theorem contained_inclusion_stalk_kernel_eq_intrinsicCentreStalkRange (d : D) :
    RingHom.ker (((inclusion hD hW hDW).hom.left.stalkMap d).hom) =
      intrinsicCentreStalkRange (ofClosedAnalytic W hW).obj.left
        ((Subtype.val : W → M) ⁻¹' D) ((inclusion hD hW hDW).hom.left.base d) := by
  let j : actualSubspaceLocallyRingedSpace (n := n) D ⟶
      actualSubspaceLocallyRingedSpace (n := n) W := (inclusion hD hW hDW).hom.left
  let qW := actualSubspaceInclusion (n := n) W
  let w : W := j.base d
  change RingHom.ker (j.stalkMap d).hom =
    intrinsicCentreStalkRange (actualSubspaceLocallyRingedSpace (n := n) W)
      ((Subtype.val : W → M) ⁻¹' D) w
  have hpre : Ideal.comap (qW.stalkMap w).hom
      (RingHom.ker (j.stalkMap d).hom) =
        actualWholeSheafStalkIdeal (vanishingIdeal (n := n) D) d.val := by
    rw [RingHom.comap_ker]
    have hsquare : (j ≫ qW).stalkMap d =
        (actualSubspaceInclusion (n := n) D).stalkMap d := by
      have h := LocallyRingedSpace.stalkMap_congr_hom (j ≫ qW)
        (actualSubspaceInclusion (n := n) D) (inclusion_ambient hD hW hDW) d
      rw [TopCat.Presheaf.stalkSpecializes_refl] at h
      exact h.trans (Category.id_comp _)
    have hcomp : RingHom.ker (((j ≫ qW).stalkMap d).hom) =
        actualWholeSheafStalkIdeal (vanishingIdeal (n := n) D) d.val :=
      (congrArg (fun f => RingHom.ker f.hom) hsquare).trans
        (actualSubspaceInclusion_stalk_kernel D d)
    simpa only [LocallyRingedSpace.stalkMap_comp, CommRingCat.hom_comp] using hcomp
  have hsurj : Function.Surjective (qW.stalkMap w).hom :=
    actualSubspaceInclusionRingedHom_stalk_surjective W w
  calc
    RingHom.ker (j.stalkMap d).hom =
        Ideal.map (qW.stalkMap w).hom
          (Ideal.comap (qW.stalkMap w).hom
            (RingHom.ker (j.stalkMap d).hom)) :=
      (Ideal.map_comap_of_surjective _ hsurj _).symm
    _ = Ideal.map (qW.stalkMap w).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) D) d.val) :=
      congrArg (Ideal.map (qW.stalkMap w).hom) hpre
    _ = _ := (intrinsicReducedCentreStalkInclusion_range_model hDW w).symm

/-- The specified native quotient by the precise original intrinsic image
ideal is the SAME closed-subspace stalk, through the actual inclusion map. -/
def containedInclusionStalkQuotientEquiv (d : D) :
    ((ofClosedAnalytic W hW).obj.left.presheaf.stalk
      ((inclusion hD hW hDW).hom.left.base d)).carrier ⧸
        intrinsicCentreStalkRange (ofClosedAnalytic W hW).obj.left
          ((Subtype.val : W → M) ⁻¹' D) ((inclusion hD hW hDW).hom.left.base d) ≃+*
      ((ofClosedAnalytic D hD).obj.left.presheaf.stalk d).carrier := by
  let i := inclusion hD hW hDW
  have hsurj : Function.Surjective (i.hom.left.stalkMap d).hom := by
    have hcomp : Function.Surjective
        ((i.hom.left ≫ actualSubspaceInclusion (n := n) W).stalkMap d) := by
      change Function.Surjective
        (((inclusion hD hW hDW).hom.left ≫ actualSubspaceInclusion (n := n) W).stalkMap d)
      rw [inclusion_ambient hD hW hDW]
      exact actualSubspaceInclusionRingedHom_stalk_surjective D d
    rw [LocallyRingedSpace.stalkMap_comp] at hcomp
    intro t
    obtain ⟨r, hr⟩ := hcomp t
    exact ⟨(actualSubspaceInclusion (n := n) W).stalkMap (i.hom.left.base d) r, hr⟩
  exact (Ideal.quotEquivOfEq
    (contained_inclusion_stalk_kernel_eq_intrinsicCentreStalkRange hD hW hDW d).symm).trans
      (((i.hom.left.stalkMap d).hom).quotientKerEquivOfSurjective hsurj)

/-- Every original germ class maps to its SAME actual inclusion-stalk image. -/
theorem containedInclusionStalkQuotientEquiv_apply_mk (d : D)
    (r : ((ofClosedAnalytic W hW).obj.left.presheaf.stalk
      ((inclusion hD hW hDW).hom.left.base d)).carrier) :
    containedInclusionStalkQuotientEquiv hD hW hDW d (Ideal.Quotient.mk _ r) =
      (inclusion hD hW hDW).hom.left.stalkMap d r := by
  simp only [containedInclusionStalkQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

end

end Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspaceStalkQuotient
