import Hironaka.Analytic.Unibranch.ComplexSpaceLocalEmbedding
import Hironaka.Resolution.HironakaActualAnalyticSubspaceIntrinsicHS
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-! Original structural scalars and whole Hilbert--Samuel profiles in EVERY
actual local embedding. BP FIRST: original-local-embedding-stalk-hs.tex.
The original stalk is the native sheaf colimit, its scalars come only from
the given structural map, and the existing embedded-model action is retained.
No global Algebra instance, initial phase, successor or resolver is added. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalLocalEmbeddingStalkHS
noncomputable section
open Hironaka
  Hironaka.HolomorphicIdealSheaves
  Hironaka
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceResidue HironakaActualAnalyticSubspaceIntrinsicHS
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetRankLoci

private def pointStalkEquiv (q : complexPoint) :
    (complexPoint.presheaf.stalk q).carrier ≃+* ℂ := by
  have h : q = (0 : ComplexModel 0) := Subsingleton.elim (α := ComplexModel 0) _ _
  subst q
  exact actualComplexPointStalkEquiv

private theorem pointStalkEquiv_specializes (q t : complexPoint) (h : q=t) (z : ℂ) :
    complexPoint.presheaf.stalkSpecializes (specializes_of_eq h)
      ((pointStalkEquiv t).symm z) = (pointStalkEquiv q).symm z := by
  subst t
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- Fixed native constants from the ORIGINAL structural map, before any chart. -/
def originalStalkConst (X : SourceReducedComplexSpace) (p : X.obj.left) :
    ℂ →+* (X.obj.left.presheaf.stalk p).carrier :=
  ((X.obj.hom.stalkMap p).hom).comp
    (pointStalkEquiv (X.obj.hom.base p)).symm.toRingHom

/-- Named native factory, installed ONLY locally; no global competing action. -/
@[instance_reducible]
def originalStalkAlgebra (X : SourceReducedComplexSpace) (p : X.obj.left) :
    Algebra ℂ (X.obj.left.presheaf.stalk p).carrier :=
  (originalStalkConst X p).toAlgebra

attribute [local instance] originalStalkAlgebra

variable (X : SourceReducedComplexSpace) (e : LocalEmbedding X)

private instance modelLocal (c : e.carrier) :
    IsLocalRing ((actualSubspaceSheaf (n := e.dim) e.carrier).presheaf.stalk c).carrier :=
  actualSubspaceStalk_isLocalRing (n := e.dim) e.carrier c

/-- The FULL complex-point triangle derives scalar preservation of the SAME map. -/
theorem localEmbedding_stalkMap_const (c : e.carrier) (z : ℂ) :
    e.map.stalkMap c (originalStalkConst X (e.toPoint c) z) =
      actualSubspaceStalkConst (n := e.dim) e.carrier c z := by
  let j : actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier ⟶ X.obj.left := e.map
  let a := subspacePointMap (n := e.dim) e.carrier
  have hja : j ≫ X.obj.hom=a := e.overPoint
  have hq : a.base c=X.obj.hom.base (j.base c) :=
    (congrArg (fun H => H.base c) hja).symm
  have hs := LocallyRingedSpace.stalkMap_congr_hom (j ≫ X.obj.hom) a hja c
  have hcomp := (LocallyRingedSpace.stalkMap_comp j X.obj.hom c).symm.trans hs
  have hv := ConcreteCategory.congr_hom hcomp
    ((pointStalkEquiv (X.obj.hom.base (e.toPoint c))).symm z)
  change j.stalkMap c (X.obj.hom.stalkMap (j.base c)
      ((pointStalkEquiv (X.obj.hom.base (j.base c))).symm z)) =
    a.stalkMap c (complexPoint.presheaf.stalkSpecializes (specializes_of_eq hq)
      ((pointStalkEquiv (X.obj.hom.base (j.base c))).symm z)) at hv
  have ht := pointStalkEquiv_specializes (a.base c) (X.obj.hom.base (j.base c)) hq z
  exact hv.trans ((congrArg (fun r => a.stalkMap c r) ht).trans
    (actualSubspacePointMap_stalk_const (n := e.dim) e.carrier c z))

/-- The underlying ring equivalence is LITERALLY the original OI stalk map. -/
def localEmbeddingStalkAlgEquiv (c : e.carrier) :
    (X.obj.left.presheaf.stalk (e.toPoint c)).carrier ≃ₐ[ℂ]
      ((actualSubspaceSheaf (n := e.dim) e.carrier).presheaf.stalk c).carrier := by
  let j : actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier ⟶ X.obj.left := e.map
  letI : LocallyRingedSpace.IsOpenImmersion j := e.isOpenImmersion
  letI : IsIso (j.stalkMap c) := LocallyRingedSpace.IsOpenImmersion.stalk_iso j c
  exact { (asIso (j.stalkMap c)).commRingCatIsoToRingEquiv with
    commutes' z := localEmbedding_stalkMap_const X e c z }

theorem localEmbeddingStalkAlgEquiv_apply (c : e.carrier)
    (r : (X.obj.left.presheaf.stalk (e.toPoint c)).carrier) :
    localEmbeddingStalkAlgEquiv X e c r = e.map.stalkMap c r := rfl

/-- The ORIGINAL stalk and the same ENTIRE old preferred-chart quotient. -/
def localEmbeddingStalkChartAlgEquiv (c : e.carrier) :
    (X.obj.left.presheaf.stalk (e.toPoint c)).carrier ≃ₐ[ℂ]
      HolGerm (ComplexModel e.dim) ⧸ wholeChartStalkIdeal
        (vanishingIdeal (n := e.dim) e.carrier) c.val c.val (mem_chart_source _ c.val) :=
  (localEmbeddingStalkAlgEquiv X e c).trans
    (actualSubspaceStalkChartAlgEquiv (n := e.dim) e.carrier c)

/-- Actual ambient quotient followed by the inverse native OI stalk map.
This is a stalk map at c; no global ambient-to-X map is asserted. -/
def ambientToOriginalStalk (c : e.carrier) :
    actualComplexStructureStalk (n := e.dim) c.val →+*
      (X.obj.left.presheaf.stalk (e.toPoint c)).carrier :=
  (localEmbeddingStalkAlgEquiv X e c).symm.toRingHom.comp
    ((actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap c).hom

/-- EVERY original ambient numerator retains the literal quotient class. -/
theorem localEmbeddingStalkChartAlgEquiv_ambient (c : e.carrier)
    (r : actualComplexStructureStalk (n := e.dim) c.val) :
    localEmbeddingStalkChartAlgEquiv X e c (ambientToOriginalStalk X e c r) =
      Ideal.Quotient.mk (wholeChartStalkIdeal (vanishingIdeal (n := e.dim) e.carrier)
        c.val c.val (mem_chart_source _ c.val)) (actualStalkChartEquiv (n := e.dim) c.val r) := by
  change actualSubspaceStalkChartEquiv (n := e.dim) e.carrier c
    (localEmbeddingStalkAlgEquiv X e c
      ((localEmbeddingStalkAlgEquiv X e c).symm
        ((actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap c r))) = _
  rw [AlgEquiv.apply_symm_apply]
  change Ideal.quotientEquiv _ _ (actualStalkChartEquiv (n := e.dim) c.val)
    (map_actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim) e.carrier) c.val).symm
    (actualSubspaceStalkWholeEquiv (n := e.dim) e.carrier c
      ((actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap c r)) = _
  rw [actualSubspaceInclusion_stalk]
  rfl

/-- The kernel remains precisely the ENTIRE original ambient defining ideal. -/
theorem ambientToOriginalStalk_kernel (c : e.carrier) :
    RingHom.ker (ambientToOriginalStalk X e c) =
      actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim) e.carrier) c.val := by
  have hk : RingHom.ker (ambientToOriginalStalk X e c) =
      RingHom.ker ((actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap c).hom := by
    ext r
    change (localEmbeddingStalkAlgEquiv X e c).symm
      ((actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap c r) = 0 ↔ _
    constructor
    · intro h
      apply (localEmbeddingStalkAlgEquiv X e c).symm.injective
      exact h.trans (localEmbeddingStalkAlgEquiv X e c).symm.map_zero.symm
    · intro h
      change (actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap c r=0 at h
      rw [h,map_zero]
  exact hk.trans (actualSubspaceInclusion_stalk_kernel (n := e.dim) e.carrier c)

/-- The TRUE original local-ring maximal-power quotient, including q=0. -/
abbrev originalStalkJet (p : X.obj.left) (q : ℕ) :=
  (X.obj.left.presheaf.stalk p).carrier ⧸
    IsLocalRing.maximalIdeal (X.obj.left.presheaf.stalk p).carrier ^ q

/-- Genuine intrinsic HS: the ORIGINAL quotient and its fixed structural scalars. -/
def originalStalkHS (p : X.obj.left) (ℓ : ℕ) : ℕ :=
  Module.finrank ℂ (originalStalkJet X p (ℓ+1))

/-- ALL powers use the SAME original native stalk map, not a selected jet proxy. -/
def localEmbeddingJetAlgEquiv (c : e.carrier) (q : ℕ) :
    originalStalkJet X (e.toPoint c) q ≃ₐ[ℂ]
      actualSubspaceStalkJet (n := e.dim) e.carrier c q := by
  let E := localEmbeddingStalkAlgEquiv X e c
  have hm : Ideal.map E.toRingEquiv.toRingHom
      (IsLocalRing.maximalIdeal (X.obj.left.presheaf.stalk (e.toPoint c)).carrier ^ q) =
        IsLocalRing.maximalIdeal ((actualSubspaceSheaf (n := e.dim) e.carrier).presheaf.stalk c).carrier ^ q := by
    rw [Ideal.map_pow,IsLocalRing.map_maximalIdeal_of_surjective
      E.toRingEquiv.toRingHom E.surjective]
  exact Ideal.quotientEquivAlg _ _ E hm.symm

/-- Every original class maps to its SAME actual inclusion-stalk numerator. -/
theorem localEmbeddingJetAlgEquiv_mk (c : e.carrier) (q : ℕ)
    (r : (X.obj.left.presheaf.stalk (e.toPoint c)).carrier) :
    localEmbeddingJetAlgEquiv X e c q (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal ((actualSubspaceSheaf (n := e.dim) e.carrier).presheaf.stalk c).carrier ^ q)
        (e.map.stalkMap c r) := rfl

theorem originalStalkJet_finiteDimensional (c : e.carrier) (q : ℕ) :
    FiniteDimensional ℂ (originalStalkJet X (e.toPoint c) q) := by
  let := actualSubspaceStalkJet_finiteDimensional (n := e.dim) e.carrier c q
  exact FiniteDimensional.of_injective (localEmbeddingJetAlgEquiv X e c q).toLinearMap
    (localEmbeddingJetAlgEquiv X e c q).injective

/-- EVERY point/order in EVERY original embedding has the existing whole HS. -/
theorem originalStalkHS_localEmbedding_eq (c : e.carrier) (ℓ : ℕ) :
    originalStalkHS X (e.toPoint c) ℓ =
      hilbertSamuelAt (vanishingIdeal (n := e.dim) e.carrier) c.val ℓ :=
  (localEmbeddingJetAlgEquiv X e c (ℓ+1)).toLinearEquiv.finrank_eq.trans
    (actualSubspaceStalkHS_eq_original (n := e.dim) e.carrier c ℓ)

end
end Hironaka.Analytic.Unibranch.OriginalLocalEmbeddingStalkHS
