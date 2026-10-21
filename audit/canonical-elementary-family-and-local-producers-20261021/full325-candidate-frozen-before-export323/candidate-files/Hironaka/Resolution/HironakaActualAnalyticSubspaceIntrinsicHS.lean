/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticSubspaceResidue

/-!
# Actual intrinsic whole-stalk Hilbert–Samuel profiles

Original complex-point compatibility produces genuine scalar-preserving
whole stalk algebra maps. An arbitrary intrinsic model isomorphism, even
in different ambient dimensions, preserves every actual maximal-power
quotient and the existing original whole-ideal Hilbert–Samuel function.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAnalyticSubspaceIntrinsicHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceResidue
  HironakaReducedComplexAnalyticSpaces HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

/-- The original structural constants equip the ACTUAL colimit stalk with its complex algebra. -/
instance actualSubspaceStalkAlgebra (C : Set M) (x : C) :
    Algebra ℂ ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier :=
  (actualSubspaceStalkConst (n := n) C x).toAlgebra

local instance actualStalkLocal (C : Set M) (x : C) :
    IsLocalRing ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier :=
  actualSubspaceStalk_isLocalRing (n := n) C x

local instance chartQuotientLocal (C : Set M) (x : C) :
    IsLocalRing (HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal (vanishingIdeal (n := n) C)
      x.val x.val (mem_chart_source _ x.val)) := actualSubspaceChartQuotient_isLocalRing C x

/-- The entire independently constructed chart quotient retains the genuine structural complex algebra. -/
def actualSubspaceStalkChartAlgEquiv (C : Set M) (x : C) :
    ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier ≃ₐ[ℂ]
      HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal (vanishingIdeal (n := n) C)
        x.val x.val (mem_chart_source _ x.val) :=
  { actualSubspaceStalkChartEquiv (n := n) C x with
    commutes' _c := (actualSubspaceStalkChartEquiv (n := n) C x).apply_symm_apply _ }

private theorem point_base_apply (C : Set M) (x : C) :
    (subspacePointMap (n := n) C).base x = (0 : ComplexModel 0) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar preservation of the genuine whole stalk map is an OUTPUT of the original structural triangle. -/
theorem actualSubspaceStalkMap_const {C : Set M} {D : Set N}
    (F : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (hF : F ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (x : C) (c : ℂ) :
    F.stalkMap x (actualSubspaceStalkConst (n := m) D (F.base x) c) =
      actualSubspaceStalkConst (n := n) C x c := by
  have h := LocallyRingedSpace.stalkMap_congr_hom
    (F ≫ subspacePointMap (n := m) D) (subspacePointMap (n := n) C) hF x
  have hs : (subspacePointMap (n := m) D).stalkMap (F.base x) ≫ F.stalkMap x =
      (subspacePointMap (n := n) C).stalkMap x := by
    calc
      _ = (F ≫ subspacePointMap (n := m) D).stalkMap x :=
        (LocallyRingedSpace.stalkMap_comp F (subspacePointMap (n := m) D) x).symm
      _ = _ := by
        simpa only [LocallyRingedSpace.comp_base,TopCat.comp_app,point_base_apply,
          TopCat.Presheaf.stalkSpecializes_refl,Category.id_comp] using h
  have hc := ConcreteCategory.congr_hom hs (actualComplexPointStalkEquiv.symm c)
  simp only [ConcreteCategory.comp_apply] at hc
  calc
    _ = F.stalkMap x ((subspacePointMap (n := m) D).stalkMap (F.base x)
        (actualComplexPointStalkEquiv.symm c)) :=
      congrArg (F.stalkMap x) (actualSubspacePointMap_stalk_const D (F.base x) c).symm
    _ = (subspacePointMap (n := n) C).stalkMap x (actualComplexPointStalkEquiv.symm c) := hc
    _ = _ := actualSubspacePointMap_stalk_const C x c

/-- Any original intrinsic complex morphism induces the genuine scalar-preserving WHOLE stalk map. -/
def actualSubspaceStalkMapAlgHom {C : Set M} {D : Set N}
    (F : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (hF : F ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C) (x : C) :
    ((actualSubspaceSheaf (n := m) D).presheaf.stalk (F.base x)).carrier →ₐ[ℂ]
      ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier :=
  { (F.stalkMap x).hom with commutes' c := actualSubspaceStalkMap_const F hF x c }

/-- An original intrinsic model isomorphism, in arbitrary dimensions, gives its ACTUAL whole-stalk algebra equivalence. -/
def actualSubspaceIsoStalkAlgEquiv {C : Set M} {D : Set N}
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D)
    (he : e.hom ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C) (x : C) :
    ((actualSubspaceSheaf (n := m) D).presheaf.stalk (e.hom.base x)).carrier ≃ₐ[ℂ]
      ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier :=
  { (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv with
    commutes' c := actualSubspaceStalkMap_const e.hom he x c }

/-- The actual intrinsic maximal-power quotient of the genuine colimit local ring. -/
abbrev actualSubspaceStalkJet (C : Set M) (x : C) (q : ℕ) :=
  ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier ⧸
    IsLocalRing.maximalIdeal ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier ^ q

/-- The genuine intrinsic profile uses true powers of the actual local-ring maximal ideal. -/
def actualSubspaceStalkHS (C : Set M) (x : C) (ℓ : ℕ) : ℕ :=
  Module.finrank ℂ (actualSubspaceStalkJet (n := n) C x (ℓ+1))

private def maximalJetAlgEquiv {R S : Type} [CommRing R] [CommRing S]
    [Algebra ℂ R] [Algebra ℂ S] [IsLocalRing R] [IsLocalRing S]
    (E : R ≃ₐ[ℂ] S) (q : ℕ) :
    (R ⧸ (IsLocalRing.maximalIdeal R ^ q)) ≃ₐ[ℂ] (S ⧸ (IsLocalRing.maximalIdeal S ^ q)) :=
  Ideal.quotientEquivAlg _ _ E (by
    rw [Ideal.map_pow,IsLocalRing.map_maximalIdeal_of_surjective (E : R →+* S) E.surjective])

/-- Every actual maximal-power quotient is preserved by the SAME original intrinsic stalk map. -/
def actualSubspaceIsoJetAlgEquiv {C : Set M} {D : Set N}
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D)
    (he : e.hom ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C) (x : C) (q : ℕ) :
    actualSubspaceStalkJet (n := m) D (e.hom.base x) q ≃ₐ[ℂ] actualSubspaceStalkJet (n := n) C x q :=
  maximalJetAlgEquiv (actualSubspaceIsoStalkAlgEquiv e he x) q

/-- EVERY original numerator is the class of the original actual stalk pullback. -/
theorem actualSubspaceIsoJetAlgEquiv_mk {C : Set M} {D : Set N}
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D)
    (he : e.hom ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C) (x : C) (q : ℕ)
    (r : ((actualSubspaceSheaf (n := m) D).presheaf.stalk (e.hom.base x)).carrier) :
    actualSubspaceIsoJetAlgEquiv e he x q (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (e.hom.stalkMap x r) := rfl

/-- The ACTUAL intrinsic maximal-power quotient equals the entire original ambient chart quotient. -/
def actualSubspaceStalkJetChartAlgEquiv (C : Set M) (x : C) (q : ℕ) :
    actualSubspaceStalkJet (n := n) C x q ≃ₐ[ℂ]
      HolGerm (ComplexModel n) ⧸
        (wholeChartStalkIdeal (vanishingIdeal (n := n) C) x.val x.val (mem_chart_source _ x.val) ⊔
          IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q) := by
  let I := wholeChartStalkIdeal (vanishingIdeal (n := n) C)
    x.val x.val (mem_chart_source _ x.val)
  let E := actualSubspaceStalkChartAlgEquiv (n := n) C x
  have hm : Ideal.map (Ideal.Quotient.mk I)
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q) =
      Ideal.map E.toRingEquiv.toRingHom
        (IsLocalRing.maximalIdeal ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier ^ q) := by
    rw [Ideal.map_pow,Ideal.map_pow,
      IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      IsLocalRing.map_maximalIdeal_of_surjective E.toRingEquiv.toRingHom E.surjective]
  exact (Ideal.quotientEquivAlg _ _ E hm).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ ℂ I
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q))

/-- Every genuine actual local maximal-power quotient is finite dimensional, without coherence assumptions. -/
theorem actualSubspaceStalkJet_finiteDimensional (C : Set M) (x : C) (q : ℕ) :
    FiniteDimensional ℂ (actualSubspaceStalkJet (n := n) C x q) := by
  let I := wholeChartStalkIdeal (vanishingIdeal (n := n) C)
    x.val x.val (mem_chart_source _ x.val)
  let := finiteDimensional_quotient_sup_maximalIdeal_pow n q I
  exact FiniteDimensional.of_injective
    (actualSubspaceStalkJetChartAlgEquiv (n := n) C x q).toLinearMap
    (actualSubspaceStalkJetChartAlgEquiv (n := n) C x q).injective

/-- The existing original WHOLE-ideal Hilbert–Samuel function equals the genuine intrinsic stalk profile. -/
theorem actualSubspaceStalkHS_eq_original (C : Set M) (x : C) (ℓ : ℕ) :
    actualSubspaceStalkHS (n := n) C x ℓ = hilbertSamuelAt (vanishingIdeal (n := n) C) x.val ℓ :=
  (actualSubspaceStalkJetChartAlgEquiv (n := n) C x (ℓ+1)).toLinearEquiv.finrank_eq

/-- ANY original intrinsic complex-point-compatible model isomorphism preserves the EXISTING entire HS profile. -/
theorem hilbertSamuelAt_vanishing_intrinsic_iso {C : Set M} {D : Set N}
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D)
    (he : e.hom ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C) (x : C) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) C) x.val ℓ =
      hilbertSamuelAt (vanishingIdeal (n := m) D) (e.hom.base x).val ℓ := by
  rw [← actualSubspaceStalkHS_eq_original C x ℓ,
    ← actualSubspaceStalkHS_eq_original D (e.hom.base x) ℓ]
  exact (actualSubspaceIsoJetAlgEquiv e he x (ℓ+1)).toLinearEquiv.finrank_eq.symm

end
end Hironaka.HironakaActualAnalyticSubspaceIntrinsicHS
