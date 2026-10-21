/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticSubspaceResidue

/-!
# Local ambient functions and intrinsic morphism faithfulness

Actual quotient sections admit whole local ambient representatives. Genuine
point evaluations determine entire sections by the original vanishing ideal.
These facts yield faithfulness of scalar-compatible intrinsic model maps,
without an incoming ambient extension or structure-sheaf equality.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAnalyticSubspaceLocalFunctions
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceResidue HironakaReducedComplexAnalyticSpaces
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

/-- Every actual quotient section has an original ambient representative on a genuine neighbourhood. -/
theorem actualSubspaceSection_local_ambient (C : Set M) (W : Opens (TopCat.of C))
    (s : ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier)
    (x : C) (hx : x ∈ W) :
    ∃ (O : Opens M) (_hxO : x.val ∈ O) (t : actualComplexSection (n := n) O)
      (hOW : ∀ (y : C), y.val ∈ O → y ∈ W),
      ∀ (y : C) (hyO : y.val ∈ O),
        (actualSubspaceSheaf (n := n) C).presheaf.germ W y (hOW y hyO) s =
        (actualSubspaceInclusion (n := n) C).stalkMap y
          ((actualComplexStructureSheaf (n := n) M).presheaf.germ O y.val hyO t) := by
  let S := (actualSubspaceSheaf (n := n) C).presheaf
  let F := (actualComplexStructureSheaf (n := n) M).presheaf
  let I := actualSubspaceInclusion (n := n) C
  obtain ⟨r,hr⟩ := actualSubspaceInclusionRingedHom_stalk_surjective C x (S.germ W x hx s)
  obtain ⟨O₀,hxO₀,t₀,ht₀⟩ := F.exists_germ_eq r
  let V := (Opens.map I.base).obj O₀
  let a := I.toHom.c.app (op O₀) t₀
  have hxa : S.germ V x hxO₀ a = S.germ W x hx s := by
    calc
      _ = I.stalkMap x (F.germ O₀ x.val hxO₀ t₀) :=
        (LocallyRingedSpace.stalkMap_germ_apply I O₀ x hxO₀ t₀).symm
      _ = I.stalkMap x r := congrArg (I.stalkMap x) ht₀
      _ = _ := hr
  obtain ⟨Q,hxQ,iV,iW,ha⟩ := S.germ_eq x hxO₀ hx a s hxa
  obtain ⟨T,hT,hTQ⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp Q.isOpen
  let O : Opens M := ⟨T,hT⟩ ⊓ O₀
  have hQ : ∀ (y : C), y.val ∈ O → y ∈ Q := by
    intro y hy
    change y ∈ (Q : Set C)
    rw [← hTQ]
    exact hy.1
  have hOW : ∀ (y : C), y.val ∈ O → y ∈ W := fun y hy => (leOfHom iW) (hQ y hy)
  have hxO : x.val ∈ O := ⟨by change x ∈ Subtype.val ⁻¹' T; rw [hTQ]; exact hxQ,hxO₀⟩
  let t := F.map (homOfLE (show O ≤ O₀ from inf_le_right)).op t₀
  refine ⟨O,hxO,t,hOW,?_⟩
  intro y hy
  have hyQ := hQ y hy
  have he := congrArg (S.germ Q y hyQ) ha
  rw [S.germ_res_apply,S.germ_res_apply] at he
  calc
    _ = S.germ V y ((leOfHom iV) hyQ) a := he.symm
    _ = I.stalkMap y (F.germ O₀ y.val hy.2 t₀) :=
      (LocallyRingedSpace.stalkMap_germ_apply I O₀ y hy.2 t₀).symm
    _ = _ := congrArg (I.stalkMap y)
      (F.germ_res_apply (homOfLE (show O ≤ O₀ from inf_le_right)) y.val hy t₀).symm

/-- Original ambient section values are the actual quotient residue values of their whole germs. -/
theorem actualSubspaceStalkEval_inclusion_germ (C : Set M) (O : Opens M)
    (t : actualComplexSection (n := n) O) (y : C) (hy : y.val ∈ O) :
    actualSubspaceStalkEval (n := n) C y ((actualSubspaceInclusion (n := n) C).stalkMap y
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ O y.val hy t)) = t ⟨y.val,hy⟩ := by
  rw [actualSubspaceStalkEval_inclusion,actualStalkChartEquiv_germ]
  simpa [sectionChartRingHom,chartTranslatedGerm,translatedGerm,HolGerm.eval_mk,
    (chartAt (ComplexModel n) y.val).left_inv (mem_chart_source (ComplexModel n) y.val)] using
    sectionExtension_apply O t y.val hy

/-- Zero values on the whole actual open force a genuine entire quotient section to vanish. -/
theorem actualSubspaceSection_eq_zero_of_eval (C : Set M) (W : Opens (TopCat.of C))
    (s : ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier)
    (hs : ∀ (y : C) (hy : y ∈ W), actualSubspaceStalkEval (n := n) C y
      ((actualSubspaceSheaf (n := n) C).presheaf.germ W y hy s) = 0) : s = 0 := by
  let S := (actualSubspaceSheaf (n := n) C).presheaf
  apply TopCat.Presheaf.section_ext (actualSubspaceSheaf (n := n) C) W s 0
  intro x hx
  obtain ⟨O,hxO,t,hOW,ht⟩ := actualSubspaceSection_local_ambient C W s x hx
  have htI : t ∈ actualSectionIdeal (vanishingIdeal (n := n) C) O := by
    apply (actualSectionIdeal_vanishing_iff C O t).mpr
    intro y hy hyC
    let z : C := ⟨y,hyC⟩
    calc
      _ = actualSubspaceStalkEval (n := n) C z
          ((actualSubspaceInclusion (n := n) C).stalkMap z
            ((actualComplexStructureSheaf (n := n) M).presheaf.germ O y hy t)) :=
        (actualSubspaceStalkEval_inclusion_germ C O t z hy).symm
      _ = actualSubspaceStalkEval (n := n) C z (S.germ W z (hOW z hy) s) :=
        congrArg (actualSubspaceStalkEval (n := n) C z) (ht z hy).symm
      _ = 0 := hs z (hOW z hy)
  have hk : (actualComplexStructureSheaf (n := n) M).presheaf.germ O x.val hxO t ∈
      RingHom.ker ((actualSubspaceInclusion (n := n) C).stalkMap x).hom := by
    rw [actualSubspaceInclusion_stalk_kernel]
    exact htI x.val hxO
  calc
    _ = (actualSubspaceInclusion (n := n) C).stalkMap x
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ O x.val hxO t) := ht x hxO
    _ = 0 := hk
    _ = _ := (map_zero (S.germ W x hx).hom).symm

/-- Genuine point values determine the entire actual quotient-sheaf section. -/
theorem actualSubspaceSection_ext_eval (C : Set M) (W : Opens (TopCat.of C))
    (s t : ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier)
    (hst : ∀ (y : C) (hy : y ∈ W), actualSubspaceStalkEval (n := n) C y
        ((actualSubspaceSheaf (n := n) C).presheaf.germ W y hy s) =
      actualSubspaceStalkEval (n := n) C y
        ((actualSubspaceSheaf (n := n) C).presheaf.germ W y hy t)) : s = t := by
  apply sub_eq_zero.mp
  apply actualSubspaceSection_eq_zero_of_eval C W (s-t)
  intro y hy
  rw [map_sub,map_sub,hst y hy,sub_self]

set_option backward.isDefEq.respectTransparency.types false in
/-- Any two intrinsic scalar-compatible actual model maps with the same base map are equal. -/
theorem actualSubspaceMap_eq_of_base_eq {C : Set M} {D : Set N}
    (F G : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (hF : F ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (hG : G ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (hbase : F.base = G.base) : F = G := by
  rcases F with ⟨⟨f,fc⟩,hf⟩
  rcases G with ⟨⟨g,gc⟩,hg⟩
  change f = g at hbase
  subst g
  suffices hc : fc = gc by cases hc; rfl
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  ext s
  apply actualSubspaceSection_ext_eval C ((Opens.map f).obj U.unop)
  intro x hx
  let a := (actualSubspaceSheaf (n := m) D).presheaf.germ U.unop (f x) hx s
  let F : actualSubspaceLocallyRingedSpace (n := n) C ⟶
      actualSubspaceLocallyRingedSpace (n := m) D := ⟨⟨f,fc⟩,hf⟩
  let G : actualSubspaceLocallyRingedSpace (n := n) C ⟶
      actualSubspaceLocallyRingedSpace (n := m) D := ⟨⟨f,gc⟩,hg⟩
  calc
    _ = actualSubspaceStalkEval (n := n) C x (F.stalkMap x a) :=
      congrArg (actualSubspaceStalkEval (n := n) C x)
        (LocallyRingedSpace.stalkMap_germ_apply F U.unop x hx s).symm
    _ = actualSubspaceStalkEval (n := m) D (f x) a :=
      actualSubspaceMap_eval_of_point_compatible F hF x a
    _ = actualSubspaceStalkEval (n := n) C x (G.stalkMap x a) :=
      (actualSubspaceMap_eval_of_point_compatible G hG x a).symm
    _ = _ := congrArg (actualSubspaceStalkEval (n := n) C x)
      (LocallyRingedSpace.stalkMap_germ_apply G U.unop x hx s)

end
end Hironaka.HironakaActualAnalyticSubspaceLocalFunctions
