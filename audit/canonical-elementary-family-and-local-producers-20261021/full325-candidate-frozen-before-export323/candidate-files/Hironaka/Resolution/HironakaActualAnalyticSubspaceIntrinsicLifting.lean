/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticSubspaceLocalFunctions

/-!
# Genuine local ambient lifts of arbitrary intrinsic complex model morphisms

Finitely many target coordinate sections are pulled back through the actual
intrinsic locally ringed map and lifted to original ambient holomorphic
sections. Residue naturality derives literal coordinate values; the actual
whole-section faithfulness theorem upgrades the resulting base equality to
the entire quotient-sheaf morphism square. No ambient lift is supplied.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAnalyticSubspaceIntrinsicLifting
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualAnalyticSubspaceResidue HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspaceLocalFunctions
variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

set_option backward.isDefEq.respectTransparency.types false in
/-- An arbitrary intrinsic complex morphism pulls an original scalar function back to real local functions. -/
theorem actualSubspaceMap_local_scalar_lift {C : Set M} {D : Set N}
    (F : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (hF : F ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (a : actualComplexSection (n := m) (⊤ : Opens N)) (x : C) :
    ∃ (O : Opens M) (_hxO : x.val ∈ O) (t : actualComplexSection (n := n) O),
      ∀ (y : C) (hyO : y.val ∈ O), t ⟨y.val,hyO⟩ = a ⟨(F.base y).val,by trivial⟩ := by
  let K := F ≫ actualSubspaceInclusion (n := m) D
  let W := (Opens.map K.base).obj (⊤ : Opens N)
  let s := K.c.app (op (⊤ : Opens N)) a
  obtain ⟨O,hxO,t,hOW,ht⟩ := actualSubspaceSection_local_ambient C W s x (by trivial)
  refine ⟨O,hxO,t,?_⟩
  intro y hy
  let r := (actualComplexStructureSheaf (n := m) N).presheaf.germ ⊤ (F.base y).val (by trivial) a
  calc
    _ = actualSubspaceStalkEval (n := n) C y
        ((actualSubspaceInclusion (n := n) C).stalkMap y
          ((actualComplexStructureSheaf (n := n) M).presheaf.germ O y.val hy t)) :=
      (actualSubspaceStalkEval_inclusion_germ C O t y hy).symm
    _ = actualSubspaceStalkEval (n := n) C y
        ((actualSubspaceSheaf (n := n) C).presheaf.germ W y (hOW y hy) s) :=
      congrArg (actualSubspaceStalkEval (n := n) C y) (ht y hy).symm
    _ = actualSubspaceStalkEval (n := n) C y (K.stalkMap y r) :=
      congrArg (actualSubspaceStalkEval (n := n) C y)
        (LocallyRingedSpace.stalkMap_germ_apply K ⊤ y (by trivial) a).symm
    _ = actualSubspaceStalkEval (n := n) C y (F.stalkMap y
        ((actualSubspaceInclusion (n := m) D).stalkMap (F.base y) r)) := by
      exact congrArg (actualSubspaceStalkEval (n := n) C y)
        (ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp F
          (actualSubspaceInclusion (n := m) D) y) r)
    _ = actualSubspaceStalkEval (n := m) D (F.base y)
        ((actualSubspaceInclusion (n := m) D).stalkMap (F.base y) r) :=
      actualSubspaceMap_eval_of_point_compatible F hF y _
    _ = _ := actualSubspaceStalkEval_inclusion_germ D ⊤ a (F.base y) (by trivial)

/-- Original target coordinate sections, constructed from genuine continuous linear projections. -/
def actualCoordinateSection (V : Opens (ComplexModel m)) (i : Fin m) :
    actualComplexSection (n := m) (⊤ : Opens V) := by
  have h₀ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ℂ) ∞
      (fun z : ComplexModel m => z i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).contMDiff
  have h₁ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ℂ) ∞
      (fun z : V => z.val i) := h₀.comp contMDiff_subtype_val
  change C^∞⟮𝓘(ℂ,ComplexModel m), (⊤ : Opens V); 𝓘(ℂ,ℂ), ℂ⟯
  exact ⟨fun z => z.val.val i,h₁.comp contMDiff_subtype_val⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Every intrinsic complex model morphism has a genuine local holomorphic lift with the WHOLE LRS square. -/
theorem exists_actualSubspaceMap_local_holomorphic_lift {C : Set M}
    {V : Opens (ComplexModel m)} {D : Set V}
    (F : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (hF : F ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C) (x : C) :
    ∃ (O : Opens M) (_hxO : x.val ∈ O) (f : O → V)
      (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
      (hCD : ∀ y ∈ (Subtype.val : O → M) ⁻¹' C, f y ∈ D),
      actualSubspaceMap hf hCD = actualOpenSubspaceMap (n := n) C O ≫ F := by
  classical
  choose O hxO t ht using fun i : Fin m =>
    actualSubspaceMap_local_scalar_lift F hF (actualCoordinateSection V i) x
  let O₀ : Opens M := ⨅ i : Fin m, O i
  have hO₀ : ∀ i : Fin m, O₀ ≤ O i := fun i => iInf_le O i
  have hxO₀ : x.val ∈ O₀ := by
    change x.val ∈ (O₀ : Set M)
    simp only [O₀,Opens.coe_iInf,Set.mem_iInter]
    exact hxO
  let g : M → ComplexModel m := fun z =>
    (EuclideanSpace.equiv (Fin m) ℂ).symm (fun i => sectionExtension (O i) (t i) z)
  have hg : ∀ z ∈ O₀, ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ g z := by
    intro z hz
    have hpi : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,Fin m → ℂ) ∞
        (fun w => fun i : Fin m => sectionExtension (O i) (t i) w) z :=
      contMDiffAt_pi_space.mpr fun i => sectionExtension_contMDiffAt (O i) (t i) z (hO₀ i hz)
    exact (EuclideanSpace.equiv (Fin m) ℂ).symm.toContinuousLinearMap.contMDiffAt.comp z hpi
  have hgC : ∀ (y : C), y.val ∈ O₀ → g y.val = (F.base y).val.val := by
    intro y hy
    ext i
    change sectionExtension (O i) (t i) y.val = (F.base y).val.val i
    rw [sectionExtension_apply (O i) (t i) y.val (hO₀ i hy)]
    exact ht i y (hO₀ i hy)
  have hxV : g x.val ∈ V := by
    rw [hgC x hxO₀]
    exact (F.base x).val.property
  have hnb : g ⁻¹' (V : Set (ComplexModel m)) ∈ nhds x.val :=
    (hg x.val hxO₀).continuousAt.preimage_mem_nhds (V.isOpen.mem_nhds hxV)
  obtain ⟨T,hTsub,hT,hxT⟩ := mem_nhds_iff.mp hnb
  let O' : Opens M := O₀ ⊓ ⟨T,hT⟩
  let f : O' → V := fun y => ⟨g y.val,hTsub y.property.2⟩
  have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff V f).mp
    intro y
    exact contMDiffAt_subtype_iff.mpr (hg y.val y.property.1)
  have hCD : ∀ y ∈ (Subtype.val : O' → M) ⁻¹' C, f y ∈ D := by
    intro y hy
    have he : f y = (F.base (⟨y.val,hy⟩ : C)).val :=
      Subtype.ext (hgC ⟨y.val,hy⟩ y.property.1)
    rw [he]
    exact (F.base (⟨y.val,hy⟩ : C)).property
  refine ⟨O',⟨hxO₀,hxT⟩,f,hf,hCD,?_⟩
  apply actualSubspaceMap_eq_of_base_eq _ _ (actualSubspaceMap_point hf hCD)
  · rw [Category.assoc,hF]
    exact actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)
  · ext y
    apply Subtype.ext
    apply Subtype.ext
    exact hgC ⟨y.val.val,y.property⟩ y.val.property.1

end
end Hironaka.HironakaActualAnalyticSubspaceIntrinsicLifting
