import Hironaka.Resolution.HironakaReducedComplexAnalyticMorphismCharts
import Hironaka.Resolution.HironakaResolutionSpaceComplex

/-!
# Holomorphy of the original point map of an intrinsic complex morphism

No native comparison map or holomorphy certificate is supplied. The original
over-complex-point locally ringed morphism itself gives a holomorphic ambient
point map from a native manifold, by genuine target charts and intrinsic
local holomorphic lifting. Faithfulness recovers the whole original sheaf map.

Blueprint: `hironaka-embedded-native-morphism.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaEmbeddedNativeMorphism

noncomputable section

open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspaceIntrinsicLifting HironakaActualAnalyticSubspaceLocalFunctions
  HironakaActualAnalyticSubspaceManifoldCharts HironakaResolutionSpaceComplex
  HironakaReducedComplexAnalyticMorphismCharts

variable {n m : ℕ} {X N : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace N] [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

/-- The ORIGINAL point map of an over-complex-point intrinsic morphism out of
the whole native source model is holomorphic into the literal target ambient. -/
theorem contMDiff_original_pointMap {D : Set N}
    (F : actualSubspaceLocallyRingedSpace (n := n) (univ : Set X) ⟶
      actualSubspaceLocallyRingedSpace (n := m) D)
    (hF : F ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) (univ : Set X)) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞
      (fun x : X => (F.base ⟨x, mem_univ x⟩).val) := by
  intro x
  let a : (univ : Set X) := ⟨x, mem_univ x⟩
  let y : N := (F.base a).val
  let j := chartModelMap (n := m) D y
  let Z := Over.mk (subspacePointMap (n := m) D)
  obtain ⟨T, hxT, H, hHp, hfac⟩ :=
    exists_actual_model_chart_factor Z F hF j (chartModelMap_point (n := m) D y) a
      (mem_range_chartModelMap (n := m) D (F.base a).property)
  let aT : ((Subtype.val : T → X) ⁻¹' (univ : Set X)) := ⟨⟨x, hxT⟩, mem_univ x⟩
  obtain ⟨O, hxO, f, hf, hD, hfH⟩ :=
    exists_actualSubspaceMap_local_holomorphic_lift H hHp aT
  let g : O → N := fun z => ((chartDiffeo (n := m) y).symm (f z)).val
  have hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ g :=
    contMDiff_subtype_val.comp ((chartDiffeo (n := m) y).symm.contMDiff.comp hf)
  have hpoint (z : O) : g z = (F.base ⟨z.val.val, mem_univ z.val.val⟩).val := by
    let zO : ((Subtype.val : O → T) ⁻¹' ((Subtype.val : T → X) ⁻¹' (univ : Set X))) :=
      ⟨z, mem_univ z.val.val⟩
    have h₀ := congrArg (fun k => k.base zO) hfH
    have h₁ := congrArg (fun k => (k.base ((actualOpenSubspaceMap
      (n := n) ((Subtype.val : T → X) ⁻¹' (univ : Set X)) O).base zO)).val) hfac
    calc
      g z = (j.base ((actualSubspaceMap hf hD).base zO)).val := rfl
      _ = (j.base (H.base ((actualOpenSubspaceMap (n := n)
          ((Subtype.val : T → X) ⁻¹' (univ : Set X)) O).base zO))).val :=
        congrArg (fun q => (j.base q).val) h₀
      _ = (F.base ⟨z.val.val, mem_univ z.val.val⟩).val := h₁
  have heq : g = fun z : O => (F.base ⟨z.val.val, mem_univ z.val.val⟩).val :=
    funext hpoint
  rw [heq] at hg
  have ht : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞
      (fun z : T => (F.base ⟨z.val, mem_univ z.val⟩).val) ⟨x, hxT⟩ :=
    (contMDiffAt_subtype_iff
      (f := fun z : T => (F.base ⟨z.val, mem_univ z.val⟩).val)).mp
        (hg (⟨⟨x, hxT⟩, hxO⟩ : O))
  exact (contMDiffAt_subtype_iff
    (f := fun z : X => (F.base ⟨z, mem_univ z⟩).val)).mp ht

/-- The recovered holomorphic map induces the ENTIRE original intrinsic
morphism, including its actual quotient structure-sheaf map. -/
theorem original_morphism_eq_actualSubspaceMap {D : Set N}
    (F : actualSubspaceLocallyRingedSpace (n := n) (univ : Set X) ⟶
      actualSubspaceLocallyRingedSpace (n := m) D)
    (hF : F ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) (univ : Set X)) :
    actualSubspaceMap (contMDiff_original_pointMap F hF)
      (fun x (_hx : x ∈ (univ : Set X)) => (F.base ⟨x, mem_univ x⟩).property) = F := by
  apply actualSubspaceMap_eq_of_base_eq _ F
    (actualSubspaceMap_point _ _) hF
  ext x
  rfl

/-- A morphism out of the ACTUAL native locally ringed manifold internally
has the original ambient holomorphic point map. -/
theorem contMDiff_native_source_pointMap {D : Set N}
    (F : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) X ⟶
      actualSubspaceLocallyRingedSpace (n := m) D)
    (hF : F ≫ subspacePointMap (n := m) D = ambientPointMap n X) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞
      (fun x : X => (F.base x).val) := by
  let Q := actualSubspaceUnivIso (n := n) (M := X)
  have hpoint : (Q.hom ≫ F) ≫ subspacePointMap (n := m) D =
      subspacePointMap (n := n) (univ : Set X) := by
    rw [Category.assoc, hF]
    rfl
  exact contMDiff_original_pointMap (Q.hom ≫ F) hpoint

private theorem univIso_inv_base_val (y : N) :
    ((actualSubspaceUnivIso (n := m) (M := N)).inv.base y).val = y := by
  have h := congrArg (fun k => k.base y)
    (actualSubspaceUnivIso (n := m) (M := N)).inv_hom_id
  exact h

/-- Every over-complex-point intrinsic morphism of genuine native manifolds
has its original holomorphic underlying point map. -/
theorem contMDiff_native_morphism
    (F : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) X ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel m) N)
    (hF : F ≫ ambientPointMap m N = ambientPointMap n X) :
    ContMDiff (M := X) (M' := N) 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞
      (fun x : X => (F.base x : N)) := by
  let Q := actualSubspaceUnivIso (n := m) (M := N)
  have hpoint : (F ≫ Q.inv) ≫ subspacePointMap (n := m) (univ : Set N) =
      ambientPointMap n X := by
    rw [Category.assoc, actualSubspaceUnivIso_inv_point]
    exact hF
  have h := contMDiff_native_source_pointMap (F ≫ Q.inv) hpoint
  have heq : (fun x : X => ((F ≫ Q.inv).base x).val) =
      (fun x : X => (F.base x : N)) := by
    funext x
    exact univIso_inv_base_val (N := N) (F.base x)
  rwa [heq] at h

section Isomorphism

variable {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- A GIVEN intrinsic isomorphism over the complex point constructs a native
biholomorphism with the very same original forward and inverse point maps. -/
def nativeDiffeomorph
    (E : actualSubspaceLocallyRingedSpace (n := n) (univ : Set X) ≅
      actualSubspaceLocallyRingedSpace (n := n) (univ : Set Y))
    (hE : E.hom ≫ subspacePointMap (n := n) (univ : Set Y) =
      subspacePointMap (n := n) (univ : Set X)) :
    X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y := by
  have hEinv : E.inv ≫ subspacePointMap (n := n) (univ : Set X) =
      subspacePointMap (n := n) (univ : Set Y) := by
    rw [← hE, ← Category.assoc, E.inv_hom_id, Category.id_comp]
  exact
    { toFun := fun x => (E.hom.base ⟨x, mem_univ x⟩).val
      invFun := fun y => (E.inv.base ⟨y, mem_univ y⟩).val
      left_inv := fun x => congrArg Subtype.val
        (congrArg (fun k => k.base ⟨x, mem_univ x⟩) E.hom_inv_id)
      right_inv := fun y => congrArg Subtype.val
        (congrArg (fun k => k.base ⟨y, mem_univ y⟩) E.inv_hom_id)
      contMDiff_toFun := contMDiff_original_pointMap E.hom hE
      contMDiff_invFun := contMDiff_original_pointMap E.inv hEinv }

theorem nativeDiffeomorph_apply
    (E : actualSubspaceLocallyRingedSpace (n := n) (univ : Set X) ≅
      actualSubspaceLocallyRingedSpace (n := n) (univ : Set Y))
    (hE : E.hom ≫ subspacePointMap (n := n) (univ : Set Y) =
      subspacePointMap (n := n) (univ : Set X)) (x : X) :
    nativeDiffeomorph E hE x = (E.hom.base ⟨x, mem_univ x⟩).val := rfl

theorem nativeDiffeomorph_symm_apply
    (E : actualSubspaceLocallyRingedSpace (n := n) (univ : Set X) ≅
      actualSubspaceLocallyRingedSpace (n := n) (univ : Set Y))
    (hE : E.hom ≫ subspacePointMap (n := n) (univ : Set Y) =
      subspacePointMap (n := n) (univ : Set X)) (y : Y) :
    (nativeDiffeomorph E hE).symm y = (E.inv.base ⟨y, mem_univ y⟩).val := rfl

end Isomorphism

end

end Hironaka.HironakaEmbeddedNativeMorphism
