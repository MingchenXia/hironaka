import Hironaka.Analytic.Unibranch.Resolution
import Hironaka.Analytic.Unibranch.SourceMorphismExt
import Hironaka.Resolution.HironakaEmbeddedNativeMorphism
import Hironaka.Analytic.AnalyticModificationLocalDiscrepancy

/-!
# The same native whole-model modification in the ORIGINAL category

Actual native good-open inverse data produces the FULL original isomorphism
over its literal good set. No original proper-bimeromorphic certificate is
assumed. Blueprint FIRST: `original-native-modification.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalNativeModification

open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaResolutionSpaceComplex AnalyticModificationLocalDiscrepancy
  SourceReducedComplexSpace

noncomputable section

section NativeMaps

variable {n m : ℕ} {M N : Type}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace N] [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

/-- The SAME original reduced quotient whole model, including its sheaf. -/
def wholeModel (M : Type) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] : SourceReducedComplexSpace :=
  ofClosedAnalytic (n := n) (univ : Set M) (isComplexAnalyticSubset_univ (n := n))

theorem isSmooth_wholeModel : (wholeModel (n := n) M).IsSmooth :=
  isSmooth_ofClosedAnalytic_of_isClosedSubmanifold
    ⟨isClosed_univ, fun x _ => ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩

/-- Actual holomorphy induces the genuine entire original whole-model map. -/
def nativeMorphism {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f) :
    wholeModel (n := n) M ⟶ wholeModel (n := m) N :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap hf (fun y (_ : y ∈ (univ : Set M)) => mem_univ (f y)))
    (actualSubspaceMap_point hf (fun y (_ : y ∈ (univ : Set M)) => mem_univ (f y))))

-- The existing open-subtype interior formula, with zero separate credit.
private theorem thin_preimage_univ {P : Type} [TopologicalSpace P] {A : Set P}
    (hA : interior A = ∅) :
    interior ((Subtype.val : ↥(univ : Set P) → P) ⁻¹' A) = ∅ := by
  have hi := isOpen_univ.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
    (continuous_subtype_val : Continuous (Subtype.val : ↥(univ : Set P) → P)) A
  exact hi.symm.trans (by rw [hA, preimage_empty])

end NativeMaps

section Modification

variable {n : ℕ} {M N : Type}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace N] [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]

/-- A genuine native modification internally satisfies the ORIGINAL
proper-bimeromorphic predicate for its SAME full original morphism. -/
theorem nativeMorphism_isProperBimeromorphic {f : M → N}
    (hf : IsAnalyticModification (n := n) f) :
    IsProperBimeromorphic (nativeMorphism hf.1) := by
  obtain ⟨hhol, hproper, A, B, s, hAc, hAa, hAt, hBc, hBa, hBt, hpre, hs, hfs, hsf⟩ := hf
  let U : Opens M := ⟨Aᶜ, hAc.isOpen_compl⟩
  let V : Opens N := ⟨Bᶜ, hBc.isOpen_compl⟩
  have hfU (y : U) : f y.val ∈ V := by
    intro hy
    apply y.property
    exact hpre ▸ hy
  have hsV (x : V) : s x.val ∈ U := by
    change s x.val ∉ A
    rw [← hpre]
    change f (s x.val) ∉ B
    rw [hfs x.val x.property]
    exact x.property
  have hsopen : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun x : V => s x.val) := by
    intro x
    exact (hs.contMDiffAt (hBc.isOpen_compl.mem_nhds x.property)).comp x
      (contMDiff_subtype_val x)
  let e : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V :=
    { toFun := fun y => ⟨f y.val, hfU y⟩
      invFun := fun x => ⟨s x.val, hsV x⟩
      left_inv := fun y => Subtype.ext (hsf y.val y.property)
      right_inv := fun x => Subtype.ext (hfs x.val x.property)
      contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk
        (hhol.comp contMDiff_subtype_val) hfU
      contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk hsopen hsV }
  let E := actualSubspaceBiholomorphicIso e (univ : Set U) (univ : Set V)
    (fun _ => Iff.rfl)
  let J := actualOpenSubspaceMap (n := n) (univ : Set M) U
  let K := actualOpenSubspaceMap (n := n) (univ : Set N) V
  have hJ : LocallyRingedSpace.IsOpenImmersion J :=
    actualOpenSubspaceMap_isOpenImmersion (n := n) (univ : Set M) U
  have hK : LocallyRingedSpace.IsOpenImmersion K :=
    actualOpenSubspaceMap_isOpenImmersion (n := n) (univ : Set N) V
  have hfacCat : nativeMorphism (M := U) (N := M) contMDiff_subtype_val ≫ nativeMorphism hhol =
      nativeMorphism e.contMDiff ≫ nativeMorphism (M := V) (N := N) contMDiff_subtype_val :=
    SourceReducedComplexSpace.morphism_eq_of_pointwise_eq _ _ (fun _ => rfl)
  have hfac : J ≫ (nativeMorphism hhol).hom.left = E.hom ≫ K :=
    congrArg (fun H : wholeModel (n := n) U ⟶ wholeModel (n := n) N => H.hom.left) hfacCat
  let T : Set (wholeModel (n := n) N).obj.left :=
    (Subtype.val : ↥(univ : Set N) → N) ⁻¹' B
  have hiso : IsIsoOver (nativeMorphism hhol) Tᶜ := by
    refine ⟨_, J, hJ, ?_, ?_, ?_⟩
    · exact (range_actualOpenSubspaceMap (n := n) (univ : Set M) U).trans (by
        ext y
        change (y.val ∉ A) ↔ f y.val ∉ B
        rw [← hpre]
        rfl)
    · have hcomp : LocallyRingedSpace.IsOpenImmersion (E.hom ≫ K) := by
        exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ E.hom (inferInstance) K hK
      exact hfac.symm ▸ hcomp
    · exact (congrArg (fun H : actualSubspaceLocallyRingedSpace (n := n)
          (univ : Set U) ⟶ (wholeModel (n := n) N).obj.left => range H.base) hfac).trans
        ((range_iso_hom_comp_base E K).trans
          ((range_actualOpenSubspaceMap (n := n) (univ : Set N) V).trans (by rfl)))
  refine ⟨?_, T, isAnalyticSubset_preimage_val (isComplexAnalyticSubset_univ (n := n)) hBa,
    thin_preimage_univ hBt, ?_, hiso⟩
  · exact (Homeomorph.Set.univ N).symm.isProperMap.comp
      (hproper.comp (Homeomorph.Set.univ M).isProperMap)
  · have hset : (nativeMorphism hhol).hom.left.base ⁻¹' T =
        (Subtype.val : ↥(univ : Set M) → M) ⁻¹' A := by
      ext y
      change f y.val ∈ B ↔ y.val ∈ A
      exact Set.ext_iff.mp hpre y.val
    exact (congrArg interior hset).trans (thin_preimage_univ hAt)

end Modification

end

end Hironaka.Analytic.Unibranch.OriginalNativeModification
