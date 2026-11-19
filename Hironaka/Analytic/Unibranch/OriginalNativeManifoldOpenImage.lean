import Hironaka.Analytic.Unibranch.OriginalNativeSmoothOpenLocality
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalFinite
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! Genuine native manifold OIs give actual whole open-image biholomorphisms.
Blueprint first: `original-native-manifold-open-image.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeManifoldOpenImage
noncomputable section
open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaEmbeddedNativeMorphism
  HironakaReducedComplexAnalyticSpaces HironakaSmoothSubmersionOriginalGlobalFinite
  HironakaSmoothSubmersionOrderedGlobalTrace HironakaSmoothSubmersionComposition BlowupTowers
  SourceReducedComplexSpace OriginalNativeModification OriginalNativeSmoothOpenLocality

variable {m n : ℕ} {M N : Type}
  [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
  [TopologicalSpace N] [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]

def pointMap (F : wholeModel (n := m) M ⟶ wholeModel (n := n) N) : M → N :=
  fun x => (F.hom.left.base ⟨x,mem_univ x⟩).val

theorem pointMap_holomorphic (F : wholeModel (n := m) M ⟶ wholeModel (n := n) N) :
    ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (pointMap F) :=
  contMDiff_original_pointMap F.hom.left (Over.w F.hom)

theorem nativeMorphism_pointMap (F : wholeModel (n := m) M ⟶ wholeModel (n := n) N) :
    nativeMorphism (pointMap_holomorphic F) = F := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact original_morphism_eq_actualSubspaceMap F.hom.left (Over.w F.hom)

/-- An ordinary native OI internally constructs the actual whole ambient open-image biholomorphism. -/
theorem exists_open_image_diffeomorph (F : wholeModel (n := m) M ⟶ wholeModel (n := n) N)
    (hF : LocallyRingedSpace.IsOpenImmersion F.hom.left) :
    ∃ (R : Opens N) (D : M ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel n)⟯ R),
      ∀ x, (D x).val = pointMap F x := by
  have hrange : Set.range (pointMap F) =
      Set.image (fun y : ↥(Set.univ : Set N) => y.val)
        (Set.range (fun x : ↥(Set.univ : Set M) => F.hom.left.base x)) := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨F.hom.left.base ⟨x,mem_univ x⟩,⟨⟨x,mem_univ x⟩,rfl⟩,rfl⟩
    · rintro ⟨z,⟨x,hx⟩,rfl⟩
      exact ⟨x.val,congrArg Subtype.val hx⟩
  have hopen : IsOpen (range (pointMap F)) := by
    rw [hrange]
    exact isOpen_univ.isOpenMap_subtype_val _ hF.base_open.isOpen_range
  let R : Opens N := ⟨range (pointMap F),hopen⟩
  let j : wholeModel (n := n) R ⟶ wholeModel (n := n) N :=
    nativeMorphism (f := (Subtype.val : R → N)) contMDiff_subtype_val
  have hj : LocallyRingedSpace.IsOpenImmersion j.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (actualOpenSubspaceMap (n := n) (univ : Set N) R)
    exact actualOpenSubspaceMap_isOpenImmersion _ _
  have hR : range j.hom.left.base = range F.hom.left.base := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      obtain ⟨x,hx⟩ := z.val.property
      exact ⟨⟨x,mem_univ x⟩,Subtype.ext hx⟩
    · rintro ⟨x,rfl⟩
      exact ⟨⟨⟨(F.hom.left.base x).val,⟨x.val,rfl⟩⟩,mem_univ _⟩,rfl⟩
  obtain ⟨H,_hH,hH⟩ := exists_native_open_lift j F hj hF (le_of_eq hR.symm)
  obtain ⟨K,_hK,hK⟩ := exists_native_open_lift F j hF hj (le_of_eq hR)
  have hHK : H ≫ K = 𝟙 (wholeModel (n := m) M) := by
    let : LocallyRingedSpace.IsOpenImmersion F.hom.left := hF
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono F.hom.left).mp
    have htriangle : (H ≫ K) ≫ F = F :=
      (Category.assoc _ _ _).trans ((congrArg (fun a => H ≫ a) hK).trans hH)
    exact congrArg (fun a => a.hom.left) htriangle
  have hKH : K ≫ H = 𝟙 (wholeModel (n := n) R) := by
    let : LocallyRingedSpace.IsOpenImmersion j.hom.left := hj
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono j.hom.left).mp
    have htriangle : (K ≫ H) ≫ j = j :=
      (Category.assoc _ _ _).trans ((congrArg (fun a => K ≫ a) hH).trans hK)
    exact congrArg (fun a => a.hom.left) htriangle
  let I : wholeModel (n := m) M ≅ wholeModel (n := n) R := ⟨H,K,hHK,hKH⟩
  let D : M ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel n)⟯ R :=
    {toEquiv := ⟨pointMap I.hom,pointMap I.inv,
        fun x => congrArg Subtype.val (congrArg (fun a => a.hom.left.base ⟨x,mem_univ x⟩) I.hom_inv_id),
        fun y => congrArg Subtype.val (congrArg (fun a => a.hom.left.base ⟨y,mem_univ y⟩) I.inv_hom_id)⟩
     contMDiff_toFun := pointMap_holomorphic I.hom
     contMDiff_invFun := pointMap_holomorphic I.inv}
  exact ⟨R,D,fun x => congrArg (fun a => (a.hom.left.base ⟨x,mem_univ x⟩).val) hH⟩

theorem pointMap_isOpenEmbedding (F : wholeModel (n := m) M ⟶ wholeModel (n := n) N)
    (hF : LocallyRingedSpace.IsOpenImmersion F.hom.left) : Topology.IsOpenEmbedding (pointMap F) := by
  obtain ⟨R,D,hD⟩ := exists_open_image_diffeomorph F hF
  have hmap : (Subtype.val : R → N) ∘ D = pointMap F := funext hD
  exact hmap ▸ (R.isOpen.isOpenEmbedding_subtypeVal.comp D.toHomeomorph.isOpenEmbedding)

/-- Model dimensions are compared only at a genuine actual source point. -/
theorem open_dimension_eq (F : wholeModel (n := m) M ⟶ wholeModel (n := n) N)
    (hF : LocallyRingedSpace.IsOpenImmersion F.hom.left) (x : M) : m = n := by
  obtain ⟨R,D,_hD⟩ := exists_open_image_diffeomorph F hF
  have hfin : Module.finrank ℂ (ComplexModel m) = Module.finrank ℂ (ComplexModel n) :=
    (D.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.finrank_eq
  simpa [ComplexModel] using hfin

theorem open_pointMap_isSubmersion (F : wholeModel (n := m) M ⟶ wholeModel (n := n) N)
    (hF : LocallyRingedSpace.IsOpenImmersion F.hom.left) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (pointMap F) := by
  classical
  by_cases hM : Nonempty M
  · obtain ⟨x⟩ := hM
    have hdim := open_dimension_eq F hF x
    subst m
    obtain ⟨R,D,hD⟩ := exists_open_image_diffeomorph F hF
    have hsub := isSubmersion_composition
      (isSubmersion_val (A := CMfd.of (n := n) N) R)
      (isSubmersion_biholomorphism (D := CMfd.of (n := n) M) (C := CMfd.of (n := n) R) D)
    exact (funext hD) ▸ hsub
  · let : IsEmpty M := not_nonempty_iff.mp hM
    exact ⟨ComplexModel 0,inferInstance,inferInstance,fun x => isEmptyElim x⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeManifoldOpenImage
