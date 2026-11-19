import Hironaka.Analytic.Unibranch.Resolution
import Hironaka.Resolution.HironakaEmbeddedNativeMorphism
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Intrinsic dimension of the original smooth local models

Two actual smooth open immersions over the complex point have the same
complex dimension at an actual common point. Thus the chosen dimension is
locally constant, and connected original smooth spaces admit uniform-dimension
local models. The original spaces, topology and whole LRS maps are retained.
Blueprint: `original-smooth-dimension.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalSmoothDimension

open Hironaka Hironaka
  HironakaReducedComplexAnalyticSpaces HironakaEmbeddedNativeMorphism
  SourceReducedComplexSpace

noncomputable section

private def isoOfRangeEq {A B T : LocallyRingedSpace} (f : A ⟶ T) (g : B ⟶ T)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (h : range f.base = range g.base) : A ≅ B where
  hom := LocallyRingedSpace.IsOpenImmersion.lift g f (le_of_eq h)
  inv := LocallyRingedSpace.IsOpenImmersion.lift f g (le_of_eq h.symm)
  hom_inv_id := by
    apply (cancel_mono f).mp
    simp only [Category.assoc, LocallyRingedSpace.IsOpenImmersion.lift_fac,
      Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono g).mp
    simp only [Category.assoc, LocallyRingedSpace.IsOpenImmersion.lift_fac,
      Category.id_comp]

private theorem nativeMap_point {n m : ℕ} {M N : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    {f : M → N} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f) :
    ChartedSpace.locallyRingedSpaceMap f hf ≫ ambientPointMap m N = ambientPointMap n M :=
  (ChartedSpace.locallyRingedSpace_comp (IM := 𝓘(ℂ, ComplexModel n))
    (IN := 𝓘(ℂ, ComplexModel m)) (IP := 𝓘(ℂ, ComplexModel 0)) hf
    (show ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel 0) ∞
      (fun _ : N => (0 : ComplexModel 0)) from contMDiff_const)).symm

/-- An actual native over-complex-point isomorphism and an actual source point
produce equality of model dimensions by its complex derivative equivalence. -/
theorem native_iso_dimension_eq {n₀ n₁ : ℕ} {M₀ M₁ : Type}
    [TopologicalSpace M₀] [ChartedSpace (ComplexModel n₀) M₀] [IsComplexManifold n₀ M₀]
    [TopologicalSpace M₁] [ChartedSpace (ComplexModel n₁) M₁] [IsComplexManifold n₁ M₁]
    (e : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n₀) M₀ ≅
      ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n₁) M₁)
    (hep : e.hom ≫ ambientPointMap n₁ M₁ = ambientPointMap n₀ M₀) (x : M₀) :
    n₀ = n₁ := by
  have heip : e.inv ≫ ambientPointMap n₀ M₀ = ambientPointMap n₁ M₁ := by
    rw [← hep, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  let D : M₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n₀), 𝓘(ℂ, ComplexModel n₁)⟯ M₁ :=
    { toFun := e.hom.base
      invFun := e.inv.base
      left_inv := fun u => congrArg (fun k => k.base u) e.hom_inv_id
      right_inv := fun v => congrArg (fun k => k.base v) e.inv_hom_id
      contMDiff_toFun := contMDiff_native_morphism e.hom hep
      contMDiff_invFun := contMDiff_native_morphism e.inv heip }
  have hfin : Module.finrank ℂ (ComplexModel n₀) = Module.finrank ℂ (ComplexModel n₁) :=
    (D.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.finrank_eq
  simpa [ComplexModel] using hfin

variable {X : SourceReducedComplexSpace}

/-- Genuine smooth local models at the same original point have equal complex
model dimensions, derived from their actual whole over-complex-point maps. -/
theorem smooth_model_dimension_eq {n₀ n₁ : ℕ}
    (V₀ : Opens (ComplexModel n₀)) (V₁ : Opens (ComplexModel n₁))
    (i₀ : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n₀) V₀ ⟶ X.obj.left)
    (i₁ : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n₁) V₁ ⟶ X.obj.left)
    (hi₀ : LocallyRingedSpace.IsOpenImmersion i₀)
    (hi₁ : LocallyRingedSpace.IsOpenImmersion i₁)
    (hp₀ : i₀ ≫ X.obj.hom = ambientPointMap n₀ V₀)
    (hp₁ : i₁ ≫ X.obj.hom = ambientPointMap n₁ V₁)
    (x : X.obj.left) (hx₀ : x ∈ range i₀.base) (hx₁ : x ∈ range i₁.base) : n₀ = n₁ := by
  let := hi₀
  let := hi₁
  let O₀ : Opens V₀ := ⟨i₀.base ⁻¹' range i₁.base,
    hi₁.base_open.isOpen_range.preimage i₀.base.hom.continuous⟩
  let O₁ : Opens V₁ := ⟨i₁.base ⁻¹' range i₀.base,
    hi₀.base_open.isOpen_range.preimage i₁.base.hom.continuous⟩
  let j₀ := ChartedSpace.locallyRingedSpaceMap (Subtype.val : O₀ → V₀)
    (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel n₀)))
  let j₁ := ChartedSpace.locallyRingedSpaceMap (Subtype.val : O₁ → V₁)
    (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel n₁)))
  let f₀ := j₀ ≫ i₀
  let f₁ := j₁ ≫ i₁
  have hr : range f₀.base = range f₁.base := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨v, hv⟩ := u.property
      exact ⟨⟨v, ⟨u.val, hv.symm⟩⟩, hv⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨u, hu⟩ := v.property
      exact ⟨⟨u, ⟨v.val, hu.symm⟩⟩, hu⟩
  let e := isoOfRangeEq f₀ f₁ hr
  have he : e.hom ≫ f₁ = f₀ :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac f₁ f₀ (le_of_eq hr)
  have hf₀ : f₀ ≫ X.obj.hom = ambientPointMap n₀ O₀ := by
    rw [show f₀ = j₀ ≫ i₀ from rfl, Category.assoc, hp₀]
    exact nativeMap_point contMDiff_subtype_val
  have hf₁ : f₁ ≫ X.obj.hom = ambientPointMap n₁ O₁ := by
    rw [show f₁ = j₁ ≫ i₁ from rfl, Category.assoc, hp₁]
    exact nativeMap_point contMDiff_subtype_val
  have hep : e.hom ≫ ambientPointMap n₁ O₁ = ambientPointMap n₀ O₀ := by
    rw [← hf₁, ← Category.assoc, he, hf₀]
  obtain ⟨u, hu⟩ := hx₀
  have huO : u ∈ O₀ := by
    change i₀.base u ∈ range i₁.base
    rwa [hu]
  let a : O₀ := ⟨u, huO⟩
  exact native_iso_dimension_eq e hep a

/-- The original smoothness witnesses produce a locally constant dimension
function together with genuine full native local models in that dimension. -/
theorem exists_locallyConstant_smooth_dimension (h : X.IsSmooth) :
    ∃ d : X.obj.left → ℕ, IsLocallyConstant d ∧
      ∀ x : X.obj.left, ∃ (V : Opens (ComplexModel (d x)))
        (i : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel (d x)) V ⟶ X.obj.left),
        LocallyRingedSpace.IsOpenImmersion i ∧
        i ≫ X.obj.hom = ambientPointMap (d x) V ∧ x ∈ range i.base := by
  choose d V i hi hp hx using h
  refine ⟨d, ?_, fun x => ⟨V x, i x, hi x, hp x, hx x⟩⟩
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨range (i x).base, (hi x).base_open.isOpen_range, hx x, ?_⟩
  intro y hy
  exact smooth_model_dimension_eq (V y) (V x) (i y) (i x) (hi y) (hi x)
    (hp y) (hp x) y (hx y) hy

/-- Connected original smooth spaces have one dimension for all their genuine
native local smooth models. No global manifold or countability is supplied. -/
theorem exists_uniform_smooth_models [ConnectedSpace X.obj.left] (h : X.IsSmooth) :
    ∃ n : ℕ, ∀ x : X.obj.left, ∃ (V : Opens (ComplexModel n))
      (i : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) V ⟶ X.obj.left),
      LocallyRingedSpace.IsOpenImmersion i ∧
      i ≫ X.obj.hom = ambientPointMap n V ∧ x ∈ range i.base := by
  obtain ⟨d, hd, hm⟩ := exists_locallyConstant_smooth_dimension h
  obtain ⟨n, hn⟩ := hd.exists_eq_const
  refine ⟨n, fun x => ?_⟩
  have hx : d x = n := congrFun hn x
  subst n
  exact hm x

end

end Hironaka.Analytic.Unibranch.OriginalSmoothDimension
