/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3C)
-/
import DeJongAlterations.StableModification.Projectivity.RelativeOnto
import DeJongAlterations.StableModification.Projectivity.SectionsMapGenerated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Lifting and generation around a fibre (`lem:sm-ltg-onto`, `lem:sm-ltg-generated`)

Blueprint `sm-projectivity-relative.tex`, `lem:sm-ltg-onto` and `lem:sm-ltg-generated`, in the
pointwise form requested by PLAN-T5 §7 (T5G's Lemma 5.1(ii)). Let `β : X ⟶ Y` and let
`D : TwoAffineCover β L` be an affine open `W ⊆ Y` with a cover `β⁻¹ W = U₀ ∪ U₁` by two affine
opens with affine intersection such that the cokernels of the difference maps
`Γ(U₀, 𝓛^m) × Γ(U₁, 𝓛^m) → Γ(U₀ ∩ U₁, 𝓛^m)` are finite `Γ(Y, W)`-modules (this holds when `β⁻¹ W`
is projective over `W` and `Y` is Noetherian or of finite presentation over a valuation ring,
`RelativeCover.lean`). Let `y ∈ W` be a closed point such that `𝓛` is ample on the fibre `X_y`
(OM3A's `FiberAmple`, applied to `F = 𝒪`). Then:

* (`TwoAffineCover.exists_lift`) for `m ≫ 0`, every section of `𝓛^m` on `X_y` is the restriction
  of a section of `𝓛^m` over `β⁻¹ W`;
* (`TwoAffineCover.exists_generating`) for `m ≫ 0`, finitely many sections of `𝓛^m` over
  `β⁻¹ W` generate `𝓛^m` on `β⁻¹ O` for an open neighbourhood `O ⊆ W` of `y`.

We also record that `𝒪_X` is a sheaf of modules of finite type (`isFiniteType_unitModule`), to
apply the Serre-form fibre-ampleness to `F = 𝒪`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Cohomology

/-- The structure sheaf is a sheaf of modules of finite type (free of rank one). -/
instance isFiniteType_unitModule (X : Scheme.{u}) :
    SheafOfModules.IsFiniteType.{u, u, u} (unitModule X) := by
  let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} ≅
      SheafOfModules.unit X.ringCatSheaf :=
    Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
  have : (SheafOfModules.free.generatingSections (R := X.ringCatSheaf)
      PUnit.{u + 1}).IsFiniteType := ⟨(inferInstance : Finite PUnit.{u + 1})⟩
  let σ := (SheafOfModules.free.generatingSections (R := X.ringCatSheaf) PUnit.{u + 1}).ofEpi e.hom
  have hσ : σ.IsFiniteType := inferInstance
  constructor
  exact ⟨σ.localGeneratorsData, by
    constructor
    intro i
    exact ⟨(inferInstance : Finite PUnit.{u + 1})⟩⟩

variable {X Y : Scheme.{u}}

/-- **Two-affine data** for `β : X ⟶ Y` and `𝓛`: an affine open `W ⊆ Y`, affine opens `U₀`, `U₁`
of `X` with affine intersection covering `β⁻¹ W`, such that the cokernel of the difference map
`Γ(U₀, 𝓛^m) × Γ(U₁, 𝓛^m) → Γ(U₀ ∩ U₁, 𝓛^m)` is a finite `Γ(Y, W)`-module for every `m`. -/
structure TwoAffineCover (β : X ⟶ Y) (L : LineBundleData X) where
  /-- The affine open of the base. -/
  W : Y.Opens
  isAffineOpen_W : IsAffineOpen W
  /-- The first affine open of `β⁻¹ W`. -/
  U₀ : X.Opens
  /-- The second affine open of `β⁻¹ W`. -/
  U₁ : X.Opens
  isAffineOpen_U₀ : IsAffineOpen U₀
  isAffineOpen_U₁ : IsAffineOpen U₁
  isAffineOpen_inf : IsAffineOpen (U₀ ⊓ U₁)
  sup_eq : U₀ ⊔ U₁ = β ⁻¹ᵁ W
  finite_coker : ∀ m : ℤ, Module.Finite Γ(Y, W)
    (sectionsModuleCat (L.twist (unitModule X) m) (β.app W).hom (U₀ ⊓ U₁)
        (inf_le_left.trans (LineBundleData.le_of_sup_eq₀ β sup_eq)) ⧸
      LinearMap.range (pairDiffOn (L.twist (unitModule X) m) (β.app W).hom
        (LineBundleData.le_of_sup_eq₀ β sup_eq) (LineBundleData.le_of_sup_eq₁ β sup_eq)))

namespace TwoAffineCover

variable {β : X ⟶ Y} {L : LineBundleData X} (D : TwoAffineCover β L)

/-- **Lifting sections from a fibre** (blueprint `lem:sm-ltg-onto`, pointwise form): for a closed
point `y ∈ W` at which `𝓛` is fibre-ample and all `m ≫ 0`, every section of `𝓛^m` on the fibre
`X_y` is the restriction of a section of `𝓛^m` over `β⁻¹ W`. -/
theorem exists_lift {y : Y} (hy : y ∈ D.W) (hcl : IsClosed ({y} : Set Y))
    (hL : FiberAmple L β y) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ z : (L.pullback (β.fiberι y)).Sections m ⊤,
      ∃ τ : L.Sections m (β ⁻¹ᵁ D.W), τ.pullback (β.fiberι y) = z.restrict le_top := by
  obtain ⟨m₀, hm₀⟩ := hL (unitModule (β.fiber y))
  refine ⟨m₀, fun m hm z => ?_⟩
  have hH1 := (hm₀ m hm).1 (LineBundleData.fibrePairCover β y D.isAffineOpen_W hy
    D.isAffineOpen_U₀ D.isAffineOpen_U₁ D.isAffineOpen_inf D.sup_eq)
  exact L.exists_lift_of_twoAffines β y (m : ℤ) D.isAffineOpen_W hy hcl D.isAffineOpen_U₀
    D.isAffineOpen_U₁ D.isAffineOpen_inf D.sup_eq hH1 (D.finite_coker m) z

/-- **Generation around a fibre** (blueprint `lem:sm-ltg-generated`, pointwise form): for a closed
point `y ∈ W` at which `𝓛` is fibre-ample and all `m ≫ 0`, finitely many sections of `𝓛^m` over
`β⁻¹ W` do not vanish simultaneously at any point of `β⁻¹ O`, for an open neighbourhood `O ⊆ W`
of `y`. -/
theorem exists_generating [IsProper β] {y : Y} (hy : y ∈ D.W) (hcl : IsClosed ({y} : Set Y))
    (hL : FiberAmple L β y) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ (K : Finset X) (τ : X → L.Sections m (β ⁻¹ᵁ D.W))
      (O : Y.Opens), y ∈ O ∧ O ≤ D.W ∧ ∀ x : X, β x ∈ O → ∃ k ∈ K, x ∈ (τ k).nonvanishingLocus := by
  obtain ⟨m₁, hlift⟩ := D.exists_lift hy hcl hL
  obtain ⟨m₂, hm₂⟩ := hL (unitModule (β.fiber y))
  refine ⟨max m₁ m₂, fun m hm => ?_⟩
  have hgen := (hm₂ m (le_of_max_le_right hm)).2
  -- a lifted section through every point of the fibre
  have hx : ∀ x : X, β x = y → ∃ τ : L.Sections m (β ⁻¹ᵁ D.W), x ∈ τ.nonvanishingLocus := by
    intro x hxy
    obtain ⟨z, rfl⟩ : x ∈ Set.range (β.fiberι y) := by
      rw [Scheme.Hom.range_fiberι]
      exact hxy
    obtain ⟨s, hs⟩ := LineBundleData.exists_mem_nonvanishingLocus_of_isGloballyGenerated
      (L := L.pullback (β.fiberι y)) (m := (m : ℤ)) hgen z
    obtain ⟨τ, hτ⟩ := hlift m (le_of_max_le_left hm) s
    refine ⟨τ, ?_⟩
    have h := congrArg LineBundleData.Sections.nonvanishingLocus hτ
    rw [LineBundleData.Sections.nonvanishingLocus_pullback,
      LineBundleData.Sections.nonvanishingLocus_restrict] at h
    have hz : z ∈ β.fiberι y ⁻¹ᵁ τ.nonvanishingLocus := by
      rw [h]
      exact ⟨LineBundleData.top_le_fiber_preimage β y hy trivial, hs⟩
    exact hz
  classical
  choose! τ hτ using hx
  -- finitely many suffice, by compactness of the fibre
  have hcpt : IsCompact (β ⁻¹' {y}) := β.isProperMap.isCompact_preimage isCompact_singleton
  obtain ⟨K, hK⟩ := hcpt.elim_finite_subcover (fun x => ((τ x).nonvanishingLocus : Set X))
    (fun x => (τ x).nonvanishingLocus.isOpen) (fun x hx => Set.mem_iUnion.mpr ⟨x, hτ x hx⟩)
  -- the locus where the sections do not generate is closed, with closed image
  set G : X.Opens := ⨆ k ∈ K, (τ k).nonvanishingLocus with hG
  have hCcl : IsClosed (β '' (G : Set X)ᶜ) := β.isClosedMap _ G.isOpen.isClosed_compl
  let O : Y.Opens := D.W ⊓ ⟨(β '' (G : Set X)ᶜ)ᶜ, hCcl.isOpen_compl⟩
  refine ⟨K, τ, O, ⟨hy, ?_⟩, inf_le_left, fun x hxO => ?_⟩
  · rintro ⟨x, hxG, hxy⟩
    apply hxG
    have := hK (show x ∈ β ⁻¹' {y} from hxy)
    simp only [Set.mem_iUnion] at this
    obtain ⟨k, hk, hxk⟩ := this
    exact Opens.mem_iSup.mpr ⟨k, Opens.mem_iSup.mpr ⟨hk, hxk⟩⟩
  · have hxG : x ∈ G := by
      by_contra h
      exact hxO.2 ⟨x, h, rfl⟩
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp hxG
    obtain ⟨hkK, hxk⟩ := Opens.mem_iSup.mp hk
    exact ⟨k, hkK, hxk⟩

end TwoAffineCover

end

end DeJongAlterations.StableModification.Projectivity
