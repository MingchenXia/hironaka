/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3C)
-/
import DeJongAlterations.StableModification.Projectivity.RelativeFibre

/-!
# Finiteness and torsion of sections of `𝓛^m`; pullback along open immersions

Blueprint `sm-projectivity-relative.tex`, `lem:sm-ltg-twist-finite`. For line-bundle data `L` on a
scheme `Z`:

* `LineBundleData.finite_twist_sections`: on an affine open `U`, the sections of `𝓛^m` form a
  finite `Γ(Z, U)`-module (locally on `U` they are the functions on basic opens inside charts);
* `LineBundleData.Sections.eq_zero_of_smul_eq_zero`: a function which is a non-zero-divisor on the
  functions on every open is a non-zero-divisor on the sections of `𝓛^m`;
* `LineBundleData.bijective_pullback_of_isOpenImmersion`: along an open immersion `f`, pullback of
  sections of `𝓛^m` over opens inside the image is bijective.

These are the coherence inputs (`hF`, `htf`) of the finiteness theorems for the cohomology of
projective schemes (`Cohomology.finite_cohomology_of_isProjectiveOver`,
`Cohomology.ProjectiveCoordinates.finitePresentation_cechCohomology_fp`), applied to `𝓛^m` on the
projective pieces `β⁻¹ W` in the local-to-global theorem (Temkin, *Stable modification of relative
curves*, Thm 1.1).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LineBundleData

variable {Z : Scheme.{u}} (L : LineBundleData Z) (m : ℤ)

/-- **Finiteness of sections of `𝓛^m` on affine opens** (blueprint `lem:sm-ltg-twist-finite`). -/
theorem finite_twist_sections {U : Z.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(Z, U) Γ(L.twist (unitModule Z) m, U) := by
  let S := L.chartBasicSet U
  let M := Cohomology.sectionsModuleCat (L.twist (unitModule Z) m) (RingHom.id Γ(Z, U)) U le_rfl
  have : ∀ g : S, IsLocalizedModule.Away g.1
      (Cohomology.sectionsRestrict (L.twist (unitModule Z) m) (RingHom.id Γ(Z, U)) le_rfl
        (Z.basicOpen_le g.1) (Z.basicOpen_le g.1)).hom :=
    fun g => L.isLocalizedModule_restrict_basicOpen m hU g.1
  have : ∀ g : S, IsLocalization.Away g.1 Γ(Z, Z.basicOpen g.1) :=
    fun g => hU.isLocalization_basicOpen g.1
  let : ∀ g : S, Module Γ(Z, Z.basicOpen g.1)
      (Cohomology.sectionsModuleCat (L.twist (unitModule Z) m) (RingHom.id Γ(Z, U))
        (Z.basicOpen g.1) (Z.basicOpen_le g.1)) :=
    fun g => inferInstanceAs (Module Γ(Z, Z.basicOpen g.1) (L.Sections m (Z.basicOpen g.1)))
  have hst : ∀ g : S, IsScalarTower Γ(Z, U) Γ(Z, Z.basicOpen g.1)
      (Cohomology.sectionsModuleCat (L.twist (unitModule Z) m) (RingHom.id Γ(Z, U))
        (Z.basicOpen g.1) (Z.basicOpen_le g.1)) := by
    intro g
    refine ⟨fun c r x => ?_⟩
    change (res (Z.basicOpen_le g.1) c * r) • (show L.Sections m (Z.basicOpen g.1) from x) =
      res (Z.basicOpen_le g.1) c • (r • (show L.Sections m (Z.basicOpen g.1) from x))
    rw [mul_smul]
  have hfinM : Module.Finite Γ(Z, U) M := by
    refine Module.Finite.of_localizationSpan' S (L.span_chartBasicSet hU)
      (Rₚ := fun g : S => Γ(Z, Z.basicOpen g.1))
      (fun g => (Cohomology.sectionsRestrict (L.twist (unitModule Z) m) (RingHom.id Γ(Z, U)) le_rfl
        (Z.basicOpen_le g.1) (Z.basicOpen_le g.1)).hom) (fun g => ?_)
    obtain ⟨i, hi⟩ := g.2
    have : Module.Finite Γ(Z, Z.basicOpen g.1) Γ(unitModule Z, Z.basicOpen g.1) :=
      Module.Finite.self _
    exact Module.Finite.equiv (localEquiv (unitModule Z) m (L := L) hi).symm
  -- the module structure of `M` agrees with the native one
  let e : M ≃ₗ[Γ(Z, U)] Γ(L.twist (unitModule Z) m, U) :=
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        change res le_rfl c • (show L.Sections m U from x) = c • (show L.Sections m U from x)
        rw [res_self]
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Finite.equiv e

/-- **No torsion**: a function which is a non-zero-divisor on the functions on every open is a
non-zero-divisor on the sections of `𝓛^m` (blueprint `lem:sm-ltg-twist-finite`). -/
theorem Sections.eq_zero_of_smul_eq_zero {W : Z.Opens} (a : Γ(Z, W))
    (ha : ∀ (V : Z.Opens) (hV : V ≤ W) (f : Γ(Z, V)), res hV a * f = 0 → f = 0)
    (s : L.Sections m W) (hs : a • s = 0) : s = 0 := by
  ext i
  have h := congrArg (fun t : L.Sections m W => t.coeff i) hs
  simp only [Sections.coeff_smul] at h
  exact ha _ inf_le_left _ h

/-- **Pullback of sections along an open immersion is bijective** over opens inside the image. -/
theorem bijective_pullback_of_isOpenImmersion {Z' : Scheme.{u}} (f : Z' ⟶ Z) [IsOpenImmersion f]
    {V : Z.Opens} (hV : V ≤ f.opensRange) :
    Function.Bijective (fun s : L.Sections m V => s.pullback f) := by
  have hiso : ∀ i, IsIso (f.app (V ⊓ L.U i)) := fun i => f.isIso_app _ (inf_le_left.trans hV)
  have hinj : ∀ i, Function.Injective (f.app (V ⊓ L.U i)) := fun i =>
    (ConcreteCategory.bijective_of_isIso (f.app (V ⊓ L.U i))).1
  have hinj' : ∀ i j, Function.Injective (f.app (V ⊓ (L.U i ⊓ L.U j))) := fun i j => by
    have := f.isIso_app (V ⊓ (L.U i ⊓ L.U j)) (inf_le_left.trans hV)
    exact (ConcreteCategory.bijective_of_isIso _).1
  refine ⟨fun s t hst => ?_, fun t => ?_⟩
  · ext i
    exact hinj i (congrArg (fun r : (L.pullback f).Sections m (f ⁻¹ᵁ V) => r.coeff i) hst)
  · let e : ∀ i, Γ(Z', f ⁻¹ᵁ (V ⊓ L.U i)) → Γ(Z, V ⊓ L.U i) := fun i => inv (f.app (V ⊓ L.U i))
    have he : ∀ i r, f.app (V ⊓ L.U i) (e i r) = r := fun i r => by
      change (inv (f.app (V ⊓ L.U i)) ≫ f.app (V ⊓ L.U i)) r = r
      rw [IsIso.inv_hom_id]
      rfl
    refine ⟨Sections.mk (fun i => e i (t.coeff i)) (fun i j => ?_), ?_⟩
    · apply hinj' i j
      rw [LineBundleData.app_res, he, map_mul, LineBundleData.app_res, he]
      have hc := t.coeff_compat i j
      refine hc.trans ?_
      congr 1
      exact L.pullback_trans_zpow m f (inf_le_right : V ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j)
    · ext i
      exact he i _

end LineBundleData

end

end DeJongAlterations.StableModification.Projectivity
