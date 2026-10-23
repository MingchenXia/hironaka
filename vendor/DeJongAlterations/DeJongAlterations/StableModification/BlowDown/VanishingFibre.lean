/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.StableComb
import DeJongAlterations.StableModification.BlowDown.VanishingNakayama
import DeJongAlterations.StableModification.Cohomology.BaseChange

/-!
# Functions on affine opens of the closed fibre (Temkin, Prop. 4.4.6, T:3214–3219)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Prop. 4.4.6: the lift of `h_s` from the closed fibre `Y_s` to `Y` (T:3214–3219). The input of the
Nakayama transfer `VanishingNakayama.subsingleton_H1_of_subsingleton` is the description of the
functions on the closed fibre over an affine open: for `q : Y → Spec V` with `V` local and an
affine open `W ⊆ Y`, restriction to the closed fibre `Γ(W, 𝒪_Y) → Γ(W_s, 𝒪_{Y_s})` is onto with
kernel `𝔪 Γ(W, 𝒪_Y)` (`fiberι_app_surjective`, `mem_smul_top_of_fiberι_app_eq_zero`), since
`Γ(W_s) = Γ(W) ⊗_V κ` (`Cohomology.isPushout_baseChange_sections`) and `V → κ` is onto with
kernel `𝔪`. The closed fibre is `q.fiber s₀`, identified with the residue-field fibre by
`BlowDown.residueFibreHom`.

Blueprint `sm-blow-down-contracting.tex`, `lem:sm-bdc-fibre-functions`.
-/

namespace DeJongAlterations.StableModification.BlowDown.VanishingFibre

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite IsLocalRing
open DeJongAlterations.StableModification.Cohomology
open ClosureComponent (residuePt)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

noncomputable section

variable {V : Type u} [CommRing V] [IsLocalRing V] {Y : Scheme.{u}}
  (q : Y ⟶ Spec (CommRingCat.of V))

local notation "s₀" => IsLocalRing.closedPoint V

instance isMaximal_closedPoint_asIdeal : (IsLocalRing.closedPoint V).asIdeal.IsMaximal :=
  IsLocalRing.maximalIdeal.isMaximal V

/-- On the residue-field fibre `pullback q (residuePt s₀)`, restriction of functions over an
affine open `W ⊆ Y` is onto with kernel `𝔪 Γ(W)`. -/
theorem residueFibre_app_surjective_ker {W : Y.Opens} (hW : IsAffineOpen W) :
    Function.Surjective ((pullback.fst q (residuePt s₀)).app W) ∧
      RingHom.ker ((pullback.fst q (residuePt s₀)).app W).hom =
        Ideal.map (sectionsRingHom (structureCoeff q) (le_top : W ≤ ⊤)) (maximalIdeal V) := by
  have H := isPushout_baseChange_sections (algebraMap V (s₀).asIdeal.ResidueField) q hW
  have hf : Function.Surjective
      (CommRingCat.ofHom (algebraMap V (s₀).asIdeal.ResidueField)) :=
    Ideal.algebraMap_residueField_surjective _
  obtain ⟨h1, h2⟩ := VanishingNakayama.surjective_and_ker_of_isPushout H hf
  rw [Scheme.Hom.appLE_eq_app] at h1 h2
  refine ⟨h1, ?_⟩
  rw [h2]
  have e1 : RingHom.ker (CommRingCat.ofHom (algebraMap V (s₀).asIdeal.ResidueField)).hom =
      maximalIdeal V :=
    Ideal.ker_algebraMap_residueField _
  rw [e1]
  rfl

lemma surjective_ker_of_eq {X : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (W : Y.Opens)
    (I : Ideal Γ(Y, W)) (hf : Function.Surjective (f.app W) ∧ RingHom.ker (f.app W).hom = I) :
    Function.Surjective (g.app W) ∧ RingHom.ker (g.app W).hom = I := by
  subst h
  exact hf

/-- **Functions on the closed fibre over an affine open**: restriction
`Γ(W, 𝒪_Y) → Γ(W_s, 𝒪_{Y_s})` is onto with kernel `𝔪 Γ(W)`. -/
theorem fiberι_app_surjective_ker {W : Y.Opens} (hW : IsAffineOpen W) :
    Function.Surjective ((q.fiberι s₀).app W) ∧
      RingHom.ker ((q.fiberι s₀).app W).hom =
        Ideal.map (sectionsRingHom (structureCoeff q) (le_top : W ≤ ⊤)) (maximalIdeal V) := by
  set F := residueFibreHom q s₀
  have hcomp := surjective_ker_of_eq (residueFibreHom_fiberι q s₀).symm W _
    (residueFibre_app_surjective_ker q hW)
  rw [Scheme.Hom.comp_app] at hcomp
  obtain ⟨hs, hk⟩ := hcomp
  have hbij : Function.Bijective (F.app ((q.fiberι s₀) ⁻¹ᵁ W)) :=
    ConcreteCategory.bijective_of_isIso _
  refine ⟨fun y => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hs (F.app ((q.fiberι s₀) ⁻¹ᵁ W) y)
    refine ⟨x, hbij.1 ?_⟩
    rw [← hx]
    rfl
  · rw [← hk]
    ext x
    simp only [RingHom.mem_ker]
    change _ ↔ F.app ((q.fiberι s₀) ⁻¹ᵁ W) ((q.fiberι s₀).app W x) = 0
    constructor
    · intro h
      rw [h, map_zero]
    · intro h
      apply hbij.1
      rw [h, map_zero]

theorem fiberι_app_surjective {W : Y.Opens} (hW : IsAffineOpen W) :
    Function.Surjective ((q.fiberι s₀).app W) :=
  (fiberι_app_surjective_ker q hW).1

/-- An element of the extension `𝔪 Γ(W)` lies in `𝔪 · Γ(W)` for the `V`-module structure of the
sections. -/
lemma mem_smul_top_of_mem_map {W : Y.Opens} (w : Γ(Y, W))
    (hw : w ∈ Ideal.map (sectionsRingHom (structureCoeff q) (le_top : W ≤ ⊤)) (maximalIdeal V)) :
    (show sectionsModuleCat (SheafOfModules.unit Y.ringCatSheaf) (structureCoeff q) W le_top
      from w) ∈ (maximalIdeal V) • (⊤ : Submodule V
        (sectionsModuleCat (SheafOfModules.unit Y.ringCatSheaf) (structureCoeff q) W le_top)) := by
  set M := sectionsModuleCat (SheafOfModules.unit Y.ringCatSheaf) (structureCoeff q) W le_top
  set N : Submodule V M := (maximalIdeal V) • ⊤
  have hmul : ∀ (s : Γ(Y, W)) (x : M), x ∈ N → (show M from (s * (show Γ(Y, W) from x))) ∈ N := by
    intro s x hx
    refine Submodule.smul_induction_on (p := fun x : M =>
      (show M from (s * (show Γ(Y, W) from x))) ∈ N) hx ?_ ?_
    · intro r hr y _
      have e : (show M from (s * (show Γ(Y, W) from r • y))) =
          r • (show M from (s * (show Γ(Y, W) from y))) := by
        change s * (sectionsRingHom (structureCoeff q) (le_top : W ≤ ⊤) r * _) =
          sectionsRingHom (structureCoeff q) (le_top : W ≤ ⊤) r * (s * _)
        ring
      rw [e]
      exact Submodule.smul_mem_smul hr trivial
    · intro x y hx hy
      have e : (show M from (s * (show Γ(Y, W) from x + y))) =
          (show M from (s * (show Γ(Y, W) from x))) + (show M from (s * (show Γ(Y, W) from y))) :=
        @mul_add Γ(Y, W) _ _ _ s x y
      rw [e]
      exact N.add_mem hx hy
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    have e : (show M from sectionsRingHom (structureCoeff q) (le_top : W ≤ ⊤) r) =
        r • (show M from (1 : Γ(Y, W))) := by
      change _ = sectionsRingHom (structureCoeff q) (le_top : W ≤ ⊤) r * 1
      rw [mul_one]
    rw [e]
    exact Submodule.smul_mem_smul hr trivial
  | zero => exact N.zero_mem
  | add x y _ _ hx hy => exact N.add_mem hx hy
  | smul a x _ hx => exact hmul a x hx

/-- **The kernel of restriction to the closed fibre over an affine open lies in `𝔪 · Γ(W)`.** -/
theorem mem_smul_top_of_fiberι_app_eq_zero {W : Y.Opens} (hW : IsAffineOpen W) (w : Γ(Y, W))
    (hw : (q.fiberι s₀).app W w = 0) :
    (show sectionsModuleCat (SheafOfModules.unit Y.ringCatSheaf) (structureCoeff q) W le_top
      from w) ∈ (maximalIdeal V) • (⊤ : Submodule V
        (sectionsModuleCat (SheafOfModules.unit Y.ringCatSheaf) (structureCoeff q) W le_top)) := by
  apply mem_smul_top_of_mem_map q w
  rw [← (fiberι_app_surjective_ker q hW).2]
  exact hw

end

end DeJongAlterations.StableModification.BlowDown.VanishingFibre
