/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ClosureComponent
import DeJongAlterations.StableModification.Projectivity.LineBundle

/-!
# `H¹(Y ∖ D, 𝒪) = 0` from the exceptional component (Temkin, Prop. 4.4.6, T:3210–3214)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Prop. 4.4.6: "Note that `Y := C'_s = (∪ Zᵢ) ∪ Z`, `Z ≅ ℙ¹_{k(s)}` intersects `∪ Zᵢ` transversally
[…]. Using that `h¹(Z, 𝒪_Z) = 0` it follows easily that `H¹(𝒪_Y(m ∑ pᵢ)) = 0` for sufficiently
large `m`." This file proves the cohomological core of that step in a cover-level form: on a
reduced scheme `Y = A ∪ B` (affine opens) with an irreducible closed subset `Z = closure {ξ}`, if
every function on `Z ∩ A ∩ B` is a difference of functions on `Z ∩ B` and `Z ∩ A` (the vanishing of
`H¹(Z, 𝒪_Z)` on the cover `(Z ∩ A, Z ∩ B)`), then every function on `A ∩ B` is a difference of a
function on `A` and a function on the open `B' ⊆ B` obtained by removing the divisor `D`
(`exists_sub_eq_res`), provided `B' = (A ∩ B) ∪ N` for an open `N ⊆ Z`. In the application
`A = Y ∖ H` for a hyperplane `H` with `H ∩ Y' = D`, `Y'` the union of the other components, and
`N = B ∖ Y'`; the statement is `H¹(Y ∖ D, 𝒪) = 0` computed on the cover `(A, B')`, the limit
hypothesis of Serre's vanishing for the twists `𝒪(mD)` (`CurvesField.exists_forall_subsingleton_H1_of_limit`).

## The argument

Let `w ∈ Γ(A ∩ B)`. Its restriction to `Z` is `bbar - abar`; lift `abar`, `bbar` to `A`, `B` (closed subschemes
of affine schemes). Then `w' = w - (b - a)` vanishes on `Z ∩ A ∩ B`, hence on `N ∩ A ∩ B ⊆ Z` (a
function on a reduced scheme vanishing at every point is zero). So `w'` on `A ∩ B` and `0` on `N`
glue to a function on `B' = (A ∩ B) ∪ N`. This replaces Temkin's exact sequence
`0 → 𝒪_Z(-∂Z) → 𝒪_Y(m ∑ pᵢ) → 𝒪_{Y'}(m ∑ pᵢ) → 0` (blueprint `rem:sm-curves-cohomology-literature`,
literature issue T10) by the sequence through `𝒪_Z` itself: no transversality, no `Z ≅ ℙ¹`, and
no sheaf-level exact sequences are needed.

Blueprint `sm-blow-down-contracting.tex`, `lem:sm-bdc-core`.
-/

namespace DeJongAlterations.StableModification.BlowDown.VanishingCore

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open DeJongAlterations.StableModification.Projectivity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- **Binary gluing of functions.** Functions on two opens which agree on the overlap glue to a
function on any open they cover. -/
lemma exists_glue₂ {U₁ U₂ W : X.Opens} (h₁ : U₁ ≤ W) (h₂ : U₂ ≤ W) (hcov : W ≤ U₁ ⊔ U₂)
    (x : Γ(X, U₁)) (y : Γ(X, U₂))
    (hxy : res (inf_le_left : U₁ ⊓ U₂ ≤ U₁) x = res (inf_le_right : U₁ ⊓ U₂ ≤ U₂) y) :
    ∃ s : Γ(X, W), res h₁ s = x ∧ res h₂ s = y := by
  let V : ULift.{u} Bool → X.Opens := fun t => cond t.down U₁ U₂
  let sf : ∀ t : ULift.{u} Bool, Γ(X, V t) := fun t =>
    match t with
    | ⟨true⟩ => x
    | ⟨false⟩ => y
  have hyx : X.presheaf.map (homOfLE (inf_le_left : U₂ ⊓ U₁ ≤ U₂)).op y =
      X.presheaf.map (homOfLE (inf_le_right : U₂ ⊓ U₁ ≤ U₁)).op x := by
    have e := congrArg (X.presheaf.map (homOfLE (le_of_eq (inf_comm U₂ U₁))).op) hxy
    change X.presheaf.map _ (X.presheaf.map _ x) = X.presheaf.map _ (X.presheaf.map _ y) at e
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← X.presheaf.map_comp,
      ← X.presheaf.map_comp] at e
    exact e.symm
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 V sf := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩
    · rfl
    · exact hyx
    · exact hxy
    · rfl
  have hc : W ≤ iSup V := by
    refine hcov.trans (sup_le ?_ ?_)
    · exact le_iSup V ⟨true⟩
    · exact le_iSup V ⟨false⟩
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V W (fun t => match t with
    | ⟨true⟩ => homOfLE h₁
    | ⟨false⟩ => homOfLE h₂) hc sf hcompat
  exact ⟨s, hs ⟨true⟩, hs ⟨false⟩⟩

variable (ξ : X)


/-- On a reduced scheme, a function on an open contained in `closure {ξ}` which vanishes on the
reduced closure of `ξ` is zero. -/
lemma eq_zero_of_app_eq_zero [IsReduced X] {W : X.Opens} (hW : (W : Set X) ⊆ closure {ξ})
    (w : Γ(X, W)) (hw : (ClosureComponent.closureι ξ).app W w = 0) : w = 0 := by
  rw [← basicOpen_eq_bot_iff]
  have hpre : (ClosureComponent.closureι ξ) ⁻¹ᵁ X.basicOpen w = ⊥ := by
    rw [Scheme.preimage_basicOpen, hw, Scheme.basicOpen_zero]
  rw [eq_bot_iff]
  intro y hy
  have hyc : y ∈ closure {ξ} := hW (X.basicOpen_le w hy)
  rw [← ClosureComponent.range_closureι ξ] at hyc
  obtain ⟨z, rfl⟩ := hyc
  have : z ∈ (ClosureComponent.closureι ξ) ⁻¹ᵁ X.basicOpen w := hy
  rw [hpre] at this
  exact this

/-- `ιZ.app` commutes with restriction. -/
lemma app_res {W W' : X.Opens} (h : W' ≤ W) (w : Γ(X, W)) :
    (ClosureComponent.closureι ξ).app W' (res h w) =
      (ClosureComponent.closureScheme ξ).presheaf.map (homOfLE (fun _ hz => h hz : (ClosureComponent.closureι ξ) ⁻¹ᵁ W' ≤ (ClosureComponent.closureι ξ) ⁻¹ᵁ W)).op ((ClosureComponent.closureι ξ).app W w) := by
  change ((X.presheaf.map (homOfLE h).op) ≫ (ClosureComponent.closureι ξ).app W') w = _
  rw [Scheme.Hom.naturality]
  rfl

/-- **`H¹(Y ∖ D, 𝒪) = 0` from `H¹(Z, 𝒪_Z) = 0`** (the core of Temkin's vanishing, T:3210–3214).
Let `X` be reduced, `A`, `B` affine opens, `ξ ∈ X`, and `B' ⊆ B` an open with
`A ∩ B ⊆ B' ⊆ (A ∩ B) ∪ N` for an open `N ⊆ B'` contained in `closure {ξ}`. If every function on
`Z ∩ A ∩ B` is a difference of a function on `Z ∩ B` and one on `Z ∩ A` (`Z` the reduced closure of
`ξ`), then every function on `A ∩ B` is the difference of a function on `B'` and one on `A`. -/
theorem exists_sub_eq_res [IsReduced X] {A B B' N : X.Opens} (hA : IsAffineOpen A)
    (hB : IsAffineOpen B) (hB'B : B' ≤ B) (hAB' : A ⊓ B ≤ B') (hNB' : N ≤ B')
    (hcov : B' ≤ (A ⊓ B) ⊔ N) (hNξ : (N : Set X) ⊆ closure {ξ})
    (hZ : ∀ w : Γ(ClosureComponent.closureScheme ξ, (ClosureComponent.closureι ξ) ⁻¹ᵁ (A ⊓ B)), ∃ (a : Γ(ClosureComponent.closureScheme ξ, (ClosureComponent.closureι ξ) ⁻¹ᵁ A)) (b : Γ(ClosureComponent.closureScheme ξ, (ClosureComponent.closureι ξ) ⁻¹ᵁ B)),
      w = (ClosureComponent.closureScheme ξ).presheaf.map (homOfLE (fun _ hz => hz.2 : (ClosureComponent.closureι ξ) ⁻¹ᵁ (A ⊓ B) ≤ (ClosureComponent.closureι ξ) ⁻¹ᵁ B)).op b -
        (ClosureComponent.closureScheme ξ).presheaf.map (homOfLE (fun _ hz => hz.1 : (ClosureComponent.closureι ξ) ⁻¹ᵁ (A ⊓ B) ≤ (ClosureComponent.closureι ξ) ⁻¹ᵁ A)).op a)
    (w : Γ(X, A ⊓ B)) :
    ∃ (a : Γ(X, A)) (b : Γ(X, B')), w = res hAB' b - res (inf_le_left : A ⊓ B ≤ A) a := by
  obtain ⟨abar, bbar, hw⟩ := hZ ((ClosureComponent.closureι ξ).app (A ⊓ B) w)
  obtain ⟨a₁, ha₁⟩ := (ClosureComponent.closureι ξ).app_surjective A hA abar
  obtain ⟨b₁, hb₁⟩ := (ClosureComponent.closureι ξ).app_surjective B hB bbar
  set w' := w - (res (inf_le_right : A ⊓ B ≤ B) b₁ - res (inf_le_left : A ⊓ B ≤ A) a₁) with hw'
  have hw'Z : (ClosureComponent.closureι ξ).app (A ⊓ B) w' = 0 := by
    rw [hw', map_sub, map_sub, app_res, app_res, ha₁, hb₁, hw, sub_self]
  -- `w'` vanishes on `A ∩ B ∩ N`
  have hw'N : res (inf_le_left : (A ⊓ B) ⊓ N ≤ A ⊓ B) w' = 0 := by
    apply eq_zero_of_app_eq_zero ξ (W := A ⊓ B ⊓ N) (fun y hy => hNξ hy.2)
    rw [app_res, hw'Z, map_zero]
  -- glue `w'` and `0`
  obtain ⟨b₂, hb₂, -⟩ := exists_glue₂ hAB' hNB' hcov w' 0 (by rw [hw'N, map_zero])
  refine ⟨a₁, res hB'B b₁ + b₂, ?_⟩
  rw [map_add, hb₂, res_res _ _ (inf_le_right : A ⊓ B ≤ B)]
  rw [hw']
  ring

end

end DeJongAlterations.StableModification.BlowDown.VanishingCore
