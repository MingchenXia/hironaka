/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ClosureComponent
import DeJongAlterations.StableModification.CurvesField.OmegaDegree
import DeJongAlterations.StableModification.CurvesField.AmpleSection
import DeJongAlterations.StableModification.Cohomology.FiniteProjective

/-!
# `h¹(Z, 𝒪_Z) = 0` for a component of arithmetic genus `0` (Temkin, Prop. 4.4.6, T:3213)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Prop. 4.4.6: "Using that `h¹(Z, 𝒪_Z) = 0` it follows easily that `H¹(𝒪_Y(m ∑ pᵢ)) = 0`". For an
exceptional component `Z` Temkin knows `Z ≅ ℙ¹`; here only the arithmetic genus
`p_a(Z) = 1 - χ(Z, 𝒪_Z) = 0` is used (it is `g(Z) = 0` by lane T44E's `NodalComponentGenus`, since
`Z` has no double point of its own).

* `finrank_cohomology_zero_eq_one`: `h⁰(Z, 𝒪_Z) = 1` for `Z` integral and universally closed of
  finite type over an algebraically closed field (`Γ(Z, 𝒪_Z)` is a finite field extension).
* `isZero_cohomology_one_of_arithmeticGenus_eq_zero`: if `Z` is moreover projective and covered by
  two affine opens with affine intersection, `p_a(Z) = 0` gives `H¹(Z, 𝒪_Z) = 0`
  (`χ = h⁰ - h¹`, `CurvesField.DualityScheme.eulerCharOf_eq_of_pair`).
* `exists_sub_eq_closure`: the cover form on the reduced closure `Z = closure {ξ}` of a point of a
  projective curve `X` covered by two affine opens `A`, `B`: every function on `Z ∩ A ∩ B` is a
  difference of functions on `Z ∩ B` and `Z ∩ A`. This is the hypothesis `hZ` of
  `VanishingCore.exists_sub_eq_res`.

Blueprint `sm-blow-down-contracting.tex`, `lem:sm-bdc-genus-zero`.
-/

namespace DeJongAlterations.StableModification.BlowDown.VanishingGenus

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **`h⁰(Z, 𝒪_Z) = 1`** for an integral scheme `Z`, universally closed and locally of finite type
over an algebraically closed field `k`: `Γ(Z, 𝒪_Z)` is a field, finite over `k`, hence `k`. -/
theorem finrank_cohomology_zero_eq_one {Z : Scheme.{u}} (p : Z ⟶ Spec (.of k)) [IsIntegral Z]
    [UniversallyClosed p] [LocallyOfFiniteType p] [CompactSpace Z]
    [IsAffineHom (pullback.diagonal (terminal.from Z))] :
    Module.finrank k (cohomology (SheafOfModules.unit Z.ringCatSheaf) (structureCoeff p) 0) = 1 := by
  set c := structureCoeff p with hc
  -- `c : k → Γ(Z, ⊤)` is bijective
  have hfin : c.Finite := by
    have h1 : p.appTop.hom.Finite := finite_appTop_of_universallyClosed k p
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
    exact h1.comp h2
  have : Nonempty Z := inferInstance
  have : IsDomain Γ(Z, ⊤) := inferInstance
  let _ : Algebra k Γ(Z, ⊤) := c.toAlgebra
  have : Module.Finite k Γ(Z, ⊤) := hfin
  have : Algebra.IsIntegral k Γ(Z, ⊤) := inferInstance
  have hbij : Function.Bijective c := IsAlgClosed.algebraMap_bijective_of_isIntegral
  -- the restriction `Γ(Z, ⊤) → Γ(Z, ⊤)` is the identity
  have hres : ∀ x : Γ(Z, ⊤), Z.presheaf.map (homOfLE (le_top : (⊤ : Z.Opens) ≤ ⊤)).op x = x := by
    intro x
    rw [show (homOfLE (le_top : (⊤ : Z.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) from rfl, Z.presheaf.map_id]
    rfl
  -- `k ≃ Γ(Z, ⊤)` as `k`-modules
  let M := sectionsModuleCat (SheafOfModules.unit Z.ringCatSheaf) c ⊤ le_top
  let φ : k →ₗ[k] M := LinearMap.toSpanSingleton k M (show Γ(Z, ⊤) from 1)
  have hφ : ∀ r : k, (φ r : Γ(Z, ⊤)) = c r := by
    intro r
    change (sectionsRingHom c (le_top : (⊤ : Z.Opens) ≤ ⊤) r : Γ(Z, ⊤)) * (1 : Γ(Z, ⊤)) = c r
    rw [mul_one]
    exact hres (c r)
  have hφbij : Function.Bijective φ := by
    refine ⟨fun a b hab => hbij.1 ?_, fun x => ?_⟩
    · rw [← hφ, ← hφ]
      exact congrArg (fun y : M => (y : Γ(Z, ⊤))) hab
    · obtain ⟨r, hr⟩ := hbij.2 (show Γ(Z, ⊤) from x)
      exact ⟨r, (hφ r).trans hr⟩
  let e₁ : k ≃ₗ[k] M := LinearEquiv.ofBijective φ hφbij
  let e₂ : M ≃ₗ[k] cohomology (SheafOfModules.unit Z.ringCatSheaf) c 0 :=
    (cohomologyZeroIso (SheafOfModules.unit Z.ringCatSheaf) c).toLinearEquiv
  rw [← (e₁.trans e₂).finrank_eq, Module.finrank_self]

/-- **`p_a(Z) = 0` gives `H¹(Z, 𝒪_Z) = 0`** for an integral projective scheme over an algebraically
closed field covered by two affine opens with affine intersection. -/
theorem isZero_cohomology_one_of_arithmeticGenus_eq_zero {Z : Scheme.{u}} (p : Z ⟶ Spec (.of k))
    [IsIntegral Z] [LocallyOfFiniteType p] [CompactSpace Z]
    [IsAffineHom (pullback.diagonal (terminal.from Z))] (hp : IsProjectiveOver p)
    {A B : Z.Opens} (h : A ⊔ B = ⊤) (hA : IsAffineOpen A) (hB : IsAffineOpen B)
    (hAB : IsAffineOpen (A ⊓ B)) (hg : Genus.arithmeticGenus Z (structureCoeff p) = 0) :
    IsZero (cohomology (SheafOfModules.unit Z.ringCatSheaf) (structureCoeff p) 1) := by
  have : IsProper p := hp.isProper
  have h0 := finrank_cohomology_zero_eq_one p
  have hχ := DualityScheme.eulerCharOf_eq_of_pair (SheafOfModules.unit Z.ringCatSheaf)
    (structureCoeff p) h hA hB hAB
  rw [DualityScheme.eulerCharOf_unit, h0] at hχ
  have hg' : Genus.eulerChar Z (structureCoeff p) = 1 := by
    unfold Genus.arithmeticGenus at hg
    omega
  have h1 : Module.finrank k
      (cohomology (SheafOfModules.unit Z.ringCatSheaf) (structureCoeff p) 1) = 0 := by
    omega
  have : Module.Finite k
      (cohomology (SheafOfModules.unit Z.ringCatSheaf) (structureCoeff p) 1) :=
    finite_cohomology_of_isProjectiveOver hp (SheafOfModules.unit Z.ringCatSheaf)
      (fun W _ => Module.Finite.self Γ(Z, W)) 1
  have : Subsingleton
      (cohomology (SheafOfModules.unit Z.ringCatSheaf) (structureCoeff p) 1) :=
    Module.finrank_zero_iff.mp h1
  exact ModuleCat.isZero_of_subsingleton _

/-- **`H¹(Z, 𝒪_Z) = 0` on the cover `(Z ∩ A, Z ∩ B)`** for the reduced closure `Z = closure {ξ}`
of a point of a projective scheme `X` over an algebraically closed field covered by two affine
opens `A`, `B`, if `p_a(Z) = 0`: every function on `Z ∩ A ∩ B` is a difference of a function on
`Z ∩ B` and one on `Z ∩ A`. -/
theorem exists_sub_eq_closure {X : Scheme.{u}} (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q]
    [IsSeparated q] [CompactSpace X] (hq : IsProjectiveOver q) (ξ : X)
    [IsAffineHom (pullback.diagonal (terminal.from (ClosureComponent.closureScheme ξ)))]
    {A B : X.Opens} (h : A ⊔ B = ⊤) (hA : IsAffineOpen A) (hB : IsAffineOpen B)
    (hg : Genus.arithmeticGenus (ClosureComponent.closureScheme ξ)
      (structureCoeff (ClosureComponent.closureι ξ ≫ q)) = 0)
    (w : Γ(ClosureComponent.closureScheme ξ, (ClosureComponent.closureι ξ) ⁻¹ᵁ (A ⊓ B))) :
    ∃ (a : Γ(ClosureComponent.closureScheme ξ, (ClosureComponent.closureι ξ) ⁻¹ᵁ A))
      (b : Γ(ClosureComponent.closureScheme ξ, (ClosureComponent.closureι ξ) ⁻¹ᵁ B)),
      w = (ClosureComponent.closureScheme ξ).presheaf.map (homOfLE (fun _ hz => hz.2 :
          (ClosureComponent.closureι ξ) ⁻¹ᵁ (A ⊓ B) ≤ (ClosureComponent.closureι ξ) ⁻¹ᵁ B)).op b -
        (ClosureComponent.closureScheme ξ).presheaf.map (homOfLE (fun _ hz => hz.1 :
          (ClosureComponent.closureι ξ) ⁻¹ᵁ (A ⊓ B) ≤ (ClosureComponent.closureι ξ) ⁻¹ᵁ A)).op a := by
  have hp : IsProjectiveOver (ClosureComponent.closureι ξ ≫ q) :=
    DeJong.IsProjectiveOver.comp_isClosedImmersion hq _
  have hA' : IsAffineOpen ((ClosureComponent.closureι ξ) ⁻¹ᵁ A) :=
    hA.preimage (ClosureComponent.closureι ξ)
  have hB' : IsAffineOpen ((ClosureComponent.closureι ξ) ⁻¹ᵁ B) :=
    hB.preimage (ClosureComponent.closureι ξ)
  have hAB' : IsAffineOpen ((ClosureComponent.closureι ξ) ⁻¹ᵁ A ⊓
      (ClosureComponent.closureι ξ) ⁻¹ᵁ B) := hA'.inf hB'
  have h' : (ClosureComponent.closureι ξ) ⁻¹ᵁ A ⊔ (ClosureComponent.closureι ξ) ⁻¹ᵁ B = ⊤ := by
    apply top_unique
    intro z _
    have hz : ClosureComponent.closureι ξ z ∈ A ⊔ B := by rw [h]; trivial
    rcases Opens.mem_sup.mp hz with hz | hz
    · exact Opens.mem_sup.mpr (Or.inl hz)
    · exact Opens.mem_sup.mpr (Or.inr hz)
  have hz := isZero_cohomology_one_of_arithmeticGenus_eq_zero (ClosureComponent.closureι ξ ≫ q)
    hp h' hA' hB' hAB' hg
  have hsurj := (isZero_cohomology_one_pair_iff
    (SheafOfModules.unit (ClosureComponent.closureScheme ξ).ringCatSheaf)
    (structureCoeff (ClosureComponent.closureι ξ ≫ q)) h' hA' hB' hAB').mp hz
  obtain ⟨⟨a, b⟩, hab⟩ := hsurj w
  exact ⟨a, b, hab.symm⟩

end

end DeJongAlterations.StableModification.BlowDown.VanishingGenus
