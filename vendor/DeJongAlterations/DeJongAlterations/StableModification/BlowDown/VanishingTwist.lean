/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.VanishingFibre
import DeJongAlterations.StableModification.CurvesField.AmpleSection
import DeJongAlterations.StableModification.CurvesField.RiemannRoch

/-!
# Serre vanishing for `𝒪(mT)` over `V` from the closed fibre (Temkin, Prop. 4.4.6, T:3210–3222)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Prop. 4.4.6 (T:3210–3222): `H¹(𝒪_{Y_s}(m ∑ pᵢ)) = 0` for `m ≫ 0`, hence a section `h_s` of
`𝒪_{Y_s}(m ∑ pᵢ)` not vanishing at the `pᵢ` lifts to a section `h` of `𝒪_Y(m ∑ P̄ᵢ)`.

We work with a two-chart cover `Y = U ∪ V` (affine, affine intersection) on which the line bundle
`𝓛` has a section `s` invertible on `U` and a generator `σ` on `V`, so that `𝓛^{k}` is the divisor
twist `𝒪(kT)` by `f = s/σ` (lane OM3B's `LineBundleData.twoChartIso`), and with the algebra of the
two-term complexes of lane COH4 (`CurvesField.RiemannRochAlgebra`).

* `exists_forall_subsingleton_H1_of_fibre`: if `H¹(Y, 𝒪)` (on the cover) is finitely generated
  over the local ring `R` and the closed fibre `X = Y_{s₀}` satisfies `H¹(X ∖ T, 𝒪) = 0` in the form
  "every function on `X ∩ U ∩ V` is a difference of a function on `X ∩ D(f)` and one on `X ∩ U`",
  then `H¹(Y, 𝒪(mT)) = 0` for `m ≫ 0`. Proof: Serre vanishing on `X`
  (`CurvesField.exists_forall_subsingleton_H1_of_limit`, finite generation passing to `X` by
  `VanishingNakayama.finite_H1_of_surjective`), then Nakayama
  (`VanishingNakayama.subsingleton_H1_of_subsingleton`, with
  `VanishingFibre.fiberι_app_surjective` and `VanishingFibre.mem_smul_top_of_fiberι_app_eq_zero`).
  Temkin's "noetherian approximation" (T:3219) and the semicontinuity theorem are not needed.
* `exists_section_of_subsingleton_H1`: if `H¹(𝒪(mT)) = 0`, the class of `1` in `Γ(V) ⧸ f` is the
  `V`-component of a global section `t` of `𝓛^{N(m+1)}` (`CurvesField.stepQ_surjective_family`),
  which therefore has no zero on `V(f) = Z(s) ∩ V`: `s` and `t` have no common zero (the
  argument of OM3B's `Ample.exists_section_sup_eq_top`, over any ring).

Blueprint `sm-blow-down-contracting.tex`, `lem:sm-bdc-serre-fibre`, `lem:sm-bdc-second-section`.
-/

namespace DeJongAlterations.StableModification.BlowDown.VanishingTwist

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.Projectivity
open DeJongAlterations.StableModification.CurvesField.Ample.LineBundleData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

noncomputable section

/-! ### The second section from the vanishing of `H¹` -/

section SecondSection

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : R →+* Γ(X, ⊤))

open Projectivity.LineBundleData in
/-- **The second section** (T:3220–3222): on a cover `X = U ∪ V` with `s` invertible on `U` and
`σ` a generator over `V`, if `H¹(𝒪(mT)) = 0` for the twist by `f = s/σ`, then some section `t` of
`𝓛^{N(m+1)}` has no common zero with `s`. -/
theorem exists_section_of_subsingleton_H1 {L : Projectivity.LineBundleData X} {N : ℤ}
    (s : L.Sections N ⊤) {U V : X.Opens} {σ : L.Sections N V} (hσ : σ.nonvanishingLocus = V)
    (hUs : U ≤ s.nonvanishingLocus) (hcov : U ⊔ V = ⊤) (m : ℕ)
    [Subsingleton (H1 (resUV (unitModule X) U V c) (resVU (unitModule X) U V c)
      (twistFamily (unitModule X) U V c (isUnit_ratio s hσ hUs) m))] :
    ∃ t : L.Sections (N * ((m + 1 : ℕ) : ℤ)) ⊤,
      s.nonvanishingLocus ⊔ t.nonvanishingLocus = ⊤ := by
  classical
  have hf := isUnit_ratio s hσ hUs
  obtain ⟨p₀, hp₀, hp₀1⟩ := stepQ_surjective_family (resUV (unitModule X) U V c)
    (resVU (unitModule X) U V c) (fEquiv (unitModule X) U V c hf)
    (fMul (unitModule X) V c (ratio s hσ)) (resVU_fMul (unitModule X) U V c hf)
    (twistFamily (unitModule X) U V c hf) (twistFamily_succ (unitModule X) U V c hf) (m : ℤ)
    (Submodule.Quotient.mk (id (1 : Γ(X, V)) : sectionsModuleCat (unitModule X) c V le_top))
  set k : ℕ := m + 1
  have hp₀' : p₀ ∈ H0 (resUV (unitModule X) U V c) (resVU (unitModule X) U V c)
      (twistFamily (unitModule X) U V c hf ((k : ℕ) : ℤ)) := by
    have e : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [← e]
    exact hp₀
  -- the global section of `𝒪(kD)` and the corresponding section `t` of `𝓛^{Nk}`
  let glob := (divisorTwistGlobalEquiv (unitModule X) U V c hf k).symm ⟨p₀, hp₀'⟩
  let e := twoChartIso s hσ (unitModule X) hUs k hcov
  let T : Γ(L.twist (unitModule X) (N * k), ⊤) := e.inv.app ⊤ glob
  have hTp : e.hom.app ⊤ T = glob := by
    change (e.inv ≫ e.hom).app ⊤ glob = glob
    rw [e.inv_hom_id]
    rfl
  have h2 : (toPair s (unitModule X) hσ hUs k ⊤ T).2 =
      (unitModule X).presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op p₀.2 := by
    have e1 : toPair s (unitModule X) hσ hUs k ⊤ T =
        (show twistSubgroup (unitModule X) U V ((isUnit_ratio s hσ hUs).unit ^ (k : ℤ)) ⊤ from
          glob).1 := by
      rw [← twoChartHom_app s hσ (unitModule X) hUs k ⊤ T]
      exact congrArg (fun z => (show twistSubgroup (unitModule X) U V
        ((isUnit_ratio s hσ hUs).unit ^ (k : ℤ)) ⊤ from z).1) hTp
    rw [e1]
    rfl
  have hmul := mulSec_toPair_snd s hσ (unitModule X) hUs k ⊤ T
  rw [h2] at hmul
  let t : L.Sections (N * ((m + 1 : ℕ) : ℤ)) ⊤ := T
  refine ⟨t, ?_⟩
  apply top_unique
  intro z _
  by_cases hz : z ∈ s.nonvanishingLocus
  · exact Opens.mem_sup.mpr (Or.inl hz)
  · refine Opens.mem_sup.mpr (Or.inr ?_)
    have hzV : z ∈ V := by
      have hz' : z ∈ U ⊔ V := by rw [hcov]; trivial
      rcases Opens.mem_sup.mp hz' with h | h
      · exact absurd (hUs h) hz
      · exact h
    -- the `V`-component is `1` modulo `f = s/σ`
    obtain ⟨b, hb⟩ := (Submodule.Quotient.eq _).mp hp₀1
    let a : Γ(X, V) := p₀.2
    let b' : Γ(X, V) := b
    have hb' : a = 1 + ratio s hσ * b' := by
      have hb2 : ratio s hσ * b' = a - 1 := hb
      rw [hb2]
      ring
    have hz1 : z ∈ X.basicOpen a := by
      rw [X.mem_basicOpen _ z hzV, hb', map_add, map_one, map_mul]
      apply Ample.isUnit_add_of_mem_maximalIdeal isUnit_one
      apply Ideal.mul_mem_right
      apply Ample.germ_mem_maximalIdeal
      rw [basicOpen_ratio]
      exact fun h => hz h.2
    have hzT : z ∈ (t.restrict (le_top : ⊤ ⊓ V ≤ ⊤)).nonvanishingLocus := by
      have e2 : t.restrict (le_top : ⊤ ⊓ V ≤ ⊤) =
          X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op a • secV σ k ⊤ := by
        rw [← mulSec_unit]
        exact hmul.symm
      rw [e2, Sections.nonvanishingLocus_smul, Scheme.basicOpen_res,
        nonvanishingLocus_secV hσ k ⊤]
      exact ⟨⟨⟨trivial, hzV⟩, hz1⟩, ⟨trivial, hzV⟩⟩
    rw [Sections.nonvanishingLocus_restrict] at hzT
    exact hzT.2

end SecondSection

/-! ### Finite generation of the twists -/

section Finite

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (F : Y.Modules) (U V : Y.Opens)
  (c : R →+* Γ(Y, ⊤)) {f : Γ(Y, V)}
  (hf : IsUnit (Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op f))

/-- Finite generation of `H¹` passes from `F` to the twists `F(mD)`, `m ≥ 0` (the maps
`H¹(F(mD)) → H¹(F((m+1)D))` are onto). -/
theorem finite_H1_twistFamily_nat
    [Module.Finite R (H1 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0))] (m : ℕ) :
    Module.Finite R (H1 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf m)) := by
  induction m with
  | zero => simpa using (inferInstance :
      Module.Finite R (H1 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0)))
  | succ n ih =>
    rw [Nat.cast_succ, twistFamily_succ]
    exact Module.Finite.of_surjective _ (stepH1_surjective (resUV F U V c) (resVU F U V c)
      (fEquiv F U V c hf) (fMul F V c f) (resVU_fMul F U V c hf) (twistFamily F U V c hf n))

end Finite

/-! ### Restriction to a closed subscheme as a map of two-chart complexes -/

section Restriction

variable {R : Type u} [CommRing R] {Y X : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of R))
  (ι : X ⟶ Y)

lemma appLE_sectionsRingHom {W : Y.Opens} {W' : X.Opens} (h : W' ≤ ι ⁻¹ᵁ W) (r : R) :
    ι.appLE W W' h (sectionsRingHom (structureCoeff q) (le_top : W ≤ ⊤) r) =
      sectionsRingHom (structureCoeff (ι ≫ q)) (le_top : W' ≤ ⊤) r := by
  change (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ ι.appLE W W' h) (structureCoeff q r) = _
  rw [Scheme.Hom.map_appLE]
  change X.presheaf.map _ (ι.app ⊤ (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))) =
    X.presheaf.map _ ((ι ≫ q).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
  rw [Scheme.Hom.comp_appTop]
  rfl

lemma appLE_res {W₁ W₂ : Y.Opens} {W₁' W₂' : X.Opens} (h₁ : W₁' ≤ ι ⁻¹ᵁ W₁)
    (h₂ : W₂' ≤ ι ⁻¹ᵁ W₂) (hW : W₂ ≤ W₁) (hW' : W₂' ≤ W₁') (x : Γ(Y, W₁)) :
    ι.appLE W₂ W₂' h₂ (Y.presheaf.map (homOfLE hW).op x) =
      X.presheaf.map (homOfLE hW').op (ι.appLE W₁ W₁' h₁ x) := by
  change (Y.presheaf.map (homOfLE hW).op ≫ ι.appLE W₂ W₂' h₂) x =
    (ι.appLE W₁ W₁' h₁ ≫ X.presheaf.map (homOfLE hW').op) x
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/-- `ι.appLE W W'` as an `R`-linear map of sections. -/
def appLin (W : Y.Opens) (W' : X.Opens) (h : W' ≤ ι ⁻¹ᵁ W) :
    sectionsModuleCat (unitModule Y) (structureCoeff q) W le_top →ₗ[R]
      sectionsModuleCat (unitModule X) (structureCoeff (ι ≫ q)) W' le_top where
  toFun x := ι.appLE W W' h x
  map_add' x y := map_add (ι.appLE W W' h).hom x y
  map_smul' r x := by
    change ι.appLE W W' h (sectionsRingHom (structureCoeff q) (le_top : W ≤ ⊤) r *
        (show Γ(Y, W) from x)) =
      sectionsRingHom (structureCoeff (ι ≫ q)) (le_top : W' ≤ ⊤) r *
        ι.appLE W W' h (show Γ(Y, W) from x)
    rw [map_mul, appLE_sectionsRingHom]

lemma appLin_apply (W : Y.Opens) (W' : X.Opens) (h : W' ≤ ι ⁻¹ᵁ W) (x : Γ(Y, W)) :
    appLin q ι W W' h x = ι.appLE W W' h x := rfl

variable {U V : Y.Opens} {f : Γ(Y, V)}
  (hf : IsUnit (Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op f))

lemma inf_le_preimage : ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V ≤ ι ⁻¹ᵁ (U ⊓ V) := fun _ hx => ⟨hx.1, hx.2⟩

include hf in
lemma isUnit_app :
    IsUnit (X.presheaf.map (homOfLE (inf_le_right : ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V ≤ ι ⁻¹ᵁ V)).op
      (ι.app V f)) := by
  have h := hf.map (ι.appLE (U ⊓ V) (ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V) (inf_le_preimage ι)).hom
  rw [appLE_res ι (le_rfl : ι ⁻¹ᵁ V ≤ ι ⁻¹ᵁ V) (inf_le_preimage ι) inf_le_right inf_le_right f,
    Scheme.Hom.appLE_eq_app] at h
  exact h

lemma appLE_unit_zpow (m : ℤ) :
    ι.appLE (U ⊓ V) (ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V) (inf_le_preimage ι)
        (((hf.unit ^ m : Γ(Y, U ⊓ V)ˣ)) : Γ(Y, U ⊓ V)) =
      ((((isUnit_app ι hf).unit ^ m : Γ(X, ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V)ˣ)) :
        Γ(X, ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V)) := by
  have e : Units.map (ι.appLE (U ⊓ V) (ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V) (inf_le_preimage ι)).hom.toMonoidHom
      hf.unit = (isUnit_app ι hf).unit := by
    ext
    change ι.appLE (U ⊓ V) (ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V) (inf_le_preimage ι) (hf.unit : Γ(Y, U ⊓ V)) = _
    rw [IsUnit.unit_spec, IsUnit.unit_spec,
      appLE_res ι (le_rfl : ι ⁻¹ᵁ V ≤ ι ⁻¹ᵁ V) (inf_le_preimage ι) inf_le_right inf_le_right f,
      Scheme.Hom.appLE_eq_app]
  rw [← e, ← map_zpow]
  rfl

lemma appLin_resUV :
    appLin q ι (U ⊓ V) (ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V) (inf_le_preimage ι) ∘ₗ
        resUV (unitModule Y) U V (structureCoeff q) =
      resUV (unitModule X) (ι ⁻¹ᵁ U) (ι ⁻¹ᵁ V) (structureCoeff (ι ≫ q)) ∘ₗ
        appLin q ι U (ι ⁻¹ᵁ U) le_rfl := by
  apply LinearMap.ext
  intro x
  exact appLE_res ι le_rfl (inf_le_preimage ι) inf_le_left inf_le_left x

lemma appLin_resVU :
    appLin q ι (U ⊓ V) (ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V) (inf_le_preimage ι) ∘ₗ
        resVU (unitModule Y) U V (structureCoeff q) =
      resVU (unitModule X) (ι ⁻¹ᵁ U) (ι ⁻¹ᵁ V) (structureCoeff (ι ≫ q)) ∘ₗ
        appLin q ι V (ι ⁻¹ᵁ V) le_rfl := by
  apply LinearMap.ext
  intro x
  exact appLE_res ι le_rfl (inf_le_preimage ι) inf_le_right inf_le_right x

lemma appLin_twistFamily (m : ℤ) :
    appLin q ι (U ⊓ V) (ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V) (inf_le_preimage ι) ∘ₗ
        twistFamily (unitModule Y) U V (structureCoeff q) hf m =
      twistFamily (unitModule X) (ι ⁻¹ᵁ U) (ι ⁻¹ᵁ V) (structureCoeff (ι ≫ q))
        (isUnit_app ι hf) m ∘ₗ appLin q ι (U ⊓ V) (ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V) (inf_le_preimage ι) := by
  apply LinearMap.ext
  intro x
  change ι.appLE (U ⊓ V) (ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V) (inf_le_preimage ι)
      ((((hf.unit ^ m : Γ(Y, U ⊓ V)ˣ)) : Γ(Y, U ⊓ V)) * (show Γ(Y, U ⊓ V) from x)) =
    ((((isUnit_app ι hf).unit ^ m : Γ(X, ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V)ˣ)) : Γ(X, ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V)) *
      ι.appLE (U ⊓ V) (ι ⁻¹ᵁ U ⊓ ι ⁻¹ᵁ V) (inf_le_preimage ι) (show Γ(Y, U ⊓ V) from x)
  rw [map_mul, appLE_unit_zpow]

end Restriction

/-! ### Serre vanishing over `V` from the closed fibre -/

section Fibre

variable {R : Type u} [CommRing R] [IsLocalRing R] {Y : Scheme.{u}}
  (q : Y ⟶ Spec (CommRingCat.of R))

local notation "s₀" => IsLocalRing.closedPoint R

instance isAffineHom_fiberι : IsAffineHom (q.fiberι s₀) :=
  MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance

/-- **`H¹(Y, 𝒪(mT)) = 0` for `m ≫ 0` from the closed fibre** (T:3210–3219): on a two-chart cover
`Y = U ∪ V` (affine, with affine intersection) and `f ∈ Γ(V)` invertible on `U ∩ V`, if
`H¹(Y, 𝒪)` is finitely generated over the local ring `R` and on the closed fibre `X` every
function on `X ∩ U ∩ V` is the difference of a function on `X ∩ D(f)` and one on `X ∩ U`
(`H¹(X ∖ T, 𝒪) = 0`), then the first cohomology of the twists `𝒪(mT)` vanishes for `m ≫ 0`. -/
theorem exists_forall_subsingleton_H1_of_fibre {U V : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V)) {f : Γ(Y, V)}
    (hf : IsUnit (Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op f))
    [Module.Finite R (H1 (resUV (unitModule Y) U V (structureCoeff q))
      (resVU (unitModule Y) U V (structureCoeff q))
      (twistFamily (unitModule Y) U V (structureCoeff q) hf 0))]
    (hcore : ∀ w : Γ(q.fiber s₀, (q.fiberι s₀) ⁻¹ᵁ U ⊓ (q.fiberι s₀) ⁻¹ᵁ V),
      ∃ (a : Γ(q.fiber s₀, (q.fiberι s₀) ⁻¹ᵁ U))
        (b : Γ(q.fiber s₀, (q.fiber s₀).basicOpen ((q.fiberι s₀).app V f)))
        (h : (q.fiberι s₀) ⁻¹ᵁ U ⊓ (q.fiberι s₀) ⁻¹ᵁ V ≤
          (q.fiber s₀).basicOpen ((q.fiberι s₀).app V f)),
        w = (q.fiber s₀).presheaf.map (homOfLE h).op b -
          (q.fiber s₀).presheaf.map (homOfLE (inf_le_left :
            (q.fiberι s₀) ⁻¹ᵁ U ⊓ (q.fiberι s₀) ⁻¹ᵁ V ≤ (q.fiberι s₀) ⁻¹ᵁ U)).op a) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      Subsingleton (H1 (resUV (unitModule Y) U V (structureCoeff q))
        (resVU (unitModule Y) U V (structureCoeff q))
        (twistFamily (unitModule Y) U V (structureCoeff q) hf m)) := by
  have hfX := isUnit_app (q.fiberι s₀) hf
  have hVX : IsAffineOpen ((q.fiberι s₀) ⁻¹ᵁ V) := hV.preimage (q.fiberι s₀)
  -- the restriction maps
  have hsurjU : Function.Surjective
      (appLin q (q.fiberι s₀) U ((q.fiberι s₀) ⁻¹ᵁ U) le_rfl) := by
    intro y
    obtain ⟨x, hx⟩ := VanishingFibre.fiberι_app_surjective q hU y
    refine ⟨x, ?_⟩
    rw [appLin_apply, Scheme.Hom.appLE_eq_app]
    exact hx
  have hsurjV : Function.Surjective
      (appLin q (q.fiberι s₀) V ((q.fiberι s₀) ⁻¹ᵁ V) le_rfl) := by
    intro y
    obtain ⟨x, hx⟩ := VanishingFibre.fiberι_app_surjective q hV y
    refine ⟨x, ?_⟩
    rw [appLin_apply, Scheme.Hom.appLE_eq_app]
    exact hx
  have hbijW := bijective_presheaf_map_of_eq (unitModule (q.fiber s₀))
    (inf_le_preimage (q.fiberι s₀) : (q.fiberι s₀) ⁻¹ᵁ U ⊓ (q.fiberι s₀) ⁻¹ᵁ V ≤
      (q.fiberι s₀) ⁻¹ᵁ (U ⊓ V)) (fun _ hx => ⟨hx.1, hx.2⟩)
  have hsurjW : Function.Surjective (appLin q (q.fiberι s₀) (U ⊓ V)
      ((q.fiberι s₀) ⁻¹ᵁ U ⊓ (q.fiberι s₀) ⁻¹ᵁ V) (inf_le_preimage (q.fiberι s₀))) := by
    intro y
    obtain ⟨y', rfl⟩ := hbijW.2 y
    obtain ⟨x, hx⟩ := VanishingFibre.fiberι_app_surjective q hUV y'
    exact ⟨x, by rw [appLin_apply, ← hx]; rfl⟩
  have hkerW : ∀ w, appLin q (q.fiberι s₀) (U ⊓ V)
      ((q.fiberι s₀) ⁻¹ᵁ U ⊓ (q.fiberι s₀) ⁻¹ᵁ V) (inf_le_preimage (q.fiberι s₀)) w = 0 →
      w ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R (sectionsModuleCat (unitModule Y)
        (structureCoeff q) (U ⊓ V) le_top)) := by
    intro w hw
    apply VanishingFibre.mem_smul_top_of_fiberι_app_eq_zero q hUV w
    apply hbijW.1
    rw [map_zero]
    exact hw
  -- finite generation on the closed fibre
  have : Module.Finite R (H1
      (resUV (unitModule (q.fiber s₀)) ((q.fiberι s₀) ⁻¹ᵁ U) ((q.fiberι s₀) ⁻¹ᵁ V)
        (structureCoeff (q.fiberι s₀ ≫ q)))
      (resVU (unitModule (q.fiber s₀)) ((q.fiberι s₀) ⁻¹ᵁ U) ((q.fiberι s₀) ⁻¹ᵁ V)
        (structureCoeff (q.fiberι s₀ ≫ q)))
      (twistFamily (unitModule (q.fiber s₀)) ((q.fiberι s₀) ⁻¹ᵁ U) ((q.fiberι s₀) ⁻¹ᵁ V)
        (structureCoeff (q.fiberι s₀ ≫ q)) hfX 0)) :=
    VanishingNakayama.finite_H1_of_surjective _ _ _ _ _ _ _ _ _
      (appLin_resUV q (q.fiberι s₀)) (appLin_resVU q (q.fiberι s₀))
      (appLin_twistFamily q (q.fiberι s₀) hf 0) hsurjW
  -- `H¹(X ∖ T, 𝒪) = 0`: the limit condition on the closed fibre
  have hlim : IsTwistLimit (unitModule (q.fiber s₀)) ((q.fiberι s₀) ⁻¹ᵁ U)
      ((q.fiberι s₀) ⁻¹ᵁ V) (structureCoeff (q.fiberι s₀ ≫ q)) hfX := by
    intro w
    obtain ⟨a, b, hle, hw⟩ := hcore w
    have hB' : (q.fiber s₀).basicOpen ((q.fiberι s₀).app V f) ⊓ (q.fiberι s₀) ⁻¹ᵁ V =
        (q.fiber s₀).basicOpen ((q.fiberι s₀).app V f) :=
      inf_eq_left.mpr ((q.fiber s₀).basicOpen_le _)
    obtain ⟨n, x, hx⟩ := exists_pow_smul_eq_res (unitModule (q.fiber s₀))
      ((q.fiber s₀).basicOpen ((q.fiberι s₀).app V f)) ((q.fiberι s₀) ⁻¹ᵁ V)
      hVX hB' ((q.fiber s₀).presheaf.map (homOfLE (inf_le_left :
        (q.fiber s₀).basicOpen ((q.fiberι s₀).app V f) ⊓ (q.fiberι s₀) ⁻¹ᵁ V ≤
          (q.fiber s₀).basicOpen ((q.fiberι s₀).app V f))).op b)
    refine ⟨n, (a, x), ?_⟩
    rw [twistDiff_apply, fEquiv_iterate]
    have hle₂ : (q.fiberι s₀) ⁻¹ᵁ U ⊓ (q.fiberι s₀) ⁻¹ᵁ V ≤
        (q.fiber s₀).basicOpen ((q.fiberι s₀).app V f) ⊓ (q.fiberι s₀) ⁻¹ᵁ V :=
      le_inf hle inf_le_right
    have hx2 : res (inf_le_right : (q.fiber s₀).basicOpen ((q.fiberι s₀).app V f) ⊓
          (q.fiberι s₀) ⁻¹ᵁ V ≤ (q.fiberι s₀) ⁻¹ᵁ V) (((q.fiberι s₀).app V f) ^ n) *
        res (inf_le_left : (q.fiber s₀).basicOpen ((q.fiberι s₀).app V f) ⊓
          (q.fiberι s₀) ⁻¹ᵁ V ≤ (q.fiber s₀).basicOpen ((q.fiberι s₀).app V f)) b =
        res (inf_le_right : (q.fiber s₀).basicOpen ((q.fiberι s₀).app V f) ⊓
          (q.fiberι s₀) ⁻¹ᵁ V ≤ (q.fiberι s₀) ⁻¹ᵁ V) x := hx
    have hx3 := congrArg (res hle₂) hx2
    rw [map_mul, res_res_trans, res_res_trans, res_res_trans] at hx3
    have hu : ((((hfX.unit ^ (n : ℤ) : Γ(q.fiber s₀, (q.fiberι s₀) ⁻¹ᵁ U ⊓
        (q.fiberι s₀) ⁻¹ᵁ V)ˣ)) : Γ(q.fiber s₀, (q.fiberι s₀) ⁻¹ᵁ U ⊓ (q.fiberι s₀) ⁻¹ᵁ V))) =
        res (inf_le_right : (q.fiberι s₀) ⁻¹ᵁ U ⊓ (q.fiberι s₀) ⁻¹ᵁ V ≤ (q.fiberι s₀) ⁻¹ᵁ V)
          (((q.fiberι s₀).app V f) ^ n) := by
      rw [zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_pow]
    change res (inf_le_right : (q.fiberι s₀) ⁻¹ᵁ U ⊓ (q.fiberι s₀) ⁻¹ᵁ V ≤ (q.fiberι s₀) ⁻¹ᵁ V) x -
        ((((hfX.unit ^ (n : ℤ) : Γ(q.fiber s₀, (q.fiberι s₀) ⁻¹ᵁ U ⊓ (q.fiberι s₀) ⁻¹ᵁ V)ˣ)) :
          Γ(q.fiber s₀, (q.fiberι s₀) ⁻¹ᵁ U ⊓ (q.fiberι s₀) ⁻¹ᵁ V)) *
          res (inf_le_left : (q.fiberι s₀) ⁻¹ᵁ U ⊓ (q.fiberι s₀) ⁻¹ᵁ V ≤ (q.fiberι s₀) ⁻¹ᵁ U) a) =
      res (inf_le_right : (q.fiberι s₀) ⁻¹ᵁ U ⊓ (q.fiberι s₀) ⁻¹ᵁ V ≤ (q.fiberι s₀) ⁻¹ᵁ V)
          (((q.fiberι s₀).app V f) ^ n) *
        (show Γ(q.fiber s₀, (q.fiberι s₀) ⁻¹ᵁ U ⊓ (q.fiberι s₀) ⁻¹ᵁ V) from w)
    rw [hu, ← hx3, hw]
    ring
  obtain ⟨m₀, hm₀⟩ := exists_forall_subsingleton_H1_of_limit _ _ _ _
    (resVU_fMul (unitModule (q.fiber s₀)) ((q.fiberι s₀) ⁻¹ᵁ U) ((q.fiberι s₀) ⁻¹ᵁ V)
      (structureCoeff (q.fiberι s₀ ≫ q)) hfX) _
    (twistFamily_succ (unitModule (q.fiber s₀)) ((q.fiberι s₀) ⁻¹ᵁ U) ((q.fiberι s₀) ⁻¹ᵁ V)
      (structureCoeff (q.fiberι s₀ ≫ q)) hfX) hlim
  refine ⟨m₀, fun m hm => ?_⟩
  have := hm₀ m hm
  have := finite_H1_twistFamily_nat (unitModule Y) U V (structureCoeff q) hf m
  exact VanishingNakayama.subsingleton_H1_of_subsingleton _ _ _ _ _ _ _ _ _
    (appLin_resUV q (q.fiberι s₀)) (appLin_resVU q (q.fiberι s₀))
    (appLin_twistFamily q (q.fiberι s₀) hf m) hsurjU hsurjV hkerW

end Fibre

end

end DeJongAlterations.StableModification.BlowDown.VanishingTwist
