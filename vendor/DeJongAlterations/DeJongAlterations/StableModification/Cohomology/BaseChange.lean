/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.Cech
import DeJongAlterations.Geometry.QuotGrassmannPivotAffineSectionUnitValues
import DeJongAlterations.StableModification.Cohomology.MumfordAlgebra
import DeJongAlterations.Geometry.ProperSteinProjectiveCechSubsetNonemptyComparison
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Base change of sections and of Čech complexes

Let `p : X → Spec A` be a scheme over `A`, `φ : A → B` a ring map, `X_B = X ×_{Spec A} Spec B`
with projections `q : X_B → X` (`bcFst`) and `X_B → Spec B` (`bcSnd`), and `F` a quasi-coherent
module on `X`. For every affine open `U ⊆ X` the map `B ⊗_A Γ(U, F) → Γ(q⁻¹U, q^*F)`,
`b ⊗ s ↦ b · q^*s`, is bijective, compatibly with restrictions; hence the Čech complex of `q^*F`
for the cover `q⁻¹U` is the base change of the Čech complex of `F` (blueprint
`prop:sm-cech-base-change`; EGA III 1.4.15, Stacks 02KH; used for the Mumford complex, Temkin,
*Stable modification of relative curves*, Lemma 4.4.2 and Proposition 4.4.6).

## Main results

* `pullbackSection f M V : Γ(M, V) → Γ(f^*M, f⁻¹V)`: the section maps of the unit of
  `f^* ⊣ f_*`, natural in `V`, semilinear over `f^♯`, compatible with composition
  (`pullbackSection_comp`, from `unit_conjugateEquiv`) and with open immersions
  (`pullbackSection_openImmersion`).
* `isBaseChange_pullbackSectionLinear`: for affine opens `U ⊆ X`, `V ⊆ Y` with `f(V) ⊆ U` and
  `F` quasi-coherent, `s ↦ f^*s|_V` exhibits `Γ(V, f^*F)` as `Γ(Y, V) ⊗_{Γ(X, U)} Γ(U, F)`.
  Proof: transport along `IsAffineOpen.fromSpec` and the square
  `Spec Γ(Y, V) → Spec Γ(X, U)` (`IsAffineOpen.SpecMap_appLE_fromSpec`) to Codex's affine
  computation `QuotGrassmann.originalSpecPullbackSectionsIso`.
* `isPushout_baseChange_sections`: `Γ(q⁻¹U, 𝒪) = Γ(U, 𝒪) ⊗_A B` (Mathlib's
  `isIso_pushoutSection_of_isAffineOpen`).
* `bijective_baseChangeSectionsMap`: `B ⊗_A Γ(U, F) ≅ Γ(q⁻¹U, q^*F)` for affine `U`
  (via `Algebra.IsPushout.cancelBaseChange`), natural in `U`
  (`cechBaseChangeComponent_naturality`).
* `subsetCechComplexBaseChangeIso`: `B ⊗_A` commutes with Codex's subset Čech complexes.
* `cechComplexBaseChangeIso`: `Č(U, F) ⊗_A B ≅ Č(q⁻¹U, q^*F)` for a finite family of opens with
  affine nonempty intersections.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.Geometry.QuotGrassmann DeJongAlterations.Geometry.ProperSteinProjectiveCech
open scoped TensorProduct ChangeOfRings

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

section PullbackSections

variable {X Y Z : Scheme.{u}}

/-- The section map `Γ(M, V) → Γ(f^*M, f⁻¹V)` induced by the unit of `f^* ⊣ f_*`. -/
def pullbackSection (f : Y ⟶ X) (M : X.Modules) (V : X.Opens) :
    Γ(M, V) →+ Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ V) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app V).hom

lemma pullbackSection_apply (f : Y ⟶ X) (M : X.Modules) (V : X.Opens) (s : Γ(M, V)) :
    pullbackSection f M V s =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app V s := rfl

/-- `pullbackSection` is semilinear over `f^♯ : Γ(X, V) → Γ(Y, f⁻¹V)`. -/
lemma pullbackSection_smul (f : Y ⟶ X) (M : X.Modules) (V : X.Opens) (r : Γ(X, V))
    (s : Γ(M, V)) : pullbackSection f M V (r • s) = f.app V r • pullbackSection f M V s :=
  Scheme.Modules.Hom.app_smul _ r s

/-- `pullbackSection` commutes with restrictions. -/
lemma pullbackSection_restrict (f : Y ⟶ X) (M : X.Modules) {V W : X.Opens} (h : W ≤ V)
    (s : Γ(M, V)) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE (f.preimage_mono h)).op
        (pullbackSection f M V s) =
      pullbackSection f M W (M.presheaf.map (homOfLE h).op s) := by
  exact (ConcreteCategory.congr_hom
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality
      (homOfLE h).op) s).symm

/-- Compatibility of `pullbackSection` with composition: pulling back along `f` and then `g`
agrees with pulling back along `g ≫ f`, through `pullbackComp`. -/
lemma pullbackSection_comp (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules) (V : X.Opens)
    (s : Γ(M, V)) :
    pullbackSection g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ V) (pullbackSection f M V s) =
      ((Scheme.Modules.pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ V)
        (pullbackSection (g ≫ f) M V s) := by
  have h := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (Scheme.Modules.pullbackPushforwardAdjunction g))
    (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f))
    (Scheme.Modules.pullbackComp g f).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  have h' := congrArg (fun φ => (Scheme.Modules.Hom.app φ V) s) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforward_map_app] at h'
  exact h'

/-- For an open immersion `j`, `pullbackSection j M V` is the restriction to `j(j⁻¹V)` followed by
the isomorphism `restrictFunctorIsoPullback j`. -/
lemma pullbackSection_openImmersion (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules)
    (V : X.Opens) (s : Γ(M, V)) :
    pullbackSection j M V s =
      ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M).app (j ⁻¹ᵁ V)
        (M.presheaf.map (homOfLE (j.image_preimage_le V)).op s) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction j)
    (Scheme.Modules.pullbackPushforwardAdjunction j) M
  have h' := congrArg (fun φ => (Scheme.Modules.Hom.app φ V) s) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h'
  exact h'.symm

/-- For an open immersion `j` and `V ⊆ j(Y)`, `pullbackSection j M V` is bijective. -/
lemma pullbackSection_bijective_of_openImmersion (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) {V : X.Opens} (hV : V ≤ j.opensRange) :
    Function.Bijective (pullbackSection j M V) := by
  have heq : j ''ᵁ (j ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hV]
  have hres : Function.Bijective (M.presheaf.map (homOfLE (j.image_preimage_le V)).op) := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨M.presheaf.map (homOfLE heq.ge).op, fun s => ?_, fun s => ?_⟩
    · exact presheaf_map_map_self M _ _ s
    · exact presheaf_map_map_self M _ _ s
  have hiso : Function.Bijective
      (((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M).app (j ⁻¹ᵁ V)) :=
    ConcreteCategory.bijective_of_isIso _
  have : (pullbackSection j M V : Γ(M, V) → _) =
      (((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M).app (j ⁻¹ᵁ V)) ∘
        (M.presheaf.map (homOfLE (j.image_preimage_le V)).op) :=
    funext (pullbackSection_openImmersion j M V)
  rw [this]
  exact hiso.comp hres

/-- `pullbackSection` along an isomorphism of schemes is bijective. -/
lemma pullbackSection_bijective_of_isIso (e : Y ⟶ X) [IsIso e] (M : X.Modules) (V : X.Opens) :
    Function.Bijective (pullbackSection e M V) :=
  pullbackSection_bijective_of_openImmersion e M (by
    rw [Scheme.Hom.opensRange_of_isIso]
    exact le_top)

/-- Naturality of `pullbackSection` in the module. -/
lemma pullbackSection_naturality (f : Y ⟶ X) {M M' : X.Modules} (φ : M ⟶ M') (V : X.Opens)
    (s : Γ(M, V)) :
    pullbackSection f M' V (φ.app V s) =
      ((Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ V) (pullbackSection f M V s) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ
  have h' := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ V) s) h
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app] at h'
  exact h'

/-- Morphisms of modules commute with restriction. -/
lemma hom_app_restrict {M M' : X.Modules} (φ : M ⟶ M') {V W : X.Opens} (h : W ≤ V)
    (s : Γ(M, V)) :
    φ.app W (M.presheaf.map (homOfLE h).op s) = M'.presheaf.map (homOfLE h).op (φ.app V s) := by
  have := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) s
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  exact this

end PullbackSections

section PullbackSectionLE

variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)

/-- The section map `Γ(F, U) → Γ(f^*F, V)` for `V ⊆ f⁻¹U`: pull back, then restrict. -/
def pullbackSectionLE {U : X.Opens} {V : Y.Opens} (hUV : V ≤ f ⁻¹ᵁ U) :
    Γ(F, U) →+ Γ((Scheme.Modules.pullback f).obj F, V) :=
  (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE hUV).op).hom.comp
    (pullbackSection f F U)

lemma pullbackSectionLE_apply {U : X.Opens} {V : Y.Opens} (hUV : V ≤ f ⁻¹ᵁ U) (s : Γ(F, U)) :
    pullbackSectionLE f F hUV s = ((Scheme.Modules.pullback f).obj F).presheaf.map
      (homOfLE hUV).op (pullbackSection f F U s) := rfl

/-- `pullbackSectionLE` is semilinear over `f.appLE U V`. -/
lemma pullbackSectionLE_smul {U : X.Opens} {V : Y.Opens} (hUV : V ≤ f ⁻¹ᵁ U) (r : Γ(X, U))
    (s : Γ(F, U)) :
    pullbackSectionLE f F hUV (r • s) = f.appLE U V hUV r • pullbackSectionLE f F hUV s := by
  rw [pullbackSectionLE_apply, pullbackSection_smul, Scheme.Modules.map_smul]
  rfl

lemma pullbackSectionLE_naturality {M M' : X.Modules} (φ : M ⟶ M') {U : X.Opens} {V : Y.Opens}
    (hUV : V ≤ f ⁻¹ᵁ U) (s : Γ(M, U)) :
    pullbackSectionLE f M' hUV (φ.app U s) =
      ((Scheme.Modules.pullback f).map φ).app V (pullbackSectionLE f M hUV s) := by
  rw [pullbackSectionLE_apply, pullbackSectionLE_apply, pullbackSection_naturality,
    hom_app_restrict]

/-- Compatibility of `pullbackSectionLE` with composition. -/
lemma pullbackSectionLE_comp (g : Z ⟶ Y) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (hUV : V ≤ f ⁻¹ᵁ U) (hVW : W ≤ g ⁻¹ᵁ V) (s : Γ(F, U)) :
    pullbackSectionLE g ((Scheme.Modules.pullback f).obj F) hVW (pullbackSectionLE f F hUV s) =
      ((Scheme.Modules.pullbackComp g f).inv.app F).app W
        (pullbackSectionLE (g ≫ f) F (hVW.trans (g.preimage_mono hUV)) s) := by
  rw [pullbackSectionLE_apply, pullbackSectionLE_apply, pullbackSectionLE_apply,
    ← pullbackSection_restrict, presheaf_map_map _ _ _ (hVW.trans (g.preimage_mono hUV)),
    pullbackSection_comp]
  exact (hom_app_restrict _ _ _).symm

/-- Transport of `pullbackSectionLE` along an equality of morphisms. -/
lemma pullbackSectionLE_congr {f₁ f₂ : Y ⟶ X} (h : f₁ = f₂) {U : X.Opens} {V : Y.Opens}
    (h₁ : V ≤ f₁ ⁻¹ᵁ U) (h₂ : V ≤ f₂ ⁻¹ᵁ U) (s : Γ(F, U)) :
    ((Scheme.Modules.pullbackCongr h).hom.app F).app V (pullbackSectionLE f₁ F h₁ s) =
      pullbackSectionLE f₂ F h₂ s := by
  subst h
  rfl

end PullbackSectionLE

section ModuleIsos

variable {X : Scheme.{u}} (M : X.Modules)

/-- Restriction along an equality of opens is bijective. -/
lemma bijective_presheaf_map_of_eq {V W : X.Opens} (h : W ≤ V) (h' : V ≤ W) :
    Function.Bijective (M.presheaf.map (homOfLE h).op) :=
  Function.bijective_iff_has_inverse.mpr ⟨M.presheaf.map (homOfLE h').op,
    fun s => presheaf_map_map_self M _ _ s, fun s => presheaf_map_map_self M _ _ s⟩

/-- The components of an isomorphism of modules are bijective. -/
lemma bijective_app_of_iso {N : X.Modules} (e : M ≅ N) (W : X.Opens) :
    Function.Bijective (e.hom.app W) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨e.inv.app W, fun x => ?_, fun x => ?_⟩
  · change (e.hom ≫ e.inv).app W x = x
    rw [e.hom_inv_id]
    rfl
  · change (e.inv ≫ e.hom).app W x = x
    rw [e.inv_hom_id]
    rfl

lemma iso_hom_app_inv_app {N : X.Modules} (e : M ≅ N) (W : X.Opens) (x : Γ(N, W)) :
    e.hom.app W (e.inv.app W x) = x := by
  change (e.inv ≫ e.hom).app W x = x
  rw [e.inv_hom_id]
  rfl

lemma natIso_hom_app_inv_app {C : Type*} [Category C] {G H : C ⥤ X.Modules} (e : G ≅ H) (c : C)
    (W : X.Opens) (x : Γ(H.obj c, W)) :
    (e.hom.app c).app W ((e.inv.app c).app W x) = x :=
  iso_hom_app_inv_app _ (e.app c) W x

lemma bijective_app_of_isIso {N : X.Modules} (φ : M ⟶ N) [IsIso φ] (W : X.Opens) :
    Function.Bijective (φ.app W) :=
  bijective_app_of_iso M (asIso φ) W

end ModuleIsos

section AffinePullback

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)

lemma bijective_pullbackSectionLE_of_openImmersion [IsOpenImmersion f] {U : X.Opens}
    (hU : U ≤ f.opensRange) {V : Y.Opens} (h₁ : V ≤ f ⁻¹ᵁ U) (h₂ : f ⁻¹ᵁ U ≤ V) :
    Function.Bijective (pullbackSectionLE f F h₁) :=
  (bijective_presheaf_map_of_eq _ h₁ h₂).comp (pullbackSection_bijective_of_openImmersion f F hU)

variable {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (hUV : V ≤ f ⁻¹ᵁ U)

/-- `Γ(F, U) → Γ(F|_{Spec Γ(X, U)}, ⊤)`. -/
noncomputable def affineSourceMap : Γ(F, U) →+ Γ(F.restrict hU.fromSpec, ⊤) :=
  (((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).inv.app F).app ⊤).hom.comp
    (pullbackSectionLE hU.fromSpec F hU.fromSpec_preimage_self.ge)

lemma bijective_affineSourceMap : Function.Bijective (affineSourceMap F hU) :=
  (bijective_app_of_iso _ ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app F).symm
    ⊤).comp (bijective_pullbackSectionLE_of_openImmersion _ F hU.opensRange_fromSpec.ge _
      hU.fromSpec_preimage_self.le)

/-- The comparison `Γ(f^*F, V) → Γ((Spec θ)^*(F|_{Spec Γ(X,U)}), ⊤)`. -/
noncomputable def affineTargetMap :
    Γ((Scheme.Modules.pullback f).obj F, V) →+
      Γ((Scheme.Modules.pullback (Spec.map (f.appLE U V hUV))).obj (F.restrict hU.fromSpec), ⊤) :=
  (((Scheme.Modules.pullback (Spec.map (f.appLE U V hUV))).map
      ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).inv.app F)).app ⊤).hom.comp <|
  (((Scheme.Modules.pullbackComp (Spec.map (f.appLE U V hUV)) hU.fromSpec).inv.app F).app ⊤).hom.comp <|
  (((Scheme.Modules.pullbackCongr (hU.SpecMap_appLE_fromSpec f hV hUV).symm).hom.app F).app ⊤).hom.comp <|
  (((Scheme.Modules.pullbackComp hV.fromSpec f).hom.app F).app ⊤).hom.comp <|
  pullbackSectionLE hV.fromSpec ((Scheme.Modules.pullback f).obj F) hV.fromSpec_preimage_self.ge

lemma bijective_affineTargetMap : Function.Bijective (affineTargetMap f F hU hV hUV) := by
  have h5 := bijective_pullbackSectionLE_of_openImmersion hV.fromSpec
    ((Scheme.Modules.pullback f).obj F) hV.opensRange_fromSpec.ge hV.fromSpec_preimage_self.ge
    hV.fromSpec_preimage_self.le
  have h4 := bijective_app_of_isIso _ ((Scheme.Modules.pullbackComp hV.fromSpec f).hom.app F) ⊤
  have h3 := bijective_app_of_isIso _ ((Scheme.Modules.pullbackCongr
    (hU.SpecMap_appLE_fromSpec f hV hUV).symm).hom.app F) ⊤
  have h2 := bijective_app_of_isIso _ ((Scheme.Modules.pullbackComp (Spec.map (f.appLE U V hUV))
    hU.fromSpec).inv.app F) ⊤
  have h1 := bijective_app_of_isIso _ ((Scheme.Modules.pullback (Spec.map (f.appLE U V hUV))).map
      ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).inv.app F)) ⊤
  exact h1.comp (h2.comp (h3.comp (h4.comp h5)))


lemma affineTargetMap_comm (s : Γ(F, U)) :
    affineTargetMap f F hU hV hUV (pullbackSectionLE f F hUV s) =
      originalSpecPullbackUnitTop (f.appLE U V hUV) (F.restrict hU.fromSpec)
        (affineSourceMap F hU s) := by
  have h₁ : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h₂ : (⊤ : (Spec Γ(Y, V)).Opens) ≤ Spec.map (f.appLE U V hUV) ⁻¹ᵁ ⊤ := le_top
  have e5 := pullbackSectionLE_comp f F hV.fromSpec hUV hV.fromSpec_preimage_self.ge s
  have e3 := pullbackSectionLE_congr F (hU.SpecMap_appLE_fromSpec f hV hUV).symm
    (hV.fromSpec_preimage_self.ge.trans (hV.fromSpec.preimage_mono hUV))
    (h₂.trans ((Spec.map (f.appLE U V hUV)).preimage_mono h₁)) s
  have e2 := pullbackSectionLE_comp hU.fromSpec F (Spec.map (f.appLE U V hUV)) h₁ h₂ s
  have e1 := pullbackSectionLE_naturality (Spec.map (f.appLE U V hUV))
    ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).inv.app F) h₂
    (pullbackSectionLE hU.fromSpec F h₁ s)
  simp only [affineTargetMap, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [e5, natIso_hom_app_inv_app, e3, ← e2, ← e1]
  rfl


lemma appLE_fromSpec_top (W : X.Opens) (hW : IsAffineOpen W) :
    hW.fromSpec.appLE W ⊤ hW.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso Γ(X, W)).inv := by
  rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, W)).presheaf.map_id _

lemma affineSourceMap_smul (r : Γ(X, U)) (s : Γ(F, U)) :
    affineSourceMap F hU (r • s) =
      (Scheme.ΓSpecIso Γ(X, U)).inv r • affineSourceMap F hU s := by
  simp only [affineSourceMap, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [pullbackSectionLE_smul, appLE_fromSpec_top]
  exact Scheme.Modules.Hom.app_smul _ _ _

lemma affineTargetMap_smul (t : Γ(Y, V)) (n : Γ((Scheme.Modules.pullback f).obj F, V)) :
    affineTargetMap f F hU hV hUV (t • n) =
      (Scheme.ΓSpecIso Γ(Y, V)).inv t • affineTargetMap f F hU hV hUV n := by
  simp only [affineTargetMap, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [pullbackSectionLE_smul, appLE_fromSpec_top]
  simp only [Scheme.Modules.Hom.app_smul]

variable {f hUV} in
/-- The `Γ(X, U)`-linear section map `s ↦ f^*s|_V`, for any algebra structure of `Γ(Y, V)` over
`Γ(X, U)` given by `f^♯` and any compatible module structure. -/
noncomputable def pullbackSectionLinear [Algebra Γ(X, U) Γ(Y, V)]
    [Module Γ(X, U) Γ((Scheme.Modules.pullback f).obj F, V)]
    [IsScalarTower Γ(X, U) Γ(Y, V) Γ((Scheme.Modules.pullback f).obj F, V)]
    (hθ : algebraMap Γ(X, U) Γ(Y, V) = (f.appLE U V hUV).hom) :
    Γ(F, U) →ₗ[Γ(X, U)] Γ((Scheme.Modules.pullback f).obj F, V) where
  toFun := pullbackSectionLE f F hUV
  map_add' := map_add _
  map_smul' r s := by
    rw [pullbackSectionLE_smul, RingHom.id_apply, ← algebraMap_smul Γ(Y, V) r, hθ]

variable [F.IsQuasicoherent]

include hU hV in
/-- **Pullback of a quasi-coherent module between affine opens**: for `f : Y → X`, affine opens
`U ⊆ X`, `V ⊆ Y` with `f(V) ⊆ U` and `F` quasi-coherent, `s ↦ f^*s|_V` exhibits `Γ(V, f^*F)` as
the base change `Γ(Y, V) ⊗_{Γ(X, U)} Γ(U, F)`. -/
theorem isBaseChange_pullbackSectionLinear [instA : Algebra Γ(X, U) Γ(Y, V)]
    [instM : Module Γ(X, U) Γ((Scheme.Modules.pullback f).obj F, V)]
    [IsScalarTower Γ(X, U) Γ(Y, V) Γ((Scheme.Modules.pullback f).obj F, V)]
    (hθ : algebraMap Γ(X, U) Γ(Y, V) = (f.appLE U V hUV).hom) :
    IsBaseChange Γ(Y, V) (pullbackSectionLinear F hθ) := by
  have hA : instA = (f.appLE U V hUV).hom.toAlgebra :=
    Algebra.algebra_ext _ _ fun r => congrFun (congrArg DFunLike.coe hθ) r
  subst hA
  let _ : Algebra Γ(X, U) Γ(Y, V) := (f.appLE U V hUV).hom.toAlgebra
  have hM : instM = Module.compHom _ (f.appLE U V hUV).hom :=
    Module.ext' _ _ fun r n => (algebraMap_smul Γ(Y, V) r n).symm
  subst hM
  let _ : Module Γ(X, U) Γ((Scheme.Modules.pullback f).obj F, V) :=
    Module.compHom _ (f.appLE U V hUV).hom
  let N := F.restrict hU.fromSpec
  let θ := f.appLE U V hUV
  let P := moduleSpecΓFunctor.obj N
  let Q := moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map θ)).obj N)
  let _ : Module Γ(X, U) Q := Module.compHom Q θ.hom
  have : IsScalarTower Γ(X, U) Γ(Y, V) Q := ⟨fun r t q => mul_smul (θ r) t q⟩
  let e₀ : Γ(Y, V) ⊗[Γ(X, U)] P ≃ₗ[Γ(Y, V)] Q :=
    (originalSpecPullbackSectionsIso θ N).toLinearEquiv
  let ρ₀ : P →ₗ[Γ(X, U)] Q :=
    { toFun := fun x => e₀ (1 ⊗ₜ x)
      map_add' := fun x y => by rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun r x => by
        have h : (1 : Γ(Y, V)) ⊗ₜ[Γ(X, U)] (r • x) = θ r • ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U)] x) := by
          rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul,
            mul_one, mul_one]
          rfl
        change e₀ ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U)] (r • x)) = θ r • e₀ (1 ⊗ₜ x)
        rw [h, map_smul] }
  have hρ₀ : IsBaseChange Γ(Y, V) ρ₀ := IsBaseChange.of_equiv e₀ fun x => rfl
  let eM₀ : Γ(F, U) →ₗ[Γ(X, U)] P :=
    { toFun := affineSourceMap F hU
      map_add' := map_add _
      map_smul' := fun r s => affineSourceMap_smul F hU r s }
  let eM : Γ(F, U) ≃ₗ[Γ(X, U)] P := LinearEquiv.ofBijective eM₀ (bijective_affineSourceMap F hU)
  let eN₀ : Γ((Scheme.Modules.pullback f).obj F, V) →ₗ[Γ(Y, V)] Q :=
    { toFun := affineTargetMap f F hU hV hUV
      map_add' := map_add _
      map_smul' := fun t n => affineTargetMap_smul f F hU hV hUV t n }
  let eN : Γ((Scheme.Modules.pullback f).obj F, V) ≃ₗ[Γ(Y, V)] Q :=
    LinearEquiv.ofBijective eN₀ (bijective_affineTargetMap f F hU hV hUV)
  have hcomm : ρ₀ ∘ₗ (eM : Γ(F, U) →ₗ[Γ(X, U)] P) =
      ((eN.restrictScalars Γ(X, U)) : Γ((Scheme.Modules.pullback f).obj F, V) →ₗ[Γ(X, U)] Q) ∘ₗ
        pullbackSectionLinear F hθ :=
    LinearMap.ext fun s => by
      change e₀ ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U)] (affineSourceMap F hU s : P)) =
        affineTargetMap f F hU hV hUV (pullbackSectionLE f F hUV s)
      exact (originalSpecPullbackSectionsIso_one_tmul θ N _).trans
        (affineTargetMap_comm f F hU hV hUV s).symm
  exact (IsBaseChange.iff_of_equiv_comm eM eN hcomm).mpr hρ₀

end AffinePullback

section SchemeBaseChange

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of A))

/-- The first projection `X_B = X ×_{Spec A} Spec B → X`. -/
noncomputable abbrev bcFst : pullback p (Spec.map (CommRingCat.ofHom φ)) ⟶ X := pullback.fst _ _

/-- The second projection `X_B → Spec B`. -/
noncomputable abbrev bcSnd : pullback p (Spec.map (CommRingCat.ofHom φ)) ⟶ Spec (CommRingCat.of B) :=
  pullback.snd _ _

theorem isPushout_baseChange_sections {U : X.Opens} (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom φ) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appLE ⊤ U le_top)
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (bcSnd φ p).appLE ⊤ (bcFst φ p ⁻¹ᵁ U) le_top)
      ((bcFst φ p).appLE U (bcFst φ p ⁻¹ᵁ U) le_rfl) := by
  have H := IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom φ))
  have hUY : bcFst φ p ⁻¹ᵁ U = bcFst φ p ⁻¹ᵁ U ⊓ bcSnd φ p ⁻¹ᵁ ⊤ := by simp
  have h := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U)
    (hUST := le_top) (hUSX := le_top) hUY (isAffineOpen_top _) (isAffineOpen_top _) hU
  have h' := (isIso_pushoutSection_iff H _ _ hUY).mp h
  refine h'.flip.of_iso (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← Scheme.ΓSpecIso_naturality]
    rfl
  · simp
  · simp
  · simp


/-- The structure coefficients `A → Γ(X, 𝒪_X)` of a morphism `p : X → Spec A`. -/
noncomputable def structureCoeff {Z : Scheme.{u}} (p : Z ⟶ Spec (CommRingCat.of A)) :
    A →+* Γ(Z, ⊤) :=
  p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

lemma structureCoeff_bc (a : A) :
    (bcFst φ p).appTop (structureCoeff p a) = structureCoeff (bcSnd φ p) (φ a) := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ (bcFst φ p).appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (bcSnd φ p).appTop := by
    rw [← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop,
      Scheme.ΓSpecIso_inv_naturality_assoc]
  exact ConcreteCategory.congr_hom h a

variable (F : X.Modules)

/-- `s ↦ q^*s : Γ(U, F) → Γ(q⁻¹U, q^*F)`, linear over `φ` for the structure coefficients. -/
noncomputable def baseChangeSectionsLinear (U : X.Opens) :
    sectionsModuleCat F (structureCoeff p) U le_top ⟶
      (ModuleCat.restrictScalars φ).obj (sectionsModuleCat
        ((Scheme.Modules.pullback (bcFst φ p)).obj F) (structureCoeff (bcSnd φ p))
        (bcFst φ p ⁻¹ᵁ U) le_top) :=
  ModuleCat.ofHom (X := sectionsModuleCat F (structureCoeff p) U le_top)
    (Y := (ModuleCat.restrictScalars φ).obj (sectionsModuleCat
        ((Scheme.Modules.pullback (bcFst φ p)).obj F) (structureCoeff (bcSnd φ p))
        (bcFst φ p ⁻¹ᵁ U) le_top))
    { toFun := fun s => pullbackSection (bcFst φ p) F U s
      map_add' := fun s t => map_add (pullbackSection (bcFst φ p) F U) s t
      map_smul' := fun a s => by
        change pullbackSection (bcFst φ p) F U
            (sectionsRingHom (structureCoeff p) (le_top : U ≤ ⊤) a • (show Γ(F, U) from s)) =
          sectionsRingHom (structureCoeff (bcSnd φ p)) (le_top : bcFst φ p ⁻¹ᵁ U ≤ ⊤) (φ a) •
            pullbackSection (bcFst φ p) F U s
        rw [pullbackSection_smul]
        congr 1
        simp only [sectionsRingHom, RingHom.coe_comp, Function.comp_apply]
        rw [← structureCoeff_bc, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality,
          ConcreteCategory.comp_apply]
        rfl }


/-- The base-change map `B ⊗_A Γ(U, F) → Γ(q⁻¹U, q^*F)`, `b ⊗ s ↦ b · q^*s`
(blueprint `prop:sm-cech-base-change`). -/
noncomputable def baseChangeSectionsMap (U : X.Opens) :
    (ModuleCat.extendScalars.{u, u, u} φ).obj (sectionsModuleCat F (structureCoeff p) U le_top) ⟶
      sectionsModuleCat ((Scheme.Modules.pullback (bcFst φ p)).obj F)
        (structureCoeff (bcSnd φ p)) (bcFst φ p ⁻¹ᵁ U) le_top :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ (baseChangeSectionsLinear φ p F U)

omit [CommRing A] [CommRing B] in
lemma pullbackSectionLE_self {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules) (W : Z.Opens)
    (s : Γ(M, W)) : pullbackSectionLE f M (le_refl (f ⁻¹ᵁ W)) s = pullbackSection f M W s := by
  rw [pullbackSectionLE_apply]
  change ((Scheme.Modules.pullback f).obj M).presheaf.map (𝟙 _) _ = _
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma bcFst_app_sectionsRingHom (U : X.Opens) (a : A) :
    (bcFst φ p).app U (sectionsRingHom (structureCoeff p) (le_top : U ≤ ⊤) a) =
      sectionsRingHom (structureCoeff (bcSnd φ p)) (le_top : bcFst φ p ⁻¹ᵁ U ≤ ⊤) (φ a) := by
  simp only [sectionsRingHom, RingHom.coe_comp, Function.comp_apply]
  rw [← structureCoeff_bc, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality,
    ConcreteCategory.comp_apply]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The first projection of a base change along `Spec B → Spec A` is affine. -/
instance isAffineHom_bcFst : IsAffineHom (bcFst φ p) :=
  MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom φ)))

variable {φ p F} in
theorem bijective_baseChangeSectionsMap [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (baseChangeSectionsMap φ p F U) := by
  have hV : IsAffineOpen (bcFst φ p ⁻¹ᵁ U) := hU.preimage _
  let _ : Algebra A Γ(X, U) := (sectionsRingHom (structureCoeff p) (le_top : U ≤ ⊤)).toAlgebra
  let _ : Algebra B Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), bcFst φ p ⁻¹ᵁ U) :=
    (sectionsRingHom (structureCoeff (bcSnd φ p)) (le_top : bcFst φ p ⁻¹ᵁ U ≤ ⊤)).toAlgebra
  let _ : Algebra Γ(X, U) Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), bcFst φ p ⁻¹ᵁ U) :=
    ((bcFst φ p).appLE U (bcFst φ p ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  let _ : Algebra A B := φ.toAlgebra
  let _ : Algebra A Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), bcFst φ p ⁻¹ᵁ U) :=
    ((algebraMap Γ(X, U) Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), bcFst φ p ⁻¹ᵁ U)).comp
      (algebraMap A Γ(X, U))).toAlgebra
  have : IsScalarTower A Γ(X, U) Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), bcFst φ p ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A B Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), bcFst φ p ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change (bcFst φ p).appLE U _ le_rfl _ = _
      rw [Scheme.Hom.appLE_eq_app]
      exact bcFst_app_sectionsRingHom φ p U a
  have : Algebra.IsPushout A B Γ(X, U)
      Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), bcFst φ p ⁻¹ᵁ U) := by
    rw [← CommRingCat.isPushout_iff_isPushout]
    exact isPushout_baseChange_sections φ p hU
  -- modules
  let _ : Module A Γ(F, U) := Module.compHom _ (algebraMap A Γ(X, U))
  have : IsScalarTower A Γ(X, U) Γ(F, U) := ⟨fun a r m => mul_smul (algebraMap A Γ(X, U) a) r m⟩
  let N := Γ((Scheme.Modules.pullback (bcFst φ p)).obj F, bcFst φ p ⁻¹ᵁ U)
  let S' := Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), bcFst φ p ⁻¹ᵁ U)
  let _ : Module Γ(X, U) N := Module.compHom N (algebraMap Γ(X, U) S')
  have : IsScalarTower Γ(X, U) S' N := ⟨fun r t n => mul_smul (algebraMap Γ(X, U) S' r) t n⟩
  let _ : Module B N := Module.compHom N (algebraMap B S')
  have : IsScalarTower B S' N := ⟨fun b t n => mul_smul (algebraMap B S' b) t n⟩
  have hρ := isBaseChange_pullbackSectionLinear (bcFst φ p) F hU hV le_rfl
    (instA := inferInstance) (instM := inferInstance) rfl
  let e₁ := Algebra.IsPushout.cancelBaseChange A B Γ(X, U) S' Γ(F, U)
  let e₂ := hρ.equiv.restrictScalars B
  let e := e₁.symm.trans e₂
  have key : ∀ x, baseChangeSectionsMap φ p F U x = e x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero e).symm
    | tmul b m =>
      have h1 : e₁.symm ((show B from b) ⊗ₜ[A] (show Γ(F, U) from m)) =
          algebraMap B S' (show B from b) ⊗ₜ[Γ(X, U)] (show Γ(F, U) from m) :=
        Algebra.IsPushout.cancelBaseChange_symm_tmul A B Γ(X, U) S' Γ(F, U) b m
      have h2 : hρ.equiv (algebraMap B S' (show B from b) ⊗ₜ[Γ(X, U)] (show Γ(F, U) from m)) =
          algebraMap B S' (show B from b) •
            pullbackSectionLE (bcFst φ p) F (le_refl _) (show Γ(F, U) from m) :=
        IsBaseChange.equiv_tmul hρ _ _
      change (show B from b) • pullbackSection (bcFst φ p) F U (show Γ(F, U) from m) =
        hρ.equiv (e₁.symm ((show B from b) ⊗ₜ[A] (show Γ(F, U) from m)))
      rw [h1, h2, pullbackSectionLE_self]
      rfl
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add e x y).symm)
  have : ⇑(baseChangeSectionsMap φ p F U) = ⇑e := funext key
  rw [this]
  exact e.bijective

end SchemeBaseChange

section CechExtendScalars

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {ι : Type u} [LinearOrder ι]
  [Fintype ι] (D : Finset ι ⥤ ModuleCat.{u} A)

omit [Fintype ι] [LinearOrder ι] in
lemma subsetCechCardProductEquiv_symm_val {K : Type u} [CommRing K] (G : Finset ι ⥤ ModuleCat.{u} K)
    (n : ℕ) (f : ∀ S : {S : Finset ι // S.card = n}, G.obj S.val) (S : Finset ι)
    (h : S.card = n) : ((subsetCechCardProductEquiv G n).symm f).val S = f ⟨S, h⟩ := by
  change (if h : S.card = n then _ else 0) = _
  rw [dif_pos h]

omit [Fintype ι] [LinearOrder ι] in
lemma subsetCechCardProductEquiv_symm_val_of_ne {K : Type u} [CommRing K]
    (G : Finset ι ⥤ ModuleCat.{u} K) (n : ℕ) (f : ∀ S : {S : Finset ι // S.card = n}, G.obj S.val)
    (S : Finset ι) (h : S.card ≠ n) : ((subsetCechCardProductEquiv G n).symm f).val S = 0 :=
  ((subsetCechCardProductEquiv G n).symm f).property S h

/-- `B ⊗_A C^n(D) ≅ C^n(B ⊗_A D)` for the cardinality-`n` part of a subset Čech complex. -/
noncomputable def cardPieceBaseChangeEquiv (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u} φ).obj (ModuleCat.of A (subsetCechCardPiece D n)) ≃ₗ[B]
      subsetCechCardPiece (D ⋙ ModuleCat.extendScalars.{u, u, u} φ) n := by
  classical
  let _ : Algebra A B := φ.toAlgebra
  show B ⊗[A] (subsetCechCardPiece D n) ≃ₗ[B] _
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (subsetCechCardProductEquiv D n)) ≪≫ₗ
    TensorProduct.piRight A B B (fun S : {S : Finset ι // S.card = n} => D.obj S.val) ≪≫ₗ
    (subsetCechCardProductEquiv (D ⋙ ModuleCat.extendScalars.{u, u, u} φ) n).symm

lemma cardPieceBaseChangeEquiv_tmul (n : ℕ) (b : B) (x : subsetCechCardPiece D n) (S : Finset ι) :
    (cardPieceBaseChangeEquiv φ D n (b ⊗ₜ[A, φ] x)).val S = b ⊗ₜ[A, φ] (x.val S) := by
  classical
  by_cases h : S.card = n
  · exact subsetCechCardProductEquiv_symm_val _ n _ S h
  · rw [x.property S h, TensorProduct.tmul_zero]
    exact subsetCechCardProductEquiv_symm_val_of_ne _ n _ S h

/-- Base change commutes with subset Čech complexes. -/
noncomputable def subsetCechComplexBaseChangeIso :
    (baseChange φ).obj (subsetCechComplex D) ≅
      subsetCechComplex (D ⋙ ModuleCat.extendScalars.{u, u, u} φ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (cardPieceBaseChangeEquiv φ D (n + 1)).toModuleIso) (by
      intro n m h
      have hm : n + 1 = m := h
      subst hm
      have h1 : (subsetCechComplex (D ⋙ ModuleCat.extendScalars.{u, u, u} φ)).d n (n + 1) =
          ModuleCat.ofHom (subsetCechCardDifferential _ (n + 1)) := subsetCechComplex_d _ n
      have h2 : ((baseChange φ).obj (subsetCechComplex D)).d n (n + 1) =
          (ModuleCat.extendScalars.{u, u, u} φ).map
            (ModuleCat.ofHom (subsetCechCardDifferential D (n + 1))) := by
        rw [← subsetCechComplex_d]
        rfl
      rw [h1, h2]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change subsetCechCardDifferential (D ⋙ ModuleCat.extendScalars.{u, u, u} φ) (n + 1)
          (cardPieceBaseChangeEquiv φ D (n + 1) x) =
        cardPieceBaseChangeEquiv φ D (n + 1 + 1)
          ((ModuleCat.extendScalars.{u, u, u} φ).map
            (ModuleCat.ofHom (subsetCechCardDifferential D (n + 1))) x)
      induction x using TensorProduct.induction_on with
      | zero =>
        exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans
          ((congrArg _ (map_zero _)).trans (map_zero _)).symm
      | tmul b y =>
        revert y
        change ∀ y : subsetCechCardPiece D (n + 1),
          subsetCechCardDifferential (D ⋙ ModuleCat.extendScalars.{u, u, u} φ) (n + 1)
            (cardPieceBaseChangeEquiv φ D (n + 1) (b ⊗ₜ[A, φ] y)) =
          cardPieceBaseChangeEquiv φ D (n + 1 + 1)
            (b ⊗ₜ[A, φ] (subsetCechCardDifferential D (n + 1) y))
        intro y
        apply Subtype.ext
        funext S
        refine Eq.trans ?_ (cardPieceBaseChangeEquiv_tmul φ D (n + 1 + 1) b _ S).symm
        change (∑ i ∈ S, subsetCechSign S i •
            (D ⋙ ModuleCat.extendScalars.{u, u, u} φ).map (homOfLE (Finset.erase_subset i S))
              ((cardPieceBaseChangeEquiv φ D (n + 1) (b ⊗ₜ[A, φ] y)).val (S.erase i))) =
          b ⊗ₜ[A, φ] (∑ i ∈ S, subsetCechSign S i •
            D.map (homOfLE (Finset.erase_subset i S)) (y.val (S.erase i)))
        rw [TensorProduct.tmul_sum]
        apply Finset.sum_congr rfl
        intro i _
        refine (congrArg (fun z => subsetCechSign S i •
          ((D ⋙ ModuleCat.extendScalars.{u, u, u} φ).map (homOfLE (Finset.erase_subset i S))) z)
          (cardPieceBaseChangeEquiv_tmul φ D (n + 1) b y (S.erase i))).trans ?_
        exact (map_zsmul (TensorProduct.mk A ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))
          (D.obj S) b) (subsetCechSign S i) _).symm
      | add x y hx hy =>
        exact ((congrArg _ (map_add _ x y)).trans (map_add _ _ _)).trans
          ((congrArg₂ (· + ·) hx hy).trans
            ((congrArg _ (map_add _ x y)).trans (map_add _ _ _)).symm))

end CechExtendScalars

section CechBaseChange

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) {ι : Type u} [LinearOrder ι]
  (U : ι → X.Opens)

/-- The comparison `B ⊗_A Γ(U_T, F) ≅ Γ((q⁻¹U)_T, q^*F)` on nonempty `T`. -/
noncomputable def cechBaseChangeComponent [F.IsQuasicoherent]
    (hU : ∀ T : Finset ι, T.Nonempty → IsAffineOpen (T.inf U)) (T : Finset ι) (hT : T.Nonempty) :
    (cechDiagram F U (structureCoeff p) ⋙ ModuleCat.extendScalars.{u, u, u} φ).obj T ≅
      (cechDiagram ((Scheme.Modules.pullback (bcFst φ p)).obj F) (fun i => bcFst φ p ⁻¹ᵁ U i)
        (structureCoeff (bcSnd φ p))).obj T :=
  (LinearEquiv.ofBijective (baseChangeSectionsMap φ p F (T.inf U)).hom
      (bijective_baseChangeSectionsMap (hU T hT))).toModuleIso ≪≫
    (LinearEquiv.ofBijective
      (sectionsRestrict ((Scheme.Modules.pullback (bcFst φ p)).obj F) (structureCoeff (bcSnd φ p))
        (le_top : bcFst φ p ⁻¹ᵁ (T.inf U) ≤ ⊤) le_top
        (preimage_finsetInf (bcFst φ p) U T).ge).hom
      (sectionsRestrict_bijective_of_eq _ _ _ _ (preimage_finsetInf (bcFst φ p) U T).symm)).toModuleIso

omit [LinearOrder ι] in
lemma sectionsRingHom_res {Y : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(Y, ⊤))
    {V W : Y.Opens} (h : W ≤ V) (r : R) :
    Y.presheaf.map (homOfLE h).op (sectionsRingHom c (le_top : V ≤ ⊤) r) =
      sectionsRingHom c (le_top : W ≤ ⊤) r := by
  simp only [sectionsRingHom, RingHom.coe_comp, Function.comp_apply]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma cechBaseChangeComponent_naturality [F.IsQuasicoherent]
    (hU : ∀ T : Finset ι, T.Nonempty → IsAffineOpen (T.inf U)) (S T : Finset ι) (hS : S.Nonempty)
    (hT : T.Nonempty) (hST : S ⊆ T) :
    (cechDiagram F U (structureCoeff p) ⋙ ModuleCat.extendScalars.{u, u, u} φ).map (homOfLE hST) ≫
        (cechBaseChangeComponent φ p F U hU T hT).hom =
      (cechBaseChangeComponent φ p F U hU S hS).hom ≫
        (cechDiagram ((Scheme.Modules.pullback (bcFst φ p)).obj F) (fun i => bcFst φ p ⁻¹ᵁ U i)
          (structureCoeff (bcSnd φ p))).map (homOfLE hST) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro s
  · let b : B := 1
    let q := bcFst φ p
    let G := (Scheme.Modules.pullback q).obj F
    have hT' := (preimage_finsetInf q U T).ge
    have hS' := (preimage_finsetInf q U S).ge
    have hm : T.inf (fun i => q ⁻¹ᵁ U i) ≤ S.inf (fun i => q ⁻¹ᵁ U i) := Finset.inf_mono hST
    have hm' : T.inf U ≤ S.inf U := Finset.inf_mono hST
    revert s
    change ∀ (s : Γ(F, S.inf U)), G.presheaf.map (homOfLE hT').op
        (sectionsRingHom (structureCoeff (bcSnd φ p)) (le_top : q ⁻¹ᵁ T.inf U ≤ ⊤) b •
          pullbackSection q F (T.inf U) (F.presheaf.map (homOfLE hm').op s)) =
      G.presheaf.map (homOfLE hm).op (G.presheaf.map (homOfLE hS').op
        (sectionsRingHom (structureCoeff (bcSnd φ p)) (le_top : q ⁻¹ᵁ S.inf U ≤ ⊤) b •
          pullbackSection q F (S.inf U) s))
    intro s
    rw [presheaf_map_map G hS' hm (hm.trans hS'), Scheme.Modules.map_smul,
      Scheme.Modules.map_smul, sectionsRingHom_res, sectionsRingHom_res,
      ← pullbackSection_restrict, presheaf_map_map]

/-- **Base change of the Čech complex** (blueprint `prop:sm-cech-base-change`): for a family of
opens of `X → Spec A` with affine nonempty intersections and `F` quasi-coherent,
`Č(U, F) ⊗_A B ≅ Č(q⁻¹U, q^*F)` on `X_B = X ×_A Spec B`. -/
noncomputable def cechComplexBaseChangeIso [Fintype ι] [F.IsQuasicoherent]
    (hU : ∀ T : Finset ι, T.Nonempty → IsAffineOpen (T.inf U)) :
    (baseChange φ).obj (cechComplex F U (structureCoeff p)) ≅
      cechComplex ((Scheme.Modules.pullback (bcFst φ p)).obj F) (fun i => bcFst φ p ⁻¹ᵁ U i)
        (structureCoeff (bcSnd φ p)) :=
  subsetCechComplexBaseChangeIso φ (cechDiagram F U (structureCoeff p)) ≪≫
    SubsetNonemptyComparison.complexIso _ _ (cechBaseChangeComponent φ p F U hU)
      (cechBaseChangeComponent_naturality φ p F U hU)

end CechBaseChange

end

end DeJongAlterations.StableModification.Cohomology
