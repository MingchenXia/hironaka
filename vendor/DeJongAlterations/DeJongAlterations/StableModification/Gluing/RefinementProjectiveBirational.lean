/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45A)
-/
import DeJongAlterations.StableModification.RiemannZariski.Refinement
import DeJongAlterations.Modification

/-!
# Refinements over the function field are modifications

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §3.2
(T:2300–2312): an `L`-modification of an integral scheme `S` with `L = K(S)` is a modification
(proper and birational), and the pieces `Wᵢ → Tᵢ` of the refinement in Proposition 3.2.6 are
`L`-modifications of the affine quasi-modifications `Tᵢ`. The integrated RZ1 files record
properness only. This file supplies the birationality (blueprint `sm-gluing-semistable.tex`,
`lem:sm-refinement-birational`; part of `PLAN-T5.md` node A2):

* `birationalOver_of_isIso_resLE`, `birationalOver_of_bijective_appLE`: a morphism of integral
  schemes restricting to an isomorphism between nonempty opens is birational;
* `exists_affine_mem_range`, `birationalOver_of_hasCharts`, `isModification_of_hasCharts`: a
  refinement of the generic point `Spec K(S) → S` with charts with respect to a finite set is a
  modification (over an affine `V` on which the finitely many chart generators are sections, the
  chart `W ⊆ p⁻¹ V` maps isomorphically onto `V`);
* `injective_sectionsToField`, `mem_basicOpen_iff_sectionsToField_ne_zero`,
  `sectionsToField_res`: section maps of a point hitting the generic point;
* `birationalOver_of_locallyOfFiniteType`: a morphism locally of finite type between integral
  schemes which induces an isomorphism of function fields (in the form: `L` is the fraction field
  of the section ring of an affine open of the target) is birational (after clearing the
  denominators of finitely many generators).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace DeJongAlterations.StableModification.Gluing

open RiemannZariskiSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Birational

/-- A morphism of affine schemes inducing an isomorphism on global sections is an isomorphism. -/
theorem isIso_of_isAffine_of_isIso_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsIso f.appTop] : IsIso f := by
  have : f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv := by
    rw [Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this]
  infer_instance

/-- **Birationality from one isomorphism between nonempty opens.** If a morphism of integral
schemes restricts to an isomorphism from a nonempty open `W` onto a nonempty open `U`, it is
birational. -/
theorem birationalOver_of_isIso_resLE {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) {U : Y.Opens} {W : X.Opens} (hWU : W ≤ f ⁻¹ᵁ U) (hU : (U : Set Y).Nonempty)
    (hW : (W : Set X).Nonempty) [IsIso (f.resLE U W hWU)] : Scheme.BirationalOver f (𝟙 Y) := by
  refine ⟨⟨W, W.isOpen.dense hW, U, U.isOpen.dense hU, asIso (f.resLE U W hWU)⟩, ?_⟩
  change f.resLE U W hWU ≫ U.ι ≫ 𝟙 Y = W.ι ≫ f
  rw [Category.comp_id, Scheme.Hom.resLE_comp_ι]

/-- **Birationality from a bijective section map**: if `f.appLE U W` is bijective for nonempty
affine opens `U ⊆ Y`, `W ⊆ f⁻¹ U` of integral schemes, `f` is birational. -/
theorem birationalOver_of_bijective_appLE {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) {U : Y.Opens} {W : X.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (hWU : W ≤ f ⁻¹ᵁ U) (hUn : (U : Set Y).Nonempty) (hWn : (W : Set X).Nonempty)
    (hbij : Function.Bijective (f.appLE U W hWU)) : Scheme.BirationalOver f (𝟙 Y) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine W.toScheme := hW
  have : IsIso (f.appLE U W hWU) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have : IsIso (f.resLE U W hWU).appTop := by
    change IsIso ((f.resLE U W hWU).app ⊤)
    rw [Scheme.Hom.resLE_app_top]
    infer_instance
  have : IsIso (f.resLE U W hWU) := isIso_of_isAffine_of_isIso_appTop _
  exact birationalOver_of_isIso_resLE f hWU hUn hWn

variable {S S' : Scheme.{u}} [IsIntegral S]

/-- Finitely many rational functions are sections over one nonempty affine open. -/
theorem exists_affine_mem_range {F : Set S.functionField} (hF : F.Finite) :
    ∃ (V : S.Opens) (hV : IsAffineOpen V) (hgV : genericPoint S ∈ V), ∀ x ∈ F,
      x ∈ (sectionsToField (functionFieldPoint S S.functionField) V
        (functionFieldPoint_preimage hV hgV)).range := by
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hg₀, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint S)) isOpen_univ
  have : Nonempty V₀ := ⟨⟨_, hg₀⟩⟩
  have : IsFractionRing Γ(S, V₀) S.functionField :=
    functionField_isFractionRing_of_isAffineOpen S V₀ hV₀
  choose a b hb hab using fun x : F ↦ IsFractionRing.div_surjective (A := Γ(S, V₀)) x.1
  have := hF.fintype
  let c : Γ(S, V₀) := ∏ x : F, b x
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ ↦ nonZeroDivisors.ne_zero (hb x)
  have hV₁ : IsAffineOpen (S.basicOpen c) := hV₀.basicOpen c
  have hne : (S.basicOpen c : Set S).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ← TopologicalSpace.Opens.coe_bot, Ne,
      TopologicalSpace.Opens.coe_inj, basicOpen_eq_bot_iff]
    exact hc0
  have hg₁ : genericPoint S ∈ S.basicOpen c :=
    ((genericPoint_spec S).mem_open_set_iff (S.basicOpen c).isOpen).2 (by simpa using hne)
  refine ⟨S.basicOpen c, hV₁, hg₁, fun x hx ↦ ?_⟩
  set s₁ := sectionsToField (functionFieldPoint S S.functionField) (S.basicOpen c)
    (functionFieldPoint_preimage hV₁ hg₁)
  let ρ := S.presheaf.map (homOfLE (S.basicOpen_le c)).op
  have hρ : ∀ y, s₁ (ρ y) = algebraMap Γ(S, V₀) S.functionField y := by
    intro y
    rw [show s₁ = _ from sectionsToField_functionFieldPoint hV₁ hg₁, RingHom.comp_apply]
    change (S.presheaf.germ (S.basicOpen c) (genericPoint S) hg₁ ≫ 𝟙 _) (ρ y) = _
    rw [Category.comp_id, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
    rfl
  have hunit : IsUnit (ρ (b ⟨x, hx⟩)) := by
    refine isUnit_of_dvd_unit (map_dvd ρ.hom ?_) (S.toRingedSpace.isUnit_res_basicOpen c)
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
  obtain ⟨u, hu⟩ := hunit
  refine ⟨ρ (a ⟨x, hx⟩) * ↑u⁻¹, ?_⟩
  rw [map_mul, hρ, map_units_inv, hu, hρ, ← div_eq_mul_inv]
  exact hab ⟨x, hx⟩

/-- **A refinement over the function field is a modification** (`PLAN-T5.md` node A2, for a
`K(S)`-modification, Temkin T:2305–2309): if `S` is integral and `(S', p, η')` is a refinement of
the generic point `Spec K(S) → S` with charts with respect to a finite set, `p` is birational. -/
theorem birationalOver_of_hasCharts {p : S' ⟶ S}
    {η' : Spec (.of S.functionField) ⟶ S'}
    (hR : IsRefinement (functionFieldPoint S S.functionField) p η') {F : Set S.functionField}
    (hF : F.Finite) (hC : HasCharts (functionFieldPoint S S.functionField) p η' F) :
    Scheme.BirationalOver p (𝟙 S) := by
  have := hR.isIntegral
  obtain ⟨V, hV, hgV, hFV⟩ := exists_affine_mem_range (S := S) hF
  have hηV := functionFieldPoint_preimage (L := S.functionField) hV hgV
  obtain ⟨W, hW, hη'W, hWV, hinj, hrange⟩ := hC V hV hηV
  set sV := sectionsToField (functionFieldPoint S S.functionField) V hηV
  set sW := sectionsToField η' W hη'W
  have hcomp : sW.comp (p.appLE V W hWV).hom = sV :=
    sectionsToField_comp_appLE p hR.comp_eq hWV hη'W hηV
  have hrange' : sW.range = sV.range := by
    rw [hrange]
    exact sup_eq_left.mpr (Subring.closure_le.mpr fun x hx ↦ hFV x hx)
  have hsV : Function.Injective sV := injective_sectionsToField_functionFieldPoint hV hgV
  have hbij : Function.Bijective (p.appLE V W hWV) := by
    refine ⟨fun a b h ↦ hsV ?_, fun w ↦ ?_⟩
    · rw [← hcomp, RingHom.comp_apply, RingHom.comp_apply]
      exact congrArg sW h
    · obtain ⟨v, hv⟩ : sW w ∈ sV.range := hrange' ▸ ⟨w, rfl⟩
      refine ⟨v, hinj ?_⟩
      rw [← hv, ← hcomp]
      rfl
  have hWn : (W : Set S').Nonempty := by
    obtain ⟨z⟩ : Nonempty (Spec (.of S.functionField)) := inferInstance
    have : z ∈ η' ⁻¹ᵁ W := by rw [hη'W]; trivial
    exact ⟨η' z, this⟩
  exact birationalOver_of_bijective_appLE p hV hW hWV ⟨_, hgV⟩ hWn hbij

/-- **A refinement over the function field is a modification.** -/
theorem isModification_of_hasCharts {p : S' ⟶ S}
    {η' : Spec (.of S.functionField) ⟶ S'}
    (hR : IsRefinement (functionFieldPoint S S.functionField) p η') {F : Set S.functionField}
    (hF : F.Finite) (hC : HasCharts (functionFieldPoint S S.functionField) p η' F) :
    IsModification p :=
  { toIsProper := hR.isProper
    sourceIntegral := hR.isIntegral
    targetIntegral := inferInstance
    birational := birationalOver_of_hasCharts hR hF hC }

end Birational

section BirationalLFT

variable {L : Type u} [Field L] {X Y : Scheme.{u}}

/-- The section map of a field point is the germ followed by the local map at the point. -/
theorem sectionsToField_eq_stalkClosedPointTo (η : Spec (.of L) ⟶ X) {U : X.Opens}
    (hU : η ⁻¹ᵁ U = ⊤) (h : η (IsLocalRing.closedPoint L) ∈ U) (r : Γ(X, U)) :
    sectionsToField η U hU r =
      (Scheme.stalkClosedPointTo η).hom (X.presheaf.germ U _ h r) := by
  have h1 : η.appLE U ⊤ hU.ge ≫ (Scheme.ΓSpecIso (.of L)).hom =
      X.presheaf.germ U _ h ≫ Scheme.stalkClosedPointTo η := by
    rw [Scheme.germ_stalkClosedPointTo, Scheme.Hom.appLE]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Category.assoc]
    rfl
  change (η.appLE U ⊤ hU.ge ≫ (Scheme.ΓSpecIso (.of L)).hom) r = _
  rw [h1]
  rfl

/-- **Section maps of the generic point are injective**: if `η : Spec L → X` hits the generic
point of the integral scheme `X`, the section map `Γ(X, U) → L` is injective for every open `U`
through which `η` factors. -/
theorem injective_sectionsToField [IsIntegral X] (η : Spec (.of L) ⟶ X)
    (hη : ∀ z, η z = genericPoint X) {U : X.Opens} (hU : η ⁻¹ᵁ U = ⊤) :
    Function.Injective (sectionsToField η U hU) := by
  have h : η (IsLocalRing.closedPoint L) ∈ U := by
    have : IsLocalRing.closedPoint L ∈ η ⁻¹ᵁ U := by rw [hU]; trivial
    exact this
  have hfield : IsField (X.presheaf.stalk (η (IsLocalRing.closedPoint L))) := by
    refine isField_stalk_of_closure_mem_irreducibleComponents X _ ?_
    rw [hη, (genericPoint_spec X).def, irreducibleComponents_eq_singleton]
    rfl
  let := hfield.toField
  have hinj : Function.Injective (Scheme.stalkClosedPointTo η).hom := RingHom.injective _
  intro a b hab
  rw [sectionsToField_eq_stalkClosedPointTo η hU h, sectionsToField_eq_stalkClosedPointTo η hU h]
    at hab
  exact germ_injective_of_isIntegral X _ h (hinj hab)

/-- A field point lies in the basic open of a section iff the section map does not kill it. -/
theorem mem_basicOpen_iff_sectionsToField_ne_zero (η : Spec (.of L) ⟶ X) {U : X.Opens}
    (hU : η ⁻¹ᵁ U = ⊤) (r : Γ(X, U)) (z : Spec (.of L)) :
    η z ∈ X.basicOpen r ↔ sectionsToField η U hU r ≠ 0 := by
  have hz : z = IsLocalRing.closedPoint L := Subsingleton.elim (h := inferInstanceAs
    (Subsingleton (PrimeSpectrum L))) _ _
  subst hz
  have h : η (IsLocalRing.closedPoint L) ∈ U := by
    have : IsLocalRing.closedPoint L ∈ η ⁻¹ᵁ U := by rw [hU]; trivial
    exact this
  rw [sectionsToField_eq_stalkClosedPointTo η hU h, X.mem_basicOpen r _ h]
  constructor
  · intro hu h0
    have := hu.map (Scheme.stalkClosedPointTo η).hom
    rw [h0] at this
    exact not_isUnit_zero this
  · intro h0
    by_contra hnu
    have := map_nonunit (Scheme.stalkClosedPointTo η).hom _
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at this
    exact h0 this

/-- Section maps are compatible with restriction. -/
theorem sectionsToField_res (η : Spec (.of L) ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (hV : η ⁻¹ᵁ V = ⊤) (hU : η ⁻¹ᵁ U = ⊤) (r : Γ(X, U)) :
    sectionsToField η V hV (X.presheaf.map (homOfLE hVU).op r) = sectionsToField η U hU r := by
  change ((X.presheaf.map (homOfLE hVU).op ≫ η.appLE V ⊤ hV.ge) ≫ _) r = _
  rw [Scheme.Hom.map_appLE]
  rfl

/-- **Birationality of a morphism of finite type inducing an isomorphism of function fields.**
Let `q : X → Y` be locally of finite type between integral schemes, `η : Spec L → X` a point
hitting the generic point of `X` with `q ∘ η` hitting the generic point of `Y`, and `U ⊆ Y` an
affine open whose section ring has fraction field `L` (via `q ∘ η`). Then `q` is birational: on a
basic open `D(c) ⊆ U` clearing the denominators of generators of `Γ(W)` (`W ⊆ q⁻¹ U` affine),
`q` restricts to an isomorphism `D_W(c) ≅ D(c)`. -/
theorem birationalOver_of_locallyOfFiniteType [IsIntegral X] [IsIntegral Y]
    (η : Spec (.of L) ⟶ X) (hη : ∀ z, η z = genericPoint X) (q : X ⟶ Y)
    [LocallyOfFiniteType q] (hηq : ∀ z, (η ≫ q) z = genericPoint Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (hηU : (η ≫ q) ⁻¹ᵁ U = ⊤)
    (hfrac : ∀ x : L, ∃ a b : Γ(Y, U), sectionsToField (η ≫ q) U hηU b ≠ 0 ∧
      x * sectionsToField (η ≫ q) U hηU b = sectionsToField (η ≫ q) U hηU a) :
    Scheme.BirationalOver q (𝟙 Y) := by
  classical
  obtain ⟨z⟩ : Nonempty (Spec (.of L)) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  set sU := sectionsToField (η ≫ q) U hηU
  have hξU : genericPoint X ∈ q ⁻¹ᵁ U := by
    rw [← hη z]
    have : z ∈ (η ≫ q) ⁻¹ᵁ U := by rw [hηU]; trivial
    exact this
  obtain ⟨_, ⟨W, hW, rfl⟩, hξW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hξU (q ⁻¹ᵁ U).isOpen
  have hηW : η ⁻¹ᵁ W = ⊤ := by
    ext z'
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    change η z' ∈ W
    rw [hη]
    exact hξW
  set sW := sectionsToField η W hηW
  have hcomp : sW.comp (q.appLE U W hWU).hom = sU :=
    sectionsToField_comp_appLE q rfl hWU hηW hηU
  -- generators of `Γ(W)` over `Γ(U)`
  let ρ := (q.appLE U W hWU).hom
  have hft : ρ.FiniteType := q.finiteType_appLE hU hW hWU
  let := ρ.toAlgebra
  obtain ⟨t, ht⟩ := (hft : Algebra.FiniteType Γ(Y, U) Γ(X, W)).out
  choose a b hb hab using fun w : t ↦ hfrac (sW w)
  let c : Γ(Y, U) := ∏ w : t, b w
  have hc : sU c ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun w _ ↦ hb w
  -- the basic opens
  have hU' : IsAffineOpen (Y.basicOpen c) := hU.basicOpen c
  have hηU' : (η ≫ q) ⁻¹ᵁ Y.basicOpen c = ⊤ := by
    ext z'
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact (mem_basicOpen_iff_sectionsToField_ne_zero (η ≫ q) hηU c z').mpr hc
  have hW' : IsAffineOpen (X.basicOpen (ρ c)) := hW.basicOpen (ρ c)
  have hW'U' : X.basicOpen (ρ c) ≤ q ⁻¹ᵁ Y.basicOpen c := by
    change X.basicOpen ((q.app U ≫ X.presheaf.map (homOfLE hWU).op) c) ≤ _
    rw [CommRingCat.comp_apply, Scheme.basicOpen_res, Scheme.preimage_basicOpen]
    exact inf_le_right
  have hηW' : η ⁻¹ᵁ X.basicOpen (ρ c) = ⊤ := by
    ext z'
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    refine (mem_basicOpen_iff_sectionsToField_ne_zero η hηW (ρ c) z').mpr ?_
    change (sW.comp ρ) c ≠ 0
    rw [hcomp]
    exact hc
  set sU' := sectionsToField (η ≫ q) (Y.basicOpen c) hηU'
  set sW' := sectionsToField η (X.basicOpen (ρ c)) hηW'
  have hsU' : Function.Injective sU' := injective_sectionsToField (η ≫ q) hηq hηU'
  have hsW' : Function.Injective sW' := injective_sectionsToField η hη hηW'
  have hcomp' : sW'.comp (q.appLE _ _ hW'U').hom = sU' :=
    sectionsToField_comp_appLE q rfl hW'U' hηW' hηU'
  have hresU : ∀ y : Γ(Y, U), sU' (Y.presheaf.map (homOfLE (Y.basicOpen_le c)).op y) = sU y :=
    fun y ↦ sectionsToField_res (η ≫ q) _ hηU' hηU y
  have hresW : ∀ w : Γ(X, W),
      sW' (X.presheaf.map (homOfLE (X.basicOpen_le (ρ c))).op w) = sW w :=
    fun w ↦ sectionsToField_res η _ hηW' hηW w
  -- `Γ(W)` lands in `s_{U'}(Γ(U'))`
  set R := sU'.range
  have hunitc : IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le c)).op c) :=
    Y.toRingedSpace.isUnit_res_basicOpen c
  have hinvc : (sU c)⁻¹ ∈ R := by
    refine ⟨↑(hunitc.unit⁻¹), ?_⟩
    rw [map_units_inv, IsUnit.unit_spec, hresU]
  have hA : ∀ y : Γ(Y, U), sU y ∈ R := fun y ↦ ⟨_, hresU y⟩
  have hgen : ∀ w ∈ (t : Set Γ(X, W)), sW w ∈ R := by
    intro w hw
    obtain ⟨d, hd⟩ : b ⟨w, hw⟩ ∣ c := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    have hbw := hb ⟨w, hw⟩
    have hd0 : sU d ≠ 0 := fun h ↦ hc (by rw [hd, map_mul, h, mul_zero])
    have hsw : sW w = sU (a ⟨w, hw⟩) * sU d * (sU c)⁻¹ := by
      rw [hd, map_mul, mul_inv, ← hab ⟨w, hw⟩]
      field_simp
    rw [hsw]
    exact mul_mem (mul_mem (hA _) (hA _)) hinvc
  have hall : ∀ w : Γ(X, W), sW w ∈ R := by
    intro w
    have hw : w ∈ Algebra.adjoin Γ(Y, U) (t : Set Γ(X, W)) := ht ▸ Algebra.mem_top
    induction hw using Algebra.adjoin_induction with
    | mem x hx => exact hgen x hx
    | algebraMap y =>
      change (sW.comp ρ) y ∈ R
      rw [hcomp]
      exact hA y
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  -- bijectivity on the basic opens
  have hbij : Function.Bijective (q.appLE _ _ hW'U') := by
    refine ⟨fun x y hxy ↦ hsU' ?_, fun w' ↦ ?_⟩
    · rw [← hcomp', RingHom.comp_apply, RingHom.comp_apply]
      exact congrArg sW' hxy
    · have hloc := hW.isLocalization_basicOpen (ρ c)
      obtain ⟨⟨r, m⟩, hr⟩ := IsLocalization.surj (Submonoid.powers (ρ c)) w'
      obtain ⟨n, hn⟩ := m.2
      have hm : sW' (algebraMap Γ(X, W) Γ(X, X.basicOpen (ρ c)) (m : Γ(X, W))) = sU c ^ n := by
        rw [← hn, map_pow, map_pow]
        change sW' (X.presheaf.map (homOfLE (X.basicOpen_le (ρ c))).op (ρ c)) ^ n = _
        rw [hresW]
        change ((sW.comp ρ) c) ^ n = _
        rw [hcomp]
      have hw' : sW' w' = sW r * ((sU c)⁻¹) ^ n := by
        have h1 := congrArg sW' hr
        rw [map_mul, hm] at h1
        change _ = sW' (X.presheaf.map (homOfLE (X.basicOpen_le (ρ c))).op r) at h1
        rw [hresW] at h1
        rw [← h1, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hc), mul_one]
      obtain ⟨v, hv⟩ : sW' w' ∈ R := by
        rw [hw']
        exact mul_mem (hall r) (pow_mem hinvc n)
      refine ⟨v, hsW' ?_⟩
      rw [← hv, ← hcomp']
      rfl
  have hUn : (Y.basicOpen c : Set Y).Nonempty := by
    refine ⟨(η ≫ q) z, ?_⟩
    have : z ∈ (η ≫ q) ⁻¹ᵁ Y.basicOpen c := by rw [hηU']; trivial
    exact this
  have hWn : (X.basicOpen (ρ c) : Set X).Nonempty := by
    refine ⟨η z, ?_⟩
    have : z ∈ η ⁻¹ᵁ X.basicOpen (ρ c) := by rw [hηW']; trivial
    exact this
  exact birationalOver_of_bijective_appLE q hU' hW' hW'U' hUn hWn hbij

end BirationalLFT

end DeJongAlterations.StableModification.Gluing
