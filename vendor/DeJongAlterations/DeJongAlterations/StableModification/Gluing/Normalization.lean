/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45A)
-/
import DeJongAlterations.StableModification.Gluing.Setup
import DeJongAlterations.StableModification.BlowDown.NormalizationCurve

/-!
# The normalization of the projective refinement (PLAN-T5 node A5)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.5.1 (`sepclosprop`, `semi-stable.tex` lines 3243–3266): after the refinement
`C' → C` (covered by opens `C'ᵢ = Wᵢ`) and cofinality, each `Wᵢ` is dominated by a strictly
semi-stable modification `qᵢ : Bᵢ → Wᵢ`; `PLAN-T5.md` §2.2 step 5 replaces Temkin's use of the
reduced fibre theorem by the normalization `N = Nor(C')` of `C'` in its function field, which over
`Wᵢ` is the Stein factorization `Spec qᵢ_* 𝒪_{Bᵢ}` of `qᵢ`.

Here `N` is Mathlib's relative normalization `(genericPt C').normalization` of `C'` in
`Spec K(C') → C'`, with `ν = (genericPt C').fromNormalization : N → C'`.

## Main results

* `isIso_normalizationComparison`: for `q : B → Y` with `B` normal and integral, the normalization
  of `Y` in the generic point of `B` is the normalization of `Y` in `B` (both are covered by the
  spectra of the integral closures of `Γ(U, 𝒪_Y)` in `K(B)` and in `Γ(q⁻¹U, 𝒪_B)`, which agree by
  normality).
* `isoOver_pullback_normalization`: the normalization of an integral `X` restricts over an open
  `W` to the normalization of `W`.
* `isoOver_normalization_of_isModification`: for a modification `q : B → W` with `B` normal, the
  normalization of `W` in its function field is `Nor_B(W) = Spec q_* 𝒪_B`.
* `isoOver_restrict_normalization_genericPt`: `N ∣_ Wᵢ ≅ Nor_{Bᵢ}(Wᵢ)` over `Wᵢ`.
* `isFinite_fromNormalization_genericPt`, `flat_fromNormalization_genericPt`,
  `locallyOfFinitePresentation_fromNormalization_genericPt`,
  `isReduced_closedFibre_fromNormalization_genericPt`: **`N` is finite over `C'`, flat and of
  finite presentation over `V`, with reduced closed fibre** when the `qᵢ` are projective relative
  to `Wᵢ → Spec V` with `Bᵢ` normal and flat over `V` (with reduced closed fibre) — Stein
  finiteness (`Cohomology.isFinite_fromNormalization_of_isRelativelyProjective`) and lane T44A's
  `BlowDown.flat_normalization` etc. on each piece.
* `isNormalScheme_normalization_genericPt`, `isModification_fromNormalization_genericPt`,
  `isProjectiveOver_fromNormalization_genericPt`: `N` is normal, `N → C'` is a modification when
  finite, and `N` is projective over `V` when `C'` is.

The hypotheses on the `qᵢ` (projectivity relative to `Wᵢ`, normality and flatness of `Bᵢ`) are the
output of PLAN-T5 node A4 (projective cofinality), which is not proved in this lane; they are
explicit hypotheses here.

The auxiliary predicate `IsoOver f₁ f₂` (an isomorphism of the sources commuting with the maps to
the common target) organizes the transport of properties along these identifications.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace DeJongAlterations.StableModification.Gluing

open ValCurves RiemannZariskiSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section GenericPoint

variable {B : Scheme.{u}} [IsIntegral B]

/-- The section map of the generic point `Spec K(B) → B` over a nonempty open is the germ to the
function field. -/
theorem sectionsToField_genericPt {V : B.Opens} [Nonempty V] (hV : genericPt B ⁻¹ᵁ V = ⊤)
    (r : Γ(B, V)) : sectionsToField (genericPt B) V hV r = B.germToFunctionField V r := by
  have h : genericPt B (IsLocalRing.closedPoint B.functionField) ∈ V := by
    have : IsLocalRing.closedPoint B.functionField ∈ genericPt B ⁻¹ᵁ V := by rw [hV]; trivial
    exact this
  rw [sectionsToField_eq_stalkClosedPointTo (genericPt B) hV h]
  unfold genericPt
  rw [Scheme.stalkClosedPointTo_fromSpecStalk, TopCat.Presheaf.stalkCongr_hom,
    ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

/-- **Normality**: on a normal integral scheme, a rational function integral over the sections
over a nonempty open `W` (through any ring `A → Γ(B, W)`) is a section over `W`. -/
theorem exists_germToFunctionField_eq_of_isIntegral (hB : IsNormalScheme B) (W : B.Opens)
    [Nonempty W] {A : Type*} [CommRing A] (ρ : A →+* Γ(B, W)) (x : B.functionField)
    (hx : @_root_.IsIntegral A _ _ _ ((B.germToFunctionField W).hom.comp ρ).toAlgebra x) :
    ∃ s : Γ(B, W), B.germToFunctionField W s = x := by
  let := ρ.toAlgebra
  let : Algebra A B.functionField := ((B.germToFunctionField W).hom.comp ρ).toAlgebra
  have : IsScalarTower A Γ(B, W) B.functionField := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hint : IsIntegral Γ(B, W) x := hx.tower_top
  refine BlowDown.exists_germToFunctionField_eq W x fun y hy ↦ ?_
  have := (hB y).1
  have := (hB y).2
  let : Algebra Γ(B, W) (B.presheaf.stalk y) := (B.presheaf.germ W y hy).hom.toAlgebra
  have htower : IsScalarTower Γ(B, W) (B.presheaf.stalk y) B.functionField :=
    IsScalarTower.of_algebraMap_eq fun r ↦
      (B.algebraMap_germ_eq_germToFunctionField hy r).symm
  have hint' : IsIntegral (B.presheaf.stalk y) x := hint.tower_top
  exact IsIntegrallyClosed.isIntegral_iff.mp hint'

end GenericPoint

section Comparison

variable {B Y : Scheme.{u}} [IsIntegral B] (q : B ⟶ Y) [QuasiCompact q] [QuasiSeparated q]

/-- The comparison map from the normalization of `Y` in the generic point of `B` to the
normalization of `Y` in `B` (Mathlib's universal property, `normalizationDesc`). -/
def normalizationComparison :
    (genericPt B ≫ q).normalization ⟶ q.normalization :=
  (genericPt B ≫ q).normalizationDesc (genericPt B ≫ q.toNormalization) q.fromNormalization
    (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization])

/-- The comparison map lies over `Y`. -/
@[reassoc (attr := simp)]
theorem normalizationComparison_fromNormalization :
    normalizationComparison q ≫ q.fromNormalization = (genericPt B ≫ q).fromNormalization :=
  Scheme.Hom.normalizationDesc_comp _ _ _ _

/-- The comparison map is compatible with the maps from the generic point. -/
@[reassoc (attr := simp)]
theorem toNormalization_normalizationComparison :
    (genericPt B ≫ q).toNormalization ≫ normalizationComparison q =
      genericPt B ≫ q.toNormalization :=
  Scheme.Hom.toNormalization_normalizationDesc _ _ _ _

/-- The comparison map is integral (it is induced by `normalizationDesc`). -/
instance : IsIntegralHom (normalizationComparison q) := by
  unfold normalizationComparison
  infer_instance

/-- `appLE` only depends on the morphism. -/
theorem appLE_eq_of_eq {X Z : Scheme.{u}} {g₁ g₂ : X ⟶ Z} (hg : g₁ = g₂) (U : Z.Opens)
    (V : X.Opens) (e₁ : V ≤ g₁ ⁻¹ᵁ U) (e₂ : V ≤ g₂ ⁻¹ᵁ U) : g₁.appLE U V e₁ = g₂.appLE U V e₂ := by
  subst hg
  rfl

/-- **The normalization of `Y` in the generic point of a normal `B` is its normalization in `B`**:
for `q : B → Y` with `B` normal and integral, the comparison map is an isomorphism (both are
covered by the spectra of the integral closures of `Γ(U, 𝒪_Y)` in `K(B)`, respectively in
`Γ(q⁻¹ U, 𝒪_B)`, which coincide by normality of `B`). -/
theorem isIso_normalizationComparison (hB : IsNormalScheme B) :
    IsIso (normalizationComparison q) := by
  set f := genericPt B ≫ q
  set α := normalizationComparison q
  have hα : α ≫ q.fromNormalization = f.fromNormalization :=
    normalizationComparison_fromNormalization q
  have hτ : f.toNormalization ≫ α = genericPt B ≫ q.toNormalization :=
    toNormalization_normalizationComparison q
  rw [← MorphismProperty.isomorphisms.iff, IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme)
    (fun U : Y.affineOpens ↦ q.fromNormalization ⁻¹ᵁ (U : Y.Opens)) ?_]
  swap
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  intro U
  have hU := U.2
  set V := q.fromNormalization ⁻¹ᵁ (U : Y.Opens)
  have hV : IsAffineOpen V := hU.preimage _
  change IsIso (α ∣_ V)
  rw [isIso_morphismRestrict_iff_isIso_app α hV]
  -- the opens
  set W := f ⁻¹ᵁ (U : Y.Opens)
  set V' := f.fromNormalization ⁻¹ᵁ (U : Y.Opens)
  set P := q ⁻¹ᵁ (U : Y.Opens)
  have h1 : V' ≤ α ⁻¹ᵁ V := by rw [← Scheme.Hom.comp_preimage, hα]
  have h2 : W ≤ f.toNormalization ⁻¹ᵁ V' := by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]
  have h3 : P ≤ q.toNormalization ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]
  have h4 : W ≤ genericPt B ⁻¹ᵁ P := le_rfl
  -- reduce to `appLE`
  suffices hbij : Function.Bijective (α.appLE V V' h1) by
    have hiso : IsIso (α.appLE V V' h1) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    have hle : α ⁻¹ᵁ V ≤ V' := by rw [← Scheme.Hom.comp_preimage, hα]
    have hmap : IsIso (f.normalization.presheaf.map (homOfLE h1).op) := by
      have : IsIso (homOfLE h1).op := by
        refine ⟨(homOfLE hle).op, ?_, ?_⟩ <;> rfl
      infer_instance
    have hdec : α.appLE V V' h1 = α.app V ≫ f.normalization.presheaf.map (homOfLE h1).op := rfl
    rw [hdec] at hiso
    exact IsIso.of_isIso_comp_right _ (f.normalization.presheaf.map (homOfLE h1).op)
  -- the maps into `Γ(Spec K(B), W)`
  set ιf := f.toNormalization.appLE V' W h2
  set ιq := q.toNormalization.appLE V P h3
  set e := (genericPt B).appLE P W h4
  have key : α.appLE V V' h1 ≫ ιf = ιq ≫ e := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_of_eq hτ _ _ _ _
  -- the integral closures
  let A := Γ(Y, (U : Y.Opens))
  let : Algebra A Γ(Spec (.of B.functionField), W) := (f.app (U : Y.Opens)).hom.toAlgebra
  let : Algebra A Γ(B, P) := (q.app (U : Y.Opens)).hom.toAlgebra
  have hιf : ιf = (f.normalizationObjIso hU).hom ≫
      CommRingCat.ofHom (Subalgebra.val (integralClosure A Γ(Spec (.of B.functionField), W))).toRingHom :=
    (Scheme.Hom.normalizationObjIso_hom_val f hU).symm
  have hιq : ιq = (q.normalizationObjIso hU).hom ≫
      CommRingCat.ofHom (Subalgebra.val (integralClosure A Γ(B, P))).toRingHom :=
    (Scheme.Hom.normalizationObjIso_hom_val q hU).symm
  have hιf_inj : Function.Injective ιf := by
    rw [hιf]
    intro a b hab
    exact (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).hom).1
      (Subtype.val_injective hab)
  have hιf_int : ∀ y, _root_.IsIntegral A (ιf y) := by
    intro y
    rw [hιf]
    exact ((f.normalizationObjIso hU).hom y).2
  have hιq_inj : Function.Injective ιq := by
    rw [hιq]
    intro a b hab
    exact (ConcreteCategory.bijective_of_isIso (q.normalizationObjIso hU).hom).1
      (Subtype.val_injective hab)
  have hιq_surj : ∀ s : Γ(B, P), _root_.IsIntegral A s → ∃ t, ιq t = s := by
    intro s hs
    refine ⟨(q.normalizationObjIso hU).inv ⟨s, hs⟩, ?_⟩
    rw [hιq]
    change (((q.normalizationObjIso hU).inv ≫ (q.normalizationObjIso hU).hom) ⟨s, hs⟩).val = s
    rw [Iso.inv_hom_id]
    rfl
  -- `e` is compatible with the algebra structures
  have he_comp : ∀ a : A, e ((q.app (U : Y.Opens)) a) = (f.app (U : Y.Opens)) a := by
    intro a
    rw [show f.app (U : Y.Opens) = q.app (U : Y.Opens) ≫ (genericPt B).app P from
      Scheme.Hom.comp_app _ _ _, Scheme.Hom.app_eq_appLE]
    rfl
  -- the two cases: `P` empty or not
  by_cases hPn : Nonempty P
  swap
  · have hPe : P = ⊥ := by
      ext z
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz ↦ hPn ⟨⟨z, hz⟩⟩
    have hsub : Subsingleton Γ(B, P) :=
      CommRingCat.subsingleton_of_isTerminal (B.sheaf.isTerminalOfEqEmpty hPe)
    have hsubN : Subsingleton Γ(q.normalization, V) := by
      have : Subsingleton (integralClosure A Γ(B, P)) := Subtype.val_injective.subsingleton
      exact (ConcreteCategory.bijective_of_isIso (q.normalizationObjIso hU).hom).1.subsingleton
    have hWe : W = ⊥ := by
      change genericPt B ⁻¹ᵁ P = ⊥
      rw [hPe]
      rfl
    have hsubW : Subsingleton Γ(Spec (.of B.functionField), W) :=
      CommRingCat.subsingleton_of_isTerminal ((Spec _).sheaf.isTerminalOfEqEmpty hWe)
    have hsubN' : Subsingleton Γ(f.normalization, V') := hιf_inj.subsingleton
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  -- `P` is nonempty: `W` is everything, and `e` is the germ to the function field
  have hξP : genericPoint B ∈ P := by
    obtain ⟨⟨z, hz⟩⟩ := hPn
    exact ((genericPoint_spec B).mem_open_set_iff P.isOpen).mpr ⟨z, Set.mem_univ z, hz⟩
  have hPtop : genericPt B ⁻¹ᵁ P = ⊤ := by
    ext z
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    change genericPt B z ∈ P
    rw [genericPt_apply]
    exact hξP
  let ρ : Γ(Spec (.of B.functionField), W) ⟶ CommRingCat.of B.functionField :=
    (Spec _).presheaf.map (homOfLE hPtop.ge).op ≫ (Scheme.ΓSpecIso _).hom
  have hρ : ∀ s, ρ (e s) = B.germToFunctionField P s := by
    intro s
    rw [← sectionsToField_genericPt hPtop]
    change ((genericPt B).appLE P W h4 ≫ (Spec _).presheaf.map (homOfLE hPtop.ge).op ≫
      (Scheme.ΓSpecIso _).hom) s = _
    rw [Scheme.Hom.appLE_map_assoc]
    rfl
  have hρ_inj : Function.Injective ρ := by
    have : IsIso (homOfLE hPtop.ge).op := ⟨(homOfLE hPtop.le).op, rfl, rfl⟩
    exact (ConcreteCategory.bijective_of_isIso ρ).1
  have he_inj : Function.Injective e := by
    intro a b hab
    apply B.germToFunctionField_injective P
    rw [← hρ, ← hρ, hab]
  -- normality: integral elements come from `Γ(B, P)`
  have hcompρ : (B.germToFunctionField P).hom.comp (q.app (U : Y.Opens)).hom =
      ρ.hom.comp (algebraMap A Γ(Spec (.of B.functionField), W)) := by
    ext a
    change B.germToFunctionField P (q.app (U : Y.Opens) a) = ρ (f.app (U : Y.Opens) a)
    rw [← he_comp, hρ]
  have hnorm : ∀ x : Γ(Spec (.of B.functionField), W), _root_.IsIntegral A x →
      ∃ s, e s = x := by
    intro x hx
    obtain ⟨p, hpm, hp⟩ := hx
    obtain ⟨s, hs⟩ := exists_germToFunctionField_eq_of_isIntegral hB P (q.app (U : Y.Opens)).hom
      (ρ x) ⟨p, hpm, by
        rw [RingHom.algebraMap_toAlgebra, hcompρ]
        have h0 := congrArg ρ hp
        rwa [map_zero, Polynomial.hom_eval₂] at h0⟩
    exact ⟨s, hρ_inj (by rw [hρ, hs])⟩
  have hcompe : e.hom.comp (algebraMap A Γ(B, P)) =
      algebraMap A Γ(Spec (.of B.functionField), W) := by
    ext a
    exact he_comp a
  refine ⟨fun a b hab ↦ hιq_inj (he_inj ?_), fun y ↦ ?_⟩
  · have h1 := congrArg ιf hab
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, key] at h1
    exact h1
  · obtain ⟨s, hs⟩ := hnorm (ιf y) (hιf_int y)
    have hsint : _root_.IsIntegral A s := by
      obtain ⟨p, hpm, hp⟩ := hιf_int y
      refine ⟨p, hpm, he_inj ?_⟩
      rw [map_zero, ← hp, ← hs]
      change e.hom (Polynomial.eval₂ _ s p) = _
      rw [Polynomial.hom_eval₂, hcompe]
    obtain ⟨t, ht⟩ := hιq_surj s hsint
    refine ⟨t, hιf_inj ?_⟩
    rw [← CommRingCat.comp_apply, key, CommRingCat.comp_apply, ht, hs]

end Comparison

section GenericPoints

variable {X Y : Scheme.{u}}

/-- **A field point through the generic point factors through the generic point**: if
`e : Spec F → X` hits the generic point of the integral `X`, then `e = Spec ψ ∘ (Spec K(X) → X)`
for the field map `ψ : K(X) → F` of `e`. -/
theorem exists_eq_SpecMap_comp_genericPt [IsIntegral X] {F : Type u} [Field F]
    (e : Spec (.of F) ⟶ X) (he : ∀ z, e z = genericPoint X) :
    ∃ ψ : X.functionField ⟶ CommRingCat.of F,
      e = Spec.map ψ ≫ genericPt X ∧
        (Function.Surjective (Scheme.stalkClosedPointTo e) → IsIso ψ) := by
  have h : e (IsLocalRing.closedPoint F) ⤳ genericPoint X := by rw [he]
  refine ⟨X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo e, ?_, fun hs ↦ ?_⟩
  · rw [Spec.map_comp, Category.assoc, genericPt, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · have hiso : IsIso (X.presheaf.stalkSpecializes h) := by
      have h' : genericPoint X ⤳ e (IsLocalRing.closedPoint F) := by rw [he]
      refine ⟨X.presheaf.stalkSpecializes h', ?_, ?_⟩ <;>
        simp only [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
    refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨RingHom.injective _, fun y ↦ ?_⟩
    obtain ⟨a, rfl⟩ := hs y
    obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (X.presheaf.stalkSpecializes h)).2 a
    exact ⟨b, rfl⟩

/-- **Normalization along an isomorphism of the source.** -/
def normalizationIsoOfIso {X' : Scheme.{u}} (i : X' ≅ X) (g : X ⟶ Y) [QuasiCompact g]
    [QuasiSeparated g] : (i.hom ≫ g).normalization ≅ g.normalization where
  hom := (i.hom ≫ g).normalizationDesc (i.hom ≫ g.toNormalization) g.fromNormalization
    (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization])
  inv := g.normalizationDesc (i.inv ≫ (i.hom ≫ g).toNormalization) (i.hom ≫ g).fromNormalization
    (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    refine Scheme.Hom.normalization.hom_ext _ _ _ (i.hom ≫ g).fromNormalization ?_ ?_ ?_
    · rw [Scheme.Hom.toNormalization_normalizationDesc_assoc, Category.assoc,
        Scheme.Hom.toNormalization_normalizationDesc, Iso.hom_inv_id_assoc, Category.comp_id]
    · rw [Category.assoc, Scheme.Hom.normalizationDesc_comp, Scheme.Hom.normalizationDesc_comp]
    · rw [Category.id_comp]
  inv_hom_id := by
    refine Scheme.Hom.normalization.hom_ext _ _ _ g.fromNormalization ?_ ?_ ?_
    · rw [Scheme.Hom.toNormalization_normalizationDesc_assoc, Category.assoc,
        Scheme.Hom.toNormalization_normalizationDesc, Iso.inv_hom_id_assoc, Category.comp_id]
    · rw [Category.assoc, Scheme.Hom.normalizationDesc_comp, Scheme.Hom.normalizationDesc_comp]
    · rw [Category.id_comp]

/-- `normalizationIsoOfIso` lies over `Y`. -/
@[reassoc (attr := simp)]
theorem normalizationIsoOfIso_hom_fromNormalization {X' : Scheme.{u}} (i : X' ≅ X)
    (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g] :
    (normalizationIsoOfIso i g).hom ≫ g.fromNormalization = (i.hom ≫ g).fromNormalization := by
  unfold normalizationIsoOfIso
  exact Scheme.Hom.normalizationDesc_comp _ _ _
    (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization])

end GenericPoints

section IsoOver

variable {Y X₁ X₂ X₃ : Scheme.{u}}

/-- Two schemes over `Y` are isomorphic over `Y`. -/
def IsoOver (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) : Prop :=
  ∃ i : X₁ ≅ X₂, i.hom ≫ f₂ = f₁

/-- Every scheme over `Y` is isomorphic to itself over `Y`. -/
theorem IsoOver.refl (f : X₁ ⟶ Y) : IsoOver f f := ⟨Iso.refl _, Category.id_comp _⟩

/-- `IsoOver` is symmetric. -/
theorem IsoOver.symm {f₁ : X₁ ⟶ Y} {f₂ : X₂ ⟶ Y} (h : IsoOver f₁ f₂) : IsoOver f₂ f₁ := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i.symm, by rw [Iso.symm_hom, ← hi, Iso.inv_hom_id_assoc]⟩

/-- `IsoOver` is transitive. -/
theorem IsoOver.trans {f₁ : X₁ ⟶ Y} {f₂ : X₂ ⟶ Y} {f₃ : X₃ ⟶ Y} (h₁ : IsoOver f₁ f₂)
    (h₂ : IsoOver f₂ f₃) : IsoOver f₁ f₃ := by
  obtain ⟨i, hi⟩ := h₁
  obtain ⟨j, hj⟩ := h₂
  exact ⟨i ≪≫ j, by rw [Iso.trans_hom, Category.assoc, hj, hi]⟩

/-- Properties respecting isomorphisms transfer along isomorphisms over `Y`. -/
theorem IsoOver.prop {P : MorphismProperty Scheme.{u}} [P.RespectsIso] {f₁ : X₁ ⟶ Y}
    {f₂ : X₂ ⟶ Y} (h : IsoOver f₁ f₂) (hP : P f₂) : P f₁ := by
  obtain ⟨i, rfl⟩ := h
  exact (P.cancel_left_of_respectsIso i.hom f₂).mpr hP

/-- Equal morphisms have isomorphic normalizations. -/
theorem isoOver_normalization_of_eq {X : Scheme.{u}} {g g' : X ⟶ Y} [QuasiCompact g]
    [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g'] (h : g = g') :
    IsoOver g.fromNormalization g'.fromNormalization := by
  subst h
  exact IsoOver.refl _

/-- Normalizations along an isomorphism of the source are isomorphic over the target. -/
theorem isoOver_normalization_of_iso {X X' : Scheme.{u}} (i : X' ≅ X) (g : X ⟶ Y)
    [QuasiCompact g] [QuasiSeparated g] :
    IsoOver (i.hom ≫ g).fromNormalization g.fromNormalization :=
  ⟨normalizationIsoOfIso i g, normalizationIsoOfIso_hom_fromNormalization i g⟩

/-- **Normalizations of generic points**: for a field point `e` of the integral `X` hitting the
generic point with surjective local map (a generic point up to isomorphism), the normalization of
`X` in `e` is the normalization of `X` in its function field. -/
theorem isoOver_normalization_genericPt [IsIntegral X₁] {F : Type u} [Field F]
    (e : Spec (.of F) ⟶ X₁) (he : ∀ z, e z = genericPoint X₁)
    (hs : Function.Surjective (Scheme.stalkClosedPointTo e)) :
    IsoOver e.fromNormalization (genericPt X₁).fromNormalization := by
  obtain ⟨ψ, hψ, hiso⟩ := exists_eq_SpecMap_comp_genericPt e he
  have := hiso hs
  subst hψ
  exact isoOver_normalization_of_iso (asIso (Spec.map ψ)) (genericPt X₁)

end IsoOver

section Restriction

variable {X Y W B : Scheme.{u}} {F : Type u} [Field F]

/-- The local map of the generic point `Spec K(X) → X` is surjective (an isomorphism). -/
theorem surjective_stalkClosedPointTo_genericPt [IsIntegral X] :
    Function.Surjective (Scheme.stalkClosedPointTo (genericPt X)) := by
  unfold genericPt
  rw [Scheme.stalkClosedPointTo_fromSpecStalk]
  exact (ConcreteCategory.bijective_of_isIso _).2

/-- Surjectivity of the local map of `e ≫ g` implies that of `e`. -/
theorem surjective_stalkClosedPointTo_of_comp (e : Spec (.of F) ⟶ X) (g : X ⟶ Y)
    (h : Function.Surjective (Scheme.stalkClosedPointTo (e ≫ g))) :
    Function.Surjective (Scheme.stalkClosedPointTo e) := by
  rw [Scheme.stalkClosedPointTo_comp] at h
  intro y
  obtain ⟨a, ha⟩ := h y
  exact ⟨g.stalkMap _ a, ha⟩

/-- Surjectivity of local maps of field points is preserved by composing with `g` when `g` is an
isomorphism on the relevant stalk. -/
theorem surjective_stalkClosedPointTo_comp (e : Spec (.of F) ⟶ X) (g : X ⟶ Y)
    [IsIso (g.stalkMap (e (IsLocalRing.closedPoint F)))]
    (h : Function.Surjective (Scheme.stalkClosedPointTo e)) :
    Function.Surjective (Scheme.stalkClosedPointTo (e ≫ g)) := by
  rw [Scheme.stalkClosedPointTo_comp]
  intro y
  obtain ⟨a, rfl⟩ := h y
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (g.stalkMap (e (IsLocalRing.closedPoint F)))).2 a
  exact ⟨b, rfl⟩

/-- Isomorphisms over `X` give isomorphisms of base changes over `Z`. -/
theorem IsoOver.pullback_snd {X₁ X₂ Z : Scheme.{u}} {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X}
    (h : IsoOver f₁ f₂) (g : Z ⟶ X) : IsoOver (pullback.snd f₁ g) (pullback.snd f₂ g) := by
  obtain ⟨i, rfl⟩ := h
  refine ⟨asIso (pullback.map (i.hom ≫ f₂) g f₂ g i.hom (𝟙 _) (𝟙 _) (by simp) (by simp)), ?_⟩
  simp

/-- **Normalization commutes with restriction to an open**: over an open `W` of the integral `X`,
the normalization of `X` in its function field restricts to the normalization of `W` in its
function field. -/
theorem isoOver_pullback_normalization [IsIntegral X] (W : X.Opens) [Nonempty W] :
    IsoOver (pullback.snd (genericPt X).fromNormalization W.ι) (genericPt W).fromNormalization := by
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  have hξ : genericPoint X ∈ W := by
    obtain ⟨⟨z, hz⟩⟩ := ‹Nonempty W›
    exact ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨z, Set.mem_univ z, hz⟩
  have hr : Set.range (genericPt X) ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, genericPt_apply]
    exact hξ
  set e := IsOpenImmersion.lift W.ι (genericPt X) hr
  have he : e ≫ W.ι = genericPt X := IsOpenImmersion.lift_fac _ _ _
  -- the restricted generic point
  have he' : ∀ z, e z = genericPoint W.toScheme := by
    intro z
    apply W.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, he, genericPt_apply, genericPoint_eq_of_isOpenImmersion]
  have hs : Function.Surjective (Scheme.stalkClosedPointTo e) := by
    refine surjective_stalkClosedPointTo_of_comp e W.ι ?_
    rw [he]
    exact surjective_stalkClosedPointTo_genericPt
  -- the chain of isomorphisms
  have h1 : IsoOver (pullback.snd (genericPt X).fromNormalization W.ι)
      (pullback.snd (e ≫ W.ι).fromNormalization W.ι) :=
    (isoOver_normalization_of_eq he.symm).pullback_snd W.ι
  have h2 : IsoOver (pullback.snd (e ≫ W.ι).fromNormalization W.ι)
      (pullback.snd (e ≫ W.ι) W.ι).fromNormalization :=
    ⟨(asIso ((e ≫ W.ι).normalizationPullback W.ι)).symm, by simp⟩
  have hsnd : pullback.snd (e ≫ W.ι) W.ι = (asIso (pullback.fst (e ≫ W.ι) W.ι)).hom ≫ e := by
    rw [asIso_hom, ← cancel_mono W.ι, Category.assoc, ← pullback.condition]
  have h3 : IsoOver (pullback.snd (e ≫ W.ι) W.ι).fromNormalization e.fromNormalization :=
    (isoOver_normalization_of_eq hsnd).trans
      (isoOver_normalization_of_iso (asIso (pullback.fst (e ≫ W.ι) W.ι)) e)
  exact h1.trans (h2.trans (h3.trans (isoOver_normalization_genericPt e he' hs)))

/-- **The normalization of a curve in its function field, locally**: for a modification
`q : B → W` with `B` normal, the normalization of `W` in its function field is the normalization
of `W` in `B` (Stein factorization of `q`). -/
theorem isoOver_normalization_of_isModification [IsIntegral W] [IsIntegral B] (q : B ⟶ W)
    [IsModification q] (hB : IsNormalScheme B) :
    IsoOver (genericPt W).fromNormalization q.fromNormalization := by
  have hbir := (inferInstance : IsModification q).birational
  have hξ : ∀ z, (genericPt B ≫ q) z = genericPoint W := by
    intro z
    rw [Scheme.Hom.comp_apply, genericPt_apply,
      Geometry.NormalCurveModification.genericPoint_map q hbir]
  have hs : Function.Surjective (Scheme.stalkClosedPointTo (genericPt B ≫ q)) := by
    have : IsIso (q.stalkMap (genericPt B (IsLocalRing.closedPoint B.functionField))) := by
      rw [genericPt_apply]
      exact Geometry.NormalCurveModification.generic_stalkMap_isIso q hbir
    exact surjective_stalkClosedPointTo_comp _ q surjective_stalkClosedPointTo_genericPt
  have := isIso_normalizationComparison q hB
  exact (isoOver_normalization_genericPt _ hξ hs).symm.trans
    ⟨asIso (normalizationComparison q), normalizationComparison_fromNormalization q⟩

end Restriction


section Transport

variable {Y Z X₁ X₂ : Scheme.{u}}

/-- Isomorphisms over `Y` compose with morphisms out of `Y`. -/
theorem IsoOver.comp {f₁ : X₁ ⟶ Y} {f₂ : X₂ ⟶ Y} (h : IsoOver f₁ f₂) (g : Y ⟶ Z) :
    IsoOver (f₁ ≫ g) (f₂ ≫ g) := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨i, by rw [Category.assoc]⟩

/-- The restriction `f ∣_ U` is the base change of `f` along `U ↪ Y`. -/
theorem isoOver_morphismRestrict {X : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    IsoOver (f ∣_ U) (pullback.snd f U.ι) :=
  ⟨(pullbackRestrictIsoRestrict f U).symm, by
    rw [Iso.symm_hom, Iso.inv_comp_eq]
    exact (pullbackRestrictIsoRestrict_hom_morphismRestrict f U).symm⟩

/-- Reducedness of base changes is invariant under isomorphisms over the base. -/
theorem IsoOver.isReduced_pullback {f₁ : X₁ ⟶ Y} {f₂ : X₂ ⟶ Y} (h : IsoOver f₁ f₂)
    (r : Z ⟶ Y) [IsReduced (pullback f₂ r)] : IsReduced (pullback f₁ r) := by
  obtain ⟨i, rfl⟩ := h
  exact isReduced_of_isOpenImmersion
    (pullback.map (i.hom ≫ f₂) r f₂ r i.hom (𝟙 _) (𝟙 _) (by simp) (by simp))

/-- **Reduced base changes are local on the source**: if `X` is covered by opens `Uᵢ` with
`Uᵢ ×_S T` reduced, then `X ×_S T` is reduced. -/
theorem isReduced_pullback_of_iSup_eq_top {X S T : Scheme.{u}} (g : X ⟶ S) (r : T ⟶ S)
    {ι : Type*} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, IsReduced (pullback ((U i).ι ≫ g) r)) : IsReduced (pullback g r) := by
  have hst : ∀ x : ↥(pullback g r), _root_.IsReduced ((pullback g r).presheaf.stalk x) := by
    intro x
    obtain ⟨i, hi⟩ : ∃ i, pullback.fst g r x ∈ U i := by
      have : pullback.fst g r x ∈ (⊤ : X.Opens) := trivial
      rw [← hU] at this
      exact TopologicalSpace.Opens.mem_iSup.mp this
    have := h i
    have : IsReduced (pullback (U i).ι (pullback.fst g r)) :=
      isReduced_of_isOpenImmersion (pullbackRightPullbackFstIso g r (U i).ι).hom
    have hx : x ∈ Set.range (pullback.snd (U i).ι (pullback.fst g r)) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      change pullback.fst g r x ∈ (U i).ι.opensRange
      rw [Scheme.Opens.opensRange_ι]
      exact hi
    obtain ⟨y, rfl⟩ := hx
    exact isReduced_of_injective _ (ConcreteCategory.bijective_of_isIso
      ((pullback.snd (U i).ι (pullback.fst g r)).stalkMap y)).1
  exact isReduced_of_isReduced_stalk _

end Transport

section Main

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
variable {C' : Scheme.{u}} [IsIntegral C'] {ι : Type*} {W : ι → C'.Opens} {B : ι → Scheme.{u}}
  (q : ∀ i, B i ⟶ W i)

/-- **The normalization of `C'` restricted to a piece**: over an open `Wᵢ ⊆ C'` dominated by a
modification `qᵢ : Bᵢ → Wᵢ` with `Bᵢ` normal, the normalization `N = Nor(C')` of `C'` (in its
function field) restricts to the Stein factorization `Nor_{Bᵢ}(Wᵢ) = Spec qᵢ_* 𝒪_{Bᵢ}`. -/
theorem isoOver_restrict_normalization_genericPt (i : ι) [IsModification (q i)]
    (hB : IsNormalScheme (B i)) :
    IsoOver ((genericPt C').fromNormalization ∣_ W i) (q i).fromNormalization := by
  have hmod : IsModification (q i) := inferInstance
  have := hmod.sourceIntegral
  have := hmod.targetIntegral
  have : Nonempty (W i) := (inferInstance : Nonempty (W i).toScheme)
  exact (isoOver_morphismRestrict _ _).trans ((isoOver_pullback_normalization (W i)).trans
    (isoOver_normalization_of_isModification (q i) hB))


/-- Over the preimage of a piece `Wᵢ`, the normalization `N → C'` is `Nor_{Bᵢ}(Wᵢ) → Wᵢ ⊆ C'`. -/
theorem isoOver_preimage_normalization_genericPt (i : ι) [IsModification (q i)]
    (hB : IsNormalScheme (B i)) :
    IsoOver (((genericPt C').fromNormalization ⁻¹ᵁ W i).ι ≫ (genericPt C').fromNormalization)
      ((q i).fromNormalization ≫ (W i).ι) := by
  rw [← morphismRestrict_ι]
  exact (isoOver_restrict_normalization_genericPt q i hB).comp _

/-- Preimages of a cover form a cover. -/
theorem iSup_preimage_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y) {U : ι → Y.Opens}
    (hU : ⨆ i, U i = ⊤) : ⨆ i, f ⁻¹ᵁ U i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]

variable (pC' : C' ⟶ Spec (.of V))

/-- **`N = Nor(C')` is finite over `C'`** (`PLAN-T5.md` §2.2 step 5, node A5): if `C'` is covered
by opens `Wᵢ` dominated by modifications `qᵢ : Bᵢ → Wᵢ`, projective relative to `Wᵢ → Spec V`,
with `Bᵢ` normal and flat over `V`, then `N → C'` is finite (Stein finiteness on each piece). -/
theorem isFinite_fromNormalization_genericPt (hW : ⨆ i, W i = ⊤)
    [LocallyOfFinitePresentation pC'] [∀ i, IsModification (q i)]
    (hB : ∀ i, IsNormalScheme (B i)) (hflat : ∀ i, Flat (q i ≫ (W i).ι ≫ pC'))
    (hq : ∀ i, DeJong.IsRelativelyProjective ((W i).ι ≫ pC') (q i)) :
    IsFinite (genericPt C').fromNormalization := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) W hW]
  intro i
  have := hflat i
  exact (isoOver_restrict_normalization_genericPt q i (hB i)).prop (P := @IsFinite)
    (Cohomology.isFinite_fromNormalization_of_isRelativelyProjective V (q i)
      ((W i).ι ≫ pC') (hq i))

/-- **`N = Nor(C')` is flat over `V`** (node A5). -/
theorem flat_fromNormalization_genericPt (hW : ⨆ i, W i = ⊤)
    [LocallyOfFinitePresentation pC'] [∀ i, IsModification (q i)]
    (hB : ∀ i, IsNormalScheme (B i)) (hflat : ∀ i, Flat (q i ≫ (W i).ι ≫ pC'))
    (hq : ∀ i, DeJong.IsRelativelyProjective ((W i).ι ≫ pC') (q i)) :
    Flat ((genericPt C').fromNormalization ≫ pC') := by
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Flat) _
    (iSup_preimage_eq_top (genericPt C').fromNormalization hW)]
  intro i
  have := hflat i
  have h := (isoOver_preimage_normalization_genericPt q i (hB i)).comp pC'
  simp only [Category.assoc] at h
  exact h.prop (P := @Flat) (BlowDown.flat_normalization (q i) ((W i).ι ≫ pC') (hq i))

/-- **`N = Nor(C')` is locally of finite presentation over `V`** (node A5). -/
theorem locallyOfFinitePresentation_fromNormalization_genericPt (hW : ⨆ i, W i = ⊤)
    [LocallyOfFinitePresentation pC'] [∀ i, IsModification (q i)]
    (hB : ∀ i, IsNormalScheme (B i)) (hflat : ∀ i, Flat (q i ≫ (W i).ι ≫ pC'))
    (hq : ∀ i, DeJong.IsRelativelyProjective ((W i).ι ≫ pC') (q i)) :
    LocallyOfFinitePresentation ((genericPt C').fromNormalization ≫ pC') := by
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
    (iSup_preimage_eq_top (genericPt C').fromNormalization hW)]
  intro i
  have := hflat i
  have h := (isoOver_preimage_normalization_genericPt q i (hB i)).comp pC'
  simp only [Category.assoc] at h
  exact h.prop (P := @LocallyOfFinitePresentation)
    (BlowDown.locallyOfFinitePresentation_normalization (q i) ((W i).ι ≫ pC') (hq i))

/-- **`N = Nor(C')` has reduced closed fibre** (node A5) when the `Bᵢ` have. -/
theorem isReduced_closedFibre_fromNormalization_genericPt (hW : ⨆ i, W i = ⊤)
    [LocallyOfFinitePresentation pC'] [∀ i, IsModification (q i)]
    (hB : ∀ i, IsNormalScheme (B i)) (hflat : ∀ i, Flat (q i ≫ (W i).ι ≫ pC'))
    (hq : ∀ i, DeJong.IsRelativelyProjective ((W i).ι ≫ pC') (q i))
    (hred : ∀ i, IsReduced (pullback (q i ≫ (W i).ι ≫ pC')
      (Spec.map (CommRingCat.ofHom (residue V))))) :
    IsReduced (pullback ((genericPt C').fromNormalization ≫ pC')
      (Spec.map (CommRingCat.ofHom (residue V)))) := by
  refine isReduced_pullback_of_iSup_eq_top _ _ _
    (iSup_preimage_eq_top (genericPt C').fromNormalization hW) fun i ↦ ?_
  have := hflat i
  have := hred i
  have := BlowDown.isReduced_closedFibre_normalization (q i) ((W i).ι ≫ pC') (hq i)
  have h := (isoOver_preimage_normalization_genericPt q i (hB i)).comp pC'
  simp only [Category.assoc] at h
  exact h.isReduced_pullback _

end Main

section Global

variable {C' : Scheme.{u}} [IsIntegral C']

/-- **`N = Nor(C')` is normal.** -/
theorem isNormalScheme_normalization_genericPt :
    IsNormalScheme (genericPt C').normalization :=
  BlowDown.isNormalScheme_normalization _ (isNormalScheme_spec C'.functionField)

/-- The generic point `Spec K(C') → C'` lands in every nonempty open. -/
theorem preimage_genericPt_eq_top {U : C'.Opens} [Nonempty U] : genericPt C' ⁻¹ᵁ U = ⊤ := by
  have hξ : genericPoint C' ∈ U := by
    obtain ⟨⟨z, hz⟩⟩ := ‹Nonempty U›
    exact ((genericPoint_spec C').mem_open_set_iff U.isOpen).mpr ⟨z, Set.mem_univ z, hz⟩
  ext z
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  change genericPt C' z ∈ U
  rw [genericPt_apply]
  exact hξ

/-- **`N → C'` is a modification** when it is finite: it is birational, `C'` and `N` having the
same function field. -/
theorem isModification_fromNormalization_genericPt [IsFinite (genericPt C').fromNormalization] :
    IsModification (genericPt C').fromNormalization := by
  set ν := (genericPt C').fromNormalization
  set η := (genericPt C').toNormalization
  have hην : η ≫ ν = genericPt C' := Scheme.Hom.toNormalization_fromNormalization _
  obtain ⟨x⟩ := (inferInstance : Nonempty C')
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hU' : genericPt C' ⁻¹ᵁ U = ⊤ := preimage_genericPt_eq_top
  have hηU : (η ≫ ν) ⁻¹ᵁ U = ⊤ := by rw [hην]; exact hU'
  refine
    { toIsProper := inferInstance
      sourceIntegral := inferInstance
      targetIntegral := inferInstance
      birational := birationalOver_of_locallyOfFiniteType η
        (apply_eq_genericPoint_of_isDominant η) ν (fun z ↦ by rw [hην, genericPt_apply]) hU hηU
        fun y ↦ ?_ }
  have hs : ∀ r, sectionsToField (η ≫ ν) U hηU r = C'.germToFunctionField U r := by
    intro r
    rw [sectionsToField_congr hην hηU hU', sectionsToField_genericPt hU']
  have := functionField_isFractionRing_of_isAffineOpen C' U hU
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors Γ(C', U)) y
  refine ⟨a, b, ?_, ?_⟩
  · rw [hs]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  · rw [hs, hs, ← hab]
    exact IsLocalization.mk'_spec _ _ _

/-- **`N = Nor(C')` is projective over `V`** when `C'` is and `N → C'` is finite. -/
theorem isProjectiveOver_fromNormalization_genericPt {V : Type u} [CommRing V]
    (pC' : C' ⟶ Spec (.of V)) (hp : IsProjectiveOver pC')
    [IsFinite (genericPt C').fromNormalization] :
    IsProjectiveOver ((genericPt C').fromNormalization ≫ pC') :=
  Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite pC' hp _

end Global

end DeJongAlterations.StableModification.Gluing
