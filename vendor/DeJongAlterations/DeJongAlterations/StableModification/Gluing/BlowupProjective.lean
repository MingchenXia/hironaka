/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45C)
-/
import DeJongAlterations.StableModification.Gluing.BlowupProjectiveFlat
import DeJongAlterations.StableModification.Blowups.Transport
import DeJongAlterations.StableModification.Projectivity.SerreIdeal
import DeJongAlterations.Geometry.BlowupOpenChart
import DeJongAlterations.Geometry.BlowupComplement

/-!
# Chart blow-ups extended by the identity are blow-ups of ideal sheaves

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.3.1 (T:2970–2983): the blow-ups of the proof are built on an étale chart
`φ : V₀ → M = Spec A` around a closed point and "extend trivially" to the whole curve `X`. Here
`V₀ ⊆ X` is an affine open, `φ` is flat and `I ⊆ A` is a finitely generated ideal such that the
centre `φ⁻¹V(I)` is closed in `X` (the fix of `ERRATA.md` DJA-T33/T48), and the modification
`Blowups.extension W (pullback.snd (Bl_I → Spec A) φ)` is the pulled-back blow-up glued with the
identity over an open `W ⊇ X ∖ V₀` disjoint from the centre.

The main result `exists_iso_blowup` identifies this extension, over `X`, with the native blow-up
`Bl_D X` (Codex's `Geometry.BlowupGluing.blowup`) of the ideal sheaf `D` of the closed subscheme
`Spec(Γ(V₀)/IΓ(V₀)) → X` (`centreIdeal`), which is of finite type. Consequently
(`isProjectiveOver_extensionHom`), **if `X` is projective and of finite presentation over a ring
`E`, so is the extension**, by SERRE-I (lane OM3C,
`Projectivity.isProjectiveOver_blowupStructure_comp_of_fg`). This is the projectivity of one step
of the induction of Temkin's Proposition 4.3.1 (`PLAN-T5.md` node A4).

## Main definitions and results

* `centreMap j I`, `centreIdeal j I`: the closed immersion `Spec(S/I) → Spec S → X` for an open
  immersion `j : Spec S → X` with closed centre, and its ideal sheaf; `comap_centreIdeal`
  (`D|_{Spec S} = Ĩ`), `coe_support_centreIdeal`, `centreIdeal_fg`;
* `exists_iso_blowup`, `isProjectiveOver_extensionHom`.

The comparison uses the flat base change of affine blow-ups
(`BlowupFlat.isPullback_affineBlowupMap_of_flat`) over `V₀`, Codex's chart identification
`Geometry.BlowupOpenChart.chartIso` and the isomorphism of the native blow-up off the support of
`D` (`Geometry.BlowupComplement.blowupStructure_supportComplement_isIso`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.BlowupProjective

open DeJongAlterations.Geometry DeJongAlterations.Geometry.BlowupGluing
  DeJongAlterations.Geometry.SpecIdealSheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Ideal

variable {X : Scheme.{u}} {S : Type u} [CommRing S] (j : Spec (.of S) ⟶ X) [IsOpenImmersion j]
  (I : Ideal S)

/-- The quotient map `Spec(S/I) → Spec S`. -/
abbrev quotientMap : Spec (.of (S ⧸ I)) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The centre `Spec(S/I) → Spec S → X`. -/
def centreMap : Spec (.of (S ⧸ I)) ⟶ X := quotientMap I ≫ j

theorem range_quotientMap :
    Set.range (quotientMap I) = PrimeSpectrum.zeroLocus (I : Set S) := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
  rw [range_comap_of_surjective (S ⧸ I) _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]

omit [IsOpenImmersion j] in
theorem range_centreMap :
    Set.range (centreMap j I) = j '' PrimeSpectrum.zeroLocus (I : Set S) := by
  rw [centreMap, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_quotientMap]

theorem isClosedImmersion_centreMap (h : IsClosed (j '' PrimeSpectrum.zeroLocus (I : Set S))) :
    IsClosedImmersion (centreMap j I) := by
  have : IsClosedImmersion (quotientMap I) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsPreimmersion (centreMap j I) := by
    rw [centreMap]
    infer_instance
  exact .of_isPreimmersion _ (by rw [range_centreMap]; exact h)

/-- The ideal sheaf of the centre. -/
def centreIdeal : X.IdealSheafData := (centreMap j I).ker

/-- The kernel of `Spec(S/I) → Spec S` is `Ĩ`. -/
theorem ker_quotientMap : (quotientMap I).ker = specIdealSheaf S I := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.Hom.ker_apply, specIdealSheaf_ideal_top]
  have hker : RingHom.ker (quotientMap I).appTop.hom =
      I.comap (Scheme.ΓSpecIso (.of S)).hom.hom := by
    rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso (.of (S ⧸ I))).commRingCatIsoToRingEquiv]
    change RingHom.ker (((quotientMap I).appTop ≫ (Scheme.ΓSpecIso (.of (S ⧸ I))).hom).hom) = _
    rw [Scheme.ΓSpecIso_naturality]
    change RingHom.ker ((Ideal.Quotient.mk I).comp (Scheme.ΓSpecIso (.of S)).hom.hom) = _
    rw [← RingHom.comap_ker, Ideal.mk_ker]
  change RingHom.ker (quotientMap I).appTop.hom = _
  rw [hker]
  exact (Ideal.map_symm (f := (Scheme.ΓSpecIso (.of S)).commRingCatIsoToRingEquiv) (I := I)).symm

variable [IsClosedImmersion (centreMap j I)]

/-- **The ideal sheaf of the centre restricts to `Ĩ` on the chart.** -/
theorem comap_centreIdeal : (centreIdeal j I).comap j = specIdealSheaf S I := by
  have sq : IsPullback (quotientMap I) (𝟙 _) j (centreMap j I) :=
    IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp]; rfl⟩
  rw [centreIdeal, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso sq.isoPullback.hom, IsPullback.isoPullback_hom_fst,
    ker_quotientMap]

omit [IsOpenImmersion j] in
theorem coe_support_centreIdeal :
    ((centreIdeal j I).support : Set X) = j '' PrimeSpectrum.zeroLocus (I : Set S) := by
  rw [centreIdeal, Scheme.Hom.support_ker, ← range_centreMap]
  exact (centreMap j I).isClosedEmbedding.isClosed_range.closure_eq

/-- **The ideal sheaf of the centre is of finite type** when `I` is finitely generated: its
ideal on an affine open `U` is the kernel of the surjection `Γ(X, U) → Γ(Spec S/I, U)` of finite
presentation. -/
theorem centreIdeal_fg (hI : I.FG) (U : X.affineOpens) : ((centreIdeal j I).ideal U).FG := by
  have : LocallyOfFinitePresentation (quotientMap I) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective
      (by rw [CommRingCat.hom_ofHom, Ideal.mk_ker]; exact hI)
  have : LocallyOfFinitePresentation (centreMap j I) := by
    rw [centreMap]
    infer_instance
  rw [centreIdeal, Scheme.Hom.ker_apply, RingHom.ker_eq_comap_bot]
  have hV : IsAffineOpen (centreMap j I ⁻¹ᵁ U) := U.2.preimage _
  have hfp := HasRingHomProperty.appLE @LocallyOfFinitePresentation (centreMap j I)
    inferInstance U ⟨_, hV⟩ le_rfl
  rw [Scheme.Hom.appLE_eq_app] at hfp
  exact Projectivity.fg_comap_of_surjective_of_finitePresentation _
    ((centreMap j I).app_surjective U U.2) hfp (Submodule.fg_bot)

end Ideal

section Main

variable {X : Scheme.{u}} [IsIntegral X] {A : Type u} [CommRing A] (I : Ideal A)
  {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) (φV : V₀.toScheme ⟶ Spec (.of A)) [Flat φV]
  (W₁ : X.Opens) [IsIso (pullback.snd (affineBlowupStructure I) φV ∣_ (V₀.ι ⁻¹ᵁ W₁))]

/-- The ring map `A → Γ(X, V₀)` of the chart `φV : V₀ → Spec A`. -/
def chartRingHom : CommRingCat.of A ⟶ Γ(X, V₀) := Spec.preimage (hV₀.isoSpec.inv ≫ φV)

omit [IsIntegral X] [Flat φV] in
theorem specMap_chartRingHom : Spec.map (chartRingHom hV₀ φV) = hV₀.isoSpec.inv ≫ φV :=
  Spec.map_preimage _

omit [IsIntegral X] in
/-- A morphism to the native blow-up is determined by its composite with the structure map, if
that composite lands in an open over which the blow-up is an isomorphism. -/
theorem eq_of_comp_eq_of_isIso {Y Z : Scheme.{u}} (π : Y ⟶ X) (W : X.Opens) [IsIso (π ∣_ W)]
    (g₁ g₂ : Z ⟶ Y) (h : g₁ ≫ π = g₂ ≫ π) (hW : Set.range (g₁ ≫ π) ⊆ W) : g₁ = g₂ := by
  have hr : ∀ g : Z ⟶ Y, g ≫ π = g₁ ≫ π → Set.range g ⊆ Set.range (π ⁻¹ᵁ W).ι := by
    rintro g hg _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change π (g z) ∈ W
    rw [← Scheme.Hom.comp_apply, hg]
    exact hW ⟨z, rfl⟩
  let l₁ := IsOpenImmersion.lift (π ⁻¹ᵁ W).ι g₁ (hr g₁ rfl)
  let l₂ := IsOpenImmersion.lift (π ⁻¹ᵁ W).ι g₂ (hr g₂ h.symm)
  have e₁ : l₁ ≫ (π ⁻¹ᵁ W).ι = g₁ := IsOpenImmersion.lift_fac _ _ _
  have e₂ : l₂ ≫ (π ⁻¹ᵁ W).ι = g₂ := IsOpenImmersion.lift_fac _ _ _
  have : l₁ = l₂ := by
    rw [← cancel_mono (π ∣_ W), ← cancel_mono W.ι, Category.assoc, Category.assoc,
      morphismRestrict_ι, reassoc_of% e₁, reassoc_of% e₂, h]
  rw [← e₁, ← e₂, this]

include hV₀ in
/-- **The extension of the pulled-back chart blow-up is a native blow-up.** Let `X` be integral,
`V₀ ⊆ X` an affine open, `φV : V₀ → Spec A` flat, `I ⊆ A` finitely generated, and
`W₁ ⊆ X` open with `V₀ ∪ W₁ = X`, `φV(V₀ ∩ W₁) ∩ V(I) = ∅` and `V₀ ∩ φV⁻¹V(I)` closed in `X`. Then
`extension W₁ (Bl_I ×_{Spec A} V₀ → V₀)` is isomorphic over `X` to the native blow-up of an ideal
sheaf of finite type on `X`. -/
theorem exists_iso_blowup (hI : I.FG) (hcov : V₀ ⊔ W₁ = ⊤)
    (hW : V₀.ι ⁻¹ᵁ W₁ ≤ φV ⁻¹ᵁ affineBlowupCenterComplement I)
    (hT : IsClosed (V₀.ι '' (φV ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)))) :
    ∃ (D : X.IdealSheafData)
      (e : Blowups.extension W₁ (pullback.snd (affineBlowupStructure I) φV) ≅ blowup D),
      (∀ U : X.affineOpens, (D.ideal U).FG) ∧
        e.hom ≫ blowupStructure D =
          Blowups.extensionHom W₁ (pullback.snd (affineBlowupStructure I) φV) := by
  classical
  set ρ := chartRingHom hV₀ φV
  let : Algebra A Γ(X, V₀) := ρ.hom.toAlgebra
  have hρ : Spec.map ρ = hV₀.isoSpec.inv ≫ φV := specMap_chartRingHom hV₀ φV
  have : Module.Flat A Γ(X, V₀) := by
    have : Flat (Spec.map ρ) := by rw [hρ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp this
  set I' : Ideal Γ(X, V₀) := I.map (algebraMap A Γ(X, V₀))
  -- flat base change of the blow-up over the chart
  have sq₀ := BlowupFlat.isPullback_affineBlowupMap_of_flat (R := A) (S := Γ(X, V₀)) I
  have sq : IsPullback (affineBlowupMap I (algebraMap A Γ(X, V₀)))
      (affineBlowupStructure I' ≫ hV₀.isoSpec.inv) (affineBlowupStructure I) φV := by
    refine sq₀.of_iso (Iso.refl _) (Iso.refl _) hV₀.isoSpec.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
      rfl
    · simp
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      rw [← hρ]
      rfl
  let eP := sq.isoPullback
  have heP : eP.inv ≫ affineBlowupStructure I' ≫ hV₀.isoSpec.inv =
      pullback.snd (affineBlowupStructure I) φV := by
    rw [Iso.inv_comp_eq]
    exact sq.isoPullback_hom_snd.symm
  -- the centre
  let j := hV₀.fromSpec
  have hzero : j '' PrimeSpectrum.zeroLocus (I' : Set Γ(X, V₀)) =
      V₀.ι '' (φV ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) := by
    have h1 : PrimeSpectrum.zeroLocus (I' : Set Γ(X, V₀)) =
        Spec.map ρ ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
      change _ = PrimeSpectrum.comap ρ.hom ⁻¹' _
      rw [PrimeSpectrum.preimage_comap_zeroLocus]
      conv_rhs => rw [← PrimeSpectrum.zeroLocus_span]
      rfl
    have h2 : j = hV₀.isoSpec.inv ≫ V₀.ι := (IsAffineOpen.isoSpec_inv_ι hV₀).symm
    rw [h1, hρ, h2, Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp,
      Set.image_preimage_eq _ hV₀.isoSpec.inv.surjective]
  have : IsClosedImmersion (centreMap j I') :=
    isClosedImmersion_centreMap j I' (by rw [hzero]; exact hT)
  set D := centreIdeal j I'
  have hDI : D.comap j = specIdealSheaf Γ(X, V₀) I' := comap_centreIdeal j I'
  have hsupp : W₁ ≤ D.support.compl := by
    intro x hx hxD
    rw [coe_support_centreIdeal, hzero] at hxD
    obtain ⟨v, hv, rfl⟩ := hxD
    exact (hW (show V₀.ι v ∈ W₁ from hx)) hv
  have : IsIso (blowupStructure D ∣_ D.support.compl) :=
    BlowupComplement.blowupStructure_supportComplement_isIso D
  have : IsIso (blowupStructure D ∣_ W₁) := Blowups.isIso_morphismRestrict_of_le _ hsupp
  -- the maps from the two pieces
  set f := pullback.snd (affineBlowupStructure I) φV
  let gP : pullback (affineBlowupStructure I) φV ⟶ blowup D :=
    eP.inv ≫ BlowupOpenChart.chartMap j D I' hDI
  have hgP : gP ≫ blowupStructure D = f ≫ V₀.ι := by
    simp only [gP, Category.assoc, BlowupOpenChart.chartMap_structure]
    rw [show j = hV₀.isoSpec.inv ≫ V₀.ι from (IsAffineOpen.isoSpec_inv_ι hV₀).symm,
      ← Category.assoc (affineBlowupStructure I'), ← Category.assoc, heP]
  let gW : W₁.toScheme ⟶ blowup D :=
    inv (blowupStructure D ∣_ W₁) ≫ (blowupStructure D ⁻¹ᵁ W₁).ι
  have hgW : gW ≫ blowupStructure D = W₁.ι := by
    simp only [gW, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  let gs : (b : Bool) → Blowups.extensionObj (pullback (affineBlowupStructure I) φV) W₁ b ⟶
      blowup D
    | false => gP
    | true => gW
  have hgs : ∀ b, gs b ≫ blowupStructure D = Blowups.extensionToBase W₁ f b := by
    rintro (_ | _)
    · exact hgP
    · exact hgW
  have hcoc : ∀ b, Blowups.extensionArrow W₁ f b ≫ gs b =
      Blowups.extensionArrow W₁ f false ≫ gP := by
    intro b
    refine eq_of_comp_eq_of_isIso (blowupStructure D) W₁ _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, hgs b, Blowups.extensionArrow_toBase,
        show gP = gs false from rfl, hgs false, Blowups.extensionArrow_toBase]
    · rw [Category.assoc, hgs b, Blowups.extensionArrow_toBase,
        ← Blowups.extensionArrow_toBase W₁ f true]
      rintro _ ⟨z, rfl⟩
      exact (Blowups.extensionArrow W₁ f true z).2
  let Φ : Blowups.extension W₁ f ⟶ blowup D :=
    colimit.desc (Blowups.extensionSpan W₁ f)
      (WidePushoutShape.mkCocone (Blowups.extensionArrow W₁ f false ≫ gP) gs hcoc)
  have hΦ₁ : Blowups.extensionι₁ W₁ f ≫ Φ = gP := colimit.ι_desc _ _
  have hΦ₂ : Blowups.extensionι₂ W₁ f ≫ Φ = gW := colimit.ι_desc _ _
  have hΦ : Φ ≫ blowupStructure D = Blowups.extensionHom W₁ f := by
    refine colimit.hom_ext fun i ↦ ?_
    rcases i with _ | (_ | _)
    · rw [← Blowups.extensionArrow_ι W₁ f false, Category.assoc, Category.assoc]
      change _ ≫ Blowups.extensionι₁ W₁ f ≫ Φ ≫ _ = _ ≫ Blowups.extensionι₁ W₁ f ≫ _
      rw [reassoc_of% hΦ₁, hgP, Blowups.extensionι₁_extensionHom]
    · change Blowups.extensionι₁ W₁ f ≫ Φ ≫ _ = Blowups.extensionι₁ W₁ f ≫ _
      rw [reassoc_of% hΦ₁, hgP, Blowups.extensionι₁_extensionHom]
    · change Blowups.extensionι₂ W₁ f ≫ Φ ≫ _ = Blowups.extensionι₂ W₁ f ≫ _
      rw [reassoc_of% hΦ₂, hgW, Blowups.extensionι₂_extensionHom]
  -- `Φ` is an isomorphism, checked over `V₀` and over `W₁`
  set O : (blowup D).Opens := blowupStructure D ⁻¹ᵁ j.opensRange
  have hjV : j.opensRange = V₀ := IsAffineOpen.opensRange_fromSpec hV₀
  have hiso₁ : IsIso (Φ ∣_ O) := by
    have hrange : Set.range (Blowups.extensionι₁ W₁ f) = Set.range (Φ ⁻¹ᵁ O).ι := by
      rw [Scheme.Opens.range_ι, ← Blowups.extensionHom_preimage_U]
      change _ = (Φ ≫ blowupStructure D) ⁻¹' (j.opensRange : Set X)
      rw [hΦ, hjV]
      rfl
    let e₁ := IsOpenImmersion.isoOfRangeEq (Blowups.extensionι₁ W₁ f) (Φ ⁻¹ᵁ O).ι hrange
    let e₂ := BlowupOpenChart.chartIso j D I' hDI
    have he : e₁.hom ≫ (Φ ∣_ O) = eP.inv ≫ e₂.hom := by
      rw [← cancel_mono O.ι, Category.assoc, morphismRestrict_ι, Category.assoc,
        BlowupOpenChart.chartIso_hom_ι]
      rw [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, hΦ₁]
    have : Φ ∣_ O = e₁.inv ≫ eP.inv ≫ e₂.hom := by rw [← he, Iso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  have hiso₂ : IsIso (Φ ∣_ (blowupStructure D ⁻¹ᵁ W₁)) := by
    have h1 : IsIso ((Φ ≫ blowupStructure D) ∣_ W₁) := by
      rw [hΦ]
      infer_instance
    rw [morphismRestrict_comp] at h1
    exact IsIso.of_isIso_comp_right (Φ ∣_ (blowupStructure D ⁻¹ᵁ W₁)) (blowupStructure D ∣_ W₁)
  have hcov' : (⨆ b : Bool, if b then O else blowupStructure D ⁻¹ᵁ W₁) = ⊤ := by
    apply top_le_iff.mp
    intro y _
    have hy : blowupStructure D y ∈ V₀ ⊔ W₁ := by rw [hcov]; trivial
    rcases hy with hy | hy
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true, by
        change blowupStructure D y ∈ j.opensRange
        rw [hjV]
        exact hy⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, hy⟩
  have : IsIso Φ := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      _ hcov' fun b ↦ ?_
    cases b
    · exact hiso₂
    · exact hiso₁
  exact ⟨D, asIso Φ, fun U ↦ centreIdeal_fg j I' (hI.map _) U, hΦ⟩

include hV₀ in
/-- **The extended chart blow-up is projective** (SERRE-I): in the situation of
`exists_iso_blowup`, if `X` is projective and of finite presentation over a ring `E`, so is the
extension of the pulled-back blow-up. -/
theorem isProjectiveOver_extensionHom (hI : I.FG) (hcov : V₀ ⊔ W₁ = ⊤)
    (hW : V₀.ι ⁻¹ᵁ W₁ ≤ φV ⁻¹ᵁ affineBlowupCenterComplement I)
    (hT : IsClosed (V₀.ι '' (φV ⁻¹' PrimeSpectrum.zeroLocus (I : Set A))))
    {E : Type u} [CommRing E] (p : X ⟶ Spec (.of E)) (hp : IsProjectiveOver p)
    [LocallyOfFinitePresentation p] :
    IsProjectiveOver
      (Blowups.extensionHom W₁ (pullback.snd (affineBlowupStructure I) φV) ≫ p) := by
  obtain ⟨D, e, hD, he⟩ := exists_iso_blowup I hV₀ φV W₁ hI hcov hW hT
  obtain ⟨n, i, hi, hip⟩ := Projectivity.isProjectiveOver_blowupStructure_comp_of_fg D p hp hD
  have := hi
  exact ⟨n, e.hom ≫ i, inferInstance, by rw [Category.assoc, hip, ← Category.assoc, he]⟩

end Main

end DeJongAlterations.StableModification.Gluing.BlowupProjective
