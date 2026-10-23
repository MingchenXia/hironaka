import DeJongAlterations.StableModification.Blowups.Basic
import DeJongAlterations.StableModification.Curves.Basic

/-!
# Flat base change of modifications

M. Temkin, *Stable modification of relative curves*, proof of Prop 4.3.1 (T:2976–2983): a blow-up
`C̄' ⟶ C̄` of a standard model is spread to the curve `C` along an étale map `C ⟶ C̄` by base
change, `C' := C̄' ×_C̄ C`. This file records the formal part (`lem:sm-modification-extension`,
second bullet):

* `isIso_pullback_snd_restrict`: if `f : X ⟶ Y` is an isomorphism over an open `V ⊆ Y`, then its
  base change along any `g : Y' ⟶ Y` is an isomorphism over `g⁻¹(V)`; in particular the
  modification locus of the base change is the inverse image of the modification locus;
* `isSchematicModification_pullback_snd`: a proper morphism which is an isomorphism over a
  quasi-compact open `V` with `V` and `f⁻¹(V)` schematically dense base changes along a flat
  `g` to a modification in Temkin's sense (`Curves.IsSchematicModification`);
* `isModification_pullback_snd`: a modification (de Jong's sense) base changes along a flat
  `g : Y' ⟶ Y` from an integral `Y'` to a modification, provided the fibre product is reduced.

Strict semi-stability of the base change of a strictly semi-stable blow-up along an étale map is
`Curves.IsStrictlySemistable.etale_comp` (the projection `C' ⟶ C̄'` is étale).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace DeJongAlterations.StableModification.Blowups

universe u

open Curves

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The restriction of the base-change square to the inverse images of an open `V ⊆ Y`. -/
theorem isPullback_pullback_restrict (V : Y.Opens) :
    IsPullback ((pullback.fst f g).resLE (f ⁻¹ᵁ V) (pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ V)) (by
        intro x hx
        change (pullback.fst f g ≫ f) x ∈ V
        rw [pullback.condition]
        exact hx))
      (pullback.snd f g ∣_ (g ⁻¹ᵁ V)) (f ∣_ V) (g ∣_ V) := by
  have hUY : pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ V) =
      pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ V) ⊓ pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage (pullback.fst f g), pullback.condition,
      Scheme.Hom.comp_preimage, inf_idem]
  have H := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g) (US := V)
    (UT := g ⁻¹ᵁ V) (UX := f ⁻¹ᵁ V) le_rfl le_rfl hUY
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using H

/-- **Base change preserves the isomorphism locus**: if `f` is an isomorphism over `V`, then
`pullback.snd f g` is an isomorphism over `g⁻¹(V)`. -/
theorem isIso_pullback_snd_restrict (V : Y.Opens) [IsIso (f ∣_ V)] :
    IsIso (pullback.snd f g ∣_ (g ⁻¹ᵁ V)) :=
  (isPullback_pullback_restrict f g V).isIso_snd_of_isIso

/-- **Flat base change of modifications.** Let `f : X ⟶ Y` be proper and an isomorphism over a
quasi-compact open `V` such that `V` and `f⁻¹(V)` are schematically dense. Then for any flat
`g : Y' ⟶ Y` the base change `pullback.snd f g` is a modification in Temkin's sense, an
isomorphism over the schematically dense open `g⁻¹(V)`. -/
theorem isSchematicModification_pullback_snd [IsProper f] [Flat g] (V : Y.Opens)
    [QuasiCompact V.ι] (hV : IsSchemeTheoreticallyDominant V.ι)
    (hfV : IsSchemeTheoreticallyDominant (f ⁻¹ᵁ V).ι) [IsIso (f ∣_ V)] :
    IsSchematicModification (pullback.snd f g) where
  toIsProper := inferInstance
  exists_isIso := by
    refine ⟨g ⁻¹ᵁ V, ?_, ?_, isIso_pullback_snd_restrict f g V⟩
    · exact IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict g V)
    · have hqc : QuasiCompact (f ⁻¹ᵁ V).ι :=
        MorphismProperty.of_isPullback (isPullback_morphismRestrict f V) inferInstance
      have hpre : pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ V) = pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ V) := by
        rw [← Scheme.Hom.comp_preimage, ← pullback.condition, Scheme.Hom.comp_preimage]
      rw [hpre]
      exact IsSchemeTheoreticallyDominant.of_isPullback
        (isPullback_morphismRestrict (pullback.fst f g) (f ⁻¹ᵁ V))

/-- **Flat base change of modifications of integral schemes.** Let `f : X ⟶ Y` be a
modification and `g : Y' ⟶ Y` flat with `Y'` integral. If `X ×_Y Y'` is reduced (e.g. when `g`
is étale and `X` is normal), then `pullback.snd f g` is a modification: every point of
`X ×_Y Y'` generizes, by flatness of the projection to `X`, to a point over the generic point of
`X`, hence into the inverse image of the isomorphism locus, which is irreducible. -/
theorem isModification_pullback_snd [hf : IsModification f] [Flat g] [IsIntegral Y']
    [IsReduced (pullback f g)] : IsModification (pullback.snd f g) := by
  have := hf.sourceIntegral
  have := hf.targetIntegral
  obtain ⟨V, hV, -, hiso⟩ := (IsModification.isSchematicModification (f := f)).exists_isIso
  have hVne : (V : Set Y).Nonempty := nonempty_of_isSchemeTheoreticallyDominant V
  have hηV : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using hVne)
  have hiso' := isIso_pullback_snd_restrict f g V
  -- the inverse image of `V` in `Y'` is nonempty
  obtain ⟨y'₀⟩ : Nonempty Y' := inferInstance
  obtain ⟨y'₁, -, hy'₁⟩ := Flat.generalizingMap g (genericPoint_specializes (g y'₀))
  have hOne : ((g ⁻¹ᵁ V : Y'.Opens) : Set Y').Nonempty := ⟨y'₁, by
    change g y'₁ ∈ V
    rw [hy'₁]
    exact hηV⟩
  -- the inverse image `O` of `g⁻¹(V)` in the pullback is irreducible
  let O : (pullback f g).Opens := pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ V)
  have : Nonempty (g ⁻¹ᵁ V).toScheme := hOne.to_subtype
  have : IsIntegral (g ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (g ⁻¹ᵁ V).ι
  have : Nonempty O.toScheme := by
    obtain ⟨y⟩ := ‹Nonempty (g ⁻¹ᵁ V).toScheme›
    obtain ⟨x, -⟩ := (pullback.snd f g ∣_ (g ⁻¹ᵁ V)).surjective y
    exact ⟨x⟩
  have : IsIntegral O.toScheme :=
    isIntegral_of_isOpenImmersion (asIso (pullback.snd f g ∣_ (g ⁻¹ᵁ V))).hom
  have hO : IsIrreducible (O : Set ↥(pullback f g)) := by
    have h := (IrreducibleSpace.isIrreducible_univ O.toScheme).image O.ι O.ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at h
  -- every point of the pullback is a specialization of a point of `O`
  have hcl : closure (O : Set ↥(pullback f g)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    obtain ⟨q, hqp, hq⟩ :=
      Flat.generalizingMap (pullback.fst f g) (genericPoint_specializes (pullback.fst f g p))
    have hqO : q ∈ (O : Set ↥(pullback f g)) := by
      change g (pullback.snd f g q) ∈ V
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hq,
        genericPoint_map_of_isDominant f]
      exact hηV
    exact closure_mono (Set.singleton_subset_iff.mpr hqO) (specializes_iff_mem_closure.mp hqp)
  have hirr : IsIrreducible (Set.univ : Set ↥(pullback f g)) := hcl ▸ hO.closure
  have : IrreducibleSpace ↥(pullback f g) := (irreducibleSpace_def _).mpr hirr
  have : IsIntegral (pullback f g) := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsDominant (pullback.snd f g) := by
    refine ⟨((g ⁻¹ᵁ V).isOpen.dense hOne).mono ?_⟩
    intro y hy
    obtain ⟨x, hx⟩ := (pullback.snd f g ∣_ (g ⁻¹ᵁ V)).surjective ⟨y, hy⟩
    refine ⟨x.1, ?_⟩
    have := congrArg Subtype.val hx
    rw [morphismRestrict_base_coe] at this
    exact this
  exact { toIsProper := inferInstance
          sourceIntegral := inferInstance
          targetIntegral := inferInstance
          birational := birationalOver_id_of_isIso_morphismRestrict _ (g ⁻¹ᵁ V) hOne }

end DeJongAlterations.StableModification.Blowups
