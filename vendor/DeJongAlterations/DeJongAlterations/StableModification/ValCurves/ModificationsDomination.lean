import DeJongAlterations.StableModification.ValCurves.ModificationsGamma

/-!
# Domination of modifications (Temkin, Proposition 4.2.3)

Let `S` be a scheme whose local rings are valuation rings, `φ : C → S` a quasi-compact separated
relative curve with `C` integral, and `f' : C' → C`, `f'' : C'' → C` modifications with `C''`
normal. M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
Proposition 4.2.3 (`schmodprop`, `semi-stable.tex` lines 2930–2946): if `Γ₀(C') ⊆ Γ₀(C'')`, then
`C''` dominates `C'`, i.e. `f''` factors through `f'` (`exists_comp_eq_of_gammaZeroSet_subset`).

## Proof

`Γ(C') ⊆ Γ(C'')` by Lemma 4.2.2 (`gammaSet_subset_of_gammaZeroSet_subset`). Let `C̄` be the
schematic closure of `Spec L` in `C' ×_C C''` (the schematic image of the point
`(η', η'') : Spec L → C' ×_C C''`, RZ1's `RiemannZariskiSpace.dominatePoint`), with projections
`q₁ : C̄ → C'`, `q₂ : C̄ → C''`. Every point `x̄` of `C̄` has residue field algebraic over that of
`q₂ x̄`:

* `C̄` is a relative curve: its generic point lies over the generic point of `C`, over which
  `f'` is an isomorphism, so `κ` of the generic point of `C̄` is algebraic over that of `C''`
  (residue fields of fibre products, `isAlgebraicAt_pullback_snd`);
* if `q₂ x̄ ∈ (C''/S)⁰` this follows from additivity of transcendence degrees;
* otherwise `q₁ x̄ ∉ (C'/S)⁰`: a valuation ring centred at `x̄` lies in `Γ(C')` if `q₁ x̄` does,
  hence in `Γ(C'')`, and its centre on the separated `C''` is `q₂ x̄`. So `κ(q₁ x̄)` is algebraic
  over the base, and then so is `κ(x̄)` over `κ(q₂ x̄)` (residue fields of fibre products; this
  is "x has to be a closed point of `C̄_s`", T:2945).

Hence the proper map `q₂` is finite (`exists_isFinite_morphismRestrict_of_isAlgebraicAt`, i.e.
"its S-fibres do not contract components", T:2937), it is an isomorphism at the generic point,
and `C''` is normal, so `q₂` is an isomorphism (`isIso_of_isFinite_of_isIso_stalkMap`) and
`q₂⁻¹ ≫ q₁ : C'' → C'` is the required morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology IsLocalRing

universe u

namespace DeJongAlterations.StableModification.ValCurves

open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)
open Geometry.ModificationCenter (isomorphismOpen center)
open RiemannZariskiSpace (toSpecValuationSubring specClosedPoint ofScheme)

section Auxiliary

variable {X Y Z : Scheme.{u}}

/-- A modification is an isomorphism on local rings at points over its isomorphism open. -/
theorem isIso_stalkMap_of_mem_isomorphismOpen (f : X ⟶ Y) {x : X}
    (hx : f x ∈ isomorphismOpen f) : IsIso (f.stalkMap x) := by
  let W := isomorphismOpen f
  let p : (f ⁻¹ᵁ W).toScheme := ⟨x, hx⟩
  have : IsIso ((f ∣_ W).stalkMap p) := inferInstance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (morphismRestrictStalkMap f W p)).mp this

/-- **Residue fields of a fibre product**, second projection: if `κ(x)/κ(f x)` is algebraic for
`x = pullback.fst f g t`, then `κ(t)` is algebraic over `κ(pullback.snd f g t)`. -/
theorem isAlgebraicAt_pullback_snd {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (t : ↑(pullback f g)) (h : IsAlgebraicAt f (pullback.fst f g t)) :
    IsAlgebraicAt (pullback.snd f g) t := by
  let e := pullbackSymmetry f g
  have h1 : pullback.snd g f (e.hom t) = pullback.fst f g t := by
    rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_snd]
  have h2 : IsAlgebraicAt (pullback.fst g f) (e.hom t) :=
    isAlgebraicAt_pullback_fst g f (e.hom t) (h1 ▸ h)
  have h3 : IsAlgebraicAt (e.hom ≫ pullback.fst g f) t :=
    IsAlgebraicAt.comp isAlgebraicAt_of_isIso_stalkMap h2
  rwa [pullbackSymmetry_hom_comp_fst] at h3

/-- A residue field map whose stalk map is surjective is surjective. -/
theorem residueFieldMap_surjective_of_stalkMap_surjective {g : X ⟶ Y} {x : X}
    (h : Function.Surjective (g.stalkMap x)) : Function.Surjective (g.residueFieldMap x) := by
  intro z
  obtain ⟨b, rfl⟩ := X.residue_surjective x z
  obtain ⟨a, rfl⟩ := h b
  refine ⟨Y.residue (g x) a, ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]

/-- At the generic point of an integral scheme the residue map is injective. -/
theorem residue_injective_of_isField {x : X} (hx : IsField (X.presheaf.stalk x)) :
    Function.Injective (X.residue x) := by
  let := hx.toField
  intro a b hab
  have h1 : IsLocalRing.residue (X.presheaf.stalk x) (a - b) = 0 := by
    change (X.residue x) (a - b) = 0
    rw [map_sub, hab, sub_self]
  have hmem := (residue_eq_zero_iff (a - b)).mp h1
  rw [maximalIdeal_eq_bot, Ideal.mem_bot, sub_eq_zero] at hmem
  exact hmem

/-- A morphism of integral schemes mapping generic point to generic point, with surjective
residue field map there, is an isomorphism on the generic local rings. -/
theorem isIso_stalkMap_genericPoint [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (hgen : f (genericPoint X) = genericPoint Y)
    (hsurj : Function.Surjective (f.residueFieldMap (genericPoint X))) :
    IsIso (f.stalkMap (genericPoint X)) := by
  have hY : IsField (Y.presheaf.stalk (f (genericPoint X))) := by
    rw [hgen]
    exact Field.toIsField Y.functionField
  have hX : IsField (X.presheaf.stalk (genericPoint X)) := Field.toIsField X.functionField
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, fun b ↦ ?_⟩
  · let := hY.toField
    exact (f.stalkMap (genericPoint X)).hom.injective
  · obtain ⟨c, hc⟩ := hsurj (X.residue _ b)
    obtain ⟨a, rfl⟩ := Y.residue_surjective _ c
    refine ⟨a, residue_injective_of_isField hX ?_⟩
    rw [← hc, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.residue_residueFieldMap]

/-- Precomposing a surjective ring map with an isomorphism keeps it surjective. -/
theorem surjective_isIso_comp {A B D : CommRingCat.{u}} (e : A ⟶ B) [IsIso e] {g : B ⟶ D}
    (hg : Function.Surjective g) : Function.Surjective (e ≫ g) := by
  intro w
  obtain ⟨v, rfl⟩ := hg w
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso e).2 v
  exact ⟨a, rfl⟩

/-- A separated morphism to a separated scheme has separated source. -/
theorem isSeparated_of_isSeparated (f : X ⟶ Y) [IsSeparated f] [Y.IsSeparated] :
    X.IsSeparated :=
  ⟨by rw [← terminal.comp_from f]; infer_instance⟩

end Auxiliary

variable {S C C' C'' : Scheme.{u}} [∀ s : S, PreValuationRing (S.presheaf.stalk s)]
  (φ : C ⟶ S) [IsIntegral C] [IsIntegral C'] [IsIntegral C'']
  (f' : C' ⟶ C) (f'' : C'' ⟶ C) [IsModification f'] [IsModification f'']

/-- **Temkin, proof of Proposition 4.2.3, first step**: `Γ₀(C') ⊆ Γ₀(C'')` implies
`Γ(C') ⊆ Γ(C'')`, by Lemma 4.2.2 (`gammaSet_eq_union`) for `C'` and `C''`. -/
theorem gammaSet_subset_of_gammaZeroSet_subset [CompactSpace C]
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    (h : gammaZeroSet (f' ≫ φ) (genericLift f') (genericPt C) ⊆
      gammaZeroSet (f'' ≫ φ) (genericLift f'') (genericPt C)) :
    gammaSet (f' ≫ φ) (genericLift f') ⊆ gammaSet (f'' ≫ φ) (genericLift f'') := by
  rw [gammaSet_eq_union φ f' hdim, gammaSet_eq_union φ f'' hdim]
  refine Set.union_subset_union_left _ fun V ⟨W, hW, hVW⟩ ↦ ⟨W, h hW, hVW⟩

/-- **Temkin, Proposition 4.2.3** (`schmodprop`): let `C → S` be a quasi-compact separated
relative curve over a base whose local rings are valuation rings, and let `f' : C' → C` and
`f'' : C'' → C` be modifications with `C''` normal. If `Γ₀(C') ⊆ Γ₀(C'')`, then `C''` dominates
`C'`: there is `g : C'' → C'` with `g ≫ f' = f''`. -/
theorem exists_comp_eq_of_gammaZeroSet_subset [CompactSpace C] [C.IsSeparated]
    (hnormal : IsNormalScheme C'') (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    (h : gammaZeroSet (f' ≫ φ) (genericLift f') (genericPt C) ⊆
      gammaZeroSet (f'' ≫ φ) (genericLift f'') (genericPt C)) :
    ∃ g : C'' ⟶ C', g ≫ f' = f'' := by
  have hΓ := gammaSet_subset_of_gammaZeroSet_subset φ f' f'' hdim h
  have : C''.IsSeparated := isSeparated_of_isSeparated f''
  -- the schematic closure of `Spec L` in `C' ×_C C''`
  have hη : genericLift f' ≫ f' = genericLift f'' ≫ f'' := by
    rw [genericLift_comp, genericLift_comp]
  let p := RiemannZariskiSpace.dominatePoint hη
  let ι := p.imageι
  let ηb := p.toImage
  let q₁ : p.image ⟶ C' := ι ≫ pullback.fst f' f''
  let q₂ : p.image ⟶ C'' := ι ≫ pullback.snd f' f''
  have hq₁ : ηb ≫ q₁ = genericLift f' := by
    simp only [ηb, q₁, ι, Scheme.Hom.toImage_imageι_assoc, p,
      RiemannZariskiSpace.dominatePoint_fst]
  have hq₂ : ηb ≫ q₂ = genericLift f'' := by
    simp only [ηb, q₂, ι, Scheme.Hom.toImage_imageι_assoc, p,
      RiemannZariskiSpace.dominatePoint_snd]
  have hq : q₁ ≫ f' = q₂ ≫ f'' := by
    simp only [q₁, q₂, Category.assoc, pullback.condition]
  have : IsProper q₂ := by dsimp only [q₂]; infer_instance
  -- the generic point of `C̄`
  obtain ⟨z⟩ : Nonempty (Spec (.of C.functionField)) := inferInstance
  have hz : ηb z = genericPoint p.image := by
    have := genericPoint_map_of_isDominant ηb
    rwa [Subsingleton.elim (genericPoint (Spec (.of C.functionField))) z] at this
  -- `C̄` is a relative curve
  have hgen₁ : (q₁ ≫ f') (genericPoint p.image) = genericPoint C := by
    rw [← hz, ← Scheme.Hom.comp_apply, reassoc_of% hq₁, genericLift_comp, genericPt_apply]
  have halg_gen : IsAlgebraicAt q₂ (genericPoint p.image) := by
    have hW : f' (q₁ (genericPoint p.image)) ∈ isomorphismOpen f' := by
      have hmem := genericPt_range_subset_isomorphismOpen f' ⟨z, rfl⟩
      obtain ⟨w, hw⟩ := hmem
      rw [genericPt_apply] at hw
      change (q₁ ≫ f') (genericPoint p.image) ∈ _
      rw [hgen₁, ← hw]
      exact w.2
    have : IsIso (f'.stalkMap (pullback.fst f' f'' (ι (genericPoint p.image)))) :=
      isIso_stalkMap_of_mem_isomorphismOpen f' hW
    have h1 : IsAlgebraicAt f' (pullback.fst f' f'' (ι (genericPoint p.image))) :=
      isAlgebraicAt_of_isIso_stalkMap
    exact (isAlgebraicAt_of_surjectiveOnStalks ι _).comp
      (isAlgebraicAt_pullback_snd f' f'' _ h1)
  have hcurve : ∀ xb : p.image, fiberTrdeg (q₂ ≫ f'' ≫ φ) xb ≤ 1 := by
    intro xb
    refine (fiberTrdeg_le_genericPoint (q₂ ≫ f'' ≫ φ) xb).trans ?_
    rw [fiberTrdeg_comp, (isAlgebraicAt_iff_fiberTrdeg_eq_zero _ _).mp halg_gen, add_zero]
    exact fiberTrdeg_le_one φ hdim f'' _
  -- every point of `C̄` is algebraic over its image in `C''`
  have halg : ∀ xb : p.image, IsAlgebraicAt q₂ xb := by
    intro xb
    have hb := hcurve xb
    rw [fiberTrdeg_comp] at hb
    by_cases hx'' : q₂ xb ∈ fibreGenericSet (f'' ≫ φ)
    · rw [hx''] at hb
      exact (isAlgebraicAt_iff_fiberTrdeg_eq_zero _ _).mpr (Cardinal.eq_zero_of_one_add_le_one hb)
    · -- the image in `C'` is not in `(C'/S)⁰`
      have hx' : q₁ xb ∉ fibreGenericSet (f' ≫ φ) := by
        intro hx'
        obtain ⟨V, ψ, hψ, hψx⟩ := RiemannZariskiSpace.image_exists_extension_closedPoint_eq p xb
        have hV : IsCentre ηb V xb := ⟨ψ, hψ, hψx⟩
        have hV₁ : IsCentre (genericLift f') V (q₁ xb) := hq₁ ▸ hV.comp q₁
        have hV₂ : IsCentre (genericLift f'') V (q₂ xb) := hq₂ ▸ hV.comp q₂
        obtain ⟨y'', hy'', hV''⟩ := hΓ ⟨q₁ xb, hx', hV₁⟩
        exact hx'' (hV₂.unique hV'' ▸ hy'')
      have h0 : fiberTrdeg (f' ≫ φ) (q₁ xb) = 0 :=
        Cardinal.eq_zero_of_le_one_of_ne_one (fiberTrdeg_le_one φ hdim f' _) hx'
      rw [fiberTrdeg_comp] at h0
      have h1 : IsAlgebraicAt f' (pullback.fst f' f'' (ι xb)) :=
        (isAlgebraicAt_iff_fiberTrdeg_eq_zero _ _).mpr (add_eq_zero.mp h0).2
      exact (isAlgebraicAt_of_surjectiveOnStalks ι _).comp
        (isAlgebraicAt_pullback_snd f' f'' _ h1)
  -- `q₂` is finite
  have : LocallyQuasiFinite q₂ := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    refine top_le_iff.mp fun xb _ ↦ ?_
    obtain ⟨V, hyV, hV, -⟩ :=
      exists_isFinite_morphismRestrict_of_isAlgebraicAt q₂ (q₂ xb) fun x _ ↦ halg x
    exact quasiFiniteAt_of_isFinite_morphismRestrict q₂ V hyV
  have : IsFinite q₂ := IsFinite.of_isProper_of_locallyQuasiFinite q₂
  -- `q₂` is an isomorphism at the generic point
  have hgen₂ : q₂ (genericPoint p.image) = genericPoint C'' := by
    rw [← hz, ← Scheme.Hom.comp_apply, hq₂, genericLift_apply]
  have hsurj : Function.Surjective (q₂.residueFieldMap (genericPoint p.image)) := by
    have hpt : Function.Surjective ((genericPt C).residueFieldMap z) :=
      residueFieldMap_surjective_of_stalkMap_surjective
        (show Function.Surjective ((C.fromSpecStalk (genericPoint C)).stalkMap z) from
          Scheme.Hom.stalkMap_surjective _ _)
    have h1 : Function.Surjective ((genericLift f'' ≫ f'').residueFieldMap z) := by
      rw [Scheme.Hom.residueFieldMap_congr (genericLift_comp f'') z]
      exact surjective_isIso_comp _ hpt
    rw [Scheme.residueFieldMap_comp] at h1
    have h2 : Function.Surjective ((genericLift f'').residueFieldMap z) :=
      Function.Surjective.of_comp h1
    have h3 : Function.Surjective ((ηb ≫ q₂).residueFieldMap z) := by
      rw [Scheme.Hom.residueFieldMap_congr hq₂ z]
      exact surjective_isIso_comp _ h2
    rw [Scheme.residueFieldMap_comp] at h3
    have hinj : Function.Injective (ηb.residueFieldMap z) := (ηb.residueFieldMap z).hom.injective
    rw [← hz]
    intro b
    obtain ⟨c, hc⟩ := h3 (ηb.residueFieldMap z b)
    exact ⟨c, hinj hc⟩
  have : IsIso (q₂.stalkMap (genericPoint p.image)) := isIso_stalkMap_genericPoint q₂ hgen₂ hsurj
  have : IsIso q₂ := isIso_of_isFinite_of_isIso_stalkMap q₂ hgen₂ hnormal
  refine ⟨inv q₂ ≫ q₁, ?_⟩
  rw [Category.assoc, hq, IsIso.inv_hom_id_assoc]

end DeJongAlterations.StableModification.ValCurves
