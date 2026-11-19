import Hironaka.Geometry.CurveFibrationMarkedOpenPoints

/-! # The actual ORIGINAL section maps restricted to a genuine original BASE open. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace Hironaka.Geometry.CurveFibrationMarkedOpen
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The native open-fibre Cartesian isomorphism retains its actual inverse first projection. -/
theorem restrictionPullbackIso_inv_fst {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) :
    ((isPullback_morphismRestrict f V).flip).isoPullback.inv ≫ (f ⁻¹ᵁ V).ι = pullback.fst f V.ι := by
  calc
    _ = ((isPullback_morphismRestrict f V).flip).isoPullback.inv ≫
        (((isPullback_morphismRestrict f V).flip).isoPullback.hom ≫ pullback.fst f V.ι) :=
      congrArg (fun t => ((isPullback_morphismRestrict f V).flip).isoPullback.inv ≫ t)
        ((isPullback_morphismRestrict f V).flip).isoPullback_hom_fst.symm
    _ = _ := by simp

/-- The native open-fibre Cartesian isomorphism retains its actual inverse structure map. -/
theorem restrictionPullbackIso_inv_snd {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) :
    ((isPullback_morphismRestrict f V).flip).isoPullback.inv ≫ (f ∣_ V) = pullback.snd f V.ι := by
  calc
    _ = ((isPullback_morphismRestrict f V).flip).isoPullback.inv ≫
        (((isPullback_morphismRestrict f V).flip).isoPullback.hom ≫ pullback.snd f V.ι) :=
      congrArg (fun t => ((isPullback_morphismRestrict f V).flip).isoPullback.inv ≫ t)
        ((isPullback_morphismRestrict f V).flip).isoPullback_hom_snd.symm
    _ = _ := by simp

/-- The ORIGINAL section restricted to the literal native source and target open schemes. -/
def restrictedSection {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) : V.toScheme ⟶ (f ⁻¹ᵁ V).toScheme :=
  CurveFibrationBaseChange.originalSectionBaseChange f V.ι σ hσ ≫
    ((isPullback_morphismRestrict f V).flip).isoPullback.inv

@[reassoc (attr := simp)]
theorem restrictedSection_fst {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) :
    restrictedSection f V σ hσ ≫ (f ⁻¹ᵁ V).ι = V.ι ≫ σ := by
  simp [restrictedSection, Category.assoc]

@[reassoc (attr := simp)]
theorem restrictedSection_snd {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) :
    restrictedSection f V σ hσ ≫ (f ∣_ V) = 𝟙 V.toScheme := by
  simp [restrictedSection, Category.assoc]

@[simp]
theorem restrictedSection_apply {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) (s : V) :
    (f ⁻¹ᵁ V).ι (restrictedSection f V σ hσ s) = σ s.val := by
  have H := congrArg (fun m => m s) (restrictedSection_fst f V σ hσ)
  change (f ⁻¹ᵁ V).ι (restrictedSection f V σ hσ s) = σ s.val at H
  exact H

/-- The actual ORIGINAL section's closed immersion is retained on the literal native source open. -/
theorem restrictedSection_isClosedImmersion {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (σ : S ⟶ X) [IsClosedImmersion σ] (hσ : σ ≫ f = 𝟙 S) :
    IsClosedImmersion (restrictedSection f V σ hσ) := by
  let : IsClosedImmersion (CurveFibrationBaseChange.originalSectionBaseChange f V.ι σ hσ) :=
    CurveFibrationBaseChange.originalSectionBaseChange_isClosedImmersion f V.ι σ hσ
  dsimp [restrictedSection]
  infer_instance

/-- The literal restricted section has exactly its ORIGINAL section-image inverse image. -/
theorem restrictedSection_range {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) :
    Set.range (restrictedSection f V σ hσ) = (f ⁻¹ᵁ V).ι ⁻¹' Set.range σ := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.val, (restrictedSection_apply f V σ hσ s).symm⟩
  · rintro ⟨s, hs⟩
    have hfs : f (σ s) = s := by simpa using congrArg (fun m => m s) hσ
    have hsV : s ∈ V := by
      rw [← hfs, hs]
      exact x.property
    refine ⟨⟨s, hsV⟩, (f ⁻¹ᵁ V).ι.isEmbedding.injective ?_⟩
    rw [restrictedSection_apply]
    exact hs

/-- Pointwise distinct ORIGINAL section values remain pointwise distinct on the literal restricted source. -/
theorem restrictedSections_pointwise_injective {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    {ι : Type u} (σ : ι → (S ⟶ X)) (hσ : ∀ i, σ i ≫ f = 𝟙 S)
    (hdist : ∀ s : V, Function.Injective (fun i => σ i s.val)) :
    ∀ s : V, Function.Injective (fun i => restrictedSection f V (σ i) (hσ i) s) := by
  intro s i j hij
  apply hdist s
  have H := congrArg (f ⁻¹ᵁ V).ι hij
  simpa only [restrictedSection_apply] using H

/-- Every unequal pair of actual restricted section images is disjoint. -/
theorem restrictedSections_disjoint_ranges {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    {ι : Type u} (σ : ι → (S ⟶ X)) (hσ : ∀ i, σ i ≫ f = 𝟙 S)
    (hdist : ∀ s : V, Function.Injective (fun i => σ i s.val))
    (i j : ι) (hij : i ≠ j) :
    Disjoint (Set.range (restrictedSection f V (σ i) (hσ i)))
      (Set.range (restrictedSection f V (σ j) (hσ j))) := by
  rw [Set.disjoint_left]
  rintro x ⟨s, hs⟩ ⟨t, ht⟩
  have hsi : (f ∣_ V) (restrictedSection f V (σ i) (hσ i) s) = s := by
    have H := congrArg (fun m => m s) (restrictedSection_snd f V (σ i) (hσ i))
    change (f ∣_ V) (restrictedSection f V (σ i) (hσ i) s) = s at H
    exact H
  have htj : (f ∣_ V) (restrictedSection f V (σ j) (hσ j) t) = t := by
    have H := congrArg (fun m => m t) (restrictedSection_snd f V (σ j) (hσ j))
    change (f ∣_ V) (restrictedSection f V (σ j) (hσ j) t) = t at H
    exact H
  have hst : s = t := hsi.symm.trans ((congrArg (f ∣_ V) (hs.trans ht.symm)).trans htj)
  subst t
  exact hij (restrictedSections_pointwise_injective f V σ hσ hdist s (hs.trans ht.symm))

/-- Full original ideal support coverage restricts EXACTLY to the literal native source open. -/
theorem restrictedSections_cover_support {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (D : X.IdealSheafData) {ι : Type u} (σ : ι → (S ⟶ X))
    (hσ : ∀ i, σ i ≫ f = 𝟙 S)
    (hcover : ⋃ i, Set.range (σ i) = (D.support : Set X)) :
    ⋃ i, Set.range (restrictedSection f V (σ i) (hσ i)) =
      ((D.comap (f ⁻¹ᵁ V).ι).support : Set (f ⁻¹ᵁ V).toScheme) := by
  simp only [restrictedSection_range, ← Set.preimage_iUnion, hcover,
    Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]

end Hironaka.Geometry.CurveFibrationMarkedOpen
