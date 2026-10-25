import DeJongAlterations.StableModification.Limits.SpreadProperty

/-!
# Descent of "isomorphism over an open"

Let `D : I ⥤ Scheme` be a cofiltered system of affine schemes with affine transition maps,
indexed by a thin category, with limit cone `c` (lane LIM1, `Limits.Descent`), and let
`h : Y₁ ⟶ Y₂` be a morphism over `D k` between the schemes of two models of finite presentation
of `X₁, X₂ ⟶ lim D`, whose base change to `lim D` is `a : X₁ ⟶ X₂`. If `a` is an isomorphism over
the preimage of a quasi-compact open `O ⊆ Y₂`, then the base change `h_l` of `h` to some level
`l` is an isomorphism over the preimage of `O` (`exists_isIso_morphismRestrict_topBaseChange`),
and this persists at all lower levels (`isIso_morphismRestrict_of_isPullback'`).

This is the part "isomorphism over a dense open" of the descent of modifications, EGA IV 8.10.5
(iv) applied to the restriction of `h` over `O`, as used by Temkin, *Stable modification of
relative curves* (`semi-stable.tex`), Remark 3.1.1 (ii) (T:2297–2298) and the proofs of
Theorems 1.2 and 1.5 (T:3347–3352, T:3384–3394), to spread a stable modification from the local
scheme of a valuation to a quasi-alteration of the base.

## Main results

* `isIso_morphismRestrict_of_isPullback`: if `φ` is the base change of `T` along an open
  immersion `e` and `φ` is an isomorphism, then `T` is an isomorphism over the image of `e`.
* `isIso_morphismRestrict_of_isPullback'`: "isomorphism over an open" is stable under base
  change, the open being replaced by its preimage.
* `exists_isIso_morphismRestrict_topBaseChange`: the descent statement.

Blueprint: `sm-spread-modification.tex`, `lem:sm-spread-mod-iso-restrict` and
`prop:sm-spread-mod-iso`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.StableModification.Limits.SpreadModification

universe u

set_option backward.isDefEq.respectTransparency false

/-! ### Isomorphisms over opens and pullback squares -/

section Restrict

variable {P A Q B : Scheme.{u}}

/-- **Isomorphism over the image of an open immersion.** If in a pullback square the base change
`φ` of `T : A ⟶ B` along an open immersion `e₂ : Q ⟶ B` is an isomorphism, then `T` is an
isomorphism over the open image of `e₂`. -/
theorem isIso_morphismRestrict_of_isPullback {e₁ : P ⟶ A} {φ : P ⟶ Q} {T : A ⟶ B}
    {e₂ : Q ⟶ B} [IsOpenImmersion e₂] (H : IsPullback e₁ φ T e₂) [IsIso φ] :
    IsIso (T ∣_ e₂.opensRange) := by
  set W := e₂.opensRange
  let σ : W.toScheme ⟶ Q := e₂.isoOpensRange.inv
  have hσ : σ ≫ e₂ = W.ι := Scheme.Hom.isoOpensRange_inv_comp e₂
  have hw : (T ⁻¹ᵁ W).ι ≫ T = ((T ∣_ W) ≫ σ) ≫ e₂ := by
    rw [Category.assoc, hσ, morphismRestrict_ι]
  let x : (T ⁻¹ᵁ W).toScheme ⟶ P := H.lift (T ⁻¹ᵁ W).ι ((T ∣_ W) ≫ σ) hw
  have hx₁ : x ≫ e₁ = (T ⁻¹ᵁ W).ι := H.lift_fst _ _ _
  have hx₂ : x ≫ φ = (T ∣_ W) ≫ σ := H.lift_snd _ _ _
  have outer : IsPullback (T ∣_ W) (x ≫ e₁) (σ ≫ e₂) T := by
    rw [hx₁, hσ]
    exact isPullback_morphismRestrict T W
  have top : IsPullback (T ∣_ W) x σ φ := IsPullback.of_bot outer hx₂.symm H.flip
  exact top.isIso_fst_of_isIso

/-- **Isomorphisms over opens are stable under base change.** In a pullback square
`A' = A ×_B B'`, if `T : A ⟶ B` is an isomorphism over an open `W ⊆ B`, then its base change
`T' : A' ⟶ B'` is an isomorphism over the preimage of `W`. -/
theorem isIso_morphismRestrict_of_isPullback' {A' B' : Scheme.{u}} {t₁ : A' ⟶ A}
    {T' : A' ⟶ B'} {T : A ⟶ B} {t₂ : B' ⟶ B} (H : IsPullback t₁ T' T t₂) (W : B.Opens)
    [IsIso (T ∣_ W)] : IsIso (T' ∣_ (t₂ ⁻¹ᵁ W)) := by
  set V := t₂ ⁻¹ᵁ W
  have hw : (T' ∣_ V ≫ t₂ ∣_ W) ≫ W.ι = ((T' ⁻¹ᵁ V).ι ≫ t₁) ≫ T := by
    rw [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, Category.assoc, H.w]
  let y : (T' ⁻¹ᵁ V).toScheme ⟶ (T ⁻¹ᵁ W).toScheme :=
    (isPullback_morphismRestrict T W).lift (T' ∣_ V ≫ t₂ ∣_ W) ((T' ⁻¹ᵁ V).ι ≫ t₁) hw
  have hy₁ : y ≫ T ∣_ W = T' ∣_ V ≫ t₂ ∣_ W := IsPullback.lift_fst _ _ _ _
  have hy₂ : y ≫ (T ⁻¹ᵁ W).ι = (T' ⁻¹ᵁ V).ι ≫ t₁ := IsPullback.lift_snd _ _ _ _
  have s : IsPullback (y ≫ (T ⁻¹ᵁ W).ι) (T' ∣_ V) T (t₂ ∣_ W ≫ W.ι) := by
    rw [hy₂, morphismRestrict_ι]
    exact (isPullback_morphismRestrict T' V).flip.paste_horiz H
  have L : IsPullback y (T' ∣_ V) (T ∣_ W) (t₂ ∣_ W) :=
    IsPullback.of_right s hy₁ (isPullback_morphismRestrict T W).flip
  exact L.isIso_snd_of_isIso

end Restrict

/-! ### Descent -/

section Descent

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  {k : I} {X₁ X₂ : Scheme.{u}} {f₁ : X₁ ⟶ c.pt} {f₂ : X₂ ⟶ c.pt}

/-- The open immersion `O ×_{D k} D l ⟶ Y ×_{D k} D l` induced by an open `O ⊆ Y` of the scheme
of a model at level `k`. -/
abbrev restrictBaseChangeι (r : Model D c f₂ k) (O : r.Y.Opens) (l : Over k) :
    (baseChangeDiagram D (r.restrict O).fY).obj l ⟶ (baseChangeDiagram D r.fY).obj l :=
  pullback.map (r.restrict O).fY (D.map l.hom) r.fY (D.map l.hom) O.ι (𝟙 _) (𝟙 _)
    (Category.comp_id _) (by simp)

lemma isPullback_restrictBaseChangeι (r : Model D c f₂ k) (O : r.Y.Opens) (l : Over k) :
    IsPullback (pullback.fst (r.restrict O).fY (D.map l.hom)) (restrictBaseChangeι r O l) O.ι
      (pullback.fst r.fY (D.map l.hom)) :=
  (isPullback_baseChange_restrict r O l).flip

instance (r : Model D c f₂ k) (O : r.Y.Opens) (l : Over k) :
    IsOpenImmersion (restrictBaseChangeι r O l) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_restrictBaseChangeι r O l)
    inferInstance

/-- The image of `O ×_{D k} D l` in `Y ×_{D k} D l` is the preimage of `O`. -/
lemma opensRange_restrictBaseChangeι (r : Model D c f₂ k) (O : r.Y.Opens) (l : Over k) :
    (restrictBaseChangeι r O l).opensRange = pullback.fst r.fY (D.map l.hom) ⁻¹ᵁ O := by
  have H : Set.range (restrictBaseChangeι r O l) =
      pullback.fst r.fY (D.map l.hom) ⁻¹' Set.range O.ι :=
    range_eq_preimage_of_isPullback (isPullback_baseChange_restrict r O l)
  rw [Scheme.Opens.range_ι] at H
  exact TopologicalSpace.Opens.ext H

variable (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k) (h : r₁.Y ⟶ r₂.Y) (hh : h ≫ r₂.fY = r₁.fY)

include hh in
lemma restrict_comp_fY (O : r₂.Y.Opens) :
    (h ∣_ O) ≫ (r₂.restrict O).fY = (r₁.restrict (h ⁻¹ᵁ O)).fY := by
  simp [Model.restrict, ← hh]

/-- The base change of the restriction `h⁻¹(O) ⟶ O` of `h` is the base change of `h_l` along
`O_l ⟶ Y₂_l`. -/
lemma isPullback_topBaseChange_restrict (O : r₂.Y.Opens) (l : Over k) :
    IsPullback (restrictBaseChangeι r₁ (h ⁻¹ᵁ O) l)
      (topBaseChange (r₁.restrict (h ⁻¹ᵁ O)) (r₂.restrict O) (h ∣_ O)
        (restrict_comp_fY r₁ r₂ h hh O) l)
      (topBaseChange r₁ r₂ h hh l) (restrictBaseChangeι r₂ O l) := by
  have hO := restrict_comp_fY r₁ r₂ h hh O
  have hsq : restrictBaseChangeι r₁ (h ⁻¹ᵁ O) l ≫ topBaseChange r₁ r₂ h hh l =
      topBaseChange (r₁.restrict (h ⁻¹ᵁ O)) (r₂.restrict O) (h ∣_ O) hO l ≫
        restrictBaseChangeι r₂ O l := by
    apply pullback.hom_ext
    · simp [restrictBaseChangeι, morphismRestrict_ι]
    · simp [restrictBaseChangeι]
  refine IsPullback.of_right ?_ hsq (isPullback_topBaseChange r₁ r₂ h hh l)
  have h1 := isPullback_topBaseChange (r₁.restrict (h ⁻¹ᵁ O)) (r₂.restrict O) (h ∣_ O) hO l
  have h2 := (isPullback_morphismRestrict h O).flip
  have e1 : restrictBaseChangeι r₁ (h ⁻¹ᵁ O) l ≫ pullback.fst r₁.fY (D.map l.hom) =
      pullback.fst _ _ ≫ (h ⁻¹ᵁ O).ι := by simp [restrictBaseChangeι]
  have e2 : restrictBaseChangeι r₂ O l ≫ pullback.fst r₂.fY (D.map l.hom) =
      pullback.fst _ _ ≫ O.ι := by simp [restrictBaseChangeι]
  rw [e1, e2]
  exact h1.paste_horiz h2

variable [IsCofiltered I] [Quiver.IsThin I] (hc : IsLimit c)
  [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)] [∀ j, IsAffine (D.obj j)]

include hc in
/-- **Descent of "isomorphism over an open"** (EGA IV 8.10.5 (iv) for the restriction over `O`).
Let `h : Y₁ ⟶ Y₂` be a morphism over `D k` between the schemes of two models of finite
presentation, whose base change to `lim D` is `a : X₁ ⟶ X₂`, and let `O ⊆ Y₂` be a
quasi-compact open such that `a` is an isomorphism over the preimage of `O` in `X₂`. Then for
some level `l` the base change `h_l` is an isomorphism over the preimage of `O`. -/
theorem exists_isIso_morphismRestrict_topBaseChange (hr₁ : r₁.IsFP) (hr₂ : r₂.IsFP)
    (a : X₁ ⟶ X₂) (ha : r₁.g ≫ h = a ≫ r₂.g) (ha' : a ≫ f₂ = f₁)
    (O : r₂.Y.Opens) (hO : IsCompact (O : Set r₂.Y)) (hiso : IsIso (a ∣_ (r₂.g ⁻¹ᵁ O))) :
    ∃ l : Over k,
      IsIso (topBaseChange r₁ r₂ h hh l ∣_ (pullback.fst r₂.fY (D.map l.hom) ⁻¹ᵁ O)) := by
  obtain ⟨_, _, _⟩ := hr₁
  obtain ⟨_, _, _⟩ := hr₂
  have : QuasiCompact (h ≫ r₂.fY) := by rw [hh]; infer_instance
  have : QuasiCompact h := QuasiCompact.of_comp h r₂.fY
  have hO₁ : IsCompact ((h ⁻¹ᵁ O : r₁.Y.Opens) : Set r₁.Y) :=
    QuasiCompact.isCompact_preimage (f := h) _ O.2 hO
  -- the restricted models
  let s₁ := r₁.restrict (h ⁻¹ᵁ O)
  let s₂ := r₂.restrict O
  have hs₁ : s₁.IsFP := Spread.isFP_restrict ⟨‹_›, ‹_›, ‹_›⟩ _ hO₁
  have hs₂ : s₂.IsFP := Spread.isFP_restrict ⟨‹_›, ‹_›, ‹_›⟩ _ hO
  obtain ⟨_, _, _⟩ := hs₁
  obtain ⟨_, _, _⟩ := hs₂
  have hO' : (h ∣_ O) ≫ s₂.fY = s₁.fY := restrict_comp_fY r₁ r₂ h hh O
  -- the restriction of `a`
  have E : r₁.g ⁻¹ᵁ (h ⁻¹ᵁ O) = a ⁻¹ᵁ (r₂.g ⁻¹ᵁ O) := by
    rw [← Scheme.Hom.comp_preimage, ha, Scheme.Hom.comp_preimage]
  let a' : (r₁.g ⁻¹ᵁ (h ⁻¹ᵁ O)).toScheme ⟶ (r₂.g ⁻¹ᵁ O).toScheme :=
    (X₁.isoOfEq E).hom ≫ (a ∣_ (r₂.g ⁻¹ᵁ O))
  have : IsIso a' := by dsimp only [a']; infer_instance
  have ha'₁ : s₁.g ≫ (h ∣_ O) = a' ≫ s₂.g := by
    rw [← cancel_mono O.ι]
    simp only [s₁, s₂, a', Model.restrict, Category.assoc, morphismRestrict_ι,
      morphismRestrict_ι_assoc]
    rw [ha, Scheme.isoOfEq_hom_ι_assoc]
  have ha'₂ : a' ≫ (r₂.g ⁻¹ᵁ O).ι ≫ f₂ = (r₁.g ⁻¹ᵁ (h ⁻¹ᵁ O)).ι ≫ f₁ := by
    simp only [a', Category.assoc, morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc, ha']
  -- descend the isomorphism of restrictions
  let l₀ : Over k := Over.mk (𝟙 k)
  obtain ⟨l, g, hg⟩ := exists_isIso_baseChangeHom hc s₁ s₂
    (topBaseChange s₁ s₂ (h ∣_ O) hO' l₀) (topBaseChange_snd _ _ _ _ _) a' ha'₂
    (π_topBaseChange s₁ s₂ (h ∣_ O) hO' a' ha'₁ ha'₂ l₀)
  have key : baseChangeHom s₁ s₂ (topBaseChange s₁ s₂ (h ∣_ O) hO' l₀)
      (topBaseChange_snd _ _ _ _ _) g = topBaseChange s₁ s₂ (h ∣_ O) hO' l := by
    apply pullback.hom_ext
    · simp
    · simp
  rw [key] at hg
  refine ⟨l, ?_⟩
  rw [← opensRange_restrictBaseChangeι]
  exact isIso_morphismRestrict_of_isPullback (isPullback_topBaseChange_restrict r₁ r₂ h hh O l)

end Descent

end DeJongAlterations.StableModification.Limits.SpreadModification
