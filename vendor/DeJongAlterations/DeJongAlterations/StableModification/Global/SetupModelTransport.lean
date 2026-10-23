import DeJongAlterations.StableModification.Global.GlueModel

/-!
# Transport of stable models

Bookkeeping for the global assembly (`PLAN-T5.md` §2.1 steps 3–5): stable models
(`Global.IsStableModel`) transport along isomorphisms of the target over the base
(`IsStableModel.comp_iso`), base change along `h : T' ⟶ T` in the form `C ×_S T'` for
`T' ⟶ T ⟶ S` (`IsStableModel.pullback'`), and a stable model over an open `U ⊆ T` in pull-back
form is a stable model over `U` in the sense of `Global.IsStableModelOn` (`IsStableModel.toOn`),
the form consumed by the gluing theorem `Global.exists_glue_isStableModelOn`.

Blueprint: `sm-global.tex`, `lem:sm-global-stable-model-transport`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsRelativelyProjective)
open Curves (pullbackCompMap)

section Transport

variable {T P₁ P₂ X : Scheme.{u}} {g₁ : P₁ ⟶ T} {g₂ : P₂ ⟶ T}

/-- **Numerical stability transports along isomorphisms of the target over the base.** -/
theorem IsNumericallyStable.comp_iso {β : X ⟶ P₁} {D' : X.IdealSheafData}
    (h : IsNumericallyStable β g₁ D') (e : P₁ ⟶ P₂) [IsIso e] (he : e ≫ g₂ = g₁) :
    IsNumericallyStable (β ≫ e) g₂ D' := by
  intro K _ _ a
  have hc : (β ≫ e) ≫ g₂ = β ≫ g₁ := by rw [Category.assoc, he]
  let φ : Limits.pullback ((β ≫ e) ≫ g₂) a ≅ Limits.pullback (β ≫ g₁) a := pullback.congrHom hc rfl
  let χ : Limits.pullback g₂ a ⟶ Limits.pullback g₁ a :=
    pullback.map g₂ a g₁ a (inv e) (𝟙 _) (𝟙 _) (by rw [Category.comp_id, IsIso.eq_inv_comp, he])
      (by simp)
  refine NumericallyStableFibre.of_iso φ χ ?_ ?_ ?_ (h K a)
  · simp only [φ, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  · apply pullback.hom_ext
    · simp only [φ, χ, pullback.congrHom_hom, Category.assoc, Curves.pullbackCompMap_fst,
        pullback.lift_fst_assoc, Category.comp_id, pullback.lift_fst]
      simp only [← Category.assoc, Curves.pullbackCompMap_fst]
      simp
    · simp only [φ, χ, pullback.congrHom_hom, Category.assoc, Curves.pullbackCompMap_snd,
        pullback.lift_snd, Category.comp_id]
  · intro y
    simp only [φ, pullback.congrHom_hom]
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Category.comp_id]

variable [IsIntegral T] {k : Type u} [CommRing k] {pT : T ⟶ Spec (.of k)}
  {D₁ : P₁.IdealSheafData} {D₂ : P₂.IdealSheafData} {β : X ⟶ P₁} {D' : X.IdealSheafData}

/-- **Stable models transport along isomorphisms of the target over the base.** -/
theorem IsStableModel.comp_iso (h : IsStableModel pT g₁ D₁ β D') (e : P₁ ⟶ P₂) [IsIso e]
    (he : e ≫ g₂ = g₁) (hD : D₂.comap e = D₁) : IsStableModel pT g₂ D₂ (β ≫ e) D' where
  flat := by
    have := h.flat
    have he' : g₂ = inv e ≫ g₁ := by rw [IsIso.eq_inv_comp, he]
    rw [he']
    infer_instance
  isSemistablePair := by
    rw [Category.assoc, he]
    exact h.isSemistablePair
  genericMarks := h.genericMarks.comp_iso e g₂ he D₂ hD
  isNumericallyStable := h.isNumericallyStable.comp_iso e he
  isRelativelyProjective := by
    obtain ⟨n, i, hi, hiβ⟩ := h.isRelativelyProjective
    have := hi
    let m : Limits.pullback (g₁ ≫ pT) (projectiveSpaceStructure k n) ⟶
        Limits.pullback (g₂ ≫ pT) (projectiveSpaceStructure k n) :=
      pullback.map _ _ _ _ e (𝟙 _) (𝟙 _) (by rw [← Category.assoc, he, Category.comp_id])
        (by simp)
    have : IsIso m := by
      simp only [m]
      infer_instance
    refine ⟨n, i ≫ m, inferInstance, ?_⟩
    simp only [m, Category.assoc, pullback.lift_fst, ← hiβ]
  isoLocus := by
    obtain ⟨U, hU, hqc, hiso⟩ := h.isoLocus
    refine ⟨U, hU, hqc, ?_⟩
    have hpre : e ⁻¹ᵁ (g₂ ⁻¹ᵁ U) = g₁ ⁻¹ᵁ U := by rw [← Scheme.Hom.comp_preimage, he]
    rw [morphismRestrict_comp]
    have h1 : IsIso (β ∣_ (e ⁻¹ᵁ (g₂ ⁻¹ᵁ U))) := by rw [hpre]; exact hiso
    have h2 : IsIso (e ∣_ (g₂ ⁻¹ᵁ U)) :=
      isIso_morphismRestrict_of_isOpenImmersion e _ (fun x _ ↦ e.homeomorph.surjective x)
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

/-- **Relative projectivity transports along isomorphisms of the target** over `Spec k`. -/
theorem IsRelativelyProjective.comp_iso {k : Type u} [CommRing k] {Y₁ Y₂ Z : Scheme.{u}}
    {p₁ : Y₁ ⟶ Spec (.of k)} {p₂ : Y₂ ⟶ Spec (.of k)} {f : Z ⟶ Y₁}
    (h : IsRelativelyProjective p₁ f) (e : Y₁ ⟶ Y₂) [IsIso e] (he : e ≫ p₂ = p₁) :
    IsRelativelyProjective p₂ (f ≫ e) := by
  obtain ⟨n, i, hi, rfl⟩ := h
  have := hi
  let m : Limits.pullback p₁ (projectiveSpaceStructure k n) ⟶
      Limits.pullback p₂ (projectiveSpaceStructure k n) :=
    pullback.map _ _ _ _ e (𝟙 _) (𝟙 _) (by rw [he, Category.comp_id]) (by simp)
  have : IsIso m := by
    simp only [m]
    infer_instance
  refine ⟨n, i ≫ m, inferInstance, ?_⟩
  simp only [m, Category.assoc, pullback.lift_fst]

end Transport

section OpenBase

variable {T U P X : Scheme.{u}} {g : P ⟶ T}

/-- The pull-back square of `f, a` is also a pull-back square of `f ≫ ι, a ≫ ι` for an open
immersion (a monomorphism) `ι`. -/
theorem isPullback_comp_isOpenImmersion (ι : U ⟶ T) [IsOpenImmersion ι] {A B : Scheme.{u}}
    (f : A ⟶ U) (a : B ⟶ U) :
    IsPullback (pullback.fst f a) (pullback.snd f a) (f ≫ ι) (a ≫ ι) :=
  IsPullback.of_isLimit (pullbackIsPullbackOfCompMono f a ι)

/-- A semi-stable pair stays semi-stable over a larger base containing the base as an open
subscheme. -/
theorem isSemistablePair_comp_isOpenImmersion {A : Scheme.{u}} {f : A ⟶ U}
    {D' : A.IdealSheafData} (h : IsSemistablePair f D') (ι : U ⟶ T) [IsOpenImmersion ι] :
    IsSemistablePair (f ≫ ι) D' where
  nodal := by
    have := h.nodal
    exact Curves.IsNodalCurve.comp_isOpenImmersion f ι
  etale := by
    have := h.etale
    rw [← Category.assoc]
    infer_instance
  smoothAlong x hx := Curves.isSmoothAt_comp (h.smoothAlong x hx) (Curves.isSmoothAt_of_smooth ι _)

/-- **Numerical stability over an open of the base**: for an open immersion `ι : U ⟶ T`, a
numerically stable `(β, D')` over `P ×_T U` is numerically stable over `P` (geometric points of
`T` outside `U` have empty fibres). -/
theorem IsNumericallyStable.comp_fst_of_isOpenImmersion (ι : U ⟶ T) [IsOpenImmersion ι]
    {β : X ⟶ Limits.pullback g ι} {D' : X.IdealSheafData}
    (h : IsNumericallyStable β (pullback.snd g ι) D') :
    IsNumericallyStable (β ≫ pullback.fst g ι) g D' := by
  intro K _ _ a
  by_cases ha : Set.range a ⊆ Set.range ι
  · obtain ⟨a', rfl⟩ : ∃ a', a' ≫ ι = a :=
      ⟨IsOpenImmersion.lift ι a ha, IsOpenImmersion.lift_fac ι a ha⟩
    have hc : (β ≫ pullback.fst g ι) ≫ g = (β ≫ pullback.snd g ι) ≫ ι := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    let H := isPullback_comp_isOpenImmersion ι (β ≫ pullback.snd g ι) a'
    let φ : Limits.pullback ((β ≫ pullback.fst g ι) ≫ g) (a' ≫ ι) ≅
        Limits.pullback (β ≫ pullback.snd g ι) a' :=
      pullback.congrHom hc rfl ≪≫ H.isoPullback.symm
    let χ : Limits.pullback g (a' ≫ ι) ⟶ Limits.pullback (pullback.snd g ι) a' :=
      (pullbackLeftPullbackSndIso g ι a').inv
    have hfst : φ.hom ≫ pullback.fst (β ≫ pullback.snd g ι) a' =
        pullback.fst ((β ≫ pullback.fst g ι) ≫ g) (a' ≫ ι) := by
      simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_fst,
        pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
    have hsnd : φ.hom ≫ pullback.snd (β ≫ pullback.snd g ι) a' =
        pullback.snd ((β ≫ pullback.fst g ι) ≫ g) (a' ≫ ι) := by
      simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_snd,
        pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
    refine NumericallyStableFibre.of_iso φ χ hsnd ?_ ?_ (h K a')
    · rw [← cancel_mono (pullbackLeftPullbackSndIso g ι a').hom]
      simp only [χ, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply pullback.hom_ext
      · simp only [Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
          Curves.pullbackCompMap_fst, Curves.pullbackCompMap_fst_assoc]
        rw [reassoc_of% hfst]
      · simp only [Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
          Curves.pullbackCompMap_snd]
        exact hsnd
    · intro y
      rw [← Scheme.Hom.comp_apply, hfst]
  · intro Z hZ
    exfalso
    obtain ⟨y, -⟩ := hZ.1.1
    refine ha ?_
    rintro _ ⟨b, rfl⟩
    have hb : b = pullback.snd ((β ≫ pullback.fst g ι) ≫ g) a y := Subsingleton.elim _ _
    have hc' : ∀ x, ((β ≫ pullback.fst g ι) ≫ g) x = ι ((β ≫ pullback.snd g ι) x) := fun x ↦ by
      rw [Category.assoc, pullback.condition, ← Category.assoc, Scheme.Hom.comp_apply]
    rw [hb, ← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hc']
    exact ⟨_, rfl⟩

variable [IsIntegral T] {k : Type u} [CommRing k] {pT : T ⟶ Spec (.of k)} {D : P.IdealSheafData}

/-- **A stable model over an open of the base, in pull-back form, is a stable model over the
open** (`IsStableModelOn`): for `U ⊆ T` open with quasi-compact inclusion and a stable model
`β : X ⟶ P ×_T U` of `(P ×_T U, D ×_T U)` over `U`, the composite `X ⟶ P ×_T U ⟶ P` is a stable
model over `U` in the sense of `IsStableModelOn`. -/
theorem IsStableModel.toOn (U : T.Opens) [Nonempty U] [QuasiCompact U.ι]
    {β : X ⟶ Limits.pullback g U.ι} {D' : X.IdealSheafData}
    (hm : IsStableModel (U.ι ≫ pT) (pullback.snd g U.ι) (D.comap (pullback.fst g U.ι)) β D') :
    IsStableModelOn pT g D U (β ≫ pullback.fst g U.ι) D' := by
  have hc : (β ≫ pullback.fst g U.ι) ≫ g = (β ≫ pullback.snd g U.ι) ≫ U.ι := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hηU : U.ι (genericPoint U) = genericPoint T := genericPoint_eq_of_isOpenImmersion U.ι
  -- the restriction of `β ≫ fst` over `g⁻¹ U`
  let e := pullbackRestrictIsoRestrict g U
  have hpre : (β ≫ pullback.fst g U.ι) ⁻¹ᵁ (g ⁻¹ᵁ U) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hc, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self,
      Scheme.Hom.preimage_top]
  have hι : IsIso ((β ≫ pullback.fst g U.ι) ⁻¹ᵁ (g ⁻¹ᵁ U)).ι := by
    rw [hpre]
    exact inferInstanceAs (IsIso X.topIso.hom)
  have hres : (β ≫ pullback.fst g U.ι) ∣_ (g ⁻¹ᵁ U) =
      ((β ≫ pullback.fst g U.ι) ⁻¹ᵁ (g ⁻¹ᵁ U)).ι ≫ β ≫ e.hom := by
    rw [← cancel_mono (g ⁻¹ᵁ U).ι, morphismRestrict_ι, Category.assoc, Category.assoc,
      pullbackRestrictIsoRestrict_hom_ι]
  refine
    { preimage_eq_top := by
        rw [hc, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
      isSemistablePair := by
        rw [hc]
        exact isSemistablePair_comp_isOpenImmersion hm.isSemistablePair U.ι
      genericMarks := ?_
      isNumericallyStable := hm.isNumericallyStable.comp_fst_of_isOpenImmersion U.ι
      isRelativelyProjective := ?_
      isoLocus := ?_ }
  · intro Y m n hmn
    let n' : Y ⟶ Spec (U.toScheme.residueField (genericPoint U)) :=
      n ≫ Spec.map (T.residueFieldCongr hηU).hom ≫
        inv (Spec.map (U.ι.residueFieldMap (genericPoint U)))
    have hn' : m ≫ β ≫ pullback.snd g U.ι =
        n' ≫ U.toScheme.fromSpecResidueField (genericPoint U) := by
      rw [← cancel_mono U.ι]
      have h1 : inv (Spec.map (U.ι.residueFieldMap (genericPoint U))) ≫
          U.toScheme.fromSpecResidueField (genericPoint U) ≫ U.ι =
            T.fromSpecResidueField (U.ι (genericPoint U)) := by
        rw [IsIso.inv_comp_eq, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
      simp only [n', Category.assoc]
      rw [h1, Scheme.residueFieldCongr_fromSpecResidueField, ← hmn, ← pullback.condition]
      simp only [Category.assoc]
    rw [hm.genericMarks Y m n' hn']
    simp only [← Scheme.IdealSheafData.comap_comp]
  · have hp := IsRelativelyProjective.comp_iso hm.isRelativelyProjective e.hom
      (p₂ := (g ⁻¹ᵁ U).ι ≫ g ≫ pT) (by
        rw [← Category.assoc, ← Category.assoc, pullbackRestrictIsoRestrict_hom_ι,
          pullback.condition, Category.assoc])
    rw [hres]
    exact IsRelativelyProjective.iso_comp hp _
  · obtain ⟨U', hU', hqc, hiso⟩ := hm.isoLocus
    refine ⟨U.ι ''ᵁ U', ?_, ?_, ?_, ?_⟩
    · exact (U.ι.image_le_opensRange U').trans (by rw [Scheme.Opens.opensRange_ι])
    · obtain ⟨x, hx⟩ := hU'
      exact ⟨U.ι x, x, hx, rfl⟩
    · have hr : Set.range (U.ι ''ᵁ U').ι = Set.range (U'.ι ≫ U.ι) := by
        rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
          Scheme.Opens.range_ι]
        rfl
      have := hqc
      rw [← IsOpenImmersion.isoOfRangeEq_hom_fac (U.ι ''ᵁ U').ι (U'.ι ≫ U.ι) hr]
      infer_instance
    · rw [morphismRestrict_comp]
      have h2 : IsIso (pullback.fst g U.ι ∣_ (g ⁻¹ᵁ (U.ι ''ᵁ U'))) := by
        refine isIso_morphismRestrict_of_isOpenImmersion _ _ fun x hx ↦ ?_
        rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.opensRange_ι]
        exact (U.ι.image_le_opensRange U').trans (le_of_eq (Scheme.Opens.opensRange_ι U))
          (show g x ∈ U.ι ''ᵁ U' from hx)
      have hopen : pullback.fst g U.ι ⁻¹ᵁ (g ⁻¹ᵁ (U.ι ''ᵁ U')) = pullback.snd g U.ι ⁻¹ᵁ U' := by
        rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
          Scheme.Hom.preimage_image_eq]
      have h1 : IsIso (β ∣_ (pullback.fst g U.ι ⁻¹ᵁ (g ⁻¹ᵁ (U.ι ''ᵁ U')))) := by
        rw [hopen]
        exact hiso
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

end OpenBase

end DeJongAlterations.StableModification.Global
