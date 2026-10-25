import DeJongAlterations.StableModification.Global.CoverGlue

/-!
# Locally projective stable models and their base change

The glued model of `Global.exists_glued_model` is projective (relative to `Spec k`) only over the
members of a finite open cover of its target (obligation E3 of PLAN-OM3 §6). This file bundles
the properties carried to the end of the global assembly (`PLAN-T5.md` §2.1 steps 5–6, node G8)
as `IsLocallyProjectiveStableModel`, and proves that they are stable under base change along
morphisms of integral schemes sending the generic point to the generic point (needed for the
normalization of the base, which gives E1) and under isomorphisms of the target, and that they
give Temkin's stable η-modifications with finite marks.

* `locallyRelativelyProjective_of_isPullback`: lane OM3A's
  `Projectivity.LocallyRelativelyProjective` is stable under base change.
* `IsLocallyProjectiveStableModel.isStableModification`, `.pullback`, `.comp_iso`,
  `.isFinite_marks`.

Blueprint: `sm-global.tex`, `lem:sm-global-locally-projective-model`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsRelativelyProjective)
open Curves (pullbackCompMap IsStableModification IsEtaModification)

section Restrict

variable {A B A' B' : Scheme.{u}}

/-- **Restriction of a pull-back square to an open of the base.** In a pull-back square
`A' = A ×_B B'`, the restriction of `T' : A' ⟶ B'` over the preimage `t⁻¹ W` of an open `W ⊆ B`
is the base change of the restriction of `T` over `W`. -/
theorem exists_isPullback_morphismRestrict {t₁ : A' ⟶ A} {T' : A' ⟶ B'} {T : A ⟶ B}
    {t₂ : B' ⟶ B} (H : IsPullback t₁ T' T t₂) (W : B.Opens) :
    ∃ y : (T' ⁻¹ᵁ (t₂ ⁻¹ᵁ W)).toScheme ⟶ (T ⁻¹ᵁ W).toScheme,
      IsPullback y (T' ∣_ (t₂ ⁻¹ᵁ W)) (T ∣_ W) (t₂ ∣_ W) := by
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
  exact ⟨y, IsPullback.of_right s hy₁ (isPullback_morphismRestrict T W).flip⟩

variable {k : Type u} [CommRing k]

/-- **Local relative projectivity is stable under base change** (lane OM3A's
`Projectivity.LocallyRelativelyProjective`): in a pull-back square `A' = A ×_B B'`, if `T` is
locally relatively projective over `pB`, then `T'` is locally relatively projective over
`B' ⟶ B ⟶ Spec k`, for the preimage cover. -/
theorem locallyRelativelyProjective_of_isPullback {pB : B ⟶ Spec (.of k)} {t₁ : A' ⟶ A}
    {T' : A' ⟶ B'} {T : A ⟶ B} {t₂ : B' ⟶ B} (h : Projectivity.LocallyRelativelyProjective pB T)
    (H : IsPullback t₁ T' T t₂) : Projectivity.LocallyRelativelyProjective (t₂ ≫ pB) T' := by
  obtain ⟨J, hJ, W, hW, hWp⟩ := h
  refine ⟨J, hJ, fun j ↦ t₂ ⁻¹ᵁ W j, ?_, fun j ↦ ?_⟩
  · rw [← Scheme.Hom.preimage_iSup, hW, Scheme.Hom.preimage_top]
  · obtain ⟨y, hy⟩ := exists_isPullback_morphismRestrict H (W j)
    have := Limits.SpreadModification.isRelativelyProjective_of_isPullback (hWp j) hy
    rwa [← Category.assoc, morphismRestrict_ι, Category.assoc] at this

/-- Local relative projectivity transports along isomorphisms of the target over `Spec k`. -/
theorem LocallyRelativelyProjective.comp_iso {Y₁ Y₂ Z : Scheme.{u}} {p₁ : Y₁ ⟶ Spec (.of k)}
    {p₂ : Y₂ ⟶ Spec (.of k)} {f : Z ⟶ Y₁} (h : Projectivity.LocallyRelativelyProjective p₁ f)
    (e : Y₁ ⟶ Y₂) [IsIso e] (he : e ≫ p₂ = p₁) :
    Projectivity.LocallyRelativelyProjective p₂ (f ≫ e) := by
  have H : IsPullback (𝟙 Z) (f ≫ e) f (inv e) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]⟩
  have := locallyRelativelyProjective_of_isPullback h H
  have he' : inv e ≫ p₁ = p₂ := by rw [IsIso.inv_comp_eq, he]
  rwa [he'] at this

end Restrict

section Model

variable {k : Type u} [CommRing k] {T P X : Scheme.{u}}

/-- **A locally projective stable model over an integral base** (the output of the gluing,
`PLAN-T5.md` §2.1 steps 5–6): for `g : P ⟶ T` flat and marks `D ⊆ P`, the proper morphism
`β : X ⟶ P` with marks `D'` makes `(X, D')` a semi-stable pair over `T` satisfying the generic
marks condition, numerically stable, locally relatively projective over `P ⟶ T ⟶ Spec k`, and is
an isomorphism over a nonempty open of `T` with quasi-compact inclusion. -/
structure IsLocallyProjectiveStableModel [IsIntegral T] (pT : T ⟶ Spec (.of k)) (g : P ⟶ T)
    (D : P.IdealSheafData) (β : X ⟶ P) (D' : X.IdealSheafData) : Prop where
  flat : Flat g
  isProper : IsProper β
  isSemistablePair : IsSemistablePair (β ≫ g) D'
  genericMarks : GenericMarksCondition g D β D'
  isNumericallyStable : IsNumericallyStable β g D'
  locallyRelativelyProjective : Projectivity.LocallyRelativelyProjective (g ≫ pT) β
  isoLocus : ∃ U : T.Opens, (U : Set T).Nonempty ∧ QuasiCompact U.ι ∧
    IsIso (β ∣_ (g ⁻¹ᵁ U))

variable [IsIntegral T] {pT : T ⟶ Spec (.of k)} {g : P ⟶ T} {D : P.IdealSheafData}
  {β : X ⟶ P} {D' : X.IdealSheafData}

/-- The morphism of a locally projective stable model is an η-modification. -/
theorem IsLocallyProjectiveStableModel.isEtaModification
    (h : IsLocallyProjectiveStableModel pT g D β D') : IsEtaModification β g := by
  have := h.flat
  have := h.isProper
  have := h.isSemistablePair.nodal
  obtain ⟨U, hU, hUc, hiso⟩ := h.isoLocus
  exact Limits.SpreadModification.isEtaModification_of_isIso_morphismRestrict β g U hU

/-- **Locally projective stable models are stable η-modifications** (with the transported marks;
exceptional components are excluded numerically). -/
theorem IsLocallyProjectiveStableModel.isStableModification
    (h : IsLocallyProjectiveStableModel pT g D β D') : IsStableModification β g D D' where
  toIsEtaModification := h.isEtaModification
  marks_eq := by
    have := h.isSemistablePair.etale
    exact h.genericMarks.eq_genericMarksClosure
  isSemistablePair := h.isSemistablePair
  not_isExceptionalComponent := h.isNumericallyStable.not_isExceptionalComponent

omit [IsIntegral T] in
/-- **The marks of a semi-stable pair which is proper over the base are finite** over it (proper
and étale, hence quasi-finite; Zariski's main theorem,
`IsFinite.of_isProper_of_locallyQuasiFinite`). -/
theorem isFinite_marks_of_isProper {f : X ⟶ T} [IsProper f] {E : X.IdealSheafData}
    (h : IsSemistablePair f E) : IsFinite (E.subschemeι ≫ f) := by
  have := h.etale
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- **Base change of locally projective stable models** along `h : T' ⟶ T` quasi-compact, from
an integral scheme and sending the generic point to the generic point. -/
theorem IsLocallyProjectiveStableModel.pullback {T' : Scheme.{u}} [IsIntegral T']
    (hm : IsLocallyProjectiveStableModel pT g D β D') (h : T' ⟶ T) [QuasiCompact h]
    (hη : h (genericPoint T') = genericPoint T) :
    IsLocallyProjectiveStableModel (h ≫ pT) (pullback.snd g h) (D.comap (pullback.fst g h))
      (pullbackCompMap β g h) (D'.comap (pullback.fst (β ≫ g) h)) where
  flat := by
    have := hm.flat
    infer_instance
  isProper := by
    have := hm.isProper
    exact MorphismProperty.of_isPullback (P := @IsProper)
      (Limits.SpreadModification.isPullback_pullbackCompMap β g h) inferInstance
  isSemistablePair := by
    rw [Curves.pullbackCompMap_snd]
    exact Curves.IsSemistablePair.pullback hm.isSemistablePair h
  genericMarks := hm.genericMarks.pullback h hη
  isNumericallyStable := hm.isNumericallyStable.pullback h
  locallyRelativelyProjective := by
    have := locallyRelativelyProjective_of_isPullback hm.locallyRelativelyProjective
      (Limits.SpreadModification.isPullback_pullbackCompMap β g h)
    rwa [pullback.condition_assoc] at this
  isoLocus := by
    obtain ⟨U, hU, hUc, hiso⟩ := hm.isoLocus
    have hηU : genericPoint T ∈ U :=
      ((genericPoint_spec T).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
    refine ⟨h ⁻¹ᵁ U, ⟨genericPoint T', by simpa [hη] using hηU⟩,
      MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_morphismRestrict h U)
        hUc, ?_⟩
    have H := Limits.SpreadModification.isPullback_pullbackCompMap β g h
    have := Limits.SpreadModification.isIso_morphismRestrict_of_isPullback' H (g ⁻¹ᵁ U)
    have hopen : (pullback.fst g h) ⁻¹ᵁ (g ⁻¹ᵁ U) = (pullback.snd g h) ⁻¹ᵁ (h ⁻¹ᵁ U) := by
      rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
    rwa [hopen] at this

/-- **Locally projective stable models transport along isomorphisms of the target over the
base.** -/
theorem IsLocallyProjectiveStableModel.comp_iso {P₂ : Scheme.{u}} {g₂ : P₂ ⟶ T}
    {D₂ : P₂.IdealSheafData} (h : IsLocallyProjectiveStableModel pT g D β D') (e : P ⟶ P₂)
    [IsIso e] (he : e ≫ g₂ = g) (hD : D₂.comap e = D) :
    IsLocallyProjectiveStableModel pT g₂ D₂ (β ≫ e) D' where
  flat := by
    have := h.flat
    have he' : g₂ = inv e ≫ g := by rw [IsIso.eq_inv_comp, he]
    rw [he']
    infer_instance
  isProper := by
    have := h.isProper
    infer_instance
  isSemistablePair := by
    rw [Category.assoc, he]
    exact h.isSemistablePair
  genericMarks := h.genericMarks.comp_iso e g₂ he D₂ hD
  isNumericallyStable := h.isNumericallyStable.comp_iso e he
  locallyRelativelyProjective :=
    LocallyRelativelyProjective.comp_iso h.locallyRelativelyProjective e
      (by rw [← Category.assoc, he])
  isoLocus := by
    obtain ⟨U, hU, hqc, hiso⟩ := h.isoLocus
    refine ⟨U, hU, hqc, ?_⟩
    have hpre : e ⁻¹ᵁ (g₂ ⁻¹ᵁ U) = g ⁻¹ᵁ U := by rw [← Scheme.Hom.comp_preimage, he]
    rw [morphismRestrict_comp]
    have h1 : IsIso (β ∣_ (e ⁻¹ᵁ (g₂ ⁻¹ᵁ U))) := by rw [hpre]; exact hiso
    have h2 : IsIso (e ∣_ (g₂ ⁻¹ᵁ U)) :=
      isIso_morphismRestrict_of_isOpenImmersion e _ (fun x _ ↦ e.homeomorph.surjective x)
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

end Model

end DeJongAlterations.StableModification.Global
