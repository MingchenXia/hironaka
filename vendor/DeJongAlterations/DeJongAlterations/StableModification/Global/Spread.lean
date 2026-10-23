import DeJongAlterations.StableModification.Global.Setup

/-!
# Spreading out the stable modification over a valuation ring

Node G3′ of `PLAN-T5.md` (§2.1 step 2; Temkin, *Stable modification of relative curves*,
`semi-stable.tex`, proof of Theorem 1.5, T:3379–3394): the stable modification over a valuation
ring `W ∈ RZ_{K(S)ᵃ}(S)` (lane T45B's `ValuationStableExistence`) descends to a projective
semi-stable η-modification over the spectrum of a finitely generated subalgebra `B ⊆ W` (lane
LIM3's `Limits.SpreadModification.exists_semistable_projective_etaModification_of_isIso_fiberMap`);
its marks are the transported marks (*G-marks*, `genericMarksCondition_of_forall`: both are
reduced over the generic point, since étale over a field, and have the same points there, by
comparison with `W`); numerical stability at the centre of `W` spreads to an open neighbourhood
(node G4, `StableOpenNbhd`), and an affine neighbourhood of the centre is a local stable piece
(`exists_localStablePiece`).

* `IsSpreadModel`: the properties of `IsStableModel` except numerical stability, with base
  change (`IsSpreadModel.pullback`).
* `numericallyStableFibre_iff_of_isPullback`: numerical stability of geometric fibres along
  pull-back squares.
* `genericMarksCondition_of_forall`: the G-marks identification.

Blueprint: `sm-global.tex`, `lem:sm-global-g-marks`, `thm:sm-global-local-piece`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsRelativelyProjective IsMultipointedCurve)
open Curves (pullbackCompMap IsStableModification)

section Spread

variable {k : Type u} [CommRing k] {T P X : Scheme.{u}}

/-- **A spread model**: the properties of a stable model (`IsStableModel`) except numerical
stability, which holds only near the centre of the valuation ring. -/
structure IsSpreadModel [IsIntegral T] (pT : T ⟶ Spec (.of k)) (g : P ⟶ T)
    (D : P.IdealSheafData) (β : X ⟶ P) (D' : X.IdealSheafData) : Prop where
  flat : Flat g
  isSemistablePair : IsSemistablePair (β ≫ g) D'
  genericMarks : GenericMarksCondition g D β D'
  isRelativelyProjective : IsRelativelyProjective (g ≫ pT) β
  isoLocus : ∃ U : T.Opens, (U : Set T).Nonempty ∧ QuasiCompact U.ι ∧
    IsIso (β ∣_ (g ⁻¹ᵁ U))

variable [IsIntegral T] {pT : T ⟶ Spec (.of k)} {g : P ⟶ T} {D : P.IdealSheafData}
  {β : X ⟶ P} {D' : X.IdealSheafData}

/-- A numerically stable spread model is a stable model. -/
theorem IsSpreadModel.toIsStableModel (h : IsSpreadModel pT g D β D')
    (hnum : IsNumericallyStable β g D') : IsStableModel pT g D β D' where
  flat := h.flat
  isSemistablePair := h.isSemistablePair
  genericMarks := h.genericMarks
  isNumericallyStable := hnum
  isRelativelyProjective := h.isRelativelyProjective
  isoLocus := h.isoLocus

/-- **Base change of spread models** along `h : T' ⟶ T` quasi-compact, from an integral scheme and
sending the generic point to the generic point. -/
theorem IsSpreadModel.pullback {T' : Scheme.{u}} [IsIntegral T'] (hm : IsSpreadModel pT g D β D')
    (h : T' ⟶ T) [QuasiCompact h] (hη : h (genericPoint T') = genericPoint T) :
    IsSpreadModel (h ≫ pT) (pullback.snd g h) (D.comap (pullback.fst g h))
      (pullbackCompMap β g h) (D'.comap (pullback.fst (β ≫ g) h)) where
  flat := by
    have := hm.flat
    infer_instance
  isSemistablePair := by
    rw [Curves.pullbackCompMap_snd]
    exact Curves.IsSemistablePair.pullback hm.isSemistablePair h
  genericMarks := hm.genericMarks.pullback h hη
  isRelativelyProjective := by
    have H := Limits.SpreadModification.isPullback_pullbackCompMap β g h
    have h₁ := hm.isRelativelyProjective.pullback_snd (pullback.fst g h)
    rw [← H.isoPullback_hom_snd]
    have h₂ := IsRelativelyProjective.iso_comp h₁ H.isoPullback.hom
    rwa [pullback.condition_assoc] at h₂
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

/-- **Spread models transport along isomorphisms of the target over the base.** -/
theorem IsSpreadModel.comp_iso {P₂ : Scheme.{u}} {g₂ : P₂ ⟶ T} {D₂ : P₂.IdealSheafData}
    (h : IsSpreadModel pT g D β D') (e : P ⟶ P₂) [IsIso e] (he : e ≫ g₂ = g)
    (hD : D₂.comap e = D) : IsSpreadModel pT g₂ D₂ (β ≫ e) D' where
  flat := by
    have := h.flat
    have he' : g₂ = inv e ≫ g := by rw [IsIso.eq_inv_comp, he]
    rw [he']
    infer_instance
  isSemistablePair := by
    rw [Category.assoc, he]
    exact h.isSemistablePair
  genericMarks := h.genericMarks.comp_iso e g₂ he D₂ hD
  isRelativelyProjective :=
    IsRelativelyProjective.comp_iso h.isRelativelyProjective e (by rw [← Category.assoc, he])
  isoLocus := by
    obtain ⟨U, hU, hqc, hiso⟩ := h.isoLocus
    refine ⟨U, hU, hqc, ?_⟩
    have hpre : e ⁻¹ᵁ (g₂ ⁻¹ᵁ U) = g ⁻¹ᵁ U := by rw [← Scheme.Hom.comp_preimage, he]
    rw [morphismRestrict_comp]
    have h1 : IsIso (β ∣_ (e ⁻¹ᵁ (g₂ ⁻¹ᵁ U))) := by rw [hpre]; exact hiso
    have h2 : IsIso (e ∣_ (g₂ ⁻¹ᵁ U)) :=
      isIso_morphismRestrict_of_isOpenImmersion e _ (fun x _ ↦ e.homeomorph.surjective x)
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

end Spread

section Fibres

/-- **Numerical stability of geometric fibres along pull-back squares**: if `X₁ = X₂ ×_{P₂} P₁`
and `P₁ = P₂ ×_{T₂} T₁`, the geometric fibre of `(β₁, g₁, D₂ ×_{X₂} X₁)` over `a` is that of
`(β₂, g₂, D₂)` over `a ≫ w`. -/
theorem numericallyStableFibre_iff_of_isPullback {X₁ X₂ P₁ P₂ T₁ T₂ : Scheme.{u}}
    {β₁ : X₁ ⟶ P₁} {β₂ : X₂ ⟶ P₂} {g₁ : P₁ ⟶ T₁} {g₂ : P₂ ⟶ T₂} {u : X₁ ⟶ X₂}
    {v : P₁ ⟶ P₂} {w : T₁ ⟶ T₂} (H₁ : IsPullback u β₁ β₂ v) (H₂ : IsPullback v g₁ g₂ w)
    (D₂ : X₂.IdealSheafData) {K : Type u} [Field K] (a : Spec (.of K) ⟶ T₁) :
    NumericallyStableFibre β₁ g₁ (D₂.comap u) a ↔ NumericallyStableFibre β₂ g₂ D₂ (a ≫ w) := by
  have H : IsPullback u (β₁ ≫ g₁) (β₂ ≫ g₂) w := H₁.paste_vert H₂
  have Hx : IsPullback (pullback.fst (β₁ ≫ g₁) a ≫ u) (pullback.snd (β₁ ≫ g₁) a) (β₂ ≫ g₂)
      (a ≫ w) := (IsPullback.of_hasPullback (β₁ ≫ g₁) a).paste_horiz H
  have Hp : IsPullback (pullback.fst g₁ a ≫ v) (pullback.snd g₁ a) g₂ (a ≫ w) :=
    (IsPullback.of_hasPullback g₁ a).paste_horiz H₂
  let φ := Hx.isoPullback
  let χ := Hp.isoPullback
  have hφf : φ.hom ≫ pullback.fst (β₂ ≫ g₂) (a ≫ w) = pullback.fst (β₁ ≫ g₁) a ≫ u :=
    Hx.isoPullback_hom_fst
  have hφs : φ.hom ≫ pullback.snd (β₂ ≫ g₂) (a ≫ w) = pullback.snd (β₁ ≫ g₁) a :=
    Hx.isoPullback_hom_snd
  have hmap : φ.hom ≫ pullbackCompMap β₂ g₂ (a ≫ w) = pullbackCompMap β₁ g₁ a ≫ χ.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, Curves.pullbackCompMap_fst, reassoc_of% hφf, Category.assoc,
        Hp.isoPullback_hom_fst, Curves.pullbackCompMap_fst_assoc, H₁.w]
    · rw [Category.assoc, Curves.pullbackCompMap_snd, hφs, Category.assoc,
        Hp.isoPullback_hom_snd, Curves.pullbackCompMap_snd]
  have hmarks : ∀ y, pullback.fst (β₂ ≫ g₂) (a ≫ w) (φ.hom y) ∈ (D₂.support : Set X₂) ↔
      pullback.fst (β₁ ≫ g₁) a y ∈ ((D₂.comap u).support : Set X₁) := by
    intro y
    rw [← Scheme.Hom.comp_apply, hφf, Scheme.IdealSheafData.support_comap]
    rfl
  constructor
  · intro h
    refine NumericallyStableFibre.of_iso φ.symm χ.inv ?_ ?_ ?_ h
    · rw [Iso.symm_hom, Iso.inv_comp_eq, hφs]
    · rw [Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, hmap, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · intro y
      have hy : φ.hom (φ.inv y) = y := by
        rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
      rw [Iso.symm_hom, ← hmarks (φ.inv y), hy]
  · exact NumericallyStableFibre.of_iso φ χ.hom hφs hmap hmarks

end Fibres

section GMarks

variable {S C T X : Scheme.{u}} [IsIntegral S] [IsIntegral T] {g : C ⟶ S}
  {D : C.IdealSheafData}

/-- The closed subscheme defined by the pull-back of an ideal sheaf along an isomorphism is reduced
if the original one is. -/
theorem isReduced_comap_of_isIso {Y Z : Scheme.{u}} (I : Z.IdealSheafData) (f : Y ⟶ Z) [IsIso f]
    [IsReduced I.subscheme] : IsReduced (I.comap f).subscheme := by
  have : IsReduced (pullback f I.subschemeι) :=
    isReduced_of_isOpenImmersion (pullback.snd f I.subschemeι)
  exact isReduced_of_isOpenImmersion (I.comapIso f).hom

/-- **G-marks** (`PLAN-T5.md` §2.1 step 2, node G3′). Let `t : T ⟶ S` map the generic point to
the generic point, the generic pair of `(C, D)` be semi-stable, and `β : X ⟶ C ×_S T` be an
isomorphism on the generic fibres with `(X, D_X)` a semi-stable pair over `T`. If the points of
`D_X` over the generic point of `T` are those mapped into `D`, then `D_X` satisfies the generic
marks condition with respect to `D ×_S T`: both closed subschemes of the generic fibre are
reduced (étale over the residue field) with the same points. -/
theorem genericMarksCondition_of_forall (t : T ⟶ S)
    (ht : t (genericPoint T) = genericPoint S)
    (hss : IsSemistablePair (g.fiberToSpecResidueField (genericPoint S))
      (DeJong.fiberMarks g D (genericPoint S)))
    (β : X ⟶ pullback (C := Scheme.{u}) g t) (DX : X.IdealSheafData)
    (hX : IsSemistablePair (β ≫ pullback.snd g t) DX)
    [IsIso (Curves.fiberMap β (pullback.snd g t) (genericPoint T))]
    (hpts : ∀ x : X, (β ≫ pullback.snd g t) x = genericPoint T →
      (x ∈ (DX.support : Set X) ↔ (β ≫ pullback.fst g t) x ∈ (D.support : Set C))) :
    GenericMarksCondition (pullback.snd g t) (D.comap (pullback.fst g t)) β DX := by
  apply GenericMarksCondition.of_fiber
  have : Etale (DX.subschemeι ≫ β ≫ pullback.snd g t) := hX.etale
  have h1 : IsReduced (DX.comap ((β ≫ pullback.snd g t).fiberι (genericPoint T))).subscheme :=
    isReduced_comap_fiberι_of_etale _ DX _
  have h2 : IsReduced (((D.comap (pullback.fst g t)).comap β).comap
      ((β ≫ pullback.snd g t).fiberι (genericPoint T))).subscheme := by
    rw [← genericMarks_eq_comap]
    have hgp := isSemistablePair_generic_pullback g D hss t ht
    have : IsReduced (DeJong.fiberMarks (pullback.snd g t) (D.comap (pullback.fst g t))
        (genericPoint T)).subscheme :=
      @isReduced_of_etale_field _ _ _ _ hgp.etale
    exact isReduced_comap_of_isIso _ _
  refine comap_eq_of_forall_of_isReduced _ _ DX _ fun x hx ↦ ?_
  rw [hpts x hx, Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
  rfl

end GMarks

end DeJongAlterations.StableModification.Global
