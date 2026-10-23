import DeJongAlterations.StableModification.Global.SetupMarks
import DeJongAlterations.StableModification.Global.StatementsBaseChange
import DeJongAlterations.StableModification.Limits.SpreadModification
import DeJongAlterations.StableModification.DeJong.BaseStepProjective

/-!
# Stable models over a base and their base change

The global assembly of Temkin's Theorem 1.5 (*Stable modification of relative curves*,
`semi-stable.tex`, §5, T:3379–3399; `PLAN-T5.md` §2.1 steps 2–5) moves stable modifications of
`(C, D) ×_S T` along base changes `T' ⟶ T` (the proper maps `W'_j ⟶ T_j` of the RZ refinements)
and glues them. This file fixes the bundle of properties carried along (`IsStableModel`) and
proves that it is stable under base change along maps sending the generic point to the generic
point (`IsStableModel.pullback`, node G5), and that it yields Temkin's stable η-modifications
(`IsStableModel.isStableModification`).

* `GenericMarksCondition g D β D'`: the marks `D'` agree scheme-theoretically with `β⁻¹(D)` over
  the generic point of `T`, in the universal form "after pull-back along every morphism lying over
  `Spec κ(η)`" (so that it transfers along base changes and restrictions without identifying
  fibres). With flatness it gives `D' = genericMarksClosure β g D η`
  (`GenericMarksCondition.eq_genericMarksClosure`, via `eq_genericMarksClosure_of_comap_eq`).
* `IsStableModel pT g D β D'`: over an integral `T`, with `g : P ⟶ T` flat, `(X, D')` is a
  semi-stable pair over `T` satisfying the generic marks condition, numerically stable
  (`IsNumericallyStable`), projective over `P` relative to `P ⟶ T ⟶ Spec k`, and `β` is an
  isomorphism over a nonempty quasi-compact open of `T`.

Blueprint: `sm-global.tex`, `def:sm-global-stable-model`, `lem:sm-global-stable-model-pullback`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsRelativelyProjective)
open Curves (pullbackCompMap genericMarksClosure IsStableModification IsEtaModification)

section GenericMarks

variable {T P X : Scheme.{u}}

/-- **The generic marks condition**: the closed subschemes `D'` and `β⁻¹(D)` of `X` agree after
pull-back along every morphism `m : Y ⟶ X` lying over the generic point `Spec κ(η) ⟶ T`. -/
def GenericMarksCondition [IrreducibleSpace T] (g : P ⟶ T) (D : P.IdealSheafData) (β : X ⟶ P)
    (D' : X.IdealSheafData) : Prop :=
  ∀ (Y : Scheme.{u}) (m : Y ⟶ X) (n : Y ⟶ Spec (T.residueField (genericPoint T))),
    m ≫ β ≫ g = n ≫ T.fromSpecResidueField (genericPoint T) →
      D'.comap m = (D.comap β).comap m

variable [IrreducibleSpace T] {g : P ⟶ T} {D : P.IdealSheafData} {β : X ⟶ P}
  {D' : X.IdealSheafData}

/-- The generic marks condition on the generic fibre. -/
theorem GenericMarksCondition.fiber (h : GenericMarksCondition g D β D') :
    D'.comap ((β ≫ g).fiberι (genericPoint T)) =
      (D.comap β).comap ((β ≫ g).fiberι (genericPoint T)) :=
  h _ _ ((β ≫ g).fiberToSpecResidueField (genericPoint T)) pullback.condition

/-- The generic marks condition follows from its form on the generic fibre. -/
theorem GenericMarksCondition.of_fiber
    (h : D'.comap ((β ≫ g).fiberι (genericPoint T)) =
      (D.comap β).comap ((β ≫ g).fiberι (genericPoint T))) :
    GenericMarksCondition g D β D' := by
  intro Y m n hmn
  have h' : D'.comap (pullback.fst (β ≫ g) (T.fromSpecResidueField (genericPoint T))) =
      (D.comap β).comap (pullback.fst (β ≫ g) (T.fromSpecResidueField (genericPoint T))) := h
  have hl : m = pullback.lift m n (by rw [← hmn]) ≫
      pullback.fst (β ≫ g) (T.fromSpecResidueField (genericPoint T)) :=
    (pullback.lift_fst _ _ _).symm
  rw [hl, Scheme.IdealSheafData.comap_comp, h', ← Scheme.IdealSheafData.comap_comp]

/-- **G-marks**: flat marks satisfying the generic marks condition are the transported marks. -/
theorem GenericMarksCondition.eq_genericMarksClosure [IsIntegral T]
    (h : GenericMarksCondition g D β D') [Flat (D'.subschemeι ≫ β ≫ g)] :
    D' = genericMarksClosure β g D (genericPoint T) :=
  eq_genericMarksClosure_of_comap_eq β g D D' h.fiber

/-- The generic marks condition restricts along any morphism to `X`. -/
theorem GenericMarksCondition.comp {X' : Scheme.{u}} (h : GenericMarksCondition g D β D')
    (e : X' ⟶ X) : GenericMarksCondition g D (e ≫ β) (D'.comap e) := by
  intro Y m n hmn
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    h Y (m ≫ e) n (by rw [← hmn, Category.assoc, Category.assoc]),
    ← Scheme.IdealSheafData.comap_comp, Category.assoc]

/-- The generic marks condition transports along isomorphisms of the target over `T`. -/
theorem GenericMarksCondition.comp_iso {P' : Scheme.{u}} (h : GenericMarksCondition g D β D')
    (e : P ⟶ P') (g' : P' ⟶ T) (he : e ≫ g' = g) (D₂ : P'.IdealSheafData)
    (hD : D₂.comap e = D) : GenericMarksCondition g' D₂ (β ≫ e) D' := by
  intro Y m n hmn
  rw [h Y m n (by rw [← hmn, ← he]; simp only [Category.assoc]), ← hD,
    ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, Category.assoc]

/-- **Base change of the generic marks condition** along `h : T' ⟶ T` sending the generic point
to the generic point. -/
theorem GenericMarksCondition.pullback {T' : Scheme.{u}} [IrreducibleSpace T']
    (hg : GenericMarksCondition g D β D') (h : T' ⟶ T) (hη : h (genericPoint T') = genericPoint T) :
    GenericMarksCondition (pullback.snd g h) (D.comap (pullback.fst g h)) (pullbackCompMap β g h)
      (D'.comap (pullback.fst (β ≫ g) h)) := by
  intro Y m n hmn
  have hn : (m ≫ pullback.fst (β ≫ g) h) ≫ β ≫ g =
      (n ≫ Spec.map (h.residueFieldMap (genericPoint T')) ≫
        Spec.map (T.residueFieldCongr hη.symm).hom) ≫ T.fromSpecResidueField (genericPoint T) := by
    simp only [Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [← reassoc_of% hmn, ← pullback.condition, Curves.pullbackCompMap_fst_assoc]
  rw [← Scheme.IdealSheafData.comap_comp, hg Y _ _ hn]
  simp only [← Scheme.IdealSheafData.comap_comp, Category.assoc, Curves.pullbackCompMap_fst]

end GenericMarks

section Model

variable {k : Type u} [CommRing k] {T P X : Scheme.{u}}

/-- **A stable model over an integral base** (`PLAN-T5.md` §2.1 steps 2–5): for `g : P ⟶ T` flat
and marks `D ⊆ P`, the morphism `β : X ⟶ P` with marks `D' ⊆ X` makes `(X, D')` a semi-stable pair
over `T` whose marks agree with `β⁻¹(D)` over the generic point, numerically stable
(`IsNumericallyStable`), projective over `P` relative to `P ⟶ T ⟶ Spec k`, and an isomorphism
over a nonempty quasi-compact open `U ⊆ T`. -/
structure IsStableModel [IsIntegral T] (pT : T ⟶ Spec (.of k)) (g : P ⟶ T)
    (D : P.IdealSheafData) (β : X ⟶ P) (D' : X.IdealSheafData) : Prop where
  flat : Flat g
  isSemistablePair : IsSemistablePair (β ≫ g) D'
  genericMarks : GenericMarksCondition g D β D'
  isNumericallyStable : IsNumericallyStable β g D'
  isRelativelyProjective : IsRelativelyProjective (g ≫ pT) β
  isoLocus : ∃ U : T.Opens, (U : Set T).Nonempty ∧ QuasiCompact U.ι ∧
    IsIso (β ∣_ (g ⁻¹ᵁ U))

variable [IsIntegral T] {pT : T ⟶ Spec (.of k)} {g : P ⟶ T} {D : P.IdealSheafData}
  {β : X ⟶ P} {D' : X.IdealSheafData}

/-- The morphism of a stable model is proper. -/
theorem IsStableModel.isProper (h : IsStableModel pT g D β D') : IsProper β :=
  h.isRelativelyProjective.isProper

/-- The morphism of a stable model is an η-modification. -/
theorem IsStableModel.isEtaModification (h : IsStableModel pT g D β D') :
    IsEtaModification β g := by
  have := h.flat
  have := h.isProper
  have := h.isSemistablePair.nodal
  obtain ⟨U, hU, hUc, hiso⟩ := h.isoLocus
  exact Limits.SpreadModification.isEtaModification_of_isIso_morphismRestrict β g U hU

/-- **Stable models are stable η-modifications** (with the transported marks; exceptional
components are excluded numerically). -/
theorem IsStableModel.isStableModification
    (h : IsStableModel pT g D β D') : IsStableModification β g D D' where
  toIsEtaModification := h.isEtaModification
  marks_eq := by
    have := h.isSemistablePair.etale
    exact h.genericMarks.eq_genericMarksClosure
  isSemistablePair := h.isSemistablePair
  not_isExceptionalComponent := h.isNumericallyStable.not_isExceptionalComponent

/-- Precomposing a relatively projective morphism with an isomorphism keeps it relatively
projective. -/
theorem IsRelativelyProjective.iso_comp {T' X' X'' : Scheme.{u}} {pT' : T' ⟶ Spec (.of k)}
    {f : X' ⟶ T'} (h : IsRelativelyProjective pT' f) (e : X'' ⟶ X') [IsIso e] :
    IsRelativelyProjective pT' (e ≫ f) :=
  Projectivity.isRelativelyProjective_iso_hom_comp h (asIso e)

/-- **Base change of stable models** (`PLAN-T5.md` §2.1 step 3, node G5): along `h : T' ⟶ T`
quasi-compact, from an integral scheme and sending the generic point to the generic point, the
base change `pullbackCompMap β g h : X ×_T T' ⟶ P ×_T T'` is a stable model of
`(P ×_T T', D ×_T T')` over `T'`. -/
theorem IsStableModel.pullback {T' : Scheme.{u}} [IsIntegral T'] (hm : IsStableModel pT g D β D')
    (h : T' ⟶ T) [QuasiCompact h] (hη : h (genericPoint T') = genericPoint T) :
    IsStableModel (h ≫ pT) (pullback.snd g h) (D.comap (pullback.fst g h))
      (pullbackCompMap β g h) (D'.comap (pullback.fst (β ≫ g) h)) where
  flat := by
    have := hm.flat
    infer_instance
  isSemistablePair := by
    rw [Curves.pullbackCompMap_snd]
    exact Curves.IsSemistablePair.pullback hm.isSemistablePair h
  genericMarks := hm.genericMarks.pullback h hη
  isNumericallyStable := hm.isNumericallyStable.pullback h
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

end Model

end DeJongAlterations.StableModification.Global
