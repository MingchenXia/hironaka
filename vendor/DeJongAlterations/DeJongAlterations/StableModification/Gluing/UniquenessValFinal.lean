/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lanes T45F, T45G)
-/
import DeJongAlterations.StableModification.Gluing.UniquenessVal
import DeJongAlterations.StableModification.Gluing.ExistenceValFinal
import DeJongAlterations.StableModification.Global.DeJongTheorem
import DeJongAlterations.StableModification.Global.MainConn

/-!
# Uniqueness of stable modifications over valuation rings, unconditionally, and de Jong's theorem

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), Theorem
1.2 over a valuation ring through Proposition 4.5.1 (T:3233–3266) and Corollary 4.4.3 (1)
(`sepcloscor`, T:3135–3149), in the route of `PLAN-T5.md` §2.2 step 11 (node V3).

Lane T45F's `Gluing.UniquenessVal.valuationStableUniqueness` (`Gluing/UniquenessVal.lean`) takes
`ExistenceVal.ProjectiveSeparationAlgClosed` as a hypothesis, used only through lane T45E's
semi-stable stage `ExistenceVal.exists_isSemistableStage_comp` in the common semi-stable model
dominating the join of two stable modifications (`UniquenessVal.exists_common_stage`). The
hypothesis-free stage `ExistenceValFinal.exists_isSemistableStage_comp`
(`Gluing/ExistenceValFinal.lean`) removes it. This file restates T45F's two theorems with that
stage (the proofs are T45F's) and proves **`Global.ValuationStableUniqueness`** with no argument
(`valuationStableUniqueness`).

With `ExistenceValFinal.valuationStableExistence`, the hypotheses `hE` and `hU` of de Jong's
alteration theorem are discharged in its three integrated forms (`deJongAlterationTheorem`,
`deJongAlterationTheorem_conn`, `deJongAlterationTheorem_of_rational`): what remains is the
spreading of numerical stability and the projectivity of stable modifications.

## Main results

* `exists_common_stage`: a semi-stable stage dominating two η-modifications projective over `W`;
* `exists_iso_of_isStableModification`: uniqueness over one valuation ring;
* `valuationStableUniqueness : Global.ValuationStableUniqueness`;
* `deJongAlterationTheorem`, `deJongAlterationTheorem_conn`, `deJongAlterationTheorem_of_rational`:
  de Jong's alteration theorem from the spreading of numerical stability and projectivity.

Blueprint: `sm-gluing-existence-final.tex`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.UniquenessValFinal

open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)
open DeJong (IsNodalCurve IsSmoothAt IsSemistablePair)
open UniquenessVal hiding exists_common_stage exists_iso_of_isStableModification
  valuationStableUniqueness

set_option backward.isDefEq.respectTransparency false

section CommonStage

variable {K : Type u} [Field K] [IsAlgClosed K] {W : ValuationSubring K} [Finite (PrimeSpectrum W)]

/-- **A semi-stable stage dominating two modifications, unconditionally** (Temkin, proof of
Cor. 4.4.3 (1), T:3135–3149: a semi-stable `C̄` dominating `C'` and `C_st`; `PLAN-T5.md` §2.2
step 11): lane T45F's `UniquenessVal.exists_common_stage` without the hypothesis
`ProjectiveSeparation W`. Let `β₁ : C₁ → C`, `β₂ : C₂ → C` be η-modifications, projective over
`W`, of a curve `(C, D)` in the situation of Temkin's §4.5. Then there is a semi-stable stage
`Cb → C` of `(C, D)` (`BlowDown.IsSemistableStage`) factoring through modifications
`hᵢ : Cb → Cᵢ` with `h₁ ≫ β₁ = h₂ ≫ β₂`: `ExistenceValFinal.exists_isSemistableStage_comp` for the
join `J → C₁ → C` (`UniquenessVal.join`, projective over `W`). -/
theorem exists_common_stage
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (IsLocalRing.ResidueField W) p)
    {C : Scheme.{u}} (φ : C ⟶ Spec (.of W)) (D : C.IdealSheafData)
    (hC : Global.IsValuationCurve φ D) {C₁ C₂ : Scheme.{u}} (β₁ : C₁ ⟶ C) (β₂ : C₂ ⟶ C)
    [IsModification β₁] [IsModification β₂] (hη₁ : Curves.IsEtaModification β₁ φ)
    (hη₂ : Curves.IsEtaModification β₂ φ) (hp₁ : IsProjectiveOver (β₁ ≫ φ))
    (hp₂ : IsProjectiveOver (β₂ ≫ φ)) :
    ∃ (Cb : Scheme.{u}) (h₁ : Cb ⟶ C₁) (h₂ : Cb ⟶ C₂), IsModification h₁ ∧ IsModification h₂ ∧
      h₁ ≫ β₁ = h₂ ≫ β₂ ∧ BlowDown.IsSemistableStage φ D (h₁ ≫ β₁) := by
  have := hC.isIntegral
  have := hC.flat
  have : IsProper φ := hC.isProjectiveOver.isProper
  have hm₁ : IsModification β₁ := inferInstance
  have hm₂ : IsModification β₂ := inferInstance
  have := hm₁.sourceIntegral
  have := hm₂.sourceIntegral
  have : Flat (β₁ ≫ φ) := Gluing.flat_of_apply_genericPoint_eq_bot (β₁ ≫ φ) (by
    rw [Scheme.Hom.comp_apply, genericPoint_map_of_isDominant β₁]
    exact Gluing.apply_genericPoint_eq_bot_of_flat φ)
  -- the generic open, over which both `βᵢ` are isomorphisms
  set U := φ ⁻¹ᵁ BlowDown.genericOpen W with hUdef
  have : IsIso (β₁ ∣_ U) := BlowDown.isIso_restrict_genericOpen φ β₁ hη₁
  have : IsIso (β₂ ∣_ U) := BlowDown.isIso_restrict_genericOpen φ β₂ hη₂
  have hU : genericPoint C₁ ∈ β₁ ⁻¹ᵁ U := by
    change (β₁ ≫ φ) (genericPoint C₁) ∈ (BlowDown.genericOpen W : Set (Spec (.of W)))
    rw [BlowDown.coe_genericOpen, genericPoint_eq_bot_of_affine]
    exact Gluing.apply_genericPoint_eq_bot_of_flat (β₁ ≫ φ)
  -- the join
  have := isModification_joinFst β₁ β₂ U hU
  have := isModification_joinSnd β₁ β₂ U hU
  have : IsModification (joinFst β₁ β₂ U hU ≫ β₁) := IsModification.comp _ _
  have hjp : IsProjectiveOver ((joinFst β₁ β₂ U hU ≫ β₁) ≫ φ) := by
    rw [Category.assoc]
    exact isProjectiveOver_join β₁ β₂ U hU φ hp₁ hp₂
  -- the semi-stable stage through the join (lane T45E, without separation hypothesis)
  obtain ⟨X, g, hst⟩ := ExistenceValFinal.exists_isSemistableStage_comp hchar φ D hC _ hjp
  have := hst.isIntegral
  have : IsModification (g ≫ joinFst β₁ β₂ U hU ≫ β₁) :=
    hst.isEtaModification.toIsSchematicModification.isModification
  have : IsModification g := Gluing.isModification_of_comp g (joinFst β₁ β₂ U hU ≫ β₁)
  refine ⟨X, g ≫ joinFst β₁ β₂ U hU, g ≫ joinSnd β₁ β₂ U hU, IsModification.comp _ _,
    IsModification.comp _ _, ?_, ?_⟩
  · simp only [Category.assoc, pullback.condition]
  · rw [Category.assoc]
    exact hst

end CommonStage

section Main

variable {K : Type u} [Field K] [IsAlgClosed K] {W : ValuationSubring K} [Finite (PrimeSpectrum W)]

/-- **Uniqueness of stable modifications over a valuation ring, unconditionally** (Temkin, Thm 1.2
over a valuation ring via Prop. 4.5.1, T:3233–3266, and Cor. 4.4.3 (1), T:3135–3149; `PLAN-T5.md`
§2.2 step 11, node V3): lane T45F's `UniquenessVal.exists_iso_of_isStableModification` without the
hypothesis `ProjectiveSeparation W`. Let `K` be algebraically closed, `W ⊆ K` a valuation ring of
finite height and equal characteristic, and `(φ : C → Spec W, D)` a curve in the situation of
Temkin's §4.5 (`Global.IsValuationCurve`). Two stable, numerically stable η-modifications
`β₁, β₂` of `(C, D)`, projective over `W`, are isomorphic over `C`. -/
theorem exists_iso_of_isStableModification
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (IsLocalRing.ResidueField W) p)
    {C : Scheme.{u}} (φ : C ⟶ Spec (.of W)) (D : C.IdealSheafData)
    (hC : Global.IsValuationCurve φ D) {C₁ C₂ : Scheme.{u}} (β₁ : C₁ ⟶ C) (β₂ : C₂ ⟶ C)
    (D₁ : C₁.IdealSheafData) (D₂ : C₂.IdealSheafData)
    (hs₁ : Curves.IsStableModification β₁ φ D D₁) (hn₁ : Global.IsNumericallyStable β₁ φ D₁)
    (hp₁ : IsProjectiveOver (β₁ ≫ φ))
    (hs₂ : Curves.IsStableModification β₂ φ D D₂) (hn₂ : Global.IsNumericallyStable β₂ φ D₂)
    (hp₂ : IsProjectiveOver (β₂ ≫ φ)) :
    ∃ e : C₁ ≅ C₂, e.hom ≫ β₂ = β₁ := by
  classical
  -- the base curve
  have := hC.isIntegral
  have := hC.flat
  have := hC.locallyOfFinitePresentation
  have hCp := hC.isProjectiveOver
  have : IsProper φ := hCp.isProper
  have htr := ExistenceVal.fiberTrdeg_genericPoint_eq_one φ hC.genericPair.nodal
  have hsep := isSepClosed_fractionRing_quotient W
  have hac := isAlgClosed_residueField W
  have := infinite_residueField W
  -- the stable modifications
  have hη₁ := hs₁.toIsEtaModification
  have hη₂ := hs₂.toIsEtaModification
  have hpair₁ := hs₁.isSemistablePair
  have hpair₂ := hs₂.isSemistablePair
  have := hpair₁.nodal
  have := hpair₂.nodal
  have := hpair₁.etale
  have := hpair₂.etale
  have : IsIntegral C₁ := isIntegral_of_isEtaModification φ β₁ hη₁
  have : IsIntegral C₂ := isIntegral_of_isEtaModification φ β₂ hη₂
  have : IsModification β₁ := isModification_of_isEtaModification φ β₁ hη₁
  have : IsModification β₂ := isModification_of_isEtaModification φ β₂ hη₂
  have hnormal₁ : IsNormalScheme C₁ :=
    isNormalScheme_of_isEtaModification φ β₁ hη₁ hC.isSmoothAt_generic
  have hnormal₂ : IsNormalScheme C₂ :=
    isNormalScheme_of_isEtaModification φ β₂ hη₂ hC.isSmoothAt_generic
  -- a common semi-stable model
  obtain ⟨Cb, h₁, h₂, hh₁, hh₂, hcomm, hst⟩ :=
    exists_common_stage hchar φ D hC β₁ β₂ hη₁ hη₂ hp₁ hp₂
  have := hst.isIntegral
  have hnormb := hst.isNormalScheme
  have hηb := hst.isEtaModification
  have hpairb := hst.isSemistablePair
  have hpb := hst.isProjectiveOver
  have := hpairb.nodal
  have := hpairb.etale
  -- the marks: sections of `C`, lifted to `Cb`
  obtain ⟨n, c, hc⟩ := exists_areGenericMarkSections hC
  have : IsIso ((h₁ ≫ β₁) ∣_ (φ ⁻¹ᵁ BlowDown.genericOpen W)) :=
    BlowDown.isIso_restrict_genericOpen φ _ hηb
  choose σ hσ using fun k ↦ Gluing.StableVal.exists_lift_of_isIso (h₁ ≫ β₁)
    (φ ⁻¹ᵁ BlowDown.genericOpen W) (c k)
    (Gluing.StableVal.apply_genericPoint_mem_genericOpen φ (c k) (hc.section_eq k))
  have hmb := hc.of_isEtaModification (h₁ ≫ β₁) hηb σ hσ
  have hm₁ : AreGenericMarkSections (β₁ ≫ φ) D₁ (fun k ↦ σ k ≫ h₁) := by
    rw [hs₁.marks_eq]
    exact hc.of_isEtaModification β₁ hη₁ _ fun k ↦ by rw [Category.assoc, hσ k]
  have hm₂ : AreGenericMarkSections (β₂ ≫ φ) D₂ (fun k ↦ σ k ≫ h₂) := by
    rw [hs₂.marks_eq]
    exact hc.of_isEtaModification β₂ hη₂ _ fun k ↦ by rw [Category.assoc, ← hcomm, hσ k]
  -- the normalization of the base
  have : Flat (h₁ ≫ β₁ ≫ φ) := by rw [← Category.assoc]; infer_instance
  obtain ⟨N, _, ν, f₁, f₂, hNn, hνη, hνp, hf₁, hf₂, hhf⟩ :=
    exists_normalization_lifts φ hCp hnormb h₁ h₂ β₁ β₂ hnormal₁ hnormal₂ hcomm hηb
      (by rw [← Category.assoc]; exact hpb)
  subst hf₁ hf₂
  -- the base `N` and the modifications
  have : IsModification ν := hνη.toIsSchematicModification.isModification
  have : IsModification f₁ := Gluing.isModification_of_comp f₁ ν
  have : IsModification f₂ := Gluing.isModification_of_comp f₂ ν
  have : IsProper (ν ≫ φ) := hνp.isProper
  have : Flat (ν ≫ φ) := Gluing.flat_of_apply_genericPoint_eq_bot (ν ≫ φ) (by
    rw [Scheme.Hom.comp_apply, genericPoint_map_of_isDominant ν]
    exact Gluing.apply_genericPoint_eq_bot_of_flat φ)
  have : LocallyOfFinitePresentation (ν ≫ φ) :=
    Gluing.locallyOfFinitePresentation_of_flat (ν ≫ φ)
  have hcurve : fiberTrdeg (ν ≫ φ) (genericPoint N) ≤ 1 := by
    rw [ValCurves.fiberTrdeg_comp_genericPoint φ ν, htr]
  have e₁ : (f₁ ≫ ν) ≫ φ = f₁ ≫ ν ≫ φ := Category.assoc _ _ _
  have e₂ : (f₂ ≫ ν) ≫ φ = f₂ ≫ ν ≫ φ := Category.assoc _ _ _
  have : IsNodalCurve (f₁ ≫ ν ≫ φ) := e₁ ▸ hpair₁.nodal
  have : IsNodalCurve (f₂ ≫ ν ≫ φ) := e₂ ▸ hpair₂.nodal
  have hp₁' : IsProjectiveOver (f₁ ≫ ν ≫ φ) := e₁ ▸ hp₁
  have hp₂' : IsProjectiveOver (f₂ ≫ ν ≫ φ) := e₂ ▸ hp₂
  have : IsProper (f₁ ≫ ν ≫ φ) := hp₁'.isProper
  have : IsProper (f₂ ≫ ν ≫ φ) := hp₂'.isProper
  -- the common model `Cb` over `N`
  set q := h₁ ≫ f₁ ≫ ν ≫ φ with hqdef
  have eb : (h₁ ≫ f₁ ≫ ν) ≫ φ = q := by simp only [hqdef, Category.assoc]
  have hq₂ : h₂ ≫ f₂ ≫ ν ≫ φ = q := by rw [← Category.assoc, ← hhf, Category.assoc]
  have : IsNodalCurve q := eb ▸ hpairb.nodal
  have hpq : IsProjectiveOver q := eb ▸ hpb
  have : IsProper q := hpq.isProper
  have hfp₁ : DeJong.IsRelativelyProjective (f₁ ≫ ν ≫ φ) h₁ :=
    Projectivity.isRelativelyProjective_of_isProjectiveOver (f₁ ≫ ν ≫ φ) h₁ hpq
  have hfp₂ : DeJong.IsRelativelyProjective (f₂ ≫ ν ≫ φ) h₂ :=
    Projectivity.isRelativelyProjective_of_isProjectiveOver (f₂ ≫ ν ≫ φ) h₂ (hq₂ ▸ hpq)
  have : IsNodalCurve (h₂ ≫ f₂ ≫ ν ≫ φ) := hq₂ ▸ inferInstance
  have hη₁' : Curves.IsEtaModification h₁ (f₁ ≫ ν ≫ φ) :=
    Gluing.isEtaModification_of_isNodalCurve (f₁ ≫ ν ≫ φ) (fun x _ ↦ (hnormal₁ x).2) h₁
  have hη₂' : Curves.IsEtaModification h₂ (f₂ ≫ ν ≫ φ) :=
    Gluing.isEtaModification_of_isNodalCurve (f₂ ≫ ν ≫ φ) (fun x _ ↦ (hnormal₂ x).2) h₂
  -- pure one-dimensional fibres of `N`
  have hpure : ∀ s, ∀ Z ∈ irreducibleComponents ((ν ≫ φ).fiber s), topologicalKrullDim Z = 1 := by
    have hηf : Curves.IsEtaModification f₁ (ν ≫ φ) :=
      Gluing.isEtaModification_of_isNodalCurve (ν ≫ φ) (fun x _ ↦ (hNn x).2) f₁
    have : Surjective f₁ := ⟨(surjective_of_isDominant_of_isClosed_range f₁
      f₁.isClosedMap.isClosed_range).surj⟩
    have : IsDominant (ν ≫ φ) := BlowDown.isDominant_of_flat (ν ≫ φ)
    have : Nonempty ((f₁ ≫ ν ≫ φ).fiber (genericPoint (Spec (.of W)))) := by
      have hg : (f₁ ≫ ν ≫ φ) (genericPoint C₁) = genericPoint (Spec (.of W)) := by
        rw [genericPoint_eq_bot_of_affine]
        exact Gluing.apply_genericPoint_eq_bot_of_flat _
      exact ⟨hg ▸ (f₁ ≫ ν ≫ φ).asFiber (genericPoint C₁)⟩
    have h := BlowDown.hasPureFiberDimension_of_isNodalCurve_comp (ν ≫ φ) f₁
      (BlowDown.one_le_fiberDimension_genericPoint (ν ≫ φ) f₁ hηf.isIso_fiberMap)
    intro s Z hZ
    simpa using h s Z hZ
  -- the marks
  have hσq : ∀ k, σ k ≫ q = 𝟙 _ := fun k ↦ by rw [← eb]; exact hmb.section_eq k
  have hsmq : ∀ s k, IsSmoothAt q (σ k s) := fun s k ↦ eb ▸ hmb.isSmoothAt hpairb k s
  have hmarks₁ : ∀ s, ∀ i j, h₁ (σ i s) = h₁ (σ j s) → i = j := fun s i j h ↦
    hm₁.eq_of_apply_eq (s := s) h
  have hmarks₂ : ∀ s, ∀ i j, h₂ (σ i s) = h₂ (σ j s) → i = j := fun s i j h ↦
    hm₂.eq_of_apply_eq (s := s) h
  have hsm₁ : ∀ s i, IsSmoothAt (f₁ ≫ ν ≫ φ) (h₁ (σ i s)) := fun s i ↦
    e₁ ▸ hm₁.isSmoothAt hpair₁ i s
  have hsm₂ : ∀ s i, IsSmoothAt (f₂ ≫ ν ≫ φ) (h₂ (σ i s)) := fun s i ↦
    e₂ ▸ hm₂.isSmoothAt hpair₂ i s
  -- the stability of the fibres in combinatorial form
  have hst₁ : ∀ s, BlowDown.Domination.FibreStable (ν ≫ φ) f₁ s (fun i ↦ σ i ≫ h₁) := by
    intro s
    have := hac s
    have : IsAlgClosed (IsLocalRing.ResidueField ((Spec (.of W)).presheaf.stalk s)) := hac s
    refine fibreStable_of_numericallyStableFibre (ν ≫ φ) f₁ _ s hNn hcurve hp₁' D₁
      (fun x hx ↦ e₁ ▸ hpair₁.smoothAlong x hx) (fun y hy ↦ ?_)
      (numericallyStableFibre_comp f₁ ν φ D₁ _ (hn₁ _ _))
    obtain ⟨k, t, hkt⟩ := hm₁.exists_eq_of_mem_support hy
    refine ⟨k, ?_⟩
    have ht : t = s := by
      have h1 : (f₁ ≫ ν ≫ φ) ((σ k ≫ h₁) t) = s := by
        rw [hkt]
        exact BlowDown.apply_fiberι _ s y
      have h2 : (f₁ ≫ ν ≫ φ) ((σ k ≫ h₁) t) = t := by
        rw [← Scheme.Hom.comp_apply, ← e₁, hm₁.section_eq k]
        rfl
      rw [← h2, h1]
    subst ht
    exact hkt
  have hst₂ : ∀ s, BlowDown.Domination.FibreStable (ν ≫ φ) f₂ s (fun i ↦ σ i ≫ h₂) := by
    intro s
    have := hac s
    have : IsAlgClosed (IsLocalRing.ResidueField ((Spec (.of W)).presheaf.stalk s)) := hac s
    refine fibreStable_of_numericallyStableFibre (ν ≫ φ) f₂ _ s hNn hcurve hp₂' D₂
      (fun x hx ↦ e₂ ▸ hpair₂.smoothAlong x hx) (fun y hy ↦ ?_)
      (numericallyStableFibre_comp f₂ ν φ D₂ _ (hn₂ _ _))
    obtain ⟨k, t, hkt⟩ := hm₂.exists_eq_of_mem_support hy
    refine ⟨k, ?_⟩
    have ht : t = s := by
      have h1 : (f₂ ≫ ν ≫ φ) ((σ k ≫ h₂) t) = s := by
        rw [hkt]
        exact BlowDown.apply_fiberι _ s y
      have h2 : (f₂ ≫ ν ≫ φ) ((σ k ≫ h₂) t) = t := by
        rw [← Scheme.Hom.comp_apply, ← e₂, hm₂.section_eq k]
        rfl
      rw [← h2, h1]
    subst ht
    exact hkt
  -- Corollary 4.4.3 (1) twice
  obtain ⟨e, he⟩ := BlowDown.Domination.nonempty_iso_of_fibreStable (ν ≫ φ) σ hsep hac f₁ f₂ h₁ h₂
    q hhf rfl hσq hp₁' hp₂' hfp₁ hfp₂ hNn hnormal₁ hnormal₂ hcurve hη₁' hη₂' hpure
    (fun s v hv ↦ BlowDown.Unconditional.componentGenus_fiber_nonneg q hpq s hv)
    (fun s i y hy ↦ BlowDown.Domination.isSmoothAt_fiber_of_isSmoothAt q s (hy ▸ hsmq s i))
    (fun s x _ ↦ BlowDown.Domination.marks_semistable_of_injective (f₁ ≫ ν ≫ φ) s
      (fun i ↦ h₁ (σ i s)) (hmarks₁ s) (hsm₁ s) x)
    (fun s x _ ↦ BlowDown.Domination.marks_semistable_of_injective (f₂ ≫ ν ≫ φ) s
      (fun i ↦ h₂ (σ i s)) (hmarks₂ s) (hsm₂ s) x)
    hst₁ hst₂
  exact ⟨e, by rw [← Category.assoc, he]⟩

end Main

section Statement

/-- **`Global.ValuationStableUniqueness` holds** (Temkin, Thm 1.2 over a valuation ring via
Prop. 4.5.1; `PLAN-T5.md` §1.3, node V3): over a valuation ring of finite height and equal
characteristic whose fraction field is algebraically closed, two stable, numerically stable
η-modifications, projective over the valuation ring, of a curve in the situation of Temkin's §4.5
are isomorphic over the curve. -/
theorem valuationStableUniqueness : Global.ValuationStableUniqueness.{u} := by
  intro K _ _ W _ hchar C φ D hC C₁ C₂ β₁ β₂ D₁ D₂ hs₁ hn₁ hp₁ hs₂ hn₂ hp₂
  exact exists_iso_of_isStableModification hchar φ D hC β₁ β₂ D₁ D₂ hs₁ hn₁ hp₁ hs₂ hn₂ hp₂

end Statement

section DeJong

/-- **De Jong's alteration theorem from the spreading of numerical stability and projectivity**
(`Global.deJongAlterationTheorem` with its hypotheses `hE` and `hU` discharged by
`ExistenceValFinal.valuationStableExistence` and `valuationStableUniqueness`; blueprint
`cor:sm-global-dejong`): from `Global.StableOpenNbhd k` (Temkin, Lemma 5.1 (ii)) and the
projectivity of locally projective stable modifications (`Global.StableModificationProjectivity k`,
Temkin, Thm 1.1). -/
theorem deJongAlterationTheorem {k : Type u} [Field k] [IsAlgClosed k]
    (hO : Global.StableOpenNbhd k) (hP : Global.StableModificationProjectivity k) :
    DeJongAlterationTheorem k :=
  Global.deJongAlterationTheorem ExistenceValFinal.valuationStableExistence
    valuationStableUniqueness hO hP

/-- **De Jong's alteration theorem from the corrected spreading and projectivity**
(`Global.deJongAlterationTheorem_conn` with `hE` and `hU` discharged; blueprint
`cor:sm-gso-dejong`): from the corrected spreading of numerical stability
`Global.StableOpenNbhdConn k` (ERRATA DJA-O36) and projectivity. -/
theorem deJongAlterationTheorem_conn {k : Type u} [Field k] [IsAlgClosed k]
    (hO : Global.StableOpenNbhdConn k) (hP : Global.StableModificationProjectivity k) :
    DeJongAlterationTheorem k :=
  Global.deJongAlterationTheorem_conn ExistenceValFinal.valuationStableExistence
    valuationStableUniqueness hO hP

/-- **De Jong's alteration theorem from the ω step and projectivity**
(`Global.deJongAlterationTheorem_of_rational` with `hE` and `hU` discharged; blueprint
`cor:sm-gso-dejong`): from `Global.StableOpenNbhdRational K` for all algebraically closed `K`
(numerical stability spreads from a rational point of a normal variety) and projectivity. -/
theorem deJongAlterationTheorem_of_rational {k : Type u} [Field k] [IsAlgClosed k]
    (hR : ∀ (K : Type u) [Field K] [IsAlgClosed K], Global.StableOpenNbhdRational K)
    (hP : Global.StableModificationProjectivity k) :
    DeJongAlterationTheorem k :=
  Global.deJongAlterationTheorem_of_rational ExistenceValFinal.valuationStableExistence
    valuationStableUniqueness hR hP

end DeJong

end DeJongAlterations.StableModification.Gluing.UniquenessValFinal
