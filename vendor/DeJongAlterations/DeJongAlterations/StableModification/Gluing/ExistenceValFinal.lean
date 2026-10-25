/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lanes T45E, T45G)
-/
import DeJongAlterations.StableModification.Gluing.MarksNodalFinal
import DeJongAlterations.StableModification.Gluing.ExistenceVal
import DeJongAlterations.StableModification.BlowDown.UnconditionalFinal

/-!
# Existence of stable modifications over valuation rings, unconditionally

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`),
Proposition 4.5.1 (`sepclosprop`, T:3233–3266), existence part, in the form of `PLAN-T5.md` §2.2
steps 1–10 (nodes V1, V2): over a valuation ring `W` of finite height and equal characteristic
whose fraction field `K` is algebraically closed, every curve `φ : C → Spec W` in the situation
`Global.IsValuationCurve` has a stable, numerically stable η-modification projective over `W`.

Lane T45E's `Gluing/ExistenceVal.lean` proves this from two named hypotheses:
`ExistenceVal.ProjectiveSeparationAlgClosed` (projective separation of marks, lane T45D) and
`BlowDown.ExcSpecialize.ClosureComponentLocal` (lane T44G). Both inputs are now theorems in the
form consumed:

* the separation of marks enters only through the local marked models at the closed bad points of
  the normalized refinement, and lane T45D's `StableVal.exists_local_marked_model_of_piece` gives
  them with no hypothesis (`MarksNodalFinal.exists_marked_nodal_modification`);
* `ExcSpecialize.closureComponentLocal` (lane T44G) proves `ClosureComponentLocal`; the stable
  blow-down without it is (in `BlowDown`)
  `UnconditionalFinal.exists_isStableModification_of_isSemistableStage_of_isProjectiveOver`.

This file restates lane T45E's results without the two hypotheses (the proofs are T45E's) and
proves **`Global.ValuationStableExistence`** (`valuationStableExistence`, no argument). The
hypothesis-free semi-stable stage also removes the separation hypothesis from uniqueness over
valuation rings (`Gluing/UniquenessValFinal.lean`), where de Jong's alteration theorem is stated
with both `hE` and `hU` discharged.

`ExistenceVal.ProjectiveSeparationAlgClosed` itself (projective separation relative to `B → Spec R`
for an *arbitrary* separated strictly semi-stable `B`) is not proved and not needed: see
`Gluing/MarksSeparation.lean` and the blueprint remark `rem:sm-sep-proj-interface`.

## Main results

* `exists_isSemistableStage_comp`: a projective semi-stable stage through a projective
  modification `h : C' → C`;
* `exists_stableModification_comp`: such a stage together with the stable modification it
  dominates;
* `exists_stableModification`: the existence over one valuation ring;
* `valuationStableExistence : Global.ValuationStableExistence`.

Blueprint: `sm-gluing-existence-final.tex`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.ExistenceValFinal

open DeJong (IsNodalCurve IsSmoothAt IsSemistablePair)
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)
open StableVal

set_option backward.isDefEq.respectTransparency false

section Main

variable {K : Type u} [Field K] [IsAlgClosed K] {W : ValuationSubring K} [Finite (PrimeSpectrum W)]

/-- **A projective semi-stable stage dominating a projective modification, unconditionally**
(Temkin, proof of Proposition 4.5.1, T:3243–3266, steps up to the blow-down; `PLAN-T5.md` §2.2
steps 1–9, nodes V1, V2): lane T45E's `ExistenceVal.exists_isSemistableStage_comp` without the
hypothesis `ProjectiveSeparation W`. Let `K` be algebraically closed, `W ⊆ K` a valuation ring of
finite height and equal characteristic, `(φ : C → Spec W, D)` a curve in the situation of Temkin's
§4.5 (`Global.IsValuationCurve`), and `h : C' → C` a modification with `C'` projective over `W`.
Then there is a semi-stable stage of `(C, D)` (`BlowDown.IsSemistableStage`: an integral normal
η-modification, projective over `W`, whose transported marks form a semi-stable pair) factoring
through `h`.

The proof is lane T45E's, with the marked nodal model `X → N → C'` of
`MarksNodalFinal.exists_marked_nodal_modification` (no separation hypothesis); `X` is projective
over `W` by the valuation-level projectivity theorem
(`Projectivity.Valuation.isProjectiveOver_of_valuationSubring`). -/
theorem exists_isSemistableStage_comp
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (IsLocalRing.ResidueField W) p)
    {C : Scheme.{u}} (φ : C ⟶ Spec (.of W)) (D : C.IdealSheafData)
    (hV : Global.IsValuationCurve φ D) {C' : Scheme.{u}} (h : C' ⟶ C) [IsModification h]
    (hC' : IsProjectiveOver (h ≫ φ)) :
    ∃ (X : Scheme.{u}) (g : X ⟶ C'), BlowDown.IsSemistableStage φ D (g ≫ h) := by
  classical
  have := hV.isIntegral
  have := hV.flat
  have := hV.locallyOfFinitePresentation
  have hC := hV.isProjectiveOver
  have : IsProper φ := hC.isProper
  have hnod : IsNodalCurve (φ.fiberToSpecResidueField (genericPoint (Spec (.of W)))) :=
    hV.genericPair.nodal
  have hnorm := ExistenceVal.isIntegrallyClosed_stalk_of_generic φ hnod hV.isSmoothAt_generic
  have htr := ExistenceVal.fiberTrdeg_genericPoint_eq_one φ hnod
  -- the curve `C'`: integral, proper and flat over `W`, normal along its generic fibre
  have hh : IsModification h := inferInstance
  have := hh.sourceIntegral
  have hgen' : (h ≫ φ) (genericPoint C') = (⊥ : PrimeSpectrum W) := by
    rw [Scheme.Hom.comp_apply, Geometry.NormalCurveModification.genericPoint_map h hh.birational]
    exact apply_genericPoint_eq_bot_of_flat φ
  have : Flat (h ≫ φ) := flat_of_apply_genericPoint_eq_bot (h ≫ φ) hgen'
  have : C'.IsSeparated := ⟨by rw [← terminal.comp_from (h ≫ φ)]; infer_instance⟩
  have : CompactSpace C' := BlowDown.compactSpace_of_quasiCompact (h ≫ φ)
  have htr' : fiberTrdeg (h ≫ φ) (genericPoint C') = 1 := by
    rw [ValCurves.fiberTrdeg_comp_genericPoint φ h, htr]
  have : IsIso (h ∣_ (φ ⁻¹ᵁ BlowDown.genericOpen W)) :=
    isIso_restrict_genericOpen φ hnorm htr.le h
  have hnorm' : ∀ x : C', (h ≫ φ) x = genericPoint (Spec (.of W)) →
      IsIntegrallyClosed (C'.presheaf.stalk x) := by
    intro x hx
    have hx' : φ (h x) = genericPoint (Spec (.of W)) := by
      rw [← Scheme.Hom.comp_apply]
      exact hx
    have hxU : h x ∈ φ ⁻¹ᵁ BlowDown.genericOpen W := by
      change φ (h x) ∈ (BlowDown.genericOpen W : Set _)
      rw [BlowDown.coe_genericOpen]
      exact hx'
    have := CurvesField.Genus.isIso_stalkMap_of_isIso_morphismRestrict h _ x hxU
    have := hnorm (h x) hx'
    exact IsIntegrallyClosed.of_equiv (asIso (h.stalkMap x)).commRingCatIsoToRingEquiv
  -- the generic marks are finitely many sections (Temkin T:3025–3027), lifted to `C'`
  have : IsAlgClosed ((Spec (.of W)).residueField (pt₀ (V := W))) :=
    ExistenceVal.isAlgClosed_residueField_pt₀
  have he : Etale ((DeJong.fiberMarks φ D pt₀).subschemeι ≫ φ.fiberToSpecResidueField pt₀) := by
    have h := hV.genericPair.etale
    rwa [genericPoint_eq_pt₀] at h
  obtain ⟨n, σ, hσ, hinj₀, hmem⟩ := exists_sections_of_etale_genericMarks φ D he
  choose σ' hσ' using fun k ↦ exists_lift_section φ hnorm htr.le h (σ k) (hσ k)
  have hσ'sec : ∀ k, σ' k ≫ h ≫ φ = 𝟙 _ := fun k ↦ by rw [← Category.assoc, hσ', hσ]
  have hinj : Function.Injective fun k ↦ σ' k (genericPoint (Spec (.of W))) := by
    intro k l hkl
    apply hinj₀
    change σ k pt₀ = σ l pt₀
    rw [← hσ' k, ← hσ' l, ← genericPoint_eq_pt₀, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact congrArg h hkl
  -- the nodal model with separated marks (steps 1–8)
  obtain ⟨N, _, b, X, β, σX, hb, hβ, -, hNlfp, hNproj, hXnod, hXloc, hσX, hdisj, hsm⟩ :=
    MarksNodalFinal.exists_marked_nodal_modification hchar (h ≫ φ) htr' hnorm' σ' hσ'sec hinj
  have := hβ.sourceIntegral
  have : IsModification (β ≫ b) := IsModification.comp β b
  have : IsModification ((β ≫ b) ≫ h) := IsModification.comp (β ≫ b) h
  set f : X ⟶ C := (β ≫ b) ≫ h with hfdef
  have hfφ : f ≫ φ = β ≫ b ≫ h ≫ φ := by simp only [hfdef, Category.assoc]
  have hYproj : IsProjectiveOver (b ≫ h ≫ φ) := hNproj hC'
  -- `X → C` is an isomorphism over the generic fibre
  have : IsIso (f ∣_ (φ ⁻¹ᵁ BlowDown.genericOpen W)) := isIso_restrict_genericOpen φ hnorm htr.le f
  have hgenU : ∀ x : X, (β ≫ b ≫ h ≫ φ) x = genericPoint (Spec (.of W)) →
      f x ∈ φ ⁻¹ᵁ BlowDown.genericOpen W := fun x hx ↦ by
    change φ (f x) ∈ (BlowDown.genericOpen W : Set _)
    rw [BlowDown.coe_genericOpen, ← Scheme.Hom.comp_apply, hfφ]
    exact hx
  have hsmgen : ∀ x : X, (β ≫ b ≫ h ≫ φ) x = genericPoint (Spec (.of W)) →
      IsSmoothAt (β ≫ b ≫ h ≫ φ) x := by
    intro x hx
    have hφx : φ (f x) = genericPoint (Spec (.of W)) := by
      rw [← Scheme.Hom.comp_apply, hfφ]
      exact hx
    have h1 := isSmoothAt_of_mem_isomorphismOpen f φ (V := φ ⁻¹ᵁ BlowDown.genericOpen W)
      (hgenU x hx) (hV.isSmoothAt_generic _ hφx)
    rwa [hfφ] at h1
  -- projectivity of `X` over `W` (node V1, lane OM3F's `thm:sm-val-proj`)
  have := hXnod
  have : LocallyOfFinitePresentation (b ≫ h ≫ φ) := hNlfp
  have hXproj : IsProjectiveOver (β ≫ b ≫ h ≫ φ) :=
    Projectivity.Valuation.isProjectiveOver_of_valuationSubring W (b ≫ h ≫ φ) hYproj β hXloc
  -- the marks of `X`: a semi-stable pair
  have hσXf : ∀ k, σX k ≫ f = σ k := fun k ↦ by
    rw [hfdef, ← Category.assoc, hσX, hσ']
  have hσXsec : ∀ k, σX k ≫ β ≫ b ≫ h ≫ φ = 𝟙 _ := fun k ↦ by
    rw [← hfφ, ← Category.assoc, hσXf, hσ]
  set DX : X.IdealSheafData := ⨅ k, (σX k).ker with hDX
  have hpair : IsSemistablePair (β ≫ b ≫ h ≫ φ) DX :=
    isSemistablePair_iInf_ker σX hσXsec hdisj hsm
  -- `X → C` is an η-modification and `DX` are the transported marks
  have : IsNodalCurve (f ≫ φ) := by
    rw [hfφ]
    exact hXnod
  have hη : Curves.IsEtaModification f φ := Gluing.isEtaModification_of_isNodalCurve φ hnorm f
  have : IsIso (Curves.fiberMap f φ (genericPoint (Spec (.of W)))) := hη.isIso_fiberMap
  have : IsReduced (DeJong.fiberMarks φ D (genericPoint (Spec (.of W)))).subscheme :=
    @Global.isReduced_of_etale_field _ _ _ _ hV.genericPair.etale
  have : IsReduced ((DeJong.fiberMarks φ D (genericPoint (Spec (.of W)))).comap
      (Curves.fiberMap f φ (genericPoint (Spec (.of W))))).subscheme :=
    Global.isReduced_comap_of_isIso _ _
  have : Etale (DX.subschemeι ≫ f ≫ φ) := by
    rw [hfφ]
    exact hpair.etale
  have hmarks : DX = Curves.genericMarksClosure f φ D (genericPoint (Spec (.of W))) := by
    refine Global.eq_genericMarksClosure_of_forall f φ D DX fun x hx ↦ ?_
    rw [hfφ] at hx
    rw [hDX, support_iInf_ker' σX hσXsec]
    have hφx : φ (f x) = pt₀ := by
      rw [← genericPoint_eq_pt₀, ← Scheme.Hom.comp_apply, hfφ]
      exact hx
    rw [hmem _ hφx]
    constructor
    · intro hxk
      obtain ⟨k, t, rfl⟩ := Set.mem_iUnion.mp hxk
      have ht : t = pt₀ := by
        rw [← genericPoint_eq_pt₀, ← hx, ← Scheme.Hom.comp_apply, hσXsec]
        rfl
      refine ⟨k, ?_⟩
      rw [← Scheme.Hom.comp_apply, hσXf, ht]
    · rintro ⟨k, hk⟩
      have h1 : f (σX k pt₀) = f x := by
        rw [← Scheme.Hom.comp_apply, hσXf, hk]
      have h2 : f (σX k pt₀) ∈ φ ⁻¹ᵁ BlowDown.genericOpen W := by
        rw [h1]
        exact hgenU x hx
      exact Set.mem_iUnion.mpr ⟨k, pt₀, eq_of_isIso_restrict f _ h1 h2⟩
  -- the semi-stable stage
  have hpair' : IsSemistablePair (f ≫ φ)
      (Curves.genericMarksClosure f φ D (genericPoint (Spec (.of W)))) := by
    rw [← hmarks, hfφ]
    exact hpair
  have hfproj : IsProjectiveOver (f ≫ φ) := by
    rw [hfφ]
    exact hXproj
  refine ⟨X, β ≫ b, BlowDown.isSemistableStage_of_isSmoothAt_generic φ D f hη hpair' hfproj
    fun y hy ↦ ?_⟩
  have hy' : (β ≫ b ≫ h ≫ φ) y = genericPoint (Spec (.of W)) := by
    rw [genericPoint_eq_bot_of_affine, ← hfφ]
    exact PrimeSpectrum.ext hy
  rw [hfφ]
  exact hsmgen y hy'

/-- **A stable modification dominated by a semi-stable stage dominating a projective
modification, unconditionally** (Temkin, Proposition 4.5.1 existence, with Proposition 4.4.6,
T:3188–3229, for the blow-down; `PLAN-T5.md` §2.2 steps 1–10): lane T45E's
`ExistenceVal.exists_stableModification_comp` without the hypotheses `ProjectiveSeparation W` and
`ClosureComponentLocal`. In the situation of `exists_isSemistableStage_comp` there are a
semi-stable stage `g ≫ h : X → C` through `h` and a semi-stable stage `β : Y → C` which is a stable
and numerically stable modification of `(C, D)`, with a morphism `c : X → Y` over `C` (the
blow-down). -/
theorem exists_stableModification_comp
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (IsLocalRing.ResidueField W) p)
    {C : Scheme.{u}} (φ : C ⟶ Spec (.of W)) (D : C.IdealSheafData)
    (hV : Global.IsValuationCurve φ D) {C' : Scheme.{u}} (h : C' ⟶ C) [IsModification h]
    (hC' : IsProjectiveOver (h ≫ φ)) :
    ∃ (X : Scheme.{u}) (g : X ⟶ C') (Y : Scheme.{u}) (β : Y ⟶ C) (c : X ⟶ Y),
      c ≫ β = g ≫ h ∧ BlowDown.IsSemistableStage φ D (g ≫ h) ∧
        BlowDown.IsSemistableStage φ D β ∧
        Curves.IsStableModification β φ D
          (Curves.genericMarksClosure β φ D (genericPoint (Spec (.of W)))) ∧
        Global.IsNumericallyStable β φ
          (Curves.genericMarksClosure β φ D (genericPoint (Spec (.of W)))) := by
  have := hV.isIntegral
  have := hV.flat
  have := hV.locallyOfFinitePresentation
  have hC := hV.isProjectiveOver
  have : IsProper φ := hC.isProper
  have htr := ExistenceVal.fiberTrdeg_genericPoint_eq_one φ hV.genericPair.nodal
  have halg : ∀ t : PrimeSpectrum W, IsAlgClosed t.asIdeal.ResidueField := fun t ↦
    BlowDown.NoClosedExc.isAlgClosed_residueField_of_isAlgClosed K t
  have hsep : ∀ P : PrimeSpectrum W, IsSepClosed (FractionRing (W ⧸ P.asIdeal)) := fun P ↦
    Cohomology.Connected.isSepClosed_fractionRing_quotient K P
  obtain ⟨X, g, hstage⟩ := exists_isSemistableStage_comp hchar φ D hV h hC'
  obtain ⟨Y, β, c, hc, hstage', hstable, hnum⟩ :=
    BlowDown.UnconditionalFinal.exists_isStableModification_of_isSemistableStage_of_isProjectiveOver
      φ D hC hsep halg htr.le X (g ≫ h) hstage
  exact ⟨X, g, Y, β, c, hc, hstage, hstage', hstable, fun K' _ _ a ↦ hnum K' a⟩

/-- **Existence of a stable modification over a valuation ring, unconditionally** (Temkin,
Proposition 4.5.1 `sepclosprop`, T:3233–3266, existence, with Thm 1.1 over `W`; `PLAN-T5.md` §2.2
steps 1–10, nodes V1, V2). Let `K` be algebraically closed, `W ⊆ K` a valuation ring of finite
height and equal characteristic, and `(φ : C → Spec W, D)` a curve in the situation of Temkin's
§4.5 (`Global.IsValuationCurve`). Then `(C, D)` has a stable, numerically stable η-modification
projective over `W` (`exists_stableModification_comp` with `h = 𝟙`). -/
theorem exists_stableModification
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (IsLocalRing.ResidueField W) p)
    {C : Scheme.{u}} (φ : C ⟶ Spec (.of W)) (D : C.IdealSheafData)
    (hV : Global.IsValuationCurve φ D) :
    ∃ (C' : Scheme.{u}) (β : C' ⟶ C) (D' : C'.IdealSheafData),
      Curves.IsStableModification β φ D D' ∧ Global.IsNumericallyStable β φ D' ∧
        IsProjectiveOver (β ≫ φ) := by
  have := hV.isIntegral
  obtain ⟨-, -, Y, β, -, -, -, hstage, hstable, hnum⟩ :=
    exists_stableModification_comp hchar φ D hV (𝟙 C)
      (by rw [Category.id_comp]; exact hV.isProjectiveOver)
  exact ⟨Y, β, _, hstable, hnum, hstage.isProjectiveOver⟩

end Main

section Statement

/-- **`Global.ValuationStableExistence` holds** (Temkin, Proposition 4.5.1, existence;
`PLAN-T5.md` §1.3, node V2): over a valuation ring of finite height and equal characteristic
whose fraction field is algebraically closed, every curve in the situation of Temkin's §4.5 has a
stable, numerically stable η-modification projective over the valuation ring. -/
theorem valuationStableExistence : Global.ValuationStableExistence.{u} := by
  intro K _ _ W _ hchar C φ D hV
  exact exists_stableModification hchar φ D hV

end Statement

end DeJongAlterations.StableModification.Gluing.ExistenceValFinal
