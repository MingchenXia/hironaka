import DeJongAlterations.StableModification.DeJong.FibrationModel

/-!
# The Temkin-ready curve fibration (weak de Jong 4.11–4.12)

This file proves the producer proposition `TemkinReadyFibration k` of `Interface.lean`
(blueprint chapter `sm-dj-fibration`, `thm:sm-dj-temkin-ready-fibration`; de Jong, *Smoothness,
semi-stability and alterations*, 1996, 4.11–4.12, `dejong96-alterations:page-0018`–`page-0020`)
over an algebraically closed field:

* `PurelyInseparableSmoothing k`: the purely inseparable base change step (plan node `PL`,
  blueprint `thm:sm-dj-perfection-global`), the only place where the characteristic matters. It
  replaces de Jong's Bertini argument 4.11 (ii) d) and is stated here as a plain proposition;
  nothing in this file assumes it.
* `purelyInseparableSmoothing_of_charZero`: in characteristic zero it holds with no base change.
* `temkinReadyFibration_of_purelyInseparableSmoothing`: `PurelyInseparableSmoothing k` implies
  `TemkinReadyFibration k`. Proof: the normal curve fibration `f : X' ⟶ Y` of
  `exists_normal_curve_fibration` (separating transcendence basis, graph model, normalization,
  Stein factor), the smoothing step for `W = φ⁻¹(Supp D)`, and the split of the boundary into its
  horizontal part `W^h` (closure of the generic fibre of `W`, reduced; étale over `κ(η)`) and a
  vertical part lying over a proper closed `T ⊊ Y` (`FibrationGeneric.lean`).
* `temkinReadyFibration_of_charZero`: `TemkinReadyFibration k` in characteristic zero.

Only generic properties of the fibration are produced: de Jong's conditions on all fibres
(4.11 (ii) a), b), 4.12 (vi) a), b)) are not needed once Temkin's theorem replaces 4.13–4.21.
The alteration `X' ⟶ X` is a modification in characteristic zero; in characteristic `p` the
smoothing step makes it purely inseparable over a modification, hence not generically étale.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.DeJong

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Geometry

variable (k : Type u) [Field k]

/-- **PL, global form** (PLAN-DJ-MAIN §4, node `PL`; the lane `StableModification/Perfection`).
Let `f : X ⟶ Y` be a proper dominant morphism of normal projective varieties over the
algebraically closed field `k` whose generic fibre is geometrically integral of dimension one,
and let `W ⊊ X` be closed. Then there are alterations `φ : X₁ ⟶ X` and `ψ : Y₁ ⟶ Y` with `X₁`,
`Y₁` projective varieties, `Y₁` normal, and a dominant `f₁ : X₁ ⟶ Y₁` over `f`, whose generic
fibre is smooth and geometrically integral, and such that the points of that generic fibre lying
over `W` have separable residue fields.

In characteristic `p > 0` one takes `Y₁` the normalization of `Y` in `K(Y)^{1/p^m}` and `X₁` the
normalization of `X` in `K(X) ⊗_{K(Y)} K(Y)^{1/p^m}` for `m ≫ 0`; this is the only step of the
fibration where the characteristic matters. In characteristic zero it holds with `m = 0`
(`purelyInseparableSmoothing_of_charZero`). -/
def PurelyInseparableSmoothing [IsAlgClosed k] : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (_ : IsVariety p), IsProjectiveOver p →
    IsNormalScheme X →
  ∀ (Y : Scheme.{u}) (pY : Y ⟶ Spec (.of k)) (_ : IsVariety pY), IsProjectiveOver pY →
    IsNormalScheme Y →
  ∀ f : X ⟶ Y, f ≫ pY = p → IsDominant f → IsProper f →
    GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint Y)) →
    topologicalKrullDim (f.fiber (genericPoint Y)) = 1 →
  ∀ W : Closeds X, genericPoint X ∉ W →
    ∃ (X₁ : Scheme.{u}) (φ : X₁ ⟶ X) (_ : IsVariety (φ ≫ p)) (Y₁ : Scheme.{u}) (ψ : Y₁ ⟶ Y)
      (_ : IsVariety (ψ ≫ pY)) (f₁ : X₁ ⟶ Y₁),
      IsAlteration φ ∧ IsProjectiveOver (φ ≫ p) ∧
      IsAlteration ψ ∧ IsNormalScheme Y₁ ∧ IsProjectiveOver (ψ ≫ pY) ∧
      f₁ ≫ ψ = φ ≫ f ∧ IsDominant f₁ ∧
      Smooth (f₁.fiberToSpecResidueField (genericPoint Y₁)) ∧
      GeometricallyIntegral (f₁.fiberToSpecResidueField (genericPoint Y₁)) ∧
      SeparableResidueFieldsAlong f₁ (genericPoint Y₁) (φ ⁻¹' (W : Set X))

variable {k}

/-- **PL in characteristic zero**: no base change is needed. The generic fibre of a morphism
from a normal variety is a normal, hence regular, curve over a field of characteristic zero,
hence smooth; closed points of curves have finite, hence separable, residue fields. -/
theorem purelyInseparableSmoothing_of_charZero [IsAlgClosed k] [CharZero k] :
    PurelyInseparableSmoothing k := by
  intro X p hpv hp hXn Y pY hYv hYp hYn f hfac hfdom hfprop hgi hdimf W hW
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ pY) := by rw [hfac]; infer_instance
    exact locallyOfFiniteType_of_comp f pY
  have hX1 : IsVariety (𝟙 X ≫ p) := by rw [Category.id_comp]; exact hpv
  have hY1 : IsVariety (𝟙 Y ≫ pY) := by rw [Category.id_comp]; exact hYv
  refine ⟨X, 𝟙 X, hX1, Y, 𝟙 Y, hY1, f, isAlteration_id X,
    by rw [Category.id_comp]; exact hp, isAlteration_id Y, hYn,
    by rw [Category.id_comp]; exact hYp, by rw [Category.comp_id, Category.id_comp], hfdom,
    smooth_genericFiber_of_charZero pY f hXn hdimf.le, hgi, ?_⟩
  have h := separableResidueFieldsAlong_of_charZero pY f hdimf.le W hW
  exact h

/-- **FIB** (`TemkinReadyFibration k`, generic part of de Jong 4.11–4.12) from the purely
inseparable smoothing step `PurelyInseparableSmoothing k`. -/
theorem temkinReadyFibration_of_purelyInseparableSmoothing [IsAlgClosed k]
    (hPL : PurelyInseparableSmoothing k) : TemkinReadyFibration k := by
  intro d hd X p hpv hp _ hdim D _ hDtop
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨X₂, φ₂, Y, pY, hYv, f₂, hφ₂, hX₂v, hX₂p, hX₂n, hYp, hYn, hYdim, hfac₂, hf₂dom,
    hf₂prop, hgi₂, hfd₂⟩ := exists_normal_curve_fibration p hp n hdim
  let W₂ : Closeds X₂ := D.support.preimage φ₂.continuous
  have hW₂ : genericPoint X₂ ∉ W₂ := by
    intro h
    change φ₂ (genericPoint X₂) ∈ (D.support : Set X) at h
    rw [genericPoint_map_of_isDominant φ₂] at h
    exact CurveBoundary.genericPoint_not_mem D.support hDtop h
  obtain ⟨X₃, φ₃, hX₃v, Y₃, ψ, hY₃v, f₃, hφ₃, hX₃p, hψ, hY₃n, hY₃p, hfac₃, hf₃dom, hsm, hgi,
    hsepW⟩ := hPL X₂ (φ₂ ≫ p) hX₂v hX₂p hX₂n Y pY hYv hYp hYn f₂ hfac₂ hf₂dom hf₂prop hgi₂ hfd₂
      W₂ hW₂
  have : LocallyOfFiniteType f₃ := by
    have : LocallyOfFiniteType (f₃ ≫ ψ ≫ pY) := by
      rw [← Category.assoc, hfac₃, Category.assoc, hfac₂]
      infer_instance
    exact locallyOfFiniteType_of_comp f₃ (ψ ≫ pY)
  have hdimX₃ : topologicalKrullDim X₃ = (n + 1 : ℕ) := by
    rw [topologicalKrullDim_eq_of_isAlteration (φ₂ ≫ p) φ₃,
      topologicalKrullDim_eq_of_isAlteration p φ₂, hdim]
  have hdimY₃ : topologicalKrullDim Y₃ = n := by
    rw [topologicalKrullDim_eq_of_isAlteration pY ψ, hYdim]
  have hfd₃ : topologicalKrullDim (f₃.fiber (genericPoint Y₃)) = 1 := by
    have := topologicalKrullDim_genericFiber_eq f₃ (ψ ≫ pY) n 1 hdimX₃ hdimY₃
    exact_mod_cast this
  let W₃ : Closeds X₃ := W₂.preimage φ₃.continuous
  have hW₃ : genericPoint X₃ ∉ W₃ := by
    intro h
    change φ₃ (genericPoint X₃) ∈ (W₂ : Set X₂) at h
    rw [genericPoint_map_of_isDominant φ₃] at h
    exact hW₂ h
  have : AlgebraicGeometry.IsNoetherian X₃ :=
    ProjectiveCurveFibration.variety_isNoetherian (φ₃ ≫ φ₂ ≫ p)
  obtain ⟨T, hT, hcover⟩ := exists_closeds_ne_top_subset_horizontalPart_union f₃ W₃
  have hpair := isSemistablePair_genericFiber f₃ hfd₃ W₃ hW₃ hsepW
  have : IsAlteration φ₂ := inferInstance
  refine ⟨X₃, φ₃ ≫ φ₂, Y₃, ψ ≫ pY, hY₃v, f₃, horizontalIdeal f₃ W₃, T,
    IsAlteration.comp φ₃ φ₂, by simpa only [Category.assoc] using hX₃p, hY₃n, hY₃p,
    by simpa using hdimY₃, ?_, hf₃dom, hsm, hgi, hpair, ?_, hT, ?_⟩
  · rw [← Category.assoc, hfac₃, Category.assoc, hfac₂, Category.assoc]
  · rw [support_horizontalIdeal]
    exact horizontalPart_le f₃ W₃
  · exact hcover

/-- **FIB in characteristic zero** (`TemkinReadyFibration k` outright). -/
theorem temkinReadyFibration_of_charZero [IsAlgClosed k] [CharZero k] :
    TemkinReadyFibration k :=
  temkinReadyFibration_of_purelyInseparableSmoothing purelyInseparableSmoothing_of_charZero

end DeJongAlterations.StableModification.DeJong
