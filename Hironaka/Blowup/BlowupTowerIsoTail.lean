/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupBiholomorphismLift
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Invariant.ContactIndependenceAlong
import Hironaka.Blowup.GlueingTrivialAction
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingAlongTower
import Hironaka.MarkedIdeal.HomogenizedGlueingLiftAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Isomorphisms of towers along concatenations, and the glueing lifts along the tail of a segment

The *tail* form of `BlowupTowerIsomorphism.exists_isTowerIso_coeffHom`, which Step 1b of `hir:maximal-order-step`
needs to show that its value "does not depend on `w`". Step 1b forms the marked ideal `𝓢_w` at the stage `T₀` where
it starts and evaluates the inductive invariant along the *tail* `T₁` of the segment `T₀ T₁`; property (6) of
`hir:centre-function` (`hir:tower-isomorphism` form) is then applied over the lift `Φ_{T₀}` of the glueing
biholomorphism, to an isomorphism of the restricted tails. The restriction `(T₀ T₁)|_U` is not definitionally
`T₀|_U` followed by `T₁|_{T₀⁻¹U}` (the stages agree only propositionally), so the tail isomorphism is built
directly. Source: Włodarczyk 2005 (arXiv `hiron.tex`), Step 1bb (the induced towers `φ^*(X_i)`, defined up to
isomorphism, and `φ_{pu}^*(..) = φ_{pv}^*(..)` along the part of the resolution after the hypersurface of maximal
contact is chosen).

## Isomorphisms of towers

* `opensCongr`: the biholomorphism between equal open sets (the identity on points).
* `IsTowerIso.refl_self`, `IsTowerIso.symm`, `IsTowerIso.step_inv`, `IsTowerIso.refl_inv`, `IsTowerIso.trans`,
  `IsTowerIso.append` (declared in the namespace `BlowupTowerIsomorphism` of `IsTowerIso`, so that dot notation applies):
  identities, inverses, composites and concatenations of isomorphisms of towers are isomorphisms of towers.
* `openPreimage_append`: `T₁⁻¹(T₀⁻¹U) = (T₀ T₁)⁻¹U`; `isTowerIso_restrict_append`: `(T₀ T₁)|_U` is isomorphic over
  `id_U` to `T₀|_U` followed by `T₁|_{T₀⁻¹U}`, with last-stage map the identity on points.

## The glueing lifts along the tail

* `exists_isGlueingLiftAlong_tail`: given a lift `Φ₀` along `T₀` which is the last-stage map of an isomorphism
  `T₀|_{U'} ≅ T₀|_U` over the glueing biholomorphism, along every `T₁` with `T₀ T₁` a multiple test blow-up of `(𝓗_N(𝔞), μ)`
  (and of a family of preserved marked ideals) there are a lift `Φ` along `T₀ T₁` (with the isomorphism of the whole
  restricted towers and the family transported) and an isomorphism `χ : T₁|_{T₀⁻¹U'} ≅ T₁|_{T₀⁻¹U}` over `Φ₀` which agrees
  with `Φ` pointwise.
* `exists_isTowerIso_tail_coeffHom`: for `J̄ = 𝓒_N(𝓗_N(𝔞), μ)` and `T₀ T₁` a multiple test blow-up of `J̄`: the lift
  `Φ₀` along `T₀` (head isomorphism over the glueing biholomorphism) and the tail isomorphism `χ` over `Φ₀`, which
  fixes `cosupp J̄_{T₀ T₁}` pointwise.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupTowerIsomorphism

open Hironaka.BlowupSequences BlowupTowers

noncomputable section

variable {n : ℕ}

/-! ### Identities, inverses, composites and concatenations -/

section Algebra

variable {X X' : CMfd.{u} n}

/-- **The identity is an isomorphism of a tower with itself.** -/
theorem IsTowerIso.refl_self : {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞) T T (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) Y ∞)
  | _, .refl => IsTowerIso.refl
  | _, .step T _ _ hπ => IsTowerIso.step (IsTowerIso.refl_self T) hπ hπ _ (fun _ => rfl) rfl

/-- **The inverse of an isomorphism of towers** is an isomorphism over the inverse biholomorphism. -/
theorem IsTowerIso.symm {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X} {Y' Y : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y} {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (h : IsTowerIso Φ T' T χ) : IsTowerIso Φ.symm T T' χ.symm := by
  induction h with
  | refl => exact IsTowerIso.refl
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    refine IsTowerIso.step ih hπ hπ' χ₁.symm (fun p => ?_) ?_
    · have h1 := hcomm (χ₁.symm p)
      rw [Diffeomorph.apply_symm_apply] at h1
      rw [h1, Diffeomorph.symm_apply_apply]
    · rw [← hC, ← preimage_comp]
      ext y
      simp

/-- **Inversion of the step constructor**: an isomorphism of two towers ending with a blowup comes from an isomorphism of
the shorter towers whose last-stage map is covered by the new one and preserves the centres. -/
theorem IsTowerIso.step_inv {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X} {Y' Y Z' Z : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y} {C' : Set Y'} {π' : Z' → Y'} {hπ' : IsBlowupAlong n C' π'}
    {C : Set Y} {π : Z → Y} {hπ : IsBlowupAlong n C π}
    {χ₁ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z}
    (h : IsTowerIso Φ (.step T' C' π' hπ') (.step T C π hπ) χ₁) :
    ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y,
      IsTowerIso Φ T' T χ ∧ (∀ p, π (χ₁ p) = χ (π' p)) ∧ χ ⁻¹' C = C' := by
  cases h with
  | step h _ _ _ hcomm hC => exact ⟨_, h, hcomm, hC⟩

/-- **Isomorphisms of the empty towers** have the base biholomorphism as last-stage map. -/
theorem IsTowerIso.refl_inv {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {χ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X} (h : IsTowerIso Φ .refl .refl χ) : χ = Φ := by
  cases h
  rfl

/-- **The composite of isomorphisms of towers** is an isomorphism over the composite biholomorphism. -/
theorem IsTowerIso.trans {X'' : CMfd.{u} n} {Φ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X'}
    {Ψ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X} {Y'' Y' Y : CMfd.{u} n}
    {T'' : BlowupTower X'' Y''} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ' : Y'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y'}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (h₁ : IsTowerIso Φ T'' T' χ') (h₂ : IsTowerIso Ψ T' T χ) : IsTowerIso (Φ.trans Ψ) T'' T (χ'.trans χ) := by
  induction h₁ generalizing Y with
  | refl =>
    cases T with
    | refl =>
      obtain rfl := h₂.refl_inv
      exact IsTowerIso.refl
    | step T C π hπ => exact absurd h₂.length_eq (by simp)
  | @step Y'' Y' Z'' Z' T'' T' χ' h C'' π'' hπ'' C' π' hπ' χ₁ hcomm hC ih =>
    cases T with
    | refl => exact absurd h₂.length_eq (by simp)
    | step T C π hπ =>
      obtain ⟨χ₀, h₀, hcomm₀, hC₀⟩ := h₂.step_inv
      refine IsTowerIso.step (ih h₀) hπ'' hπ (χ₁.trans χ) (fun p => ?_) ?_
      · simp only [Diffeomorph.coe_trans, Function.comp_apply]
        rw [hcomm₀, hcomm]
      · rw [Diffeomorph.coe_trans, preimage_comp, hC₀, hC]

/-- **Concatenation of isomorphisms of towers**: an isomorphism `T'₀ ≅ T₀` over `Φ` with last-stage map `χ₀`, followed by
an isomorphism `T'₁ ≅ T₁` over `χ₀`, is an isomorphism `T'₀ T'₁ ≅ T₀ T₁` over `Φ`. -/
theorem IsTowerIso.append {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X} {Y'₀ Y₀ : CMfd.{u} n}
    {T'₀ : BlowupTower X' Y'₀} {T₀ : BlowupTower X Y₀}
    {χ₀ : Y'₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₀} (h₀ : IsTowerIso Φ T'₀ T₀ χ₀)
    {Z' Z : CMfd.{u} n} {T'₁ : BlowupTower Y'₀ Z'} {T₁ : BlowupTower Y₀ Z}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z} (h₁ : IsTowerIso χ₀ T'₁ T₁ χ) :
    IsTowerIso Φ (T'₀.append T'₁) (T₀.append T₁) χ := by
  induction h₁ with
  | refl => exact h₀
  | step _ hπ' hπ χ₁ hcomm hC ih => exact IsTowerIso.step ih hπ' hπ χ₁ hcomm hC

end Algebra

end

end Hironaka.BlowupTowerIsomorphism

namespace Hironaka.BlowupTowerIsoTail

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupStrictSubmanifold HomogenizedIdealAlong CoefficientIdealRestriction TangentDirectionAlong BlowupTowerIsomorphism BlowupRestrictOpen
open HomogenizedGlueingTower (strictAlong)

noncomputable section

variable {n : ℕ}

/-! ### Equal open sets -/

section OpensCongr

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **The biholomorphism between equal open sets**, the identity on points. -/
def opensCongr {A B : Opens Y} (h : A = B) :
    CMfd.of (n := n) A ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) B where
  toFun p := ⟨p.1, h ▸ p.2⟩
  invFun q := ⟨q.1, h ▸ q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_opens_mk contMDiff_subtype_val _
  contMDiff_invFun := contMDiff_opens_mk contMDiff_subtype_val _

@[simp] theorem coe_opensCongr_apply {A B : Opens Y} (h : A = B) (p : A) :
    ((opensCongr (n := n) h p : B) : Y) = p := rfl

@[simp] theorem coe_opensCongr_symm_apply {A B : Opens Y} (h : A = B) (q : B) :
    (((opensCongr (n := n) h).symm q : A) : Y) = q := rfl

end OpensCongr

/-! ### Restriction of a concatenation -/

section RestrictAppend

variable {X Y : CMfd.{u} n}

/-- **The open preimage along a concatenation**: `T₁⁻¹(T₀⁻¹U) = (T₀ T₁)⁻¹U`. -/
theorem openPreimage_append (T₀ : BlowupTower X Y) {Z : CMfd.{u} n} (T₁ : BlowupTower Y Z) (U : Opens X) :
    openPreimage T₁ (openPreimage T₀ U) = openPreimage (T₀.append T₁) U := by
  ext p
  show T₀.proj (T₁.proj p) ∈ U ↔ (T₀.append T₁).proj p ∈ U
  rw [BlowupTower.proj_append]
  rfl

/-- **The restriction of a concatenation is the concatenation of the restrictions, up to isomorphism**: `(T₀ T₁)|_U` is
isomorphic over `id_U` to `T₀|_U` followed by `T₁|_{T₀⁻¹U}`, with last-stage map the identity on points
(`opensCongr`). -/
theorem isTowerIso_restrict_append (U : Opens X) (T₀ : BlowupTower X Y) :
    {Z : CMfd.{u} n} → (T₁ : BlowupTower Y Z) →
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) (restrict U (T₀.append T₁))
        ((restrict U T₀).append (restrict (openPreimage T₀ U) T₁)) (opensCongr (openPreimage_append T₀ T₁ U).symm)
  | _, .refl => by
      have : (opensCongr (n := n) (openPreimage_append T₀ (BlowupTower.refl : BlowupTower Y Y) U).symm) =
          Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) (openPreimage T₀ U)) ∞ :=
        Diffeomorph.ext fun _ => rfl
      rw [this]
      exact IsTowerIso.refl_self (restrict U T₀)
  | _, .step T₁ _ _ hπ =>
      IsTowerIso.step (isTowerIso_restrict_append U T₀ T₁) _ _ _ (fun _ => rfl) rfl

end RestrictAppend

/-! ### The glueing lifts along the tail of a segment -/

section Glueing

open HomogenizedGlueingAlong HomogenizedGlueingAlongTower HomogenizedGlueingLiftAlong GlueingTrivialAction ContactIndependenceAlong BlowupBiholomorphismLift

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ} (G : GlueingDataAlong N 𝔞 μ u v)

/-- **The glueing lifts along the tail of a segment**: let `Φ₀` be a lift of the glueing biholomorphism along `T₀`
(`IsGlueingLiftAlong`) which is the last-stage map of an isomorphism `T₀|_{U'} ≅ T₀|_U` over `G.equiv` and transports a
family of pairs `(𝔫 i)_{T₀}`, `(𝔫' i)_{T₀}`.  Along every `T₁` such that `T₀ T₁` is a multiple test blow-up of
`(𝓗_N(𝔞), μ)` and of every `𝔫 i`, `𝔫' i` there are a lift `Φ` along `T₀ T₁`, the last-stage map of an isomorphism
`(T₀ T₁)|_{U'} ≅ (T₀ T₁)|_U` over `G.equiv` transporting every `(𝔫 i)_{T₀ T₁}`, and an isomorphism of the restricted
tails `T₁|_{T₀⁻¹U'} ≅ T₁|_{T₀⁻¹U}` over `Φ₀` whose last-stage map `χ` agrees with `Φ` pointwise. -/
theorem exists_isGlueingLiftAlong_tail (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    {ι : Sort*} (𝔫 𝔫' : ι → MarkedIdeal n M) (hN𝔫 : ∀ i, IsClosedSubmanifold n (𝔫 i).N)
    (h𝔫 : ∀ i, (𝔫 i).ideal.IsCoherent) (hN𝔫' : ∀ i, IsClosedSubmanifold n (𝔫' i).N)
    (h𝔫' : ∀ i, (𝔫' i).ideal.IsCoherent) {Y : CMfd.{u} n} (T₀ : BlowupTower (CMfd.of (n := n) M) Y)
    {Φ₀ : CMfd.of (n := n) (openPreimage T₀ G.dom) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T₀ G.cod)} (hL₀ : IsGlueingLiftAlong G T₀ Φ₀)
    (hI₀ : IsTowerIso G.equiv (restrict G.dom T₀) (restrict G.cod T₀) Φ₀)
    (hP₀ : ∀ i, MarkedIdeal.pullback Φ₀ (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ G.cod → Y)
        (geoTransformAlong (𝔫 i) T₀)) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T₀ G.dom → Y) (geoTransformAlong (𝔫' i) T₀)) :
    {Z : CMfd.{u} n} → (T₁ : BlowupTower Y Z) →
      IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) (T₀.append T₁) → (∀ i, IsGeoTestTower (𝔫 i) (T₀.append T₁)) →
      (∀ i, IsGeoTestTower (𝔫' i) (T₀.append T₁)) →
      ∃ (Φ : CMfd.of (n := n) (openPreimage (T₀.append T₁) G.dom) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage (T₀.append T₁) G.cod))
        (χ : CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ G.dom))
          ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ G.cod))),
        IsGlueingLiftAlong G (T₀.append T₁) Φ ∧
        IsTowerIso G.equiv (restrict G.dom (T₀.append T₁)) (restrict G.cod (T₀.append T₁)) Φ ∧
        IsTowerIso Φ₀ (restrict (openPreimage T₀ G.dom) T₁) (restrict (openPreimage T₀ G.cod) T₁) χ ∧
        (∀ (p : openPreimage T₁ (openPreimage T₀ G.dom)) (q : openPreimage (T₀.append T₁) G.dom),
          (p : Z) = q → (χ p : Z) = Φ q) ∧
        ∀ i, MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : openPreimage (T₀.append T₁) G.cod → Z)
            (geoTransformAlong (𝔫 i) (T₀.append T₁))) =
          MarkedIdeal.pullback (Subtype.val : openPreimage (T₀.append T₁) G.dom → Z)
            (geoTransformAlong (𝔫' i) (T₀.append T₁))
  | _, .refl, _, _, _ => by
      refine ⟨Φ₀, Φ₀, hL₀, hI₀, IsTowerIso.refl, fun p q hpq => ?_, hP₀⟩
      have hpq' : p = q := Subtype.ext hpq
      rw [hpq']
      rfl
  | _, .step T₁ C π hπ, hT, h𝔫T, h𝔫'T => by
      obtain ⟨Φ, χ, hL, hI, hχ, hpt, hP⟩ := exists_isGlueingLiftAlong_tail h𝔞 hN hμ 𝔫 𝔫' hN𝔫 h𝔫 hN𝔫' h𝔫' T₀ hL₀
        hI₀ hP₀ T₁ hT.1 (fun i => (h𝔫T i).1) (fun i => (h𝔫'T i).1)
      obtain ⟨hcorr, Φ₁, hΦ₁, hL₁⟩ := exists_isGlueingLiftAlong_step G h𝔞 hN hμ (T₀.append T₁) C π hπ hT hL
      have hd : preOpen hπ (openPreimage T₁ (openPreimage T₀ G.dom)) =
          preOpen hπ (openPreimage (T₀.append T₁) G.dom) :=
        congrArg (preOpen hπ) (openPreimage_append T₀ T₁ G.dom)
      have hc : preOpen hπ (openPreimage T₁ (openPreimage T₀ G.cod)) =
          preOpen hπ (openPreimage (T₀.append T₁) G.cod) :=
        congrArg (preOpen hπ) (openPreimage_append T₀ T₁ G.cod)
      have hpt' : ∀ (p : openPreimage T₁ (openPreimage T₀ G.dom)),
          Subtype.val (χ p) = Subtype.val (Φ (opensCongr (openPreimage_append T₀ T₁ G.dom) p)) := fun p =>
        hpt p (opensCongr (openPreimage_append T₀ T₁ G.dom) p) rfl
      refine ⟨Φ₁, (opensCongr hd).trans (Φ₁.trans (opensCongr hc).symm), hL₁,
        IsTowerIso.step hI _ _ Φ₁ (fun p => Subtype.ext (hΦ₁ p)) hcorr,
        IsTowerIso.step hχ _ _ _ (fun p => Subtype.ext ?_) ?_, fun p q hpq => ?_, fun i => ?_⟩
      · show π (Φ₁ (opensCongr hd p) : _) = _
        rw [hΦ₁, hpt']
        rfl
      · ext p
        show Subtype.val (χ p) ∈ C ↔ Subtype.val p ∈ C
        rw [hpt' p]
        exact Iff.of_eq (congrArg (fun S => opensCongr (openPreimage_append T₀ T₁ G.dom) p ∈ S) hcorr)
      · show Subtype.val (Φ₁ (opensCongr hd p)) = _
        have hq : opensCongr (n := n) hd p = q := Subtype.ext hpq
        rw [hq]
        rfl
      · obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong (hN𝔫 i) (h𝔫 i) (T₀.append T₁)
          (h𝔫T i).1
        obtain ⟨hNT', hcT'⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong (hN𝔫' i) (h𝔫' i)
          (T₀.append T₁) (h𝔫'T i).1
        exact pullback_lift_geoTransform_pair hπ Φ hcorr Φ₁ hΦ₁ hcT
          (HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNT hcT (h𝔫T i).2 hπ) hcT'
          (HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNT' hcT' (h𝔫'T i).2 hπ) (hP i)

/-- **The lifts along the tail of a segment, for `J̄ = 𝓒_N(𝓗_N(𝔞), μ)`** (Step 1b of `hir:maximal-order-step` with
`hir:tower-isomorphism`, its "does not depend on `w`" step): for glueing data `G` along `N` acting trivially modulo the glue
ideal and towers `T₀`, `T₁` with `T₀ T₁` a multiple test blow-up of `J̄`, there are a lift `Φ₀` of the glueing
biholomorphism along `T₀`, the last-stage map of an isomorphism `T₀|_{U'} ≅ T₀|_U` over `G.equiv`, and an isomorphism of
the restricted tails `T₁|_{T₀⁻¹U'} ≅ T₁|_{T₀⁻¹U}` over `Φ₀` with last-stage map `χ`, such that `Φ₀` transports `J̄_{T₀}`
and maps the restricted coefficient ideal on `(N ∩ V(u))_{T₀}` to that on `(N ∩ V(v))_{T₀}` (with and without `𝓒`), `Φ₀`
fixes `cosupp J̄_{T₀}` pointwise, and `χ` fixes `cosupp J̄_{T₀ T₁}` pointwise.  Property (6) of `hir:centre-function` over
`Φ₀`, for the marked ideal `S_{u,T₀}|_{T₀⁻¹U}` and the tails, then compares the invariants of `S_{v,T₀}` and `S_{u,T₀}`
along `T₁` at every point of the cosupport. -/
theorem exists_isTowerIso_tail_coeffHom (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    (htriv : ∀ y ∈ G.W, y ∈ zeroSet (glueIdealAlong N 𝔞 μ) →
      TrivialAt G.φ (glueIdealAlong N 𝔞 μ) y ∧ TrivialAt G.ψ (glueIdealAlong N 𝔞 μ) y)
    {Y Z : CMfd.{u} n} (T₀ : BlowupTower (CMfd.of (n := n) M) Y) (T₁ : BlowupTower Y Z)
    (hT : IsGeoTestTower (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) (T₀.append T₁)) :
    ∃ (Φ₀ : CMfd.of (n := n) (openPreimage T₀ G.dom) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage T₀ G.cod))
      (χ : CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ G.dom))
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ G.cod))),
      IsGlueingLiftAlong G T₀ Φ₀ ∧ IsTowerIso G.equiv (restrict G.dom T₀) (restrict G.cod T₀) Φ₀ ∧
      IsTowerIso Φ₀ (restrict (openPreimage T₀ G.dom) T₁) (restrict (openPreimage T₀ G.cod) T₁) χ ∧
      MarkedIdeal.pullback Φ₀ (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ G.cod → Y)
          (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀)) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T₀ G.dom → Y)
          (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀) ∧
      MarkedIdeal.pullback Φ₀ (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ G.cod → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀))
            (strictAlong T₀ (N ∩ {x | u x = 0})))) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T₀ G.dom → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀))
            (strictAlong T₀ (N ∩ {x | v x = 0}))) ∧
      MarkedIdeal.pullback Φ₀ (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ G.cod → Y)
          (withN (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀)
            (strictAlong T₀ (N ∩ {x | u x = 0})))) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T₀ G.dom → Y)
          (withN (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀)
            (strictAlong T₀ (N ∩ {x | v x = 0}))) ∧
      (∀ p : openPreimage T₀ G.dom,
        (p : Y) ∈ (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀).cosupp →
          (Φ₀ p : Y) = p) ∧
      ∀ p : openPreimage T₁ (openPreimage T₀ G.dom),
        (p : Z) ∈ (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) (T₀.append T₁)).cosupp →
          (χ p : Z) = p := by
  have hW := wEquiv_coeffHom h𝔞 hN hμ
  have hT₀ : IsGeoTestTower (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀ :=
    ((isGeoTestTower_append_iff _ T₀ T₁).mp hT).1
  obtain ⟨Φ₀, hL₀, hI₀, hJ₀, hS₀, hR₀, hfix₀⟩ :=
    BlowupTowerIsomorphism.exists_isTowerIso_coeffHom G h𝔞 hN hμ htriv T₀ hT₀
  have hH : IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) (T₀.append T₁) := (hW.2 _).1.mp hT
  obtain ⟨Φ, χ, hL, -, hχ, hpt, -⟩ := exists_isGlueingLiftAlong_tail G h𝔞 hN hμ (ι := Empty) Empty.elim Empty.elim
    (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) T₀ hL₀ hI₀ (fun i => i.elim) T₁ hH
    (fun i => i.elim) (fun i => i.elim)
  refine ⟨Φ₀, χ, hL₀, hI₀, hχ, hJ₀, hS₀, hR₀, hfix₀, fun p hp => ?_⟩
  rw [hpt p (opensCongr (n := n) (openPreimage_append T₀ T₁ G.dom) p) rfl]
  rw [(hW.2 _).2 hT] at hp
  exact hL.apply_eq_of_mem_cosupp G h𝔞 hN hμ hH (opensCongr (n := n) (openPreimage_append T₀ T₁ G.dom) p) hp

end Glueing

end

end Hironaka.BlowupTowerIsoTail
