import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Invariant.StepOneTangentChange

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The companion ideal of the general step along isomorphisms of towers (property (6))

Hironaka phase H2 (TN3), for TN-CLASSICAL's general step (`hir:general-step`); claim I-0977 C-0172 (no objection C-0175).
Blueprint `bcalc:companion-tower-iso` (chapter `blowup-calculus.tex`).  Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`),
Step 2a of Proposition `pr:resol` and the commutativity of the resolution with étale morphisms; Bierstone--Milman 2008
(`bierstone-milman08-functoriality`), Step II.B.

The general step computes the value at a point of order `o ≥ 1` from the companion ideal `𝓞(𝔪_{T₀}, o)` formed at the
start stage `T₀`, restricted to an open set `W` (the mask), along the restricted tail `T₁|_W`.  Property (6) of the general
invariant compares this with the same construction for `Φ^*𝔪` along a tower isomorphic over a biholomorphism `Φ`.  An
isomorphism of towers `T₀'T₁' ≅ T₀T₁` splits as `T₀' ≅ T₀` over `Φ` (last-stage map `χ₀`) and `T₁' ≅ T₁` over `χ₀`
(`BlowupTowerSplitIso.IsTowerIso.exists_split`); with opens `W'`, `W` matched by `χ₀`:

* **`companionOf_isTowerIso`**: `𝓞((Φ^*𝔪)_{T₀'}, o)|_{W'} = ψ^*(𝓞(𝔪_{T₀}, o)|_W)` for every biholomorphism `ψ : W' ≅ W` agreeing
  with `χ₀` (the transform along isomorphic towers, `IsTowerIso.geoTransformAlong_eq`, and `CompanionRebase`);
* `bound_isTowerIso`: the bound `ord ≤ o` on the cosupport over the mask transports;
* `isGeoTestTower_companionOf_isTowerIso`: the restricted tails are multiple test blow-ups of the two companion ideals
  together (`T₁'|_{W'} ≅ T₁|_W`, TN23's `StepOneTangentChange.isTowerIso_restrictOpens`);
* **`inv_companionOf_isTowerIso`**: for a resolution invariant `R` (or any invariant with property (6), through the first
  item), the companion ideals lie in the domain, the restricted tails are canonical segments together, and the values at
  corresponding points of the cosupports agree.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.CompanionTowerIso

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong
  Hironaka.CompanionReductionAlong Hironaka.CompanionRebase
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerIsomorphism Hironaka.StepOneTangentChange
  Hironaka.NonmonomialOrderLocal Hironaka.InvDomainCompanion
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isCanonical_of_isTowerIso)

noncomputable section

variable {n : ℕ}

section Iso

variable {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {𝔪 : MarkedIdeal n X}
  {Y₀' Y₀ : CMfd.{u} n} {T₀' : BlowupTower X' Y₀'} {T₀ : BlowupTower X Y₀}
  {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₀}

/-- **The companion ideal along an isomorphism of towers** (property (6), marked ideals): for `T₀' ≅ T₀` over `Φ : X' ≅ X`
with last-stage map `χ₀`, `T₀` a multiple test blow-up of `𝔪` (in the domain, `n > 0`, `o ≥ 1`), opens `W'`, `W` of the
two last stages and `ψ : W' ≅ W` agreeing with `χ₀`: `𝓞((Φ^*𝔪)_{T₀'}, o)|_{W'} = ψ^*(𝓞(𝔪_{T₀}, o)|_W)`. -/
theorem companionOf_isTowerIso (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) {o : ℕ} (ho : 1 ≤ o)
    (hiso : IsTowerIso Φ T₀' T₀ χ₀) (hT₀ : IsGeoTestTower 𝔪 T₀) (W' : Opens Y₀') (W : Opens Y₀)
    (ψ : CMfd.of (n := n) W' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) W)
    (hψ : ∀ q : W', ((ψ q : W) : Y₀) = χ₀ q) :
    MarkedIdeal.pullback (Subtype.val : W' → Y₀') (companionOf n (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T₀') o) =
      MarkedIdeal.pullback ψ (MarkedIdeal.pullback (Subtype.val : W → Y₀) (companionOf n (geoTransformAlong 𝔪 T₀) o)) := by
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
  have hcoh : (companionOf n (geoTransformAlong 𝔪 T₀) o).ideal.IsCoherent :=
    (isInvDomain_companionAlong hn hdomT ho).isWellFormed.isCoherent
  rw [IsTowerIso.geoTransformAlong_eq Φ h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent hiso hT₀,
    ← pullback_diffeo_companionOf hn χ₀ hdomT.isWellFormed hdomT.isNonzeroAlongAt o]
  exact ContactMarkedCanonical.pullback_pullback_of_comp_eq hcoh χ₀.contMDiff contMDiff_subtype_val ψ.contMDiff
    contMDiff_subtype_val fun q => (hψ q).symm

/-- **The bound on the order transports along an isomorphism of towers**: with `q ∈ W' ↔ χ₀ q ∈ W`, if the order of the
nonmonomial part of `𝔪_{T₀}` is `≤ o` on `cosupp 𝔪_{T₀} ∩ W`, that of `(Φ^*𝔪)_{T₀'}` is `≤ o` on its cosupport over `W'`. -/
theorem bound_isTowerIso (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) (hiso : IsTowerIso Φ T₀' T₀ χ₀)
    (hT₀ : IsGeoTestTower 𝔪 T₀) {o : ℕ} {W' : Opens Y₀'} {W : Opens Y₀} (hW : ∀ q, q ∈ W' ↔ χ₀ q ∈ W)
    (hbound : ∀ x ∈ (geoTransformAlong 𝔪 T₀).cosupp, x ∈ W → x ∉ ordGe (geoTransformAlong 𝔪 T₀) (o + 1)) :
    ∀ x ∈ (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T₀').cosupp, x ∈ W' →
      x ∉ ordGe (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T₀') (o + 1) := by
  intro x hx hxW hxo
  rw [IsTowerIso.cosupp_geoTransformAlong Φ h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent hiso hT₀]
    at hx
  exact hbound (χ₀ x) hx ((hW x).mp hxW) ((mem_ordGe_geoTransformAlong_isTowerIso hn Φ h hiso hT₀ (o + 1) x).mp hxo)

/-- **The restricted tails are multiple test blow-ups of the two companion ideals together**: for `T₁' ≅ T₁` over `χ₀`
and `q ∈ W' ↔ χ₀ q ∈ W`, if `T₁|_W` is a multiple test blow-up of `𝓞(𝔪_{T₀}, o)|_W`, then `T₁'|_{W'}` is one of
`𝓞((Φ^*𝔪)_{T₀'}, o)|_{W'}`. -/
theorem isGeoTestTower_companionOf_isTowerIso (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) {o : ℕ} (ho : 1 ≤ o)
    (hiso : IsTowerIso Φ T₀' T₀ χ₀) (hT₀ : IsGeoTestTower 𝔪 T₀) {W' : Opens Y₀'} {W : Opens Y₀}
    (hW : ∀ q, q ∈ W' ↔ χ₀ q ∈ W) {Z' Z : CMfd.{u} n} {T₁' : BlowupTower Y₀' Z'} {T₁ : BlowupTower Y₀ Z}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z} (hχ : IsTowerIso χ₀ T₁' T₁ χ)
    (hT₁ : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → Y₀) (companionOf n (geoTransformAlong 𝔪 T₀) o))
      (restrict W T₁)) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W' → Y₀')
      (companionOf n (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T₀') o)) (restrict W' T₁') := by
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
  have hξ := isTowerIso_restrictOpens hW hχ (isTowerIso_mem_openPreimage_iff hχ hW)
  rw [companionOf_isTowerIso Φ hn h ho hiso hT₀ W' W (diffeoOpens χ₀ W' W hW) fun _ => rfl]
  have hdomW := isInvDomain_pullback_val_companionAlong hn hdomT W ho
  exact (IsTowerIso.isGeoTestTower_iff (diffeoOpens χ₀ W' W hW) hdomW.isWellFormed.isClosedSubmanifold_N
    hdomW.isWellFormed.isCoherent hξ).mpr hT₁

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **The values of the companion ideal along an isomorphism of towers** (property (6), values): let `T₀' ≅ T₀` over `Φ`
with last-stage map `χ₀` and `T₁' ≅ T₁` over `χ₀` (the split of an isomorphism `T₀'T₁' ≅ T₀T₁`), `T₀` a multiple test
blow-up of `𝔪` (in the domain, `n > 0`, `o ≥ 1`), and `W'`, `W` opens with `q ∈ W' ↔ χ₀ q ∈ W`.  If `T₁|_W` is a canonical
segment of `𝓞₀ = 𝓞(𝔪_{T₀}, o)|_W` for a resolution invariant `R`, then `𝓞₀' = 𝓞((Φ^*𝔪)_{T₀'}, o)|_{W'}` lies in the domain,
`T₁'|_{W'}` is a canonical segment of it, and the values at corresponding points of the cosupports agree. -/
theorem inv_companionOf_isTowerIso (hn : 0 < n) (R : ResolutionInvariant.{u, v} n k Λ) (h : IsInvDomain k 𝔪) {o : ℕ}
    (ho : 1 ≤ o) (hiso : IsTowerIso Φ T₀' T₀ χ₀) (hT₀ : IsGeoTestTower 𝔪 T₀) {W' : Opens Y₀'} {W : Opens Y₀}
    (hW : ∀ q, q ∈ W' ↔ χ₀ q ∈ W) {Z' Z : CMfd.{u} n} {T₁' : BlowupTower Y₀' Z'} {T₁ : BlowupTower Y₀ Z}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z} (hχ : IsTowerIso χ₀ T₁' T₁ χ)
    (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : W → Y₀) (companionOf n (geoTransformAlong 𝔪 T₀) o))
      (R.inv (MarkedIdeal.pullback (Subtype.val : W → Y₀) (companionOf n (geoTransformAlong 𝔪 T₀) o)))
      (restrict W T₁)) :
    IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W' → Y₀')
        (companionOf n (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T₀') o)) ∧
      IsCanonical (MarkedIdeal.pullback (Subtype.val : W' → Y₀')
          (companionOf n (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T₀') o))
        (R.inv (MarkedIdeal.pullback (Subtype.val : W' → Y₀')
          (companionOf n (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T₀') o))) (restrict W' T₁') ∧
      ∀ (p : openPreimage T₁' W') (q : openPreimage T₁ W), (χ p : Z) = q →
        q ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y₀)
          (companionOf n (geoTransformAlong 𝔪 T₀) o)) (restrict W T₁)).cosupp →
        R.inv (MarkedIdeal.pullback (Subtype.val : W' → Y₀')
            (companionOf n (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T₀') o)) (restrict W' T₁') p =
          R.inv (MarkedIdeal.pullback (Subtype.val : W → Y₀) (companionOf n (geoTransformAlong 𝔪 T₀) o))
            (restrict W T₁) q := by
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
  have hdomW := isInvDomain_pullback_val_companionAlong hn hdomT W ho
  have hξ := isTowerIso_restrictOpens hW hχ (isTowerIso_mem_openPreimage_iff hχ hW)
  rw [companionOf_isTowerIso Φ hn h ho hiso hT₀ W' W (diffeoOpens χ₀ W' W hW) fun _ => rfl]
  refine ⟨InvDomainTowerAlong.isInvDomain_pullback _ hdomW, isCanonical_of_isTowerIso R hdomW _ hξ hcan,
    fun p q hpq hq => ?_⟩
  have hpq' : diffeoOpens χ (openPreimage T₁' W') (openPreimage T₁ W) (isTowerIso_mem_openPreimage_iff hχ hW) p = q :=
    Subtype.ext hpq
  have key := R.towerIso _ _ hdomW _ _ _ hξ hcan p (by rw [hpq']; exact hq)
  rw [key, hpq']

end Iso

end

end Hironaka.CompanionTowerIso
