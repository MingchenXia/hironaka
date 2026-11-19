import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.ContactStageTail

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1b's restricted marked ideal along isomorphisms of towers and on restricted towers

Hironaka phase H3 (TN23-ENVELOPES), claimed on I-0981 C-0108 / I-0977 C-0149: the H3 inputs of properties (5) and (6) of
`hir:centre-function` for the Step 1 value function (`hir:maximal-order-step`, `blueprint/src/hironaka.tex`; TN-CLASSICAL's
`StepOneValue.stepOneInv`), Step 1b part.  Blueprint `mc:contact-marked-canonical` (`blueprint/src/maximal-contact.tex`).
Source: Włodarczyk 2005 (arXiv `hiron.tex`), the lemma on the commutativity of the resolution procedure in Step 1 with étale
morphisms (`J̄'_{|V(u)} = φ^*(J̄_{|V(u)})`).

At a point of level `0`, the Step 1 value function evaluates a resolution invariant `R` in dimension `≤ k - 1` on
`𝓢_{u,T₀}|_W = MaximalOrderStepOneB.contactMarked N 𝔞 μ u T₀ W` (the coefficient ideal of `J̄_{T₀}`, `J̄ = 𝓒_N(𝓗_N(𝔞), μ)`,
restricted to the strict transform of `N ∩ V(u)` and to an open `W` of the stage `T₀`), along the restricted tail.  For
property (6) the marked ideal `Φ^*𝔍` along a tower isomorphic to the given one over a biholomorphism `Φ` of the bases is
compared with `𝔍`; for property (5) the restriction `𝔍|_U` along the restricted tower.  This module shows that the
restricted marked ideal of Step 1b is carried along: with the tangent direction `u ∘ Φ` (resp. `u ∘ ι`), the marked ideal
formed for `Φ^*𝔍` (resp. `𝔍|_U`) is the pullback of the one formed for `𝔍`, and the domain, canonical segments and values
of `R` correspond.  (The change from `u ∘ Φ` to the tangent direction the value function chooses for `Φ^*𝔍` is
TN-CLASSICAL's `StepOneTangentChange`.)

## Main results

* `pullback_pullback_of_comp_eq` (generic): pullbacks of a coherent marked ideal along two commuting squares agree;
* `stepOneMarked_pullback`, `stepOneMarked_pullback_val`: `J̄` commutes with biholomorphisms and with restriction to open sets;
  `isTangentDirectionAlong_comp`, `isTangentDirectionAlong_comp_val`: tangent directions pull back;
* **`contactMarked_isTowerIso`** (property (6), marked ideals): for an isomorphism of towers `T₀' ≅ T₀` over `Φ` with last-stage
  map `χ₀` and opens `W'`, `W` of the two stages with a biholomorphism `ψ : W' ≅ W` agreeing with `χ₀`,
  `contactMarked (Φ⁻¹N) (Φ^*𝔞) μ (u ∘ Φ) T₀' W' = ψ^*(contactMarked N 𝔞 μ u T₀ W)`; `contactMarked_isTowerIso_refl` over
  the identity;
* **`inv_contactMarked_isTowerIso`** (property (6), values): along any isomorphism of the restricted tails over `ψ`, the domain
  and the canonical segments pass and the values correspond;
* **`contactMarked_restrict`**, **`inv_contactMarked_restrict`** (property (5)): for `U` open in the base and `W ⊆ T₀⁻¹U`, the
  marked ideal of `𝔍|_U` along `T₀|_U` on `W` (seen inside `T₀⁻¹U`) is the transport of `contactMarked N 𝔞 μ u T₀ W`, and the
  domain, canonical segments, cosupports and values pass from `𝔍` along `T₁|_W` to `𝔍|_U` along `(T₁|_{T₀⁻¹U})|_W`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ContactMarkedCanonical

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  CoefficientIdealRestriction HomogenizedIdealAlong MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  BlowupTowerIsomorphism ResolutionInvariantExt MaxLocusLocal
open HomogenizedGlueingTower (strictAlong)
open HomogenizedGlueingAlongTower (homogenizedMarkedAlong)
open MaximalOrderStepOneB (stepOneMarked contactMarked)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Pullbacks along commuting squares -/

section Generic

variable {P Q R Y : Type u} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  [TopologicalSpace Q] [ChartedSpace (ComplexModel n) Q] [IsComplexManifold n Q]
  [TopologicalSpace R] [ChartedSpace (ComplexModel n) R] [IsComplexManifold n R]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Pullbacks along a commuting square**: for holomorphic `a : P → Y`, `b : Q → P`, `c : Q → R`, `d : R → Y` with
`a ∘ b = d ∘ c` and `𝔫` with coherent ideal, `b^*(a^*𝔫) = c^*(d^*𝔫)`. -/
theorem pullback_pullback_of_comp_eq {𝔫 : MarkedIdeal n Y} (h𝔫 : 𝔫.ideal.IsCoherent) {a : P → Y} {b : Q → P}
    {c : Q → R} {d : R → Y} (ha : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ a)
    (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b)
    (hc : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ c)
    (hd : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ d) (h : ∀ q, a (b q) = d (c q)) :
    MarkedIdeal.pullback b (MarkedIdeal.pullback a 𝔫) = MarkedIdeal.pullback c (MarkedIdeal.pullback d 𝔫) := by
  have hfun : a ∘ b = d ∘ c := funext h
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ rfl
  · show b ⁻¹' (a ⁻¹' 𝔫.N) = c ⁻¹' (d ⁻¹' 𝔫.N)
    rw [← preimage_comp, ← preimage_comp, hfun]
  · show (𝔫.E.map (a ⁻¹' ·)).map (b ⁻¹' ·) = (𝔫.E.map (d ⁻¹' ·)).map (c ⁻¹' ·)
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun S _ => ?_
    show b ⁻¹' (a ⁻¹' S) = c ⁻¹' (d ⁻¹' S)
    rw [← preimage_comp, ← preimage_comp, hfun]
  · show GermIdeal.pullback (m := n) b (GermIdeal.pullback (m := n) a 𝔫.ideal) =
      GermIdeal.pullback (m := n) c (GermIdeal.pullback (m := n) d 𝔫.ideal)
    rw [← GermIdealTotalTransform.pullback_comp ha hb h𝔫, ← GermIdealTotalTransform.pullback_comp hd hc h𝔫, hfun]

end Generic

/-! ### Property (6): isomorphisms of towers -/

section Transport

variable {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {N : Set X}
  {𝔞 : GermIdeal n X} {μ : ℕ}

/-- **`J̄` commutes with biholomorphisms**: `𝓒_{Φ⁻¹N}(𝓗_{Φ⁻¹N}(Φ^*𝔞), μ) = Φ^*𝓒_N(𝓗_N(𝔞), μ)` (`𝔞` coherent, `N` a closed
submanifold, `μ ≥ 1`). -/
theorem stepOneMarked_pullback (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) :
    stepOneMarked (Φ ⁻¹' N) (GermIdeal.pullback (m := n) Φ 𝔞) μ = MarkedIdeal.pullback Φ (stepOneMarked N 𝔞 μ) := by
  have hH : (homogenizedMarkedAlong N 𝔞 μ).ideal.IsCoherent := isCoherent_homogenizedIdealAlong h𝔞 hN μ
  show coeffMarkedAlong (homogenizedMarkedAlong (Φ ⁻¹' N) (GermIdeal.pullback (m := n) Φ 𝔞) μ) =
    MarkedIdeal.pullback Φ (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ))
  rw [pullback_coeffMarkedAlong_of_inverse Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply Φ.symm_apply_apply
    (homogenizedMarkedAlong N 𝔞 μ) hH hN hμ]
  congr 1
  exact (pullback_homMarkedAlong_of_inverse Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply Φ.symm_apply_apply
    (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n X) h𝔞 hN hμ).symm

/-- **Tangent directions pull back by biholomorphisms**: a tangent direction `u` of `(𝔞|_N, μ)` on `U` gives the tangent
direction `u ∘ Φ` of `(Φ^*𝔞|_{Φ⁻¹N}, μ)` on `Φ⁻¹U`. -/
theorem isTangentDirectionAlong_comp (h𝔞 : 𝔞.IsCoherent) {U : Set X} {u : X → ℂ}
    (hu : IsTangentDirectionAlong N 𝔞 μ U u) :
    IsTangentDirectionAlong (Φ ⁻¹' N) (GermIdeal.pullback (m := n) Φ 𝔞) μ (Φ ⁻¹' U) (u ∘ Φ) :=
  ContactEquivalenceAlong.isTangentDirectionAlong_pullback
    (fun y => ⟨_, isLocalInverseAt_of_contMDiff Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply
      Φ.symm_apply_apply y⟩) (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞) hu

variable {Y₀' Y₀ : CMfd.{u} n} {T₀' : BlowupTower X' Y₀'} {T₀ : BlowupTower X Y₀}
  {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₀}

/-- **Step 1b's restricted marked ideal along an isomorphism of towers** (property (6), marked ideals): let `T₀' ≅ T₀` be
an isomorphism of towers over `Φ : X' ≅ X` with last-stage map `χ₀`, `T₀` a multiple test blow-up of
`J̄ = stepOneMarked N 𝔞 μ`, `W'`, `W` opens of the two last stages and `ψ : W' ≅ W` a biholomorphism agreeing with `χ₀`.
Then the marked ideal of Step 1b formed for `Φ^*𝔞` along `T₀'` with the tangent direction `u ∘ Φ` on `W'` is the
`ψ`-pullback of the one formed for `𝔞` along `T₀` with `u` on `W`. -/
theorem contactMarked_isTowerIso (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    (hiso : IsTowerIso Φ T₀' T₀ χ₀) (hT₀ : IsGeoTestTower (stepOneMarked N 𝔞 μ) T₀) (u : X → ℂ) (W' : Opens Y₀')
    (W : Opens Y₀) (ψ : CMfd.of (n := n) W' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) W)
    (hψ : ∀ q : W', ((ψ q : W) : Y₀) = χ₀ q) :
    contactMarked (Φ ⁻¹' N) (GermIdeal.pullback (m := n) Φ 𝔞) μ (u ∘ Φ) T₀' W' =
      MarkedIdeal.pullback ψ (contactMarked N 𝔞 μ u T₀ W) := by
  obtain ⟨hJN, hJc, hJd⟩ := ContactIndependenceAlong.coeffHom_basic (μ := μ) h𝔞 hN
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc T₀ hT₀
  have hcoh : (withN (coeffMarkedAlong (geoTransformAlong (stepOneMarked N 𝔞 μ) T₀))
      (strictAlong T₀ (N ∩ {x | u x = 0}))).ideal.IsCoherent := isCoherent_coeffMarkedAlong hcT hNT
  unfold contactMarked
  rw [stepOneMarked_pullback Φ h𝔞 hN hμ]
  have hA : (Φ ⁻¹' N) ∩ {x | (u ∘ Φ) x = 0} = Φ ⁻¹' (N ∩ {x | u x = 0}) := rfl
  rw [hA, IsTowerIso.restrictedCoeff_eq Φ hJN hJc hJd hiso hT₀ (N ∩ {x | u x = 0})]
  exact pullback_pullback_of_comp_eq hcoh χ₀.contMDiff contMDiff_subtype_val ψ.contMDiff contMDiff_subtype_val
    fun q => (hψ q).symm

/-- **Step 1b's restricted marked ideal along an isomorphism of towers over the identity of the base**:
`contactMarked N 𝔞 μ u T₀' W' = ψ^*(contactMarked N 𝔞 μ u T₀ W)`. -/
theorem contactMarked_isTowerIso_refl (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    {T₀' : BlowupTower X Y₀'} (hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞) T₀' T₀ χ₀)
    (hT₀ : IsGeoTestTower (stepOneMarked N 𝔞 μ) T₀) (u : X → ℂ) (W' : Opens Y₀') (W : Opens Y₀)
    (ψ : CMfd.of (n := n) W' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) W)
    (hψ : ∀ q : W', ((ψ q : W) : Y₀) = χ₀ q) :
    contactMarked N 𝔞 μ u T₀' W' = MarkedIdeal.pullback ψ (contactMarked N 𝔞 μ u T₀ W) := by
  have h := contactMarked_isTowerIso _ h𝔞 hN hμ hiso hT₀ u W' W ψ hψ
  rwa [show GermIdeal.pullback (m := n) (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞) 𝔞 = 𝔞 from
    BlowupControlledTransform.pullback_id h𝔞] at h

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Step 1b's values along an isomorphism of towers** (property (6), values): in the situation of
`contactMarked_isTowerIso`, if `contactMarked N 𝔞 μ u T₀ W` lies in the domain of a resolution invariant `R` and `T₁` is a
canonical segment of it, then along every tower `T₁'` isomorphic to `T₁` over `ψ` (last-stage map `ξ`) the marked ideal
`contactMarked (Φ⁻¹N) (Φ^*𝔞) μ (u ∘ Φ) T₀' W'` lies in the domain, `T₁'` is a canonical segment of it, and the values at `p`
and `ξ p` agree on the cosupport. -/
theorem inv_contactMarked_isTowerIso (R : ResolutionInvariant.{u, v} n k Λ) (h𝔞 : 𝔞.IsCoherent)
    (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) (hiso : IsTowerIso Φ T₀' T₀ χ₀)
    (hT₀ : IsGeoTestTower (stepOneMarked N 𝔞 μ) T₀) (u : X → ℂ) (W' : Opens Y₀') (W : Opens Y₀)
    (ψ : CMfd.of (n := n) W' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) W)
    (hψ : ∀ q : W', ((ψ q : W) : Y₀) = χ₀ q) (hdom : IsInvDomain k (contactMarked N 𝔞 μ u T₀ W))
    {Z' Z : CMfd.{u} n} {T₁' : BlowupTower (CMfd.of (n := n) W') Z'} {T₁ : BlowupTower (CMfd.of (n := n) W) Z}
    {ξ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z} (hξ : IsTowerIso ψ T₁' T₁ ξ)
    (hcan : IsCanonical (contactMarked N 𝔞 μ u T₀ W) (R.inv (contactMarked N 𝔞 μ u T₀ W)) T₁) :
    IsInvDomain k (contactMarked (Φ ⁻¹' N) (GermIdeal.pullback (m := n) Φ 𝔞) μ (u ∘ Φ) T₀' W') ∧
      IsCanonical (contactMarked (Φ ⁻¹' N) (GermIdeal.pullback (m := n) Φ 𝔞) μ (u ∘ Φ) T₀' W')
        (R.inv (contactMarked (Φ ⁻¹' N) (GermIdeal.pullback (m := n) Φ 𝔞) μ (u ∘ Φ) T₀' W')) T₁' ∧
      ∀ p : Z', ξ p ∈ (geoTransformAlong (contactMarked N 𝔞 μ u T₀ W) T₁).cosupp →
        R.inv (contactMarked (Φ ⁻¹' N) (GermIdeal.pullback (m := n) Φ 𝔞) μ (u ∘ Φ) T₀' W') T₁' p =
          R.inv (contactMarked N 𝔞 μ u T₀ W) T₁ (ξ p) := by
  rw [contactMarked_isTowerIso Φ h𝔞 hN hμ hiso hT₀ u W' W ψ hψ]
  exact ⟨InvDomainTowerAlong.isInvDomain_pullback ψ hdom, isCanonical_of_isTowerIso R hdom ψ hξ hcan,
    fun p hp => R.towerIso ψ _ hdom T₁' T₁ ξ hξ hcan p hp⟩

end Transport

/-! ### Property (5): restriction to an open set of the base -/

section Restrict

variable {X : CMfd.{u} n} (U : Opens X) {N : Set X} {𝔞 : GermIdeal n X} {μ : ℕ}

/-- **`J̄` commutes with restriction to an open set**: `J̄` formed for `(ι⁻¹N, ι^*𝔞, μ)` is `ι^*J̄` (`ι : U → X`). -/
theorem stepOneMarked_pullback_val (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) :
    stepOneMarked ((Subtype.val : U → X) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔞) μ =
      MarkedIdeal.pullback (Subtype.val : U → X) (stepOneMarked N 𝔞 μ) := by
  have hH : (homogenizedMarkedAlong N 𝔞 μ).ideal.IsCoherent := isCoherent_homogenizedIdealAlong h𝔞 hN μ
  show coeffMarkedAlong (homogenizedMarkedAlong ((Subtype.val : U → X) ⁻¹' N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔞) μ) =
    MarkedIdeal.pullback (Subtype.val : U → X) (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ))
  rw [pullback_val_coeffMarkedAlong U (homogenizedMarkedAlong N 𝔞 μ) hH hN hμ]
  congr 1
  exact (pullback_val_homMarkedAlong U (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n X) h𝔞 hN hμ).symm

/-- **Tangent directions restrict to open sets**: a tangent direction `u` of `(𝔞|_N, μ)` on `U₀` gives the tangent direction
`u ∘ ι` of `(ι^*𝔞|_{ι⁻¹N}, μ)` on `ι⁻¹U₀` (`ι : U → X`). -/
theorem isTangentDirectionAlong_comp_val (h𝔞 : 𝔞.IsCoherent) {U₀ : Set X} {u : X → ℂ}
    (hu : IsTangentDirectionAlong N 𝔞 μ U₀ u) :
    IsTangentDirectionAlong ((Subtype.val : U → X) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔞) μ
      ((Subtype.val : U → X) ⁻¹' U₀) (u ∘ Subtype.val) :=
  ContactEquivalenceAlong.isTangentDirectionAlong_pullback
    (fun y => ⟨DerivativeIdealAlongEtale.openInv U y, DerivativeIdealAlongEtale.isLocalInverseAt_val U y⟩)
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞) hu

variable {Y₀ : CMfd.{u} n}

/-- **Step 1b's restricted marked ideal on a restricted tower** (property (5), marked ideals): for `U` open in the base, a
multiple test blow-up `T₀` of `J̄` and an open `W ⊆ T₀⁻¹U`, the marked ideal of Step 1b formed for `(ι⁻¹N, ι^*𝔞, μ)` along
`T₀|_U` with the tangent direction `u ∘ ι`, on `W` seen inside `T₀⁻¹U`, is the transport along `nestedOpensDiffeo` (the
identity on points) of `contactMarked N 𝔞 μ u T₀ W`. -/
theorem contactMarked_restrict (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (stepOneMarked N 𝔞 μ) T₀) (u : X → ℂ) {W : Opens Y₀}
    (hW : W ≤ openPreimage T₀ U) :
    contactMarked ((Subtype.val : U → X) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔞) μ
        (u ∘ Subtype.val) (restrict U T₀) (nestedOpens (openPreimage T₀ U) W) =
      MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW) (contactMarked N 𝔞 μ u T₀ W) := by
  obtain ⟨hJN, hJc, hJd⟩ := ContactIndependenceAlong.coeffHom_basic (μ := μ) h𝔞 hN
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc T₀ hT₀
  have hcoh : (withN (coeffMarkedAlong (geoTransformAlong (stepOneMarked N 𝔞 μ) T₀))
      (strictAlong T₀ (N ∩ {x | u x = 0}))).ideal.IsCoherent := isCoherent_coeffMarkedAlong hcT hNT
  unfold contactMarked
  rw [stepOneMarked_pullback_val U h𝔞 hN hμ]
  have hA : ((Subtype.val : U → X) ⁻¹' N) ∩ {x | (u ∘ Subtype.val) x = 0} =
      (Subtype.val : U → X) ⁻¹' (N ∩ {x | u x = 0}) := rfl
  rw [hA, ContactCanonicalAlong.restrictedCoeff_geoTransformAlong_restrict U hJN hJc hJd T₀ hT₀ (N ∩ {x | u x = 0})]
  exact pullback_val_pullback_val hcoh hW

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Step 1b's values on a restricted tower** (property (5), values): for `U` open in the base, a multiple test blow-up `T₀`
of `J̄`, an open `W ⊆ T₀⁻¹U` and a tower `T₁` over the last stage of `T₀`: if `𝓢 = contactMarked N 𝔞 μ u T₀ W` lies in the
domain of a resolution invariant `R` and `T₁|_W` is a canonical segment of it, then the marked ideal `𝓢_U` of Step 1b formed
for `(ι⁻¹N, ι^*𝔞, μ)` along `T₀|_U` with `u ∘ ι` on `W` (inside `T₀⁻¹U`) lies in the domain, the restriction to `W` of
`T₁|_{T₀⁻¹U}` is a canonical segment of it, and at points `p`, `q` of the two last stages with the same image, `p` lies in the
cosupport of `𝓢_U` iff `q` lies in that of `𝓢`, and then the values agree. -/
theorem inv_contactMarked_restrict (R : ResolutionInvariant.{u, v} n k Λ) (h𝔞 : 𝔞.IsCoherent)
    (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (stepOneMarked N 𝔞 μ) T₀) (u : X → ℂ) {W : Opens Y₀} (hW : W ≤ openPreimage T₀ U)
    (hdom : IsInvDomain k (contactMarked N 𝔞 μ u T₀ W)) {Z : CMfd.{u} n} (T₁ : BlowupTower Y₀ Z)
    (hcan : IsCanonical (contactMarked N 𝔞 μ u T₀ W) (R.inv (contactMarked N 𝔞 μ u T₀ W)) (restrict W T₁)) :
    IsInvDomain k (contactMarked ((Subtype.val : U → X) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔞) μ
        (u ∘ Subtype.val) (restrict U T₀) (nestedOpens (openPreimage T₀ U) W)) ∧
      IsCanonical (contactMarked ((Subtype.val : U → X) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔞) μ
          (u ∘ Subtype.val) (restrict U T₀) (nestedOpens (openPreimage T₀ U) W))
        (R.inv (contactMarked ((Subtype.val : U → X) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔞) μ
          (u ∘ Subtype.val) (restrict U T₀) (nestedOpens (openPreimage T₀ U) W)))
        (restrict (nestedOpens (openPreimage T₀ U) W) (restrict (openPreimage T₀ U) T₁)) ∧
      ∀ (p : openPreimage (restrict (openPreimage T₀ U) T₁) (nestedOpens (openPreimage T₀ U) W))
        (q : openPreimage T₁ W), (((p : openPreimage T₁ (openPreimage T₀ U)) : Z)) = q →
        (p ∈ (geoTransformAlong (contactMarked ((Subtype.val : U → X) ⁻¹' N)
            (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔞) μ (u ∘ Subtype.val) (restrict U T₀)
            (nestedOpens (openPreimage T₀ U) W)) (restrict (nestedOpens (openPreimage T₀ U) W)
              (restrict (openPreimage T₀ U) T₁))).cosupp ↔
          q ∈ (geoTransformAlong (contactMarked N 𝔞 μ u T₀ W) (restrict W T₁)).cosupp) ∧
        (q ∈ (geoTransformAlong (contactMarked N 𝔞 μ u T₀ W) (restrict W T₁)).cosupp →
          R.inv (contactMarked ((Subtype.val : U → X) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔞) μ
              (u ∘ Subtype.val) (restrict U T₀) (nestedOpens (openPreimage T₀ U) W))
              (restrict (nestedOpens (openPreimage T₀ U) W) (restrict (openPreimage T₀ U) T₁)) p =
            R.inv (contactMarked N 𝔞 μ u T₀ W) (restrict W T₁) q) := by
  have hiso := isTowerIso_restrict_nestedOpens (X := Y₀) hW T₁
  have hTt := isGeoTestTower_of_isCanonical R hdom _ hcan
  have hcos := IsTowerIso.cosupp_geoTransformAlong (nestedOpensDiffeo (n := n) hW)
    hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent hiso hTt
  rw [contactMarked_restrict U h𝔞 hN hμ T₀ hT₀ u hW]
  refine ⟨InvDomainTowerAlong.isInvDomain_pullback _ hdom, isCanonical_of_isTowerIso R hdom _ hiso hcan,
    fun p q hpq => ?_⟩
  have hχ : nestedDiffeo (n := n) (openPreimage T₁ (openPreimage T₀ U))
      (openPreimage (restrict (openPreimage T₀ U) T₁) (nestedOpens (openPreimage T₀ U) W)) (openPreimage T₁ W)
      (mem_openPreimage_restrict_nestedOpens (openPreimage T₀ U) W T₁) (openPreimage_mono T₁ hW) p = q :=
    Subtype.ext hpq
  refine ⟨?_, fun hq => ?_⟩
  · rw [hcos, mem_preimage, hχ]
  · have key := R.towerIso (nestedOpensDiffeo (n := n) hW) _ hdom _ _ _ hiso hcan p (by rw [hχ]; exact hq)
    rw [key, hχ]

end Restrict

end

end Hironaka.ContactMarkedCanonical
