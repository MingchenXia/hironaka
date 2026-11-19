import Hironaka.Invariant.ContactStageTail
import Hironaka.Invariant.InvDomainRebase

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Re-basing Step 1b's restricted marked ideal across steps that are empty near the point

Hironaka phase H3 (TN23-ENVELOPES), claimed on I-0981 C-0095 / I-0977 C-0134 (confirmed by TN-CLASSICAL, C-0098) for the Step 1
value function (`hir:maximal-order-step`, `blueprint/src/hironaka.tex`; TN-CLASSICAL's `StepOneValue`): the Step 1b analogue of
TN3's `InvDomainRebase.memberRestrict_rebase` (Step 1a).  Blueprint `mc:contact-stage-rebase`
(`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005 (arXiv `hiron.tex`), the lemma on the commutativity of the
resolution procedure in Step 1 with étale morphisms (`J̄'_{|V(u)} = φ^*(J̄_{|V(u)})`; blow-ups whose centres miss the image
pull back to isomorphisms).

In Step 1b the value at a point involves the invariant of `𝓢_{u,T₀}|_W = (𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩ V(u))_{T₀}})|_W`
(`MaximalOrderStepOneB.contactMarked N 𝔞 μ u T₀ W`), formed at a stage `T₀` that depends on the point and restricted to a
neighbourhood `W ⊆ T₀⁻¹U` of it, along the rest of the segment.  For a nearby point whose stage is later, `T₀ T`, the steps of
`T` are empty over `W` (`RestrictEmptyTower.CentresAvoid W T`), and re-basing (property (4') of
`ResolutionInvariantExt.ResolutionInvariant`) compares the two values once the marked ideal formed at the earlier stage,
transformed along `T|_W`, is known to be the one formed at the later stage.  This module proves that, up to restricted
equivalence, and the resulting identity of values.

## Main results

* `restrictEquiv_restrictedCoeff_geoTransformAlong_of_isEmptyTower` (generic): along a tower with only empty centres,
  `𝓒_{N_T}(𝔪_T)|_{A_T} ≃ (𝓒_N(𝔪)|_A)_T` (TN23's (K3) `ContactCanonicalAlong.restrictEquiv_restrictedCoeff_geoTransformAlong_empty`
  step by step);
* `restrictEquiv_restrictedCoeffHomAlong_rebase` (any divisor): for `J̄ = 𝓒_N(𝓗_N(𝔍))`, a multiple test blow-up `T₀ T` of `J̄`,
  `W ⊆ T₀⁻¹U` open with the centres of `T` missing `W`: `𝓢_{u,T₀T}|_{T⁻¹W} ≃ (𝓢_{u,T₀}|_W)_{T|_W}`;
* `restrictEquiv_contactMarked_rebase`: the same for `E = ∅` in TN-CLASSICAL's notation, `contactMarked N 𝔞 μ u (T₀.append T)
  (openPreimage T W) ≃ (contactMarked N 𝔞 μ u T₀ W)_{restrict W T}`;
* **`contactMarked_rebase`**: with TN3's `InvDomainRebase.inv_rebase` -- if `𝓢_{u,T₀}|_W` lies in the domain of a resolution
  invariant `R` and `T|_W T₁` is a canonical segment of it, then `𝓢_{u,T₀T}|_{T⁻¹W}` lies in the domain, `T₁` is a canonical
  segment of it, its transforms along `T₁` lie in the domain, and the values agree on the cosupport.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ContactStageRebase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen MemberInterTowerAlong MaximalContactAlongTower MarkedIdealOperationsAlong.MarkedIdeal
  ResolutionInvariantExt RestrictEmptyTower
open HomogenizedGlueingTower (strictAlong strictAlong_restrict)
open MemberInterLocusAlong (strictAlong_append)
open ContactIndependenceAlong (one_le_coeffMarkedAlong_d)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Restricted coefficient ideals along towers with only empty centres -/

section Generic

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
  (hd : 1 ≤ 𝔪.d) {A : Set X} (hA : IsClosedSubmanifold n A) (hAN : A ⊆ 𝔪.N)

include hN h𝔞 hd hA hAN in
/-- **The restricted coefficient ideal along a tower with only empty centres** ((K3) along the tower): for `𝔪` with `N` a
closed submanifold, coherent ideal and mark `≥ 1`, a closed submanifold `A ⊆ N` and a tower `T` all of whose centres are
empty, `𝓒_{N_T}(𝔪_T)|_{A_T} ≃ (𝓒_N(𝔪)|_A)_T`: restricting at the last stage or transforming the restriction formed at the
first stage gives restricted-equivalent marked ideals. -/
theorem restrictEquiv_restrictedCoeff_geoTransformAlong_of_isEmptyTower :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsEmptyTower T →
      RestrictEquiv (withN (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (strictAlong T A))
        (geoTransformAlong (withN (coeffMarkedAlong 𝔪) A) T)
  | _, .refl, _ => RestrictEquiv.refl (isCoherent_coeffMarkedAlong h𝔞 hN)
  | _, .step T C π hπ, hT => by
      obtain ⟨hT, hC⟩ : IsEmptyTower T ∧ C = ∅ := hT
      subst hC
      have hTt : IsGeoTestTower 𝔪 T := isGeoTestTower_of_isEmptyTower 𝔪 T hT
      obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hTt
      have hK := ContactCanonicalAlong.restrictEquiv_restrictedCoeff_geoTransformAlong_empty hN h𝔞 hd T hTt π hπ hAN
      have ih := restrictEquiv_restrictedCoeff_geoTransformAlong_of_isEmptyTower T hT
      have hcS : (geoTransformAlong (withN (coeffMarkedAlong 𝔪) A) T).ideal.IsCoherent :=
        (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong (𝔪 := withN (coeffMarkedAlong 𝔪) A) hA
          (isCoherent_coeffMarkedAlong h𝔞 hN) T (isGeoTestTower_of_isEmptyTower _ T hT)).2
      have heq := ih.geoTransform_eq (isClosed_strictAlong T hA.1) (isCoherent_coeffMarkedAlong hcT hNT) hcS
        (C := ∅) hπ.contMDiff
      show RestrictEquiv _ ((geoTransformAlong (withN (coeffMarkedAlong 𝔪) A) T).geoTransform ∅ π)
      rw [← heq]
      exact hK

end Generic

/-! ### Step 1b: `J̄ = 𝓒_N(𝓗_N(𝔍))`, any divisor -/

section CoeffHomAlong

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔍.N) (h𝔞 : 𝔍.ideal.IsCoherent)
  (hd : 1 ≤ 𝔍.d) (U : Opens X) {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u)

include hN h𝔞 hd hu in
/-- **Step 1b's restricted marked ideal re-based across steps empty over `W`** (any divisor; READING `(𝔞, μ)`): for
`J̄ = 𝓒_N(𝓗_N(𝔍))`, a tangent direction `u` of `(𝔍.ideal|_N, d)` along `N` on `U`, a multiple test blow-up `T₀ T` of `J̄` and
an open `W ⊆ T₀⁻¹U` of the last stage of `T₀` missed by the centres of `T`: the restricted coefficient ideal formed at the
later stage, `𝓢_{u,T₀T}|_{T⁻¹W}`, is restricted-equivalent to the transform along `T|_W` of the one formed at `T₀`,
`(𝓢_{u,T₀}|_W)_{T|_W}`. -/
theorem restrictEquiv_restrictedCoeffHomAlong_rebase {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T : BlowupTower Y₀ Y) (hT : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀.append T)) (W : Opens Y₀)
    (hWU : (W : Set Y₀) ⊆ openPreimage T₀ U) (hW : CentresAvoid W T) :
    RestrictEquiv
      (MarkedIdeal.pullback (Subtype.val : openPreimage T W → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀.append T)))
          (strictAlong (T₀.append T) (𝔍.N ∩ {x | u x = 0}))))
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y₀)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
          (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))) (restrict W T)) := by
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff _ T₀ T).mp hT
  have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong 𝔍)).N := hN
  have hJc : (coeffMarkedAlong (homMarkedAlong 𝔍)).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
  have hT₀a : IsGeoTestTower 𝔍 T₀ := ((coeff_homAlong_wEquiv 𝔍 hN h𝔞 hd).2 T₀).1.mp hT₀
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc T₀ hT₀
  have hdT : 1 ≤ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).d := by
    rw [d_geoTransformAlong]; exact one_le_coeffMarkedAlong_d _
  have hSN : strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ⊆ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).N :=
    strictAlong_subset_N (coeffMarkedAlong (homMarkedAlong 𝔍)) (fun x hx => hx.1) T₀
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → Y₀) := contMDiff_subtype_val
  have he : IsEmptyTower (restrict W T) := (isEmptyTower_restrict_iff W T).mpr hW
  have hK := restrictEquiv_restrictedCoeff_geoTransformAlong_of_isEmptyTower (X := CMfd.of (n := n) W)
    (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
    (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hNT W) (GermIdealPullbackCalculus.isCoherent_pullback hval hcT)
    hdT (ContactStageInvDomain.isClosedSubmanifold_strictAlong_stage_of_le 𝔍 hN h𝔞 hd U hu T₀ hT₀a W hWU)
    (preimage_mono hSN) (restrict W T) he
  rw [ContactCanonicalAlong.restrictedCoeff_geoTransformAlong_restrict W hNT hcT hdT T hT₁,
    ← pullback_val_coeffMarkedAlong W _ hcT hNT hdT] at hK
  rw [geoTransformAlong_append, strictAlong_append]
  exact hK

end CoeffHomAlong

/-! ### Step 1b with `E = ∅`, in the notation of `MaximalOrderStepOneB` -/

section ContactMarked

open MaximalOrderStepOneB (stepOneMarked contactMarked)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ}

/-- **Step 1b's restricted marked ideal re-based, `E = ∅`** (TN-CLASSICAL's notation): for a multiple test blow-up `T₀ T` of
`stepOneMarked N 𝔞 μ` and an open `W ⊆ T₀⁻¹U` missed by the centres of `T`,
`contactMarked N 𝔞 μ u (T₀ T) (T⁻¹W) ≃ (contactMarked N 𝔞 μ u T₀ W)_{T|_W}`. -/
theorem restrictEquiv_contactMarked_rebase (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    (U : Opens M) {u : M → ℂ} (hu : IsTangentDirectionAlong N 𝔞 μ U u) {Y₀ Y : CMfd.{u} n}
    (T₀ : BlowupTower (CMfd.of (n := n) M) Y₀) (T : BlowupTower Y₀ Y)
    (hT : IsGeoTestTower (stepOneMarked N 𝔞 μ) (T₀.append T)) (W : Opens Y₀) (hWU : (W : Set Y₀) ⊆ openPreimage T₀ U)
    (hW : CentresAvoid W T) :
    RestrictEquiv (contactMarked N 𝔞 μ u (T₀.append T) (openPreimage T W))
      (geoTransformAlong (contactMarked N 𝔞 μ u T₀ W) (restrict W T)) := by
  unfold contactMarked
  exact restrictEquiv_restrictedCoeffHomAlong_rebase (X := CMfd.of (n := n) M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) hN h𝔞 hμ
    U hu T₀ T hT W hWU hW

variable {Λ : Type v} [LinearOrder Λ] {k : ℕ}

/-- **Step 1b's values re-based** (the form the Step 1 value function uses to compare nearby points, the analogue of TN3's
`InvDomainRebase.memberRestrict_rebase` for Step 1a): let `T₀ T` be a multiple test blow-up of `J̄ = stepOneMarked N 𝔞 μ`,
`W ⊆ T₀⁻¹U` open with the centres of `T` missing `W`, and `R` a resolution invariant in dimension `≤ k`.  If
`𝓢₀ = contactMarked N 𝔞 μ u T₀ W` lies in the domain and `T|_W T₁` is a canonical segment of it, then
`𝓢₁ = contactMarked N 𝔞 μ u (T₀ T) (T⁻¹W)` lies in the domain, `T₁` is a canonical segment of `𝓢₁`, every transform of `𝓢₁`
along `T₁` lies in the domain, and the values of `𝓢₀` along `T|_W T₁` are those of `𝓢₁` along `T₁` on the cosupport. -/
theorem contactMarked_rebase (R : ResolutionInvariant.{u, v} n k Λ) (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hμ : 1 ≤ μ) (U : Opens M) {u : M → ℂ} (hu : IsTangentDirectionAlong N 𝔞 μ U u) {Y₀ Y : CMfd.{u} n}
    (T₀ : BlowupTower (CMfd.of (n := n) M) Y₀) (T : BlowupTower Y₀ Y)
    (hT : IsGeoTestTower (stepOneMarked N 𝔞 μ) (T₀.append T)) (W : Opens Y₀) (hWU : (W : Set Y₀) ⊆ openPreimage T₀ U)
    (hW : CentresAvoid W T) (hdom : IsInvDomain k (contactMarked N 𝔞 μ u T₀ W))
    {Z : CMfd.{u} n} (T₁ : BlowupTower (CMfd.of (n := n) (openPreimage T W)) Z)
    (hcan : IsCanonical (contactMarked N 𝔞 μ u T₀ W) (R.inv (contactMarked N 𝔞 μ u T₀ W)) ((restrict W T).append T₁)) :
    IsInvDomain k (contactMarked N 𝔞 μ u (T₀.append T) (openPreimage T W)) ∧
      IsCanonical (contactMarked N 𝔞 μ u (T₀.append T) (openPreimage T W))
        (R.inv (contactMarked N 𝔞 μ u (T₀.append T) (openPreimage T W))) T₁ ∧
      IsInvDomain k (geoTransformAlong (contactMarked N 𝔞 μ u (T₀.append T) (openPreimage T W)) T₁) ∧
      ∀ z ∈ (geoTransformAlong (contactMarked N 𝔞 μ u T₀ W) ((restrict W T).append T₁)).cosupp,
        R.inv (contactMarked N 𝔞 μ u T₀ W) ((restrict W T).append T₁) z =
          R.inv (contactMarked N 𝔞 μ u (T₀.append T) (openPreimage T W)) T₁ z := by
  have he : IsEmptyTower (restrict W T) := (isEmptyTower_restrict_iff W T).mpr hW
  have hEq := restrictEquiv_contactMarked_rebase h𝔞 hN hμ U hu T₀ T hT W hWU hW
  obtain ⟨hJN, hJc, -⟩ := ContactIndependenceAlong.coeffHom_basic (μ := μ) h𝔞 hN
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc (T₀.append T) hT
  have hcoh : (contactMarked N 𝔞 μ u (T₀.append T) (openPreimage T W)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val (isCoherent_coeffMarkedAlong hcT hNT)
  obtain ⟨h1, h2, h3⟩ := InvDomainRebase.inv_rebase (X := CMfd.of (n := n) W) R hdom (restrict W T) he hEq hcoh T₁ hcan
  exact ⟨h1, h2, isInvDomain_of_isCanonical R h1 T₁ h2, h3⟩

end ContactMarked

end

end Hironaka.ContactStageRebase
