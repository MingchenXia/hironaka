import Hironaka.Invariant.ContactIndependenceAlong
import Hironaka.Invariant.ContactCanonicalAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Isomorphisms of towers over a biholomorphism of the bases

Hironaka phase H3 (TN23-ENVELOPES), claimed on I-0981 C-0074 at TN-CLASSICAL's request (C-0073, answer (a) to TN23's
C-0072): the Lean form of TN-CLASSICAL's design node `hir:tower-isomorphism` (`blueprint/src/hironaka.tex`, fbf21d2b) and
its three uses.  Property (6) of `hir:centre-function` is stated for isomorphisms of towers over a biholomorphism of the
bases; the transport `Φ^*T` of `hir:tower-transport` is the case `χ_i = id` (`i ≥ 1`), and the stage-by-stage lifts of the
glueing biholomorphism along a segment are another (the "does not depend on `w`" step of Step 1b of
`hir:maximal-order-step`).  Blueprint `mc:tower-isomorphism-basic`, `mc:tower-isomorphism-transform`,
`mc:tower-isomorphism-coefficient`, `mc:glueing-lift-tower-isomorphism` (`blueprint/src/maximal-contact.tex`).  Source:
Włodarczyk 2005 (arXiv `hiron.tex`): Proposition `pr: funct` (the induced towers `φ^*(X_i) = X' ×_X X_i`, defined up to
isomorphism, with lifts `φ_i` commuting with the blow-ups) and Step 1bb (`φ_{pu}^*(..) = φ_{pv}^*(..)`).

## Isomorphisms of towers

* `IsTowerIso Φ T' T χ`: an inductive predicate on pairs of towers of the same length over `Φ : X' ≅ X`; `χ : Y' ≅ Y` is
  the last-stage biholomorphism of a family `χ_i` with `χ_0 = Φ`, `σ_i ∘ χ_i = χ_{i-1} ∘ σ'_i`, `χ_{i-1}⁻¹ C_{i-1} = C'_{i-1}`.
* `IsTowerIso.length_eq`, `IsTowerIso.proj_comm` (`Φ ∘ p_{T'} = p_T ∘ χ`), `IsTowerIso.strictAlong_eq`
  (`(Φ⁻¹A)_{T'} = χ⁻¹(A_T)`); `transport_isTowerIso`: the transport is an isomorphism with its last-stage biholomorphism.

## Naturality (for `𝔪` with closed submanifold `N` and coherent ideal)

* `IsTowerIso.geoTransformAlong_eq`: along a multiple test blow-up `T` of `𝔪`, `(Φ^*𝔪)_{T'} = χ^*(𝔪_T)`;
  `IsTowerIso.isGeoTestTower_iff`, `IsTowerIso.isGeoResolution_iff`: multiple test blow-ups and resolutions correspond;
  `IsTowerIso.cosupp_geoTransformAlong`.
* `IsTowerIso.coeffMarkedAlong_eq`, `IsTowerIso.restrictedCoeff_eq` (`S_{Φ⁻¹A}((Φ^*𝔪)_{T'}) = χ^* S_A(𝔪_T)`,
  `S_A(𝔪_T) = 𝓒_{N_T}(𝔪_T)|_{A_T}`), `IsTowerIso.restricted_eq`, `IsTowerIso.cosupp_restrictedCoeff_eq`,
  `IsTowerIso.isTangentDirectionAlong` (`u ∘ χ`, with `N'_{T'} ∩ V(u ∘ χ) = χ⁻¹(N_T ∩ V(u))`): the form of
  `ContactCanonicalAlong`'s (K1) for isomorphic towers.

## The glueing lifts

* `exists_isGlueingLiftAlong_isTowerIso`: along every multiple test blow-up `T` of `(𝓗_N(𝔞), μ)` and of a family of
  pairs `(𝔫 i, 𝔫' i)` preserved by the glueing biholomorphism, one lift `Φ_T` (`IsGlueingLiftAlong`) is the last-stage
  biholomorphism of an isomorphism `T|_U ≅ T|_{U'}` over `G.equiv` and transports every `(𝔫 i)_T`;
  `exists_isGlueingLiftAlong_isTowerIso_hom` (no family).
* `exists_isTowerIso_coeffHom`: for `J̄ = 𝓒_N(𝓗_N(𝔞), μ)`, the same with the four clauses of
  `ContactIndependenceAlong.exists_isGlueingLiftAlong_coeffHom` (`J̄_T` transported, `S_{u,T}|_{U'} ↦ S_{v,T}|_U` with and
  without `𝓒`, `cosupp J̄_T` fixed pointwise); `contact_independence_along_isTowerIso`: packaged from two tangent
  directions at a point of the cosupport.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupTowerIsomorphism

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealTowerTransport MarkedIdealRestrictOpen BlowupStrictSubmanifold HomogenizedIdealAlong
  CoefficientIdealRestriction TangentDirectionAlong
open HomogenizedGlueingTower (strictAlong)

noncomputable section

variable {n : ℕ}

/-! ### Isomorphisms of towers -/

/-- **An isomorphism of towers over a biholomorphism of the bases** (`hir:tower-isomorphism`): for towers `T'` over `X'`
and `T` over `X` of the same length and a biholomorphism `Φ : X' ≅ X`, `IsTowerIso Φ T' T χ` says that `χ` is the
last-stage biholomorphism of a family `χ_i : X'_i ≅ X_i` with `χ_0 = Φ`, `σ_i ∘ χ_i = χ_{i-1} ∘ σ'_i` and
`χ_{i-1}⁻¹(C_{i-1}) = C'_{i-1}` (built stage by stage). -/
inductive IsTowerIso {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) :
    {Y' Y : CMfd.{u} n} → BlowupTower X' Y' → BlowupTower X Y →
      (Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y) → Prop
  /-- The empty towers are isomorphic over `Φ`, with last-stage biholomorphism `Φ`. -/
  | refl : IsTowerIso Φ .refl .refl Φ
  /-- An isomorphism extends over blowups whose centres correspond and which commute with the stage maps. -/
  | step {Y' Y Z' Z : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
      {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (h : IsTowerIso Φ T' T χ)
      {C' : Set Y'} {π' : Z' → Y'} (hπ' : IsBlowupAlong n C' π') {C : Set Y} {π : Z → Y}
      (hπ : IsBlowupAlong n C π) (χ₁ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z)
      (hcomm : ∀ p, π (χ₁ p) = χ (π' p)) (hC : χ ⁻¹' C = C') :
      IsTowerIso Φ (.step T' C' π' hπ') (.step T C π hπ) χ₁

section Basic

variable {X X' : CMfd.{u} n} {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
  {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
  {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}

/-- **Isomorphic towers have the same length.** -/
theorem IsTowerIso.length_eq (h : IsTowerIso Φ T' T χ) : T'.length = T.length := by
  induction h with
  | refl => rfl
  | step _ _ _ _ _ _ ih => exact congrArg (· + 1) ih

/-- **The stage biholomorphisms commute with the projections to the bases**: `Φ ∘ p_{T'} = p_T ∘ χ`. -/
theorem IsTowerIso.proj_comm (h : IsTowerIso Φ T' T χ) : ∀ p, Φ (T'.proj p) = T.proj (χ p) := by
  induction h with
  | refl => exact fun _ => rfl
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro p
    show Φ (T'.proj (π' p)) = T.proj (π (χ₁ p))
    rw [hcomm]
    exact ih (π' p)

/-- **Strict transforms correspond**: `(Φ⁻¹A)_{T'} = χ⁻¹(A_T)`. -/
theorem IsTowerIso.strictAlong_eq (h : IsTowerIso Φ T' T χ) (A : Set X) :
    strictAlong T' (Φ ⁻¹' A) = χ ⁻¹' strictAlong T A := by
  induction h with
  | refl => rfl
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    show geoStrictTransform π' C' (strictAlong T' (Φ ⁻¹' A)) = χ₁ ⁻¹' geoStrictTransform π C (strictAlong T A)
    rw [ih, ← hC, ← BlowupBiholomorphismLift.geoStrictTransform_comp_diffeo χ₁ π C]
    have hfun : χ ∘ π' = π ∘ χ₁ := funext fun p => (hcomm p).symm
    unfold geoStrictTransform
    rw [← preimage_sdiff, ← preimage_comp, hfun]

end Basic

/-- **The transport is an isomorphism of towers** (`hir:tower-isomorphism`, `χ_i = id` for `i ≥ 1`): the transport
`Φ^*T` of a tower `T` is isomorphic to `T` over `Φ`, with its last-stage biholomorphism. -/
theorem transport_isTowerIso {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsTowerIso Φ (transport Φ T).tower T (transport Φ T).back
  | _, .refl => IsTowerIso.refl
  | _, .step T C π hπ =>
      IsTowerIso.step (transport_isTowerIso Φ T) _ hπ (transport Φ (.step T C π hπ)).back
        (fun p => ((transport Φ T).back.apply_symm_apply (π p)).symm) rfl

/-! ### Naturality of the transforms -/

section Naturality

variable {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {𝔪 : MarkedIdeal n X}
  {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
  {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}

/-- **Transforms along isomorphic towers** (`hir:tower-isomorphism`, the generalisation of
`MarkedIdealTowerTransport.geoTransformAlong_transport_step`): along a multiple test blow-up `T` of `𝔪` (closed
submanifold, coherent ideal) and a tower `T'` isomorphic to it over `Φ`, the transform of `Φ^*𝔪` along `T'` is the
`χ`-pullback of the transform of `𝔪` along `T`. -/
theorem IsTowerIso.geoTransformAlong_eq (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (h : IsTowerIso Φ T' T χ) : IsGeoTestTower 𝔪 T →
      geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T' = MarkedIdeal.pullback χ (geoTransformAlong 𝔪 T) := by
  induction h with
  | refl => exact fun _ => rfl
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro hT
    obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT.1
    have hc := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNT hcT hT.2 hπ
    have hfun : π' = χ.symm ∘ (π ∘ χ₁) := funext fun p => by simp [hcomm]
    subst hC hfun
    show (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T').geoTransform (χ ⁻¹' C) (χ.symm ∘ (π ∘ χ₁)) =
      MarkedIdeal.pullback χ₁ ((geoTransformAlong 𝔪 T).geoTransform C π)
    rw [ih hT.1, MarkedIdeal.geoTransform_pullback χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply
      χ.symm_apply_apply _ hcT C (hπ.contMDiff.comp χ₁.contMDiff)]
    exact BlowupBiholomorphismLift.geoTransform_comp_diffeo χ₁ _ hcT C
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hπ.1) hπ.contMDiff hc

/-- **Multiple test blow-ups correspond along isomorphic towers**: `T'` is a multiple test blow-up of `Φ^*𝔪` iff `T` is
one of `𝔪`. -/
theorem IsTowerIso.isGeoTestTower_iff (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (h : IsTowerIso Φ T' T χ) : IsGeoTestTower (MarkedIdeal.pullback Φ 𝔪) T' ↔ IsGeoTestTower 𝔪 T := by
  induction h with
  | refl => exact Iff.rfl
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    rw [isGeoTestTower_step_iff, isGeoTestTower_step_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hT := ih.mp h1
      obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
      rw [IsTowerIso.geoTransformAlong_eq Φ hN h𝔞 h hT, ← hC] at h2
      exact ⟨hT, (isAdmissibleCentre_pullback_iff hcT).mp h2⟩
    · rintro ⟨hT, h2⟩
      obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
      refine ⟨ih.mpr hT, ?_⟩
      rw [IsTowerIso.geoTransformAlong_eq Φ hN h𝔞 h hT, ← hC]
      exact (isAdmissibleCentre_pullback_iff hcT).mpr h2

/-- **Cosupports correspond along isomorphic multiple test blow-ups**: `cosupp (Φ^*𝔪)_{T'} = χ⁻¹ cosupp 𝔪_T`. -/
theorem IsTowerIso.cosupp_geoTransformAlong (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (h : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower 𝔪 T) :
    (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T').cosupp = χ ⁻¹' (geoTransformAlong 𝔪 T).cosupp := by
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  rw [IsTowerIso.geoTransformAlong_eq Φ hN h𝔞 h hT, cosupp_pullback_eq hcT]

/-- **Resolutions correspond along isomorphic towers.** -/
theorem IsTowerIso.isGeoResolution_iff (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (h : IsTowerIso Φ T' T χ) : IsGeoResolution (MarkedIdeal.pullback Φ 𝔪) T' ↔ IsGeoResolution 𝔪 T := by
  unfold IsGeoResolution
  rw [IsTowerIso.isGeoTestTower_iff Φ hN h𝔞 h]
  refine and_congr_right fun hT => ?_
  rw [IsTowerIso.cosupp_geoTransformAlong Φ hN h𝔞 h hT]
  refine ⟨fun h' => ?_, fun h' => by rw [h', preimage_empty]⟩
  rw [← χ.toEquiv.surjective.image_preimage (geoTransformAlong 𝔪 T).cosupp]
  rw [show ⇑χ.toEquiv = ⇑χ from rfl, h', image_empty]

/-- **The coefficient ideals along `N_T` correspond along isomorphic multiple test blow-ups**:
`𝓒((Φ^*𝔪)_{T'}) = χ^*𝓒(𝔪_T)` (`d ≥ 1`). -/
theorem IsTowerIso.coeffMarkedAlong_eq (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d)
    (h : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower 𝔪 T) :
    coeffMarkedAlong (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T') =
      MarkedIdeal.pullback χ (coeffMarkedAlong (geoTransformAlong 𝔪 T)) := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  rw [IsTowerIso.geoTransformAlong_eq Φ hN h𝔞 h hT, pullback_coeffMarkedAlong_of_inverse χ.contMDiff
    χ.symm.contMDiff χ.apply_symm_apply χ.symm_apply_apply _ hcT hNT (by rwa [d_geoTransformAlong])]

/-- **The restricted coefficient ideals correspond along isomorphic multiple test blow-ups** (property (6) of
`hir:centre-function` for Steps 1a/1b inside `N`, in the form of `hir:tower-isomorphism`):
`S_{Φ⁻¹A}((Φ^*𝔪)_{T'}) = χ^* S_A(𝔪_T)` for `S_A(𝔪_T) = 𝓒_{N_T}(𝔪_T)|_{A_T}`. -/
theorem IsTowerIso.restrictedCoeff_eq (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d)
    (h : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower 𝔪 T) (A : Set X) :
    withN (coeffMarkedAlong (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T')) (strictAlong T' (Φ ⁻¹' A)) =
      MarkedIdeal.pullback χ (withN (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (strictAlong T A)) := by
  rw [IsTowerIso.coeffMarkedAlong_eq Φ hN h𝔞 hd h hT, h.strictAlong_eq A]
  rfl

/-- **The restrictions of the transforms correspond along isomorphic multiple test blow-ups** (without `𝓒`). -/
theorem IsTowerIso.restricted_eq (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (h : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower 𝔪 T) (A : Set X) :
    withN (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T') (strictAlong T' (Φ ⁻¹' A)) =
      MarkedIdeal.pullback χ (withN (geoTransformAlong 𝔪 T) (strictAlong T A)) := by
  rw [IsTowerIso.geoTransformAlong_eq Φ hN h𝔞 h hT, h.strictAlong_eq A]
  rfl

/-- **Cosupports of the restricted coefficient ideals correspond**: `cosupp S_{Φ⁻¹A}((Φ^*𝔪)_{T'}) = χ⁻¹ cosupp S_A(𝔪_T)`. -/
theorem IsTowerIso.cosupp_restrictedCoeff_eq (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) (h : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower 𝔪 T) (A : Set X) :
    (withN (coeffMarkedAlong (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T')) (strictAlong T' (Φ ⁻¹' A))).cosupp =
      χ ⁻¹' (withN (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (strictAlong T A)).cosupp := by
  rw [IsTowerIso.restrictedCoeff_eq Φ hN h𝔞 hd h hT A]
  exact MarkedIdeal.cosupp_pullback χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply χ.symm_apply_apply _
    fun _ _ hg => ContactCanonicalAlong.holomorphicAt_of_mem_coeffMarkedAlong _ hg

/-- **Tangent directions correspond along isomorphic multiple test blow-ups**: if `u` is a tangent direction of
`(𝔪_T|_{N_T}, μ)` on `V`, then `u ∘ χ` is one of `((Φ^*𝔪)_{T'}|_{N'_{T'}}, μ)` on `χ⁻¹V`, and
`N'_{T'} ∩ V(u ∘ χ) = χ⁻¹(N_T ∩ V(u))`. -/
theorem IsTowerIso.isTangentDirectionAlong (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (h : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower 𝔪 T) {μ : ℕ} {V : Set Y} {u : Y → ℂ}
    (hu : IsTangentDirectionAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal μ V u) :
    IsTangentDirectionAlong (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T').N
        (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T').ideal μ (χ ⁻¹' V) (u ∘ χ) ∧
      (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T').N ∩ {p | (u ∘ χ) p = 0} =
        χ ⁻¹' ((geoTransformAlong 𝔪 T).N ∩ {y | u y = 0}) := by
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  rw [IsTowerIso.geoTransformAlong_eq Φ hN h𝔞 h hT]
  exact ⟨ContactEquivalenceAlong.isTangentDirectionAlong_pullback
    (fun y => ⟨_, isLocalInverseAt_of_contMDiff χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply
      χ.symm_apply_apply y⟩) (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcT) hu, rfl⟩

end Naturality

/-! ### The glueing lifts along a segment form an isomorphism of the restricted segments -/

section Glueing

open HomogenizedGlueingAlong HomogenizedGlueingAlongTower HomogenizedGlueingLiftAlong GlueingTrivialAction
  ContactIndependenceAlong

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ} (G : GlueingDataAlong N 𝔞 μ u v)

/-- **The glueing lifts along `N` form an isomorphism of the restricted towers, transporting preserved marked ideals**:
for glueing data `G` along `N` acting trivially modulo the glue ideal and a family of pairs `(𝔫 i, 𝔫' i)` with
`G.equiv^*(𝔫 i|_{U'}) = 𝔫' i|_U`, along every tower `T` that is a multiple test blow-up of `(𝓗_N(𝔞), μ)` and of every
`𝔫 i`, `𝔫' i` there is one lift `Φ_T` (`IsGlueingLiftAlong`) which is the last-stage biholomorphism of an isomorphism
`T|_U ≅ T|_{U'}` over `G.equiv` and transports every `(𝔫 i)_T` to `(𝔫' i)_T`. -/
theorem exists_isGlueingLiftAlong_isTowerIso (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    (htriv : ∀ y ∈ G.W, y ∈ zeroSet (glueIdealAlong N 𝔞 μ) →
      TrivialAt G.φ (glueIdealAlong N 𝔞 μ) y ∧ TrivialAt G.ψ (glueIdealAlong N 𝔞 μ) y)
    {ι : Sort*} (𝔫 𝔫' : ι → MarkedIdeal n M) (hN𝔫 : ∀ i, IsClosedSubmanifold n (𝔫 i).N)
    (h𝔫 : ∀ i, (𝔫 i).ideal.IsCoherent) (hN𝔫' : ∀ i, IsClosedSubmanifold n (𝔫' i).N)
    (h𝔫' : ∀ i, (𝔫' i).ideal.IsCoherent)
    (hpb : ∀ i, MarkedIdeal.pullback G.equiv (MarkedIdeal.pullback (Subtype.val : G.cod → M) (𝔫 i)) =
      MarkedIdeal.pullback (Subtype.val : G.dom → M) (𝔫' i)) :
    {Y : CMfd.{u} n} → (T : BlowupTower (CMfd.of (n := n) M) Y) →
      IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) T → (∀ i, IsGeoTestTower (𝔫 i) T) →
      (∀ i, IsGeoTestTower (𝔫' i) T) →
      ∃ Φ, IsGlueingLiftAlong G T Φ ∧ IsTowerIso G.equiv (restrict G.dom T) (restrict G.cod T) Φ ∧ ∀ i,
        MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : openPreimage T G.cod → Y)
          (geoTransformAlong (𝔫 i) T)) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T G.dom → Y) (geoTransformAlong (𝔫' i) T)
  | _, .refl, hT, _, _ => by
      obtain ⟨Φ, hL⟩ := exists_isGlueingLiftAlong G h𝔞 hN hμ htriv .refl hT
      have hΦ : Φ = G.equiv := lift_eq_equiv_refl G hL
      subst hΦ
      exact ⟨_, hL, IsTowerIso.refl, hpb⟩
  | _, .step T C π hπ, hT, h𝔫T, h𝔫'T => by
      obtain ⟨Φ, hL, hI, hP⟩ := exists_isGlueingLiftAlong_isTowerIso h𝔞 hN hμ htriv 𝔫 𝔫' hN𝔫 h𝔫 hN𝔫' h𝔫' hpb T
        hT.1 (fun i => (h𝔫T i).1) (fun i => (h𝔫'T i).1)
      obtain ⟨hcorr, Φ₁, hΦ₁, hL₁⟩ := exists_isGlueingLiftAlong_step G h𝔞 hN hμ T C π hπ hT hL
      refine ⟨Φ₁, hL₁, IsTowerIso.step hI _ _ Φ₁ (fun p => Subtype.ext (hΦ₁ p)) hcorr, fun i => ?_⟩
      obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong (hN𝔫 i) (h𝔫 i) T (h𝔫T i).1
      obtain ⟨hNT', hcT'⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong (hN𝔫' i) (h𝔫' i) T
        (h𝔫'T i).1
      exact pullback_lift_geoTransform_pair hπ Φ hcorr Φ₁ hΦ₁ hcT
        (HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNT hcT (h𝔫T i).2 hπ) hcT'
        (HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNT' hcT' (h𝔫'T i).2 hπ) (hP i)

/-- **The glueing lifts form an isomorphism of the restricted segments** (`hir:tower-isomorphism`): along every
multiple test blow-up `T` of `(𝓗_N(𝔞), μ)` some lift `Φ_T` of the glueing biholomorphism is the last-stage
biholomorphism of an isomorphism `T|_U ≅ T|_{U'}` over `G.equiv`. -/
theorem exists_isGlueingLiftAlong_isTowerIso_hom (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    (htriv : ∀ y ∈ G.W, y ∈ zeroSet (glueIdealAlong N 𝔞 μ) →
      TrivialAt G.φ (glueIdealAlong N 𝔞 μ) y ∧ TrivialAt G.ψ (glueIdealAlong N 𝔞 μ) y)
    {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y)
    (hT : IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) T) :
    ∃ Φ, IsGlueingLiftAlong G T Φ ∧ IsTowerIso G.equiv (restrict G.dom T) (restrict G.cod T) Φ := by
  obtain ⟨Φ, hL, hI, -⟩ := exists_isGlueingLiftAlong_isTowerIso G h𝔞 hN hμ htriv (ι := Empty) Empty.elim Empty.elim
    (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) T hT (fun i => i.elim)
    (fun i => i.elim)
  exact ⟨Φ, hL, hI⟩

/-- **The independence of the hypersurface of maximal contact inside `N` along isomorphic restricted segments**
(Step 1b of `hir:maximal-order-step` with `hir:tower-isomorphism`): along every multiple test blow-up `T` of
`J̄ = 𝓒_N(𝓗_N(𝔞), μ)` there is a lift `Φ_T` of the glueing biholomorphism which is the last-stage biholomorphism of an
isomorphism `T|_U ≅ T|_{U'}` over `G.equiv` and satisfies the four clauses of
`ContactIndependenceAlong.exists_isGlueingLiftAlong_coeffHom`: it transports `J̄_T`, maps the restricted coefficient ideal
on `(N ∩ V(u))_T` to that on `(N ∩ V(v))_T` (with and without `𝓒`), and fixes `cosupp J̄_T` pointwise. -/
theorem exists_isTowerIso_coeffHom (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    (htriv : ∀ y ∈ G.W, y ∈ zeroSet (glueIdealAlong N 𝔞 μ) →
      TrivialAt G.φ (glueIdealAlong N 𝔞 μ) y ∧ TrivialAt G.ψ (glueIdealAlong N 𝔞 μ) y)
    {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y)
    (hT : IsGeoTestTower (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T) :
    ∃ Φ, IsGlueingLiftAlong G T Φ ∧ IsTowerIso G.equiv (restrict G.dom T) (restrict G.cod T) Φ ∧
      MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : openPreimage T G.cod → Y)
          (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T)) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T G.dom → Y)
          (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T) ∧
      MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : openPreimage T G.cod → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T))
            (strictAlong T (N ∩ {x | u x = 0})))) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T G.dom → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T))
            (strictAlong T (N ∩ {x | v x = 0}))) ∧
      MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : openPreimage T G.cod → Y)
          (withN (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T)
            (strictAlong T (N ∩ {x | u x = 0})))) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T G.dom → Y)
          (withN (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T)
            (strictAlong T (N ∩ {x | v x = 0}))) ∧
      ∀ p : openPreimage T G.dom,
        (p : Y) ∈ (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T).cosupp → (Φ p : Y) = p := by
  obtain ⟨hJN, hJc, hJd⟩ := coeffHom_basic (μ := μ) h𝔞 hN
  have hW := wEquiv_coeffHom h𝔞 hN hμ
  have hH : IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) T := (hW.2 T).1.mp hT
  obtain ⟨Φ, hL, hI, hP⟩ := exists_isGlueingLiftAlong_isTowerIso G h𝔞 hN hμ htriv (ι := Unit)
    (fun _ => coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ))
    (fun _ => coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) (fun _ => hJN) (fun _ => hJc) (fun _ => hJN)
    (fun _ => hJc) (fun _ => pullback_restrict_coeffHom G h𝔞 hN hμ) T hH (fun _ => hT) (fun _ => hT)
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc T hT
  have hdT : 1 ≤ (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T).d := by
    rw [d_geoTransformAlong]; exact hJd
  refine ⟨Φ, hL, hI, hP (), lift_pullback_restrictedCoeff hL hNT hcT hdT hNT hcT hdT (hP ()),
    lift_pullback_restricted hL (hP ()), fun p hp => ?_⟩
  rw [(hW.2 T).2 hT] at hp
  exact hL.apply_eq_of_mem_cosupp G h𝔞 hN hμ hH p hp

/-- **Packaged from two tangent directions** (Step 1bb, with `hir:tower-isomorphism`): for tangent directions `u`, `v`
along `N` of `(𝔞|_N, μ)` on open sets containing `x ∈ cosupp(𝔞|_N, μ)` there are glueing data `G` along `N` with
`x ∈ U ∩ U'` such that along every multiple test blow-up `T` of `J̄` some lift `Φ_T` is the last-stage biholomorphism of
an isomorphism `T|_U ≅ T|_{U'}` over `G.equiv` with the four clauses of `exists_isTowerIso_coeffHom`. -/
theorem contact_independence_along_isTowerIso (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    {x : M} (hx : x ∈ cosupport n N 𝔞 μ) {U₁ U₂ : Set M} (hu : IsTangentDirectionAlong N 𝔞 μ U₁ u) (hxU₁ : x ∈ U₁)
    (hv : IsTangentDirectionAlong N 𝔞 μ U₂ v) (hxU₂ : x ∈ U₂) :
    ∃ G : GlueingDataAlong N 𝔞 μ u v, x ∈ G.dom ∧ x ∈ G.cod ∧
      ∀ {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y),
        IsGeoTestTower (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T →
        ∃ Φ, IsGlueingLiftAlong G T Φ ∧ IsTowerIso G.equiv (restrict G.dom T) (restrict G.cod T) Φ ∧
          MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : openPreimage T G.cod → Y)
              (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T))
                (strictAlong T (N ∩ {x | u x = 0})))) =
            MarkedIdeal.pullback (Subtype.val : openPreimage T G.dom → Y)
              (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T))
                (strictAlong T (N ∩ {x | v x = 0}))) ∧
          ∀ p : openPreimage T G.dom,
            (p : Y) ∈ (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T).cosupp →
              (Φ p : Y) = p := by
  obtain ⟨G, hxW, htriv⟩ := exists_glueingDataAlong_trivial h𝔞 hN hμ hx hu hxU₁ hv hxU₂
  obtain ⟨hxd, hxc⟩ := G.mem_dom_and_mem_cod hxW hx
  refine ⟨G, hxd, hxc, fun T hT => ?_⟩
  obtain ⟨Φ, hL, hI, -, hS, -, hfix⟩ := exists_isTowerIso_coeffHom G h𝔞 hN hμ htriv T hT
  exact ⟨Φ, hL, hI, hS, hfix⟩

end Glueing

end

end Hironaka.BlowupTowerIsomorphism
