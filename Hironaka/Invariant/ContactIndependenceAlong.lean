/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.HomogenizedGlueingLiftAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupBiholomorphismLift
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Blowup.GlueingTrivialAction
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingAlongTower
import Hironaka.MarkedIdeal.HomogenizedGlueingLift
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.HomogenizedIdealAlongTower
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.MarkedIdeal.RestrictLe
import Hironaka.Coherence.VanishingIdealCoherent
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Independence of the hypersurface of maximal contact inside a submanifold, along multiple test blow-ups

Source: Włodarczyk 2005, Step 1bb ("We need to show that these invariants do not depend on the choice of `u`":
`φ_{pu}^*(U_p, J̄_p, E_p, μ̄) = φ_{pv}^*(U_p, J̄_p, E_p, μ̄)` and `φ_{pu}^{-1}(V(u)_p) = φ_{pv}^{-1}(V(v)_p)`), with
Lemma `le:homo` (4), `φ_u = φ` the glueing biholomorphism `U ≅ U'` along `N`; the lifts are those of
`HomogenizedGlueingLiftAlong`).

## One step

* `pullback_lift_geoTransform_pair`: under the lift `Φ₁` of `Φ : A ≅ B` along a blowup, if `Φ^*(𝔪|_B) = 𝔪'|_A`, then
  `Φ₁^*(𝔪_1|_{π⁻¹B}) = 𝔪'_1|_{π⁻¹A}` for the transforms (the form of `HomogenizedGlueingLift.pullback_lift_geoTransform`
  with two marked ideals).

## (T1) Transport

## (T2) The restricted coefficient ideals correspond

* `pullback_withN_of_pullback`, `pullback_withN_coeffMarkedAlong_of_pullback`: if `Φ^*(𝔪|_B) = 𝔪'|_A` and
  `Φ⁻¹(S ∩ B) = S' ∩ A`, then `Φ^*((𝔪|_S)|_B) = (𝔪'|_{S'})|_A` and `Φ^*((𝓒(𝔪)|_S)|_B) = (𝓒(𝔪')|_{S'})|_A` (coefficient
  ideals along the submanifolds of `𝔪`, `𝔪'`), for any biholomorphism `Φ : A ≅ B` of open sets.
* `lift_pullback_restrictedCoeff` ((b)): `Φ_T^*(S_{u,T}|_{cod}) = S_{v,T}|_{dom}` for `S_{u,T} = 𝓒_{N_T}(𝔫_T)|_{(N ∩
  V(u))_T}`; `lift_pullback_restricted`: the form without `𝓒`.

## (T3) The instance `J̄ = 𝓒_N(𝓗_N(𝔞), μ)`

* `one_le_coeffMarkedAlong_d`, `coeffHom_basic`: `J̄` has submanifold `N`, a coherent ideal and mark `≥ 1`;
  `pullback_restrict_coeffHom`: `G.equiv^*(J̄|_{U'}) = J̄|_U`; `wEquiv_coeffHom`: `J̄ ≃ (𝓗_N(𝔞), μ)`;
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ContactIndependenceAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder TangentDirectionAlong HomogenizedIdealAlong HomogenizedGlueingAlong HomogenizedGlueingAlongTower GlueingTrivialAction HomogenizedGlueingLift HomogenizedGlueingLiftAlong CoefficientIdealRestriction
open HomogenizedGlueingTower (strictAlong)

noncomputable section

/-! ### One step of the lift -/

section Step

open BlowupBiholomorphismLift MarkedIdealRestrictOpen MarkedIdealBiholomorphism BlowupStrictSubmanifold BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal BlowupRestrictOpen

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π) {A B : Opens Y}
  (Φ : CMfd.of (n := n) A ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) B)
  (hcorr : Φ ⁻¹' ((↑) ⁻¹' C : Set B) = ((↑) ⁻¹' C : Set A))
  (Φ₁ : CMfd.of (n := n) (preOpen hπ A) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
    CMfd.of (n := n) (preOpen hπ B))
  (hΦ₁ : ∀ p : preOpen hπ A, π (Φ₁ p : Z) = (Φ (restrictMap hπ A p) : Y))
include hcorr hΦ₁

/-- **Transforms of two marked ideals correspond under the lift**: if `Φ^*(𝔪|_B) = 𝔪'|_A`, then
`Φ₁^*((𝔪_1)|_{π⁻¹B}) = (𝔪'_1)|_{π⁻¹A}` for the transforms `𝔪_1`, `𝔪'_1` of `𝔪`, `𝔪'` along `π` (coherent ideals, `C` a
closed submanifold). -/
theorem pullback_lift_geoTransform_pair {m m' : MarkedIdeal n Y} (hm : m.ideal.IsCoherent)
    (hc : (m.geoTransform C π).ideal.IsCoherent) (hm' : m'.ideal.IsCoherent)
    (hc' : (m'.geoTransform C π).ideal.IsCoherent)
    (hpb : MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : B → Y) m) =
      MarkedIdeal.pullback (Subtype.val : A → Y) m') :
    MarkedIdeal.pullback Φ₁ (MarkedIdeal.pullback (Subtype.val : preOpen hπ B → Z) (m.geoTransform C π)) =
      MarkedIdeal.pullback (Subtype.val : preOpen hπ A → Z) (m'.geoTransform C π) := by
  have hmB : (MarkedIdeal.pullback (Subtype.val : B → Y) m).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hm
  have hICB : (vanishingIdeal (n := n) ((↑) ⁻¹' C : Set B)).IsCoherent :=
    VanishingIdealCoherent.isCoherent_vanishingIdeal (isClosedSubmanifold_preimage_val hπ.1 B)
  have hBr : MarkedIdeal.pullback (Subtype.val : preOpen hπ B → Z) (m.geoTransform C π) =
      (MarkedIdeal.pullback (Subtype.val : B → Y) m).geoTransform ((↑) ⁻¹' C : Set B) (restrictMap hπ B) :=
    (geoTransform_pullback_val hm hπ hc B (preOpen hπ B).isOpen).symm
  have hAr : MarkedIdeal.pullback (Subtype.val : preOpen hπ A → Z) (m'.geoTransform C π) =
      (MarkedIdeal.pullback (Subtype.val : A → Y) m').geoTransform ((↑) ⁻¹' C : Set A) (restrictMap hπ A) :=
    (geoTransform_pullback_val hm' hπ hc' A (preOpen hπ A).isOpen).symm
  have hcB : ((MarkedIdeal.pullback (Subtype.val : B → Y) m).geoTransform ((↑) ⁻¹' C : Set B)
      (restrictMap hπ B)).ideal.IsCoherent := by
    rw [← hBr]
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hc
  have hnat := MarkedIdeal.geoTransform_pullback Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply
    Φ.symm_apply_apply (MarkedIdeal.pullback (Subtype.val : B → Y) m) hmB ((↑) ⁻¹' C : Set B)
    (Φ.contMDiff.comp (isBlowupAlong_restrictMap hπ A).contMDiff)
  have hsimp : (Φ.symm ∘ Φ ∘ restrictMap hπ A) = restrictMap hπ A := funext fun p => by simp
  rw [hBr, hAr, ← geoTransform_comp_diffeo Φ₁ _ hmB _ hICB (isBlowupAlong_restrictMap hπ B).contMDiff hcB,
    restrictMap_comp_lift hπ Φ hcorr Φ₁ hΦ₁, ← hnat, hpb, hcorr, hsimp]

end Step

section LiftStep

open BlowupBiholomorphismLift MarkedIdealRestrictOpen BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupControlledTransform HomogenizedIdealAlongTower

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ} (G : GlueingDataAlong N 𝔞 μ u v)

/-- **One step of the lift along `N`** (the induction step of `HomogenizedGlueingLiftAlong.exists_isGlueingLiftAlong`):
if `Φ` is a lift along `T` and the tower `T` followed by the blowup `π` along `C` is a multiple test blow-up of
`(𝓗_N(𝔞), μ)`, then `Φ⁻¹(C ∩ cod) = C ∩ dom` and there is a lift `Φ₁` along the longer tower lifting `Φ` (`π ∘ Φ₁ =
Φ ∘ π`). -/
theorem exists_isGlueingLiftAlong_step (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    {Y Z : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (hT : IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) (.step T C π hπ))
    {Φ : CMfd.of (n := n) (openPreimage T G.dom) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T G.cod)} (hL : IsGlueingLiftAlong G T Φ) :
    Φ ⁻¹' ((↑) ⁻¹' C : Set (openPreimage T G.cod)) = ((↑) ⁻¹' C : Set (openPreimage T G.dom)) ∧
    ∃ Φ₁ : CMfd.of (n := n) (preOpen hπ (openPreimage T G.dom)) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (preOpen hπ (openPreimage T G.cod)),
      (∀ p : preOpen hπ (openPreimage T G.dom), π (Φ₁ p : Z) = (Φ (restrictMap hπ _ p) : Y)) ∧
      IsGlueingLiftAlong G (.step T C π hπ) Φ₁ := by
  have hT0 : IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) T := hT.1
  have hC : (geoTransformAlong (homogenizedMarkedAlong N 𝔞 μ) T).IsAdmissibleCentre C := hT.2
  have hH : (homogenizedMarkedAlong N 𝔞 μ).ideal.IsCoherent := isCoherent_homogenizedIdealAlong h𝔞 hN μ
  obtain ⟨-, -, -, hNT, hcohH, -, -⟩ := inclusions_tower_along (X := CMfd.of (n := n) M)
    (homogenizedMarkedAlong N 𝔞 μ) hN hH (j := 0) (Nat.zero_le _) T hT0
  obtain ⟨-, -, hzero, hcohJ, hNJ⟩ := glue_tower (X := CMfd.of (n := n) M) h𝔞 hN hμ T hT0
  set J := (geoTransformAlong (glueMarkedAlong N 𝔞 μ) T).ideal with hJdef
  have hCzero : C ⊆ zeroSet J := fun y hy => hzero (hC.2.1 hy)
  have hJ' : (geoTransformAlong (glueMarkedAlong N 𝔞 μ) (.step T C π hπ)).ideal = controlledTransform hπ J 1 := by
    rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hNJ hcohJ hπ, d_geoTransformAlong]
    rfl
  have hcorr := hL.preimage_inter_eq G hCzero
  refine ⟨hcorr, ?_⟩
  obtain ⟨Φ₁, hΦ₁⟩ := exists_lift hπ Φ hcorr
  have hcorr' : Φ.symm ⁻¹' ((↑) ⁻¹' C : Set (openPreimage T G.dom)) =
      ((↑) ⁻¹' C : Set (openPreimage T G.cod)) := by
    ext q
    have := congrArg (fun S => Φ.symm q ∈ S) hcorr
    simp only [mem_preimage, Diffeomorph.apply_symm_apply] at this
    exact Iff.of_eq this.symm
  have hΦ₁s : ∀ q : preOpen hπ (openPreimage T G.cod),
      π (Φ₁.symm q).1 = (Φ.symm (restrictMap hπ _ q) : _) := by
    intro q
    have h1 := hΦ₁ (Φ₁.symm q)
    rw [Diffeomorph.apply_symm_apply] at h1
    have h2 : restrictMap hπ _ q = Φ (restrictMap hπ _ (Φ₁.symm q)) :=
      Subtype.ext h1
    rw [h2, Diffeomorph.symm_apply_apply]
    rfl
  have hcohT' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNT hcohH hC hπ
  refine ⟨Φ₁, hΦ₁, fun p => ?_, fun p hp => ?_, fun q hq => ?_, ?_, ?_, ?_⟩
  · change T.proj (π (Φ₁ p)) = G.φ (T.proj (π p))
    rw [hΦ₁ p]
    exact hL.proj_eq _
  · rw [hJ'] at hp ⊢
    have hpz : π p ∈ zeroSet J := mem_zeroSet_of_mem_zeroSet_controlledTransform hπ hcohJ hp
    have hA : π p ∈ openPreimage T G.dom := p.2
    refine trivialAt_lift hπ hcohJ hCzero hp (eventually_mdifferentiableAt_extendMap Φ₁.contMDiff p) ?_ ?_
      (hL.trivial ⟨π p, hA⟩ hpz)
    · filter_upwards [(preOpen hπ (openPreimage T G.dom)).isOpen.mem_nhds p.2] with q hq
      have e1 : extendMap Φ₁ q = (Φ₁ ⟨q, hq⟩ : _) := extendMap_of_mem _ hq
      have e2 : extendMap Φ (π q) = (Φ ⟨π q, hq⟩ : _) :=
        extendMap_of_mem (A := openPreimage T G.dom) (B := openPreimage T G.cod) Φ
          (show π q ∈ openPreimage T G.dom from hq)
      exact (congrArg π e1).trans ((hΦ₁ ⟨q, hq⟩).trans e2.symm)
    · filter_upwards [(openPreimage T G.dom).isOpen.mem_nhds hA] with y hy hyC
      rw [extendMap_of_mem Φ hy]
      intro hΦy
      apply hyC
      have : (⟨y, hy⟩ : openPreimage T G.dom) ∈ Φ ⁻¹' ((↑) ⁻¹' C : Set (openPreimage T G.cod)) := hΦy
      rw [hcorr] at this
      exact this
  · rw [hJ'] at hq ⊢
    have hqz : π q ∈ zeroSet J := mem_zeroSet_of_mem_zeroSet_controlledTransform hπ hcohJ hq
    have hB : π q ∈ openPreimage T G.cod := q.2
    refine trivialAt_lift hπ hcohJ hCzero hq (eventually_mdifferentiableAt_extendMap Φ₁.symm.contMDiff q) ?_ ?_
      (hL.trivial_symm ⟨π q, hB⟩ hqz)
    · filter_upwards [(preOpen hπ (openPreimage T G.cod)).isOpen.mem_nhds q.2] with r hr
      have e1 : extendMap Φ₁.symm r = (Φ₁.symm ⟨r, hr⟩ : _) := extendMap_of_mem _ hr
      have e2 : extendMap Φ.symm (π r) = (Φ.symm ⟨π r, hr⟩ : _) :=
        extendMap_of_mem (A := openPreimage T G.cod) (B := openPreimage T G.dom) Φ.symm
          (show π r ∈ openPreimage T G.cod from hr)
      exact (congrArg π e1).trans ((hΦ₁s ⟨r, hr⟩).trans e2.symm)
    · filter_upwards [(openPreimage T G.cod).isOpen.mem_nhds hB] with y hy hyC
      rw [extendMap_of_mem Φ.symm hy]
      intro hΦy
      apply hyC
      have : (⟨y, hy⟩ : openPreimage T G.cod) ∈
          Φ.symm ⁻¹' ((↑) ⁻¹' C : Set (openPreimage T G.dom)) := hΦy
      rw [hcorr'] at this
      exact this
  · exact pullback_lift_geoTransform hπ Φ hcorr Φ₁ hΦ₁ hcohH hcohT' hL.pullback_eq
  · exact preimage_lift_geoStrictTransform hπ Φ hcorr Φ₁ hΦ₁ hL.strict_eq
  · exact preimage_lift_geoStrictTransform hπ Φ hcorr Φ₁ hΦ₁ hL.strict_eq_N

/-- **Every lift along the empty tower is the glueing biholomorphism.** -/
theorem lift_eq_equiv_refl
    {Φ : CMfd.of (n := n) (openPreimage (BlowupTower.refl : BlowupTower (CMfd.of (n := n) M) (CMfd.of (n := n) M)) G.dom)
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage (BlowupTower.refl : BlowupTower (CMfd.of (n := n) M) (CMfd.of (n := n) M)) G.cod)}
    (hL : IsGlueingLiftAlong G .refl Φ) : Φ = G.equiv :=
  Diffeomorph.ext fun p => Subtype.ext (hL.proj_eq p)

end LiftStep

/-! ### (T2) The restricted coefficient ideals correspond -/

section Restricted

open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupRestrictOpen

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {A B : Opens Y} (Φ : CMfd.of (n := n) A ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) B)

/-- **Restrictions correspond**: if `Φ^*(𝔪|_B) = 𝔪'|_A` and `Φ⁻¹(S ∩ B) = S' ∩ A`, then `Φ^*((𝔪|_S)|_B) = (𝔪'|_{S'})|_A`. -/
theorem pullback_withN_of_pullback {m m' : MarkedIdeal n Y}
    (hpb : MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : B → Y) m) =
      MarkedIdeal.pullback (Subtype.val : A → Y) m')
    {S S' : Set Y} (hS : Φ ⁻¹' ((↑) ⁻¹' S : Set B) = ((↑) ⁻¹' S' : Set A)) :
    MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : B → Y) (withN m S)) =
      MarkedIdeal.pullback (Subtype.val : A → Y) (withN m' S') := by
  change withN (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : B → Y) m))
      (Φ ⁻¹' ((↑) ⁻¹' S : Set B)) = withN (MarkedIdeal.pullback (Subtype.val : A → Y) m') ((↑) ⁻¹' S' : Set A)
  rw [hpb, hS]

/-- **Restricted coefficient ideals correspond**: if `Φ^*(𝔪|_B) = 𝔪'|_A` (closed submanifolds, coherent ideals, marks
`≥ 1`) and `Φ⁻¹(S ∩ B) = S' ∩ A`, then `Φ^*((𝓒(𝔪)|_S)|_B) = (𝓒(𝔪')|_{S'})|_A`, the coefficient ideals being taken along the
submanifolds of `𝔪`, `𝔪'` (`𝓒_N` commutes with restriction to open sets and with biholomorphisms,
`HomogenizedIdealAlong.pullback_val_coeffMarkedAlong`, `pullback_coeffMarkedAlong_of_inverse`). -/
theorem pullback_withN_coeffMarkedAlong_of_pullback {m m' : MarkedIdeal n Y} (hNm : IsClosedSubmanifold n m.N)
    (hm : m.ideal.IsCoherent) (hd : 1 ≤ m.d) (hNm' : IsClosedSubmanifold n m'.N) (hm' : m'.ideal.IsCoherent)
    (hd' : 1 ≤ m'.d)
    (hpb : MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : B → Y) m) =
      MarkedIdeal.pullback (Subtype.val : A → Y) m')
    {S S' : Set Y} (hS : Φ ⁻¹' ((↑) ⁻¹' S : Set B) = ((↑) ⁻¹' S' : Set A)) :
    MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : B → Y) (withN (coeffMarkedAlong m) S)) =
      MarkedIdeal.pullback (Subtype.val : A → Y) (withN (coeffMarkedAlong m') S') := by
  refine pullback_withN_of_pullback Φ ?_ hS
  have hmB : (MarkedIdeal.pullback (Subtype.val : B → Y) m).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hm
  have hNB : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : B → Y) m).N :=
    isClosedSubmanifold_preimage_val hNm B
  rw [pullback_val_coeffMarkedAlong B m hm hNm hd,
    pullback_coeffMarkedAlong_of_inverse Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply Φ.symm_apply_apply _ hmB hNB hd,
    hpb, pullback_val_coeffMarkedAlong A m' hm' hNm' hd']

end Restricted

section RestrictedLift

open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen MarkedIdealBiholomorphism

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ} {G : GlueingDataAlong N 𝔞 μ u v}
  {Y : CMfd.{u} n} {T : BlowupTower (CMfd.of (n := n) M) Y}
  {Φ : CMfd.of (n := n) (openPreimage T G.dom) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
    CMfd.of (n := n) (openPreimage T G.cod)}

/-- **(T2) The restricted coefficient ideals correspond under the lifts** ((b); Włodarczyk, Step 1bb): if `Φ_T` is a
lift along `T` transporting `𝔪` to `𝔪'` (`Φ_T^*(𝔪|_{cod}) = 𝔪'|_{dom}`; for instance `𝔪 = 𝔪' = 𝔫_T`, (T1)), then for
`S_{u,T}(𝔪) = 𝓒_{N_T}(𝔪)|_{(N ∩ V(u))_T}` (the coefficient ideal along the submanifold of `𝔪`, restricted to the
strict transform of the hypersurface of maximal contact `N ∩ V(u)`): `Φ_T^*(S_{u,T}(𝔪)|_{cod}) =
S_{v,T}(𝔪')|_{dom}`. -/
theorem lift_pullback_restrictedCoeff (hL : IsGlueingLiftAlong G T Φ) {m m' : MarkedIdeal n Y}
    (hNm : IsClosedSubmanifold n m.N) (hm : m.ideal.IsCoherent) (hd : 1 ≤ m.d) (hNm' : IsClosedSubmanifold n m'.N)
    (hm' : m'.ideal.IsCoherent) (hd' : 1 ≤ m'.d)
    (hpb : MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : openPreimage T G.cod → Y) m) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T G.dom → Y) m') :
    MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : openPreimage T G.cod → Y)
        (withN (coeffMarkedAlong m) (strictAlong T (N ∩ {x | u x = 0})))) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T G.dom → Y)
        (withN (coeffMarkedAlong m') (strictAlong T (N ∩ {x | v x = 0}))) :=
  pullback_withN_coeffMarkedAlong_of_pullback Φ hNm hm hd hNm' hm' hd' hpb hL.strict_eq_N

/-- **(T2) without `𝓒`**: `Φ_T^*((𝔪|_{(N ∩ V(u))_T})|_{cod}) = (𝔪'|_{(N ∩ V(v))_T})|_{dom}`. -/
theorem lift_pullback_restricted (hL : IsGlueingLiftAlong G T Φ) {m m' : MarkedIdeal n Y}
    (hpb : MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : openPreimage T G.cod → Y) m) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T G.dom → Y) m') :
    MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : openPreimage T G.cod → Y)
        (withN m (strictAlong T (N ∩ {x | u x = 0})))) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T G.dom → Y) (withN m' (strictAlong T (N ∩ {x | v x = 0}))) :=
  pullback_withN_of_pullback Φ hpb hL.strict_eq_N

end RestrictedLift

/-! ### (T3) The instance `J̄ = 𝓒_N(𝓗_N(𝔞), μ)` -/

section Instance

open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen MarkedIdealEquivalence.MarkedIdeal HomogenizedIdealAlongTower BlowupRestrictOpen MarkedIdealBiholomorphism

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ}

/-- **The mark of a coefficient ideal along `N` is positive**: `μ_𝓒 = ∏_{j<d} (d - j) ≥ 1` (an empty product for `d = 0`). -/
theorem one_le_coeffMarkedAlong_d (𝔪 : MarkedIdeal n M) : 1 ≤ (coeffMarkedAlong 𝔪).d := by
  show 1 ≤ (Finset.range 𝔪.d).prod fun j => 𝔪.d - j
  exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun j hj => by
    have := Finset.mem_range.mp hj
    omega)

/-- **`J̄ = 𝓒_N(𝓗_N(𝔞), μ)` has submanifold `N`, a coherent ideal and mark `≥ 1`.** -/
theorem coeffHom_basic (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) :
    IsClosedSubmanifold n (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)).N ∧
      (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)).ideal.IsCoherent ∧
      1 ≤ (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)).d :=
  ⟨hN, isCoherent_coeffMarkedAlong (𝔪 := homogenizedMarkedAlong N 𝔞 μ) (isCoherent_homogenizedIdealAlong h𝔞 hN μ) hN,
    one_le_coeffMarkedAlong_d (homogenizedMarkedAlong N 𝔞 μ)⟩

/-- **`J̄ ≃ (𝓗_N(𝔞), μ)`** (`HomogenizedIdealAlongTower.coeffAlong_wEquiv`): the same multiple test blow-ups, with equal
cosupports along them. -/
theorem wEquiv_coeffHom (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) :
    WEquiv (X := CMfd.of (n := n) M) (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ))
      (homogenizedMarkedAlong N 𝔞 μ) :=
  coeffAlong_wEquiv (X := CMfd.of (n := n) M) (homogenizedMarkedAlong N 𝔞 μ) hN
    (isCoherent_homogenizedIdealAlong h𝔞 hN μ) hμ

/-- **The glueing biholomorphism transports `J̄`**: `G.equiv^*(J̄|_{U'}) = J̄|_U` (`𝓒_N` commutes with restriction to open
sets and with biholomorphisms, and `G.equiv^*((𝓗_N(𝔞), μ)|_{U'}) = (𝓗_N(𝔞), μ)|_U`). -/
theorem pullback_restrict_coeffHom (G : GlueingDataAlong N 𝔞 μ u v) (h𝔞 : 𝔞.IsCoherent)
    (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) :
    MarkedIdeal.pullback G.equiv
        (MarkedIdeal.pullback (Subtype.val : G.cod → M) (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ))) =
      MarkedIdeal.pullback (Subtype.val : G.dom → M) (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) := by
  have hH : (homogenizedMarkedAlong N 𝔞 μ).ideal.IsCoherent := isCoherent_homogenizedIdealAlong h𝔞 hN μ
  have hHB : (MarkedIdeal.pullback (Subtype.val : G.cod → M) (homogenizedMarkedAlong N 𝔞 μ)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hH
  have hNB : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : G.cod → M) (homogenizedMarkedAlong N 𝔞 μ)).N :=
    isClosedSubmanifold_preimage_val hN G.cod
  rw [pullback_val_coeffMarkedAlong G.cod _ hH hN hμ,
    pullback_coeffMarkedAlong_of_inverse G.equiv.contMDiff G.equiv.symm.contMDiff G.equiv.apply_symm_apply
      G.equiv.symm_apply_apply _ hHB hNB hμ,
    G.pullback_restrict h𝔞 hN, pullback_val_coeffMarkedAlong G.dom _ hH hN hμ]

end Instance

end

end Hironaka.ContactIndependenceAlong
