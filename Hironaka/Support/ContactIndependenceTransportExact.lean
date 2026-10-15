/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.ContactIndependenceAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ContactIndependenceAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder
  TangentDirectionAlong HomogenizedIdealAlong HomogenizedGlueingAlong HomogenizedGlueingAlongTower
  GlueingTrivialAction HomogenizedGlueingLift HomogenizedGlueingLiftAlong CoefficientIdealRestriction
open HomogenizedGlueingTower (strictAlong)

noncomputable section

section Transport

open BlowupBiholomorphismLift MarkedIdealRestrictOpen BlowupTowers BlowupTowerTransforms MarkedIdeals
  MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism HomogenizedIdealAlongTower

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ} (G : GlueingDataAlong N 𝔞 μ u v)

/-- **(T1) The lifts transport the transforms of marked ideals that the glueing biholomorphism transports**
(Włodarczyk, Step 1bb: `φ_{pu}^*(U_p, J̄_p, E_p, μ̄) = φ_{pv}^*(U_p, J̄_p, E_p, μ̄)`, along `N`, for the lifts of
`le:homo` (4)).  Let `G` be glueing data along `N` acting trivially modulo `𝓓_N^{μ-1}(𝓗_N(𝔞))` at its zeros in `W`
(`HomogenizedGlueingLiftAlong.exists_glueingDataAlong_trivial`), and `(𝔫 i, 𝔫' i)` a family of pairs of marked ideals on `M`
with closed submanifolds and coherent ideals such that `G.equiv^*(𝔫 i|_{U'}) = 𝔫' i|_U`.  Along every tower `T` that is a
multiple test blow-up of `(𝓗_N(𝔞), μ)` and of every `𝔫 i` and `𝔫' i` there is one lift `Φ_T` of the glueing biholomorphism
(`IsGlueingLiftAlong`) with `Φ_T^*((𝔫 i)_T|_{cod}) = (𝔫' i)_T|_{dom}` for every `i`. -/
theorem exists_isGlueingLiftAlong_transport (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
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
      ∃ Φ, IsGlueingLiftAlong G T Φ ∧ ∀ i,
        MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : openPreimage T G.cod → Y)
          (geoTransformAlong (𝔫 i) T)) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T G.dom → Y) (geoTransformAlong (𝔫' i) T)
  | _, .refl, hT, _, _ => by
      obtain ⟨Φ, hL⟩ := exists_isGlueingLiftAlong G h𝔞 hN hμ htriv .refl hT
      have hΦ : Φ = G.equiv := lift_eq_equiv_refl G hL
      subst hΦ
      exact ⟨_, hL, hpb⟩
  | _, .step T C π hπ, hT, h𝔫T, h𝔫'T => by
      obtain ⟨Φ, hL, hP⟩ := exists_isGlueingLiftAlong_transport h𝔞 hN hμ htriv 𝔫 𝔫' hN𝔫 h𝔫 hN𝔫' h𝔫' hpb T hT.1
        (fun i => (h𝔫T i).1) (fun i => (h𝔫'T i).1)
      obtain ⟨hcorr, Φ₁, hΦ₁, hL₁⟩ := exists_isGlueingLiftAlong_step G h𝔞 hN hμ T C π hπ hT hL
      refine ⟨Φ₁, hL₁, fun i => ?_⟩
      obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong (hN𝔫 i) (h𝔫 i) T (h𝔫T i).1
      obtain ⟨hNT', hcT'⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong (hN𝔫' i) (h𝔫' i) T
        (h𝔫'T i).1
      exact pullback_lift_geoTransform_pair hπ Φ hcorr Φ₁ hΦ₁ hcT
        (HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNT hcT (h𝔫T i).2 hπ) hcT'
        (HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNT' hcT' (h𝔫'T i).2 hπ) (hP i)

/-- **(T1) for one preserved marked ideal**: if `G.equiv^*(𝔫|_{U'}) = 𝔫|_U`, then along every multiple test blow-up of
`(𝓗_N(𝔞), μ)` and of `𝔫` some lift `Φ_T` has `Φ_T^*(𝔫_T|_{cod}) = 𝔫_T|_{dom}`. -/
theorem exists_isGlueingLiftAlong_transport_one (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    (htriv : ∀ y ∈ G.W, y ∈ zeroSet (glueIdealAlong N 𝔞 μ) →
      TrivialAt G.φ (glueIdealAlong N 𝔞 μ) y ∧ TrivialAt G.ψ (glueIdealAlong N 𝔞 μ) y)
    (𝔫 : MarkedIdeal n M) (hN𝔫 : IsClosedSubmanifold n 𝔫.N) (h𝔫 : 𝔫.ideal.IsCoherent)
    (hpb : MarkedIdeal.pullback G.equiv (MarkedIdeal.pullback (Subtype.val : G.cod → M) 𝔫) =
      MarkedIdeal.pullback (Subtype.val : G.dom → M) 𝔫)
    {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y)
    (hT : IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) T) (h𝔫T : IsGeoTestTower 𝔫 T) :
    ∃ Φ, IsGlueingLiftAlong G T Φ ∧
      MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : openPreimage T G.cod → Y) (geoTransformAlong 𝔫 T)) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T G.dom → Y) (geoTransformAlong 𝔫 T) := by
  obtain ⟨Φ, hL, hP⟩ := exists_isGlueingLiftAlong_transport G h𝔞 hN hμ htriv (ι := Unit) (fun _ => 𝔫) (fun _ => 𝔫)
    (fun _ => hN𝔫) (fun _ => h𝔫) (fun _ => hN𝔫) (fun _ => h𝔫) (fun _ => hpb) T hT (fun _ => h𝔫T) (fun _ => h𝔫T)
  exact ⟨Φ, hL, hP ()⟩

end Transport

section Instance

open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen
  MarkedIdealEquivalence.MarkedIdeal HomogenizedIdealAlongTower BlowupRestrictOpen MarkedIdealBiholomorphism

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ}

/-- **(T3) The independence of the hypersurface of maximal contact inside `N`, for `J̄ = 𝓒_N(𝓗_N(𝔞), μ)`** (Włodarczyk,
Step 1bb, along `N`, `E = ∅`).  For glueing data `G` along `N` acting trivially modulo `𝓓_N^{μ-1}(𝓗_N(𝔞))` at its zeros in
`W`, along every multiple test blow-up `T` of `J̄` (equivalently of `(𝓗_N(𝔞), μ)`) there is a lift `Φ_T` of the glueing
biholomorphism (`IsGlueingLiftAlong`) with
1. `Φ_T^*(J̄_T|_{cod}) = J̄_T|_{dom}`;
2. `Φ_T^*(S_{u,T}|_{cod}) = S_{v,T}|_{dom}` for `S_{u,T} = 𝓒_{N_T}(J̄_T)|_{(N ∩ V(u))_T}`;
3. `Φ_T^*((J̄_T|_{(N ∩ V(u))_T})|_{cod}) = (J̄_T|_{(N ∩ V(v))_T})|_{dom}`;
4. `Φ_T` fixes `cosupp J̄_T` pointwise. -/
theorem exists_isGlueingLiftAlong_coeffHom (G : GlueingDataAlong N 𝔞 μ u v) (h𝔞 : 𝔞.IsCoherent)
    (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    (htriv : ∀ y ∈ G.W, y ∈ zeroSet (glueIdealAlong N 𝔞 μ) →
      TrivialAt G.φ (glueIdealAlong N 𝔞 μ) y ∧ TrivialAt G.ψ (glueIdealAlong N 𝔞 μ) y)
    {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y)
    (hT : IsGeoTestTower (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T) :
    ∃ Φ, IsGlueingLiftAlong G T Φ ∧
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
  obtain ⟨Φ, hL, hP⟩ := exists_isGlueingLiftAlong_transport_one G h𝔞 hN hμ htriv _ hJN hJc
    (pullback_restrict_coeffHom G h𝔞 hN hμ) T hH hT
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc T hT
  have hdT : 1 ≤ (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T).d := by
    rw [d_geoTransformAlong]; exact hJd
  refine ⟨Φ, hL, hP, lift_pullback_restrictedCoeff hL hNT hcT hdT hNT hcT hdT hP, lift_pullback_restricted hL hP,
    fun p hp => ?_⟩
  rw [(hW.2 T).2 hT] at hp
  exact hL.apply_eq_of_mem_cosupp G h𝔞 hN hμ hH p hp

end Instance
end
end Hironaka.ContactIndependenceAlong
