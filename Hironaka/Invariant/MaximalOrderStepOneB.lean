import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.ResolutionInvariantExt

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1b of the maximal-order case: the value does not depend on the hypersurface of maximal contact

Blueprint `hir:step-one-b-independence` (`blueprint/src/hironaka.tex`, Hironaka phase H4, a piece of
`hir:maximal-order-step`).  Source: Włodarczyk 2005 (arXiv `hiron.tex`), Proposition `pr:resol`, Step 1bb: the
invariant at a point is computed on a hypersurface of maximal contact, and by the Glueing Lemma `le:homo` it does not
depend on the choice of the hypersurface ("`φ_{pu}^*(..) = φ_{pv}^*(..)`" along the part of the resolution after the
hypersurface is chosen).

Let `J̄ = 𝓒_N(𝓗_N(𝔞), μ)` (`stepOneMarked`) be the marked ideal Step 1 works with, `u` a tangent direction of
`(𝔞|_N, μ)` on an open set, `T₀` the stage at which Step 1b starts and `T₁` the rest of the segment.  Step 1b evaluates
the inductive invariant (in dimension `≤ k - 1`) on `𝓢_{u,T₀}|_W = (Y, strict transform of N ∩ V(u), E, 𝓒(J̄_{T₀}), μ_𝓒)|_W`
(`contactMarked`) along the restricted tail `T₁|_{T₀⁻¹W}`.  TN23's tail form of the glueing lifts
(`BlowupTowerIsoTail.contact_independence_along_tail`) gives, for two tangent directions `u`, `v` at `x`, an isomorphism
of the restricted tails over the lift `Φ₀` of the glueing biholomorphism with `Φ₀^*𝓢_u = 𝓢_v` and fixing the cosupport
pointwise; property (6) of the inductive invariant (`ResolutionInvariant.towerIso`) then identifies the two values.

## Main results

* `stepOneMarked`, `contactMarked`: abbreviations for `J̄` and `𝓢_{u,T₀}|_W` (the forms TN23's tail theorem transports);
* `inv_contactMarked_eq`: **Step 1b's value does not depend on the tangent direction** -- at every point of the
  cosupport of `J̄_{T₀ T₁}` over the glueing neighbourhood, the inductive invariants of `𝓢_v` and of `𝓢_u` along the
  restricted tails agree, provided `𝓢_u|_{T₀⁻¹U}` lies in the domain, the restricted tail is one of its multiple test
  blow-ups and the point lies in its cosupport (the hypotheses the Step 1b assembly supplies from the contact equivalence
  at `T₀` and the domain of the restriction);
* `inv_contactMarked_eq_ext`: the same for the second form of the inductive invariant
  (`ResolutionInvariantExt.ResolutionInvariant`, properties along canonical segments), with "the restricted tail is a
  canonical segment of `𝓢_u|_{T₀⁻¹U}`" in place of "a multiple test blow-up of it" (the first form `inv_contactMarked_eq`
  is kept; it concerns the superseded `ResolutionInvariantSpec.ResolutionInvariant`).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u w

namespace Hironaka.MaximalOrderStepOneB

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HomogenizedIdealAlong CoefficientIdealRestriction TangentDirectionAlong BlowupTowerIsomorphism
  HomogenizedGlueingAlongTower BlowupTowerIsoTail ResolutionInvariantSpec
open HomogenizedGlueingTower (strictAlong)

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The marked ideal of Step 1**: `J̄ = 𝓒_N(𝓗_N(𝔞), μ)`, the coefficient marked ideal of the homogenized marked ideal
along `N`. -/
abbrev stepOneMarked (N : Set M) (𝔞 : GermIdeal n M) (μ : ℕ) : MarkedIdeal n M :=
  coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)

/-- **The marked ideal of Step 1b on an open set of the stage `T₀`**: `𝓢_{u,T₀}|_W`, the coefficient marked ideal of
`J̄_{T₀}` on the strict transform along `T₀` of `N ∩ V(u)`, restricted to the open `W` of the last stage of `T₀`. -/
def contactMarked (N : Set M) (𝔞 : GermIdeal n M) (μ : ℕ) (u : M → ℂ) {Y : CMfd.{u} n}
    (T₀ : BlowupTower (CMfd.of (n := n) M) Y) (W : Opens Y) : MarkedIdeal n W :=
  MarkedIdeal.pullback (Subtype.val : W → Y)
    (withN (coeffMarkedAlong (geoTransformAlong (stepOneMarked N 𝔞 μ) T₀)) (strictAlong T₀ (N ∩ {x | u x = 0})))

/-- **Step 1b's value does not depend on the tangent direction** (Włodarczyk, Step 1bb): for tangent directions `u`, `v`
of `(𝔞|_N, μ)` at a point `x` of the cosupport there is a glueing neighbourhood (`GlueingDataAlong`, with `x` in its domain
`U'` and codomain `U`) such that, for every segment `T₀ T₁` which is a multiple test blow-up of `J̄`, at every point `p` of
the cosupport of `J̄_{T₀ T₁}` over `U'` the inductive invariant `R` of `𝓢_v|_{T₀⁻¹U'}` along `T₁|_{T₀⁻¹U'}` equals that of
`𝓢_u|_{T₀⁻¹U}` along `T₁|_{T₀⁻¹U}` at the same point -- provided `𝓢_u|_{T₀⁻¹U}` lies in the domain of `R`, the restricted
tail is one of its multiple test blow-ups, and the point lies in its cosupport.  Proof: TN23's isomorphism of the
restricted tails over the lift `Φ₀` (it fixes the cosupport of `J̄_{T₀ T₁}` pointwise and `Φ₀^*𝓢_u = 𝓢_v`) and
property (6). -/
theorem inv_contactMarked_eq {k : ℕ} {Λ : Type w} [LinearOrder Λ] (R : ResolutionInvariant.{u, w} n k Λ)
    {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    {x : M} (hx : x ∈ cosupport n N 𝔞 μ) {u v : M → ℂ} {U₁ U₂ : Set M}
    (hu : IsTangentDirectionAlong N 𝔞 μ U₁ u) (hxU₁ : x ∈ U₁)
    (hv : IsTangentDirectionAlong N 𝔞 μ U₂ v) (hxU₂ : x ∈ U₂) :
    ∃ G : GlueingDataAlong N 𝔞 μ u v, x ∈ G.dom ∧ x ∈ G.cod ∧
      ∀ {Y Z : CMfd.{u} n} (T₀ : BlowupTower (CMfd.of (n := n) M) Y) (T₁ : BlowupTower Y Z),
        IsGeoTestTower (stepOneMarked N 𝔞 μ) (T₀.append T₁) →
        IsInvDomain k (contactMarked N 𝔞 μ u T₀ (openPreimage T₀ G.cod)) →
        IsGeoTestTower (contactMarked N 𝔞 μ u T₀ (openPreimage T₀ G.cod)) (restrict (openPreimage T₀ G.cod) T₁) →
        ∀ (p : openPreimage T₁ (openPreimage T₀ G.dom)) (q : openPreimage T₁ (openPreimage T₀ G.cod)),
          (p : Z) ∈ (geoTransformAlong (stepOneMarked N 𝔞 μ) (T₀.append T₁)).cosupp → (q : Z) = p →
          q ∈ (geoTransformAlong (contactMarked N 𝔞 μ u T₀ (openPreimage T₀ G.cod))
            (restrict (openPreimage T₀ G.cod) T₁)).cosupp →
          R.inv (contactMarked N 𝔞 μ v T₀ (openPreimage T₀ G.dom)) (restrict (openPreimage T₀ G.dom) T₁) p =
            R.inv (contactMarked N 𝔞 μ u T₀ (openPreimage T₀ G.cod)) (restrict (openPreimage T₀ G.cod) T₁) q := by
  obtain ⟨G, hxd, hxc, hG⟩ := contact_independence_along_tail h𝔞 hN hμ hx hu hxU₁ hv hxU₂
  refine ⟨G, hxd, hxc, fun T₀ T₁ hT hdom htest p q hp hqp hq => ?_⟩
  obtain ⟨Φ₀, χ, -, hχ, hS₀, hfix⟩ := hG T₀ T₁ hT
  have hχq : χ p = q := Subtype.ext ((hfix p hp).trans hqp.symm)
  have hχp : χ p ∈ (geoTransformAlong (contactMarked N 𝔞 μ u T₀ (openPreimage T₀ G.cod))
      (restrict (openPreimage T₀ G.cod) T₁)).cosupp := by
    rw [hχq]
    exact hq
  have key := R.towerIso Φ₀ (contactMarked N 𝔞 μ u T₀ (openPreimage T₀ G.cod)) hdom _ _ χ hχ htest p hχp
  have hpull : MarkedIdeal.pullback Φ₀ (contactMarked N 𝔞 μ u T₀ (openPreimage T₀ G.cod)) =
      contactMarked N 𝔞 μ v T₀ (openPreimage T₀ G.dom) := hS₀
  rw [hpull, hχq] at key
  exact key

/-- **Step 1b's value does not depend on the tangent direction**, for the second form of the inductive invariant
(`ResolutionInvariantExt.ResolutionInvariant`, properties along canonical segments): as `inv_contactMarked_eq`, with the
hypothesis that the restricted tail `T₁|_{T₀⁻¹U}` is a canonical segment of `𝓢_u|_{T₀⁻¹U}` (which is how the Step 1b
assembly reaches it: near the point, the centres of the outer canonical segment are empty or the maximum loci of the
second component of the value). -/
theorem inv_contactMarked_eq_ext {k : ℕ} {Λ : Type w} [LinearOrder Λ]
    (R : ResolutionInvariantExt.ResolutionInvariant.{u, w} n k Λ)
    {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    {x : M} (hx : x ∈ cosupport n N 𝔞 μ) {u v : M → ℂ} {U₁ U₂ : Set M}
    (hu : IsTangentDirectionAlong N 𝔞 μ U₁ u) (hxU₁ : x ∈ U₁)
    (hv : IsTangentDirectionAlong N 𝔞 μ U₂ v) (hxU₂ : x ∈ U₂) :
    ∃ G : GlueingDataAlong N 𝔞 μ u v, x ∈ G.dom ∧ x ∈ G.cod ∧
      ∀ {Y Z : CMfd.{u} n} (T₀ : BlowupTower (CMfd.of (n := n) M) Y) (T₁ : BlowupTower Y Z),
        IsGeoTestTower (stepOneMarked N 𝔞 μ) (T₀.append T₁) →
        IsInvDomain k (contactMarked N 𝔞 μ u T₀ (openPreimage T₀ G.cod)) →
        IsCanonical (contactMarked N 𝔞 μ u T₀ (openPreimage T₀ G.cod))
          (R.inv (contactMarked N 𝔞 μ u T₀ (openPreimage T₀ G.cod))) (restrict (openPreimage T₀ G.cod) T₁) →
        ∀ (p : openPreimage T₁ (openPreimage T₀ G.dom)) (q : openPreimage T₁ (openPreimage T₀ G.cod)),
          (p : Z) ∈ (geoTransformAlong (stepOneMarked N 𝔞 μ) (T₀.append T₁)).cosupp → (q : Z) = p →
          q ∈ (geoTransformAlong (contactMarked N 𝔞 μ u T₀ (openPreimage T₀ G.cod))
            (restrict (openPreimage T₀ G.cod) T₁)).cosupp →
          R.inv (contactMarked N 𝔞 μ v T₀ (openPreimage T₀ G.dom)) (restrict (openPreimage T₀ G.dom) T₁) p =
            R.inv (contactMarked N 𝔞 μ u T₀ (openPreimage T₀ G.cod)) (restrict (openPreimage T₀ G.cod) T₁) q := by
  obtain ⟨G, hxd, hxc, hG⟩ := contact_independence_along_tail h𝔞 hN hμ hx hu hxU₁ hv hxU₂
  refine ⟨G, hxd, hxc, fun T₀ T₁ hT hdom hcan p q hp hqp hq => ?_⟩
  obtain ⟨Φ₀, χ, -, hχ, hS₀, hfix⟩ := hG T₀ T₁ hT
  have hχq : χ p = q := Subtype.ext ((hfix p hp).trans hqp.symm)
  have hχp : χ p ∈ (geoTransformAlong (contactMarked N 𝔞 μ u T₀ (openPreimage T₀ G.cod))
      (restrict (openPreimage T₀ G.cod) T₁)).cosupp := by
    rw [hχq]
    exact hq
  have key := R.towerIso Φ₀ (contactMarked N 𝔞 μ u T₀ (openPreimage T₀ G.cod)) hdom _ _ χ hχ hcan p hχp
  have hpull : MarkedIdeal.pullback Φ₀ (contactMarked N 𝔞 μ u T₀ (openPreimage T₀ G.cod)) =
      contactMarked N 𝔞 μ v T₀ (openPreimage T₀ G.dom) := hS₀
  rw [hpull, hχq] at key
  exact key

end

end Hironaka.MaximalOrderStepOneB
