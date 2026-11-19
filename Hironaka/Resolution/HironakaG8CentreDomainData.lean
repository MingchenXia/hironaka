import Hironaka.Resolution.HironakaG8PairDomainOpen
/-! # Centrewise data from a common domain open -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8CentreDomainData
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  DivisorExponentAlong GermIdealOrder ResolutionInvariantSpec
open HironakaStepOneZeroContactRemainderGlueing (isNonzeroAlongAt_pullback_val_iff)

/-- An above-mark centre in a common invariant-domain open automatically has
both nonvanishing conditions required by the directrix trace comparison. -/
theorem centre_data_of_domain_open
    {n : ℕ} {X : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (hP : P.IsWellFormed) (hQ : Q.IsWellFormed) (hcos : P.cosupp = Q.cosupp)
    {C : Set X} (hC : C ⊆ P.cosupp) (G : Opens X)
    (hPG : IsInvDomain n (MarkedIdeal.pullback (Subtype.val : G → X) P))
    (hQG : IsInvDomain n (MarkedIdeal.pullback (Subtype.val : G → X) Q))
    {x : X} (hxG : x ∈ G)
    (habove : ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ cosupport n P.N P.ideal (P.d+1)) :
    ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ P.cosupp ∧
      IsNonzeroAlongAt P.N P.ideal y ∧ IsNonzeroAlongAt Q.N Q.ideal y ∧
      y ∈ cosupport n P.N P.ideal (P.d+1) := by
  filter_upwards [G.isOpen.mem_nhds hxG, habove] with y hyG hyAbove hyC
  have hyP := hC hyC
  have hyQ := hcos ▸ hyP
  let p : G := ⟨y,hyG⟩
  have hpP : p ∈ (MarkedIdeal.pullback (Subtype.val : G → X) P).N := P.cosupp_subset_N hyP
  have hpQ : p ∈ (MarkedIdeal.pullback (Subtype.val : G → X) Q).N := Q.cosupp_subset_N hyQ
  have hnP := (isNonzeroAlongAt_pullback_val_iff hP.isCoherent G p).mp (hPG.isNonzeroAlongAt p hpP)
  have hnQ := (isNonzeroAlongAt_pullback_val_iff hQ.isCoherent G p).mp (hQG.isNonzeroAlongAt p hpQ)
  exact ⟨hyP,hnP,hnQ,hyAbove hyC⟩

end
end Hironaka.HironakaG8CentreDomainData
