import Hironaka.Resolution.HironakaG4SmoothMemberJet
import Hironaka.Invariant.MonomialCase

/-! An SNC member is locally the zero locus of any actual principal generator. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4PrincipalMemberLocus
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings BlowupFlatCoordinates MonomialCase MemberPullback RelativePrincipalizationSpan
  InvertibleIdealQuotient

variable {n : ℕ} {X : CMfd.{u} n}

/-- Any principal generator of an incident SNC member cuts out that member
on an actual neighborhood. -/
theorem eventually_mem_iff_principal_generator_zero (hn : 0 < n)
    {L : List (Set X)} {H : Set X} {x : X} (hL : IsSNCDivisor n L) (hHL : H ∈ L)
    (hxH : x ∈ H) {f : X → ℂ} (hf : HolomorphicAt n f x)
    (hF : ∀ g, (vanishingIdeal (n := n) H).mem x g ↔ IsInSpanAt (n := n) (· = f) x g) :
    ∀ᶠ y in 𝓝 x, y ∈ H ↔ f y = 0 := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hHL
  obtain ⟨Φ, σ, hsrc, h0, hinj, hA⟩ := exists_snc_chart hn hL x
  have hxD := mem_flatDomain_self Φ
  have hxi : x ∈ L.get i := hi ▸ hxH
  let g : X → ℂ := flatCoord Φ (σ i)
  have hg : HolomorphicAt n g x := holomorphicAt_flatCoord Φ (σ i) hxD
  have hG : ∀ v, (vanishingIdeal (n := n) H).mem x v ↔
      IsInSpanAt (n := n) (· = g) x v := by
    intro v
    rw [← hi]
    exact vanishingIdeal_mem_iff_flatCoord Φ (hA i hxi) hxD v
  have hfI : (vanishingIdeal (n := n) H).mem x f :=
    (hF f).mpr (isInSpanAt_self rfl hf)
  have hgI : (vanishingIdeal (n := n) H).mem x g :=
    (hG g).mpr (isInSpanAt_self rfl hg)
  obtain ⟨_, a, ha, hfa⟩ := isInSpanAt_eq_iff.mp ((hG f).mp hfI)
  obtain ⟨_, b, hb, hgb⟩ := isInSpanAt_eq_iff.mp ((hF g).mp hgI)
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD, hfa, hgb] with y hy hfy hgy
  have hH : y ∈ H ↔ g y = 0 := by
    rw [← hi]
    exact hA i hxi hy.1 hy.2
  rw [hH]
  constructor
  · intro hg0
    rw [hfy, hg0, mul_zero]
  · intro hf0
    rw [hgy, hf0, mul_zero]

end
end Hironaka.HironakaG4PrincipalMemberLocus
