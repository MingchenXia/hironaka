import Hironaka.Resolution.HironakaG4WindowUnitTrace
import Hironaka.Resolution.HironakaG4PrincipalMemberLocus

/-! In the unit branch the protected slice is the actual old trace locally. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4UnitSliceIdentity
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings BlowupFlatCoordinates DivisorExponentAlong MonomialPartAlong
  NonmonomialTransformAlong RestrictedIdealExtension RelativePrincipalizationSpan
  HironakaG4WindowUnitTrace HironakaG4PrincipalMemberLocus

variable {n : ℕ} {X : CMfd.{u} n}

/-- If the monomial part is a unit, the actual member and auxiliary slice
have the same trace on the carrier in a neighborhood of the point. -/
theorem eventually_unit_slice_identity (hn : 0 < n)
    {N Haux H : Set X} {F B L : List (Set X)} {x : X}
    (hEF : IsSNCDivisor n (Haux :: F)) (hTF : IsTransverse n N (Haux :: F))
    (hL : IsSNCDivisor n L) (hHL : H ∈ L) (hxN : x ∈ N) (hxHaux : x ∈ Haux)
    (hI : (restrictOn n N (vanishingIdeal (n := n) H)).IsCoherent)
    (hnz : IsNonzeroAlongAt N (restrictOn n N (vanishingIdeal (n := n) H)) x)
    (hunit : (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mem x 1)
    (hJZ : ∀ g, (nonmonomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mem x g ↔
      (vanishingIdeal (n := n) (N ∩ Haux)).mem x g) :
    ∀ᶠ y in 𝓝 x, y ∈ N ∩ Haux ↔ y ∈ N ∩ H := by
  obtain ⟨k, Φ, p, t, f, a, hsrc, h0, hp0, ht, hpk, hinj, hflat, hNflat,
    hf, ha, hax, hF, heq⟩ := exists_window_unit_trace hn hEF hTF hL hHL hxN hxHaux hI hnz hunit hJZ
  have hfx : f x = 0 := by
    have hh := heq.self_of_nhds hxN
    have hz : flatCoord Φ t x = 0 := by simp [flatCoord,h0]
    simpa [hz] using hh
  have hxH : x ∈ H := by
    have hzero : x ∈ (vanishingIdeal (n := n) H).zeroLocus := by
      intro g hg
      obtain ⟨_, b, hb, hbg⟩ := isInSpanAt_eq_iff.mp ((hF g).mp hg)
      simpa [hfx] using hbg.self_of_nhds
    rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (hL.1 H hHL)] at hzero
    exact hzero
  have hmem := eventually_mem_iff_principal_generator_zero hn hL hHL hxH hf hF
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ),
    ha.continuousAt.eventually_ne hax,heq,hmem] with y hy ha' heq' hmem'
  have haux := hflat y hy ⟨0,by simp⟩
  change y ∈ Haux ↔ x ∈ Haux ∧ flatCoord Φ (p ⟨0, by simp⟩) y = 0 at haux
  simp only [hxHaux,true_and,hp0] at haux
  constructor
  · rintro ⟨hyN,hyA⟩
    refine ⟨hyN,hmem'.mpr ?_⟩
    rw [heq' hyN,(haux.mp hyA)]
    simp
  · rintro ⟨hyN,hyH⟩
    refine ⟨hyN,haux.mpr ?_⟩
    have hh := hmem'.mp hyH
    rw [heq' hyN] at hh
    exact (mul_eq_zero.mp hh).resolve_left ha'

end
end Hironaka.HironakaG4UnitSliceIdentity
