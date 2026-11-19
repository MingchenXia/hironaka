import Hironaka.Resolution.HironakaG4WindowUnitTrace
import Hironaka.Resolution.HironakaG4UnitMemberChart

/-! Construct the unit-branch simultaneous chart from the actual residual. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4PreparedUnitChart
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings BlowupFlatCoordinates GiraudAlong DivisorExponentAlong MonomialPartAlong
  NonmonomialTransformAlong RestrictedIdealExtension RelativePrincipalizationSpan
  HironakaG4OptionalBoundaryTransform HironakaG4OptionalDivisorMasks HironakaG4WindowUnitTrace
  HironakaG4UnitMemberChart

variable {n : ℕ} {X : CMfd.{u} n}

/-- In the monomial-unit case, the actual selected member replaces the
auxiliary slice coordinate and remains transverse to all other tracked
boundary members. -/
theorem exists_prepared_unit_chart (hn : 0 < n)
    {N Haux H : Set X} {F B L : List (Set X)} {x : X}
    (hEF : IsSNCDivisor n (Haux :: F)) (hTF : IsTransverse n N (Haux :: F))
    (hL : IsSNCDivisor n L) (hHL : H ∈ L) (hxN : x ∈ N) (hxHaux : x ∈ Haux)
    (hI : (restrictOn n N (vanishingIdeal (n := n) H)).IsCoherent)
    (hnz : IsNonzeroAlongAt N (restrictOn n N (vanishingIdeal (n := n) H)) x)
    (hunit : (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mem x 1)
    (hJZ : ∀ g, (nonmonomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mem x g ↔
      (vanishingIdeal (n := n) (N ∩ Haux)).mem x g) :
    ∃ (S : Finset (Fin n)) (m : Fin (Haux :: F).length → Option (Fin n))
      (t : Fin n) (Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)),
      DivisorMasksValid S m ∧ m ⟨0, by simp⟩ = some t ∧ t ∉ S ∧
      Ψ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Ψ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ y ∈ flatDomain Ψ, y ∈ N ↔ GiraudAlong.flatMap Ψ y ∈ coordSubspace S) ∧
      (∀ (i : Fin F.length) y, y ∈ flatDomain Ψ → (y ∈ F.get i ↔
        GiraudAlong.flatMap Ψ y ∈ optionalCoordLocus (((m ⟨i.val + 1, by simp⟩)).map (fun k => {k})))) ∧
      ∀ y ∈ flatDomain Ψ, y ∈ H ↔ GiraudAlong.flatMap Ψ y t = 0 := by
  obtain ⟨k, Φ, p, t, f, a, hsrc, h0, hp0, ht, hpk, hinj, hflat, hNflat,
    hf, ha, hax, hF, heq⟩ := exists_window_unit_trace hn hEF hTF hL hHL hxN hxHaux hI hnz hunit hJZ
  let S : Finset (Fin n) := Finset.univ.filter fun j => k ≤ j.val
  let m : Fin (Haux :: F).length → Option (Fin n) := fun i => if x ∈ (Haux :: F).get i then some (p i) else none
  have hm : DivisorMasksValid S m := by
    constructor
    · intro i j hj hjs
      change (if x ∈ (Haux :: F).get i then some (p i) else none) = some j at hj
      by_cases hi : x ∈ (Haux :: F).get i
      · rw [if_pos hi] at hj
        have he : p i = j := Option.some.inj hj
        subst j
        have := hpk i hi
        have := (Finset.mem_filter.mp hjs).2
        omega
      · rw [if_neg hi] at hj
        contradiction
    · intro i j b hi hj
      change (if x ∈ (Haux :: F).get i then some (p i) else none) = some b at hi
      change (if x ∈ (Haux :: F).get j then some (p j) else none) = some b at hj
      by_cases hxi : x ∈ (Haux :: F).get i
      · by_cases hxj : x ∈ (Haux :: F).get j
        · rw [if_pos hxi] at hi
          rw [if_pos hxj] at hj
          apply hinj hxi hxj
          exact (Option.some.inj hi).trans (Option.some.inj hj).symm
        · rw [if_neg hxj] at hj
          contradiction
      · rw [if_neg hxi] at hi
        contradiction
  have htS : t ∉ S := by simp [S]; omega
  have hm0 : m ⟨0, by simp⟩ = some t := by
    change (if x ∈ (Haux :: F).get ⟨0, by simp⟩ then some (p ⟨0, by simp⟩) else none) = some t
    have hxHead : x ∈ (Haux :: F).get ⟨0, by simp⟩ := hxHaux
    rw [if_pos hxHead, hp0]
  have hN' : ∀ y ∈ flatDomain Φ, y ∈ N ↔ GiraudAlong.flatMap Φ y ∈ coordSubspace S := by
    intro y hy
    rw [coordSubspace_eq_complexCoordinatePlane]
    exact hNflat hy.1 hy.2
  have hE' : ∀ i y, y ∈ flatDomain Φ → (y ∈ (Haux :: F).get i ↔
      GiraudAlong.flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))) := by
    intro i y hy
    have hh := hflat y hy i
    change y ∈ (Haux :: F).get i ↔ GiraudAlong.flatMap Φ y ∈
      optionalCoordLocus (((if x ∈ (Haux :: F).get i then some (p i) else none) : Option (Fin n)).map (fun k => {k}))
    by_cases hi : x ∈ (Haux :: F).get i
    · rw [if_pos hi]
      simp only [hi, true_and] at hh
      simpa [optionalCoordLocus, coordSubspace, flatCoord, GiraudAlong.flatMap] using hh
    · rw [if_neg hi]
      simp only [hi, false_and, iff_false] at hh
      simpa [optionalCoordLocus] using hh
  let mF : Fin F.length → Option (Fin n) := fun i => m ⟨i.val + 1, by simp⟩
  have hmt : ∀ i, mF i ≠ some t := by
    intro i hi
    have he := hm.2 ⟨i.val + 1, by simp⟩ ⟨0, by simp⟩ t hi hm0
    have hv := congrArg Fin.val he
    simp at hv
  have hE_F : ∀ i y, y ∈ flatDomain Φ → (y ∈ F.get i ↔
      GiraudAlong.flatMap Φ y ∈ optionalCoordLocus ((mF i).map (fun k => {k}))) := by
    intro i y hy
    exact hE' ⟨i.val + 1, by simp⟩ y hy
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
  have htrace : ∀ᶠ y in 𝓝 x, y ∈ N → f y = a y * (GiraudAlong.flatMap Φ y) t := by
    simpa [flatCoord,GiraudAlong.flatMap] using heq
  obtain ⟨Ψ,hΨsrc,hΨ0,hΨN,hΨF,hΨH⟩ :=
    exists_unit_trace_member_chart hn hL hHL hxH Φ hsrc h0 S mF hN' hE_F t htS hmt hf ha hax hF htrace
  exact ⟨S,m,t,Ψ,hm,hm0,htS,hΨsrc,hΨ0,hΨN,hΨF,hΨH⟩

end
end Hironaka.HironakaG4PreparedUnitChart
