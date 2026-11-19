import Hironaka.API
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Invariant.OrderMultiplicativity
import Hironaka.Invariant.MonomialPart

set_option autoImplicit false

/-! # Point-supported ideal truncations principalized over the same whole manifold -/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.PointSupportedIdealPrincipalization

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  GermIdealOrder IdealWeightPowers RestrictedIdealExtension BlowupFlatCoordinates
  HironakaAdmissibleSequence NormalCrossings DivisorExponentAlong

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Genuine singleton flattening and its coherent point ideal, in every dimension. -/
theorem singleton_geometry_and_coherence (x : X) :
    IsClosedSubmanifold n ({x} : Set X) ∧ (pointIdeal n x).IsCoherent := by
  let e := complexChartAt (n := n) x
  let p := e.val x
  let Φ : LocalHolomorphicEquivAt (n := n) p := {
    source := e.val.target
    target := (fun w : ComplexModel n => w + p) ⁻¹' e.val.target
    isOpen_source := e.val.open_target
    isOpen_target := e.val.open_target.preimage (continuous_id.add_const p)
    center_mem_source := e.val.map_source (mem_complexChartAt_source x)
    toFun := fun z => z - p
    invFun := fun w => w + p
    toFun_holomorphic := (differentiable_id.sub_const p).differentiableOn
    invFun_holomorphic := (differentiable_id.add_const p).differentiableOn
    mapsTo_toFun := by intro z hz; simpa only [mem_preimage, sub_add_cancel] using hz
    mapsTo_invFun := fun _ hw => hw
    left_inv := fun z _ => sub_add_cancel z p
    right_inv := fun w _ => add_sub_cancel_right w p }
  have hreg : RegularAtDim (n := n) ({x} : Set X) x 0 := by
    refine ⟨Nat.zero_le _, rfl, Φ, Subset.rfl, sub_self p, ?_⟩
    intro y hy _
    constructor
    · intro hyx
      rw [mem_singleton_iff.mp hyx]
      change p - p ∈ complexCoordinatePlane n 0
      rw [sub_self]
      intro i _
      rfl
    · intro hz
      have heq : e.val y - p = 0 := by
        ext i
        exact hz i (Nat.zero_le _)
      exact e.val.injOn hy (mem_complexChartAt_source x) (sub_eq_zero.mp heq)
  have hC : IsClosedSubmanifold n ({x} : Set X) :=
    ⟨isClosed_singleton, fun y hy => by
      rw [mem_singleton_iff.mp hy]
      exact ⟨0, hreg⟩⟩
  exact ⟨hC, VanishingIdealCoherent.isCoherent_vanishingIdeal hC⟩

section PositiveDimension

variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Coherence, singleton zero support and every nonzero stalk germ are internally supplied. -/
theorem truncation_properties (x : M) {𝔞 : GermIdeal (m + 1) M}
    (h𝔞 : 𝔞.IsCoherent) (N : ℕ) :
    let 𝔟 := sumIdeal 𝔞 (idealPow (pointIdeal (m + 1) x) N)
    𝔟.IsCoherent ∧ 𝔟.zeroLocus ⊆ ({x} : Set M) ∧
      ∀ y, ∃ g, 𝔟.mem y g ∧ ∃ᶠ z in 𝓝 y, g z ≠ 0 := by
  classical
  dsimp only
  obtain ⟨hC, hpt⟩ := singleton_geometry_and_coherence (n := m + 1) x
  have hpow := GermIdealPullbackCalculus.isCoherent_idealPow hpt N
  have hle := le_sumIdeal_right (𝔞 := 𝔞) hpow
  have hone {y : M} (hy : y ≠ x) :
      (idealPow (pointIdeal (m + 1) x) N).mem y (fun _ => (1 : ℂ)) := by
    have hmem : (pointIdeal (m + 1) x).mem y (fun _ => (1 : ℂ)) := by
      refine ⟨holomorphicAt_const 1, ?_⟩
      filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds
        (show y ∈ ({x} : Set M)ᶜ by simpa using hy)] with z hz hzx
      exact absurd (mem_singleton_iff.mpr hzx) hz
    simpa only [one_pow] using
      OrderMultiplicativity.pow_mem_idealPow hmem (holomorphicAt_const 1) N
  refine ⟨isCoherent_sumIdeal h𝔞 hpow, ?_, ?_⟩
  · intro y hy
    by_contra hyx
    have h1 := hle y (fun _ => (1 : ℂ)) (hone (by simpa using hyx))
    exact one_ne_zero (hy _ h1)
  · intro y
    by_cases hy : y = x
    · subst y
      obtain ⟨k, _, _, Φ, hsrc, h0, _⟩ := hC.2 x rfl
      let j : Fin (m + 1) := ⟨0, Nat.zero_lt_succ _⟩
      let g := flatCoord Φ j
      have hgh : HolomorphicAt (m + 1) g x :=
        holomorphicAt_flatCoord Φ j (mem_flatDomain_self Φ)
      have hg0 : g x = 0 := by
        change Φ.toFun (chartAt (ComplexModel (m + 1)) x x) j = 0
        have h0' : Φ.toFun (chartAt (ComplexModel (m + 1)) x x) = 0 := h0
        rw [h0']
        rfl
      have hgmem := mem_pointIdeal_of_apply_eq_zero hgh hg0
      refine ⟨fun z => g z ^ N, hle x _
        (OrderMultiplicativity.pow_mem_idealPow hgmem hgh N), ?_⟩
      apply (MonomialPart.frequently_flatMap_ne_zero hsrc
        (mem_flatDomain_self Φ) {j}).mono
      intro z hz
      exact pow_ne_zero N (hz.2.1 j (Finset.mem_singleton_self j))
    · exact ⟨fun _ => 1, hle y _ (hone hy),
        Frequently.of_forall fun _ => one_ne_zero⟩

/-- Genuine compact-zero-locus principalization targets the same whole original manifold. -/
theorem exists_principalization_truncation (x : M) {𝔞 : GermIdeal (m + 1) M}
    (h𝔞 : 𝔞.IsCoherent) (N : ℕ) :
    let 𝔟 := sumIdeal 𝔞 (idealPow (pointIdeal (m + 1) x) N)
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel (m + 1)) Y)
      (_ : IsComplexManifold (m + 1) Y) (π : Y → M)
      (D : EffectiveDivisor (m + 1) Y) (E : List (Set Y)),
      IsAdmissibleBlowupSequence (m + 1) M [] 𝔟.zeroLocus Y π E ∧
      GermIdeal.pullback (m := m + 1) π 𝔟 = D.ideal ∧
      IsSNCDivisor (m + 1) E ∧ D.support = ⋃ H ∈ E, H ∧
      D.support = π ⁻¹' 𝔟.zeroLocus ∧ IsIsomorphismOver (m + 1) π 𝔟.zeroLocusᶜ := by
  dsimp only
  obtain ⟨hcoh, hsub, hne⟩ := truncation_properties x h𝔞 N
  have hclosed := OrderTaylor.isClosed_zeroLocus_of_isCoherent hcoh
  have hcompact := isCompact_singleton.of_isClosed_subset hclosed hsub
  exact Hironaka.exists_principalization_of_isCompact hcoh hne hcompact

end PositiveDimension
end
end Hironaka.PointSupportedIdealPrincipalization
