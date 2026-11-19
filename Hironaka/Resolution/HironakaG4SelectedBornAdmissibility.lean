import Hironaka.Resolution.HironakaG4SelectedBornChartStep
import Hironaka.Invariant.NonmonomialStepAlong

set_option autoImplicit false

/-! Genuine current monomial ideals and actual centre admissibility produce
canonical shared actual exponent rows, with no supplied original generators
or numerical inequalities. Blueprint: `hironaka-g4-selected-born-admissibility.tex`. -/

open Set Filter Classical
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4SelectedBornAdmissibility

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings SimultaneousNormalCrossings BlowupFlatCoordinates GiraudAlong
  BlowupStrictSubmanifold MemberPullback
  MonomialPart MonomialPartAlong MonomialCaseAlong DivisorExponentAlong
  BoundaryCount GermIdealOrder RelativePrincipalizationSpan
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG4CommonMonomialChart
  HironakaG4SelectedBornChartStep HironakaG4MonomialMaximalContact
  HironakaMonomialBlowup

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- A genuine selected-born blowup and actual monomial row family internally
produce their canonical original exponent rows, whole original dictionaries,
selected feasibility, one shared pivot and every actual transformed cosupport. -/
theorem exists_canonical_selected_born_chart_step {ι : Type v}
    {N : Set X} {E : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E)
    (S : Finset (Fin E.length)) {π : Y → X}
    (hπ : IsBlowupAlong n (N ∩ memberInter E S) π)
    (I : ι → GermIdeal n X) (d : ι → ℕ) (hI : ∀ r, (I r).IsCoherent)
    (hne : ∀ r, ∀ y ∈ N, IsNonzeroAlongAt N (I r) y)
    (hmono : ∀ r, IsMonomialAlong n N (I r) E)
    (hC : ∀ r, (markedRow N E (I r) (d r)).IsAdmissibleCentre (N ∩ memberInter E S))
    {z : Y} (hz : z ∈ geoStrictTransform π (N ∩ memberInter E S) N)
    (hzC : π z ∈ N ∩ memberInter E S) :
    let R : Finset (Fin E.length) := Finset.univ.filter
      (fun i => z ∈ geoStrictTransform π (N ∩ memberInter E S) (E.get i))
    ∃ p : Fin E.length, p ∈ S ∧ p ∉ R ∧
      ∀ r q, z ∈ cosupport n (geoStrictTransform π (N ∩ memberInter E S) N)
          ((markedRow N E (I r) (d r)).geoTransform (N ∩ memberInter E S) π).ideal q ↔
        q ≤ ∑ j : Fin (E.length+1), transformRow (d r) S R
          (fun i => divExpAlong n N (I r) (E.get i) (π z)) j := by
  have hn : 0 < n := pos_of_isBlowupAlong hπ hzC
  obtain ⟨_kC, kN, Φ, σ, hsrc, hσk, hinj, hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn subset_rfl hE hTr hTr.hasNormalCrossings hzC.1
  have hxD : π z ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hNflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kN) :=
    fun hy hyΦ => (hflat hy hyΦ).2.1
  have hA : ∀ i, π z ∈ E.get i → ∀ {y : X},
      y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
      (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) (σ i) = 0) :=
    fun i hi _ hy hyΦ => (hflat hy hyΦ).2.2 i hi
  let a : ι → Fin E.length → ℕ := fun r i => divExpAlong n N (I r) (E.get i) (π z)
  let u : ι → Fin E.length → X → ℂ := fun _ i => flatCoord Φ (σ i)
  have hu : ∀ r i, π z ∈ E.get i → HolomorphicAt n (u r i) (π z) ∧
      ∀ g, (vanishingIdeal (n := n) (E.get i)).mem (π z) g ↔
        IsInSpanAt (n := n) (· = u r i) (π z) g := by
    intro r i hi
    exact ⟨holomorphicAt_flatCoord Φ (σ i) hxD,
      vanishingIdeal_mem_iff_flatCoord Φ (hA i hi) hxD⟩
  have hgen : ∀ r g, IsInSpanOnAt (n := n) N ((I r).mem (π z)) (π z) g ↔
      IsInSpanOnAt (n := n) N
        (· = fun y => ∏ i ∈ Finset.univ.filter (fun i => π z ∈ E.get i),
          u r i y ^ a r i) (π z) g := by
    intro r g
    exact isInSpanOnAt_iff_generator_of_isMonomialAlong hsrc hNflat hA hn hN hE hTr
      (hI r) (hne r) (hmono r) hzC.1 hσk hinj g
  have hd : ∀ r, d r ≤ ∑ i ∈ S, a r i := by
    intro r
    have hbound := NonmonomialStepAlong.le_sum_divExpAlong_of_subset_cosupport hn hN hE hTr
      (hI r) (hne r) (hmono r) (hC r).2.2 inter_subset_left (hC r).2.1 hzC
    rw [filter_eventually_subset_inter_memberInter_eq hn hE hTr hzC.1 hzC.2] at hbound
    exact hbound
  exact exists_selected_born_chart_step hN hE hTr S hπ I d hI hC hz hzC a u hu hgen hd

end

end Hironaka.HironakaG4SelectedBornAdmissibility
