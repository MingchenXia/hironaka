import Hironaka.Blowup.MonomialBlowupAlongChart
import Hironaka.Resolution.HironakaSharpActualControlledRelativeSaturation

set_option autoImplicit false

/-! A single actual adapted chart computes a family of whole controlled ideals.
Blueprint: `hironaka-g4-common-monomial-chart.tex`. -/

open Set Filter Classical
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4CommonMonomialChart

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  SimultaneousNormalCrossings BlowupSNCTransform BlowupFlatCoordinates
  BlowupExceptionalDivisor BlowupStrictSubmanifold BlowupStrictIdeal MonomialPart
  RelativePrincipalizationSpan InvertibleIdealQuotient
  MonomialBlowupAlongChart MonomialBlowupAlong MonomialBlowup
  GermIdealOrder IdealWeightPowers RestrictedIdealExtension RestrictedIdealQuotient
  HironakaSharpActualControlledRelativeSaturation
  HironakaSharpActualProductNewExceptionalFactor

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- An actual ideal and mark on the same literal carrier and boundary. -/
def markedRow (N : Set X) (E : List (Set X)) (I : GermIdeal n X) (d : ℕ) :
    MarkedIdeal n X := ⟨N, E, I, d⟩

/-- One row-independent actual adapted chart gives BOTH entire controlled
ideal directions for every row, at the same actual point. The family can be
infinite: only the geometric neighbourhood is uniform, not all ideal germs. -/
theorem exists_common_monomial_chart {ι : Type v} {N C : Set X} {E : List (Set X)}
    {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E)
    (hTr : IsTransverse n N E) (hCN : C ⊆ N) (hCNC : HasNormalCrossings n C E)
    (I : ι → GermIdeal n X) (d : ι → ℕ)
    (hI : ∀ r, (I r).IsCoherent)
    (hC : ∀ r, (markedRow N E (I r) (d r)).IsAdmissibleCentre C)
    {z : Y} (hz : z ∈ geoStrictTransform π C N) (hzC : π z ∈ C)
    (a : ι → Fin E.length → ℕ) (u : ι → Fin E.length → X → ℂ)
    (hu : ∀ r i, π z ∈ E.get i → HolomorphicAt n (u r i) (π z) ∧
      ∀ g, (vanishingIdeal (n := n) (E.get i)).mem (π z) g ↔
        IsInSpanAt (n := n) (· = u r i) (π z) g)
    (hgen : ∀ r g, IsInSpanOnAt (n := n) N ((I r).mem (π z)) (π z) g ↔
      IsInSpanOnAt (n := n) N
        (· = fun x => ∏ i ∈ Finset.univ.filter (fun i => π z ∈ E.get i),
          u r i x ^ a r i) (π z) g)
    (hd : ∀ r, d r ≤ ∑ i ∈ Finset.univ.filter
      (fun i => π z ∈ E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i), a r i) :
    ∃ (k : ℕ) (j : Fin n) (s : Fin E.length → Fin n)
      (W : Y → ComplexModel n) (U : Set Y),
      IsOpen U ∧ z ∈ U ∧
      (∀ y ∈ U, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W y) ∧
      Function.Injective (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ))
        (chartAt (ComplexModel n) z z)) ∧
      j.val < k ∧ W z j = 0 ∧
      (∀ y ∈ U, ∀ g, (exceptionalDivisor hπ).ideal.mem y g ↔
        IsInSpanAt (n := n) (· = fun w => W w j) y g) ∧
      (∀ i, z ∈ geoStrictTransform π C (E.get i) →
        π z ∈ E.get i ∧ s i ≠ j ∧ W z (s i) = 0 ∧
        ∀ y ∈ U, ∀ g, (vanishingIdeal (n := n) (geoStrictTransform π C (E.get i))).mem y g ↔
          IsInSpanAt (n := n) (· = fun w => W w (s i)) y g) ∧
      Set.InjOn s {i | π z ∈ E.get i} ∧
      (∀ i, π z ∈ E.get i → (s i).val < k) ∧
      (∀ y ∈ U, y ∈ geoStrictTransform π C N ↔ W y ∈ complexCoordinatePlane n k) ∧
      ∀ r g, ((markedRow N E (I r) (d r)).geoTransform C π).ideal.mem z g ↔
        HolomorphicAt n g z ∧
        IsInSpanOnAt (n := n) (geoStrictTransform π C N)
          (· = fun w => W w j ^ ((∑ i ∈ Finset.univ.filter
              (fun i => π z ∈ E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i), a r i) - d r) *
            ∏ i ∈ Finset.univ.filter (fun i => z ∈ geoStrictTransform π C (E.get i)),
              W w (s i) ^ a r i) z g := by
  classical
  have hn : 0 < n := pos_of_isBlowupAlong hπ hzC
  have had : IsAdaptedAt n C N E (π z) :=
    isAdaptedAt_of_hasNormalCrossings hn hCN hE hTr hCNC hzC
  obtain ⟨k, j, s, W, U, hU, hzU, hWs, hinj, hWzj, hD, hH, hsinj, hslt, hNU, hmono⟩ :=
    exists_monomial_chart_of_isAdaptedAt hπ hE.1 hzC had
  have hjk : j.val < k := ((hNU z hzU).mp hz).1
  refine ⟨k, j, s, W, U, hU, hzU, hWs, hinj, hjk, hWzj, hD, hH, hsinj, hslt, ?_, ?_⟩
  · intro y hy
    simpa only [hjk, true_and] using hNU y hy
  · intro r g
    obtain ⟨c, hc, hcz, heq⟩ := hmono (a r) (u r) (hu r)
    have hWj : HolomorphicAt n (fun w => W w j) z := holomorphicAt_coord hU hWs j hzU
    have hq : HolomorphicAt n (fun w => ∏ i ∈ Finset.univ.filter
        (fun i => z ∈ geoStrictTransform π C (E.get i)), W w (s i) ^ a r i) z :=
      holomorphicAt_finset_prod _ fun i _ =>
        CompanionReduction.holomorphicAt_pow_of (holomorphicAt_coord hU hWs (s i) hzU) (a r i)
    have hspan := isInSpanOnAt_geoTransform_iff_of_eq hπ (𝔪 := markedRow N E (I r) (d r))
      hN (hI r) (hC r) hz (hgen r) (hD z hzU) hWj hc hcz hq (hd r) heq g
    have hden : ∀ b, (idealPow (exceptionalDivisor hπ).ideal (d r)).mem z b →
        HolomorphicAt n b z := by
      intro b hb
      exact (isInSpanAt_eq_iff.mp ((idealPow_principal_mem_iff hWj (hD z hzU) (d r) b).mp hb)).1
    have hnorm := restrictOn_colonAlong_mem_iff (geoStrictTransform π C N)
      (GermIdeal.pullback (m := n) π (I r))
      (idealPow (exceptionalDivisor hπ).ideal (d r)) hden g
    exact hnorm.symm.trans (and_congr_right fun _ => hspan)

end

end Hironaka.HironakaG4CommonMonomialChart
