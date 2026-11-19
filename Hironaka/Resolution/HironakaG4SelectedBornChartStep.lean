import Hironaka.Resolution.HironakaG4MonomialChartCosupport
import Hironaka.Resolution.HironakaG4MonomialMaximalContact
import Hironaka.Resolution.HironakaMonomialBlowup
import Hironaka.Invariant.BoundaryCountAlong

set_option autoImplicit false

/-! A genuine selected-born ambient blowup produces one valid shared arithmetic row step.
Blueprint: `hironaka-g4-selected-born-chart-step.tex`. -/

open Set Filter Classical
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4SelectedBornChartStep

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  RelativePrincipalizationSpan GermIdealOrder InvertibleIdealQuotient
  MemberInterAlong BoundaryCountAlong HironakaMonomialBlowup
  HironakaG4CommonMonomialChart HironakaG4MonomialChartCosupport
  HironakaG4MonomialMaximalContact

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- A real selected-born blowup INTERNALLY supplies one valid shared arithmetic
pivot witness and exact actual controlled cosupport weights for all its rows. -/
theorem exists_selected_born_chart_step {ι : Type v} {N : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E)
    (S : Finset (Fin E.length)) {π : Y → X}
    (hπ : IsBlowupAlong n (N ∩ BoundaryCount.memberInter E S) π)
    (I : ι → GermIdeal n X) (d : ι → ℕ) (hI : ∀ r, (I r).IsCoherent)
    (hC : ∀ r, (markedRow N E (I r) (d r)).IsAdmissibleCentre
      (N ∩ BoundaryCount.memberInter E S))
    {z : Y} (hz : z ∈ geoStrictTransform π (N ∩ BoundaryCount.memberInter E S) N)
    (hzC : π z ∈ N ∩ BoundaryCount.memberInter E S)
    (a : ι → Fin E.length → ℕ) (u : ι → Fin E.length → X → ℂ)
    (hu : ∀ r i, π z ∈ E.get i → HolomorphicAt n (u r i) (π z) ∧
      ∀ g, (vanishingIdeal (n := n) (E.get i)).mem (π z) g ↔
        IsInSpanAt (n := n) (· = u r i) (π z) g)
    (hgen : ∀ r g, IsInSpanOnAt (n := n) N ((I r).mem (π z)) (π z) g ↔
      IsInSpanOnAt (n := n) N
        (· = fun x => ∏ i ∈ Finset.univ.filter (fun i => π z ∈ E.get i),
          u r i x ^ a r i) (π z) g)
    (hd : ∀ r, d r ≤ ∑ i ∈ S, a r i) :
    let R : Finset (Fin E.length) := Finset.univ.filter
      (fun i => z ∈ geoStrictTransform π (N ∩ BoundaryCount.memberInter E S) (E.get i))
    ∃ p : Fin E.length, p ∈ S ∧ p ∉ R ∧
      ∀ r q, z ∈ cosupport n (geoStrictTransform π (N ∩ BoundaryCount.memberInter E S) N)
          ((markedRow N E (I r) (d r)).geoTransform (N ∩ BoundaryCount.memberInter E S) π).ideal q ↔
        q ≤ ∑ j : Fin (E.length+1), transformRow (d r) S R (a r) j := by
  classical
  let C := N ∩ BoundaryCount.memberInter E S
  let R : Finset (Fin E.length) := Finset.univ.filter
    (fun i => z ∈ geoStrictTransform π C (E.get i))
  have hn : 0 < n := SimultaneousNormalCrossings.pos_of_isBlowupAlong hπ hzC
  have hNC : HasNormalCrossings n C E := hasNormalCrossings_inter_memberInter hTr S
  have hdrop := card_filter_mem_geoStrictTransform_lt_along hπ inter_subset_left hE hTr hNC S
    hzC hz (Eventually.of_forall fun _ hyN hyS => ⟨hyN, hyS⟩)
  have hp : ∃ p : Fin E.length, p ∈ S ∧ p ∉ R := by
    by_contra hno
    push Not at hno
    have heq : (S.filter fun i => z ∈ geoStrictTransform π C (E.get i)) = S := by
      apply Finset.filter_eq_self.mpr
      intro i hi
      exact (Finset.mem_filter.mp (hno i hi)).2
    rw [heq] at hdrop
    exact (Nat.lt_irrefl _) hdrop
  obtain ⟨p, hpS, hpR⟩ := hp
  have hFilter := filter_eventually_subset_inter_memberInter_eq hn hE hTr hzC.1 hzC.2
  have hdnative : ∀ r, d r ≤ ∑ i ∈ Finset.univ.filter
      (fun i => π z ∈ E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i), a r i := by
    intro r
    rw [hFilter]
    exact hd r
  obtain ⟨k, j, s, W, U, hU, hzU, hWs, hinj, hjk, hj0, _hD, hH, _hsinj, hslt, hNU, hWhole⟩ :=
    exists_common_monomial_chart hπ hN hE hTr inter_subset_left hNC I d hI hC hz hzC a u hu hgen hdnative
  refine ⟨p, hpS, hpR, ?_⟩
  intro r q
  let T : Finset (Option (Fin E.length)) := insert none (R.image some)
  let σ : Option (Fin E.length) → Fin n := fun o => o.elim j s
  let b : Option (Fin E.length) → ℕ := fun o => o.elim ((∑ i ∈ S, a r i) - d r) (a r)
  have hprod (w : Y) : (∏ o ∈ T, W w (σ o) ^ b o) =
      W w j ^ ((∑ i ∈ S, a r i) - d r) * ∏ i ∈ R, W w (s i) ^ a r i := by
    simp [T, σ, b, Finset.prod_image]
  have hweight : (∑ o ∈ T, b o) = ((∑ i ∈ S, a r i) - d r) + ∑ i ∈ R, a r i := by
    simp [T, b, Finset.sum_image]
  have hFactor : ∀ o ∈ T, (σ o).val < k ∧ W z (σ o) = 0 := by
    intro o ho
    rcases Finset.mem_insert.mp ho with ho | ho
    · subst o
      exact ⟨hjk, hj0⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ho
      have hret := (Finset.mem_filter.mp hi).2
      exact ⟨hslt i (hH i hret).1, (hH i hret).2.2.1⟩
  have hWholeT (g : Y → ℂ) :
      ((markedRow N E (I r) (d r)).geoTransform C π).ideal.mem z g ↔
        HolomorphicAt n g z ∧ IsInSpanOnAt (n := n) (geoStrictTransform π C N)
          (· = fun w => ∏ o ∈ T, W w (σ o) ^ b o) z g := by
    have hfun : (fun w => ∏ o ∈ T, W w (σ o) ^ b o) =
        fun w => W w j ^ ((∑ i ∈ S, a r i) - d r) * ∏ i ∈ R, W w (s i) ^ a r i :=
      funext hprod
    rw [hfun]
    simpa only [hFilter] using hWhole r g
  have hcos := cosupport_raw_coordinate_monomial_iff W hU hzU hWs hinj k hNU hz T σ b
    (fun o ho => (hFactor o ho).1) (fun o ho => (hFactor o ho).2) hWholeT q
  have hdegree : (∑ t : Fin (E.length+1), transformRow (d r) S R (a r) t) =
      ((∑ i ∈ S, a r i) - d r) + ∑ i ∈ R, a r i := by
    simp [transformRow, rowWeight, Fin.sum_univ_castSucc, Nat.add_comm]
  rw [hweight] at hcos
  change z ∈ cosupport n (geoStrictTransform π C N)
    ((markedRow N E (I r) (d r)).geoTransform C π).ideal q ↔
      q ≤ ∑ t : Fin (E.length+1), transformRow (d r) S R (a r) t
  rw [hdegree]
  exact hcos

end

end Hironaka.HironakaG4SelectedBornChartStep
