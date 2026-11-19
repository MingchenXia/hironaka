import Hironaka.Resolution.HironakaOriginalNCCountHistoryGeometry

set_option autoImplicit false

/-! Causal old-count chronology and first current-count years for arbitrary
actual compatible original histories. Definitions read only H and the SAME T.
Whole-history restrictions and isomorphisms retain all actual empty-step years.
This is not a remainder/phase interpreter or the original canonical NC driver.
Blueprint: hironaka-original-nc-count-birth-history-extension.tex.
Source-only proof-body draft, with no kernel-check claim. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCCountHistory

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HomogenizedGlueingTower
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaOriginalOldBranchOpenHistory

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Forward year j of the actual original old-count history, saturated after
the terminal year. Every actual step, including an empty step, is retained. -/
def countAt (H : Set X) : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → ℕ → ℕ
  | _, .refl, y, _ => oldCount H .refl y
  | _, .step T C π hπ, y, j =>
      if j ≤ T.length then countAt H T (π y) j else oldCount H (.step T C π hπ) y

theorem countAt_length (H : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y),
      countAt H T y T.length = oldCount H T y
  | _, .refl, _ => rfl
  | _, .step T C π hπ, y => by
      simp only [countAt, BlowupTower.length_step, Nat.not_succ_le_self, if_false]

/-- Exact prefix/suffix dictionary. The existing head parameter counts removed
terminal steps; the forward year therefore uses length(T)-j. -/
theorem countAt_eq_prefix_count (H : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) (j : ℕ),
      countAt H T y j = oldCount H (head T (T.length - j)) ((tail T (T.length - j)).proj y)
  | _, .refl, y, j => by
      have hs : (BlowupTower.refl : BlowupTower X X).length - j = 0 := Nat.zero_sub j
      rw [hs]
      rfl
  | _, .step T C π hπ, y, j => by
      by_cases hj : j ≤ T.length
      · have hs : (BlowupTower.step T C π hπ).length - j = T.length - j + 1 := by
          rw [BlowupTower.length_step]
          omega
        rw [countAt, if_pos hj, hs]
        change countAt H T (π y) j =
          oldCount H (head T (T.length - j)) ((tail T (T.length - j)).proj (π y))
        exact countAt_eq_prefix_count H T (π y) j
      · have hs : (BlowupTower.step T C π hπ).length - j = 0 := by
          rw [BlowupTower.length_step]
          omega
        rw [countAt, if_neg hj, hs]
        rfl

-- Preserve the fixed public result's named prefix even though its other
-- fields already write that same prefix explicitly.
set_option linter.unusedVariables false in
/-- Every value in the defined forward chronology is a genuine intrinsic NC
count internally produced from the arbitrary actual original history domain. -/
theorem countAt_is_intrinsic
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (y : Y) (j : ℕ) :
    let P := head T (T.length - j)
    let Q := tail T (T.length - j)
    let hc := currentPair_head M hN hI h T hT hHistory (T.length - j)
    countAt H T y j = branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) (Q.proj y) := by
  dsimp only
  rw [countAt_eq_prefix_count]
  exact oldCount_eq _ _ _

/-- Literal strict membership proves nonincreasing old count along ANY actual
compatible original history, without a canonical or highest-centre assumption. -/
theorem countAt_antitone
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower M T →
      IsOriginalBranchTestTower M H T → ∀ y : Y, Antitone (countAt H T y)
  | _, .refl, _hT, _hHistory, _y => fun _i _j _hij => le_rfl
  | _, .step T C π hπ, hT, hHistory, y => by
      have hHistoryT : IsOriginalBranchTestTower M H T :=
        fun U B hSNC hUnion => (hHistory U B hSNC hUnion).1
      have ih := countAt_antitone M hN hI h T hT.1 hHistoryT (π y)
      have hStep := oldCount_step_le M hN hI h T C π hπ hT hHistory y
      intro i j hij
      by_cases hj : j ≤ T.length
      · have hi : i ≤ T.length := hij.trans hj
        simpa only [countAt, if_pos hi, if_pos hj] using ih hij
      · by_cases hi : i ≤ T.length
        · simp only [countAt, if_neg hj, if_pos hi]
          exact hStep.trans ((countAt_length H T (π y)) ▸ ih hi)
        · simp only [countAt, if_neg hj, if_neg hi]
          exact le_rfl

/-- The first current-count year is internally defined from H and T alone.
The terminal year is the explicit existence witness; no future output tower
or caller count/history certificate is involved in the definition. -/
def birthYear (H : Set X) (T : BlowupTower X Y) (y : Y) : ℕ :=
  Nat.find (show ∃ j : ℕ, countAt H T y j = oldCount H T y from
    ⟨T.length, countAt_length H T y⟩)

theorem birthYear_spec (H : Set X) (T : BlowupTower X Y) (y : Y) :
    countAt H T y (birthYear H T y) = oldCount H T y := by
  unfold birthYear
  exact Nat.find_spec (p := fun j : ℕ => countAt H T y j = oldCount H T y)
    (show ∃ j : ℕ, countAt H T y j = oldCount H T y from
      ⟨T.length, countAt_length H T y⟩)

theorem birthYear_le_length (H : Set X) (T : BlowupTower X Y) (y : Y) :
    birthYear H T y ≤ T.length := Nat.find_min' _ (countAt_length H T y)

/-- First attainment, exact constant tail, and the last strict count drop are
consequences of actual geometric antitonicity, never supplied as certificates. -/
theorem birthYear_characterization
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (y : Y) :
    let β := birthYear H T y
    β ≤ T.length ∧ countAt H T y β = countAt H T y T.length ∧
      (∀ j ≤ T.length, countAt H T y j = countAt H T y T.length ↔ β ≤ j) ∧
      (∀ j < β, countAt H T y T.length < countAt H T y j) ∧
      (0 < β → countAt H T y β < countAt H T y (β - 1)) ∧
      (∀ i j, β ≤ i → i ≤ j → j ≤ T.length → countAt H T y i = countAt H T y j) := by
  dsimp only
  let β := birthYear H T y
  have hb : β ≤ T.length := birthYear_le_length H T y
  have he : countAt H T y β = oldCount H T y := birthYear_spec H T y
  have hAnti := countAt_antitone M hN hI h T hT hHistory y
  have hChar : ∀ j ≤ T.length, countAt H T y j = oldCount H T y ↔ β ≤ j := by
    intro j hj
    constructor
    · exact fun hjEq => Nat.find_min' _ hjEq
    · intro hbj
      exact le_antisymm ((hAnti hbj).trans_eq he)
        ((countAt_length H T y).symm.trans_le (hAnti hj))
  have hEarly : ∀ j < β, oldCount H T y < countAt H T y j := by
    intro j hj
    have hjL : j ≤ T.length := (Nat.le_of_lt hj).trans hb
    have hle : oldCount H T y ≤ countAt H T y j :=
      (countAt_length H T y).symm.trans_le (hAnti hjL)
    have hne : countAt H T y j ≠ oldCount H T y :=
      Nat.find_min (p := fun i : ℕ => countAt H T y i = oldCount H T y)
        (show ∃ i : ℕ, countAt H T y i = oldCount H T y from
          ⟨T.length, countAt_length H T y⟩) hj
    exact lt_of_le_of_ne hle hne.symm
  refine ⟨hb, he.trans (countAt_length H T y).symm, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [countAt_length]
    exact hChar j hj
  · intro j hj
    rw [countAt_length]
    exact hEarly j hj
  · intro hPos
    rw [he]
    exact hEarly (β - 1) (by omega)
  · intro i j hbi hij hjL
    exact ((hChar i (hij.trans hjL)).mpr hbi).trans
      ((hChar j hjL).mpr (hbi.trans hij)).symm

/-- All forward years commute with literal restriction of the SAME whole tower.
The recursion uses the true restriction length, including actual empty steps. -/
theorem countAt_restrict
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower M T →
      IsOriginalBranchTestTower M H T → ∀ (U : Opens X) (p : openPreimage T U) (j : ℕ),
        countAt ((Subtype.val : U → X) ⁻¹' H) (restrict U T) p j = countAt H T p.val j
  | _, .refl, hT, hHistory, U, p, j => oldCount_restrict M hN hI h .refl hT hHistory U p
  | _, .step T C π hπ, hT, hHistory, U, p, j => by
      have hHistoryT : IsOriginalBranchTestTower M H T :=
        fun V B hSNC hUnion => (hHistory V B hSNC hUnion).1
      by_cases hj : j ≤ T.length
      · have hjU : j ≤ (restrict U T).length := by rw [length_restrict]; exact hj
        simp only [BlowupTowerTransforms.restrict, countAt, if_pos hjU, if_pos hj]
        exact countAt_restrict M hN hI h T hT.1 hHistoryT U ⟨π p.val, p.property⟩ j
      · have hjU : ¬ j ≤ (restrict U T).length := by rw [length_restrict]; exact hj
        simp only [BlowupTowerTransforms.restrict, countAt, if_neg hjU, if_neg hj]
        exact oldCount_restrict M hN hI h (.step T C π hπ) hT hHistory U p

/-- All forward years agree under an actual uncompressed whole-history
isomorphism. Neither branch labels nor numerical years are discarded. -/
theorem countAt_towerIso
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    {X' Y' : CMfd.{u} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : IsTowerIso Φ T' T χ) :
    IsGeoTestTower M T → IsOriginalBranchTestTower M H T → ∀ (y : Y') (j : ℕ),
      countAt (Φ ⁻¹' H) T' y j = countAt H T (χ y) j := by
  induction hIso with
  | refl =>
    intro hT hHistory y _j
    exact oldCount_towerIso M hN hI h IsTowerIso.refl hT hHistory y
  | @step Y' Y Z' Z T' T χ hIso C' π' hπ' C π hπ χ₁ hComm hC ih =>
    intro hT hHistory y j
    have hHistoryT : IsOriginalBranchTestTower M H T :=
      fun U B hSNC hUnion => (hHistory U B hSNC hUnion).1
    by_cases hj : j ≤ T.length
    · have hj' : j ≤ T'.length := by rw [hIso.length_eq]; exact hj
      simp only [countAt, if_pos hj', if_pos hj, hComm]
      exact ih hT.1 hHistoryT (π' y) j
    · have hj' : ¬ j ≤ T'.length := by rw [hIso.length_eq]; exact hj
      simp only [countAt, if_neg hj', if_neg hj]
      exact oldCount_towerIso M hN hI h
        (IsTowerIso.step hIso hπ' hπ χ₁ hComm hC) hT hHistory y

private theorem birthYear_eq_of_countAt_eq
    {X' Y' : CMfd.{u} n} (H' : Set X') (T' : BlowupTower X' Y') (y' : Y')
    (H : Set X) (T : BlowupTower X Y) (y : Y)
    (hLen : T'.length = T.length)
    (hCounts : ∀ j, countAt H' T' y' j = countAt H T y j) :
    birthYear H' T' y' = birthYear H T y := by
  have hEnd : oldCount H' T' y' = oldCount H T y := by
    rw [← countAt_length H' T' y', hLen, hCounts, countAt_length]
  apply le_antisymm
  · apply Nat.find_min'
    rw [hCounts, hEnd]
    exact birthYear_spec H T y
  · apply Nat.find_min'
    rw [← hCounts, ← hEnd]
    exact birthYear_spec H' T' y'

/-- First attainment of the terminal old count commutes with the literal
restriction of the whole history; no empty-year compression occurs. -/
theorem birthYear_restrict
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (U : Opens X) (p : openPreimage T U) :
    birthYear ((Subtype.val : U → X) ⁻¹' H) (restrict U T) p = birthYear H T p.val :=
  birthYear_eq_of_countAt_eq _ _ _ _ _ _ (length_restrict U T)
    (countAt_restrict M hN hI h T hT hHistory U p)

/-- First attainment commutes with an actual isomorphism of complete histories,
with their SAME literal length and all retained original/born slots. -/
theorem birthYear_towerIso
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    {X' Y' : CMfd.{u} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (y : Y') :
    birthYear (Φ ⁻¹' H) T' y = birthYear H T (χ y) :=
  birthYear_eq_of_countAt_eq _ _ _ _ _ _ hIso.length_eq
    (countAt_towerIso M hN hI h hIso hT hHistory y)

end
end Hironaka.HironakaOriginalNCCountHistory
