import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.Invariant.DivisorExponentAlong

set_option autoImplicit false

/-! True unit rows remain actual whole units for every marked quotient, without
row admissibility, and all actual canonical columns vanish.
Blueprint: `hironaka-g4-unit-row-geo-transform.tex`. -/

open Set Filter Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4UnitRowGeoTransform

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  InvertibleIdealQuotient GermIdealOrder DivisorExponentAlong

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The whole actual quotient is the unit ideal, for any original natural mark.
No admissibility of the unit row is required. -/
theorem geoTransform_mem_iff_holomorphic_of_one_mem
    {M : MarkedIdeal n X} {C : Set X} {π : Y → X} {z : Y}
    (hUnit : M.ideal.mem (π z) (fun _ => (1 : ℂ))) (g : Y → ℂ) :
    (M.geoTransform C π).ideal.mem z g ↔ HolomorphicAt n g z := by
  have hPB : (GermIdeal.pullback (m := n) π M.ideal).mem z (fun _ => (1 : ℂ)) :=
    GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨fun _ => (1 : ℂ), hUnit, rfl⟩ (holomorphicAt_const 1))
  constructor
  · intro hg
    exact hg.1
  · intro hg
    refine ⟨hg, ?_⟩
    intro f hf
    have hfhol := holomorphicAt_of_mem_idealPow hf
    refine ⟨hfhol.mul hg, 1, (fun _ => fun _ => (1 : ℂ)),
      (fun _ => fun y => f y * g y), (fun _ => hPB), (fun _ => hfhol.mul hg), ?_⟩
    filter_upwards with y _hy
    simp

private theorem divExpAlong_eq_zero_of_one_mem
    {N H : Set Y} {I : GermIdeal n Y} {z : Y}
    (hClosed : IsClosed (N ∩ H)) (hUnit : I.mem z (fun _ => (1 : ℂ))) :
    divExpAlong n N I H z = 0 := by
  by_cases hz : z ∈ N ∩ H
  · have hnot : ¬ IsDivNearAlong n N I H 1 z := by
      intro hDiv
      have hCos := hDiv.self_of_nhds hz.1 hz.2
      have hVan := hCos.2 (fun _ => (1 : ℂ)) hUnit
      have hZero := (vanishesToOrderOn_one_iff hz.1 (holomorphicAt_const 1)).mp hVan
      exact one_ne_zero hZero
    have hFin : ∃ e, ¬ IsDivNearAlong n N I H (e + 1) z := ⟨0, hnot⟩
    rw [divExpAlong, dif_pos hFin]
    exact (Nat.find_eq_zero hFin).mpr hnot
  · have hInf : ¬ ∃ e, ¬ IsDivNearAlong n N I H (e + 1) z := by
      rintro ⟨e, he⟩
      exact he (isDivNearAlong_of_notMem hClosed hz (e + 1))
    rw [divExpAlong, dif_neg hInf]

/-- The literal full transformed boundary has zero canonical columns for an
actual unit row, without assigning that row an admissible positive mark. -/
theorem canonical_columns_geoTransform_of_one_mem
    {M : MarkedIdeal n X} {C : Set X}
    {π : Y → X} (hπ : IsBlowupAlong n C π) {z : Y}
    (hUnit : M.ideal.mem (π z) (fun _ => (1 : ℂ))) :
    ∀ j : Fin (M.geoTransform C π).E.length,
      divExpAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal
        ((M.geoTransform C π).E.get j) z = 0 := by
  have hOne := (geoTransform_mem_iff_holomorphic_of_one_mem (C := C) hUnit
    (fun _ => (1 : ℂ))).mpr (holomorphicAt_const 1)
  have hN : IsClosed (M.geoTransform C π).N := isClosed_closure
  have hE : ∀ H ∈ (M.geoTransform C π).E, IsClosed H := by
    intro H hH
    change H ∈ M.E.map (geoStrictTransform π C) ++ [π ⁻¹' C] at hH
    rcases List.mem_append.mp hH with hOld | hNew
    · obtain ⟨A, _hA, rfl⟩ := List.mem_map.mp hOld
      exact isClosed_closure
    · have hEq := List.mem_singleton.mp hNew
      subst H
      exact hπ.1.1.preimage hπ.contMDiff.continuous
  intro j
  exact divExpAlong_eq_zero_of_one_mem
    (hN.inter (hE _ (List.get_mem _ j))) hOne

end

end Hironaka.HironakaG4UnitRowGeoTransform
