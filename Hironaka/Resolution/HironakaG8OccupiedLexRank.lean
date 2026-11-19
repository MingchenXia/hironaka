import Hironaka.Resolution.HironakaHomogeneousCanonicalResolution

set_option autoImplicit false
open Set
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8OccupiedLexRank

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  HironakaHomogeneousCanonicalResolution

/-- In one actual raw native chart, an occupied canonical step strictly
lowers the secondary value at every point of the new cosupport. The fixed
intrinsic HS epoch label can be retained as the first coordinate. -/
theorem occupied_chart_stage_lex_drop {n : ℕ} {X Y Z : CMfd.{0} n}
    (hn : 0 < n) (H : ℕ → ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (T : BlowupTower X Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCan : IsCanonical M ((invFamily hn n).inv M) (.step T C π hπ))
    (x : Y) (hx : x ∈ C)
    (z : Z) (hz : z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp) :
    Prod.Lex (fun a b : ℕ → ℕ => toLex a < toLex b) (· < ·)
      (H, (invFamily hn n).inv M (.step T C π hπ) z)
      (H, (invFamily hn n).inv M T x) := by
  obtain ⟨hT,hC⟩ := hCan
  rcases hC with hC | hC
  · simp [hC] at hx
  · subst C
    exact Prod.Lex.right H
      (value_lt_old_maximum_after_blowup (invFamily hn n) M hM T hT hx π hπ z hz)

/-- Even a two-coordinate natural lexicographic decrease does not imply
an increasing natural serialization rank. The direction is chronological:
a larger value precedes a smaller value. -/
theorem no_serial_rank_from_lex_decrease :
    ¬ ∃ r : ℕ × ℕ → ℕ, ∀ ⦃a b⦄,
      Prod.Lex (· < ·) (· < ·) b a → r a < r b := by
  rintro ⟨r,hr⟩
  have hChain (k : ℕ) : r (1,k+1) < r (1,k) :=
    hr (Prod.Lex.right 1 (Nat.lt_succ_self k))
  have hBound (k : ℕ) : r (1,k) + k ≤ r (1,0) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk := hChain k
      omega
  have := hBound (r (1,0) + 1)
  omega

#print axioms occupied_chart_stage_lex_drop
#print axioms no_serial_rank_from_lex_decrease

end Hironaka.HironakaG8OccupiedLexRank
