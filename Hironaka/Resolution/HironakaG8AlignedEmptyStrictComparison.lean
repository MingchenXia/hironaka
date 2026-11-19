import Hironaka.Resolution.HironakaG8CofinalOccupiedAncestry
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareAlgebra

/-! Empty-aware comparisons with aligned raw empty slots are strict. -/
set_option autoImplicit false
open Set
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8AlignedEmptyStrictComparison

open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  HironakaG3EmptyAwareHistory HironakaG8CofinalOccupiedAncestry
  HironakaNormalCrossingsOpenRestrictionSeparation

private theorem occupied_step_iff_of_lt {n : ℕ} {X Y Z : CMfd.{0} n}
    {T : BlowupTower X Y} {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π)
    {k : ℕ} (hk : k < T.length) :
    Occupied (.step T C π hπ) k ↔ Occupied T k := by
  exact ⟨fun h => h.resolve_right (fun h => (Nat.ne_of_lt hk) h.1),Or.inl⟩

private theorem occupied_last_iff {n : ℕ} {X Y Z : CMfd.{0} n}
    {T : BlowupTower X Y} {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π) :
    Occupied (.step T C π hπ) T.length ↔ C.Nonempty := by
  exact ⟨fun h => (h.resolve_left (fun h => Nat.lt_irrefl _ (occupied_lt_length T h))).2,
    fun h => Or.inr ⟨rfl,h⟩⟩

private theorem aligned_prefixes {n : ℕ} {X X' A B Y Y' : CMfd.{0} n}
    {S : BlowupTower X A} {T : BlowupTower X' B}
    {C : Set A} {D : Set B} {π : Y → A} {ρ : Y' → B}
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong n D ρ) (hLen : S.length = T.length)
    (hOcc : ∀ i, Occupied (.step S C π hπ) i ↔ Occupied (.step T D ρ hρ) i)
    (i : ℕ) : Occupied S i ↔ Occupied T i := by
  by_cases hi : i < S.length
  · exact (occupied_step_iff_of_lt hπ hi).symm.trans
      ((hOcc i).trans (occupied_step_iff_of_lt hρ (hLen ▸ hi)))
  · exact iff_of_false (fun hs => hi (occupied_lt_length S hs))
      (fun ht => hi (hLen.symm ▸ occupied_lt_length T ht))

/-- A physical empty-aware comparison preserves every literal constructor
when the raw lengths and the positions of occupied steps agree. -/
theorem isTowerIso_of_emptyAware_aligned {n : ℕ} {X X' Y Y' : CMfd.{0} n}
    {f : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X'}
    {g : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y'}
    {S : BlowupTower X Y} {T : BlowupTower X' Y'}
    (h : EmptyAwareTowerIso f S T g) (hLen : S.length = T.length)
    (hOcc : ∀ i, Occupied S i ↔ Occupied T i) :
    IsTowerIso f S T g := by
  cases h with
  | refl => exact .refl
  | @step A B Y Y' S T e h C π hπ D ρ hρ g hComm hC =>
    have hLen' : S.length = T.length := Nat.succ.inj hLen
    have hOcc' := aligned_prefixes hπ hρ hLen' hOcc
    exact .step (isTowerIso_of_emptyAware_aligned h hLen' hOcc') _ _ g hComm hC
  | @leftEmpty A Y' Y S T e h π hπ a ha =>
    cases T with
    | refl => simp [BlowupTower.length_step] at hLen
    | @step B Y' T D ρ hρ =>
      have hLen' : S.length = T.length := Nat.succ.inj hLen
      have hD : D = ∅ := by
        apply Set.not_nonempty_iff_eq_empty.mp
        intro hD
        have hO := (occupied_last_iff (T := T) hρ).mpr hD
        have hL := (hOcc T.length).mpr hO
        rw [← hLen'] at hL
        exact (occupied_last_iff (T := S) hπ).mp hL |>.ne_empty rfl
      subst D
      obtain ⟨b,hb⟩ := exists_empty_blowup_biholomorphism hρ
      have hBase := G3UniverseEmptyAwareCore.strip_right_empty hρ b hb h
      have hOcc' := aligned_prefixes hπ hρ hLen' hOcc
      refine .step (isTowerIso_of_emptyAware_aligned hBase hLen' hOcc') _ _ (a.trans e) ?_ ?_
      · intro x
        change ρ (e (a x)) = b (e (π x))
        rw [ha,hb]
      · exact preimage_empty
  | @rightEmpty Y B Y' S T e h ρ hρ b hb =>
    cases S with
    | refl => simp [BlowupTower.length_step] at hLen
    | @step A Y S C π hπ =>
      have hLen' : S.length = T.length := Nat.succ.inj hLen
      have hC : C = ∅ := by
        apply Set.not_nonempty_iff_eq_empty.mp
        intro hC
        have hO := (occupied_last_iff (T := S) hπ).mpr hC
        have hR := (hOcc S.length).mp hO
        rw [hLen'] at hR
        exact (occupied_last_iff (T := T) hρ).mp hR |>.ne_empty rfl
      subst C
      obtain ⟨a,ha⟩ := exists_empty_blowup_biholomorphism hπ
      have hBase := G3UniverseEmptyAwareCore.symm
        (G3UniverseEmptyAwareCore.strip_right_empty hπ a ha (G3UniverseEmptyAwareCore.symm h))
      have hOcc' := aligned_prefixes hπ hρ hLen' hOcc
      refine .step (isTowerIso_of_emptyAware_aligned hBase hLen' hOcc') _ _ (e.trans b.symm) ?_ ?_
      · intro x
        change ρ (b.symm (e x)) = e (a.symm (π x))
        rw [← hb,← ha]
        simp
      · exact preimage_empty
termination_by S.length + T.length
decreasing_by
  all_goals
    simp only [BlowupTower.length_step] at *
    omega

end Hironaka.HironakaG8AlignedEmptyStrictComparison
