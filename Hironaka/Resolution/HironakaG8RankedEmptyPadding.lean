import Hironaka.Resolution.HironakaG8StageRankCoherence

/-! Literal stage synchronization by inserting real empty identity blowups. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8RankedEmptyPadding
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  HironakaG3EmptyAwareHistory HironakaSharpActualCurveEmptyPadding
  BlowupTowerTransforms BlowupTowerIsoTail BlowupRestrictOpen

variable {n : ℕ} {X Y A B : CMfd.{0} n}

/-- Assign a chronological zero-based slot to each literal step of a tower.
The index is one past the final assigned slot, or zero for a reflexive tower. -/
inductive RankedTower (X : CMfd.{0} n) : {Y : CMfd.{0} n} → BlowupTower X Y → ℕ → Type 1
  | refl : RankedTower X (.refl : BlowupTower X X) 0
  | step {Y Z : CMfd.{0} n} {T : BlowupTower X Y} {i k : ℕ}
      (D : RankedTower X T i) (h : i ≤ k)
      {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π) :
      RankedTower X (.step T C π hπ) (k+1)

/-- The physical padded tower has exactly the original endpoint. -/
def RankedTower.pad : {Y : CMfd.{0} n} → {T : BlowupTower X Y} → {i : ℕ} →
    RankedTower X T i → BlowupTower X Y
  | _,_,_,.refl => .refl
  | _,_,_,@RankedTower.step _ _ Y _ _ i k D _ C π hπ =>
    .step (D.pad.append (identityEmptyTail Y (k-i))) C π hπ

def RankedTower.through {T : BlowupTower X Y} {i : ℕ} (D : RankedTower X T i) (k : ℕ) :
    BlowupTower X Y :=
  D.pad.append (identityEmptyTail Y (k-i))

theorem RankedTower.pad_length {T : BlowupTower X Y} {i : ℕ} (D : RankedTower X T i) :
    D.pad.length = i := by
  induction D with
  | refl => rfl
  | step D h hπ ih =>
    simp only [RankedTower.pad,BlowupTower.length_step,BlowupTower.length_append,
      identityEmptyTail_length,ih]
    omega

theorem RankedTower.through_length {T : BlowupTower X Y} {i k : ℕ} (D : RankedTower X T i)
    (h : i ≤ k) : (D.through k).length = k := by
  simp only [RankedTower.through,BlowupTower.length_append,identityEmptyTail_length,D.pad_length]
  omega

theorem RankedTower.through_extend {T : BlowupTower X Y} {i k N : ℕ}
    (D : RankedTower X T i) (hi : i ≤ k) (hk : k ≤ N) :
    D.through N = (D.through k).append (identityEmptyTail Y (N-k)) := by
  simp only [RankedTower.through,BlowupTower.append_assoc,← identityEmptyTail_append]
  congr 2
  omega

theorem RankedTower.through_succ {T : BlowupTower X Y} {i k : ℕ}
    (D : RankedTower X T i) (h : i ≤ k) :
    D.through (k+1) = .step (D.through k) ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty := by
  have h' := D.through_extend h (show k ≤ k+1 by omega)
  have hSub : k+1-k = 1 := by omega
  rw [hSub] at h'
  exact h'

/-- A matched step uses the same slot on both sides. A unilateral empty
step has a slot after all steps already consumed on the other side. This
is a condition on the empty-aware derivation and uses no strict tower iso. -/
inductive ClockComparison (φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A) :
    {Y B : CMfd.{0} n} → {T : BlowupTower X Y} → {S : BlowupTower A B} →
    {i j : ℕ} → RankedTower X T i → RankedTower A S j →
    (Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B) → Prop
  | refl : ClockComparison φ .refl .refl φ
  | pair {Y B Z W : CMfd.{0} n} {T : BlowupTower X Y} {S : BlowupTower A B}
      {i j k : ℕ} {D : RankedTower X T i} {F : RankedTower A S j}
      {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
      (h : ClockComparison φ D F ψ) (hi : i ≤ k) (hj : j ≤ k)
      {C : Set Y} {C' : Set B} {π : Z → Y} {ρ : W → B}
      (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong n C' ρ)
      (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ W)
      (hMap : ∀ z, ρ (χ z) = ψ (π z)) (hC : ψ ⁻¹' C' = C) :
      ClockComparison φ (.step D hi hπ) (.step F hj hρ) χ
  | left {Y B Z : CMfd.{0} n} {T : BlowupTower X Y} {S : BlowupTower A B}
      {i j k : ℕ} {D : RankedTower X T i} {F : RankedTower A S j}
      {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
      (h : ClockComparison φ D F ψ) (hi : i ≤ k) (hj : j ≤ k)
      {π : Z → Y} (hπ : IsBlowupAlong n (∅ : Set Y) π)
      (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y) (he : ∀ z, e z = π z) :
      ClockComparison φ (.step D hi hπ) F (e.trans ψ)
  | right {Y B W : CMfd.{0} n} {T : BlowupTower X Y} {S : BlowupTower A B}
      {i j k : ℕ} {D : RankedTower X T i} {F : RankedTower A S j}
      {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
      (h : ClockComparison φ D F ψ) (hi : i ≤ k) (hj : j ≤ k)
      {ρ : W → B} (hρ : IsBlowupAlong n (∅ : Set B) ρ)
      (e : W ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B) (he : ∀ z, e z = ρ z) :
      ClockComparison φ D (.step F hj hρ) (ψ.trans e.symm)

private theorem padBoth {T : BlowupTower X Y} {S : BlowupTower A B}
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    (h : IsTowerIso φ T S ψ) (k : ℕ) :
    IsTowerIso φ (T.append (identityEmptyTail Y k)) (S.append (identityEmptyTail B k)) ψ := by
  induction k with
  | zero => exact h
  | succ k ih =>
    exact .step ih BlowupExistenceCodimOne.isBlowupAlong_id_empty
      BlowupExistenceCodimOne.isBlowupAlong_id_empty ψ (fun _ => rfl) preimage_empty

/-- The strict comparison holds at the exact same cutoff and with the
same endpoint biholomorphism as the supplied physical comparison. -/
theorem ClockComparison.isTowerIso_through
    {T : BlowupTower X Y} {S : BlowupTower A B} {i j : ℕ}
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {D : RankedTower X T i} {F : RankedTower A S j}
    (h : ClockComparison φ D F ψ) (N : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    IsTowerIso φ (D.through N) (F.through N) ψ := by
  induction h generalizing N with
  | refl => exact padBoth .refl N
  | @pair Y B Z W T S i j k D F ψ h hDi hFj C C' π ρ hπ hρ χ hMap hC ih =>
    have hh := IsTowerIso.step (ih k hDi hFj) hπ hρ χ hMap hC
    exact padBoth hh (N-(k+1))
  | @left Y B Z T S i j k D F ψ h hDi hFj π hπ e he ih =>
    have hStep : IsTowerIso φ
        (.step (D.through k) ∅ π hπ)
        (.step (F.through k) ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty)
        (e.trans ψ) :=
      .step (ih k hDi hFj) hπ BlowupExistenceCodimOne.isBlowupAlong_id_empty _ (fun z => by
        change ψ (e z) = ψ (π z)
        rw [he]) preimage_empty
    rw [F.through_extend (show j ≤ k+1 by omega) hi, F.through_succ hFj]
    exact padBoth hStep (N-(k+1))
  | @right Y B W T S i j k D F ψ h hDi hFj ρ hρ e he ih =>
    have hStep : IsTowerIso φ
        (.step (D.through k) ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty)
        (.step (F.through k) ∅ ρ hρ)
        (ψ.trans e.symm) :=
      .step (ih k hDi hFj) BlowupExistenceCodimOne.isBlowupAlong_id_empty hρ _ (fun z => by
        change ρ (e.symm (ψ z)) = ψ z
        rw [← he,e.apply_symm_apply]) preimage_empty
    rw [D.through_extend (show i ≤ k+1 by omega) hj, D.through_succ hDi]
    exact padBoth hStep (N-(k+1))


/-- An unmatched empty step can be inserted at its assigned slot even if
the other side has already consumed later unmatched empty steps. -/
theorem ClockComparison.left_any
    {T : BlowupTower X Y} {S : BlowupTower A B} {i j : ℕ}
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {D : RankedTower X T i} {F : RankedTower A S j} (h : ClockComparison φ D F ψ) :
    ∀ {V : CMfd.{0} n} {k : ℕ} (hi : i ≤ k) {π : V → Y}
      (hπ : IsBlowupAlong n (∅ : Set Y) π)
      (e : V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y) (_he : ∀ z, e z = π z),
      ClockComparison φ (.step D hi hπ) F (e.trans ψ) := by
  induction h with
  | refl =>
    intro V k hi π hπ e he
    exact .left .refl hi (Nat.zero_le _) hπ e he
  | pair h hDi hFj hπ hρ χ hMap hC ih =>
    intro V k hi π hπ' e he
    exact .left (.pair h hDi hFj hπ hρ χ hMap hC) hi hi hπ' e he
  | left h hDi hFj hπ g hg ih =>
    intro V k hi π hπ' e he
    exact .left (.left h hDi hFj hπ g hg) hi (by omega) hπ' e he
  | @right Y B W T S i j l D F ψ h hDi hFj ρ hρ g hg ih =>
    intro V k hi π hπ e he
    by_cases hLater : l+1 ≤ k
    · exact .left (.right h hDi hFj hρ g hg) hi hLater hπ e he
    by_cases hEq : k = l
    · subst k
      exact .pair h hi hFj hπ hρ (e.trans (ψ.trans g.symm)) (fun z => by
        change ρ (g.symm (ψ (e z))) = ψ (π z)
        rw [← hg,g.apply_symm_apply,he]) preimage_empty
    · exact .right (ih hi hπ e he) (by omega) hFj hρ g hg


/-- The right-handed form of insertion at an arbitrary assigned empty slot. -/
theorem ClockComparison.right_any
    {T : BlowupTower X Y} {S : BlowupTower A B} {i j : ℕ}
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {D : RankedTower X T i} {F : RankedTower A S j} (h : ClockComparison φ D F ψ) :
    ∀ {V : CMfd.{0} n} {k : ℕ} (hj : j ≤ k) {ρ : V → B}
      (hρ : IsBlowupAlong n (∅ : Set B) ρ)
      (e : V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B) (_he : ∀ z, e z = ρ z),
      ClockComparison φ D (.step F hj hρ) (ψ.trans e.symm) := by
  induction h with
  | refl =>
    intro V k hj ρ hρ e he
    exact .right .refl (Nat.zero_le _) hj hρ e he
  | pair h hDi hFj hπ hρ χ hMap hC ih =>
    intro V k hj ρ hρ' e he
    exact .right (.pair h hDi hFj hπ hρ χ hMap hC) hj hj hρ' e he
  | right h hDi hFj hρ g hg ih =>
    intro V k hj ρ hρ' e he
    exact .right (.right h hDi hFj hρ g hg) (by omega) hj hρ' e he
  | @left Y B W T S i j l D F ψ h hDi hFj π hπ g hg ih =>
    intro V k hj ρ hρ e he
    by_cases hLater : l+1 ≤ k
    · exact .right (.left h hDi hFj hπ g hg) hLater hj hρ e he
    by_cases hEq : k = l
    · subst k
      exact .pair h hDi hj hπ hρ ((g.trans ψ).trans e.symm) (fun z => by
        change ρ (e.symm (ψ (g z))) = ψ (π z)
        rw [← he,e.apply_symm_apply,hg]) preimage_empty
    · exact .left (ih hj hρ e he) hDi (by omega) hπ g hg

/-- The empty-aware comparison annotated only by equality of the slots of
matched occupied steps. Empty steps on either side carry no rank equations. -/
inductive OccupiedComparison (φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A) :
    {Y B : CMfd.{0} n} → {T : BlowupTower X Y} → {S : BlowupTower A B} →
    {i j : ℕ} → RankedTower X T i → RankedTower A S j →
    (Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B) → Prop
  | refl : OccupiedComparison φ .refl .refl φ
  | pair {Y B Z W : CMfd.{0} n} {T : BlowupTower X Y} {S : BlowupTower A B}
      {i j k l : ℕ} {D : RankedTower X T i} {F : RankedTower A S j}
      {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
      (h : OccupiedComparison φ D F ψ) (hi : i ≤ k) (hj : j ≤ l)
      {C : Set Y} {C' : Set B} {π : Z → Y} {ρ : W → B}
      (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong n C' ρ)
      (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ W)
      (hMap : ∀ z, ρ (χ z) = ψ (π z)) (hC : ψ ⁻¹' C' = C)
      (hSlot : C.Nonempty → k = l) :
      OccupiedComparison φ (.step D hi hπ) (.step F hj hρ) χ
  | left {Y B Z : CMfd.{0} n} {T : BlowupTower X Y} {S : BlowupTower A B}
      {i j k : ℕ} {D : RankedTower X T i} {F : RankedTower A S j}
      {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
      (h : OccupiedComparison φ D F ψ) (hi : i ≤ k)
      {π : Z → Y} (hπ : IsBlowupAlong n (∅ : Set Y) π)
      (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y) (he : ∀ z, e z = π z) :
      OccupiedComparison φ (.step D hi hπ) F (e.trans ψ)
  | right {Y B W : CMfd.{0} n} {T : BlowupTower X Y} {S : BlowupTower A B}
      {i j k : ℕ} {D : RankedTower X T i} {F : RankedTower A S j}
      {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
      (h : OccupiedComparison φ D F ψ) (hj : j ≤ k)
      {ρ : W → B} (hρ : IsBlowupAlong n (∅ : Set B) ρ)
      (e : W ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B) (he : ∀ z, e z = ρ z) :
      OccupiedComparison φ D (.step F hj hρ) (ψ.trans e.symm)

theorem OccupiedComparison.clockComparison
    {T : BlowupTower X Y} {S : BlowupTower A B} {i j : ℕ}
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {D : RankedTower X T i} {F : RankedTower A S j} (h : OccupiedComparison φ D F ψ) :
    ClockComparison φ D F ψ := by
  induction h with
  | refl => exact .refl
  | left h hi hπ e he ih => exact ih.left_any hi hπ e he
  | right h hj hρ e he ih => exact ih.right_any hj hρ e he
  | @pair Y B Z W T S i j k l D F ψ h hi hj C C' π ρ hπ hρ χ hMap hC hSlot ih =>
    by_cases hOccupied : C.Nonempty
    · have hEq := hSlot hOccupied
      subst l
      exact .pair ih hi hj hπ hρ χ hMap hC
    have hEmpty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hOccupied
    have hEmpty' : C' = ∅ := by
      rw [hEmpty,← Set.preimage_empty (f := ψ)] at hC
      exact ψ.surjective.preimage_injective hC
    subst C
    subst C'
    obtain ⟨e,he⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ
    obtain ⟨g,hg⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hρ
    have hχ : χ = (e.trans ψ).trans g.symm := by
      ext z
      apply g.injective
      change g (χ z) = g (g.symm (ψ (e z)))
      rw [g.apply_symm_apply,hg,he,hMap]
    rw [hχ]
    exact (ih.left_any hi hπ e he).right_any hj hρ g hg

/-- Matching occupied slots are sufficient to attain strict isomorphism
after the literal rank padding. All empty-step matching is constructed. -/
theorem OccupiedComparison.isTowerIso_through
    {T : BlowupTower X Y} {S : BlowupTower A B} {i j : ℕ}
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {D : RankedTower X T i} {F : RankedTower A S j}
    (h : OccupiedComparison φ D F ψ) (N : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    IsTowerIso φ (D.through N) (F.through N) ψ :=
  h.clockComparison.isTowerIso_through N hi hj


/-- The local schedule retains its clock under restriction, even when a
nonempty original centre has an empty trace on the overlap. -/
def RankedTower.restrict (U : Opens X) : {Y : CMfd.{0} n} → {T : BlowupTower X Y} →
    {i : ℕ} → RankedTower X T i → RankedTower (CMfd.of (n := n) U) (restrict U T) i
  | _,_,_,.refl => .refl
  | _,_,_,@RankedTower.step _ _ V _ T _ k D h C π hπ =>
    .step (D.restrict U) h
      (isBlowupAlong_restrict hπ (openPreimage T U)
        ((openPreimage T U).isOpen.preimage hπ.contMDiff.continuous))

theorem RankedTower.pad_proj {T : BlowupTower X Y} {i : ℕ} (D : RankedTower X T i) :
    D.pad.proj = T.proj := by
  induction D with
  | refl => rfl
  | step D h hπ ih =>
    simp only [RankedTower.pad,BlowupTower.proj_step,BlowupTower.proj_append,
      identityEmptyTail_proj,Function.comp_id,ih]

theorem RankedTower.through_proj {T : BlowupTower X Y} {i : ℕ}
    (D : RankedTower X T i) (k : ℕ) : (D.through k).proj = T.proj := by
  simp only [RankedTower.through,BlowupTower.proj_append,identityEmptyTail_proj,
    Function.comp_id,D.pad_proj]

private theorem openPreimage_eq_of_proj {T S : BlowupTower X Y}
    (h : T.proj = S.proj) (U : Opens X) : openPreimage T U = openPreimage S U := by
  ext y
  change T.proj y ∈ U ↔ S.proj y ∈ U
  rw [h]

private def restrictPadEnd (U : Opens X) (T : BlowupTower X Y) (q : ℕ) :
    CMfd.of (n := n) (openPreimage (T.append (identityEmptyTail Y q)) U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T U) :=
  opensCongr (openPreimage_eq_of_proj (by rw [BlowupTower.proj_append,identityEmptyTail_proj,Function.comp_id]) U)

private theorem isTowerIso_restrict_identity_padding (U : Opens X) (T : BlowupTower X Y) (q : ℕ) :
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      (restrict U (T.append (identityEmptyTail Y q)))
      ((restrict U T).append (identityEmptyTail (CMfd.of (n := n) (openPreimage T U)) q))
      (restrictPadEnd U T q) := by
  induction q with
  | zero =>
    have h : restrictPadEnd U T 0 = Diffeomorph.refl
        𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (openPreimage T U)) ∞ :=
      Diffeomorph.ext (fun _ => rfl)
    rw [h]
    exact IsTowerIso.refl_self _
  | succ q ih =>
    refine IsTowerIso.step ih _ _ (restrictPadEnd U T (q+1)) (fun _ => Subtype.ext rfl) ?_
    exact preimage_empty

/-- Padded histories on overlap restrictions are the restrictions of the
original padded histories, with the identity on the underlying endpoint points. -/
theorem RankedTower.restrict_pad_iso (U : Opens X) {T : BlowupTower X Y} {i : ℕ}
    (D : RankedTower X T i) :
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      (BlowupTowerTransforms.restrict U D.pad) (D.restrict U).pad
      (opensCongr (openPreimage_eq_of_proj D.pad_proj U)) := by
  induction D with
  | refl => exact .refl
  | @step Y Z T i k D h C π hπ ih =>
    have hPre := (isTowerIso_restrict_identity_padding U D.pad (k-i)).trans (padBoth ih (k-i))
    refine IsTowerIso.step hPre _ _ (opensCongr (openPreimage_eq_of_proj
      (RankedTower.step D h hπ).pad_proj U)) (fun _ => Subtype.ext rfl) ?_
    ext y
    rfl


/-- The same restriction law holds through a prescribed common clock. -/
theorem RankedTower.restrict_through_iso (U : Opens X) {T : BlowupTower X Y} {i : ℕ}
    (D : RankedTower X T i) (N : ℕ) :
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      (BlowupTowerTransforms.restrict U (D.through N)) ((D.restrict U).through N)
      (opensCongr (openPreimage_eq_of_proj (D.through_proj N) U)) := by
  have hm := (isTowerIso_restrict_identity_padding U D.pad (N-i)).trans
    (padBoth (D.restrict_pad_iso U) (N-i))
  apply BlowupTowerSplitIso.IsTowerIso.congr_last hm
  intro z
  exact Subtype.ext rfl

/-- Exact comparison on the literal restrictions of padded charts.
The supplied rank agreement is only on the original overlap's occupied
steps. Ranks of the empty traces can differ. -/
theorem strict_overlap_of_ranked_occupied_comparison {T : BlowupTower X Y}
    {S : BlowupTower A B} {i j : ℕ} (D : RankedTower X T i) (F : RankedTower A S j)
    (U : Opens X) (V : Opens A)
    (φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V)
    (ψ : CMfd.of (n := n) (openPreimage T U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage S V))
    (h : OccupiedComparison φ (D.restrict U) (F.restrict V) ψ) (N : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    ∃ χ : CMfd.of (n := n) (openPreimage (D.through N) U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage (F.through N) V),
      IsTowerIso φ (restrict U (D.through N)) (restrict V (F.through N)) χ ∧
      ∀ z, (χ z).val = (ψ ⟨z.val,by
        have hz := z.property
        change (D.through N).proj z.val ∈ U at hz
        rwa [D.through_proj N] at hz⟩).val := by
  have hh := ((D.restrict_through_iso U N).trans (h.isTowerIso_through N hi hj)).trans
    (F.restrict_through_iso V N).symm
  refine ⟨((opensCongr (openPreimage_eq_of_proj (D.through_proj N) U)).trans ψ).trans
    (opensCongr (openPreimage_eq_of_proj (F.through_proj N) V)).symm, ?_,fun z => ?_⟩
  · apply BlowupTowerSplitIso.IsTowerIso.congr_base hh
    intro z
    rfl
  · rfl


end
end Hironaka.HironakaG8RankedEmptyPadding
