import Hironaka.Resolution.HironakaSmoothSubmersionOrderedCompressedImagePullback
import Hironaka.Resolution.HironakaSmoothSubmersionControlledTransform
import Hironaka.Resolution.HironakaStageCenters

/-! Ordinary smooth pullback of an actual finite tower with precisely its
empty source stages omitted. Physical target indices and original old slots
are retained. Blueprint first: `hironaka-g1-deleted-smooth-history.tex`.
This does not identify independently assigned intrinsic canonical centres. -/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG1DeletedSmoothHistory
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerSplit
  BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaStageCenters HironakaSmoothSubmersionBlowupLift
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionControlledTransform
  HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionOrderedCompressedImagePullback

variable {n m : ℕ}

/-- The held smooth structural trace refined by its exact retained physical
target numbers and the nonemptiness of every retained source centre. -/
inductive IsDeletedSmoothHistory {X : CMfd.{u} n} {Y : CMfd.{u} m} (f : Y → X) :
    {D' : CMfd.{u} m} → {D : CMfd.{u} n} → BlowupTower Y D' → BlowupTower X D →
      (D' → D) → List ℕ → Prop
  | refl (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f) :
      IsDeletedSmoothHistory f .refl .refl f []
  | matched {A' : CMfd.{u} m} {A : CMfd.{u} n} {B' : CMfd.{u} m} {B : CMfd.{u} n}
      {Q : BlowupTower Y A'} {T : BlowupTower X A} {g : A' → A} {L : List ℕ}
      (h : IsDeletedSmoothHistory f Q T g L) {C' : Set A'} {ρ : B' → A'}
      (hρ : IsBlowupAlong m C' ρ) {C : Set A} {π : B → A}
      (hπ : IsBlowupAlong n C π) (g₁ : B' → B)
      (hg : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g₁)
      (hcomm : ∀ x, π (g₁ x) = g (ρ x)) (hC : g ⁻¹' C = C')
      (hcart : HolomorphicSquarePullback g g₁ ρ π) (hne : C'.Nonempty) :
      IsDeletedSmoothHistory f (.step Q C' ρ hρ) (.step T C π hπ) g₁ (L ++ [T.length])
  | silent {A' : CMfd.{u} m} {A B : CMfd.{u} n}
      {Q : BlowupTower Y A'} {T : BlowupTower X A} {g : A' → A} {L : List ℕ}
      (h : IsDeletedSmoothHistory f Q T g L) {C : Set A} {π : B → A}
      (hπ : IsBlowupAlong n C π) (g₁ : A' → B)
      (hg : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g₁)
      (hcomm : ∀ x, π (g₁ x) = g x) (hC : g ⁻¹' C = ∅)
      (hcart : HolomorphicSquarePullback g g₁ (id : A' → A') π) :
      IsDeletedSmoothHistory f Q (.step T C π hπ) g₁ L

variable {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D} {L : List ℕ}

/-- This is a refinement of the existing geometric trace, not a new square foundation. -/
theorem IsDeletedSmoothHistory.toTrace (h : IsDeletedSmoothHistory f Q T g L) :
    IsSmoothTowerTrace f Q T g := by
  induction h with
  | refl hf => exact .refl hf
  | matched _ hρ hπ g₁ hg hc hC hcart _ ih =>
    exact .matched ih hρ hπ g₁ hg hc hC hcart
  | silent _ hπ g₁ hg hc hC hcart ih => exact .silent ih hπ g₁ hg hc hC hcart

theorem IsDeletedSmoothHistory.nonempty_centres (h : IsDeletedSmoothHistory f Q T g L) :
    StageCentres (fun _ C => C.Nonempty) Q := by
  induction h with
  | refl => trivial
  | matched _ _ _ _ _ _ _ _ hne ih => exact ⟨ih,hne⟩
  | silent _ _ _ _ _ _ _ ih => exact ih

/-- The list counts actual source blowups and is a strictly ordered subsequence
of the original physical target clock. -/
theorem IsDeletedSmoothHistory.physical_accounting (h : IsDeletedSmoothHistory f Q T g L) :
    L.length = Q.length ∧ L.Pairwise (· < ·) ∧ ∀ j ∈ L, j < T.length := by
  induction h with
  | refl => exact ⟨rfl,by simp,by simp⟩
  | @matched A' A B' B Q T g L h C' ρ hρ C π hπ g₁ hg hc hC hcart hne ih =>
    refine ⟨?_,?_,?_⟩
    · simpa only [List.length_append,List.length_singleton,BlowupTower.length_step] using
        congrArg (· + 1) ih.1
    · exact List.pairwise_append.mpr ⟨ih.2.1,by simp,by
        intro a ha b hb
        rw [List.mem_singleton.mp hb]
        exact ih.2.2 a ha⟩
    · intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · exact (ih.2.2 j hj).trans (Nat.lt_succ_self _)
      · rw [List.mem_singleton.mp hj]
        exact Nat.lt_succ_self _
  | silent _ _ _ _ _ _ _ ih =>
    exact ⟨ih.1,ih.2.1,fun j hj => (ih.2.2 j hj).trans (Nat.lt_succ_self _)⟩

/-- The actual source and actual deletion are constructed from ordinary inputs. -/
theorem exists_deleted_smooth_history
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (T : BlowupTower X D) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D) (L : List ℕ),
      IsDeletedSmoothHistory f Q T g L := by
  classical
  induction T with
  | refl => exact ⟨Y,.refl,f,[],.refl hf⟩
  | @step A B T C π hπ ih =>
    obtain ⟨A',Q,g,L,h⟩ := ih
    have hg := h.toTrace.isSubmersion
    by_cases hne : (g ⁻¹' C).Nonempty
    · obtain ⟨B',ρ,hρ⟩ := exists_actual_source_blowup hg hπ
      refine ⟨B',.step Q (g ⁻¹' C) ρ hρ,actualLift hg hπ hρ,L ++ [T.length],
        .matched h hρ hπ _ (HironakaSmoothSubmersionBlowupChoiceGeometry.actualLift_isSubmersion hg hπ hρ)
          (fun x => congrFun (actualLift_proj_comm hg hπ hρ) x) rfl ?_ hne⟩
      exact (IsActualTowerPullback.step (.refl hg) hg hπ hρ).universal
    · have he : g ⁻¹' C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hρ : IsBlowupAlong m (g ⁻¹' C) (id : A' → A') := by
        rw [he]
        exact BlowupExistenceCodimOne.isBlowupAlong_id_empty
      refine ⟨A',Q,actualLift hg hπ hρ,L,
        .silent h hπ _ (HironakaSmoothSubmersionBlowupChoiceGeometry.actualLift_isSubmersion hg hπ hρ)
          (fun x => congrFun (actualLift_proj_comm hg hπ hρ) x) he ?_⟩
      exact (IsActualTowerPullback.step (.refl hg) hg hπ hρ).universal

/-- Removing actual final target stages removes exactly the retained physical
indices beyond that chronological prefix. -/
theorem IsDeletedSmoothHistory.prefix (h : IsDeletedSmoothHistory f Q T g L) (j : ℕ) :
    ∃ (i : ℕ) (k : (split Q i).1 → (split T j).1),
      IsDeletedSmoothHistory f (head Q i) (head T j) k
        (L.filter (fun a => decide (a < T.length-j))) := by
  classical
  induction h generalizing j with
  | refl hf =>
    cases j <;> exact ⟨0,f,.refl hf⟩
  | @matched A' A B' B Q T g L h C' ρ hρ C π hπ g₁ hg hc hC hcart hne ih =>
    cases j with
    | zero =>
      refine ⟨0,?_⟩
      change ∃ k : B' → B, IsDeletedSmoothHistory f (Q.step C' ρ hρ) (T.step C π hπ) k _
      refine ⟨g₁,?_⟩
      have hfilt : (L ++ [T.length]).filter
          (fun a => decide (a < (T.step C π hπ).length)) = L ++ [T.length] :=
        List.filter_eq_self.mpr fun a ha => by
          simpa using (IsDeletedSmoothHistory.matched h hρ hπ g₁ hg hc hC hcart hne).physical_accounting.2.2 a ha
      change IsDeletedSmoothHistory f (Q.step C' ρ hρ) (T.step C π hπ) g₁
        ((L ++ [T.length]).filter (fun a => decide (a < (T.step C π hπ).length)))
      rw [hfilt]
      exact .matched h hρ hπ g₁ hg hc hC hcart hne
    | succ j =>
      obtain ⟨i,k,hk⟩ := ih j
      refine ⟨i+1,k,?_⟩
      change IsDeletedSmoothHistory f (head Q i) (head T j) k
        ((L ++ [T.length]).filter (fun a => decide (a < (T.length+1)-(j+1))))
      have hn : ¬ T.length < T.length-j := by omega
      simpa only [Nat.add_sub_add_right,List.filter_append,List.filter_cons,decide_eq_false hn,
        Bool.false_eq_true,↓reduceIte,List.filter_nil,List.append_nil] using hk
  | @silent A' A B Q T g L h C π hπ g₁ hg hc hC hcart ih =>
    cases j with
    | zero =>
      have hfilt : L.filter (fun a => decide (a < (T.step C π hπ).length)) = L :=
        List.filter_eq_self.mpr fun a ha => by
          simpa using (IsDeletedSmoothHistory.silent h hπ g₁ hg hc hC hcart).physical_accounting.2.2 a ha
      cases Q <;> refine ⟨0,g₁,?_⟩
      all_goals
        dsimp only [head,split,Nat.sub_zero]
        rw [hfilt]
        exact .silent h hπ g₁ hg hc hC hcart
    | succ j =>
      obtain ⟨i,k,hk⟩ := ih j
      refine ⟨i,k,?_⟩
      change IsDeletedSmoothHistory f (head Q i) (head T j) k
        (L.filter (fun a => decide (a < (T.length+1)-(j+1))))
      simpa only [Nat.add_sub_add_right] using hk

/-- Empty sources retain no physical blowup, including when target centres
are globally nonempty. -/
theorem IsDeletedSmoothHistory.empty_source (h : IsDeletedSmoothHistory f Q T g L)
    [IsEmpty Y] : Q.length = 0 ∧ L = [] := by
  have hQ : Q.length = 0 := by
    cases Q with
    | refl => rfl
    | step Q C π hπ =>
      obtain ⟨a,ha⟩ := h.nonempty_centres.2
      exact isEmptyElim (Q.proj a)
  exact ⟨hQ,List.length_eq_zero_iff.mp (h.physical_accounting.1.trans hQ)⟩

/-- All original slots, with neither empty slots nor duplicate slots removed. -/
def oldBoundaryAlong {X : CMfd.{u} n} (E : List (Set X)) :
    {D : CMfd.{u} n} → BlowupTower X D → List (Set D)
  | _, .refl => E
  | _, .step T C π _ => (oldBoundaryAlong E T).map (geoStrictTransform π C)

/-- Each physical target blowup contributes precisely one chronological slot. -/
def bornBoundaryAlong {X : CMfd.{u} n} :
    {D : CMfd.{u} n} → BlowupTower X D → List (Set D)
  | _, .refl => []
  | _, .step T C π _ => (bornBoundaryAlong T).map (geoStrictTransform π C) ++ [π ⁻¹' C]

theorem bornBoundaryAlong_length (T : BlowupTower X D) :
    (bornBoundaryAlong T).length = T.length := by
  induction T with
  | refl => rfl
  | step T C π hπ ih => simp only [bornBoundaryAlong,List.length_append,List.length_map,
      List.length_singleton,BlowupTower.length_step,ih]

theorem oldBoundaryAlong_closed (E : List (Set X)) (hE : ∀ A ∈ E, IsClosed A)
    (T : BlowupTower X D) : ∀ A ∈ oldBoundaryAlong E T, IsClosed A := by
  cases T with
  | refl => exact hE
  | step T C π hπ =>
    intro A hA
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hA
    exact isClosed_closure

theorem bornBoundaryAlong_closed (T : BlowupTower X D) :
    ∀ A ∈ bornBoundaryAlong T, IsClosed A := by
  cases T with
  | refl => simp [bornBoundaryAlong]
  | step T C π hπ =>
    intro A hA
    rcases List.mem_append.mp hA with hA | hA
    · obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hA
      exact isClosed_closure
    · rw [List.mem_singleton.mp hA]
      exact hπ.1.1.preimage hπ.contMDiff.continuous

/-- The actual marked boundary, with its full original old/born history. -/
theorem boundary_decomposition (M : MarkedIdeal n X) (T : BlowupTower X D) :
    (geoTransformAlong M T).E = oldBoundaryAlong M.E T ++ bornBoundaryAlong T := by
  induction T with
  | refl => simp [oldBoundaryAlong,bornBoundaryAlong]
  | step T C π hπ ih =>
    simp only [geoTransformAlong_step,geoTransform_E,oldBoundaryAlong,bornBoundaryAlong,
      ih,List.map_append,List.append_assoc]

/-- Reading physical birth numbers never changes old slots. -/
def selectBirths {A : Type*} (B : List (Set A)) (L : List ℕ) : List (Set A) :=
  L.map (fun j => B.getD j ∅)

private theorem getD_map_empty {A B : Type*} (F : Set A → Set B) (hF : F ∅ = ∅)
    (E : List (Set A)) (j : ℕ) :
    (E.map F).getD j ∅ = F (E.getD j ∅) := by
  simp only [List.getD,List.getElem?_map]
  cases E[j]? <;> simp [hF]

private theorem getD_append_left {A : Type*} (E : List (Set A)) (A' : Set A)
    (j : ℕ) (hj : j < E.length) :
    (E ++ [A']).getD j ∅ = E.getD j ∅ := by
  induction E generalizing j with
  | nil => simp at hj
  | cons B E ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j (by simpa using hj)

private theorem getD_append_last {A : Type*} (E : List (Set A)) (A' : Set A) :
    (E ++ [A']).getD E.length ∅ = A' := by
  induction E with
  | nil => rfl
  | cons B E ih => exact ih

private theorem getD_closed {A : Type*} [TopologicalSpace A] (E : List (Set A))
    (hE : ∀ B ∈ E, IsClosed B) (j : ℕ) : IsClosed (E.getD j ∅) := by
  induction E generalizing j with
  | nil => exact isClosed_empty
  | cons B E ih =>
    cases j with
    | zero => exact hE B (by simp)
    | succ j => exact ih (fun B hB => hE B (by simp [hB])) j

private theorem selectBirths_map {A B : Type*} (F : Set A → Set B) (hF : F ∅ = ∅)
    (E : List (Set A)) (L : List ℕ) :
    selectBirths (E.map F) L = (selectBirths E L).map F := by
  simp only [selectBirths,List.map_map]
  exact List.map_congr_left fun j _ => getD_map_empty F hF E j

private theorem selectBirths_append_left {A : Type*} (E : List (Set A)) (A' : Set A)
    (L : List ℕ) (hL : ∀ j ∈ L, j < E.length) :
    selectBirths (E ++ [A']) L = selectBirths E L := by
  apply List.map_congr_left
  intro j hj
  exact getD_append_left E A' j (hL j hj)

private theorem selectBirths_append_retained {A : Type*} (E : List (Set A)) (A' : Set A)
    (L : List ℕ) (hL : ∀ j ∈ L, j < E.length) :
    selectBirths (E ++ [A']) (L ++ [E.length]) = selectBirths E L ++ [A'] := by
  change (L ++ [E.length]).map _ = _
  rw [List.map_append]
  change selectBirths (E ++ [A']) L ++ [(E ++ [A']).getD E.length ∅] = _
  rw [selectBirths_append_left E A' L hL,getD_append_last]

private theorem strict_preimage_square {A B : CMfd.{u} n} {A' B' : CMfd.{u} m}
    {g : A' → A} {g₁ : B' → B} {π : B → A} {ρ : B' → A'}
    {C : Set A} {C' : Set A'}
    (hg : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g₁)
    (hc : ∀ x, π (g₁ x) = g (ρ x)) (hC : g ⁻¹' C = C') (H : Set A) :
    g₁ ⁻¹' geoStrictTransform π C H = geoStrictTransform ρ C' (g ⁻¹' H) := by
  unfold geoStrictTransform
  have hopen := HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion hg
  rw [hopen.preimage_closure_eq_closure_preimage hg.contMDiff.continuous]
  congr 1
  ext x
  change π (g₁ x) ∈ H \ C ↔ ρ x ∈ (g ⁻¹' H) \ C'
  rw [hc x,← hC]
  rfl

private theorem boundary_preimage_square {A B : CMfd.{u} n} {A' B' : CMfd.{u} m}
    {g : A' → A} {g₁ : B' → B} {π : B → A} {ρ : B' → A'}
    {C : Set A} {C' : Set A'}
    (hg : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g₁)
    (hc : ∀ x, π (g₁ x) = g (ρ x)) (hC : g ⁻¹' C = C') (E : List (Set A)) :
    (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).map (fun H => g₁ ⁻¹' H) =
      (E.map (fun H => g ⁻¹' H)).map (geoStrictTransform ρ C') ++ [ρ ⁻¹' C'] := by
  simp only [List.map_append,List.map_map,List.map_singleton]
  apply congrArg₂ (fun E F => E ++ F)
  · exact List.map_congr_left fun H _ => strict_preimage_square hg hc hC H
  · congr 1
    rw [← hC]
    ext x
    exact Iff.of_eq (congrArg (fun a => a ∈ C) (hc x))

private theorem strict_id_empty_closed {A : Type*} [TopologicalSpace A]
    (H : Set A) (hH : IsClosed H) : geoStrictTransform (id : A → A) ∅ H = H := by
  simpa only [geoStrictTransform,sdiff_empty,preimage_id_eq,id_eq] using hH.closure_eq

private theorem strict_id_empty_map {A : Type*} [TopologicalSpace A]
    (E : List (Set A)) (hE : ∀ H ∈ E, IsClosed H) :
    E.map (geoStrictTransform (id : A → A) ∅) = E := by
  calc
    E.map (geoStrictTransform (id : A → A) ∅) = E.map id :=
      List.map_congr_left fun H hH => strict_id_empty_closed H (hE H hH)
    _ = E := List.map_id E

/-- Every old label is transported literally, including empty and repeated labels. -/
theorem IsDeletedSmoothHistory.old_boundary_dictionary
    (h : IsDeletedSmoothHistory f Q T g L) (E : List (Set X))
    (hE : ∀ A ∈ E, IsClosed A) :
    oldBoundaryAlong (E.map (fun A => f ⁻¹' A)) Q =
      (oldBoundaryAlong E T).map (fun A => g ⁻¹' A) := by
  induction h with
  | refl => rfl
  | @matched A' A B' B Q T g L h C' ρ hρ C π hπ g₁ hg hc hC hcart hne ih =>
    change (oldBoundaryAlong (E.map (fun A => f ⁻¹' A)) Q).map (geoStrictTransform ρ C') = _
    rw [ih]
    simp only [oldBoundaryAlong,List.map_map]
    exact List.map_congr_left fun H _ => (strict_preimage_square hg hc hC H).symm
  | @silent A' A B Q T g L h C π hπ g₁ hg hc hC hcart ih =>
    rw [ih]
    change (oldBoundaryAlong E T).map (fun H => g ⁻¹' H) =
      ((oldBoundaryAlong E T).map (geoStrictTransform π C)).map (fun H => g₁ ⁻¹' H)
    rw [List.map_map]
    apply List.map_congr_left
    intro H hH
    change g ⁻¹' H = g₁ ⁻¹' geoStrictTransform π C H
    rw [strict_preimage_square hg hc hC H]
    exact (strict_id_empty_closed _ ((oldBoundaryAlong_closed E hE T H hH).preimage
      h.toTrace.isSubmersion.contMDiff.continuous)).symm

/-- The actual born boundary is selected by the original physical numbers;
original old slots are not part of this selection. -/
theorem IsDeletedSmoothHistory.born_boundary_dictionary
    (h : IsDeletedSmoothHistory f Q T g L) :
    bornBoundaryAlong Q = selectBirths ((bornBoundaryAlong T).map (fun A => g ⁻¹' A)) L := by
  induction h with
  | refl => rfl
  | @matched A' A B' B Q T g L h C' ρ hρ C π hπ g₁ hg hc hC hcart hne ih =>
    have hb := boundary_preimage_square hg hc hC (bornBoundaryAlong T)
    change (bornBoundaryAlong Q).map (geoStrictTransform ρ C') ++ [ρ ⁻¹' C'] =
      selectBirths (((bornBoundaryAlong T).map (geoStrictTransform π C) ++ [π ⁻¹' C]).map
        (fun H => g₁ ⁻¹' H)) (L ++ [T.length])
    rw [hb]
    have hlen : (((bornBoundaryAlong T).map (fun H => g ⁻¹' H)).map
        (geoStrictTransform ρ C')).length = T.length := by
      simp only [List.length_map,bornBoundaryAlong_length]
    have hL : ∀ j ∈ L, j < (((bornBoundaryAlong T).map (fun H => g ⁻¹' H)).map
        (geoStrictTransform ρ C')).length := by
      rw [hlen]
      exact h.physical_accounting.2.2
    rw [← hlen,selectBirths_append_retained _ _ L hL]
    rw [selectBirths_map (geoStrictTransform ρ C') (by simp [geoStrictTransform]),← ih]
  | @silent A' A B Q T g L h C π hπ g₁ hg hc hC hcart ih =>
    have hb := boundary_preimage_square hg hc hC (bornBoundaryAlong T)
    change bornBoundaryAlong Q =
      selectBirths (((bornBoundaryAlong T).map (geoStrictTransform π C) ++ [π ⁻¹' C]).map
        (fun H => g₁ ⁻¹' H)) L
    rw [hb]
    have hclosed : ∀ H ∈ (bornBoundaryAlong T).map (fun H => g ⁻¹' H), IsClosed H := by
      intro H hH
      obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hH
      exact (bornBoundaryAlong_closed T K hK).preimage h.toTrace.isSubmersion.contMDiff.continuous
    change bornBoundaryAlong Q = selectBirths
      (((bornBoundaryAlong T).map (fun H => g ⁻¹' H)).map
        (geoStrictTransform (id : A' → A') ∅) ++ [∅]) L
    rw [strict_id_empty_map _ hclosed]
    exact ih.trans (selectBirths_append_left _ _ L (by
      simpa only [List.length_map,bornBoundaryAlong_length] using h.physical_accounting.2.2)).symm

/-- Every omitted physical birth, including an interior one, has empty actual
preimage at the final stage. -/
theorem IsDeletedSmoothHistory.omitted_birth_empty
    (h : IsDeletedSmoothHistory f Q T g L) (j : ℕ) (hj : j < T.length) (hjL : j ∉ L) :
    g ⁻¹' ((bornBoundaryAlong T).getD j ∅) = ∅ := by
  induction h generalizing j with
  | refl => exact False.elim (Nat.not_lt_zero j hj)
  | @matched A' A B' B Q T g L h C' ρ hρ C π hπ g₁ hg hc hC hcart hne ih =>
    have hjne : j ≠ T.length := by
      intro he
      apply hjL
      simp [he]
    have hjold : j < T.length := by change j < T.length+1 at hj; omega
    have hjLold : j ∉ L := fun hmem => hjL (List.mem_append_left _ hmem)
    change g₁ ⁻¹' (((bornBoundaryAlong T).map (geoStrictTransform π C) ++ [π ⁻¹' C]).getD j ∅) = ∅
    rw [getD_append_left _ _ j (by simpa only [List.length_map,bornBoundaryAlong_length] using hjold),
      getD_map_empty (geoStrictTransform π C) (by simp [geoStrictTransform]),
      strict_preimage_square hg hc hC,ih j hjold hjLold]
    simp [geoStrictTransform]
  | @silent A' A B Q T g L h C π hπ g₁ hg hc hC hcart ih =>
    change g₁ ⁻¹' (((bornBoundaryAlong T).map (geoStrictTransform π C) ++ [π ⁻¹' C]).getD j ∅) = ∅
    by_cases hjold : j < T.length
    · rw [getD_append_left _ _ j (by simpa only [List.length_map,bornBoundaryAlong_length] using hjold),
        getD_map_empty (geoStrictTransform π C) (by simp [geoStrictTransform]),
        strict_preimage_square hg hc hC,ih j hjold hjL]
      simp [geoStrictTransform]
    · have he : j = ((bornBoundaryAlong T).map (geoStrictTransform π C)).length := by
        rw [List.length_map,bornBoundaryAlong_length]
        change j < T.length+1 at hj
        omega
      rw [he,getD_append_last]
      ext x
      change π (g₁ x) ∈ C ↔ x ∈ (∅ : Set A')
      rw [hc x]
      change x ∈ g ⁻¹' C ↔ x ∈ (∅ : Set A')
      rw [hC]

end
end Hironaka.HironakaG1DeletedSmoothHistory
