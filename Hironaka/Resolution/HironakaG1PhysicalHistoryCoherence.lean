import Hironaka.Resolution.HironakaG1DeletedSmoothHistory
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalTerminalFunctor

/-! Structural identity and composition for actual deleted smooth histories.
Blueprint first: `hironaka-g1-physical-history-coherence.tex`.
No intrinsic analytic resolution assignment or centre compatibility is assumed. -/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG1PhysicalHistoryCoherence
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaStageCenters
  HironakaG1DeletedSmoothHistory HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionComposition HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionOriginalTerminalFunctor

variable {n m ℓ : ℕ}

/-- Substitute actual retained intermediate physical positions into the
original physical clock. Valid histories prove all reads are in range. -/
def composeRetained (L K : List ℕ) : List ℕ := K.map (fun i => L.getD i 0)

private theorem read_append_left (L : List ℕ) (a i : ℕ) (hi : i < L.length) :
    (L ++ [a]).getD i 0 = L.getD i 0 := by
  induction L generalizing i with
  | nil => simp at hi
  | cons b L ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using hi)

private theorem read_append_last (L : List ℕ) (a : ℕ) :
    (L ++ [a]).getD L.length 0 = a := by
  induction L with
  | nil => rfl
  | cons b L ih => exact ih

private theorem read_map_of_lt (F : ℕ → ℕ) (L : List ℕ) (i : ℕ) (hi : i < L.length) :
    (L.map F).getD i 0 = F (L.getD i 0) := by
  simp only [List.getD,List.getElem?_map,List.getElem?_eq_getElem hi,
    Option.map_some,Option.getD_some]

private theorem composeRetained_append_left (L K : List ℕ) (a : ℕ)
    (hK : ∀ i ∈ K, i < L.length) :
    composeRetained (L ++ [a]) K = composeRetained L K :=
  List.map_congr_left fun i hi => read_append_left L a i (hK i hi)

private theorem composeRetained_append_both (L K : List ℕ) (a : ℕ)
    (hK : ∀ i ∈ K, i < L.length) :
    composeRetained (L ++ [a]) (K ++ [L.length]) = composeRetained L K ++ [a] := by
  change (K ++ [L.length]).map _ = _
  rw [List.map_append]
  change composeRetained (L ++ [a]) K ++ [(L ++ [a]).getD L.length 0] = _
  rw [composeRetained_append_left L K a hK,read_append_last]

theorem composeRetained_identity_left (s : ℕ) (L : List ℕ)
    (hL : ∀ i ∈ L, i < s) : composeRetained (List.range s) L = L := by
  calc
    composeRetained (List.range s) L = L.map id := by
      apply List.map_congr_left
      intro i hi
      simp only [List.getD,List.getElem?_range (hL i hi),Option.getD_some,id_eq]
    _ = L := List.map_id L

theorem composeRetained_identity_right (L : List ℕ) :
    composeRetained L (List.range L.length) = L := by
  apply List.ext_getElem (by simp [composeRetained])
  intro i hi hi'
  simp only [composeRetained,List.getElem_map,List.getElem_range]
  simp only [List.getD,List.getElem?_eq_getElem hi',Option.getD_some]

theorem composeRetained_assoc (L K J : List ℕ) (hJ : ∀ i ∈ J, i < K.length) :
    composeRetained (composeRetained L K) J = composeRetained L (composeRetained K J) := by
  simp only [composeRetained,List.map_map]
  exact List.map_congr_left fun i hi => read_map_of_lt (fun j => L.getD j 0) K i (hJ i hi)

/-- Identity is literal on every physical step of an empty-free history. -/
theorem identity_of_nonempty_centres {X D : CMfd.{u} n} (T : BlowupTower X D)
    (hne : StageCentres (fun _ C => C.Nonempty) T) :
    IsDeletedSmoothHistory (id : X → X) T T (id : D → D) (List.range T.length) := by
  induction T with
  | refl => exact .refl Manifold.IsSubmersion.id
  | @step A B T C π hπ ih =>
    rw [BlowupTower.length_step,List.range_succ]
    refine .matched (ih hne.1) hπ hπ id Manifold.IsSubmersion.id
      (fun _ => rfl) rfl ?_ hne.2
    intro k P a b ha hb hc
    refine ⟨b,⟨hb,fun x => (hc x).symm,fun _ => rfl⟩,?_⟩
    intro c hc'
    exact funext hc'.2.2

/-- Structural composition of the complete physical histories, with literal
substitution of retained original indices. -/
theorem IsDeletedSmoothHistory.comp
    {X D : CMfd.{u} n} {Y D' : CMfd.{u} m} {f : Y → X} {g : D' → D}
    {Q : BlowupTower Y D'} {T : BlowupTower X D} {L : List ℕ}
    (H₁ : IsDeletedSmoothHistory f Q T g L) :
    ∀ {Z D'' : CMfd.{u} ℓ} {h : Z → Y} {k : D'' → D'}
      {R : BlowupTower Z D''} {K : List ℕ},
      IsDeletedSmoothHistory h R Q k K →
      IsDeletedSmoothHistory (f ∘ h) R T (g ∘ k) (composeRetained L K) := by
  induction H₁ with
  | refl hf =>
    intro Z D'' h k R K H₂
    cases H₂ with
    | refl hh => exact .refl (isSubmersion_composition hf hh)
  | @matched A' A B' B Q T g L H₁ C' ρ hρ C π hπ g₁ hg hc hC hcart hne ih =>
    intro Z D'' h k R K H₂
    cases H₂ with
    | @matched A'' A₀ B'' B₀ R Q₀ k₀ K₀ H₂ C'' τ hτ C₀ ρ₀ hρ₀ k₁ hk₁ hc₂ hC₂ hcart₂ hne₂ =>
      have hK : ∀ i ∈ K₀, i < L.length := by
        rw [H₁.physical_accounting.1]
        exact H₂.physical_accounting.2.2
      rw [← H₁.physical_accounting.1,composeRetained_append_both L K₀ T.length hK]
      refine .matched (ih H₂) hτ hπ (g₁ ∘ k) (isSubmersion_composition hg hk₁)
        (fun x => (hc (k x)).trans (congrArg g (hc₂ x))) ?_ ?_ hne₂
      · rw [preimage_comp,hC,hC₂]
      · exact holomorphicSquarePullback_pasting ρ τ π
          H₂.toTrace.isSubmersion.contMDiff hk₁.contMDiff hc₂ hcart hcart₂
    | @silent A'' A₀ B₀ R Q₀ k₀ K₀ H₂ C₀ ρ₀ hρ₀ k₁ hk₁ hc₂ hC₂ hcart₂ =>
      have hK : ∀ i ∈ K, i < L.length := by
        rw [H₁.physical_accounting.1]
        exact H₂.physical_accounting.2.2
      rw [composeRetained_append_left L K T.length hK]
      refine .silent (ih H₂) hπ (g₁ ∘ k) (isSubmersion_composition hg hk₁)
        (fun x => (hc (k x)).trans (congrArg g (hc₂ x))) ?_ ?_
      · rw [preimage_comp,hC,hC₂]
      · exact holomorphicSquarePullback_pasting ρ id π
          H₂.toTrace.isSubmersion.contMDiff hk₁.contMDiff hc₂ hcart hcart₂
  | @silent A' A B Q T g L H₁ C π hπ g₁ hg hc hC hcart ih =>
    intro Z D'' h k R K H₂
    have hk := H₂.toTrace.isSubmersion
    refine .silent (ih H₂) hπ (g₁ ∘ k) (isSubmersion_composition hg hk)
      (fun x => hc (k x)) ?_ ?_
    · rw [preimage_comp,hC,preimage_empty]
    · exact holomorphicSquarePullback_pasting id id π hk.contMDiff hk.contMDiff
        (fun _ => rfl) hcart (IsActualTowerPullback.refl hk).universal

/-- Ordinary two-step pullback internally supplies both deletions and their
actual structural composite on the same physical source tower R. -/
theorem exists_composed_deleted_smooth_history
    {X D : CMfd.{u} n} {Y : CMfd.{u} m} {Z : CMfd.{u} ℓ}
    {f : Y → X} {h : Z → Y}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel ℓ) 𝓘(ℂ,ComplexModel m) ∞ h)
    (T : BlowupTower X D) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D) (L : List ℕ)
      (D'' : CMfd.{u} ℓ) (R : BlowupTower Z D'') (k : D'' → D') (K : List ℕ),
      IsDeletedSmoothHistory f Q T g L ∧ IsDeletedSmoothHistory h R Q k K ∧
      IsDeletedSmoothHistory (f ∘ h) R T (g ∘ k) (composeRetained L K) := by
  obtain ⟨D',Q,g,L,H₁⟩ := exists_deleted_smooth_history hf T
  obtain ⟨D'',R,k,K,H₂⟩ := exists_deleted_smooth_history hh Q
  exact ⟨D',Q,g,L,D'',R,k,K,H₁,H₂,IsDeletedSmoothHistory.comp H₁ H₂⟩

/-- The same actual composite history transports the entire original old list
and exactly its selected physical births; no old slot is filtered. -/
theorem composed_boundary_dictionaries
    {X D : CMfd.{u} n} {Y D' : CMfd.{u} m} {Z D'' : CMfd.{u} ℓ}
    {f : Y → X} {h : Z → Y} {g : D' → D} {k : D'' → D'}
    {Q : BlowupTower Y D'} {T : BlowupTower X D} {R : BlowupTower Z D''}
    {L K : List ℕ} (H₁ : IsDeletedSmoothHistory f Q T g L)
    (H₂ : IsDeletedSmoothHistory h R Q k K) (E : List (Set X))
    (hE : ∀ A ∈ E, IsClosed A) :
    oldBoundaryAlong ((E.map (fun A => f ⁻¹' A)).map (fun A => h ⁻¹' A)) R =
        (oldBoundaryAlong E T).map (fun A => (g ∘ k) ⁻¹' A) ∧
      bornBoundaryAlong R = selectBirths ((bornBoundaryAlong T).map (fun A => (g ∘ k) ⁻¹' A))
        (composeRetained L K) ∧
      ∀ j < T.length, j ∉ composeRetained L K →
        (g ∘ k) ⁻¹' ((bornBoundaryAlong T).getD j ∅) = ∅ := by
  have H := IsDeletedSmoothHistory.comp H₁ H₂
  refine ⟨?_,H.born_boundary_dictionary,H.omitted_birth_empty⟩
  rw [List.map_map]
  exact H.old_boundary_dictionary E hE

end
end Hironaka.HironakaG1PhysicalHistoryCoherence
