import Hironaka.Resolution.HironakaG1DeletedHistoryChoiceComparison

/-! Actual full-clock pullback followed by genuine physical deletion.
The retained indices are the SAME literal target physical indices.
Blueprint first: `hironaka-g1-actual-deleted-history-composition.tex`. -/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG1ActualDeletedHistoryComposition
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  HironakaG1DeletedSmoothHistory HironakaG1DeletedHistoryChoiceComparison
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionComposition
  HironakaSmoothSubmersionBlowupLift HironakaSmoothSubmersionBlowupChoiceGeometry
  HironakaSmoothSubmersionOriginalTerminalFunctor

variable {n m : ℕ} {X D : CMfd.{u} n} {Y E : CMfd.{u} m}
  {b : Y → X} {g : E → D} {Q : BlowupTower Y E} {T : BlowupTower X D}

/-- True Cartesian pasting retains the literal original physical clock. -/
theorem actual_comp_deleted (H : IsActualTowerPullback b Q T g) :
    ∀ {ℓ : ℕ} {Z F : CMfd.{u} ℓ} {h : Z → Y} {e : F → E}
      {S : BlowupTower Z F} {L : List ℕ},
      IsDeletedSmoothHistory h S Q e L →
        IsDeletedSmoothHistory (b ∘ h) S T (g ∘ e) L := by
  induction H with
  | refl hb =>
    intro ℓ Z F h e S L HD
    cases HD with
    | refl hh => exact .refl (isSubmersion_composition hb hh)
  | @step E D F G Q T g H hg C π hπ ρ hρ ih =>
    intro ℓ Z F' h e S L HD
    have hg₁ := actualLift_isSubmersion hg hπ hρ
    have hc₁ := actualLift_proj_comm hg hπ hρ
    have hcart₁ := (IsActualTowerPullback.step (.refl hg) hg hπ hρ).universal
    cases HD with
    | @matched A'' A₀ B'' B₀ R Q₀ e₀ K HD C'' τ hτ C₀ ρ₀ hρ₀ e₁ he₁ hc₂ hC₂ hcart₂ hne =>
      rw [H.length_eq]
      refine .matched (ih HD) hτ hπ (actualLift hg hπ hρ ∘ e)
        (isSubmersion_composition hg₁ he₁)
        (fun z => (congrFun hc₁ (e z)).trans (congrArg g (hc₂ z))) hC₂ ?_ hne
      exact holomorphicSquarePullback_pasting ρ τ π
        HD.toTrace.isSubmersion.contMDiff he₁.contMDiff hc₂ hcart₁ hcart₂
    | @silent A'' A₀ B₀ R Q₀ e₀ K HD C₀ ρ₀ hρ₀ e₁ he₁ hc₂ hC₂ hcart₂ =>
      refine .silent (ih HD) hπ (actualLift hg hπ hρ ∘ e)
        (isSubmersion_composition hg₁ he₁)
        (fun z => (congrFun hc₁ (e z)).trans (congrArg g (hc₂ z))) hC₂ ?_
      exact holomorphicSquarePullback_pasting ρ id π
        HD.toTrace.isSubmersion.contMDiff he₁.contMDiff hc₂ hcart₁ hcart₂

variable {F : CMfd.{u} m} {e : F → E} {S : BlowupTower Y F} {L : List ℕ}

/-- In particular, delete the empty stages of precisely the existing actual Q. -/
theorem actual_comp_id_deleted (H : IsActualTowerPullback b Q T g)
    (HD : IsDeletedSmoothHistory (id : Y → Y) S Q e L) :
    IsDeletedSmoothHistory b S T (g ∘ e) L :=
  actual_comp_deleted H HD

theorem composite_old_boundary (H : IsActualTowerPullback b Q T g)
    (HD : IsDeletedSmoothHistory (id : Y → Y) S Q e L)
    (B : List (Set X)) (hB : ∀ A ∈ B, IsClosed A) :
    oldBoundaryAlong (B.map (b ⁻¹' ·)) S =
      (oldBoundaryAlong B T).map ((g ∘ e) ⁻¹' ·) :=
  (actual_comp_id_deleted H HD).old_boundary_dictionary B hB

theorem composite_born_boundary (H : IsActualTowerPullback b Q T g)
    (HD : IsDeletedSmoothHistory (id : Y → Y) S Q e L) :
    bornBoundaryAlong S = selectBirths ((bornBoundaryAlong T).map ((g ∘ e) ⁻¹' ·)) L :=
  (actual_comp_id_deleted H HD).born_boundary_dictionary

theorem composite_omitted_birth (H : IsActualTowerPullback b Q T g)
    (HD : IsDeletedSmoothHistory (id : Y → Y) S Q e L)
    (j : ℕ) (hj : j < T.length) (hjL : j ∉ L) :
    (g ∘ e) ⁻¹' (bornBoundaryAlong T).getD j ∅ = ∅ :=
  (actual_comp_id_deleted H HD).omitted_birth_empty j hj hjL

/-- An actual structural comparison with any genuine direct deletion, not an assigned source. -/
theorem direct_choice_comparison (H : IsActualTowerPullback b Q T g)
    (HD : IsDeletedSmoothHistory (id : Y → Y) S Q e L)
    {F' : CMfd.{u} m} {R : BlowupTower Y F'} {k : F' → D} {K : List ℕ}
    (HR : IsDeletedSmoothHistory b R T k K) :
    L = K ∧ ∃ φ : F ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ F',
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel m) Y ∞) S R φ ∧
        ∀ z, k (φ z) = g (e z) :=
  physical_choice_comparison (actual_comp_id_deleted H HD) HR

end
end Hironaka.HironakaG1ActualDeletedHistoryComposition
