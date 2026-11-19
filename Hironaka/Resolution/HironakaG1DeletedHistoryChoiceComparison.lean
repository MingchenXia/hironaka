import Hironaka.Resolution.HironakaG1PhysicalHistoryCoherence

/-! Choice independence of deleted ordinary smooth pullback histories.
Actual physical tower isomorphisms are derived by induction; endpoint
Cartesian comparison alone is never called a tower comparison.
Blueprint first: `hironaka-g1-deleted-history-choice-comparison.tex`. -/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG1DeletedHistoryChoiceComparison
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  BlowupTowerSplit HironakaG1DeletedSmoothHistory HironakaG1PhysicalHistoryCoherence
  HironakaSmoothSubmersionOrderedCompressedImagePullback

variable {n m : ℕ} {X D : CMfd.{u} n} {Y D₁ D₂ : CMfd.{u} m}
  {f : Y → X} {T : BlowupTower X D} {Q₁ : BlowupTower Y D₁} {Q₂ : BlowupTower Y D₂}
  {g₁ : D₁ → D} {g₂ : D₂ → D} {L₁ L₂ : List ℕ}

/-- Genuine Cartesian traces give unique endpoint comparisons. The later
physical induction supplies the separate tower-isomorphism assertion. -/
theorem existsUnique_trace_comparison
    (H₁ : IsSmoothTowerTrace f Q₁ T g₁) (H₂ : IsSmoothTowerTrace f Q₂ T g₂) :
    ∃! a : D₁ ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ D₂,
      (∀ x, Q₂.proj (a x) = Q₁.proj x) ∧ (∀ x, g₂ (a x) = g₁ x) := by
  obtain ⟨a,ha,huniq⟩ := H₂.universal m D₁ Q₁.proj g₁ Q₁.contMDiff_proj
    H₁.isSubmersion.contMDiff (fun x => (H₁.proj_comm x).symm)
  obtain ⟨b,hb,_⟩ := H₁.universal m D₂ Q₂.proj g₂ Q₂.contMDiff_proj
    H₂.isSubmersion.contMDiff (fun x => (H₂.proj_comm x).symm)
  have hba : b ∘ a = id :=
    (H₁.universal m D₁ Q₁.proj g₁ Q₁.contMDiff_proj H₁.isSubmersion.contMDiff
      (fun x => (H₁.proj_comm x).symm)).unique
      ⟨hb.1.comp ha.1,fun x => (hb.2.1 (a x)).trans (ha.2.1 x),
        fun x => (hb.2.2 (a x)).trans (ha.2.2 x)⟩
      ⟨contMDiff_id,fun _ => rfl,fun _ => rfl⟩
  have hab : a ∘ b = id :=
    (H₂.universal m D₂ Q₂.proj g₂ Q₂.contMDiff_proj H₂.isSubmersion.contMDiff
      (fun x => (H₂.proj_comm x).symm)).unique
      ⟨ha.1.comp hb.1,fun x => (ha.2.1 (b x)).trans (hb.2.1 x),
        fun x => (ha.2.2 (b x)).trans (hb.2.2 x)⟩
      ⟨contMDiff_id,fun _ => rfl,fun _ => rfl⟩
  let φ : D₁ ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ D₂ :=
    { toEquiv := ⟨a,b,fun x => congrFun hba x,fun x => congrFun hab x⟩
      contMDiff_toFun := ha.1
      contMDiff_invFun := hb.1 }
  refine ⟨φ,ha.2,?_⟩
  intro ψ hψ
  exact Diffeomorph.ext fun x => congrFun (huniq ψ ⟨ψ.contMDiff,hψ⟩) x

private theorem trace_lifts_eq (H : IsSmoothTowerTrace f Q₂ T g₂)
    {P : CMfd.{u} m} {a b : P → D₂}
    (ha : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ a)
    (hb : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ b)
    (hp : ∀ x, Q₂.proj (a x) = Q₂.proj (b x))
    (hg : ∀ x, g₂ (a x) = g₂ (b x)) : a = b := by
  exact (H.universal m P (Q₂.proj ∘ a) (g₂ ∘ a) (Q₂.contMDiff_proj.comp ha)
    (H.isSubmersion.contMDiff.comp ha) (fun x => (H.proj_comm (a x)).symm)).unique
      ⟨ha,fun _ => rfl,fun _ => rfl⟩
      ⟨hb,fun x => (hp x).symm,fun x => (hg x).symm⟩

private theorem centres_correspond {A₁ A₂ : CMfd.{u} m} {A : CMfd.{u} n}
    (χ : A₁ ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ A₂)
    {g₁ : A₁ → A} {g₂ : A₂ → A} (hg : ∀ x, g₂ (χ x) = g₁ x)
    {C : Set A} {C₁ : Set A₁} {C₂ : Set A₂}
    (hC₁ : g₁ ⁻¹' C = C₁) (hC₂ : g₂ ⁻¹' C = C₂) : χ ⁻¹' C₂ = C₁ := by
  rw [← hC₁,← hC₂]
  ext x
  exact Iff.of_eq (congrArg (fun a => a ∈ C) (hg x))

/-- Identical deletion indices and an actual physical tower isomorphism are
derived together. Cartesian endpoint uniqueness alone is insufficient. -/
theorem physical_choice_comparison
    (H₁ : IsDeletedSmoothHistory f Q₁ T g₁ L₁) :
    ∀ {D₂ : CMfd.{u} m} {Q₂ : BlowupTower Y D₂} {g₂ : D₂ → D} {L₂ : List ℕ},
      IsDeletedSmoothHistory f Q₂ T g₂ L₂ →
      L₁ = L₂ ∧ ∃ a : D₁ ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ D₂,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel m) Y ∞) Q₁ Q₂ a ∧
          ∀ x, g₂ (a x) = g₁ x := by
  induction H₁ with
  | refl hf =>
    intro D₂ Q₂ g₂ L₂ H₂
    cases H₂ with
    | refl => exact ⟨rfl,_,IsTowerIso.refl,fun _ => rfl⟩
  | @matched A₁ A B₁ B Q T g L H₁ C₁ ρ hρ C π hπ g₁ hg hc hC hcart hne ih =>
    have P₁ := IsDeletedSmoothHistory.matched H₁ hρ hπ g₁ hg hc hC hcart hne
    intro D₂ Q₂ g₂ L₂ H₂
    have P₂ := H₂
    cases H₂ with
    | @matched A₂ A₀ B₂ B₀ R S k K H₂ C₂ τ hτ C₀ π₀ hπ₀ k₁ hk₁ hc₂ hC₂ hcart₂ hne₂ =>
      obtain ⟨he,χ,hi,hprev⟩ := ih H₂
      obtain ⟨a,ha,_⟩ := existsUnique_trace_comparison P₁.toTrace P₂.toTrace
      have hsquare : τ ∘ a = χ ∘ ρ := by
        apply trace_lifts_eq H₂.toTrace (hτ.contMDiff.comp a.contMDiff)
          (χ.contMDiff.comp hρ.contMDiff)
        · intro x
          exact (ha.1 x).trans (hi.proj_comm (ρ x))
        · intro x
          exact (hc₂ (a x)).symm.trans ((congrArg π (ha.2 x)).trans
            ((hc x).trans (hprev (ρ x)).symm))
      exact ⟨congrArg (fun K => K ++ [T.length]) he,a,
        IsTowerIso.step hi hρ hτ a (fun x => congrFun hsquare x)
          (centres_correspond χ hprev hC hC₂),ha.2⟩
    | @silent A₂ A₀ B₀ R S k K H₂ C₀ π₀ hπ₀ k₁ hk₁ hc₂ hC₂ hcart₂ =>
      obtain ⟨he,χ,hi,hprev⟩ := ih H₂
      have hempty : C₁ = ∅ := by
        simpa only [preimage_empty] using (centres_correspond χ hprev hC hC₂).symm
      obtain ⟨x,hx⟩ := hne
      rw [hempty] at hx
      exact False.elim hx
  | @silent A₁ A B Q T g L H₁ C π hπ g₁ hg hc hC hcart ih =>
    have P₁ := IsDeletedSmoothHistory.silent H₁ hπ g₁ hg hc hC hcart
    intro D₂ Q₂ g₂ L₂ H₂
    have P₂ := H₂
    cases H₂ with
    | @matched A₂ A₀ B₂ B₀ R S k K H₂ C₂ τ hτ C₀ π₀ hπ₀ k₁ hk₁ hc₂ hC₂ hcart₂ hne₂ =>
      obtain ⟨he,χ,hi,hprev⟩ := ih H₂
      obtain ⟨x,hx⟩ := hne₂
      have hy : χ.symm x ∈ χ ⁻¹' C₂ := by simpa only [mem_preimage,χ.apply_symm_apply] using hx
      rw [centres_correspond χ hprev hC hC₂] at hy
      exact False.elim hy
    | @silent A₂ A₀ B₀ R S k K H₂ C₀ π₀ hπ₀ k₁ hk₁ hc₂ hC₂ hcart₂ =>
      obtain ⟨he,χ,hi,hprev⟩ := ih H₂
      obtain ⟨a,ha,_⟩ := existsUnique_trace_comparison P₁.toTrace P₂.toTrace
      have hamap : (a : _ → _) = χ := by
        apply trace_lifts_eq H₂.toTrace a.contMDiff χ.contMDiff
        · intro x
          exact (ha.1 x).trans (hi.proj_comm x)
        · intro x
          exact (hc₂ (a x)).symm.trans ((congrArg π (ha.2 x)).trans
            ((hc x).trans (hprev x).symm))
      have hae : a = χ := Diffeomorph.ext fun x => congrFun hamap x
      exact ⟨he,a,hae.symm ▸ hi,ha.2⟩

/-- Every target prefix has actual source prefixes with the identical retained
original physical sublist and an actual physical comparison. -/
theorem physical_choice_prefixes (H₁ : IsDeletedSmoothHistory f Q₁ T g₁ L₁)
    (H₂ : IsDeletedSmoothHistory f Q₂ T g₂ L₂) (j : ℕ) :
    ∃ (i₁ i₂ : ℕ) (k₁ : (split Q₁ i₁).1 → (split T j).1)
      (k₂ : (split Q₂ i₂).1 → (split T j).1),
      IsDeletedSmoothHistory f (head Q₁ i₁) (head T j) k₁
        (L₁.filter (fun a => decide (a < T.length-j))) ∧
      IsDeletedSmoothHistory f (head Q₂ i₂) (head T j) k₂
        (L₁.filter (fun a => decide (a < T.length-j))) ∧
      ∃ a : (split Q₁ i₁).1 ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ (split Q₂ i₂).1,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel m) Y ∞)
          (head Q₁ i₁) (head Q₂ i₂) a ∧ ∀ x, k₂ (a x) = k₁ x := by
  classical
  have he := (physical_choice_comparison H₁ H₂).1
  obtain ⟨i₁,k₁,HP₁⟩ := H₁.prefix j
  obtain ⟨i₂,k₂,HP₂⟩ := H₂.prefix j
  rw [← he] at HP₂
  exact ⟨i₁,i₂,k₁,k₂,HP₁,HP₂,(physical_choice_comparison HP₁ HP₂).2⟩

/-- The unique actual comparison, independent of primitive blowup choices. -/
def comparison (H₁ : IsDeletedSmoothHistory f Q₁ T g₁ L₁)
    (H₂ : IsDeletedSmoothHistory f Q₂ T g₂ L₂) :
    D₁ ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ D₂ :=
  Classical.choose (existsUnique_trace_comparison H₁.toTrace H₂.toTrace)

theorem comparison_spec (H₁ : IsDeletedSmoothHistory f Q₁ T g₁ L₁)
    (H₂ : IsDeletedSmoothHistory f Q₂ T g₂ L₂) :
    (∀ x, Q₂.proj (comparison H₁ H₂ x) = Q₁.proj x) ∧
      (∀ x, g₂ (comparison H₁ H₂ x) = g₁ x) :=
  (Classical.choose_spec (existsUnique_trace_comparison H₁.toTrace H₂.toTrace)).1

theorem comparison_isTowerIso (H₁ : IsDeletedSmoothHistory f Q₁ T g₁ L₁)
    (H₂ : IsDeletedSmoothHistory f Q₂ T g₂ L₂) :
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel m) Y ∞) Q₁ Q₂ (comparison H₁ H₂) := by
  obtain ⟨he,a,hi,ha⟩ := physical_choice_comparison H₁ H₂
  have heq : a = comparison H₁ H₂ :=
    (Classical.choose_spec (existsUnique_trace_comparison H₁.toTrace H₂.toTrace)).2 a
      ⟨fun x => (hi.proj_comm x).symm,ha⟩
  exact heq ▸ hi

theorem comparison_identity (H : IsDeletedSmoothHistory f Q₁ T g₁ L₁) :
    comparison H H = Diffeomorph.refl 𝓘(ℂ,ComplexModel m) D₁ ∞ := by
  exact ((Classical.choose_spec (existsUnique_trace_comparison H.toTrace H.toTrace)).2 _
    ⟨fun _ => rfl,fun _ => rfl⟩).symm

theorem comparison_cocycle {D₃ : CMfd.{u} m} {Q₃ : BlowupTower Y D₃}
    {g₃ : D₃ → D} {L₃ : List ℕ} (H₁ : IsDeletedSmoothHistory f Q₁ T g₁ L₁)
    (H₂ : IsDeletedSmoothHistory f Q₂ T g₂ L₂) (H₃ : IsDeletedSmoothHistory f Q₃ T g₃ L₃) :
    (comparison H₁ H₂).trans (comparison H₂ H₃) = comparison H₁ H₃ := by
  apply (Classical.choose_spec (existsUnique_trace_comparison H₁.toTrace H₃.toTrace)).2
  exact ⟨fun x => ((comparison_spec H₂ H₃).1 _).trans ((comparison_spec H₁ H₂).1 x),
    fun x => ((comparison_spec H₂ H₃).2 _).trans ((comparison_spec H₁ H₂).2 x)⟩

private theorem read_map_preimage {A B : Type*} (p : B → A) (E : List (Set A)) (i : ℕ) :
    (E.map (fun H => p ⁻¹' H)).getD i ∅ = p ⁻¹' (E.getD i ∅) := by
  simp only [List.getD,List.getElem?_map]
  cases E[i]? <;> simp

/-- Complete old and born histories are literal under the actual choice map. -/
theorem comparison_boundary_dictionaries (H₁ : IsDeletedSmoothHistory f Q₁ T g₁ L₁)
    (H₂ : IsDeletedSmoothHistory f Q₂ T g₂ L₂) (E : List (Set X))
    (hE : ∀ A ∈ E, IsClosed A) :
    oldBoundaryAlong (E.map (fun A => f ⁻¹' A)) Q₁ =
        (oldBoundaryAlong (E.map (fun A => f ⁻¹' A)) Q₂).map
          (fun A => comparison H₁ H₂ ⁻¹' A) ∧
      bornBoundaryAlong Q₁ = (bornBoundaryAlong Q₂).map
        (fun A => comparison H₁ H₂ ⁻¹' A) := by
  have he := (physical_choice_comparison H₁ H₂).1
  subst L₂
  have hg := (comparison_spec H₁ H₂).2
  constructor
  · rw [H₁.old_boundary_dictionary E hE,H₂.old_boundary_dictionary E hE,List.map_map]
    apply List.map_congr_left
    intro A hA
    ext x
    exact Iff.of_eq (congrArg (fun a => a ∈ A) (hg x).symm)
  · rw [H₁.born_boundary_dictionary,H₂.born_boundary_dictionary]
    simp only [selectBirths,List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply,read_map_preimage]
    ext x
    exact Iff.of_eq (congrArg (fun a => a ∈ (bornBoundaryAlong T).getD i ∅) (hg x).symm)

/-- The independently constructed direct history agrees physically with the
actual iterated history and with its substituted original indices. -/
theorem direct_iterated_comparison
    {ℓ : ℕ} {Z D₃ D₄ : CMfd.{u} ℓ} {h : Z → Y} {k : D₃ → D₁}
    {R : BlowupTower Z D₃} {S : BlowupTower Z D₄} {s : D₄ → D} {K J : List ℕ}
    (H₁ : IsDeletedSmoothHistory f Q₁ T g₁ L₁)
    (H₂ : IsDeletedSmoothHistory h R Q₁ k K)
    (Hdirect : IsDeletedSmoothHistory (f ∘ h) S T s J) :
    let Hcomp := HironakaG1PhysicalHistoryCoherence.IsDeletedSmoothHistory.comp H₁ H₂
    J = composeRetained L₁ K ∧
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel ℓ) Z ∞) R S (comparison Hcomp Hdirect) ∧
      ∀ x, s (comparison Hcomp Hdirect x) = (g₁ ∘ k) x := by
  dsimp only
  exact ⟨(physical_choice_comparison
      (HironakaG1PhysicalHistoryCoherence.IsDeletedSmoothHistory.comp H₁ H₂) Hdirect).1.symm,
    comparison_isTowerIso _ _,(comparison_spec _ _).2⟩

end
end Hironaka.HironakaG1DeletedHistoryChoiceComparison
