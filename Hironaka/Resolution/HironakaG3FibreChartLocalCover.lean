import Hironaka.Resolution.HironakaG3SelectedChartLocalMap
import Hironaka.Resolution.HironakaG3EmptyChartTowerComparison
import Hironaka.Resolution.HironakaG3FiniteDisjointTowerMerge
import Hironaka.Resolution.HironakaG3TowerRestrictedQIdentification
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3FibreChartLocalCover
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsoTail
  RestrictEmptyTower HironakaG3RTowerClass HironakaG3FiniteDisjointTowerMerge
  HironakaG3SelectedChartLocalMap HironakaG3EmptyChartTowerComparison HironakaG3RigidOverLocalGlue
  MaxLocusLocal
open ResolutionInvariantExt (IsEmptyTower)

theorem fibre_chart_local_cover {n : ℕ} {Z Y B : CMfd.{0} n} {ι : Type u}
    (C : ι → Set Z) (W : ι → Opens Z) (hCW : ∀ i, C i ⊆ W i) (A : Opens Z)
    (s : Finset ι) {σ : Y → Z} (hσ : Continuous σ) (𝒞 : LocalTowerClass Z)
    (c : {j // j ∈ s} → TowerChart 𝒞 Y σ) (hc : ∀ i, (c i).U = W i.val ⊓ A)
    (c₀ : TowerChart 𝒞 Y σ) (hc₀ : (c₀.U : Set Z) = (A : Set Z) ∩ (⋃ i, C i)ᶜ)
    (hEmpty₀ : IsEmptyTower c₀.T) (M : BlowupTower (CMfd.of (n := n) A) B)
    (hM : CentresOver (finiteSupport (n := n) (X := CMfd.of (n := n) A) (fun i : {j // j ∈ s} => (Subtype.val : A → Z) ⁻¹' C i.val) s.attach) M)
    (hSupport : finiteSupport (n := n) (X := CMfd.of (n := n) A) (fun i : {j // j ∈ s} => (Subtype.val : A → Z) ⁻¹' C i.val) s.attach =
      (Subtype.val : A → Z) ⁻¹' (⋃ i, C i))
    (hCharts : ∀ i, ∃ e : (CMfd.of (n := n) (openPreimage M (nestedOpens A (W i.val)))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (c i).Y,
      ∀ z, (((c i).T.proj (e z) : (c i).U) : Z) = ((M.proj z.val : A) : Z)) :
    let QA := window σ hσ A
    let qA := restrictedBaseMap σ hσ A
    ∃ (V : Option {j // j ∈ s} → Opens A), (∀ x : A, ∃ j, x ∈ V j) ∧
      ∃ φ : ∀ j, (CMfd.of (n := n) (window M.proj M.contMDiff_proj.continuous (V j))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        (CMfd.of (n := n) (window (X := CMfd.of (n := n) A) (X₁ := CMfd.of (n := n) QA)
          qA (restrictedBaseMap_continuous σ hσ A) (V j))),
        ∀ j z, qA (φ j z).val = M.proj z.val := by
  classical
  dsimp only
  let V : Option {j // j ∈ s} → Opens A := fun j => j.elim (nestedOpens A c₀.U) (fun i => nestedOpens A (c i).U)
  have hc₀A : c₀.U ≤ A := by
    intro z hz
    have h : z ∈ (c₀.U : Set Z) := hz
    rw [hc₀] at h
    exact h.1
  have hciA (i : {j // j ∈ s}) : (c i).U ≤ A := by rw [hc i]; exact inf_le_right
  have hCover : ∀ x : A, ∃ j, x ∈ V j := by
    intro x
    by_cases hx : x ∈ finiteSupport (n := n) (X := CMfd.of (n := n) A) (fun i : {j // j ∈ s} => (Subtype.val : A → Z) ⁻¹' C i.val) s.attach
    · obtain ⟨i,_,hi⟩ := Set.mem_iUnion₂.mp hx
      refine ⟨some i,?_⟩
      change x.val ∈ (c i).U
      rw [hc i]
      exact ⟨hCW i.val hi,x.property⟩
    · refine ⟨none,?_⟩
      change x.val ∈ c₀.U
      change x.val ∈ (c₀.U : Set Z)
      rw [hc₀]
      refine ⟨x.property,?_⟩
      intro hUnion
      apply hx
      rw [hSupport]
      exact hUnion
  have hDis : Disjoint (nestedOpens A c₀.U : Set A)
      (finiteSupport (n := n) (X := CMfd.of (n := n) A) (fun i : {j // j ∈ s} => (Subtype.val : A → Z) ⁻¹' C i.val) s.attach) := by
    rw [hSupport]
    apply Set.disjoint_left.mpr
    intro x hxU hxS
    change x.val ∈ c₀.U at hxU
    change x.val ∈ (c₀.U : Set Z) at hxU
    rw [hc₀] at hxU
    exact hxU.2 hxS
  have hLocal : ∀ j, ∃ φ : (CMfd.of (n := n) (window M.proj M.contMDiff_proj.continuous (V j))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      (CMfd.of (n := n) (window (X := CMfd.of (n := n) A)
        (X₁ := CMfd.of (n := n) (window σ hσ A)) (restrictedBaseMap σ hσ A)
        (restrictedBaseMap_continuous σ hσ A) (V j))),
      ∀ z, (restrictedBaseMap σ hσ A) (φ z).val = M.proj z.val := by
    intro j
    cases j with
    | none =>
      obtain ⟨e,he⟩ := empty_chart_tower_comparison A 𝒞 c₀ hc₀A hEmpty₀ M _ hM hDis
      exact selected_chart_local_map A hσ 𝒞 c₀ hc₀A M e he
    | some i =>
      obtain ⟨e,he⟩ := hCharts i
      have hEq : nestedOpens A (c i).U = nestedOpens A (W i.val) := by
        rw [hc i]
        apply Opens.ext
        ext x
        change (x.val ∈ W i.val ∧ x.val ∈ A) ↔ x.val ∈ W i.val
        exact and_iff_left x.property
      let δ := opensCongr (n := n) (congrArg (openPreimage M) hEq)
      have he' : ∀ z, (((c i).T.proj (e (δ z)) : (c i).U) : Z) = ((M.proj z.val : A) : Z) := by
        intro z
        exact he (δ z)
      exact selected_chart_local_map A hσ 𝒞 (c i) (hciA i) M (δ.trans e) he'
  choose φ hφ using hLocal
  exact ⟨V,hCover,φ,hφ⟩
end
end Hironaka.HironakaG3FibreChartLocalCover
