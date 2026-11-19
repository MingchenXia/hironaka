import Hironaka.Resolution.HironakaG3RTowerClass
import Hironaka.Invariant.MaxLocusLocal
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SelectedChartLocalMap
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms HironakaG3RTowerClass MaxLocusLocal

theorem selected_chart_local_map {n : ℕ} {Z Y B : CMfd.{0} n}
    (A : Opens Z) {σ : Y → Z} (hσ : Continuous σ) (𝒞 : LocalTowerClass Z)
    (c : TowerChart 𝒞 Y σ) (hcA : c.U ≤ A)
    (M : BlowupTower (CMfd.of (n := n) A) B)
    (e : (CMfd.of (n := n) (openPreimage M (nestedOpens A c.U))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ c.Y)
    (he : ∀ z, ((c.T.proj (e z) : c.U) : Z) = ((M.proj z.val : A) : Z)) :
    let QA : Opens Y := ⟨σ ⁻¹' (A : Set Z),A.isOpen.preimage hσ⟩
    let qA : QA → A := fun y => ⟨σ y.val,y.property⟩
    let V : Opens A := nestedOpens A c.U
    let VQ : Opens QA := ⟨qA ⁻¹' (V : Set A),V.isOpen.preimage (Continuous.subtype_mk (hσ.comp continuous_subtype_val) _)⟩
    ∃ φ : (CMfd.of (n := n) (openPreimage M V)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) VQ),
      ∀ z, qA (φ z).val = M.proj z.val := by
  dsimp only
  let QA : Opens Y := ⟨σ ⁻¹' (A : Set Z),A.isOpen.preimage hσ⟩
  let qA : QA → A := fun y => ⟨σ y.val,y.property⟩
  let V : Opens A := nestedOpens A c.U
  let VQ : Opens QA := ⟨qA ⁻¹' (V : Set A),V.isOpen.preimage (Continuous.subtype_mk (hσ.comp continuous_subtype_val) _)⟩
  have hcV (y : Y) : y ∈ c.V ↔ σ y ∈ c.U := by
    change y ∈ (c.V : Set Y) ↔ σ y ∈ c.U
    rw [c.V_eq]
    rfl
  have hBD : ∀ q : QA, q ∈ VQ ↔ (q : Y) ∈ c.V := by
    intro q
    change σ q.val ∈ c.U ↔ q.val ∈ c.V
    exact (hcV q.val).symm
  have hDA : c.V ≤ QA := by
    intro y hy
    exact hcA ((hcV y).mp hy)
  let δ := nestedDiffeo (n := n) QA VQ c.V hBD hDA
  refine ⟨e.trans (c.φ.trans δ.symm),?_⟩
  intro z
  apply Subtype.ext
  change σ (c.φ (e z)).val = ((M.proj z.val : A) : Z)
  rw [c.proj_φ]
  exact he z
end
end Hironaka.HironakaG3SelectedChartLocalMap
