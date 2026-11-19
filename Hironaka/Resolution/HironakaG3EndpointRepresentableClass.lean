import Hironaka.Resolution.HironakaG3TowerRestrictedQIdentification
import Hironaka.Resolution.HironakaG3RGluedBoundary
import Hironaka.Blowup.BlowupTowerIsoTail
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3RestrictedEndpointWindow
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsoTail
  MarkedIdealTowerTransport HironakaG3RGluedBoundary HironakaG3RigidOverLocalGlue MaxLocusLocal

theorem restricted_endpoint_window {n : ℕ} {X Y B : CMfd.{u} n}
    (Q : Y → X) (hQ : Continuous Q) (A A' : Opens X) (hA : A' ≤ A)
    (M : BlowupTower (CMfd.of (n := n) A) B)
    (Φ : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (window Q hQ A))
    (hΦ : ∀ z, restrictedBaseMap Q hQ A (Φ z) = M.proj z) :
    ∃ e : (CMfd.of (n := n) (openPreimage M (nestedOpens A A'))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (window Q hQ A'),
      ∀ z, Q (e z).val = ((M.proj z.val : A) : X) := by
  let V : Opens A := nestedOpens A A'
  let R : Opens (window Q hQ A) := window (X := CMfd.of (n := n) A) (X₁ := CMfd.of (n := n) (window Q hQ A)) (restrictedBaseMap Q hQ A) (restrictedBaseMap_continuous Q hQ A) V
  have hEq : preimageOpens Φ R = openPreimage M V := by
    apply Opens.ext
    ext z
    change restrictedBaseMap Q hQ A (Φ z) ∈ V ↔ M.proj z ∈ V
    rw [hΦ]
  let e := (opensCongr (n := n) hEq.symm).trans (preimageDiffeo Φ R).symm
  have hNested : ∀ y : window Q hQ A, y ∈ R ↔ y.val ∈ window Q hQ A' := by
    intro y
    rfl
  have hSub : window Q hQ A' ≤ window Q hQ A := fun y hy => hA hy
  let η := nestedDiffeo (n := n) (window Q hQ A) R (window Q hQ A') hNested hSub
  refine ⟨e.trans η,?_⟩
  intro z
  exact congrArg Subtype.val (hΦ z.val)
end
end Hironaka.G3RestrictedEndpointWindow

namespace Hironaka.G3EndpointRepresentableClass
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsoTail
  HironakaG3RTowerClass HironakaG3RGluedBoundary HironakaG3RigidOverLocalGlue
  MaxLocusLocal G3RestrictedEndpointWindow

def endpointRepresentable {n : ℕ} {X Y : CMfd.{u} n} (P : Y → X) (hP : Continuous P) : LocalTowerClass X :=
  fun U B T => ∃ Φ : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (window P hP U),
    ∀ z, restrictedBaseMap P hP U (Φ z) = T.proj z

theorem endpointRepresentable_hasComparisons {n : ℕ} {X Y : CMfd.{u} n} (P : Y → X) (hP : Continuous P) :
    HasComparisons (endpointRepresentable P hP) := by
  intro U₁ U₂ B₁ B₂ T₁ T₂ h₁ h₂
  obtain ⟨Φ₁,hΦ₁⟩ := h₁
  obtain ⟨Φ₂,hΦ₂⟩ := h₂
  obtain ⟨e₁,he₁⟩ := restricted_endpoint_window P hP U₁ (U₁ ⊓ U₂) inf_le_left T₁ Φ₁ hΦ₁
  obtain ⟨e₂,he₂⟩ := restricted_endpoint_window P hP U₂ (U₁ ⊓ U₂) inf_le_right T₂ Φ₂ hΦ₂
  refine ⟨e₁.trans e₂.symm,?_⟩
  intro z
  have h := he₂ (e₂.symm (e₁ z))
  rw [e₂.apply_symm_apply] at h
  exact h.symm.trans (he₁ z)

theorem endpointRepresentable_of_chart {n : ℕ} {X Y : CMfd.{u} n} {P : Y → X}
    (hP : Continuous P) {𝒞 : LocalTowerClass X} (c : TowerChart 𝒞 Y P) :
    endpointRepresentable P hP c.U c.Y c.T := by
  have hV : c.V = window P hP c.U := Opens.ext c.V_eq
  let Φ := c.φ.trans (opensCongr (n := n) hV)
  refine ⟨Φ,?_⟩
  intro z
  apply Subtype.ext
  exact c.proj_φ z

theorem endpointRepresentable_covers_of_charts {n : ℕ} {X Y : CMfd.{u} n} {P : Y → X}
    (hP : Continuous P) (𝒞 : LocalTowerClass X)
    (hCharts : ∀ x, ∃ c : TowerChart 𝒞 Y P, x ∈ c.U) :
    Covers (endpointRepresentable P hP) := by
  intro x
  obtain ⟨c,hx⟩ := hCharts x
  exact ⟨c.U,hx,c.Y,c.T,endpointRepresentable_of_chart hP c⟩
end
end Hironaka.G3EndpointRepresentableClass
