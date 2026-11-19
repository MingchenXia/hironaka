import Hironaka.Resolution.HironakaG3ActualOpenLiftComparison
import Hironaka.Analytic.SubmanifoldCodRestrict
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3AmbientContactEquiv
noncomputable section
open Hironaka.BlowupSequences BlowupTowers SubmanifoldChartedSpace SubmanifoldCodRestrict
  HironakaActualNativeSectionFiniteHistory HironakaDisjointNativeOpenLift
  HironakaDisjointNativeReferenceWindow HironakaG3ActualOpenLiftComparison
  HironakaG3RTowerClass MaxLocusLocal BlowupTowerTransforms HironakaOriginalTerminalOverlapComparison

/-- A biholomorphism carrying one actual smooth contact onto another induces
the literal biholomorphism of their native manifolds. -/
def inducedContactEquiv {d t : ℕ} {X₁ X₂ : CMfd.{0} (d+t)}
    (N₁ : Set X₁) (N₂ : Set X₂)
    (hN₁ : ∀ x ∈ N₁, RegularAtDim (n := d+t) N₁ x d)
    (hN₂ : ∀ x ∈ N₂, RegularAtDim (n := d+t) N₂ x d)
    (Ξ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ X₂)
    (hN : Ξ ⁻¹' N₂ = N₁) :
    nativeManifold (Nat.le_add_right d t) N₁ hN₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
      nativeManifold (Nat.le_add_right d t) N₂ hN₂ := by
  let := chartedSpace (Nat.le_add_right d t) hN₁
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN₁
  let := chartedSpace (Nat.le_add_right d t) hN₂
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN₂
  have hf : ∀ x : N₁, Ξ x.val ∈ N₂ := by
    intro x
    change x.val ∈ Ξ ⁻¹' N₂
    rw [hN]
    exact x.property
  have hg : ∀ x : N₂, Ξ.symm x.val ∈ N₁ := by
    intro x
    rw [← hN]
    change Ξ (Ξ.symm x.val) ∈ N₂
    rw [Ξ.apply_symm_apply]
    exact x.property
  refine ⟨⟨(fun x => ⟨Ξ x.val,hf x⟩), (fun x => ⟨Ξ.symm x.val,hg x⟩),
    (fun x => Subtype.ext (Ξ.symm_apply_apply x.val)),
    (fun x => Subtype.ext (Ξ.apply_symm_apply x.val))⟩,?_,?_⟩
  · exact contMDiff_codRestrict (Nat.le_add_right d t) hN₂
      (Ξ.contMDiff.comp (contMDiff_val (Nat.le_add_right d t) hN₁)) hf
  · exact contMDiff_codRestrict (Nat.le_add_right d t) hN₁
      (Ξ.symm.contMDiff.comp (contMDiff_val (Nat.le_add_right d t) hN₂)) hg

@[simp] theorem inducedContactEquiv_val {d t : ℕ} {X₁ X₂ : CMfd.{0} (d+t)}
    (N₁ : Set X₁) (N₂ : Set X₂)
    (hN₁ : ∀ x ∈ N₁, RegularAtDim (n := d+t) N₁ x d)
    (hN₂ : ∀ x ∈ N₂, RegularAtDim (n := d+t) N₂ x d)
    (Ξ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ X₂)
    (hN : Ξ ⁻¹' N₂ = N₁) (p : nativeManifold (Nat.le_add_right d t) N₁ hN₁) :
    (inducedContactEquiv N₁ N₂ hN₁ hN₂ Ξ hN p).val = Ξ p.val := rfl

/-- The induced native map on the actual contact windows of two ambient
opens, derived from the ambient base biholomorphism. -/
def inducedWindowEquiv {d t : ℕ} {X₁ X₂ : CMfd.{0} (d+t)}
    (N₁ : Set X₁) (N₂ : Set X₂) (hNc₁ : IsClosed N₁) (hNc₂ : IsClosed N₂)
    (hN₁ : ∀ x ∈ N₁, RegularAtDim (n := d+t) N₁ x d)
    (hN₂ : ∀ x ∈ N₂, RegularAtDim (n := d+t) N₂ x d)
    (O₁ : Opens X₁) (O₂ : Opens X₂)
    (Ξ : CMfd.of (n := d+t) O₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ CMfd.of (n := d+t) O₂)
    (hN : Ξ ⁻¹' openSection N₂ O₂ = openSection N₁ O₁) :
    CMfd.of (n := d) (contactWindow N₁ hN₁ O₁) ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
      CMfd.of (n := d) (contactWindow N₂ hN₂ O₂) :=
  (windowEquiv (Nat.le_add_right d t) N₁ hN₁ hNc₁ O₁).symm.trans
    ((inducedContactEquiv (openSection N₁ O₁) (openSection N₂ O₂)
      (openSection_regular hN₁ O₁) (openSection_regular hN₂ O₂) Ξ hN).trans
      (windowEquiv (Nat.le_add_right d t) N₂ hN₂ hNc₂ O₂))

@[simp] theorem inducedWindowEquiv_val {d t : ℕ} {X₁ X₂ : CMfd.{0} (d+t)}
    (N₁ : Set X₁) (N₂ : Set X₂) (hNc₁ : IsClosed N₁) (hNc₂ : IsClosed N₂)
    (hN₁ : ∀ x ∈ N₁, RegularAtDim (n := d+t) N₁ x d)
    (hN₂ : ∀ x ∈ N₂, RegularAtDim (n := d+t) N₂ x d)
    (O₁ : Opens X₁) (O₂ : Opens X₂)
    (Ξ : CMfd.of (n := d+t) O₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ CMfd.of (n := d+t) O₂)
    (hN : Ξ ⁻¹' openSection N₂ O₂ = openSection N₁ O₁)
    (p : contactWindow N₁ hN₁ O₁) :
    (inducedWindowEquiv N₁ N₂ hNc₁ hNc₂ hN₁ hN₂ O₁ O₂ Ξ hN p).val.val =
      (Ξ ⟨p.val.val,p.property⟩).val := rfl

/-- The native map on the two actual restrictions to an ambient overlap;
the ambient identification carries the two literal contact sets. -/
def overlapContactEquiv {d t : ℕ} {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (U₁ U₂ : Opens X) :
    CMfd.of (n := d) (contactWindow (openSection N U₁) (openSection_regular hN U₁)
      (nestedOpens U₁ (U₁ ⊓ U₂))) ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
    CMfd.of (n := d) (contactWindow (openSection N U₂) (openSection_regular hN U₂)
      (nestedOpens U₂ (U₁ ⊓ U₂))) :=
  inducedWindowEquiv (openSection N U₁) (openSection N U₂)
    (hNc.preimage continuous_subtype_val) (hNc.preimage continuous_subtype_val)
    (openSection_regular hN U₁) (openSection_regular hN U₂)
    (nestedOpens U₁ (U₁ ⊓ U₂)) (nestedOpens U₂ (U₁ ⊓ U₂))
    (overlapBaseEquiv (n := d+t) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right) (by
      ext p
      rfl)

@[simp] theorem overlapContactEquiv_point {d t : ℕ} {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (U₁ U₂ : Opens X)
    (p : contactWindow (openSection N U₁) (openSection_regular hN U₁) (nestedOpens U₁ (U₁ ⊓ U₂))) :
    (((overlapContactEquiv N hNc hN U₁ U₂ p).val.val : U₂) : X) = ((p.val.val : U₁) : X) := rfl

end
end Hironaka.HironakaG3AmbientContactEquiv
