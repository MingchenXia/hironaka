import Hironaka.Resolution.HironakaCompactOpenBlowupExtension
import Hironaka.Resolution.HironakaG3ClosedSupportedWindowExtension
import Hironaka.Invariant.RestrictEmptyTower
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaClosedFootprintOpenTowerExtension
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupRestrictOpen RestrictEmptyTower HironakaCompactOpenBlowupExtension
variable {n : ℕ} {X : CMfd.{u} n}
/-- A new local blowup whose footprint lies in a closed set inside the
window extends by one blowup on the SAME already extended prefix. -/
theorem exists_closed_footprint_step_extension
    (U : Opens X) (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    {A B Y : CMfd.{u} n}
    (T : BlowupTower (CMfd.of (n := n) U) A) (Q : BlowupTower X Y)
    (e : A ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ openPreimage Q U)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) U ∞) T (restrict U Q) e)
    {C : Set A} {π : B → A} (hπ : IsBlowupAlong n C π)
    (hOver : ∀ c ∈ C, (T.proj c).val ∈ K) :
    ∃ (Z : CMfd.{u} n) (D : Set Y) (q : Z → Y) (hq : IsBlowupAlong n D q),
      D ⊆ Q.proj ⁻¹' K ∧
      ∃ ξ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ openPreimage (.step Q D q hq) U,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) U ∞) (.step T C π hπ) (restrict U (.step Q D q hq)) ξ := by
  let V : Opens Y := openPreimage Q U
  let D : Set V := e.symm ⁻¹' C
  have hDclosed : IsClosed D := hπ.1.1.preimage e.symm.continuous
  have hDpre : e ⁻¹' D = C := by
    ext c
    simp only [D,mem_preimage,e.symm_apply_apply]
  have hMoved : IsBlowupAlong n D (e ∘ π) :=
    MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse e.symm.contMDiff e.contMDiff
      e.symm_apply_apply e.apply_symm_apply hπ
  have hBase (c : A) : Q.proj (e c).val = (T.proj c).val := by
    exact (proj_restrict U Q (e c)).symm.trans
      (congrArg Subtype.val (he.proj_comm c)).symm
  have hCover : (Subtype.val : V → Y) '' D ⊆ Q.proj ⁻¹' K := by
    rintro _ ⟨p,hp,rfl⟩
    have hb := hBase (e.symm p)
    rw [e.apply_symm_apply] at hb
    change Q.proj p.val ∈ K
    rw [hb]
    exact hOver _ hp
  have hFclosed : IsClosed (Q.proj ⁻¹' K) := hK.preimage Q.contMDiff_proj.continuous
  have hFV : Q.proj ⁻¹' K ⊆ V := fun y hy => hKU hy
  have hDsupport : D ⊆ (Subtype.val : V → Y) ⁻¹' (Q.proj ⁻¹' K) :=
    fun p hp => hCover ⟨p,hp,rfl⟩
  have hDimageClosed : IsClosed ((Subtype.val : V → Y) '' D) :=
    HironakaG3ClosedSupportedWindowExtension.isClosed_image_of_closed_support V (Q.proj ⁻¹' K)
      hFclosed hFV D hDclosed hDsupport
  obtain ⟨Z,q,hq,ξ,hξ⟩ := exists_extension_of_closed_image hMoved hDimageClosed
  refine ⟨Z,_,q,hq,hCover,ξ,?_⟩
  refine IsTowerIso.step
    (Z := CMfd.of (n := n) (openPreimage (.step Q ((Subtype.val : V → Y) '' D) q hq) U))
    he hπ (isBlowupAlong_restrict hq V (V.isOpen.preimage hq.contMDiff.continuous)) ξ ?_ ?_
  · intro p
    apply Subtype.ext
    exact hξ p
  · change e ⁻¹' ((Subtype.val : V → Y) ⁻¹' ((Subtype.val : V → Y) '' D)) = C
    rw [Subtype.val_injective.preimage_image]
    exact hDpre

theorem exists_closed_footprint_extension (U : Opens X) (K : Set X)
    (hK : IsClosed K) (hKU : K ⊆ U) {Z : CMfd.{u} n}
    (T : BlowupTower (CMfd.of (n := n) U) Z)
    (hT : CentresOver ((Subtype.val : U → X) ⁻¹' K) T) :
    ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y), CentresOver K Q ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) T (restrict U Q) e ∧
        T.length = Q.length ∧ ∀ z, Q.proj (e z).val = (T.proj z).val := by
  have hExtend : ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y), CentresOver K Q ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) T (restrict U Q) e := by
    induction T with
    | refl =>
      exact ⟨X, .refl, trivial, Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞, .refl⟩
    | @step A B T C π hπ ih =>
      obtain ⟨Y, Q, hQ, e, he⟩ := ih hT.1
      obtain ⟨Z,D,q,hq,hD,ξ,hξ⟩ := exists_closed_footprint_step_extension U K hK hKU
        T Q e he hπ (fun _ hc => hT.2 hc)
      exact ⟨Z,.step Q D q hq,⟨hQ,hD⟩,ξ,hξ⟩
  obtain ⟨Y, Q, hQ, e, he⟩ := hExtend
  refine ⟨Y, Q, hQ, e, he, he.length_eq.trans (length_restrict U Q), ?_⟩
  intro z
  exact (proj_restrict U Q (e z)).symm.trans
    (congrArg Subtype.val (he.proj_comm z)).symm

end
end Hironaka.HironakaClosedFootprintOpenTowerExtension
