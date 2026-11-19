import Hironaka.Resolution.HironakaG3EmptyAwareComposition
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareAlgebra
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Invariant.RestrictEmptyTower
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3AppendEmptyTailComparison
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail RestrictEmptyTower HironakaG3EmptyAwareHistory
open ResolutionInvariantExt (IsEmptyTower)

theorem emptyAware_append_empty_tail {n : ℕ} {X Y Z : CMfd.{u} n}
    (T : BlowupTower X Y) (S : BlowupTower Y Z) (hS : IsEmptyTower S) :
    ∃ ψ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) (T.append S) T ψ := by
  induction S with
  | refl => exact ⟨Diffeomorph.refl _ _ ∞,emptyAware_of_isTowerIso (IsTowerIso.refl_self T)⟩
  | @step A B S C π hπ ih =>
    obtain ⟨ψ,hψ⟩ := ih hS.1
    have hC : C = ∅ := hS.2
    subst C
    obtain ⟨φ, hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ
    exact ⟨φ.trans ψ, by
      simpa only [BlowupTower.append_step] using EmptyAwareTowerIso.leftEmpty hψ hπ φ hφ⟩

/-- A restriction with a wholly empty suffix retains the physical prefix. -/
theorem restricted_append_comparison_of_empty_tail {n : ℕ} {X Y Z : CMfd.{u} n}
    (T : BlowupTower X Y) (Q : BlowupTower Y Z) (U : Opens X)
    (he : IsEmptyTower (restrict (openPreimage T U) Q)) :
    ∃ ψ : (CMfd.of (n := n) (openPreimage (T.append Q) U)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage T U)),
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞)
        (restrict U (T.append Q)) (restrict U T) ψ := by
  obtain ⟨ψ,hψ⟩ := emptyAware_append_empty_tail (restrict U T) (restrict (openPreimage T U) Q) he
  have hIso := isTowerIso_restrict_append U T Q
  refine ⟨(opensCongr (openPreimage_append T Q U).symm).trans ψ, ?_⟩
  simpa only [Diffeomorph.refl_trans] using G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso hIso) hψ

theorem restricted_append_comparison_off_tail_support {n : ℕ} {X Y Z : CMfd.{u} n}
    (T : BlowupTower X Y) (Q : BlowupTower Y Z) (F : Set X)
    (hQ : CentresOver (T.proj ⁻¹' F) Q) (U : Opens X)
    (hUF : Disjoint (U : Set X) F) :
    ∃ ψ : (CMfd.of (n := n) (openPreimage (T.append Q) U)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage T U)),
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞)
        (restrict U (T.append Q)) (restrict U T) ψ := by
  have hDis : Disjoint (openPreimage T U : Set Y) (T.proj ⁻¹' F) := by
    apply Set.disjoint_left.mpr
    intro y hyU hyF
    exact Set.disjoint_left.mp hUF hyU hyF
  have he := isEmptyTower_restrict_of_centresOver (openPreimage T U) hDis Q hQ
  exact restricted_append_comparison_of_empty_tail T Q U he

end
end Hironaka.HironakaG3AppendEmptyTailComparison
