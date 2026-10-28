import TranscendentalNakamaye.Pending.HironakaNormalCrossingsOpenRestrictionSeparation

/-!
# The actual projection biholomorphism of an empty tower

This is the accepted empty-projection induction from checkpoint
636442a87402a67de1f914cb4120ee28c3ed6ad7, isolated from the unrelated
canonical empty-head development. Every centre and step of the given tower
is retained. This import reduction makes no new mathematical closure claim.

Blueprint: hir:original-old-branch-empty-projection.
-/

set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

universe u

namespace TranscendentalNakamaye.Pending.HironakaOriginalOldBranchEmptyProjection

noncomputable section

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  BlowupTowers BlowupTowerTransforms
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X D : CMfd.{u} n}

/-- A real all-empty tower has its entire actual projection as a biholomorphism. -/
theorem exists_empty_tower_projection (T : BlowupTower X D) (he : IsEmptyTower T) :
    ∃ β : D ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,∀ z,β z=T.proj z := by
  induction T with
  | refl => exact ⟨Diffeomorph.refl _ _ ∞,fun _ => rfl⟩
  | step T C π hπ ih =>
    obtain ⟨heT,rfl⟩ := he
    obtain ⟨χ,hχ⟩ := ih heT
    obtain ⟨φ,hφ⟩ :=
      HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ
    exact ⟨φ.trans χ,fun z => by change χ (φ z)=T.proj (π z);rw [hχ,hφ]⟩

end
end TranscendentalNakamaye.Pending.HironakaOriginalOldBranchEmptyProjection

