/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3C)
-/
import DeJongAlterations.StableModification.Projectivity.RelativeQuasiFinite
import DeJongAlterations.StableModification.Projectivity.Reduction
import DeJongAlterations.Geometry.ChowLemmaProduct
import DeJongAlterations.Geometry.FiniteProjectivePreservation

/-!
# The finite-map criterion with several maps

Blueprint `sm-projectivity-relative.tex`, last step of `thm:sm-ltg` (PLAN-OM3 §3 step 4). Let
`Y` be projective over a ring `R` and `β : X ⟶ Y` proper. Suppose that for every closed point `y`
of `Y` there is an `R`-morphism `h : X ⟶ ℙᴺ_R` such that `(β, h) : X ⟶ Y ×_R ℙᴺ_R` is
quasi-finite at every point over a neighbourhood `O ∋ y`. Then `β` is projective relative to
`Y ⟶ Spec R` (`isRelativelyProjective_of_quasiFiniteAt`): finitely many `O`'s cover the closed
points; the product map `X ⟶ Y ×_R ℙ^{N₁} ×_R ⋯ ×_R ℙ^{Nₖ}` is quasi-finite over every closed point,
hence everywhere (its quasi-finite locus is open and `β` is closed), hence finite (Zariski's main
theorem), so `X` is projective over `R` (Codex's `Geometry.FiniteProjective.
isProjectiveOver_comp_of_isFinite`) and `β` is relatively projective (OM3A's
`isRelativelyProjective_of_isProjectiveOver`).

This replaces a single map `X ⟶ ℙᴺ` with finite fibres (OM3A's
`isRelativelyProjective_of_finite_fibres`): no common line bundle and no Segre embedding are
needed, and quasi-finiteness only has to be checked near one fibre at a time.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

open DeJong

/-- Quasi-finiteness of a composite at a point implies quasi-finiteness of the first map. -/
theorem quasiFiniteAt_of_comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {x : X}
    (h : (f ≫ g).QuasiFiniteAt x) : f.QuasiFiniteAt x := by
  simp only [Scheme.Hom.QuasiFiniteAt, Scheme.Hom.stalkMap_comp] at h
  exact RingHom.QuasiFinite.of_comp h

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- **The finite-map criterion with several maps** (blueprint `thm:sm-ltg`, last step). -/
theorem isRelativelyProjective_of_quasiFiniteAt (pY : Y ⟶ Spec (.of R)) (hY : IsProjectiveOver pY)
    (β : X ⟶ Y) [IsProper β] {N₀ : ℕ} (h₀ : X ⟶ projectiveSpace R N₀)
    (hh₀ : h₀ ≫ projectiveSpaceStructure R N₀ = β ≫ pY) {κ : Type*} (s : Finset κ) (N : κ → ℕ)
    (h : ∀ i, X ⟶ projectiveSpace R (N i))
    (hh : ∀ i, h i ≫ projectiveSpaceStructure R (N i) = β ≫ pY) (O : κ → Y.Opens)
    (hqf : ∀ i x, β x ∈ O i → (pullback.lift β (h i) (hh i).symm).QuasiFiniteAt x)
    (hO : ∀ y : Y, IsClosed ({y} : Set Y) → ∃ i ∈ s, y ∈ O i) :
    IsRelativelyProjective pY β := by
  classical
  have hP : ∀ t : Finset κ, ∃ (P : Scheme.{u}) (pP : P ⟶ Spec (.of R)) (_ : IsProjectiveOver pP)
      (g : X ⟶ P) (hg : g ≫ pP = β ≫ pY), ∀ i ∈ t, ∀ x, β x ∈ O i →
        (pullback.lift β g hg.symm).QuasiFiniteAt x := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      exact ⟨_, _, isProjectiveOver_projectiveSpaceStructure R N₀, h₀, hh₀, by simp⟩
    | insert i t hi ih =>
      obtain ⟨P, pP, hPp, g, hg, hqfg⟩ := ih
      have hgi : g ≫ pP = h i ≫ projectiveSpaceStructure R (N i) := by rw [hg, hh i]
      have hg' : pullback.lift g (h i) hgi ≫ pullback.fst pP (projectiveSpaceStructure R (N i)) ≫
          pP = β ≫ pY := by
        rw [pullback.lift_fst_assoc, hg]
      refine ⟨pullback pP (projectiveSpaceStructure R (N i)), pullback.fst _ _ ≫ pP,
        Geometry.ChowLemmaProduct.isProjectiveOver_product pP _ hPp
          (isProjectiveOver_projectiveSpaceStructure R (N i)),
        pullback.lift g (h i) hgi, hg', ?_⟩
      intro j hj x hx
      rcases Finset.mem_insert.mp hj with rfl | hj
      · let π : pullback pY (pullback.fst pP (projectiveSpaceStructure R (N j)) ≫ pP) ⟶
            pullback pY (projectiveSpaceStructure R (N j)) :=
          pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
            rw [pullback.condition (f := pY), pullback.condition (f := pP), Category.assoc])
        have hπ : pullback.lift β (pullback.lift g (h j) hgi) hg'.symm ≫ π =
            pullback.lift β (h j) (hh j).symm := by
          apply pullback.hom_ext
          · simp only [π, Category.assoc, pullback.lift_fst]
          · simp only [π, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
        apply quasiFiniteAt_of_comp (g := π)
        rw [hπ]
        exact hqf j x hx
      · let π : pullback pY (pullback.fst pP (projectiveSpaceStructure R (N i)) ≫ pP) ⟶
            pullback pY pP :=
          pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst _ _) (by
            rw [pullback.condition (f := pY), Category.assoc])
        have hπ : pullback.lift β (pullback.lift g (h i) hgi) hg'.symm ≫ π =
            pullback.lift β g hg.symm := by
          apply pullback.hom_ext
          · simp only [π, Category.assoc, pullback.lift_fst]
          · simp only [π, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
              pullback.lift_fst]
        apply quasiFiniteAt_of_comp (g := π)
        rw [hπ]
        exact hqfg j hj x hx
  obtain ⟨P, pP, hPp, g, hg, hqfg⟩ := hP s
  set Ψ := pullback.lift β g hg.symm with hΨ
  have hΨβ : Ψ ≫ pullback.fst pY pP = β := pullback.lift_fst _ _ _
  have : IsProper pY := hY.isProper
  have : IsProper pP := hPp.isProper
  have : CompactSpace Y := by
    have : CompactSpace (Spec (.of R)) := inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace pY
  have : IsProper (Ψ ≫ pullback.fst pY pP) := by rw [hΨβ]; infer_instance
  have : IsProper Ψ := IsProper.of_comp Ψ (pullback.fst pY pP)
  have : LocallyOfFiniteType Ψ := locallyOfFiniteType_of_comp Ψ (pullback.fst pY pP)
  have hall : ∀ x, Ψ.QuasiFiniteAt x := by
    by_contra hne
    push Not at hne
    obtain ⟨x₀, hx₀⟩ := hne
    have hC : IsClosed (β '' (Ψ.quasiFiniteLocus : Set X)ᶜ) :=
      β.isClosedMap _ Ψ.quasiFiniteLocus.isOpen.isClosed_compl
    obtain ⟨_, ⟨x, hx, rfl⟩, hcl⟩ := hC.exists_closed_singleton ⟨β x₀, x₀, hx₀, rfl⟩
    obtain ⟨i, hi, hxi⟩ := hO (β x) hcl
    exact hx (hqfg i hi x hxi)
  have : LocallyQuasiFinite Ψ :=
    (Scheme.Hom.quasiFiniteLocus_eq_top_iff Ψ).mp (top_unique fun x _ => hall x)
  have : IsFinite Ψ := IsFinite.of_isProper_of_locallyQuasiFinite Ψ
  have hPY := Geometry.ChowLemmaProduct.isProjectiveOver_product pY pP hY hPp
  have hX := Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite _ hPY Ψ
  rw [← Category.assoc, hΨβ] at hX
  exact isRelativelyProjective_of_isProjectiveOver pY β hX

end

end DeJongAlterations.StableModification.Projectivity
