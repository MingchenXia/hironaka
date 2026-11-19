/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
import Hironaka.Scheme.BlowUp.Composite.Iso
import Hironaka.Scheme.BlowUp.Glue.Trivial
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
/-!
# A finite succession of monoidal transformations is one blow-up

A morphism obtained by a finite succession of monoidal transformations "can be also obtained by a
single monoidal transformation with suitably chosen center" (the remark following Main Theorem I
in [Hir64, pp. 132–133]; the induction step is Hironaka's `J(m)` device, the composition of two
blow-ups as one blow-up, [Sta, Tag 080B]): for `X` Noetherian and `S : BlowUpSequence X`, there is
an ideal sheaf `K` on `X` whose support is the union of the images of the centers under the
partial composites and a canonical isomorphism `S.last ≅ K.blowUp` over `X`.

The empty sequence gives `K = ⊤` (the trivial blow-up, `blowUp.isIso_π_of_isInvertible`); the
inductive step is `blowUp.exists_comp_iso` applied to the first center and the center of the
induction hypothesis on the blown-up scheme, the support union splitting off the index `0`. Main
Theorem I takes the composite of the resolution sequence as a single blow-up `K.blowUp` and then
enlarges its centre (`Hironaka/Resolution/Algebraic/Hir64/MainTheoremI.lean`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence Scheme.IdealSheafData
  IdealSheafData

namespace AlgebraicGeometry


/-- A union over `Fin (n + 1)` splits off the index `0`. -/
theorem iUnion_fin_succ_eq {α : Type*} {n : ℕ} (F : Fin (n + 1) → Set α) :
    ⋃ i, F i = F 0 ∪ ⋃ j : Fin n, F j.succ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union, Fin.exists_fin_succ]

/-- The empty sequence is one blow-up: `K = ⊤`, `blowUp X ⊤ ≅ X`. -/
theorem exists_blowUp_composite_iso_nil (X : Scheme.{u}) :
    ∃ K : X.IdealSheafData,
      (K.support : Set X) = ⋃ i : Fin (nil X).length,
        (nil X).stageMap i.castSucc '' (((nil X).center i).support : Set ((nil X).stage _)) ∧
      ∃ e : (nil X).last ≅ K.blowUp,
        e.hom ≫ K.blowUpπ = (nil X).composite ∧
        ∀ ψ : (nil X).last ⟶ K.blowUp, ψ ≫ K.blowUpπ =
            (nil X).composite → ψ = e.hom := by
  obtain ⟨g, hg1, hg2⟩ :=
    (blowUp.isIso_π_of_isInvertible (⊤ : X.IdealSheafData) isInvertible_top).out
  refine ⟨⊤, ?_, ⟨g, IdealSheafData.blowUpπ ⊤, hg2, hg1⟩, hg2, fun ψ hψ => ?_⟩
  · rw [support_top, TopologicalSpace.Closeds.coe_bot]
    exact (Set.iUnion_eq_empty.mpr fun i => i.elim0).symm
  · have hid : ((⊤ : X.IdealSheafData).comap (𝟙 X)).IsInvertible := by
      rw [comap_id]; exact isInvertible_top
    exact blowUp.hom_ext ⊤ (𝟙 X) hid ψ g hψ hg2

/-- The inductive step: the composition of two blow-ups as one blow-up (`blowUp.exists_comp_iso`,
[Sta, Tag 080B]) applied to `D` and the center `K'` of the induction hypothesis on `D.blowUp`;
the support union splits off the index `0` (`|V(D)|`, under `𝟙 X`) and shifts the other indices
along `π_D`. -/
theorem exists_blowUp_composite_iso_cons (X : Scheme.{u}) [IsNoetherian X] (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) (K' : D.blowUp.IdealSheafData)
    (hK' : (K'.support : Set D.blowUp) = ⋃ i : Fin rest.length,
      rest.stageMap i.castSucc '' ((rest.center i).support : Set (rest.stage _)))
    (e' : rest.last ≅ K'.blowUp)
    (he' : e'.hom ≫ K'.blowUpπ = rest.composite) :
    ∃ K : X.IdealSheafData,
      (K.support : Set X) = ⋃ i : Fin (cons X D rest).length,
        (cons X D rest).stageMap i.castSucc ''
          (((cons X D rest).center i).support : Set ((cons X D rest).stage _)) ∧
      ∃ e : (cons X D rest).last ≅ K.blowUp,
        e.hom ≫ K.blowUpπ = (cons X D rest).composite ∧
        ∀ ψ : (cons X D rest).last ⟶ K.blowUp,
          ψ ≫ K.blowUpπ = (cons X D rest).composite → ψ = e.hom := by
  obtain ⟨K, hK, hiso⟩ := blowUp.exists_comp_iso D K'
  refine ⟨K, ?_, ?_⟩
  · rw [hK, hK', Set.image_iUnion]
    refine Eq.trans ?_ (iUnion_fin_succ_eq _).symm
    exact congrArg₂ (· ∪ ·) (Set.image_id _).symm
      (Set.iUnion_congr fun j => (Set.image_comp _ _ _).symm)
  · exact exists_unique_iso_over_of_iso e'
      ((Category.assoc _ _ _).symm.trans (congrArg (fun φ => φ ≫ D.blowUpπ) he')) hiso

/-- `exists_blowUp_composite_iso` by induction on the sequence, the Noetherian hypothesis carried
along the stages (`blowUp.isNoetherian`). -/
theorem exists_blowUp_composite_iso' :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) [IsNoetherian X],
    ∃ K : X.IdealSheafData,
      (K.support : Set X) =
        ⋃ i : Fin S.length, S.stageMap i.castSucc '' ((S.center i).support : Set (S.stage _)) ∧
      ∃ e : S.last ≅ K.blowUp,
        e.hom ≫ K.blowUpπ = S.composite ∧
        ∀ ψ : S.last ⟶ K.blowUp, ψ ≫ K.blowUpπ = S.composite → ψ = e.hom := by
  intro X S
  induction S with
  | nil X =>
    intro _
    exact exists_blowUp_composite_iso_nil X
  | cons X D rest ih =>
    intro _
    have := blowUp.isNoetherian D
    obtain ⟨K', hK', e', he', -⟩ := ih
    exact exists_blowUp_composite_iso_cons X D rest K' hK' e' he'

/-- A finite succession of monoidal transformations of a Noetherian scheme is one blow-up, with
center supported in the union of the images of the centers (the remark following Main Theorem I
in [Hir64, pp. 132–133]). -/
theorem exists_blowUp_composite_iso {X : Scheme.{u}} [IsNoetherian X] (S : BlowUpSequence X) :
    ∃ K : X.IdealSheafData,
      (K.support : Set X) =
        ⋃ i : Fin S.length, S.stageMap i.castSucc '' ((S.center i).support : Set (S.stage _)) ∧
      ∃ e : S.last ≅ K.blowUp,
        e.hom ≫ K.blowUpπ = S.composite ∧
        ∀ ψ : S.last ⟶ K.blowUp, ψ ≫ K.blowUpπ = S.composite → ψ = e.hom :=
  exists_blowUp_composite_iso' S

end AlgebraicGeometry
