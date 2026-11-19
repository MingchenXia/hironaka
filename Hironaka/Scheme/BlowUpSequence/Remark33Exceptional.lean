/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.BlowUpMap.Defs
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Membership
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.InvertibleSheaf
public import Hironaka.Scheme.BlowUpSequence.Remark33Iso
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Hironaka.Scheme.BlowUp.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Covers by open immersions, and blow-ups of restrictions to opens

General lemmas written for the exceptional divisors of [Kol07, Remark 33] on the affine model
(`HironakaExamples/Sequence/Remark33Exceptional.lean`):

* `le_of_comap_le_of_forall_exists`: an inequality of ideal sheaves holds if it holds after `comap`
  along a jointly surjective family of open immersions (the affine version is
  `le_of_comap_le_of_iSup_eq_top`);
* `comap_colon_of_isOpenImmersion'`: inverse image along any open immersion commutes with the colon
  by an invertible ideal sheaf;
* `isOpenImmersion_blowUpMap`, `exists_blowUpMap_eq`: along an open immersion `h`, `blowUpMap h D`
  is an open immersion (the base change of `h` along `IdealSheafData.blowUpπ D`,
  `isPullback_blowUpMap`) whose image is the preimage of the range of `h`;
* `specIdealSheaf_top`: the ideal sheaf of the unit ideal is the unit ideal sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry Scheme.IdealSheafData Scheme.Hom
  affineBlowUpAlgebra MvPolynomial

namespace AlgebraicGeometry.Remark33

/-! ### Covers by open immersions from arbitrary schemes -/

section Cover

variable {M : Scheme.{u}}

/-- An inequality of ideal sheaves holds if it holds after `comap` along a jointly surjective
family of open immersions (the affine version is `le_of_comap_le_of_iSup_eq_top`). -/
theorem le_of_comap_le_of_forall_exists {I J : M.IdealSheafData} {ι : Type*}
    {Y : ι → Scheme.{u}} (c : ∀ i, Y i ⟶ M) [∀ i, IsOpenImmersion (c i)]
    (hc : ∀ x : M, ∃ i y, c i y = x) (h : ∀ i, I.comap (c i) ≤ J.comap (c i)) : I ≤ J := by
  refine le_of_iSup_eq_top
    (fun p : Σ i, (Y i).affineOpens =>
      ⟨c p.1 ''ᵁ p.2.1, p.2.2.image_of_isOpenImmersion (c p.1)⟩) ?_ fun p => ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, y, rfl⟩ := hc x
    obtain ⟨V, hyV⟩ : ∃ V : (Y i).affineOpens, y ∈ V.1 := by
      have hy : y ∈ (⊤ : (Y i).Opens) := trivial
      rw [← iSup_affineOpens_eq_top (Y i)] at hy
      exact TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, V⟩, ⟨y, hyV, rfl⟩⟩
  · have h1 := le_def.mp (h p.1) p.2
    rw [ideal_comap_of_isOpenImmersion, ideal_comap_of_isOpenImmersion] at h1
    exact (Ideal.comap_le_comap_iff_of_surjective _
      ((c p.1).appIso p.2.1).symm.commRingCatIsoToRingEquiv.surjective _ _).mp h1

/-- Inverse image along any open immersion commutes with the colon by an invertible ideal sheaf
(from the affine case `comap_colon_of_isOpenImmersion`). -/
theorem comap_colon_of_isOpenImmersion' {Y : Scheme.{u}} (c : Y ⟶ M) [IsOpenImmersion c]
    (I : M.IdealSheafData) {K : M.IdealSheafData} (hK : K.IsInvertible) :
    (I.colon K).comap c = (I.comap c).colon (K.comap c) := by
  have key : ∀ V : Y.affineOpens,
      ((I.colon K).comap c).comap V.1.ι = ((I.comap c).colon (K.comap c)).comap V.1.ι := by
    intro V
    have : IsAffine (V.1 : Scheme.{u}) := V.2
    rw [← comap_comp, comap_colon_of_isOpenImmersion (V.1.ι ≫ c) I hK,
      comap_colon_of_isOpenImmersion V.1.ι _ (hK.comap_of_isOpenImmersion c), comap_comp,
      comap_comp]
  have hcov : ∀ x : Y, ∃ (V : Y.affineOpens) (y : (V.1 : Scheme.{u})), V.1.ι y = x := by
    intro x
    have hx : x ∈ (⊤ : Y.Opens) := trivial
    rw [← iSup_affineOpens_eq_top Y] at hx
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨V, ⟨x, hV⟩, rfl⟩
  exact le_antisymm
    (le_of_comap_le_of_forall_exists (fun V : Y.affineOpens => V.1.ι) hcov fun V => (key V).le)
    (le_of_comap_le_of_forall_exists (fun V : Y.affineOpens => V.1.ι) hcov fun V => (key V).ge)

end Cover

/-! ### The blow-up of a restriction to an open covers the preimage of that open -/

section BlowUpMap

variable {Y X : Scheme.{u}}

/-- `blowUpMap h D` along an open immersion `h` is an open immersion: it is the base change of
`h` along `IdealSheafData.blowUpπ D` (the pullback square `isPullback_blowUpMap`). -/
instance isOpenImmersion_blowUpMap (h : Y ⟶ X) [IsOpenImmersion h] (D : X.IdealSheafData) :
    IsOpenImmersion (blowUpMap h D) := by
  rw [← (isPullback_blowUpMap h D).isoPullback_hom_fst]
  infer_instance

/-- A point of `blowUp D` over the range of the open immersion `h` comes from `blowUp (D|_U)`. -/
theorem exists_blowUpMap_eq (h : Y ⟶ X) [IsOpenImmersion h] (D : X.IdealSheafData)
    (x : blowUp D) (y : Y) (hxy : blowUpπ D x = h y) : ∃ z, blowUpMap h D z = x := by
  have sq := isPullback_blowUpMap h D
  obtain ⟨w, hw, -⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := blowUpπ D) (g := h) x y hxy
  have hb : sq.isoPullback.inv ≫ blowUpMap h D = Limits.pullback.fst (blowUpπ D) h :=
    (Iso.inv_comp_eq _).mpr sq.isoPullback_hom_fst.symm
  exact ⟨sq.isoPullback.inv w, by rw [← Scheme.Hom.comp_apply, hb, hw]⟩

end BlowUpMap

section Spec

variable {R : Type u} [CommRing R]

/-- The ideal sheaf of the unit ideal is the unit ideal sheaf. -/
theorem specIdealSheaf_top : specIdealSheaf (⊤ : Ideal R) = ⊤ :=
  le_antisymm le_top (le_of_isAffine (by
    simp only [specIdealSheaf, ofIdealTop_ideal_top, Ideal.map_top, le_top]))

end Spec

end AlgebraicGeometry.Remark33
