/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Admissible
public import Hironaka.Scheme.IdealSheaf.Defs
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUp.Transform
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Hironaka.Scheme.Smooth.BlowUpSmoothChart  -- shake: keep (used only by `example`s)
import Hironaka.Scheme.BlowUp.Transform.TransformIso  -- shake: keep (used only by `example`s)
import Hironaka.Scheme.BlowUp.Transform.WeakTransform  -- shake: keep (used only by `example`s)
import Hironaka.Scheme.BlowUp.Composite  -- shake: keep (used only by `example`s)
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Restrict  -- shake: keep (used only by `example`s)
import Hironaka.Scheme.BlowUp.BlowUpMap  -- shake: keep (used only by `example`s)

/-!
# Colon ideals along ring maps and open immersions; inequalities on covers

Helpers for colon ideals and ideal sheaves, written for the computation of [Kol07, Remark 33] on
the affine model (`HironakaExamples/Sequence/Remark33Iso.lean`):

* `Ideal.comap_colon_of_surjective`, `Ideal.map_colon_of_bijective`: the colon commutes with the
  comap along a surjective ring map and with the map along a bijective one;
* `le_of_comap_le_of_iSup_eq_top`: an inequality of ideal sheaves holds if it holds after `comap`
  along a cover by open immersions from affine schemes;
* `comap_colon_of_isOpenImmersion`: inverse image along an open immersion from an affine scheme
  commutes with the colon by an invertible ideal sheaf;
* `specIdealSheaf_colon`: on `Spec R`, the colon of ideal sheaves is the ideal sheaf of the colon
  when the divisor is invertible.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData CoordinateSubspace MvPolynomial

/-! ### Ring-level helpers: colon ideals along surjective and bijective ring maps -/

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The comap along a surjective ring map commutes with the colon. -/
theorem comap_colon_of_surjective (f : R →+* S) (hf : Function.Surjective f) (I J : Ideal S) :
    (I.colon (J : Set S)).comap f = (I.comap f).colon ((J.comap f : Ideal R) : Set R) := by
  ext x
  simp only [Ideal.mem_comap, Submodule.mem_colon, smul_eq_mul]
  constructor
  · intro h p hp
    rw [map_mul]
    exact h (f p) (Ideal.mem_comap.mp hp)
  · intro h q hq
    obtain ⟨p, rfl⟩ := hf q
    have := h p (Ideal.mem_comap.mpr hq)
    rwa [map_mul] at this

/-- The map along a bijective ring map commutes with the colon. -/
theorem map_colon_of_bijective (f : R →+* S) (hf : Function.Bijective f) (I J : Ideal R) :
    (I.colon (J : Set R)).map f = (I.map f).colon ((J.map f : Ideal S) : Set S) := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective f hf.2, Submodule.mem_colon]
  constructor
  · rintro ⟨x, hx, rfl⟩ q hq
    obtain ⟨p, hp, rfl⟩ := Ideal.mem_map_iff_of_surjective f hf.2 |>.mp hq
    rw [smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem f (Submodule.mem_colon.mp hx p hp)
  · intro h
    obtain ⟨x, rfl⟩ := hf.2 y
    refine ⟨x, Submodule.mem_colon.mpr fun p hp => ?_, rfl⟩
    have := h (f p) (Ideal.mem_map_of_mem f hp)
    rw [smul_eq_mul, ← map_mul] at this
    obtain ⟨z, hz, hzx⟩ := Ideal.mem_map_iff_of_surjective f hf.2 |>.mp this
    rwa [hf.1 hzx] at hz

end Ideal

namespace AlgebraicGeometry.Remark33

/-! ### Sheaf-level helpers: inequalities on a cover by open immersions, colons along them -/

section Cover

variable {M : Scheme.{u}}

/-- An inequality of ideal sheaves holds if it holds after `comap` along the members of a cover by
open immersions from affine schemes. -/
theorem le_of_comap_le_of_iSup_eq_top {I J : M.IdealSheafData} {ι : Type*} {Y : ι → Scheme.{u}}
    (c : ∀ i, Y i ⟶ M) [∀ i, IsOpenImmersion (c i)] [∀ i, IsAffine (Y i)]
    (hc : ⨆ i, (c i).opensRange = ⊤) (h : ∀ i, I.comap (c i) ≤ J.comap (c i)) : I ≤ J := by
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun i => ⟨(c i) ''ᵁ ⊤, (isAffineOpen_top (Y i)).image_of_isOpenImmersion (c i)⟩) ?_ fun i => ?_
  · simpa only [Scheme.Hom.image_top_eq_opensRange] using hc
  · have h1 := Scheme.IdealSheafData.le_def.mp (h i) ⟨⊤, isAffineOpen_top (Y i)⟩
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
        Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h1
    exact (Ideal.comap_le_comap_iff_of_surjective _
      ((c i).appIso ⊤).symm.commRingCatIsoToRingEquiv.surjective _ _).mp h1

/-- Inverse image along an open immersion from an affine scheme commutes with the colon by an
invertible ideal sheaf. -/
theorem comap_colon_of_isOpenImmersion {Y : Scheme.{u}} [IsAffine Y] (c : Y ⟶ M)
    [IsOpenImmersion c] (I : M.IdealSheafData) {K : M.IdealSheafData} (hK : K.IsInvertible) :
    (I.colon K).comap c = (I.comap c).colon (K.comap c) := by
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  have hθ : Function.Surjective ⇑((c.appIso ⊤).inv.hom) :=
    (c.appIso ⊤).symm.commRingCatIsoToRingEquiv.surjective
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (I.colon K) c ⟨⊤,
      isAffineOpen_top Y⟩
  have h2 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I c ⟨⊤, isAffineOpen_top Y⟩
  have h3 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion K c ⟨⊤, isAffineOpen_top Y⟩
  rw [h1, Scheme.IdealSheafData.ideal_colon_of_isInvertible I K hK,
      Ideal.comap_colon_of_surjective _ hθ, ← h2, ← h3,
    Scheme.IdealSheafData.ideal_colon_of_isInvertible _ _ (hK.comap_of_isOpenImmersion c)]

end Cover

section Spec

variable {R : Type u} [CommRing R]

/-- On `Spec R`, the colon of the ideal sheaves of `P` and of an invertible `Q` is the ideal
sheaf of the colon. -/
theorem specIdealSheaf_colon (P Q : Ideal R) (hQ : (specIdealSheaf Q).IsInvertible) :
    (specIdealSheaf P).colon (specIdealSheaf Q) = specIdealSheaf (P.colon (Q : Set R)) := by
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  have hι : Function.Bijective ⇑((Scheme.ΓSpecIso (.of R)).inv.hom) :=
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective
  rw [Scheme.IdealSheafData.ideal_colon_of_isInvertible _ _ hQ, specIdealSheaf_ideal_top,
      specIdealSheaf_ideal_top,
    specIdealSheaf_ideal_top, Ideal.map_colon_of_bijective _ hι]

end Spec

end AlgebraicGeometry.Remark33
