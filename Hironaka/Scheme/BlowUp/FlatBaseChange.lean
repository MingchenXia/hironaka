/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.UniversalProperty
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.BlowUp.InvertibleSheaf

/-!
# Blow-ups commute with flat base change

For a flat `g : X₁ ⟶ X₂` and a centre `I` on `X₂`, the blow-up of `X₁` along `I·𝒪_{X₁} = I.comap g`
is the fibre product `X₁ ×_{X₂} B_I X₂` [Sta, Tag 0805].  The restriction of a blow-up to an open
subscheme [Hau14, Corollary 5.2 (b)] is the case of an open immersion, the blow-up of a product
[Hau14, Corollary 5.2 (e)] the case of a product projection.  The flat case along
`Spec 𝒪_{X,x} ⟶ X` gives the local structure of a blow-up at a point
(`Hironaka.Scheme.Smooth.LocalBlowUp`), and along a flat morphism of bases it gives the induced
morphism of blow-ups (`Hironaka.Scheme.BlowUp.BlowUpMap`).

## The argument, from the universal property

The Stacks Project proves the lemma by computing the relative Proj: flatness makes
`g^*Iⁿ → 𝒪_{X₁}` injective with image `(I·𝒪_{X₁})ⁿ`.  The proof below reaches the same statement
from the same hypotheses through the universal property [Hau14, Definition 4.4] alone, in the
manner of Hauser's proof of [Hau14, Proposition 5.1] (the universal property of the blow-up
against the universal property of the fibre product), so that it applies to any `π` with
`IsBlowUp I π`.

Let `P := X₁ ×_{X₂} B₂` with projections `p₁ : P ⟶ X₁`, `p₂ : P ⟶ B₂`, and write `I₁ := I.comap g`.

1. *`P ⟶ X₁` is admissible for `I₁`.*  `I₁.comap p₁ = I.comap (p₁ ≫ g) = I.comap (p₂ ≫ π₂) =
   (I.comap π₂).comap p₂`; `I.comap π₂` is invertible (clause (i) for `π₂`) and `p₂`, the base
   change of the flat `g`, is flat, and the inverse image of an invertible ideal sheaf along a
   flat morphism is invertible (`IsInvertible.comap_of_flat`: a nonzerodivisor stays a
   nonzerodivisor under a flat ring map, the injectivity that flatness gives in [Sta, Tag 0805],
   for `n = 1`).  So `p₁` lifts to `τ : P ⟶ B₁` with `τ ≫ π₁ = p₁`.
2. *`π₁ ≫ g` is admissible for `I`* (`I.comap (π₁ ≫ g) = I₁.comap π₁`, clause (i) for `π₁`), so
   it lifts to `φ : B₁ ⟶ B₂` with `φ ≫ π₂ = π₁ ≫ g`; this is the morphism of the square, and
   `σ := (π₁, φ) : B₁ ⟶ P` is the canonical comparison map.
3. *`σ` and `τ` are inverse.*  `σ ≫ τ` and `𝟙 B₁` are two lifts of `π₁` along `π₁`, which is
   admissible for `I₁`, so they agree (clause (ii)).  `τ ≫ φ` and `p₂` are two lifts along `π₂`
   of the admissible `p₁ ≫ g = p₂ ≫ π₂`, so they agree; hence `τ ≫ σ` agrees with `𝟙 P` on both
   projections.  Therefore `B₁ ≅ P` over the two projections: the square is cartesian.

Nothing about `B₁`, `B₂` beyond the two clauses is used; no Noetherian, separatedness or
finiteness hypothesis enters ([Sta, Tag 0805] has none).

## Main declarations

* `IdealSheafData.IsInvertible.comap_of_flat`: the inverse image of an invertible ideal sheaf
  along a flat morphism is invertible.
* `IsBlowUp.exists_isPullback_of_flat`, `IsBlowUp.exists_isPullback_of_etale`,
  `IsBlowUp.exists_isPullback_prod` (with the pasted square `B_{Z × a}(Z ×_S Y) = Z ×_S B_a Y`).
* `exists_restrictIso_of_isPullback`: the pullback square of a blow-up along an open `U ⊆ X` read
  as Hauser prints it, an isomorphism `B_{I|_U} U ≅ π⁻¹(U)` carrying `π_U` to the restriction
  `π ∣_ U` — both are pullbacks of the same cospan.

Every morphism to `Spec k`, `k` a field, is flat (`flat_of_field`, in
`Hironaka/Scheme/Smooth/ExceptionalBaseChange.lean`), which makes Hauser's product formula over a
field an instance of flat base change.
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory Limits

universe u

section InvertibleComap

variable {X Y : Scheme.{u}}

/-- The inverse image of an invertible ideal sheaf along a flat morphism is invertible (flatness
of `g` makes `g^*𝓘ⁿ → 𝒪` injective [Sta, Tag 0805], here for `n = 1`).  On an affine open
`V ⊆ f⁻¹(U)` with `J(U) = (a)`, `(J.comap f)(V) = (f♯a)` (`ideal_comap_of_le`) and `f♯a` is a
nonzerodivisor because `f♯ : Γ(U) → Γ(V)` is flat and multiplication by `a` is injective. -/
theorem Scheme.IdealSheafData.IsInvertible.comap_of_flat (f : Y ⟶ X)
    [Flat f] {J : X.IdealSheafData} (hJ : J.IsInvertible) : (J.comap f).IsInvertible := fun y => by
  obtain ⟨U, hxU, a, ha, hJU⟩ := hJ (f y)
  obtain ⟨V₁, hyV₁⟩ := Scheme.IdealSheafData.exists_affineOpens_mem y
  obtain ⟨s, hs_le, hys⟩ := V₁.2.exists_basicOpen_le (V := f ⁻¹ᵁ U.1) ⟨y, hxU⟩ hyV₁
  have e : (Y.affineBasicOpen s).1 ≤ f ⁻¹ᵁ U.1 := hs_le
  have hφ : (f.appLE U.1 (Y.affineBasicOpen s).1 e).hom.Flat :=
    f.flat_appLE U.2 (Y.affineBasicOpen s).2 e
  set φ := (f.appLE U.1 (Y.affineBasicOpen s).1 e).hom with hφ_def
  have hnzd : φ a ∈ nonZeroDivisors Γ(Y, Y.affineBasicOpen s) := by
    algebraize [φ]
    have hreg : IsSMulRegular Γ(X, U) a :=
      isLeftRegular_iff.mp
        (isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr (mem_nonZeroDivisors_iff'.mp ha).1)
    have hreg' : IsSMulRegular Γ(Y, Y.affineBasicOpen s) (algebraMap Γ(X, U) _ a) :=
      hreg.of_flat
    rw [RingHom.algebraMap_toAlgebra] at hreg'
    refine mem_nonZeroDivisors_iff.mpr ⟨fun x hx => hreg' ?_, fun x hx => hreg' ?_⟩
    · change φ a • x = φ a • 0
      rw [smul_eq_mul, smul_zero]; exact hx
    · change φ a • x = φ a • 0
      rw [smul_eq_mul, smul_zero, mul_comm]; exact hx
  refine ⟨Y.affineBasicOpen s, hys, φ a, hnzd, ?_⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_le J f U (Y.affineBasicOpen s) e, hJU, Ideal.map_span,
    Set.image_singleton]

end InvertibleComap

section Restrict

variable {X B B' : Scheme.{u}}

/-- The blow-up of an open `U` along `U ∩ Z` is the restriction of `π` to `π⁻¹(U)`
[Hau14, Corollary 5.2 (b)]: a pullback square `B' → B` over `U.ι : U → X` gives an isomorphism
`B' ≅ π⁻¹(U)` carrying `π' : B' ⟶ U` to Mathlib's restriction `π ∣_ U`, because `π⁻¹(U)` with
`π ∣_ U` is a pullback of the same cospan (`isPullback_morphismRestrict`). -/
theorem exists_restrictIso_of_isPullback {π : B ⟶ X} (U : X.Opens) {π' : B' ⟶ U} {φ : B' ⟶ B}
    (H : IsPullback φ π' π U.ι) :
    ∃ e : B' ≅ (π ⁻¹ᵁ U).toScheme, e.hom ≫ (π ∣_ U) = π' :=
  ⟨H.flip.isoIsPullback _ _ (isPullback_morphismRestrict π U),
    H.flip.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict π U)⟩

end Restrict

namespace IsBlowUp

variable {X₁ X₂ B₁ B₂ : Scheme.{u}} {I : X₂.IdealSheafData}

/-- **Blowing up commutes with flat base change** [Sta, Tag 0805], proved from the universal
property as described in the module docstring: for `g : X₁ ⟶ X₂` flat and blow-ups `π₂ : B₂ ⟶ X₂`
along `I` and `π₁ : B₁ ⟶ X₁` along `I.comap g` in the sense of `IsBlowUp`, there is `φ : B₁ ⟶ B₂`
over `g` with `B₁ = X₁ ×_{X₂} B₂`. -/
theorem exists_isPullback_of_flat (g : X₁ ⟶ X₂) [Flat g] {π₂ : B₂ ⟶ X₂} (h₂ : IsBlowUp I π₂)
    {π₁ : B₁ ⟶ X₁} (h₁ : IsBlowUp (I.comap g) π₁) : ∃ φ : B₁ ⟶ B₂, IsPullback φ π₁ π₂ g := by
  have hcond : Limits.pullback.fst π₂ g ≫ π₂ = Limits.pullback.snd π₂ g ≫ g :=
      Limits.pullback.condition
  -- step 1: the first projection of the fibre product is admissible for `I.comap g`
  have hinv : ((I.comap g).comap (Limits.pullback.snd π₂ g)).IsInvertible := by
    rw [← Scheme.IdealSheafData.comap_comp, ← hcond, Scheme.IdealSheafData.comap_comp]
    exact h₂.admissible.comap_of_flat (Limits.pullback.fst π₂ g)
  obtain ⟨τ, hτ⟩ := h₁.exists_lift (Limits.pullback.snd π₂ g) hinv
  -- step 2: `π₁ ≫ g` is admissible for `I`; its lift is the morphism of the square
  have hadm : (I.comap (π₁ ≫ g)).IsInvertible := by
    rw [Scheme.IdealSheafData.comap_comp]
    exact h₁.admissible
  obtain ⟨φ, hφ⟩ := h₂.exists_lift (π₁ ≫ g) hadm
  let σ : B₁ ⟶ Limits.pullback π₂ g := Limits.pullback.lift φ π₁ hφ
  have hσ₁ : σ ≫ Limits.pullback.fst π₂ g = φ := Limits.pullback.lift_fst _ _ _
  have hσ₂ : σ ≫ Limits.pullback.snd π₂ g = π₁ := Limits.pullback.lift_snd _ _ _
  -- step 3: `σ` and `τ` are inverse, by uniqueness of lifts
  have hστ : σ ≫ τ = 𝟙 B₁ :=
    h₁.hom_ext π₁ h₁.admissible (σ ≫ τ) (𝟙 B₁)
      (by rw [Category.assoc, hτ, hσ₂]) (Category.id_comp π₁)
  have hτφ : τ ≫ φ = Limits.pullback.fst π₂ g :=
    h₂.hom_ext (Limits.pullback.snd π₂ g ≫ g)
      (by rw [Scheme.IdealSheafData.comap_comp]; exact hinv) (τ ≫ φ) (Limits.pullback.fst π₂ g)
      (by rw [Category.assoc, hφ, ← Category.assoc, hτ]) hcond
  have hτσ : τ ≫ σ = 𝟙 (Limits.pullback π₂ g) := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hσ₁, Category.id_comp, hτφ]
    · rw [Category.assoc, hσ₂, Category.id_comp, hτ]
  exact ⟨φ, IsPullback.of_iso_pullback ⟨hφ⟩ ⟨σ, τ, hστ, hτσ⟩ hσ₁ hσ₂⟩

/-- The base-change square for an étale `g` [Sta, Tag 0805] (étale morphisms are flat, Mathlib's
`Etale → Smooth → Flat`). -/
theorem exists_isPullback_of_etale (g : X₁ ⟶ X₂) [Etale g] {π₂ : B₂ ⟶ X₂} (h₂ : IsBlowUp I π₂)
    {π₁ : B₁ ⟶ X₁} (h₁ : IsBlowUp (I.comap g) π₁) : ∃ φ : B₁ ⟶ B₂, IsPullback φ π₁ π₂ g :=
  h₂.exists_isPullback_of_flat g h₁

/-- The blow-up of a product [Hau14, Corollary 5.2 (e)], over any base `S` with `Z ⟶ S` flat
(Hauser's case is `S = Spec k`, where every morphism is flat): the blow-up of
`Z ×_S Y` along `Z × a = a.comap pr₂` is the flat base change of `B_a Y ⟶ Y` along the projection
`pr₂`, and, pasting with the product square, it is `Z ×_S B_a Y`: `B' = Z ×_S B_a Y` over
`Z ⟶ S ⟵ B_a Y ⟶ Y ⟶ S`. -/
theorem exists_isPullback_prod {S Z Y BY B' : Scheme.{u}} (fZ : Z ⟶ S) [Flat fZ] (fY : Y ⟶ S)
    {a : Y.IdealSheafData} {πY : BY ⟶ Y} (hY : IsBlowUp a πY) {π' : B' ⟶ Limits.pullback fZ fY}
    (h' : IsBlowUp (a.comap (Limits.pullback.snd fZ fY)) π') :
    ∃ φ : B' ⟶ BY, IsPullback φ π' πY (Limits.pullback.snd fZ fY) ∧
      IsPullback (π' ≫ Limits.pullback.fst fZ fY) φ fZ (πY ≫ fY) := by
  obtain ⟨φ, H⟩ := hY.exists_isPullback_of_flat (Limits.pullback.snd fZ fY) h'
  exact ⟨φ, H, H.flip.paste_horiz (IsPullback.of_hasPullback fZ fY)⟩

end IsBlowUp

end AlgebraicGeometry
