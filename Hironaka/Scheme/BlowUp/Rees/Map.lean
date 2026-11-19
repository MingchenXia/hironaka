/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Hironaka.Scheme.BlowUp.Rees.Basic
import Hironaka.Scheme.BlowUp.Rees.DegreeZero
import Hironaka.Scheme.BlowUp.Rees.Irrelevant

/-!
# The graded Rees algebra along a ring map, and `Proj.map` over degree zero

For a ring map `φ : R → S` and ideals `I ⊆ R`, `J ⊆ S` with `φ(I) ⊆ J`, applying `φ` to the
coefficients sends `Rees(I) = ⨁ Iⁿtⁿ` into `Rees(J)` degreewise: the graded ring map
`reesAlgebra.mapOfLe φ hIJ : grading I →+*ᵍ grading J`.  These are the transition maps of the
relative `Proj` of the Rees algebra of an ideal sheaf [Sta, Tags 01OF and 0804]: they are
induced by the restriction maps of the structure sheaf, along which `I(U) = I(V) Γ(U)`.  When
`J = I S`, the degree-one elements `b t`, `b ∈ J`, are `S`-combinations of the images `φ(a) t`,
`a ∈ I`, so the irrelevant ideal of `Rees(J)` lies in the image of that of `Rees(I)`
(`reesAlgebra.irrelevant_le_map_mapOfEq`, from the generation in degree one of
`Hironaka.Scheme.BlowUp.Rees.Irrelevant`) — the hypothesis under which Mathlib's `Proj.map` produces
`Proj Rees(J) ⟶ Proj Rees(I)`.

Mathlib's `Proj.map` comes with its chart compatibility `awayι_comp_map` but not with its
compatibility with the structure map `toSpecZero`; `Proj.map_toSpecZero` below proves it for any
graded ring map, by the affine cover of `Proj` and `awayι_toSpecZero`: on `Spec (B_{f s})₀` both
composites are `Spec` of the ring map `𝒜₀ → (B_{f s})₀`, `x ↦ f(x)/1`.

## Boundary cases

No hypothesis on `φ` (it need not be flat or injective); `I.map φ ≤ J` suffices for the graded
map, `I.map φ = J` for the `Proj.map` hypothesis.  `φ = id` gives the identity graded map
(`reesAlgebra.mapOfLe_id`) and composites compose (`reesAlgebra.mapOfLe_comp`).
-/

@[expose] public section

open AlgebraicGeometry

open Polynomial

universe u

section GradedMap

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable {I : Ideal R} {J : Ideal S} {K : Ideal T}

@[simp]
theorem reesAlgebra.coe_mapOfLe_apply (φ : R →+* S) (hIJ : I.map φ ≤ J) (p : reesAlgebra I) :
    ((reesAlgebra.mapOfLe φ hIJ p : reesAlgebra J) : S[X]) = (p : R[X]).map φ :=
  rfl

theorem reesAlgebra.mapOfLe_degreeOne (φ : R →+* S) (hIJ : I.map φ ≤ J) (a : I) :
    reesAlgebra.mapOfLe φ hIJ (reesAlgebra.degreeOne I a) =
      reesAlgebra.degreeOne J ⟨φ a, hIJ (Ideal.mem_map_of_mem φ a.2)⟩ :=
  Subtype.ext (by simp [map_monomial])

theorem reesAlgebra.mapOfLe_id (h : I.map (RingHom.id R) ≤ I) :
    reesAlgebra.mapOfLe (RingHom.id R) h = GradedRingHom.id (reesAlgebra.grading I) :=
  GradedRingHom.ext fun p => Subtype.ext (Polynomial.map_id (p := (p : R[X])))

theorem reesAlgebra.mapOfLe_comp (φ : R →+* S) (ψ : S →+* T) (hIJ : I.map φ ≤ J)
    (hJK : J.map ψ ≤ K) (hIK : I.map (ψ.comp φ) ≤ K) :
    reesAlgebra.mapOfLe (ψ.comp φ) hIK =
      (reesAlgebra.mapOfLe ψ hJK).comp (reesAlgebra.mapOfLe φ hIJ) :=
  GradedRingHom.ext fun p => Subtype.ext (Polynomial.map_map φ ψ (p : R[X])).symm

/-- The degree-zero restriction of a graded Rees map is the constant map `φ`, through the
identifications `grading I 0 ≅ R` and `grading J 0 ≅ S`. -/
theorem reesAlgebra.coe_mapOfLe_gradingZeroEquiv_symm (φ : R →+* S) (hIJ : I.map φ ≤ J) (r : R) :
    ((reesAlgebra.mapOfLe φ hIJ ((reesAlgebra.gradingZeroEquiv I).symm r) : reesAlgebra J) : S[X]) =
      (((reesAlgebra.gradingZeroEquiv J).symm (φ r) : reesAlgebra J) : S[X]) := by
  rw [reesAlgebra.coe_mapOfLe_apply, reesAlgebra.coe_gradingZeroEquiv_symm,
    reesAlgebra.coe_gradingZeroEquiv_symm, map_C]

/-- The `Proj.map` hypothesis: when `J = I S`, the irrelevant ideal of `Rees(J)` lies in the image
of that of `Rees(I)`, because `Rees(J)` is generated in degree one [Hau14, Definition 4.6] and
every degree-one element `b t`, `b ∈ J`, is an `S`-combination of the images `φ(a) t`, `a ∈ I`. -/
theorem reesAlgebra.irrelevant_le_map_mapOfEq (φ : R →+* S) (hJ : I.map φ = J) :
    HomogeneousIdeal.irrelevant (reesAlgebra.grading J) ≤
      (HomogeneousIdeal.irrelevant (reesAlgebra.grading I)).map (reesAlgebra.mapOfLe φ hJ.le) := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map]
  refine (reesAlgebra.irrelevant_le_span_degreeOne J).trans (Ideal.span_le.mpr ?_)
  rintro _ ⟨b, rfl⟩
  set M := (HomogeneousIdeal.irrelevant (reesAlgebra.grading I)).toIdeal.map
    (reesAlgebra.mapOfLe φ hJ.le) with hM
  have hb : (b : S) ∈ Ideal.map φ I := hJ ▸ b.2
  refine Submodule.span_induction
    (p := fun b _ => ∀ hb : b ∈ J, reesAlgebra.degreeOne J ⟨b, hb⟩ ∈ M) ?_ ?_ ?_ ?_ hb b.2
  · rintro _ ⟨a, ha, rfl⟩ hb
    rw [show reesAlgebra.degreeOne J ⟨φ a, hb⟩ =
        reesAlgebra.mapOfLe φ hJ.le (reesAlgebra.degreeOne I ⟨a, ha⟩) from
      (reesAlgebra.mapOfLe_degreeOne φ hJ.le ⟨a, ha⟩).symm]
    exact Ideal.mem_map_of_mem _
      (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (reesAlgebra.degreeOne_mem _))
  · intro _
    exact (map_zero (reesAlgebra.degreeOne J)).symm ▸ Ideal.zero_mem _
  · intro x y hx hy ihx ihy _
    have hx' : x ∈ J := hJ ▸ hx
    have hy' : y ∈ J := hJ ▸ hy
    exact (map_add (reesAlgebra.degreeOne J) ⟨x, hx'⟩ ⟨y, hy'⟩).symm ▸
      Ideal.add_mem _ (ihx hx') (ihy hy')
  · intro s x hx ih _
    have hx' : x ∈ J := hJ ▸ hx
    exact (map_smul (reesAlgebra.degreeOne J) s ⟨x, hx'⟩).symm ▸
      Submodule.smul_of_tower_mem _ s (ih hx')

end GradedMap

section ProjMap

open AlgebraicGeometry CategoryTheory HomogeneousLocalization Graded

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The degree-zero part of a graded ring map, as a ring map `𝒜 0 →+* ℬ 0`. -/
def GradedRingHom.zeroRingHom (f : 𝒜 →+*ᵍ ℬ) : 𝒜 0 →+* ℬ 0 where
  toFun x := ⟨f x, map_mem f x.2⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f (x : A) (y : A))
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f (x : A) (y : A))

@[simp]
theorem GradedRingHom.coe_zeroRingHom_apply (f : 𝒜 →+*ᵍ ℬ) (x : 𝒜 0) :
    (GradedRingHom.zeroRingHom f x : B) = f x :=
  rfl

/-- `Away.map` sends the constants of degree zero to the constants of degree zero. -/
theorem AlgebraicGeometry.Away.map_fromZeroRingHom (f : 𝒜 →+*ᵍ ℬ) (s : A) (x : 𝒜 0) :
    HomogeneousLocalization.Away.map f s (fromZeroRingHom 𝒜 (Submonoid.powers s) x) =
      fromZeroRingHom ℬ (Submonoid.powers (f s)) (GradedRingHom.zeroRingHom f x) := by
  change HomogeneousLocalization.map f _ (HomogeneousLocalization.mk ⟨0, x, 1, one_mem _⟩) =
    HomogeneousLocalization.mk ⟨0, GradedRingHom.zeroRingHom f x, 1, one_mem _⟩
  rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.ext_iff_val, val_mk, val_mk]
  congr 1
  exact Subtype.ext (map_one f)

variable (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)

/-- The chart-by-chart statement of `Proj.map_toSpecZero`: on the chart `D₊(f x)` of `Proj ℬ`
both composites are `Spec` of the ring map `𝒜₀ → (B_{f x})₀`, `x ↦ f(x)/1`. -/
theorem AlgebraicGeometry.Proj.awayι_map_toSpecZero (i : ℕ+) (x : 𝒜 i) :
    Proj.awayι ℬ (f x) (f.2 x.2) i.pos ≫ Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.awayι ℬ (f x) (f.2 x.2) i.pos ≫ Proj.toSpecZero ℬ ≫
        Spec.map (CommRingCat.ofHom (GradedRingHom.zeroRingHom f)) := by
  rw [Proj.awayι_comp_map_assoc _ _ i.pos _ x.2, Proj.awayι_toSpecZero,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun y => ?_)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  exact Away.map_fromZeroRingHom f _ y

/-- `Proj.map` over the structure maps to degree zero: for a graded ring map `f : 𝒜 → ℬ`, the
square `Proj ℬ → Proj 𝒜` over `Spec ℬ₀ → Spec 𝒜₀` commutes (Mathlib has the chart compatibility
`Proj.awayι_comp_map`; this is its consequence for `Proj.toSpecZero`, by the affine cover of
`Proj ℬ` and `Proj.awayι_toSpecZero`). -/
@[reassoc]
theorem AlgebraicGeometry.Proj.map_toSpecZero :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom (GradedRingHom.zeroRingHom f)) :=
  (Proj.mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s =>
    Proj.awayι_map_toSpecZero f hf s.1 s.2

end ProjMap

