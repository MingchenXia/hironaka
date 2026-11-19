/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The conormal map of a local algebra at its residue field

Let `R` be a local `k`-algebra with maximal ideal `𝔪` and residue field `κ`. The *conormal map*
`d̄ : 𝔪/𝔪² → κ ⊗[R] Ω[R⁄k]`, `f̄ ↦ 1 ⊗ d f`, is Mathlib's `kerCotangentToTensor k R κ`, and it
sits in the conormal exact sequence `𝔪/𝔪² → κ ⊗[R] Ω[R⁄k] → Ω[κ⁄k] → 0` ([Sta, Tag 00RU];
Mathlib's `exact_kerCotangentToTensor_mapBaseChange`).

**Injectivity.** [Sta, Tag 00TU] says that `d̄` is injective when `κ` is a finitely generated
separable extension of the field `k`. Here separability is used only through *formal smoothness*
of `κ` over `k` [Sta, Tag 0322], and formal smoothness produces, by lifting the identity of `κ`
along the square-zero surjection `R/𝔪² → κ`, a `k`-algebra section `σ : κ → R/𝔪²`. Mathlib's
`retractionKerCotangentToTensorEquivSection` turns such a section into an `R`-linear retraction
of `d̄`, so `d̄` is split injective. This is [Sta, Tag 02HP] ("a right inverse of `S → S'` splits
the conormal sequence") with the right inverse supplied by formal smoothness instead of the
explicit Hensel adjustment in the printed proof of [Sta, Tag 00TU]. Noetherianity of `R` is not
used.

**The dimension count** (the first display in the proof of [Sta, Tag 00TV]): once `d̄` is injective
the conormal sequence is short exact, `0 → 𝔪/𝔪² → κ ⊗[R] Ω[R⁄k] → Ω[κ⁄k] → 0`, so for `R`
essentially of finite type over `k` (which makes `Ω[R⁄k]` a finite module)
`dim_κ κ ⊗[R] Ω[R⁄k] = dim_κ 𝔪/𝔪² + dim_κ Ω[κ⁄k]`. To speak of `κ`-dimensions we repackage `d̄` as
the `κ`-linear map `cotangentSpaceToTensor k R : CotangentSpace R →ₗ[κ] κ ⊗[R] Ω[R⁄k]` on
Mathlib's cotangent space `𝔪/𝔪²` (the domain of `kerCotangentToTensor` is the cotangent module
of `ker (R → κ)`, which is `𝔪` by `IsLocalRing.ker_residue`; the transport is
`Ideal.cotangentEquivOfEq`).
-/

@[expose] public section

universe u

open IsLocalRing KaehlerDifferential
open scoped TensorProduct

namespace Ideal

variable {R : Type u} [CommRing R]

/-- Transport of the cotangent module `I/I²` along an equality of ideals. -/
def cotangentEquivOfEq {I J : Ideal R} (h : I = J) : I.Cotangent ≃ₗ[R] J.Cotangent := by
  subst h; exact LinearEquiv.refl R _

@[simp]
theorem cotangentEquivOfEq_toCotangent {I J : Ideal R} (h : I = J) (x : I) :
    cotangentEquivOfEq h (I.toCotangent x) = J.toCotangent ⟨x, h ▸ x.2⟩ := by
  subst h; rfl

end Ideal

namespace IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- `IsLocalRing.ker_residue` stated for the structure map `R → κ` (the same map). -/
theorem ker_algebraMap_residueField :
    RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R :=
  ker_residue

end IsLocalRing

namespace KaehlerDifferential

variable (k R : Type u) [CommRing k] [CommRing R] [IsLocalRing R] [Algebra k R]

/-- If the residue field `κ` of the local `k`-algebra `R` is formally smooth over `k`, the
conormal map `d̄ : 𝔪/𝔪² → κ ⊗[R] Ω[R⁄k]` is injective ([Sta, Tag 00TU], proved through
[Sta, Tag 02HP] with the section supplied by formal smoothness). Formal smoothness lifts the
identity of `κ` along the square-zero surjection `R/𝔪² → κ` to a `k`-algebra section, and
Mathlib's `retractionKerCotangentToTensorEquivSection` converts the section into a retraction of
`d̄`. -/
theorem injective_kerCotangentToTensor_residueField_of_formallySmooth
    [Algebra.FormallySmooth k (ResidueField R)] :
    Function.Injective (kerCotangentToTensor k R (ResidueField R)) := by
  set φ : R →ₐ[k] ResidueField R := IsScalarTower.toAlgHom k R (ResidueField R) with hφ
  have hsurj : Function.Surjective φ := residue_surjective
  have hsq : RingHom.ker φ.kerSquareLift ^ 2 = ⊥ :=
    (congrArg (· ^ 2) (AlgHom.ker_kerSquareLift φ)).trans (Ideal.cotangentIdeal_square _)
  have hsurj' : Function.Surjective φ.kerSquareLift := fun x => by
    obtain ⟨y, rfl⟩ := hsurj x
    exact ⟨Ideal.Quotient.mk _ y, φ.kerSquareLift_mk y⟩
  set e := Ideal.quotientKerAlgEquivOfSurjective hsurj' with he
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective k (ResidueField R) _ hsq e.symm.toAlgHom
  have hsec : φ.kerSquareLift.comp g = AlgHom.id k (ResidueField R) := by
    ext x
    have h1 : Ideal.Quotient.mkₐ k (RingHom.ker φ.kerSquareLift) (g x) = e.symm x :=
      AlgHom.congr_fun hg x
    have h2 : e (Ideal.Quotient.mkₐ k (RingHom.ker φ.kerSquareLift) (g x)) =
        φ.kerSquareLift (g x) :=
      Ideal.quotientKerAlgEquivOfSurjective_mk hsurj' (g x)
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq]
    rw [← h2, h1, AlgEquiv.apply_symm_apply]
  obtain ⟨l, hl⟩ :=
    (retractionKerCotangentToTensorEquivSection (R := k) (P := R) (S := ResidueField R) hsurj).symm
      ⟨g, hsec⟩
  exact Function.LeftInverse.injective (g := l) fun x => LinearMap.congr_fun hl x

/-- The conormal sequence `𝔪/𝔪² → κ ⊗[R] Ω[R⁄k] → Ω[κ⁄k]` is exact in the middle
[Sta, Tag 00RU]. -/
theorem exact_kerCotangentToTensor_mapBaseChange_residueField :
    Function.Exact (kerCotangentToTensor k R (ResidueField R))
      (mapBaseChange k R (ResidueField R)) :=
  exact_kerCotangentToTensor_mapBaseChange k R (ResidueField R) residue_surjective

/-- The map `κ ⊗[R] Ω[R⁄k] → Ω[κ⁄k]` of the conormal sequence is surjective [Sta, Tag 00RU]. -/
theorem mapBaseChange_residueField_surjective :
    Function.Surjective (mapBaseChange k R (ResidueField R)) :=
  mapBaseChange_surjective k R (ResidueField R) residue_surjective

/-- The conormal map `d̄` as a `κ`-linear map on Mathlib's cotangent space `𝔪/𝔪²`: the domain of
`kerCotangentToTensor k R κ` is the cotangent module of `ker (R → κ) = 𝔪`. -/
noncomputable def cotangentSpaceToTensor :
    CotangentSpace R →ₗ[ResidueField R] ResidueField R ⊗[R] Ω[R⁄k] :=
  (kerCotangentToTensor k R (ResidueField R) ∘ₗ
    (Ideal.cotangentEquivOfEq
      (ker_algebraMap_residueField R).symm).toLinearMap).extendScalarsOfSurjective
      residue_surjective

theorem cotangentSpaceToTensor_apply (x : CotangentSpace R) :
    cotangentSpaceToTensor k R x =
      kerCotangentToTensor k R (ResidueField R)
        (Ideal.cotangentEquivOfEq (ker_algebraMap_residueField R).symm x) :=
  rfl

@[simp]
theorem cotangentSpaceToTensor_toCotangent (x : maximalIdeal R) :
    cotangentSpaceToTensor k R ((maximalIdeal R).toCotangent x) = 1 ⊗ₜ D k R x := by
  rw [cotangentSpaceToTensor_apply, Ideal.cotangentEquivOfEq_toCotangent,
    kerCotangentToTensor_toCotangent]

theorem injective_cotangentSpaceToTensor [Algebra.FormallySmooth k (ResidueField R)] :
    Function.Injective (cotangentSpaceToTensor k R) :=
  (injective_kerCotangentToTensor_residueField_of_formallySmooth k R).comp
    (LinearEquiv.injective _)

theorem exact_cotangentSpaceToTensor_mapBaseChange :
    Function.Exact (cotangentSpaceToTensor k R) (mapBaseChange k R (ResidueField R)) := by
  intro y
  rw [(exact_kerCotangentToTensor_mapBaseChange_residueField k R) y]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(Ideal.cotangentEquivOfEq (ker_algebraMap_residueField R).symm).symm x, ?_⟩
    rw [cotangentSpaceToTensor_apply, LinearEquiv.apply_symm_apply]
  · rintro ⟨x, rfl⟩
    exact ⟨_, (cotangentSpaceToTensor_apply k R x).symm⟩

/-- With `d̄` injective (`κ` formally smooth over `k`) the conormal sequence is short exact, so
`dim_κ κ ⊗[R] Ω[R⁄k] = dim_κ 𝔪/𝔪² + dim_κ Ω[κ⁄k]` for `R` essentially of finite type over `k`
(the first display in the proof of [Sta, Tag 00TV]). -/
theorem finrank_residueField_tensor_kaehlerDifferential [Algebra.EssFiniteType k R]
    [Algebra.FormallySmooth k (ResidueField R)] :
    Module.finrank (ResidueField R) (ResidueField R ⊗[R] Ω[R⁄k]) =
      Module.finrank (ResidueField R) (CotangentSpace R) +
        Module.finrank (ResidueField R) Ω[ResidueField R⁄k] := by
  rw [← LinearMap.finrank_range_add_finrank_ker (mapBaseChange k R (ResidueField R)),
    LinearMap.range_eq_top.mpr (mapBaseChange_residueField_surjective k R), finrank_top,
    add_comm, (exact_cotangentSpaceToTensor_mapBaseChange k R).linearMap_ker_eq,
    LinearMap.finrank_range_of_inj (injective_cotangentSpaceToTensor k R)]

end KaehlerDifferential
