/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.RegularSmooth.Stalk
public import Hironaka.Algebra.RegularSmooth.Defs
import Hironaka.Algebra.RegularSmooth.Dimension
import Hironaka.Algebra.RegularSmooth.Regular
import Hironaka.Algebra.RegularSmooth.SmoothImpliesRegular

/-!
# Scheme forms of "smooth implies regular" and of the dimension of a smooth stalk

The affine reduction of `Hironaka/Algebra/RegularSmooth/SmoothAt.lean` and `Regular.lean` turns the
ring statements of this directory into statements about a scheme `X` locally of finite type over a
field `k`, `f : X ⟶ Spec k`. *Regularity* (the last sentence of [Sta, Tag 00TT]): a point `x` of
the smooth locus of `f` is a regular point, because on an affine open `U ∋ x` with prime `𝔮` of
`x`, `x ∈ f.smoothLocus` means `Γ(X, U)` is smooth at `𝔮` over `k`
(`mem_smoothLocus_iff_isSmoothAt`), `Γ(X, U)` is of finite type over `k`, so `Γ(X, U)_𝔮` is
regular (`SmoothImpliesRegular.lean`), and `Γ(X, U)_𝔮 ≅ 𝒪_{X,x}`
(`isRegularAt_iff_isRegularLocalRing_localization`). *Dimension* ([Sta, Tag 0A21, (10)]): if `f`
is smooth of relative dimension `n`, every `x` has an affine open `V ∋ x` on which `Γ(X, V)` is
standard smooth of relative dimension `n` over `k` (Mathlib's `SmoothOfRelativeDimension`, with
`Spec k` a single point so the affine open of the target is `⊤`, and the base ring `Γ(Spec k, ⊤)`
replaced by `k` along `Scheme.ΓSpecIso`); the stalk `𝒪_{X,x} ≅ Γ(X, V)_𝔮` as `k`-algebras
(`Scheme.Hom.stalkAlgebra`, the scalar tower of `Stalk.lean`), so `dim 𝒪_{X,x} + trdeg_k κ(x) = n`
and, at a closed point (where `𝔮` is maximal), `dim 𝒪_{X,x} = n` follow from the affine statements
of `Dimension.lean`. The closed-point form gives the dimension of the local rings of a smooth
variety, used for étale coordinates and normal crossings (`Hironaka/Smooth/`, `Hironaka/Snc/`).
-/

public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- For `X` locally of finite type over a field `k`, a point of the smooth locus of `X → Spec k` is
a regular point (the last sentence of [Sta, Tag 00TT]). -/
theorem Scheme.isRegularAt_of_mem_smoothLocus (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    {x : X} (hx : x ∈ f.smoothLocus) : X.IsRegularAt x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := f.sectionsAlgebra U
  have : Algebra.FiniteType k Γ(X, U) := f.finiteType_sectionsAlgebra hU
  have : Algebra.IsSmoothAt k (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    (f.mem_smoothLocus_iff_isSmoothAt hU hxU).mp hx
  rw [Scheme.isRegularAt_iff_isRegularLocalRing_localization hU hxU]
  exact Algebra.IsSmoothAt.isRegularLocalRing (k := k) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal

/-- For `f : X ⟶ Spec k` smooth of relative dimension `n`, every point has an affine open
neighbourhood `V` on which `Γ(X, V)` is standard smooth of relative dimension `n` over `k`
(Mathlib's `SmoothOfRelativeDimension`, with the affine open of `Spec k` necessarily `⊤` and the
base ring `Γ(Spec k, ⊤)` replaced by `k` along `Scheme.ΓSpecIso`). -/
theorem Scheme.Hom.exists_affineOpen_isStandardSmoothOfRelativeDimension (f : X ⟶ Spec (.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V),
      letI := f.sectionsAlgebra V
      Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, V) := by
  obtain ⟨U', hU', V, hV, hxV, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  have hU'top : U' = ⊤ := by
    apply TopologicalSpace.Opens.ext
    apply Set.eq_univ_of_forall
    intro y
    rw [Subsingleton.elim (α := PrimeSpectrum k) y (f x)]
    exact e hxV
  subst hU'top
  refine ⟨V, hV, hxV, ?_⟩
  let := f.sectionsAlgebra V
  have := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).2
    (f.appLE ⊤ V e).hom (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv hstd
  exact this

/-- The scheme form of [Sta, Tag 0A21, (10)]: for `k` perfect and `f : X ⟶ Spec k` smooth of
relative dimension `n`, at every point `x`, with `κ(x)` the residue field of the stalk as a
`k`-algebra through `f`, `dim 𝒪_{X,x} + trdeg_k κ(x) = n`. -/
theorem Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension
    [PerfectField k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    letI := f.stalkAlgebra x
    ringKrullDim (X.presheaf.stalk x) +
      ((Cardinal.toENat (Algebra.trdeg k (ResidueField (X.presheaf.stalk x))) : ℕ∞) :
        WithBot ℕ∞) = n := by
  let := f.stalkAlgebra x
  obtain ⟨V, hV, hxV, hstd⟩ := f.exists_affineOpen_isStandardSmoothOfRelativeDimension n x
  let := f.sectionsAlgebra V
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  have := f.isScalarTower_sectionsAlgebra_stalk V hxV
  set 𝔮 := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let e : Localization.AtPrime 𝔮 ≃ₐ[k] X.presheaf.stalk x :=
    (IsLocalization.algEquiv 𝔮.primeCompl (Localization.AtPrime 𝔮)
      (X.presheaf.stalk x)).restrictScalars k
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv,
    ← (IsLocalRing.ResidueField.mapAlgEquiv e).trdeg_eq]
  exact Algebra.IsStandardSmoothOfRelativeDimension.ringKrullDim_localization_add_trdeg_residueField
    (k := k) n 𝔮

/-- For `k` perfect and `f : X ⟶ Spec k` smooth of relative dimension `n`, the stalk at a closed
point has dimension `n` (its residue field is finite over `k` by Zariski's lemma). -/
theorem Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed [PerfectField k]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] {x : X}
    (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = n := by
  obtain ⟨V, hV, hxV, hstd⟩ := f.exists_affineOpen_isStandardSmoothOfRelativeDimension n x
  let := f.sectionsAlgebra V
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  set 𝔮 := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : 𝔮.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  rw [← ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv 𝔮.primeCompl
    (Localization.AtPrime 𝔮) (X.presheaf.stalk x)).toRingEquiv]
  exact Algebra.IsStandardSmoothOfRelativeDimension.ringKrullDim_localization_of_isMaximal
    (k := k) n 𝔮

end AlgebraicGeometry
