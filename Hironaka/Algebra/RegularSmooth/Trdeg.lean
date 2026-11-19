/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.Etale.Field

/-!
# The rank of the Kähler differentials of a separably generated field extension

The proof of [Sta, Tag 00TV] uses, as known, that `dim_κ Ω[κ⁄k] = trdeg_k κ` for a finitely
generated separable extension `κ/k`; "separable" means separably generated [Sta, Tags 030O, 030W]:
there is a transcendence basis `s` with `κ` separable algebraic over `k(s)`. The argument: `k(s)`
is the fraction field of `k[s] ≅ k[x_i]_{i ∈ s}`, so `Ω[k(s)⁄k]` is free on the `d x_i`
([Sta, Tags 00RX, 00RT], through Mathlib's `mvPolynomialBasis`, the formally étale base change
along the isomorphism `k[x] ≅ k[s]`, and `Basis.ofIsLocalizedModule`); `κ/k(s)` is separable
algebraic, hence formally étale, so `Ω[κ⁄k] ≅ κ ⊗_{k(s)} Ω[k(s)⁄k]` (Mathlib's
`tensorKaehlerEquivOfFormallyEtale`) is free of rank `|s| = trdeg_k κ` (Mathlib's
`cardinalMk_eq_trdeg`). Over a perfect field every finitely generated extension has a separating
transcendence basis (Mathlib's `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`), and
for a separable algebraic extension, such as the residue field of a closed point, `Ω[κ⁄k] = 0`,
`κ` being formally unramified over `k`. These are the ingredients of the dimension formula
`dim S_𝔮 + trdeg_k κ(𝔮) = n` for a smooth algebra in
`Hironaka/Algebra/RegularSmooth/Dimension.lean`.
-/

public section

universe u

open KaehlerDifferential
open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin

namespace Algebra

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- For a field extension `K/k` with a separating transcendence basis `s` (`K` separable over
`k(s)`), the rank of `Ω[K⁄k]` is the transcendence degree of `K/k` (used in [Sta, Tag 00TV]). -/
theorem rank_kaehlerDifferential_eq_trdeg_of_isSeparable {s : Set K}
    (hs : IsTranscendenceBasis k ((↑) : s → K))
    [Algebra.IsSeparable (IntermediateField.adjoin k s) K] :
    Module.rank K Ω[K⁄k] = Algebra.trdeg k K := by
  classical
  set A := Algebra.adjoin k s with hA
  set F := IntermediateField.adjoin k s with hF
  -- the polynomial ring `k[x_i]` is isomorphic to `A = k[s]`
  have hrange : Algebra.adjoin k (Set.range ((↑) : s → K)) = A := by rw [Subtype.range_coe]
  let e : MvPolynomial s k ≃ₐ[k] A := hs.1.aevalEquiv.trans (Subalgebra.equivOfEq _ _ hrange)
  let : Algebra (MvPolynomial s k) A := e.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial s k) A :=
    IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  have : IsLocalization (⊥ : Submonoid (MvPolynomial s k)) (MvPolynomial s k) :=
    IsLocalization.of_le_isUnit bot_le
  have : IsLocalization (⊥ : Submonoid (MvPolynomial s k)) A :=
    IsLocalization.isLocalization_of_algEquiv (⊥ : Submonoid (MvPolynomial s k))
      (AlgEquiv.ofBijective (Algebra.ofId (MvPolynomial s k) A) e.bijective)
  have : Algebra.FormallyEtale (MvPolynomial s k) A :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := A) ⊥
  -- a basis of `Ω[A⁄k]`, then of `Ω[F⁄k]` (`F` is the fraction field of `A`), then of `Ω[K⁄k]`
  let bA : Module.Basis s A Ω[A⁄k] :=
    ((mvPolynomialBasis k s).baseChange A).map
      (tensorKaehlerEquivOfFormallyEtale k (MvPolynomial s k) A)
  let bF : Module.Basis s F Ω[F⁄k] :=
    bA.ofIsLocalizedModule F (nonZeroDivisors A) (map k k A F)
  have : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  let bK : Module.Basis s K Ω[K⁄k] :=
    (bF.baseChange K).map (tensorKaehlerEquivOfFormallyEtale k F K)
  rw [← bK.mk_eq_rank'', hs.cardinalMk_eq_trdeg]

/-- For `k` perfect and `K/k` finitely generated (essentially of finite type),
`rank_K Ω[K⁄k] = trdeg_k K`: every such extension has a separating transcendence basis. -/
theorem rank_kaehlerDifferential_eq_trdeg_of_perfectField [PerfectField k]
    [Algebra.EssFiniteType k K] :
    Module.rank K Ω[K⁄k] = Algebra.trdeg k K := by
  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  exact rank_kaehlerDifferential_eq_trdeg_of_isSeparable k K (s := (s : Set K)) hs

/-- For `K/k` separable algebraic, `Ω[K⁄k] = 0`: `K` is formally unramified over `k`. -/
theorem subsingleton_kaehlerDifferential_of_isSeparable [Algebra.IsSeparable k K] :
    Subsingleton Ω[K⁄k] :=
  have := Algebra.FormallyUnramified.of_isSeparable k K
  inferInstance

end Algebra
