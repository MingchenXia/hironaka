/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ClosureLocalScheme

/-!
# Generizations of a point of a nodal curve and the local structure

Let `g : Y → Spec R` be a nodal curve over an integrally closed domain `R`, `U ⊆ Y` an affine
open and `y ∈ U`. The primes of the local ring `A = Γ(U, 𝒪_Y)_y` are the generizations of `y`
(`locPt`, `locPt_locIdeal`, `locPt_injective`), its minimal primes are the generic points of `Y`
specializing to `y` (`mem_minimalPrimes_locIdeal`, `isGeneric_locPt`), and the image of such a
point in `Spec R` is read off from the contraction to `R` (`comap_locPt`). Through this
dictionary the algebraic local structure of lane T44E (`LocalStructure`,
`localStructure_of_isNodalCurve`, `isDomain_localization_of_isSmoothAt`) becomes a statement about
points:

* `eq_of_isSmoothAt`: **at most one generic point of `Y` specializes to a smooth point** (the
  local ring at a smooth point is a domain);
* `exists_node`: **a branch through a point of the closed fibre off the component of `z` gives a
  node of the generic fibre on the component of `z`**: if `R` is local, `y` lies over the closed
  point, `z` is a generic point of `Y` with `z ⤳ y` and `w ⤳ y` lies over the closed point but not
  on the closure of `z`, then some `n` over the generic point of `Spec R` with `z ⤳ n ⤳ y` lies on
  the closure of a second generic point `z₂ ≠ z`.

This is the point-level form of Temkin's implicit claim in the proof of Lemma 4.4.4 (M. Temkin,
*Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, T:3164–3166): blueprint
`sm-blow-down-closure-local.tex`, `lem:sm-bdcl-points`, `lem:sm-bdcl-smooth-unique`,
`lem:sm-bdcl-node`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing Topology

namespace DeJongAlterations.StableModification.BlowDown.ClosureLocal

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Points

variable {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U)

/-- **Specialization of points of an affine open is inclusion of their primes.** -/
theorem primeIdealOf_le_iff {x₁ x₂ : Y} (h₁ : x₁ ∈ U) (h₂ : x₂ ∈ U) :
    (hU.primeIdealOf ⟨x₁, h₁⟩).asIdeal ≤ (hU.primeIdealOf ⟨x₂, h₂⟩).asIdeal ↔ x₁ ⤳ x₂ := by
  have h := hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff
    (x := hU.primeIdealOf ⟨x₁, h₁⟩) (y := hU.primeIdealOf ⟨x₂, h₂⟩)
  rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h
  rw [h]
  exact PrimeSpectrum.le_iff_specializes _ _

/-- The points `fromSpec P` lie in `U`. -/
theorem fromSpec_mem (P : PrimeSpectrum Γ(Y, U)) : hU.fromSpec P ∈ U := by
  have h : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
  rwa [hU.range_fromSpec] at h

/-- The prime of the point `fromSpec P` is `P`. -/
theorem primeIdealOf_fromSpec (P : PrimeSpectrum Γ(Y, U)) (h : hU.fromSpec P ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec P, h⟩ = P :=
  hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)

variable {y : Y} (hyU : y ∈ U)

/-- The local ring `Γ(U, 𝒪_Y)_y` of `y`. -/
abbrev LocRing : Type u := Localization.AtPrime (hU.primeIdealOf ⟨y, hyU⟩).asIdeal

/-- The point of `Y` of a prime `n` of the local ring `Γ(U)_y` (a generization of `y`). -/
def locPt (n : Ideal (LocRing hU hyU)) (hn : n.IsPrime) : Y :=
  hU.fromSpec ⟨n.comap (algebraMap Γ(Y, U) (LocRing hU hyU)), Ideal.comap_isPrime _ _⟩

/-- The prime of `Γ(U)_y` of a point `x ∈ U`. -/
abbrev locIdeal {x : Y} (hxU : x ∈ U) : Ideal (LocRing hU hyU) :=
  (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.map (algebraMap Γ(Y, U) (LocRing hU hyU))

/-- The prime of a point `x ∈ U` misses the complement of the prime of `y` if `x ⤳ y`. -/
theorem disjoint_primeCompl {x : Y} (hxU : x ∈ U) (hxy : x ⤳ y) :
    Disjoint ((hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl : Set Γ(Y, U))
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
  rw [Set.disjoint_left]
  intro a ha ha'
  exact ha ((primeIdealOf_le_iff hU hxU hyU).mpr hxy ha')

/-- The prime of a generization `x` of `y` in `Γ(U)_y`. -/
theorem isPrime_locIdeal {x : Y} (hxU : x ∈ U) (hxy : x ⤳ y) :
    (locIdeal hU hyU hxU).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint _ _ _ (hU.primeIdealOf ⟨x, hxU⟩).isPrime
    (disjoint_primeCompl hU hyU hxU hxy)

/-- The contraction of the prime of a generization `x` of `y` is the prime of `x`. -/
theorem comap_locIdeal {x : Y} (hxU : x ∈ U) (hxy : x ⤳ y) :
    (locIdeal hU hyU hxU).comap (algebraMap Γ(Y, U) (LocRing hU hyU)) =
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
  IsLocalization.under_map_of_isPrime_disjoint _ _ (hU.primeIdealOf ⟨x, hxU⟩).isPrime
    (disjoint_primeCompl hU hyU hxU hxy)

/-- **The point of the prime of a generization `x` of `y` is `x`.** -/
theorem locPt_locIdeal {x : Y} (hxU : x ∈ U) (hxy : x ⤳ y) :
    locPt hU hyU (locIdeal hU hyU hxU) (isPrime_locIdeal hU hyU hxU hxy) = x := by
  have := isPrime_locIdeal hU hyU hxU hxy
  have h : (⟨(locIdeal hU hyU hxU).comap (algebraMap Γ(Y, U) (LocRing hU hyU)),
      Ideal.comap_isPrime _ _⟩ : PrimeSpectrum Γ(Y, U)) = hU.primeIdealOf ⟨x, hxU⟩ :=
    PrimeSpectrum.ext (comap_locIdeal hU hyU hxU hxy)
  rw [locPt, h, hU.fromSpec_primeIdealOf]

/-- The points of `U` are the points of their primes. -/
theorem locPt_mem (n : Ideal (LocRing hU hyU)) (hn : n.IsPrime) : locPt hU hyU n hn ∈ U :=
  fromSpec_mem hU _

/-- The prime of the point of a prime `n` of `Γ(U)_y` is the contraction of `n`. -/
theorem primeIdealOf_locPt (n : Ideal (LocRing hU hyU)) (hn : n.IsPrime) :
    (hU.primeIdealOf ⟨locPt hU hyU n hn, locPt_mem hU hyU n hn⟩).asIdeal =
      n.comap (algebraMap Γ(Y, U) (LocRing hU hyU)) :=
  congrArg PrimeSpectrum.asIdeal (primeIdealOf_fromSpec hU _ _)

/-- Inclusions of primes of `Γ(U)_y` are specializations of their points. -/
theorem locPt_specializes_locPt {n₁ n₂ : Ideal (LocRing hU hyU)} (hn₁ : n₁.IsPrime)
    (hn₂ : n₂.IsPrime) (h : n₁ ≤ n₂) : locPt hU hyU n₁ hn₁ ⤳ locPt hU hyU n₂ hn₂ := by
  refine Specializes.map ?_ hU.fromSpec.continuous
  exact (PrimeSpectrum.le_iff_specializes _ _).mp (Ideal.comap_mono h)

/-- **The points of the primes of `Γ(U)_y` are generizations of `y`.** -/
theorem locPt_specializes (n : Ideal (LocRing hU hyU)) (hn : n.IsPrime) :
    locPt hU hyU n hn ⤳ y := by
  have hle : n.comap (algebraMap Γ(Y, U) (LocRing hU hyU)) ≤
      (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    have h := Localization.AtPrime.under_maximalIdeal (I := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal)
    exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hn.ne_top)).trans h.le
  have := (primeIdealOf_le_iff hU (locPt_mem hU hyU n hn) hyU).mp
    (by rw [primeIdealOf_locPt]; exact hle)
  exact this

/-- **Distinct primes of `Γ(U)_y` have distinct points.** -/
theorem locPt_injective {n₁ n₂ : Ideal (LocRing hU hyU)} (hn₁ : n₁.IsPrime) (hn₂ : n₂.IsPrime)
    (h : locPt hU hyU n₁ hn₁ = locPt hU hyU n₂ hn₂) : n₁ = n₂ := by
  have h' := hU.fromSpec.isOpenEmbedding.injective h
  have hc : n₁.comap (algebraMap Γ(Y, U) (LocRing hU hyU)) =
      n₂.comap (algebraMap Γ(Y, U) (LocRing hU hyU)) := congrArg PrimeSpectrum.asIdeal h'
  rw [← IsLocalization.map_under (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
      (LocRing hU hyU) n₁,
    ← IsLocalization.map_under (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
      (LocRing hU hyU) n₂]
  exact congrArg (Ideal.map (algebraMap Γ(Y, U) (LocRing hU hyU))) hc

/-- **A generic point of `Y` specializing to `y` gives a minimal prime of `Γ(U)_y`.** -/
theorem mem_minimalPrimes_locIdeal {z : Y} (hzU : z ∈ U) (hzy : z ⤳ y)
    (hz : ∀ ξ, ξ ⤳ z → ξ = z) : locIdeal hU hyU hzU ∈ minimalPrimes (LocRing hU hyU) := by
  refine ⟨⟨isPrime_locIdeal hU hyU hzU hzy, bot_le⟩, fun P' hP' hle => ?_⟩
  have h := locPt_specializes_locPt hU hyU hP'.1 (isPrime_locIdeal hU hyU hzU hzy) hle
  rw [locPt_locIdeal hU hyU hzU hzy] at h
  have he := hz _ h
  rw [← locPt_locIdeal hU hyU hzU hzy] at he
  exact (locPt_injective hU hyU hP'.1 _ he).symm.le

/-- **The point of a minimal prime of `Γ(U)_y` is a generic point of `Y`.** -/
theorem isGeneric_locPt {P : Ideal (LocRing hU hyU)} (hP : P ∈ minimalPrimes (LocRing hU hyU)) :
    ∀ ξ, ξ ⤳ locPt hU hyU P hP.1.1 → ξ = locPt hU hyU P hP.1.1 := by
  intro ξ hξ
  have hξy : ξ ⤳ y := hξ.trans (locPt_specializes hU hyU P hP.1.1)
  have hξU : ξ ∈ U := hξy.mem_open U.2 hyU
  have hQ := isPrime_locIdeal hU hyU hξU hξy
  have hle : locIdeal hU hyU hξU ≤ P := by
    rw [← IsLocalization.map_under (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
      (LocRing hU hyU) P]
    refine Ideal.map_mono ?_
    have h := (primeIdealOf_le_iff hU hξU (locPt_mem hU hyU P hP.1.1)).mpr hξ
    rw [primeIdealOf_locPt hU hyU P hP.1.1] at h
    exact h
  have heq : locIdeal hU hyU hξU = P := le_antisymm hle (hP.2 ⟨hQ, bot_le⟩ hle)
  rw [← locPt_locIdeal hU hyU hξU hξy]
  congr 1

end Points

section Base

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R))
  {U : Y.Opens} (hU : IsAffineOpen U) {y : Y} (hyU : y ∈ U)

/-- **The image in `Spec R` of the point of a prime `n` of `Γ(U)_y`** is the contraction of `n`
to `R`. -/
theorem comap_locPt (n : Ideal (LocRing hU hyU)) (hn : n.IsPrime) :
    letI := sectionsAlgebra g U
    (g (locPt hU hyU n hn)).asIdeal = n.comap (algebraMap R (LocRing hU hyU)) := by
  let := sectionsAlgebra g U
  rw [← comap_primeIdealOf g hU _ (locPt_mem hU hyU n hn), primeIdealOf_locPt, Ideal.comap_comap,
    ← IsScalarTower.algebraMap_eq]

end Base

section Nodal

variable {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {Y : Scheme.{u}}
  (g : Y ⟶ Spec (CommRingCat.of R)) [DeJong.IsNodalCurve g]

/-- **At most one generic point of a nodal curve specializes to a smooth point** (the local ring
at a smooth point is a domain, `isDomain_localization_of_isSmoothAt`; blueprint
`lem:sm-bdcl-smooth-unique`). -/
theorem eq_of_isSmoothAt {y : Y} (hsm : DeJong.IsSmoothAt g y) {η₁ η₂ : Y}
    (h₁ : ∀ ξ, ξ ⤳ η₁ → ξ = η₁) (h₂ : ∀ ξ, ξ ⤳ η₂ → ξ = η₂) (hη₁ : η₁ ⤳ y)
    (hη₂ : η₂ ⤳ y) : η₁ = η₂ := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  let := sectionsAlgebra g U
  have hdom : IsDomain (LocRing hU hyU) := isDomain_localization_of_isSmoothAt g hU y hyU hsm
  have hbot : (⊥ : Ideal (LocRing hU hyU)).IsPrime := Ideal.isPrime_bot
  have key : ∀ η : Y, (∀ ξ, ξ ⤳ η → ξ = η) → η ⤳ y → η = locPt hU hyU ⊥ hbot := by
    intro η hη hηy
    have hηU : η ∈ U := hηy.mem_open U.2 hyU
    have h := locPt_specializes_locPt hU hyU hbot (isPrime_locIdeal hU hyU hηU hηy) bot_le
    rw [locPt_locIdeal hU hyU hηU hηy] at h
    exact (hη _ h).symm
  rw [key η₁ h₁ hη₁, key η₂ h₂ hη₂]

/-- **A branch off a component gives a node of the generic fibre** (blueprint `lem:sm-bdcl-node`,
from `LocalStructure.node`): over an integrally closed local domain `R`, let `y` lie over the
closed point, `z` be a generic point of `Y` with `z ⤳ y`, and `w ⤳ y` lie over the closed point
with `z ⤳̸ w`. Then there are `n` over the generic point of `Spec R` with `z ⤳ n ⤳ y` and a second
generic point `z₂ ≠ z` of `Y` with `z₂ ⤳ n`. -/
theorem exists_node [IsLocalRing R] {y z w : Y} (hy : (g y).asIdeal = maximalIdeal R)
    (hz : ∀ ξ, ξ ⤳ z → ξ = z) (hzy : z ⤳ y) (hw : maximalIdeal R ≤ (g w).asIdeal)
    (hwy : w ⤳ y) (hzw : ¬ z ⤳ w) :
    ∃ n : Y, z ⤳ n ∧ n ⤳ y ∧ (g n).asIdeal = ⊥ ∧
      ∃ z₂ : Y, (∀ ξ, ξ ⤳ z₂ → ξ = z₂) ∧ z₂ ≠ z ∧ z₂ ⤳ n := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  let := sectionsAlgebra g U
  have hLS := localStructure_of_isNodalCurve g hU y hyU hy
  have hzU : z ∈ U := hzy.mem_open U.2 hyU
  have hwU : w ∈ U := hwy.mem_open U.2 hyU
  have hPz := isPrime_locIdeal hU hyU hzU hzy
  have hPw := isPrime_locIdeal hU hyU hwU hwy
  have hmin := mem_minimalPrimes_locIdeal hU hyU hzU hzy hz
  have h𝔭w : (maximalIdeal R).map (algebraMap R (LocRing hU hyU)) ≤ locIdeal hU hyU hwU := by
    rw [IsScalarTower.algebraMap_eq R Γ(Y, U) (LocRing hU hyU), ← Ideal.map_map]
    refine Ideal.map_mono ?_
    rw [Ideal.map_le_iff_le_comap, comap_primeIdealOf g hU w hwU]
    exact hw
  have hPw' : ¬ locIdeal hU hyU hzU ≤ locIdeal hU hyU hwU := by
    intro hle
    have h := locPt_specializes_locPt hU hyU hPz hPw hle
    rw [locPt_locIdeal hU hyU hzU hzy, locPt_locIdeal hU hyU hwU hwy] at h
    exact hzw h
  obtain ⟨n, hn, hPn, hnR, -, P₂, hP₂, hP₂P, hP₂n⟩ := hLS.node _ hmin _ hPw h𝔭w hPw'
  refine ⟨locPt hU hyU n hn, ?_, locPt_specializes hU hyU n hn, ?_, locPt hU hyU P₂ hP₂.1.1,
    isGeneric_locPt hU hyU hP₂, ?_, locPt_specializes_locPt hU hyU hP₂.1.1 hn hP₂n⟩
  · have h := locPt_specializes_locPt hU hyU hPz hn hPn
    rwa [locPt_locIdeal hU hyU hzU hzy] at h
  · rw [comap_locPt g hU hyU n hn]
    exact hnR
  · intro heq
    apply hP₂P
    apply locPt_injective hU hyU hP₂.1.1 hPz
    rw [heq, locPt_locIdeal hU hyU hzU hzy]

end Nodal

end DeJongAlterations.StableModification.BlowDown.ClosureLocal
