/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Order
public import Hironaka.Scheme.BlowUp.Transform
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Algebra.Local.Chart
import Hironaka.Algebra.Local.ChartFibre
import Hironaka.Algebra.Local.ChartGenericFibre
import Hironaka.Algebra.Local.PolynomialOrder
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.TransformOrder
import Hironaka.Scheme.BlowUp.Composite.Transition
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUp.Transform.WeakTransform
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Derivative.Sheaf
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Exceptional
import Hironaka.Scheme.IdealSheaf.Order.Lemma61
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Smooth.ChartRing
import Hironaka.Scheme.Smooth.LocalBlowUp
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# The order of an ideal along a smooth center of any shape

The divisibility `F^m ∣ π^* I`, the exceptional order of `π^* I` and Kollár's Lemma 61 are proved
elsewhere in this library for an integral center `Z` of pure codimension, working at *the* generic
point of `Z` (`Hironaka/Scheme/IdealSheaf/Order/Lemma61.lean`,
`Hironaka/Scheme/IdealSheaf/Order/ExceptionalOrder.lean`). A center of [Kol07, Definition 66] may
have several components; this module runs the same arguments at the generic point of the component
through each point of the center, for a center that is merely smooth. The order of an ideal along a
reducible `Z` is understood at every generic point of `Z`, as in [Kol07, Definition 47].

**The component through a point.** At `z ∈ Z` the stalk `Z_z` is prime (`𝒪_{X,z}/Z_z ≅ 𝒪_{Z,z}` is
regular, so a domain). On an affine `U ∋ z` the prime `p = Z_z ∩ Γ(U)` has a point `η ∈ U`; `η` lies
in `Z`, specializes to `z`, and is a generic point of `Z` (no proper generization inside `Z`: a
prime `q ⊆ p` containing `Z(U)` becomes `Z_z` in `𝒪_{X,z}`, so `q = p`). The stalk `𝒪_{X,η}` is the
localization of `𝒪_{X,z}` at `Z_z`, whence `ord_{Z_z} I_z = ord_η I` and `Z_η = 𝔪_η`
(`exists_genericPoint_of_isPrime_stalkIdeal`). Every generic point of `Z` in the sense of
`Closeds.genericPoints` arises this way from any point of its component.

The main results are `weakTransform_eq_markedTransform_of_smooth` (the birational transform of
[Kol07, 58] is the marked transform of [Kol07, Definition 60] when `ord_Z I = m` along every
component of `Z`) and `maxOrd_controlledTransform_le_of_smooth` ([Kol07, Lemma 61] for a smooth
center of any shape). They enter the transforms of triples and Remark 67
(`Hironaka/Scheme/BlowUpSequence/Triple.lean`, `Remark67.lean`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing Ideal
  Scheme.IdealSheafData Scheme.BlowUpSequence AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

open Hironaka

variable {X : Scheme.{u}}

/-! ### The generic point of the component of the center through a point -/

/-- For `z ∈ Z` with `Z_z` prime: the generic point `η` of the component of `Z` through `z` (the
point of the prime `Z_z ∩ Γ(U)` of an affine `U ∋ z`) is a generic point of `Z`, specializes to
`z`, has `Z_η = 𝔪_η`, and `ord_{Z_z} I_z = ord_η I` for every `I`: the order along a center
[Kol07, Definition 47] read at the component through `z`. Not in the sources; the point-set
topology behind the arguments below. -/
theorem exists_genericPoint_of_isPrime_stalkIdeal (Z : X.IdealSheafData) (z : X)
    [hP : (Z.stalkIdeal z).IsPrime] [IsDomain (X.presheaf.stalk z)] :
    ∃ η : X, η ∈ Z.support.genericPoints ∧ η ⤳ z ∧
      Z.stalkIdeal η = maximalIdeal (X.presheaf.stalk η) ∧
      (Z.stalkIdeal z ≠ ⊥ → Z.stalkIdeal η ≠ ⊥) ∧
      ∀ I : X.IdealSheafData, IsLocalRing.ordAlong (Z.stalkIdeal z) (I.stalkIdeal z) =
        IsLocalRing.ord (I.stalkIdeal η) := by
  classical
  obtain ⟨U, hzU⟩ := exists_affineOpens_mem z
  have hU : IsAffineOpen U.1 := U.2
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hzU⟩ : U.1)
  have hloc_z := hU.isLocalization_stalk ⟨z, hzU⟩
  set P := Z.stalkIdeal z with hPdef
  have hPmap : P = (Z.ideal U).map (algebraMap Γ(X, U) (X.presheaf.stalk z)) :=
    stalkIdeal_eq_map_germ Z U hzU
  -- the prime `p = Z_z ∩ Γ(U)` and its point `η`
  set p : Ideal Γ(X, U) := P.comap (algebraMap Γ(X, U) (X.presheaf.stalk z)) with hpdef
  have hp : p.IsPrime := Ideal.IsPrime.comap _
  have hZp : Z.ideal U ≤ p := fun a ha => by
    change algebraMap Γ(X, U) (X.presheaf.stalk z) a ∈ P
    rw [hPmap]
    exact Ideal.mem_map_of_mem _ ha
  have hpz : p ≤ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    intro a ha
    by_contra hna
    have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk z) a) :=
      IsLocalization.map_units (X.presheaf.stalk z)
        (⟨a, hna⟩ : (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl)
    exact (IsLocalRing.mem_maximalIdeal _).mp (IsLocalRing.le_maximalIdeal hP.ne_top ha) hu
  have hpmap : p.map (algebraMap Γ(X, U) (X.presheaf.stalk z)) = P :=
    le_antisymm Ideal.map_comap_le (by rw [hPmap]; exact Ideal.map_mono hZp)
  let y : PrimeSpectrum Γ(X, U) := ⟨p, hp⟩
  have hyU : hU.fromSpec y ∈ (U.1 : Set X) := by
    rw [← hU.range_fromSpec]
    exact ⟨y, rfl⟩
  have hpid : hU.primeIdealOf ⟨hU.fromSpec y, hyU⟩ = y :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨hU.fromSpec y, hyU⟩)
  have hyZ : hU.fromSpec y ∈ Z.support :=
    (mem_support_iff_of_mem hyU).mpr ((mem_zeroLocus_iff_le_primeIdealOf U hyU _).mpr
      (by rw [hpid]; exact hZp))
  have hyz : hU.fromSpec y ⤳ z := by
    have h := ((PrimeSpectrum.le_iff_specializes y (hU.primeIdealOf ⟨z, hzU⟩)).mp hpz).map
      hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf] at h
  -- `η` is a generic point of `Z`: a generization `ξ ∈ Z` of `η` is `η`
  have hgen : hU.fromSpec y ∈ Z.support.genericPoints := by
    refine ⟨hyZ, fun ξ hξZ hξ => ?_⟩
    have hξU : ξ ∈ (U.1 : Set X) := hξ.mem_open U.1.2 hyU
    set q := hU.primeIdealOf ⟨ξ, hξU⟩ with hqdef
    have hqp : q ≤ y := by
      rw [PrimeSpectrum.le_iff_specializes]
      have h1 : hU.fromSpec q ⤳ hU.fromSpec y := by
        rw [hqdef, hU.fromSpec_primeIdealOf]
        exact hξ
      exact hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp h1
    have hZq : Z.ideal U ≤ q.asIdeal :=
      (mem_zeroLocus_iff_le_primeIdealOf U hξU _).mp ((mem_support_iff_of_mem hξU).mp hξZ)
    have hqmap : q.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk z)) = P :=
      le_antisymm (hpmap ▸ Ideal.map_mono hqp) (by rw [hPmap]; exact Ideal.map_mono hZq)
    have hdisj : Disjoint ((hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl : Set Γ(X, U))
        (q.asIdeal : Set Γ(X, U)) :=
      Set.disjoint_left.mpr fun a ha haq => ha (hpz (hqp haq))
    have hq : q.asIdeal = p := by
      rw [hpdef, ← hqmap]
      exact (IsLocalization.under_map_of_isPrime_disjoint _ (X.presheaf.stalk z) q.isPrime
        hdisj).symm
    have hqy : q = y := PrimeSpectrum.ext hq
    exact (hU.fromSpec_primeIdealOf ⟨ξ, hξU⟩).symm.trans (congrArg (fun t => hU.fromSpec t) hqy)
  -- the stalk at `η` is the localization of `Γ(U)` at `p`
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hU.fromSpec y, hyU⟩ : U.1)
  have hloc_η : IsLocalization p.primeCompl (X.presheaf.stalk (hU.fromSpec y)) :=
    hU.isLocalization_stalk' y hyU
  -- `Z_η = 𝔪_η`
  have hZη : Z.stalkIdeal (hU.fromSpec y) = maximalIdeal (X.presheaf.stalk (hU.fromSpec y)) := by
    rw [stalkIdeal_eq_map_germ Z U hyU, ← IsLocalization.AtPrime.map_eq_maximalIdeal (p := p)]
    refine le_antisymm (Ideal.map_mono hZp) ?_
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change algebraMap Γ(X, U) (X.presheaf.stalk z) a ∈ P at ha
    rw [hPmap, IsLocalization.mem_map_algebraMap_iff (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl]
      at ha
    obtain ⟨⟨i, s⟩, hs⟩ := ha
    rw [← map_mul, IsLocalization.eq_iff_exists (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl] at hs
    obtain ⟨t, ht⟩ := hs
    have hts : (t : Γ(X, U)) * s ∈ p.primeCompl := by
      intro hmem
      exact (hU.primeIdealOf ⟨z, hzU⟩).isPrime.mul_mem_iff_mem_or_mem.mp (hpz hmem) |>.elim t.2 s.2
    have hunit : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) ((t : Γ(X, U)) * s))
      :=
      IsLocalization.map_units _ (⟨_, hts⟩ : p.primeCompl)
    change algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) a ∈
      (Z.ideal U).map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)))
    have hmem : algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) ((t : Γ(X, U)) * s * a) ∈
        (Z.ideal U).map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) := by
      have : (t : Γ(X, U)) * s * a = t * i := by
        rw [mul_assoc, mul_comm (s : Γ(X, U)) a]
        exact ht
      rw [this, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ i.2)
    rw [map_mul] at hmem
    exact (Ideal.unit_mul_mem_iff_mem _ hunit).mp hmem
  -- `Z_z ≠ 0` forces `Z_η ≠ 0`: a section of `Z(U)` killed in `𝒪_{X,η}` is killed by some `t ∉ p`,
  -- and `𝒪_{X,z}` is a domain in which `t` is nonzero
  have hne : Z.stalkIdeal z ≠ ⊥ → Z.stalkIdeal (hU.fromSpec y) ≠ ⊥ := by
    intro hZz h0
    rw [stalkIdeal_eq_map_germ Z U hyU, Ideal.map_eq_bot_iff_le_ker] at h0
    apply hZz
    change P = ⊥
    rw [hPmap, Ideal.map_eq_bot_iff_le_ker]
    intro a ha
    have h1 : algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) a = 0 := h0 ha
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ a).mp h1
    have h2 : algebraMap Γ(X, U) (X.presheaf.stalk z) ((t : Γ(X, U)) * a) = 0 := by
      rw [ht, map_zero]
    rw [map_mul] at h2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exfalso
      apply t.2
      change algebraMap Γ(X, U) (X.presheaf.stalk z) t ∈ P
      rw [h3]
      exact zero_mem _
    · exact h3
  refine ⟨hU.fromSpec y, hgen, hyz, hZη, hne, fun I => ?_⟩
  -- the two orders (the argument for an integral center, with `p` in place of `Z(U)`)
  have hT : IsLocalization p.primeCompl (Localization.AtPrime P) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl (Localization.AtPrime P) P
  let e := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime P)
    (X.presheaf.stalk (hU.fromSpec y))
  unfold IsLocalRing.ordAlong
  have hI : I.stalkIdeal z = (I.ideal U).map (algebraMap Γ(X, U) (X.presheaf.stalk z)) :=
    stalkIdeal_eq_map_germ I U hzU
  have hIη : I.stalkIdeal (hU.fromSpec y) =
      (I.ideal U).map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) :=
    stalkIdeal_eq_map_germ I U hyU
  rw [hI, Ideal.map_map, hIη, ← ord_map_ringEquiv e.toRingEquiv, Ideal.map_map]
  congr 2
  refine RingHom.ext fun a => ?_
  change e ((algebraMap (X.presheaf.stalk z) (Localization.AtPrime P))
    ((algebraMap Γ(X, U) (X.presheaf.stalk z)) a)) = _
  rw [← IsScalarTower.algebraMap_apply]
  exact e.commutes a

/-! ### A smooth center: containment in the powers of the center, the exceptional order, Lemma 61 -/

section SmoothCenterOrder

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)]
  (I : X.IdealSheafData)

include f n

omit [CharZero k] in
/-- The stalk of a smooth center at a point of the center is prime (`𝒪_{X,z}/Z_z` is regular). -/
theorem isPrime_stalkIdeal_of_smooth {z : X} (hz : z ∈ Z.support) : (Z.stalkIdeal z).IsPrime := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have := isRegularLocalRing_quotient_stalkIdeal Z f hz
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

omit [CharZero k] n in
/-- Under a point of the blow-up the center's stalk is nonzero (it contains a member of a regular
system of parameters). -/
theorem stalkIdeal_ne_bot_of_mem_support_of_smooth [Smooth f] (q : Z.blowUp)
    (hq : Z.blowUpπ q ∈ Z.support) : Z.stalkIdeal (Z.blowUpπ q) ≠ ⊥ := by
  obtain ⟨n', y, ρ, hn', hy, hZ', -⟩ := exists_stalk_equiv_localization_chart_of_smooth f Z q hq
  have := isRegularLocalRing_stalk f (Z.blowUpπ q)
  intro h0
  apply x_ne_zero_of_span_eq y hy hn' ρ
  have hmem : y ρ ∈ chartCenter y ρ := Ideal.subset_span ⟨ρ, show ρ ≤ ρ from le_rfl, rfl⟩
  rw [← hZ', h0] at hmem
  exact (Submodule.mem_bot _).mp hmem

/-- Stalkwise, for a smooth center of any shape: if `ord_Z I ≥ m` along every component and
`Z_z ≠ 0`, then `I_z ⊆ Z_z^m`; the order along `Z_z` is the order at the generic point of the
component through `z`, and for a prime generated by part of a regular system of parameters an
ideal of order `≥ m` along it lies in its `m`-th power. -/
theorem stalkIdeal_le_pow_of_leOrdAlong {m : ℕ} (hm : I.LeOrdAlong Z.support (m : ℕ∞)) {z : X}
    (hz : z ∈ Z.support) (hZz : Z.stalkIdeal z ≠ ⊥) : I.stalkIdeal z ≤ Z.stalkIdeal z ^ m := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hreg := isRegularLocalRing_stalk f z
  have hP : (Z.stalkIdeal z).IsPrime := isPrime_stalkIdeal_of_smooth f n Z hz
  obtain ⟨η, hη, -, -, -, hord⟩ := exists_genericPoint_of_isPrime_stalkIdeal Z z
  have h1 : (m : ℕ∞) ≤ IsLocalRing.ordAlong (Z.stalkIdeal z) (I.stalkIdeal z) := by
    rw [hord I, ← ord_eq_ord_stalkIdeal]
    exact hm η hη
  let := f.stalkAlgebraRat z
  obtain ⟨m', c, y, hcm, hm', hy, hZ⟩ := exists_adaptedParameters_of_smooth f Z hz
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso
      apply hZz
      have hemp : {j : Fin m' | j.val < c} = ∅ := by
        ext j
        simp [h0]
      rw [hZ, hemp, Set.image_empty, Ideal.span_empty]
    · exact h0
  have hm'0 : 0 < m' := lt_of_lt_of_le hc0 hcm
  let ρ : Fin m' := ⟨min (c - 1) (m' - 1), by omega⟩
  have hset : {j : Fin m' | j.val < c} = {j | j ≤ ρ} := by
    ext j
    change j.val < c ↔ j ≤ ρ
    rw [Fin.le_def]
    change j.val < c ↔ j.val ≤ min (c - 1) (m' - 1)
    have := j.2
    omega
  have hZ' : Z.stalkIdeal z = chartCenter y ρ := by
    rw [hZ, hset]
    rfl
  exact le_pow_of_le_ordAlong_of_eq_chartCenter y hy hm' ρ (Z.stalkIdeal z) hZ'
    (I.stalkIdeal z) m h1

/-- On the blow-up of a smooth center of any shape: `π^* I ⊆ F^m` when `ord_Z I ≥ m` along every
component; at points over the center by `stalkIdeal_le_pow_of_leOrdAlong`, off it trivially. -/
theorem comap_le_pow_comap_of_leOrdAlong {m : ℕ} (hm : I.LeOrdAlong Z.support (m : ℕ∞)) :
    I.comap Z.blowUpπ ≤ (Z.comap Z.blowUpπ) ^ m := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  refine le_of_stalkIdeal_le fun q => ?_
  rw [stalkIdeal_pow, stalkIdeal_comap, stalkIdeal_comap, ← Ideal.map_pow]
  by_cases hq : Z.blowUpπ q ∈ Z.support
  · exact Ideal.map_mono (stalkIdeal_le_pow_of_leOrdAlong f n Z I hm hq
      (stalkIdeal_ne_bot_of_mem_support_of_smooth f Z q hq))
  · rw [stalkIdeal_eq_top_of_notMem_support Z hq, Ideal.top_pow, Ideal.map_top]
    exact le_top

/-- `F^m ∣ π^* I` when `ord_Z I ≥ m` along every component of a smooth center: "the number
`ord_Z I` equals the multiplicity of `π^* I` along the exceptional divisor" [Kol07, Definition 47],
the inequality `≥`. -/
theorem pow_dvd_comap_of_leOrdAlong {m : ℕ} (hm : I.LeOrdAlong Z.support (m : ℕ∞)) :
    Z.exceptionalDivisor ^ m ∣ I.comap Z.blowUpπ :=
  pow_dvd_of_le_pow_of_isInvertible (blowUp.isInvertible_comap_π Z)
    (comap_le_pow_comap_of_leOrdAlong f n Z I hm)

omit [CharZero k] in
/-- At a generic point `η` of a smooth center `Z` of any shape over which the blow-up has points
(`Z_η ≠ 0`), `ord_η I = m` forbids `F^{m+1} ∣ π^* I`: the multiplicity of `π^* I` along the
exceptional divisor is at most `ord_Z I` [Kol07, Definition 47]. The argument is run on the chart
of the local blow-up at `η`, where `Z_η = 𝔪_η`: an element of `I_η` of order exactly `m` is not
in the `(m+1)`-st power of the center's ideal in the chart ring. -/
theorem not_pow_succ_dvd_comap_of_smooth {η : X} (hη : η ∈ Z.support.genericPoints)
    (hZη : Z.stalkIdeal η ≠ ⊥) {m : ℕ} (hm : I.ord η = m) :
    ¬ Z.exceptionalDivisor ^ (m + 1) ∣ I.comap Z.blowUpπ := by
  classical
  intro hdvd
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hreg := isRegularLocalRing_stalk f η
  have hle : I.comap (Scheme.IdealSheafData.blowUpπ Z) ≤ (Z.comap
      (Scheme.IdealSheafData.blowUpπ Z)) ^ (m + 1) := le_pow_of_pow_dvd hdvd
  obtain ⟨φ, H⟩ := exists_isPullback_fromSpecStalk Z η
  -- pull back along the local blow-up at `η`
  have h1 : (specIdealSheaf (I.stalkIdeal η)).comap (affineBlowUp.π (Z.stalkIdeal η)) ≤
      ((specIdealSheaf (Z.stalkIdeal η)).comap (affineBlowUp.π (Z.stalkIdeal η))) ^ (m + 1) := by
    have h : (I.comap (Scheme.IdealSheafData.blowUpπ Z)).comap φ ≤ ((Z.comap
        (Scheme.IdealSheafData.blowUpπ Z)) ^ (m + 1)).comap φ :=
      comap_mono φ hle
    rwa [comap_pow, ← comap_comp, ← comap_comp, H.w, comap_comp, comap_comp,
      comap_fromSpecStalk_eq_specIdealSheaf, comap_fromSpecStalk_eq_specIdealSheaf] at h
  -- `Z_η = 𝔪_η`: `η` is the generic point of its own component
  have hP : (Z.stalkIdeal η).IsPrime := isPrime_stalkIdeal_of_smooth f n Z hη.1
  have hZmax : Z.stalkIdeal η = maximalIdeal (X.presheaf.stalk η) := by
    obtain ⟨η', hη', hspec, hmax, -, -⟩ := exists_genericPoint_of_isPrime_stalkIdeal Z η
    rw [hη.2 hη'.1 hspec] at hmax
    exact hmax
  -- adapted parameters at `η`; `𝔪_η ≠ 0`
  obtain ⟨m', -, y, -, hm', hy, -⟩ := exists_adaptedParameters_of_smooth f Z hη.1
  have hm'pos : 0 < m' := by
    rcases Nat.eq_zero_or_pos m' with h0 | h0
    · exfalso
      apply hZη
      rw [hZmax, hy]
      subst h0
      rw [Set.range_eq_empty, Ideal.span_empty]
    · exact h0
  let ρ : Fin m' := ⟨m' - 1, by omega⟩
  have hρ : ρ.val + 1 = m' := by
    change m' - 1 + 1 = m'
    omega
  have hcenter : Z.stalkIdeal η = chartCenter y ρ := by
    rw [hZmax, hy, chartCenter]
    congr 1
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_, rfl⟩
      change i.val ≤ m' - 1
      have := i.2
      omega
    · rintro ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩
  have hmem : y ρ ∈ Z.stalkIdeal η :=
    hcenter ▸ Ideal.subset_span ⟨ρ, show ρ ≤ ρ from le_rfl, rfl⟩
  -- restrict to the chart of `y_ρ`
  have h2 : ((specIdealSheaf (I.stalkIdeal η)).comap (affineBlowUp.π (Z.stalkIdeal η))).comap
        (affineBlowUp.chart (Z.stalkIdeal η) ⟨y ρ, hmem⟩) ≤
      (((specIdealSheaf (Z.stalkIdeal η)).comap (affineBlowUp.π (Z.stalkIdeal η))) ^ (m + 1)).comap
        (affineBlowUp.chart (Z.stalkIdeal η) ⟨y ρ, hmem⟩) :=
    comap_mono (affineBlowUp.chart (Z.stalkIdeal η) ⟨y ρ, hmem⟩) h1
  rw [comap_pow, ← comap_comp, ← comap_comp, affineBlowUp.chart_π, comap_specIdealSheaf_Spec_map,
    comap_specIdealSheaf_Spec_map, ← specIdealSheaf_pow, specIdealSheaf_le_iff] at h2
  -- an element of `I_η` of order `m`
  have hordI : IsLocalRing.ord (I.stalkIdeal η) = m := by
    rw [← ord_eq_ord_stalkIdeal]
    exact hm
  obtain ⟨g, hgI, hgm⟩ := exists_mem_ordElem_eq_of_ord_eq hordI
  have h3 := h2 (Ideal.mem_map_of_mem _ hgI)
  -- read on the chart ring `𝒪_{X,η}[y_i/y_ρ]`
  have hC : affineBlowUpAlgebra (Z.stalkIdeal η) (y ρ) = chartRing y ρ := by
    rw [hcenter]
    exact affineBlowUpAlgebra_span_eq_chartRing y ρ
  have key : ∀ C : Subalgebra (X.presheaf.stalk η) (Localization.Away (y ρ)), C = chartRing y ρ →
      algebraMap _ C g ∉ ((Z.stalkIdeal η).map (algebraMap _ C)) ^ (m + 1) := by
    rintro C rfl h
    rw [hcenter, map_chartCenter] at h
    exact algebraMap_notMem_span_pow_succ y hy hm' ρ hρ g m hgm h
  exact key _ hC h3

/-- For a smooth center of any shape with `ord_Z I = m` along every component, the birational
transform of [Kol07, 58, (58.1)] is the marked transform `π_*^{-1}(I, m)` of
[Kol07, Definition 60]: the exceptional order of `π^* I` is `m` when the blow-up has a point over
the center, and when it has none the exceptional divisor is `𝒪` and both transforms are
`π^* I`. -/
theorem weakTransform_eq_markedTransform_of_smooth {m : ℕ} (hm : I.OrdAlongEq Z.support (m : ℕ∞)) :
    I.weakTransform Z = I.markedTransform Z m := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hle : I.LeOrdAlong Z.support (m : ℕ∞) := fun η hη => (hm η hη).ge
  by_cases hex : ∃ q : Z.blowUp, Z.blowUpπ q ∈ Z.support
  · obtain ⟨q, hq⟩ := hex
    have hP : (Z.stalkIdeal (Z.blowUpπ q)).IsPrime :=
        isPrime_stalkIdeal_of_smooth f n Z hq
    have hreg := isRegularLocalRing_stalk f (Z.blowUpπ q)
    obtain ⟨η, hη, -, -, hne, -⟩ := exists_genericPoint_of_isPrime_stalkIdeal Z
        (Z.blowUpπ q)
    have hZη : Z.stalkIdeal η ≠ ⊥ := hne (stalkIdeal_ne_bot_of_mem_support_of_smooth f Z q hq)
    have heq : exceptionalOrderAlong Z.blowUpπ Z.exceptionalDivisor I = m := by
      unfold exceptionalOrderAlong
      refine IsGreatest.csSup_eq ⟨pow_dvd_comap_of_leOrdAlong f n Z I hle, fun c hc => ?_⟩
      by_contra hlt
      exact not_pow_succ_dvd_comap_of_smooth f n Z I hη hZη (hm η hη)
        (dvd_trans (pow_dvd_pow _ (Nat.succ_le_of_lt (not_le.mp hlt))) hc)
    change I.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor (exceptionalOrderAlong
        Z.blowUpπ Z.exceptionalDivisor I) = _
    rw [heq]
  · have hex' : ∀ q : Z.blowUp, Z.blowUpπ q ∉ Z.support := fun q hq => hex
      ⟨q, hq⟩
    have hF : Z.exceptionalDivisor = ⊤ := by
      rw [← support_eq_bot_iff]
      ext q
      simp only [exceptionalDivisor, support_comap, TopologicalSpace.Closeds.coe_preimage,
        Set.mem_preimage, TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact hex' q
    have htop : ∀ c : ℕ, (⊤ : Z.blowUp.IdealSheafData) ^ c = ⊤ := fun c => by
      induction c with
      | zero => rw [pow_zero, one_eq_top]
      | succ c ih => rw [pow_succ, ih]; exact mul_top _
    change I.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor _ =
      I.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor m
    rw [hF]
    unfold controlledTransformAlong
    rw [htop, htop]

/-- [Kol07, Lemma 61] for a smooth center of any shape: if `ord_Z I = m` along every component
and `max-ord I = m`, the marked transform `π_*^{-1}(I, m)` has order at most `m` at every point
of `B_Z X`. The proof is Kollár's computation in the chart at each point over the center (an
element of order `m` of `I_z` has a transform of order `≤ m`), the order at the center's point
being pinned by the generic point of its component; off the center the blow-up is an
isomorphism. -/
theorem ord_controlledTransform_le_of_smooth {m : ℕ} (hm : I.OrdAlongEq Z.support (m : ℕ∞))
    (hmax : I.maxOrd = m) (q : Z.blowUp) :
    (I.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor m).ord q ≤ m := by
  classical
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hle : I.LeOrdAlong Z.support (m : ℕ∞) := fun η hη => (hm η hη).ge
  by_cases hq : Z.blowUpπ q ∈ Z.support
  · have hP : (Z.stalkIdeal (Z.blowUpπ q)).IsPrime :=
      isPrime_stalkIdeal_of_smooth f n Z hq
    have hreg := isRegularLocalRing_stalk f (Z.blowUpπ q)
    obtain ⟨η, hη, hspec, -, -, -⟩ := exists_genericPoint_of_isPrime_stalkIdeal Z
        (Z.blowUpπ q)
    -- `ord_z I = m`
    have hordz : I.ord (Z.blowUpπ q) = m := by
      apply le_antisymm
      · rw [← hmax]
        exact I.le_maxOrd _
      · rw [← hm η hη]
        exact ord_le_ord_of_specializes I f n hspec
    have hIZ : I.stalkIdeal (Z.blowUpπ q) ≤ Z.stalkIdeal (Z.blowUpπ q) ^ m :=
      stalkIdeal_le_pow_of_leOrdAlong f n Z I hle hq
        (stalkIdeal_ne_bot_of_mem_support_of_smooth f Z q hq)
    have hFT : Z.exceptionalDivisor ^ m *
        I.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor m =
        I.comap Z.blowUpπ :=
      pow_mul_markedTransform Z I m (pow_dvd_comap_of_leOrdAlong f n Z I hle)
    -- the chart at `q`
    obtain ⟨n', y, ρ, hn', hy, hZ', 𝔮, hprime, hle', e, he⟩ :=
      exists_stalk_equiv_localization_chart_of_smooth f Z q hq
    rw [ord_eq_ord_stalkIdeal, ← ord_map_ringEquiv (B := Localization.AtPrime 𝔮) e,
      ← RingEquiv.toRingHom_eq_coe]
    -- an element `f₀ ∈ I_z` of order exactly `m`, in `Z_z^m = P^m`
    have hordIz : IsLocalRing.ord (I.stalkIdeal (Z.blowUpπ q)) = m := by
      rw [← ord_eq_ord_stalkIdeal]
      exact hordz
    obtain ⟨f₀, hf₀I, hf₀⟩ := exists_mem_ordElem_eq_of_ord_eq hordIz
    have hf₀P : f₀ ∈ chartCenter y ρ ^ m := by
      have := hIZ hf₀I
      rwa [hZ'] at this
    -- `π^♯ f₀` lies in the stalk of `F^m · T = I^*`
    have hmem0 : Z.blowUpπ.stalkMap q f₀ ∈
        (Z.exceptionalDivisor ^ m *
          I.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor m).stalkIdeal
              q := by
      rw [hFT, stalkIdeal_comap]
      exact Ideal.mem_map_of_mem _ hf₀I
    have hkey := algebraMap_transformElem_mem_map_of_mem q y hy hn' ρ hZ' 𝔮 e he _
      hf₀P hmem0
    -- the local Lemma 61 at the prime `𝔮` of the fibre
    have hbound := ordElem_algebraMap_transformElem_le y hy hn' ρ 𝔮 hle' hf₀P hf₀
    refine le_trans (IsLocalRing.ord_anti (Ideal.span_le.mpr
      (Set.singleton_subset_iff.mpr hkey))) ?_
    rw [ord_span_singleton]
    exact hbound
  · have h2 : (I.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor m).ord q ≤
        I.ord (Z.blowUpπ q) :=
      ord_controlledTransform_le_of_notMem Z I m q hq
    refine h2.trans ?_
    rw [← hmax]
    exact I.le_maxOrd _

/-- [Kol07, Lemma 61] in its global form: `max-ord π_*^{-1}(I, m) ≤ m` when
`ord_Z I = max-ord I = m` along a smooth center of any shape. -/
theorem maxOrd_controlledTransform_le_of_smooth {m : ℕ} (hm : I.OrdAlongEq Z.support (m : ℕ∞))
    (hmax : I.maxOrd = m) :
    (I.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor m).maxOrd ≤ m :=
  (maxOrd_le_iff _).mpr fun q => ord_controlledTransform_le_of_smooth f n Z I hm hmax q

end SmoothCenterOrder

end AlgebraicGeometry
