/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Scheme.BlowUp.Transform.Defs
import Hironaka.Algebra.Local.Chart
import Hironaka.Algebra.Local.ChartFibre
import Hironaka.Algebra.Local.PolynomialOrder
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.Transform
import Hironaka.Algebra.Local.TransformOrder
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Glue.Trivial
import Hironaka.Scheme.BlowUp.Transform
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Exceptional
import Hironaka.Scheme.IdealSheaf.Order.ExceptionalOrder
import Hironaka.Scheme.IdealSheaf.Order.Invariance
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Smooth.LocalBlowUpChart
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Lemma 61: the maximal order does not increase under a blow-up of maximal order

[Kol07, Lemma 61]: for a smooth blow-up `π : B_Z X → X` with `ord_Z I = max-ord I = m`, the marked
transform `π_*^{-1}(I, m)` has order at most `m` at every point `q` of `B_Z X`
(`ord_controlledTransform_le`), hence `max-ord π_*^{-1}(I, m) ≤ max-ord I`
(`maxOrd_controlledTransform_le`); in Kollár's unmarked form the transform is the weak transform
(`maxOrd_weakTransform_le`, `Hironaka/Scheme/IdealSheaf/Order/ExceptionalOrder.lean`).

**Why.** Off the exceptional divisor `π` is an isomorphism and the marked transform contains `I^*`,
so `ord_q ≤ ord_{π q} I ≤ max-ord I` (`ord_controlledTransform_le_of_notMem`, with
`ord_comap_of_isOpenImmersion` of `Hironaka/Scheme/IdealSheaf/Order/Invariance.lean`). At `q ∈ F`
over `z ∈ Z`: `ord_z I = m` (`m = ord_Z I ≤ ord_z I ≤ max-ord I = m`,
`Hironaka/Scheme/IdealSheaf/Order/Specialization.lean`), `I_z ≤ Z_z^m`
(`Hironaka/Scheme/IdealSheaf/Order/Exceptional.lean`), and `𝒪_{B,q}` is the localization of the
chart ring `𝒪_{X,z}[y_i/y_ρ]` (`Hironaka/Algebra/Local/ChartRing.lean`) at a prime `𝔮` of the fibre
(`exists_stalk_equiv_localization_chart`, `Hironaka/Scheme/Smooth/LocalBlowUpChart.lean`). The
identity `F^m · π_*^{-1}(I, m) = I^*` read on stalks says `(y_ρ)^m · T_q = I_z 𝒪_{B,q}`, so for `f ∈
I_z` of order `m` the transform `f/y_ρ^m` lies in `T_q` (`y_ρ` is a nonzerodivisor of the domain
`𝒪_{B,q}`), and its order is `≤ m` by the local Lemma 61 at every prime of the fibre
(`ordElem_algebraMap_transformElem_le`, `Hironaka/Algebra/Local/ChartFibre.lean`). Kollár's proof
treats the origins of the charts and reaches every point of the exceptional divisor by a linear
change of coordinates; the argument at the non-rational points of the fibre is the library's own.

Used for the orders along centres in a blow-up sequence
(`Hironaka/Scheme/BlowUpSequence/OrderAlongCenter.lean`,
`Hironaka/Scheme/BlowUpSequence/CentersCosupport.lean`,
`Hironaka/Scheme/BlowUpSequence/SmoothCenter.lean`,
`Hironaka/Scheme/BlowUpSequence/TransformDerivative.lean`).
-/

public section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Off the exceptional divisor: `π` is an isomorphism over `X ∖ Z`, and the marked transform
contains `I^*`, so its order at `q` is at most `ord_{π q} I`. -/
theorem ord_controlledTransform_le_of_notMem (Z I : X.IdealSheafData) (m : ℕ) (q : blowUp Z)
    (hq : blowUpπ Z q ∉ Z.support) :
    (I.controlledTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z)) m).ord q ≤
      I.ord (blowUpπ Z q) := by
  refine
      (Scheme.IdealSheafData.ord_anti
          (comap_le_controlledTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z)) I m)
    q).trans (le_of_eq ?_)
  have hqU : q ∈ blowUpπ Z ⁻¹ᵁ Z.support.compl := (blowUpπ Z).mem_preimage.mpr hq
  have := blowUp.isIso_π_restrict_compl_support Z
  have hcomp : (I.comap (blowUpπ Z)).comap (Scheme.Opens.ι (blowUpπ Z ⁻¹ᵁ Z.support.compl)) =
      (I.comap (Scheme.Opens.ι Z.support.compl)).comap (blowUpπ Z ∣_ Z.support.compl) := by
    rw [← comap_comp, ← comap_comp, morphismRestrict_ι]
  -- the three order identities, at the point `⟨q, hqU⟩` of `π⁻¹(X ∖ Z)`
  have h1 := ord_comap_ι (I.comap (blowUpπ Z)) (blowUpπ Z ⁻¹ᵁ Z.support.compl) ⟨q, hqU⟩
  have h2 := ord_comap_of_isIso (I.comap (Scheme.Opens.ι Z.support.compl))
    (blowUpπ Z ∣_ Z.support.compl) ⟨q, hqU⟩
  have h3 := ord_comap_ι I Z.support.compl ((blowUpπ Z ∣_ Z.support.compl) ⟨q, hqU⟩)
  have h4 : Scheme.Opens.ι Z.support.compl ((blowUpπ Z ∣_ Z.support.compl) ⟨q, hqU⟩) =
      blowUpπ Z q :=
    morphismRestrict_base_coe (blowUpπ Z) Z.support.compl ⟨q, hqU⟩
  rw [hcomp] at h1
  rw [h4] at h3
  exact h1.symm.trans (h2.trans h3)

/-- The stalk of the exceptional divisor `F = Z·𝒪_B` at a point `q` of the fibre, in the chart data
of `exists_stalk_equiv_localization_chart`: it is the principal ideal `(π^♯ y_ρ)`, since each
generator `π^♯ y_i` (`i ≤ ρ`) is `π^♯ y_ρ` times `(y_i/y_ρ)` read back through `e`.  (The
equivalence `e` is used only through `e.toRingHom`: applying it directly makes the unifier work
through the localization's ring instances and exceeds the heartbeat limit.) -/
theorem stalkIdeal_comap_eq_span_of_chart {Z : X.IdealSheafData} (q : blowUp Z) {n' : ℕ}
    (y : Fin n' → X.presheaf.stalk (blowUpπ Z q)) (ρ : Fin n')
    (hZ' : Z.stalkIdeal (blowUpπ Z q) = chartCenter y ρ) (𝔮 : Ideal (chartRing y ρ))
    [𝔮.IsPrime] (e : (blowUp Z).presheaf.stalk q ≃+* Localization.AtPrime 𝔮)
    (he : ∀ c, e ((blowUpπ Z).stalkMap q c) =
      algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
        (algebraMap (X.presheaf.stalk (blowUpπ Z q)) (chartRing y ρ) c)) :
    (Z.comap (blowUpπ Z)).stalkIdeal q = Ideal.span {(blowUpπ Z).stalkMap q (y ρ)} := by
  have hcomp : e.toRingHom.comp ((blowUpπ Z).stalkMap q).hom =
      (algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)).comp
        (algebraMap (X.presheaf.stalk (blowUpπ Z q)) (chartRing y ρ)) := RingHom.ext he
  have hψ : ∀ c, e.toRingHom ((blowUpπ Z).stalkMap q c) =
      algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
        (algebraMap (X.presheaf.stalk (blowUpπ Z q)) (chartRing y ρ) c) :=
    fun c => RingHom.congr_fun hcomp c
  have hinj : Function.Injective e.toRingHom := e.injective
  have hsurj : Function.Surjective e.toRingHom := e.surjective
  rw [stalkIdeal_comap, hZ', chartCenter, Ideal.map_span, ← Set.image_comp]
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ ⟨i, hi, rfl⟩
    change i ≤ ρ at hi
    rcases eq_or_lt_of_le hi with heq | hlt
    · rw [heq]
      exact Ideal.subset_span rfl
    · obtain ⟨u, hu⟩ := hsurj (algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
        (chartYR y ρ i))
      -- `rw` with `hψ` would compare stalk-map applications against the pattern and time out;
      -- chain the equalities explicitly
      have h1 : e.toRingHom ((blowUpπ Z).stalkMap q (y i)) =
          e.toRingHom ((blowUpπ Z).stalkMap q (y ρ) * u) :=
        calc e.toRingHom ((blowUpπ Z).stalkMap q (y i))
            = algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
                (algebraMap _ (chartRing y ρ) (y i)) := hψ (y i)
          _ = algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
                (algebraMap _ (chartRing y ρ) (y ρ) * chartYR y ρ i) := by
              rw [algebraMap_x_eq_mul_chartYR y ρ hlt]
          _ = algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
                (algebraMap _ (chartRing y ρ) (y ρ)) *
              algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮) (chartYR y ρ i) :=
              map_mul _ _ _
          _ = e.toRingHom ((blowUpπ Z).stalkMap q (y ρ)) * e.toRingHom u :=
              congrArg₂ (· * ·) (hψ (y ρ)).symm hu.symm
          _ = e.toRingHom ((blowUpπ Z).stalkMap q (y ρ) * u) := (map_mul _ _ _).symm
      change (blowUpπ Z).stalkMap q (y i) ∈ _
      rw [hinj h1]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · rintro _ rfl
    exact Ideal.subset_span ⟨ρ, show ρ ≤ ρ from le_rfl, rfl⟩

/-- In the chart data at `q`: if `π^♯ f` lies in the stalk of `F^m · T`, then
`π^♯ f = (π^♯ y_ρ)^m · t` for some `t` in the stalk of `T`. -/
theorem exists_mem_stalkIdeal_pow_mul_eq {Z : X.IdealSheafData} (q : blowUp Z) {n' : ℕ}
    (y : Fin n' → X.presheaf.stalk (blowUpπ Z q)) (ρ : Fin n')
    (hZ' : Z.stalkIdeal (blowUpπ Z q) = chartCenter y ρ) (𝔮 : Ideal (chartRing y ρ))
    [𝔮.IsPrime] (e : (blowUp Z).presheaf.stalk q ≃+* Localization.AtPrime 𝔮)
    (he : ∀ c, e ((blowUpπ Z).stalkMap q c) =
      algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
        (algebraMap (X.presheaf.stalk (blowUpπ Z q)) (chartRing y ρ) c))
    (T : (blowUp Z).IdealSheafData) {m : ℕ} {f₀ : X.presheaf.stalk (blowUpπ Z q)}
    (hmem0 : (blowUpπ Z).stalkMap q f₀ ∈ ((Z.comap (blowUpπ Z)) ^ m * T).stalkIdeal q) :
    ∃ t ∈ T.stalkIdeal q, (blowUpπ Z).stalkMap q (y ρ) ^ m * t = (blowUpπ Z).stalkMap q f₀ := by
  have hFq := stalkIdeal_comap_eq_span_of_chart q y ρ hZ' 𝔮 e he
  rw [stalkIdeal_mul, stalkIdeal_pow, hFq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton_mul] at hmem0
  exact hmem0

/-- The equation `(π^♯ y_ρ)^m · t = π^♯ f` read through `e`: `y_ρ^m · e t = f` in `R'_𝔮`. -/
theorem toRingHom_pow_mul_eq_of_pow_mul_eq {Z : X.IdealSheafData} (q : blowUp Z) {n' : ℕ}
    (y : Fin n' → X.presheaf.stalk (blowUpπ Z q)) (ρ : Fin n') (𝔮 : Ideal (chartRing y ρ))
    [𝔮.IsPrime] (e : (blowUp Z).presheaf.stalk q ≃+* Localization.AtPrime 𝔮)
    (he : ∀ c, e ((blowUpπ Z).stalkMap q c) =
      algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
        (algebraMap (X.presheaf.stalk (blowUpπ Z q)) (chartRing y ρ) c))
    {m : ℕ} {f₀ : X.presheaf.stalk (blowUpπ Z q)} {t : (blowUp Z).presheaf.stalk q}
    (hteq : (blowUpπ Z).stalkMap q (y ρ) ^ m * t = (blowUpπ Z).stalkMap q f₀) :
    algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
        (algebraMap _ (chartRing y ρ) (y ρ)) ^ m * e.toRingHom t =
      algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮) (algebraMap _ (chartRing y ρ) f₀) := by
  have hcomp : e.toRingHom.comp ((blowUpπ Z).stalkMap q).hom =
      (algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)).comp
        (algebraMap (X.presheaf.stalk (blowUpπ Z q)) (chartRing y ρ)) := RingHom.ext he
  have hψ : ∀ c, e.toRingHom ((blowUpπ Z).stalkMap q c) =
      algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
        (algebraMap (X.presheaf.stalk (blowUpπ Z q)) (chartRing y ρ) c) :=
    fun c => RingHom.congr_fun hcomp c
  -- explicit chains: `rw` with `hψ` would compare stalk-map applications against the pattern
  have hteq2 : e.toRingHom ((blowUpπ Z).stalkMap q (y ρ)) ^ m * e.toRingHom t =
      e.toRingHom ((blowUpπ Z).stalkMap q f₀) :=
    ((congrArg₂ (· * ·) (map_pow e.toRingHom ((blowUpπ Z).stalkMap q (y ρ)) m).symm rfl).trans
      (map_mul e.toRingHom _ _).symm).trans (congrArg e.toRingHom hteq)
  exact ((congrArg₂ (· * ·) (congrArg (· ^ m) (hψ (y ρ)).symm) rfl).trans hteq2).trans (hψ f₀)

/-- Cancelling `y_ρ^m` in the domain `R'_𝔮`: `y_ρ^m · e t = f` forces `e t = f/y_ρ^m`. -/
theorem toRingHom_eq_algebraMap_transformElem {Z : X.IdealSheafData} (q : blowUp Z) {n' : ℕ}
    (y : Fin n' → X.presheaf.stalk (blowUpπ Z q))
    [IsRegularLocalRing (X.presheaf.stalk (blowUpπ Z q))]
    (hy : maximalIdeal (X.presheaf.stalk (blowUpπ Z q)) = Ideal.span (Set.range y))
    (hn' : (n' : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (blowUpπ Z q))) (ρ : Fin n')
    (𝔮 : Ideal (chartRing y ρ)) [𝔮.IsPrime]
    (e : (blowUp Z).presheaf.stalk q ≃+* Localization.AtPrime 𝔮)
    {m : ℕ} {f₀ : X.presheaf.stalk (blowUpπ Z q)} (hf₀P : f₀ ∈ chartCenter y ρ ^ m)
    {t : (blowUp Z).presheaf.stalk q}
    (hteq3 : algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
        (algebraMap _ (chartRing y ρ) (y ρ)) ^ m * e.toRingHom t =
      algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮) (algebraMap _ (chartRing y ρ) f₀)) :
    e.toRingHom t = algebraMap _ (Localization.AtPrime 𝔮) (transformElem y ρ f₀ hf₀P) := by
  have hdom : IsDomain (chartRing y ρ) := isDomain_chartRing y ρ hy hn'
  have hdom' : IsDomain (Localization.AtPrime 𝔮) :=
    IsLocalization.isDomain_localization 𝔮.primeCompl_le_nonZeroDivisors
  have hne : algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
      (algebraMap _ (chartRing y ρ) (y ρ)) ≠ 0 := by
    intro h0
    have hinj' : Function.Injective (algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)) :=
      IsLocalization.injective (M := 𝔮.primeCompl) (S := Localization.AtPrime 𝔮)
        𝔮.primeCompl_le_nonZeroDivisors
    have h1' := hinj' (h0.trans (map_zero _).symm)
    exact x_ne_zero_of_span_eq y hy hn' ρ
      (algebraMap_chartRing_injective y ρ hy hn' (h1'.trans (map_zero _).symm))
  have hteq' : algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
        (algebraMap _ (chartRing y ρ) (y ρ)) ^ m * e.toRingHom t =
      algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
        (algebraMap _ (chartRing y ρ) (y ρ)) ^ m *
        algebraMap _ (Localization.AtPrime 𝔮) (transformElem y ρ f₀ hf₀P) :=
    hteq3.trans (by
      rw [← map_pow (algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮))
        (algebraMap _ (chartRing y ρ) (y ρ)) m,
        ← map_mul (algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)),
        algebraMap_pow_mul_transformElem])
  have _ : IsLeftCancelMulZero (Localization.AtPrime 𝔮) :=
    hdom'.toIsCancelMulZero.toIsLeftCancelMulZero
  exact mul_left_cancel₀ (pow_ne_zero m hne) hteq'

/-- In the chart data at `q`, if `π^♯ f` lies in the stalk of `F^m · T`, then the transform
`f/y_ρ^m` of `f ∈ P^m` lies in the stalk of `T` transported to the chart ring's localization. -/
theorem algebraMap_transformElem_mem_map_of_mem {Z : X.IdealSheafData} (q : blowUp Z) {n' : ℕ}
    (y : Fin n' → X.presheaf.stalk (blowUpπ Z q))
    [IsRegularLocalRing (X.presheaf.stalk (blowUpπ Z q))]
    (hy : maximalIdeal (X.presheaf.stalk (blowUpπ Z q)) = Ideal.span (Set.range y))
    (hn' : (n' : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (blowUpπ Z q))) (ρ : Fin n')
    (hZ' : Z.stalkIdeal (blowUpπ Z q) = chartCenter y ρ) (𝔮 : Ideal (chartRing y ρ))
    [𝔮.IsPrime] (e : (blowUp Z).presheaf.stalk q ≃+* Localization.AtPrime 𝔮)
    (he : ∀ c, e ((blowUpπ Z).stalkMap q c) =
      algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
        (algebraMap (X.presheaf.stalk (blowUpπ Z q)) (chartRing y ρ) c))
    (T : (blowUp Z).IdealSheafData) {m : ℕ} {f₀ : X.presheaf.stalk (blowUpπ Z q)}
    (hf₀P : f₀ ∈ chartCenter y ρ ^ m)
    (hmem0 : (blowUpπ Z).stalkMap q f₀ ∈ ((Z.comap (blowUpπ Z)) ^ m * T).stalkIdeal q) :
    algebraMap _ (Localization.AtPrime 𝔮) (transformElem y ρ f₀ hf₀P) ∈
      (T.stalkIdeal q).map e.toRingHom := by
  obtain ⟨t, ht, hteq⟩ := exists_mem_stalkIdeal_pow_mul_eq q y ρ hZ' 𝔮 e he T hmem0
  have h3 := toRingHom_pow_mul_eq_of_pow_mul_eq q y ρ 𝔮 e he hteq
  have hc := toRingHom_eq_algebraMap_transformElem q y hy hn' ρ 𝔮 e hf₀P h3
  have hmem := Ideal.mem_map_of_mem e.toRingHom ht
  rw [hc] at hmem
  exact hmem

section Global

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n r : ℕ)
  [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData)
  [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)] (hr : 1 ≤ r) (hrn : r ≤ n)
  (I : X.IdealSheafData) {η : X} (hη : IsGenericPoint η (Z.support : Set X))

include f n r hr hrn hη

/-- On the exceptional divisor: through the chart at `q` (`exists_stalk_equiv_localization_chart`),
`F^m · π_*^{-1}(I, m) = I^*` (`Hironaka/Scheme/IdealSheaf/Order/ExceptionalOrder.lean`) and the
local Lemma 61 at every prime of the fibre (`ordElem_algebraMap_transformElem_le`). -/
theorem ord_controlledTransform_le_of_mem (m : ℕ) (hm : I.ord η = m) (hmax : I.maxOrd = m)
    (q : blowUp Z) (hq : blowUpπ Z q ∈ Z.support) :
    (I.controlledTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z)) m).ord q ≤ m := by
  classical
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  -- `ord_z I = m`
  have hordz : I.ord (blowUpπ Z q) = m := by
    apply le_antisymm
    · rw [← hmax]
      exact I.le_maxOrd _
    · rw [← hm]
      exact ord_le_ord_of_specializes I f n (hη.specializes hq)
  have hIZ : I ≤ Z ^ m := le_pow_of_le_ord f n r Z hr hrn I hη m (le_of_eq hm.symm)
  have hFT := pow_mul_controlledTransformAlong f n r Z hr hrn I hη m (le_of_eq hm.symm)
  -- the chart at `q`
  obtain ⟨n', y, ρ, hn', hy, hZ', 𝔮, hprime, hle, e, he⟩ :=
    exists_stalk_equiv_localization_chart f n r Z hrn q hq
  have hreg : IsRegularLocalRing (X.presheaf.stalk (blowUpπ Z q)) :=
    isRegularLocalRing_stalk f _
  rw [ord_eq_ord_stalkIdeal, ← ord_map_ringEquiv (B := Localization.AtPrime 𝔮) e,
    ← RingEquiv.toRingHom_eq_coe]
  -- an element `f₀ ∈ I_z` of order exactly `m`, in `Z_z^m = P^m`
  have hordIz : IsLocalRing.ord (I.stalkIdeal (blowUpπ Z q)) = m := by
    rw [← ord_eq_ord_stalkIdeal]
    exact hordz
  obtain ⟨f₀, hf₀I, hf₀⟩ := exists_mem_ordElem_eq_of_ord_eq hordIz
  have hf₀P : f₀ ∈ chartCenter y ρ ^ m := by
    have := stalkIdeal_mono hIZ (blowUpπ Z q) hf₀I
    rwa [stalkIdeal_pow, hZ'] at this
  -- `π^♯ f₀` lies in the stalk of `F^m · T = I^*`
  have hmem0 : (blowUpπ Z).stalkMap q f₀ ∈
      ((Z.comap (blowUpπ Z)) ^ m *
        I.controlledTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z)) m).stalkIdeal q := by
    rw [hFT, stalkIdeal_comap]
    exact Ideal.mem_map_of_mem _ hf₀I
  have hkey := algebraMap_transformElem_mem_map_of_mem q y hy hn' ρ hZ' 𝔮 e he _ hf₀P hmem0
  -- the local Lemma 61 at the prime `𝔮` of the fibre
  have hbound := ordElem_algebraMap_transformElem_le y hy hn' ρ 𝔮 hle hf₀P hf₀
  refine le_trans (IsLocalRing.ord_anti (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hkey))) ?_
  rw [ord_span_singleton]
  exact hbound

/-- [Kol07, Lemma 61] pointwise: if `ord_Z I = max-ord I = m`, the marked transform
`π_*^{-1}(I, m)` has order at most `m` at every point of `B_Z X`. -/
theorem ord_controlledTransform_le (m : ℕ) (hm : I.ord η = m) (hmax : I.maxOrd = m)
    (q : blowUp Z) :
    (I.controlledTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z)) m).ord q ≤ m := by
  by_cases hq : blowUpπ Z q ∈ Z.support
  · exact ord_controlledTransform_le_of_mem f n r Z hr hrn I hη m hm hmax q hq
  · refine (ord_controlledTransform_le_of_notMem Z I m q hq).trans ?_
    rw [← hmax]
    exact I.le_maxOrd _

/-- [Kol07, Lemma 61]: `max-ord π_*^{-1}(I, m) ≤ max-ord I` when `ord_Z I = max-ord I = m`. -/
theorem maxOrd_controlledTransform_le (m : ℕ) (hm : I.ord η = m) (hmax : I.maxOrd = m) :
    (I.controlledTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z)) m).maxOrd ≤ I.maxOrd := by
  rw [maxOrd_le_iff, hmax]
  exact fun q => ord_controlledTransform_le f n r Z hr hrn I hη m hm hmax q

/-- [Kol07, Lemma 61] in its unmarked form: the weak transform is the marked transform with mark
`ord_Z I` (`weakTransformAlong_eq`). -/
theorem maxOrd_weakTransform_le (m : ℕ) (hm : I.ord η = m) (hmax : I.maxOrd = m) :
    (I.weakTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z))).maxOrd ≤ I.maxOrd := by
  rw [weakTransformAlong_eq f n r Z hr hrn I hη m hm]
  exact maxOrd_controlledTransform_le f n r Z hr hrn I hη m hm hmax

end Global

end AlgebraicGeometry
