/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Scheme.BlowUp.Transform.Defs
public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Hironaka.Scheme.Smooth.EtaleCoordinatesDefs
import Hironaka.Algebra.Local.Chart
import Hironaka.Algebra.Local.QuotientParameters
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.RegularSmooth.SchemeForms
public import Hironaka.Scheme.BlowUp.Descent
public import Hironaka.Scheme.BlowUp.Glue.BlowUp
import Hironaka.Scheme.BlowUp.Transform
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Lemma61
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
public import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.Adapted
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Smooth.BlowUpSmooth
import Hironaka.Scheme.Smooth.ChartRing
import Hironaka.Scheme.Smooth.DifferentialBasis
import Hironaka.Scheme.Smooth.EtaleCoordinates
import Hironaka.Scheme.Smooth.EtaleLocal
import Hironaka.Scheme.Smooth.LocalBlowUp
import Hironaka.Scheme.Smooth.LocalBlowUpChart
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Sets.Closeds
public import Hironaka.Scheme.IdealSheaf.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Hironaka.Algebra.Local.ChartRing
public import Mathlib.CategoryTheory.Category.Basic
public import Hironaka.Scheme.BlowUpSequence.Defs
/-!
# Smooth centers of any shape: local coordinates, the chart of the blow-up, nonvanishing

Kollár's smooth blow-ups [Kol07, Notation 19 and Definition 66 (2)] have a center `Z ⊂ X` smooth
over `k`, possibly reducible, its components possibly of different dimensions: the algorithm blows
up the disjoint components of a stratum simultaneously. The theory of the blow-up of a smooth
center elsewhere in this library (`Hironaka/Scheme/Smooth/BlowUpSmooth.lean`,
`Hironaka/Scheme/IdealSheaf/Order/Lemma61.lean`) works with a center of pure codimension `r`
(`SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)`), but its proofs are assembled from local
cores whose only inputs at a point `x ∈ Z` are a regular system of parameters of `𝒪_{X,x}` an
initial segment of which generates `Z_x`. This module produces those inputs for a smooth center as
such and re-runs the local cores.

**Adapted parameters.** At `x ∈ Z`, `𝒪_{X,x}` is regular and `𝒪_{X,x}/Z_x ≅ 𝒪_{Z,x}` is regular
(from `Smooth (Z.subschemeι ≫ f)` alone), so a regular system of parameters `y_0, …, y_{m-1}` of
`𝔪_x`, `m = dim 𝒪_{X,x}`, can be chosen with `Z_x = (y_0, …, y_{c-1})` [Sta, Tag 00NR], `c` the
codimension of `Z` at `x`, which the statement carries instead of assuming.

**The chart of the blow-up at a point.** With these parameters, at a point `q` of `B_Z X` over
`x ∈ Z` the stalk `𝒪_{B,q}` is the localization of the chart ring `𝒪_{X,x}[y_i/y_ρ]` at a prime
over `𝔪_x`, compatibly with `π^♯` (`exists_stalk_equiv_localization_chart_of_smooth`); once the
parameters are chosen the proof is local (the chart cover of the local blow-up, and the
identification of the affine blow-up algebra with the chart ring).

**Consequences.** `π^♯ : 𝒪_{X,x} → 𝒪_{B,q}` is injective (the chart ring is a subring of
`𝒪_{X,x}[1/y_ρ]`, `y_ρ ≠ 0` in the domain `𝒪_{X,x}`, and localizations of domains are injective),
so the total transform of an ideal sheaf nonzero at `x` is nonzero at `q`; off the exceptional
divisor the blow-up is an isomorphism and the order is unchanged
(`ord_controlledTransform_le_of_notMem`). Hence `π^* I` and its controlled transforms are nonzero
everywhere when `I` is. At a generic point `η` of an irreducible component of `X` the only
generization of `η` is `η`, so `Spec 𝒪_{X,η}` is a point and the domain `𝒪_{X,η}` is a field; a
center of order `≥ m ≥ 1` therefore contains no component (`I_η ⊆ 𝔪_η = 0` would contradict
nonvanishing), Kollár's remark after Lemma 62. Finally the blow-up of an equidimensional smooth
scheme along a smooth center of any shape is smooth of the same relative dimension
(`smoothOfRelativeDimension_blowUpπ_comp_of_smooth`, [Kol07, Notation 19]), by gluing over the
complement of the center and the charts of adapted étale coordinates at the closed points of the
center, each with its own codimension. These are the facts that make the transform of a triple a
triple (`Hironaka/Scheme/BlowUpSequence/Triple.lean`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
  Scheme.IdealSheafData Scheme.BlowUpSequence AlgebraicGeometry.Scheme.IdealSheafData
  KaehlerDifferential TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

section Center

variable (f : X ⟶ Spec (.of k)) [Smooth f] (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)]

include f

/-- Adapted parameters at any point `x` of a smooth center: a regular system of parameters `y` of
`𝒪_{X,x}` whose first `c` members generate `Z_x`, `c` the local codimension of `Z` at `x`
[Sta, Tag 00NR]. -/
theorem exists_adaptedParameters_of_smooth {x : X} (hx : x ∈ Z.support) :
    ∃ (m c : ℕ) (y : Fin m → X.presheaf.stalk x), c ≤ m ∧
      (m : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) ∧
      maximalIdeal (X.presheaf.stalk x) = Ideal.span (Set.range y) ∧
      Z.stalkIdeal x = Ideal.span (y '' {j | j.val < c}) := by
  have := isRegularLocalRing_stalk f x
  have := isRegularLocalRing_quotient_stalkIdeal Z f hx
  exact IsRegularLocalRing.exists_span_eq_maximalIdeal_and_eq_span_image_lt
    (Z.stalkIdeal x)

/-- The chart of the blow-up at a point `q` of `B_Z X` over `z ∈ Z`, for a smooth center of any
shape: the stalk `𝒪_{B,q}` is the localization of the chart ring `𝒪_{X,z}[y_i/y_ρ]` at a prime
`𝔮` lying over `𝔪_z`, compatibly with `π^♯`, for adapted parameters `y` with `Z_z = (y_0, …, y_ρ)`.
The proof is that of `AlgebraicGeometry.exists_stalk_equiv_localization_chart` with
`exists_adaptedParameters_of_smooth` in place of the pure-codimension adapted parameters. -/
theorem exists_stalk_equiv_localization_chart_of_smooth (q : Z.blowUp)
    (hq : Z.blowUpπ q ∈ Z.support) :
    ∃ (n' : ℕ) (y : Fin n' → X.presheaf.stalk (Z.blowUpπ q)) (ρ : Fin n'),
      (n' : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (Z.blowUpπ q)) ∧
      maximalIdeal (X.presheaf.stalk (Z.blowUpπ q)) = Ideal.span (Set.range y) ∧
      Z.stalkIdeal (Z.blowUpπ q) = chartCenter y ρ ∧
      ∃ (𝔮 : Ideal (chartRing y ρ)) (_ : 𝔮.IsPrime),
        maximalIdeal (X.presheaf.stalk (Z.blowUpπ q)) ≤
            𝔮.comap (algebraMap (X.presheaf.stalk (Z.blowUpπ q))
                (chartRing y ρ)) ∧
          ∃ e : Z.blowUp.presheaf.stalk q ≃+* Localization.AtPrime 𝔮,
            ∀ c : X.presheaf.stalk (Z.blowUpπ q),
              e (Z.blowUpπ.stalkMap q c) =
                algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
                  (algebraMap (X.presheaf.stalk (Z.blowUpπ q))
                      (chartRing y ρ) c) := by
  classical
  obtain ⟨n', r, y, -, hn', hy, hZ⟩ := exists_adaptedParameters_of_smooth f Z hq
  -- a point of the local blow-up over `q`, for the degenerate cases
  obtain ⟨φ, H⟩ := exists_isPullback_fromSpecStalk Z (Scheme.IdealSheafData.blowUpπ Z q)
  obtain ⟨q', -, -⟩ := Scheme.exists_preimage_of_isPullback H q (closedPoint _)
    (by rw [Scheme.fromSpecStalk_closedPoint])
  have hZbot : Z.stalkIdeal (Scheme.IdealSheafData.blowUpπ Z q) = ⊥ → False := by
    intro hZ0
    have : IsEmpty (affineBlowUp (Z.stalkIdeal (Scheme.IdealSheafData.blowUpπ Z q))) := by
      rw [hZ0]
      exact affineBlowUp.isEmpty_bot
    exact this.false q'
  have hn0 : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h0 | h0
    · exfalso
      subst h0
      apply hZbot
      rw [hZ, Set.eq_empty_of_isEmpty ({j : Fin 0 | j.val < r}), Set.image_empty, Ideal.span_empty]
    · exact h0
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      subst h0
      apply hZbot
      have hemp : {j : Fin n' | j.val < 0} = ∅ := by
        ext j
        simp
      rw [hZ, hemp, Set.image_empty, Ideal.span_empty]
    · exact h0
  let ρ : Fin n' := ⟨min (r - 1) (n' - 1), by omega⟩
  have hset : {j : Fin n' | j.val < r} = {j | j ≤ ρ} := by
    ext j
    change j.val < r ↔ j ≤ ρ
    rw [Fin.le_def]
    change j.val < r ↔ j.val ≤ min (r - 1) (n' - 1)
    have := j.2
    omega
  have hZ' : Z.stalkIdeal (Scheme.IdealSheafData.blowUpπ Z q) = chartCenter y ρ := by
    rw [hZ, hset]
    rfl
  obtain ⟨j, hj, h⟩ := exists_hasChartData Z y ρ hZ' q rfl
  -- permute the parameters so that the chart of `y j` is the chart of the last center coordinate
  have hyρ : (y ∘ Equiv.swap j ρ) ρ = y j := by
    change y (Equiv.swap j ρ ρ) = y j
    rw [Equiv.swap_apply_right]
  have hrange : Set.range (y ∘ Equiv.swap j ρ) = Set.range y := by
    rw [Set.range_comp, (Equiv.swap j ρ).surjective.range_eq, Set.image_univ]
  have hZ'' : Z.stalkIdeal (Scheme.IdealSheafData.blowUpπ Z q) = chartCenter
      (y ∘ Equiv.swap j ρ) ρ := by
    rw [hZ', chartCenter, chartCenter, Set.image_comp, image_swap_Iic hj]
  have h1 : HasChartData Z (Scheme.IdealSheafData.blowUpπ Z q) q ((y ∘ Equiv.swap j ρ) ρ)
      (affineBlowUpAlgebra (Z.stalkIdeal (Scheme.IdealSheafData.blowUpπ Z q))
          ((y ∘ Equiv.swap j ρ) ρ)) :=
    hyρ.symm ▸ h
  have hC : affineBlowUpAlgebra (Z.stalkIdeal (Scheme.IdealSheafData.blowUpπ Z q))
      ((y ∘ Equiv.swap j ρ) ρ) =
      chartRing (y ∘ Equiv.swap j ρ) ρ := by
    rw [hZ'']
    exact affineBlowUpAlgebra_span_eq_chartRing (y ∘ Equiv.swap j ρ) ρ
  have h2 : HasChartData Z (Scheme.IdealSheafData.blowUpπ Z q) q ((y ∘ Equiv.swap j ρ) ρ)
      (chartRing (y ∘ Equiv.swap j ρ) ρ) := hC ▸ h1
  obtain ⟨𝔮, hprime, hle, e, he⟩ := h2
  refine ⟨n', y ∘ Equiv.swap j ρ, ρ, hn', by rw [hy, hrange], hZ'', 𝔮, hprime, hle, e,
    fun c => ?_⟩
  obtain ⟨V, hV, s, rfl⟩ := X.presheaf.exists_germ_eq c
  exact he V hV hV s

/-- `π^♯ : 𝒪_{X,π q} → 𝒪_{B,q}` is injective at every point `q` over the center: through the chart
bridge it is `𝒪_{X,x} → 𝒪_{X,x}[y_i/y_ρ] → 𝒪_{X,x}[y_i/y_ρ]_𝔮`, the inclusion of a domain into a
localization at a nonzero element followed by a localization of a domain. -/
theorem injective_stalkMap_blowUpπ_of_mem (q : Z.blowUp)
    (hq : Z.blowUpπ q ∈ Z.support) :
    Function.Injective (Z.blowUpπ.stalkMap q) := by
  obtain ⟨n', y, ρ, hn', hy, -, 𝔮, hprime, -, e, he⟩ :=
    exists_stalk_equiv_localization_chart_of_smooth f Z q hq
  have hreg := isRegularLocalRing_stalk f (Z.blowUpπ q)
  have hdom : IsDomain (Localization.Away (y ρ)) := isDomain_away y ρ hy hn'
  have hinj1 : Function.Injective
      (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ)) := by
    intro a b hab
    have hab' : algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (Localization.Away
        (y ρ)) a =
        algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (Localization.Away
            (y ρ)) b :=
      congrArg Subtype.val hab
    exact IsLocalization.injective (Localization.Away (y ρ))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (x_ne_zero_of_span_eq y hy hn' ρ)) hab'
  have hinj2 : Function.Injective (algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)) :=
    IsLocalization.injective (Localization.AtPrime 𝔮) 𝔮.primeCompl_le_nonZeroDivisors
  intro a b hab
  have h := congrArg e hab
  rw [he, he] at h
  exact hinj1 (hinj2 h)

/-- Nonvanishing under one blow-up, at the level of controlled transforms: if `I` is nonzero at
every point of `X`, every controlled transform `(π^* I : F^m)` is nonzero at every point of
`B_Z X`; over the center by injectivity of `π^♯`, off it because `π` is an isomorphism there and
the order is finite. Condition (2) of [Kol07, Notation 64] is thereby preserved. -/
theorem stalkIdeal_controlledTransform_ne_bot (I : X.IdealSheafData)
    (hI : IsNonzeroEverywhere I) (m : ℕ) (q : Z.blowUp) :
    (I.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor m).stalkIdeal q ≠ ⊥ := by
  intro h0
  have hle : (I.comap Z.blowUpπ).stalkIdeal q ≤
      (I.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor m).stalkIdeal q :=
    stalkIdeal_mono (comap_le_controlledTransformAlong _ _ I m) q
  by_cases hq : Z.blowUpπ q ∈ Z.support
  · have h1 : (I.comap Z.blowUpπ).stalkIdeal q = ⊥ := le_bot_iff.mp (h0 ▸ hle)
    rw [stalkIdeal_comap,
      Ideal.map_eq_bot_iff_of_injective (injective_stalkMap_blowUpπ_of_mem f Z q hq)] at h1
    exact hI _ h1
  · have : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
    have : IsProper (Scheme.IdealSheafData.blowUpπ Z) := blowUp.isProper_π Z
    have : IsLocallyNoetherian Z.blowUp :=
        (Z.blowUpπ ≫ f).isLocallyNoetherian_of_field
    have h2 : (I.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor m).ord q ≤
        I.ord (Z.blowUpπ q) :=
      ord_controlledTransform_le_of_notMem Z I m q hq
    rw
        [(Scheme.IdealSheafData.ord_eq_top_iff _ q).mpr h0, top_le_iff,
            Scheme.IdealSheafData.ord_eq_top_iff] at h2
    exact hI _ h2

end Center

/-! ### Generic points of irreducible components -/

section GenericPoint

/-- The only generization of a generic point of an irreducible component is the point itself:
`closure {ξ} ⊇ W` is irreducible, so equals `W` by maximality, and `W` has one generic point. -/
theorem eq_of_specializes_of_isGenericPoint_of_mem_irreducibleComponents {W : Set X}
    (hW : W ∈ irreducibleComponents X) {η ξ : X} (hη : IsGenericPoint η W) (hξ : ξ ⤳ η) :
    ξ = η := by
  have hsub : W ⊆ closure {ξ} := by
    rw [← hη.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hξ))
      isClosed_closure
  have hgen : IsGenericPoint ξ W := hW.eq_of_ge isIrreducible_singleton.closure hsub
  exact hgen.eq hη

/-- `Spec 𝒪_{X,η}` is a point when `η` is a generic point of an irreducible component: its points
are the generizations of `η` (`range_fromSpecStalk`), and `Spec 𝒪_{X,η} → X` is injective. -/
theorem subsingleton_primeSpectrum_stalk_of_isGenericPoint {W : Set X}
    (hW : W ∈ irreducibleComponents X) {η : X} (hη : IsGenericPoint η W) :
    Subsingleton (PrimeSpectrum (X.presheaf.stalk η)) := by
  refine ⟨fun p q => ?_⟩
  have key : ∀ p : PrimeSpectrum (X.presheaf.stalk η), X.fromSpecStalk η p = η := by
    intro p
    have hmem : X.fromSpecStalk η p ∈ Set.range (X.fromSpecStalk η) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hmem
    exact eq_of_specializes_of_isGenericPoint_of_mem_irreducibleComponents hW hη hmem
  exact (X.fromSpecStalk η).isEmbedding.injective ((key p).trans (key q).symm)

/-- At a generic point of an irreducible component, a domain stalk is a field: its spectrum is a
point, so its Krull dimension is `0`. -/
theorem maximalIdeal_stalk_eq_bot_of_isGenericPoint {W : Set X} (hW : W ∈ irreducibleComponents X)
    {η : X} (hη : IsGenericPoint η W) [IsDomain (X.presheaf.stalk η)] :
    maximalIdeal (X.presheaf.stalk η) = ⊥ := by
  have := subsingleton_primeSpectrum_stalk_of_isGenericPoint hW hη
  have : Ring.KrullDimLE 0 (X.presheaf.stalk η) :=
    Ring.krullDimLE_iff.mpr (by simpa [ringKrullDim] using
      Order.krullDim_nonpos_of_subsingleton (α := PrimeSpectrum (X.presheaf.stalk η)))
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mp Ring.KrullDimLE.isField_of_isDomain

/-- A generic point of an irreducible component of `X` lying in a closed `Z` is a generic point of
`Z` (in the sense of `Closeds.genericPoints`). -/
theorem mem_genericPoints_of_isGenericPoint_of_mem {W : Set X} (hW : W ∈ irreducibleComponents X)
    {η : X} (hη : IsGenericPoint η W) (Z : Closeds X) (hηZ : η ∈ Z) : η ∈ Z.genericPoints :=
  ⟨hηZ, fun _ _ hξ => eq_of_specializes_of_isGenericPoint_of_mem_irreducibleComponents hW hη hξ⟩

/-- On a smooth `X`, a closed subscheme `Z` along which an everywhere-nonzero `I` has order
`≥ m ≥ 1` contains no irreducible component of `X`: at the generic point of such a component the
stalk is a field, so `I_η ⊆ 𝔪_η^m = 0`. This is why codimension-one components of the cosupport
need separate treatment, Kollár's remark after [Kol07, Lemma 62]. -/
theorem not_subset_support_of_leOrdAlong (f : X ⟶ Spec (.of k)) [Smooth f]
    (Z I : X.IdealSheafData) (hI : IsNonzeroEverywhere I) {m : ℕ} (hm : 1 ≤ m)
    (hord : I.LeOrdAlong Z.support (m : ℕ∞)) {W : Set X} (hW : W ∈ irreducibleComponents X) :
    ¬ W ⊆ (Z.support : Set X) := by
  intro hsub
  have hirr : IsIrreducible W := hW.prop
  have hη : IsGenericPoint hirr.genericPoint W :=
    hirr.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
  have hgen : hirr.genericPoint ∈ Z.support.genericPoints :=
    mem_genericPoints_of_isGenericPoint_of_mem hW hη Z.support (hsub hη.mem)
  have h1 : (m : ℕ∞) ≤ I.ord hirr.genericPoint := hord _ hgen
  have hreg := isRegularLocalRing_stalk f hirr.genericPoint
  have hmax := maximalIdeal_stalk_eq_bot_of_isGenericPoint hW hη
  have h2 : I.stalkIdeal hirr.genericPoint ≤
      maximalIdeal (X.presheaf.stalk hirr.genericPoint) ^ m :=
          (Scheme.IdealSheafData.le_ord_iff I _).mp h1
  rw [hmax, Ideal.bot_pow (by omega : m ≠ 0)] at h2
  exact hI _ (le_bot_iff.mp h2)

end GenericPoint

/-! ### The blow-up of a smooth center of any shape is smooth -/

section BlowUpSmooth

variable [PerfectField k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)]

include f n

/-- Adapted coordinates at a closed point of a smooth center: `n` parameters generating `𝔪_x`,
the first `c` generating `Z_x`. -/
theorem exists_adaptedCoordinates_of_smooth {x : X} (hxZ : x ∈ Z.support)
    (hx : IsClosed ({x} : Set X)) :
    ∃ (c : ℕ) (y : Fin n → X.presheaf.stalk x), c ≤ n ∧
      maximalIdeal (X.presheaf.stalk x) = Ideal.span (Set.range y) ∧
      Z.stalkIdeal x = Ideal.span (y '' {j | j.val < c}) := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨m, c, y, hcm, hm, hspan, hI⟩ := exists_adaptedParameters_of_smooth f Z hxZ
  have hn := Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed f n hx
  rw [hn] at hm
  obtain rfl : m = n := by exact_mod_cast hm
  exact ⟨c, y, hcm, hspan, hI⟩

/-- Étale coordinates adapted to a smooth center at a closed point, with the local codimension:
the proof of `nonempty_etaleCoordinatesAdapted` from `exists_adaptedCoordinates_of_smooth`. -/
theorem exists_etaleCoordinatesAdapted_of_smooth {x : X} (hxZ : x ∈ Z.support)
    (hx : IsClosed ({x} : Set X)) : ∃ r : ℕ, Nonempty (EtaleCoordinatesAdapted f n r Z x) := by
  classical
  let _ := f.stalkAlgebra x
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨r, y, -, hspan, hZ⟩ := exists_adaptedCoordinates_of_smooth f n Z hxZ hx
  refine ⟨r, ?_⟩
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV₀, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨V, hxV, -, w, hw⟩ := exists_affineOpen_germ_eq ⟨V₀, hV₀⟩ hxV₀ y
  obtain ⟨b, hb⟩ := exists_basis_tensor_kaehlerDifferential_of_span_eq_maximalIdeal f n hx y hspan
  have hb' : ∃ b' : Module.Basis (Fin n) (ResidueField (X.presheaf.stalk x))
      (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k]),
      ∀ i, b' i = 1 ⊗ₜ D k (X.presheaf.stalk x) (X.presheaf.germ V.1 x hxV (w i)) :=
    ⟨b, fun i => by rw [hb i, hw i]⟩
  obtain ⟨U, hxU, hUV, hE⟩ := exists_etale_toAffineSpace_of_basis f n V hxV w hb'
  set w' : Fin n → Γ(X, U.1) := fun i => X.presheaf.map (homOfLE hUV).op (w i) with hw'def
  have hZ' : Z.stalkIdeal x =
      Ideal.span ((fun i => X.presheaf.germ U.1 x hxU (w' i)) '' {i | i.val < r}) := by
    rw [hZ]
    congr 1
    refine Set.image_congr fun i _ => ?_
    rw [hw'def]
    change y i = X.presheaf.germ U.1 x hxU (X.presheaf.map (homOfLE hUV).op (w i))
    rw [X.presheaf.germ_res_apply, hw i]
  obtain ⟨U', hxU', hU'U, hAd⟩ :=
    exists_comap_eq_comap_coordinateSubspace f n r Z U hxU w' hZ'
  have : Etale (toAffineSpace f U.1 w') := hE
  exact ⟨⟨U', hxU', fun i => X.presheaf.map (homOfLE hU'U).op (w' i),
    etale_toAffineSpace_restrict f hU'U w', hAd⟩⟩

/-- The blow-up of an equidimensional smooth scheme along a smooth center of any shape is smooth
of the same relative dimension ("if `π_{Z,X}` is a smooth blow-up, then `F` and `B_Z X` are both
smooth", [Kol07, Notation 19]). Smoothness is Zariski local on the source; it is checked over the
complement of the center and on the charts of adapted étale coordinates at the closed points of
the center, each with its own codimension. -/
theorem smoothOfRelativeDimension_blowUpπ_comp_of_smooth :
    SmoothOfRelativeDimension n (Z.blowUpπ ≫ f) := by
  classical
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} n) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsJacobsonRing k := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  let E : ∀ x : {x : X // IsClosed ({x} : Set X) ∧ x ∈ Z.support},
      Σ r : ℕ, EtaleCoordinatesAdapted f n r Z x.1 :=
    fun x => Classical.choice (by
      obtain ⟨r, ⟨e⟩⟩ := exists_etaleCoordinatesAdapted_of_smooth f n Z x.2.2 x.2.1
      exact ⟨⟨r, e⟩⟩)
  let V : Option {x : X // IsClosed ({x} : Set X) ∧ x ∈ Z.support} → X.Opens :=
    fun o => o.elim Z.support.compl fun x => (E x).2.U.1
  have hV : iSup V = ⊤ := by
    rw [← iSup_eq_top_of_forall_isClosed Z (fun x => (E x).2.U.1) fun x => (E x).2.mem]
    apply le_antisymm
    · refine iSup_le fun o => ?_
      cases o with
      | none => exact le_sup_right
      | some x => exact (le_iSup (fun x => (E x).2.U.1) x).trans le_sup_left
    · exact sup_le (iSup_le fun x => le_iSup V (some x)) (le_iSup V none)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{u} n)
    (fun o => Scheme.IdealSheafData.blowUpπ Z ⁻¹ᵁ V o) ?_ fun o => ?_
  · rw [← Scheme.Hom.preimage_iSup, hV, Scheme.Hom.preimage_top]
  · rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    cases o with
    | none => exact smoothOfRelativeDimension_restrict_compl_support f n Z
    | some x => exact smoothOfRelativeDimension_restrict_of_etaleCoordinates (E x).2

/-- `B_Z X` is smooth over `k` for a smooth center of any shape [Kol07, Notation 19]. -/
theorem smooth_blowUpπ_comp_of_smooth : Smooth (Z.blowUpπ ≫ f) := by
  have := smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n Z
  exact SmoothOfRelativeDimension.smooth n _

end BlowUpSmooth

end AlgebraicGeometry
