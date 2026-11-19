/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Balanced.Basic
public import Hironaka.Resolution.Algebraic.BoundaryClearing.Data
import Hironaka.Resolution.Algebraic.Balanced.Order
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.BoundaryClearing.Center
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Transform.TransformIso
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Invariance
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.SubschemeStalk
import Hironaka.Scheme.Snc.HasSncWith
import Hironaka.Scheme.Snc.TrivialSncData
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The new ideal `I_0`

The proof of [Kol07, Lemma 102] continues: the blow-up `π_{-1}` of `Z_{-1}` is an isomorphism, but
the order of `I` along the selected components `E^{jk}` drops by `m`, giving a new ideal sheaf
`I_0`; since the order of `I` along `E^{jk}` was at most `m`, it is now `0`, so `cosupp(I_0, m)`
contains no irreducible component of `E^j`.

**The transform.** `Z_{-1}` is a smooth center with `ord_{Z_{-1}} I = m` (`Center.lean`), so
Kollár's formula (58.1) for the birational transform ([Kol07, 58]) is the marked transform
`I_0 = (π^* I : F^m)` (`weakTransform_eq_markedTransform_of_smooth`,
`Hironaka/Scheme/BlowUpSequence/OrderAlongCenter.lean`), and `F^m` divides `π^* I`
(`pow_dvd_comap_of_leOrdAlong`), so `F^m · I_0 = π^* I`
(`exceptionalDivisor_pow_mul_weakTransform`).

**Over `Z_{-1}`.** At a point `x` of the exceptional divisor `F` (which is `Z_{-1}` under the
isomorphism `π`), `ord_x (F^m · I_0) ≥ m · ord_x F + ord_x I_0 ≥ m + ord_x I_0` (superadditivity
of the order) while `ord_x (π^* I) = ord_{π x} I ≤ max-ord I = m`; hence `ord_x I_0 = 0`
(`ord_weakTransform_eq_zero_of_mem_exceptional`).

**Off `Z_{-1}`.** The birational transform of `E^j` is `(E^j : Z_{-1}^∞)` carried along the
isomorphism (`strictTransformAlong_of_isIso`, `Hironaka/Scheme/BlowUp/Transform/TransformIso.lean`);
its points are the points of `E^j` off `Z_{-1}` (on `Z_{-1}` the stalks of `E^j` and `Z_{-1}` agree
and the saturation is the unit ideal; off `Z_{-1}` the saturation is `E^j` itself). A generic point
`η` of the birational transform maps to a generic point of `E^j` which is NOT selected into `Z_{-1}`
(`exists_genericPoint_of_mem_genericPoints_strictTransform`: a generic point of `E^j`
specializing to `π η` lies off `Z_{-1}`, hence on the saturation, and `η` is maximal there). Since
`π^* I ⊆ I_0`, `ord_η I_0 ≤ ord_{π η} I < m` (`ord_weakTransform_lt_of_mem_genericPoints`, no
D-balancedness needed), and for D-balanced `I` the dichotomy of `Basic.lean` gives
`ord_{π η} I = 0`, so `ord_η I_0 = 0` (`ord_weakTransform_eq_zero_of_mem_genericPoints`); at such
a generic point the stalk of `I_0` is the unit ideal, so its restriction to the birational
transform of `E^j` is nonzero on every irreducible component
(`isNonzeroEverywhere_comap_weakTransform`, through `isNonzeroEverywhere_iff_irreducibleComponents`
of `Hironaka/Scheme/BlowUpSequence/InducedData.lean` on the subscheme: the generic points of its
irreducible components are the generic points of the closed set under the closed embedding). This
last statement, the nonvanishing required of the ideal of a triple ([Kol07, Definition 31, (1)]), is
not made explicit by Kollár. Used by `Restriction.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Hironaka Scheme.BlowUpSequence IsLocalRing

namespace Hironaka.BD

variable {k : Type u} [Field k]

/-! ### Kollár's formula (58.1) -/

/-- For `max-ord I = m`, `F^m · I_0 = π_{-1}^* I` (Kollár's formula (58.1), [Kol07, 58], and its
Warning on the trivial blow-up of a smooth divisor): `I_0` is the marked transform with control `m`
and `F^m` divides `π^* I`. -/
theorem exceptionalDivisor_pow_mul_weakTransform [CharZero k] (T : Triple k) (m : ℕ) (j : T.E.ι)
    (hmax : T.I.maxOrd = m) :
    (Zminus1 T.I m (T.E.component j)).exceptionalDivisor ^ m *
        T.I.weakTransform (Zminus1 T.I m (T.E.component j)) =
      T.I.comap (Zminus1 T.I m (T.E.component j)).blowUpπ := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have := smooth_Zminus1 T m j
  have hord := ordAlongEq_Zminus1 T m j hmax
  rw [weakTransform_eq_markedTransform_of_smooth (T.X.left ↘ Spec (.of k)) n _ T.I
    hord, markedTransform_eq_colon]
  exact pow_mul_colon_of_dvd _ _ _ (pow_dvd_comap_of_leOrdAlong
    (T.X.left ↘ Spec (.of k)) n _ T.I fun η hη => (hord η hη).ge)

/-! ### Over `Z_{-1}` -/

/-- For `max-ord I = m`, `I_0` has order `0` at every point over `Z_{-1}`
(`m + ord_x I_0 ≤ ord_x (F^m · I_0) = ord_{π x} I ≤ m`): the order along `E^{jk}` is "reduced by
`m`" in the proof of [Kol07, Lemma 102]. -/
theorem ord_weakTransform_eq_zero_of_mem_exceptional [CharZero k] (T : Triple k) (m : ℕ)
    (j : T.E.ι) (hmax : T.I.maxOrd = m) {x : (Zminus1 T.I m (T.E.component j)).blowUp}
    (hx : x ∈ (Zminus1 T.I m (T.E.component j)).exceptionalDivisor.support) :
    (T.I.weakTransform (Zminus1 T.I m (T.E.component j))).ord x = 0 := by
  have h58 := exceptionalDivisor_pow_mul_weakTransform T m j hmax
  have hiso := isIso_blowUpπ_Zminus1 T m j
  have h1 : (T.I.comap (Zminus1 T.I m (T.E.component j)).blowUpπ).ord x ≤ m := by
    rw [ord_comap_of_isIso]
    exact hmax ▸ T.I.le_maxOrd _
  have hF : (1 : ℕ∞) ≤ IsLocalRing.ord
      ((Zminus1 T.I m (T.E.component j)).exceptionalDivisor.stalkIdeal x) := by
    rw [← ord_eq_ord_stalkIdeal]; exact (one_le_ord_iff _ _).mpr hx
  have h2 : (m : ℕ∞) + (T.I.weakTransform (Zminus1 T.I m (T.E.component j))).ord x ≤
      ((Zminus1 T.I m (T.E.component j)).exceptionalDivisor ^ m *
        T.I.weakTransform (Zminus1 T.I m (T.E.component j))).ord x := by
    simp only [ord_eq_ord_stalkIdeal]
    rw [stalkIdeal_mul, stalkIdeal_pow]
    refine le_trans (add_le_add ?_ le_rfl) (le_ord_mul _ _)
    calc (m : ℕ∞) = (m : ℕ∞) * 1 := (mul_one _).symm
      _ ≤ (m : ℕ∞) * IsLocalRing.ord
          ((Zminus1 T.I m (T.E.component j)).exceptionalDivisor.stalkIdeal x) :=
          mul_le_mul' le_rfl hF
      _ ≤ _ := le_ord_pow _ _
  rw [h58] at h2
  have h3 : (m : ℕ∞) + (T.I.weakTransform (Zminus1 T.I m (T.E.component j))).ord x ≤
      (m : ℕ∞) + 0 := by
    rw [add_zero]
    exact h2.trans h1
  exact le_antisymm ((ENat.add_le_add_iff_left (ENat.natCast_ne_top m)).mp h3) zero_le

/-! ### Off `Z_{-1}`: the birational transform of `E^j` -/

/-- The points of the saturation `(E^j : Z_{-1}^∞)` are the points of `E^j` off `Z_{-1}`: on
`Z_{-1}` the stalks of `E^j` and `Z_{-1}` agree and the saturation is the unit ideal; off `Z_{-1}`
the colon by the unit ideal does not change `E^j`. -/
theorem mem_support_saturate_iff (T : Triple k) (m : ℕ) (j : T.E.ι) (x : T.X.left) :
    x ∈ ((T.E.component j).saturate (Zminus1 T.I m (T.E.component j))).support ↔
      x ∈ (T.E.component j).support ∧ x ∉ (Zminus1 T.I m (T.E.component j)).support := by
  have hinv := isInvertible_Zminus1 T m j
  constructor
  · intro hx
    refine ⟨support_antitone (le_saturate _ _) hx, fun hxZ => ?_⟩
    exact notMem_support_saturate_of_stalkIdeal_eq _ _ hinv
      (stalkIdeal_Zminus1_eq T m j hxZ).symm hx
  · rintro ⟨hxE, hxZ⟩
    rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_saturate_of_isInvertible _ hinv,
      stalkIdeal_eq_top_of_notMem_support _ hxZ]
    refine iSup_le fun i => ?_
    rw [Ideal.top_pow]
    intro r hr
    have := Submodule.mem_colon.mp hr 1 Submodule.mem_top
    rw [smul_eq_mul, mul_one] at this
    exact (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp hxE this

/-- The birational transform of `E^j` under the trivial blow-up is the saturation `(E^j : Z_{-1}^∞)`
carried along the isomorphism `π_{-1}` (`strictTransformAlong_of_isIso`). -/
theorem strictTransform_eq_comap_saturate (T : Triple k) (m : ℕ) (j : T.E.ι) :
    (T.E.component j).strictTransform (Zminus1 T.I m (T.E.component j)) =
      ((T.E.component j).saturate (Zminus1 T.I m (T.E.component j))).comap
        (Zminus1 T.I m (T.E.component j)).blowUpπ := by
  have := isIso_blowUpπ_Zminus1 T m j
  exact strictTransformAlong_of_isIso _ _ _

/-- A generic point of the birational transform of `E^j` maps under `π_{-1}` to a generic point of
`E^j` that is NOT selected into `Z_{-1}`. -/
theorem exists_genericPoint_of_mem_genericPoints_strictTransform (T : Triple k)
    (m : ℕ) (j : T.E.ι) {η : (Zminus1 T.I m (T.E.component j)).blowUp}
    (hη : η ∈ ((T.E.component j).strictTransform
        (Zminus1 T.I m (T.E.component j))).support.genericPoints) :
    (Zminus1 T.I m (T.E.component j)).blowUpπ η ∈
        (T.E.component j).support.genericPoints ∧
      ¬ (m : ℕ∞) ≤ T.I.ord ((Zminus1 T.I m (T.E.component j)).blowUpπ η) := by
  have hiso := isIso_blowUpπ_Zminus1 T m j
  have hN := noetherianSpace_triple T
  have hcoe := Set.ext_iff.mp (coe_support_Zminus1 T.I m (T.E.component j))
  obtain ⟨hηS, hmax⟩ := hη
  rw [strictTransform_eq_comap_saturate T m j] at hηS hmax
  have hmem : ∀ y : (Zminus1 T.I m (T.E.component j)).blowUp,
      y ∈ (((T.E.component j).saturate (Zminus1 T.I m (T.E.component j))).comap
        (Zminus1 T.I m (T.E.component j)).blowUpπ).support ↔
      (Zminus1 T.I m (T.E.component j)).blowUpπ y ∈
        ((T.E.component j).saturate (Zminus1 T.I m (T.E.component j))).support := fun y => by
    rw [support_comap]; exact Iff.rfl
  obtain ⟨hπE, hπZ⟩ := (mem_support_saturate_iff T m j _).mp ((hmem η).mp hηS)
  obtain ⟨ξ, hξ, hξη⟩ := Closeds.exists_mem_genericPoints_specializes _ hπE
  have hξZ : ξ ∉ (Zminus1 T.I m (T.E.component j)).support := fun h =>
    hπZ (hξη.mem_closed (Zminus1 T.I m (T.E.component j)).support.isClosed h)
  -- the preimage `ξ'` of `ξ` lies on the birational transform and specializes to `η`
  set π := (Zminus1 T.I m (T.E.component j)).blowUpπ with hπ
  have hπinv : ∀ y, π (inv π y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  have hinvπ : ∀ y, inv π (π y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have hξ'S : inv π ξ ∈ (((T.E.component j).saturate (Zminus1 T.I m (T.E.component j))).comap
      π).support := by
    rw [hmem, hπinv]
    exact (mem_support_saturate_iff T m j ξ).mpr ⟨hξ.1, hξZ⟩
  have hξ'η : inv π ξ ⤳ η := by
    have := hξη.map (inv π).base.hom.continuous
    rwa [hinvπ] at this
  have heq : inv π ξ = η := hmax hξ'S hξ'η
  have hπη : π η = ξ := by rw [← heq, hπinv]
  rw [hπη]
  refine ⟨hξ, fun hle => hξZ ?_⟩
  exact (hcoe ξ).mpr ⟨ξ, hξ, hle, specializes_refl _⟩

/-- For `max-ord I = m`, no generic point of the birational transform of `E^j` lies in
`cosupp(I_0, m)` ("`cosupp(I_0, m)` does not contain any irreducible component of `E^j`", the proof
of [Kol07, Lemma 102]): `π^* I ⊆ I_0` and `π η` is a non-selected generic point of `E^j`. Neither
D-balancedness nor `m ≥ 1` is needed. -/
theorem ord_weakTransform_lt_of_mem_genericPoints (T : Triple k) (m : ℕ) (j : T.E.ι)
    (_hmax : T.I.maxOrd = m) {η : (Zminus1 T.I m (T.E.component j)).blowUp}
    (hη : η ∈ ((T.E.component j).strictTransform
        (Zminus1 T.I m (T.E.component j))).support.genericPoints) :
    (T.I.weakTransform (Zminus1 T.I m (T.E.component j))).ord η < m := by
  have hiso := isIso_blowUpπ_Zminus1 T m j
  obtain ⟨-, hlt⟩ := exists_genericPoint_of_mem_genericPoints_strictTransform T m j hη
  rw [not_le] at hlt
  calc (T.I.weakTransform (Zminus1 T.I m (T.E.component j))).ord η
      ≤ (T.I.comap (Zminus1 T.I m (T.E.component j)).blowUpπ).ord η :=
        Scheme.IdealSheafData.ord_anti (comap_le_controlledTransformAlong _ _ _ _) η
    _ = T.I.ord ((Zminus1 T.I m (T.E.component j)).blowUpπ η) :=
        ord_comap_of_isIso _ _ _
    _ < m := hlt

/-- For D-balanced `I` with `max-ord I = m`, `I_0` has order `0` along every irreducible component
of the birational transform of `E^j` (the dichotomy of `Basic.lean`: at a non-selected generic
point `ord I = 0`). -/
theorem ord_weakTransform_eq_zero_of_mem_genericPoints [CharZero k] (T : Triple k) (m : ℕ)
    (j : T.E.ι) (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m)
    {η : (Zminus1 T.I m (T.E.component j)).blowUp}
    (hη : η ∈ ((T.E.component j).strictTransform
        (Zminus1 T.I m (T.E.component j))).support.genericPoints) :
    (T.I.weakTransform (Zminus1 T.I m (T.E.component j))).ord η = 0 := by
  have hiso := isIso_blowUpπ_Zminus1 T m j
  obtain ⟨hgen, hlt⟩ := exists_genericPoint_of_mem_genericPoints_strictTransform T m j hη
  have h0 : T.I.ord ((Zminus1 T.I m (T.E.component j)).blowUpπ η) = 0 := by
    rcases ord_eq_zero_or_eq_of_mem_genericPoints T m j hI hmax hgen with h | h
    · exact h
    · exact absurd h.ge hlt
  refine le_antisymm ?_ zero_le
  calc (T.I.weakTransform (Zminus1 T.I m (T.E.component j))).ord η
      ≤ (T.I.comap (Zminus1 T.I m (T.E.component j)).blowUpπ).ord η :=
        Scheme.IdealSheafData.ord_anti (comap_le_controlledTransformAlong _ _ _ _) η
    _ = T.I.ord ((Zminus1 T.I m (T.E.component j)).blowUpπ η) :=
        ord_comap_of_isIso _ _ _
    _ = 0 := h0

/-- For D-balanced `I` with `max-ord I = m`, the restriction of `I_0` to the birational transform
of `E^j` is nonzero on every irreducible component (the requirement on the ideal of a triple,
[Kol07, Definition 31, (1)]): at the generic point of each component the stalk of `I_0` is the unit
ideal. -/
theorem isNonzeroEverywhere_comap_weakTransform [CharZero k] (T : Triple k) (m : ℕ) (j : T.E.ι)
    (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m) :
    IsNonzeroEverywhere ((T.I.weakTransform (Zminus1 T.I m (T.E.component j))).comap
      ((T.E.component j).strictTransform (Zminus1 T.I m (T.E.component j))).subschemeι) := by
  rw [isNonzeroEverywhere_iff_irreducibleComponents]
  intro W hW s hs
  have hη : ((T.E.component j).strictTransform (Zminus1 T.I m (T.E.component j))).subschemeι s ∈
      ((T.E.component j).strictTransform
          (Zminus1 T.I m (T.E.component j))).support.genericPoints := by
    have hs' : s ∈ (⊤ : Closeds
        ((T.E.component j).strictTransform
        (Zminus1 T.I m (T.E.component j))).subscheme).genericPoints :=
      mem_genericPoints_of_isGenericPoint_of_mem hW hs ⊤ trivial
    refine ⟨subschemeι_mem_support _ s, fun η' hη' hspec => ?_⟩
    obtain ⟨s', rfl⟩ := Scheme.IdealSheafData.exists_subschemeι_eq _ hη'
    have h1 : s' ⤳ s := (Scheme.Hom.isClosedEmbedding _).isInducing.specializes_iff.mp hspec
    rw [hs'.2 trivial h1]
  have h0 := ord_weakTransform_eq_zero_of_mem_genericPoints T m j hI hmax hη
  rw [stalkIdeal_comap, stalkIdeal_eq_top_of_ord_eq_zero h0, Ideal.map_top]
  exact top_ne_bot

end Hironaka.BD
