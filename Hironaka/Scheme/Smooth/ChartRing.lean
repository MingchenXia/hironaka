/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Defs
public import Hironaka.Algebra.Local.ChartRing
import Hironaka.Algebra.Local.Chart
import Hironaka.Algebra.Local.ChartLocal

/-!
# The chart ring of the blow-up along the first `r` coordinates

Two descriptions of the chart of a blow-up along `I = (x_0, …, x_r)` at `a = x_r` coincide. The
affine blow-up algebra `R[I/a] = {z/aᵐ : z ∈ Iᵐ} ⊆ R[1/a]` (Hauser's local blow-up,
[Hau14, Definition 4.16]) is the ring that glues to the blow-up; Kollár's chart ring
`R' = R[x_i/x_r : i < r] ⊆ R[1/x_r]` is the ring of the coordinates (60.2) of
[Kol07, Definition 60] (`chartRing` of `Hironaka/Algebra/Local/Chart.lean`). They are the same
subalgebra (`affineBlowUpAlgebra_span_eq_chartRing`): a fraction `z/x_rᵐ` with `z` a product of `m`
generators is a monomial in the `x_i/x_r`. Through this identification the standard chart of
`x_r` of `B_Z X` is the ring map `R → R'`, and the theorems about `R'` and its origin
`𝔪' = (y_1, …, y_n)` of `Hironaka/Algebra/Local/ChartLocal.lean` are statements about the local ring
of `B_Z X` at the origin of the chart.

At the ring level the file also shows: in adapted coordinates the chart ring of the local blow-up
`B_{I_x} Spec 𝒪_{X,x}` is `chartRing y ρ` (`affineBlowUpAlgebra_stalkIdeal_eq_chartRing`); the
`y_i` are a regular system of parameters of `R'_𝔮` exactly when `𝔮 = 𝔪'`
(`maximalIdeal_localization_eq_span_iff`); and every `κ`-rational point of the fibre in the chart
is the origin after a linear change of the first `r` coordinates (`exists_eq_chartOriginAt`,
`chartOriginAt`), as in the proof of [Kol07, Lemma 61]: "every preimage of `p` appears as the
origin after a suitable linear change". Used for the local blow-up
(`Hironaka/Scheme/Smooth/LocalBlowUp.lean`) and for the order of an ideal along the exceptional
divisor (`Hironaka/Scheme/IdealSheaf/Order/ExceptionalOrder.lean`).
-/

public section

open IsLocalRing

universe u

namespace AlgebraicGeometry

open AlgebraicGeometry IsLocalRing

section Identification

variable {R : Type u} [CommRing R] {n : ℕ} (x : Fin n → R) (r : Fin n)

/-- The affine blow-up algebra `R[I/x_r]` for `I = (x_i : i ≤ r)` ([Hau14, Definition 4.16]) is
Kollár's chart ring `R' = R[x_i/x_r : i < r]` ([Kol07, Definition 60, (60.2)]), as subalgebras of
`R[1/x_r]`. -/
theorem affineBlowUpAlgebra_span_eq_chartRing :
    affineBlowUpAlgebra (Ideal.span (x '' {i | i ≤ r})) (x r) = chartRing x r := by
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨z, hz, rfl⟩
    refine Submodule.span_induction
      (p := fun z _ => Localization.mk z ⟨x r, Submonoid.mem_powers _⟩ ∈ chartRing x r)
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨i, hi, rfl⟩
      rcases lt_or_eq_of_le (show i ≤ r from hi) with h | h
      · exact Algebra.subset_adjoin ⟨i, h, rfl⟩
      · subst h
        rw [Localization.mk_self ⟨x i, Submonoid.mem_powers _⟩]
        exact Subalgebra.one_mem _
    · rw [Localization.mk_zero]
      exact Subalgebra.zero_mem _
    · intro a b _ _ ha hb
      rw [← Localization.add_mk_self]
      exact Subalgebra.add_mem _ ha hb
    · intro c a _ ha
      rw [← Localization.smul_mk]
      exact Subalgebra.smul_mem _ ha c
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨i, hi, rfl⟩
    exact Algebra.subset_adjoin ⟨x i, Ideal.subset_span ⟨i, show i ≤ r from le_of_lt hi, rfl⟩, rfl⟩

end Identification

/-- In adapted coordinates `y` at `x` (`I_x = (y_0, …, y_{r-1})`), the chart ring of `y_ρ`
(`ρ = r − 1`) of the local blow-up `B_{I_x} Spec 𝒪_{X,x}` is the chart ring `chartRing y ρ` of
Kollár's coordinates (60.2) ([Kol07, Definition 60]). -/
theorem affineBlowUpAlgebra_stalkIdeal_eq_chartRing {X : AlgebraicGeometry.Scheme.{u}}
    (Z : X.IdealSheafData) (x : X) {n r : ℕ} {y : Fin n → X.presheaf.stalk x}
    (hZ : Z.stalkIdeal x = Ideal.span (y '' {i | i.val < r})) (ρ : Fin n) (hρ : ρ.val + 1 = r) :
    affineBlowUpAlgebra (Z.stalkIdeal x) (y ρ) = chartRing y ρ := by
  have hset : {i : Fin n | i.val < r} = {i | i ≤ ρ} := by
    ext i
    change i.val < r ↔ i ≤ ρ
    rw [Fin.le_def, ← hρ]
    exact Nat.lt_succ_iff
  rw [hZ, hset]
  exact affineBlowUpAlgebra_span_eq_chartRing y ρ

section Fibre

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {n : ℕ} (x : Fin n → R) (r : Fin n)
  (hx : maximalIdeal R = Ideal.span (Set.range x)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)

include hx hn

/-- At a prime `𝔮` of the chart ring `R'`, the chart functions `y_i` form a regular system of
parameters of `R'_𝔮` exactly when `𝔮` is the origin `𝔪' = (y_1, …, y_n)` of the chart; the "if" is
`maximalIdeal_localization_chartOrigin` of `Hironaka/Algebra/Local/ChartLocal.lean`. -/
theorem maximalIdeal_localization_eq_span_iff (𝔮 : Ideal (chartRing x r)) [𝔮.IsPrime] :
    maximalIdeal (Localization.AtPrime 𝔮) =
        Ideal.span (Set.range fun i => algebraMap (chartRing x r) (Localization.AtPrime 𝔮)
          (chartYR x r i)) ↔
      𝔮 = chartOrigin x r := by
  constructor
  · intro h
    have hle : chartOrigin x r ≤ 𝔮 := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      have hmem : algebraMap (chartRing x r) (Localization.AtPrime 𝔮) (chartYR x r i) ∈
          maximalIdeal (Localization.AtPrime 𝔮) := by
        rw [h]
        exact Ideal.subset_span ⟨i, rfl⟩
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔮) 𝔮 _).mp hmem
    exact ((chartOrigin_isMaximal x r hx hn).eq_of_le ‹𝔮.IsPrime›.ne_top hle).symm
  · rintro rfl
    exact maximalIdeal_localization_chartOrigin x r

/-- Every `κ`-rational point of the fibre in the chart of `x_r` (a prime `𝔮` of `R'` over `𝔪` with
`R/𝔪 → R'/𝔮` bijective) is `chartOriginAt x r a` for some `a`: the origin of the chart after the
linear change `x_i ↦ x_i − a_i x_r` of the first `r` coordinates. This is the remark in the proof
of [Kol07, Lemma 61] that "every preimage of `p` appears as the origin after a suitable linear
change", and item (9) of [Hau03, Appendix C]. -/
theorem exists_eq_chartOriginAt (𝔮 : Ideal (chartRing x r)) [𝔮.IsPrime]
    (h : maximalIdeal R ≤ 𝔮.comap (algebraMap R (chartRing x r)))
    (hrat : Function.Bijective (Ideal.quotientMap 𝔮 (algebraMap R (chartRing x r)) h)) :
    ∃ a : Fin n → R, 𝔮 = chartOriginAt x r a := by
  classical
  have hlift : ∀ i : Fin n, ∃ a : R, chartYR x r i - algebraMap R (chartRing x r) a ∈ 𝔮 := by
    intro i
    obtain ⟨b, hb⟩ := hrat.2 (Ideal.Quotient.mk 𝔮 (chartYR x r i))
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨a, ?_⟩
    rw [Ideal.quotientMap_mk] at hb
    rw [← neg_sub]
    exact 𝔮.neg_mem (Ideal.Quotient.eq.mp hb)
  choose a ha using hlift
  refine ⟨a, ?_⟩
  have hle : chartOriginAt x r a ≤ 𝔮 := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    dsimp only
    split_ifs with hi
    · exact ha i
    · have hyi : chartYR x r i = algebraMap R (chartRing x r) (x i) :=
        Subtype.ext (by rw [coe_chartYROf, chartYOf_of_not_lt x r _ hi]; rfl)
      rw [hyi]
      exact Ideal.mem_comap.mp (h (hx ▸ Ideal.subset_span ⟨i, rfl⟩))
  exact ((chartOriginAt_isMaximal x r a hx hn).eq_of_le ‹𝔮.IsPrime›.ne_top hle).symm

end Fibre

end AlgebraicGeometry
