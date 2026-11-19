/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Scheme.BlowUp.Transform.Defs
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.IdealSheaf.Order.Lemma61
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorem 88: the chart missing the strict transform of the hypersurface

In the proof of [Kol07, Theorem 88], only `r − 1` of the charts of the blow-up have the displayed
form, but "these `r − 1` charts, however, completely cover `S_1`": the chart whose distinguished
coordinate is
the equation `y_ρ` of `S` misses the strict transform `S_1`. In the chart description of the stalk
of the blow-up at a point `q ∈ B_Z X` over `z ∈ Z` with `S_z = (y_ρ)`, the stalk of `S_1` at `q` is
the saturation `⋃ᵢ (π^* S_z : F_qⁱ)` of the total transform by the exceptional ideal
(`stalkIdeal_saturate_of_isInvertible`), where `π^* S_z = (π^♯ y_ρ) = F_q`
(`stalkIdeal_comap_eq_span_of_chart`); so `1 ∈ (F_q : F_q)` and `(S_1)_q = 𝒪_{B,q}`. This is the
observation in the proof of [Kol07, Lemma 62] that the remaining chart "does not contain any point
of the birational transform".
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData IsLocalRing

namespace Hironaka.Sequence

variable {k : Type u} [Field k] {X : Scheme.{u}} (Z S : X.IdealSheafData)

/-- In the chart description of the stalk at `q ∈ B_Z X` over `z ∈ Z`, when the distinguished
coordinate `y_ρ` is the local equation of `S` (`S_z = (y_ρ)`), the strict transform of `S` misses
`q`: `(S_1)_q = 𝒪_{B,q}` (the proofs of [Kol07, Lemma 62 and Theorem 88]). -/
theorem stalkIdeal_strictTransform_eq_top_of_pivot (q : Z.blowUp) {n' : ℕ}
    (y : Fin n' → X.presheaf.stalk (Z.blowUpπ q)) (ρ : Fin n')
    (hZ' : Z.stalkIdeal (Z.blowUpπ q) = chartCenter y ρ)
    (hSz : S.stalkIdeal (Z.blowUpπ q) = Ideal.span {y ρ}) (𝔮 : Ideal (chartRing y ρ))
    [𝔮.IsPrime] (e : Z.blowUp.presheaf.stalk q ≃+* Localization.AtPrime 𝔮)
    (he : ∀ a, e (Z.blowUpπ.stalkMap q a) =
      algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
        (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) a)) :
    (S.strictTransform Z).stalkIdeal q = ⊤ := by
  have hK : Z.exceptionalDivisor.IsInvertible := blowUp.isInvertible_comap_π Z
  -- the exceptional ideal and the total transform of `S` at `q` are both `(π^♯ y_ρ)`
  have hF : Z.exceptionalDivisor.stalkIdeal q =
      Ideal.span {Z.blowUpπ.stalkMap q (y ρ)} :=
    stalkIdeal_comap_eq_span_of_chart q y ρ hZ' 𝔮 e he
  have hS1 : (S.comap Z.blowUpπ).stalkIdeal q =
      Ideal.span {Z.blowUpπ.stalkMap q (y ρ)} := by
    rw [stalkIdeal_comap, hSz, Ideal.map_span, Set.image_singleton]
  unfold strictTransform strictTransformAlong
  rw [stalkIdeal_saturate_of_isInvertible _ hK, hF, hS1]
  -- `1 ∈ ((π^♯ y_ρ) : (π^♯ y_ρ)^1)`
  refine top_unique (le_iSup_of_le 1 fun t _ => ?_)
  rw [pow_one]
  exact Submodule.mem_colon.mpr fun p hp => by
    rw [smul_eq_mul]
    exact Ideal.mul_mem_left _ t hp

end Hironaka.Sequence
