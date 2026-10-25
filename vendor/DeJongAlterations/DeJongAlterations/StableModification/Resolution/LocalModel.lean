import DeJongAlterations.StableModification.Resolution.LocalRegular
import DeJongAlterations.StableModification.Resolution.LocalSmooth
import DeJongAlterations.Algebra.NodeFittingRelativeSchemeTrace
import DeJongAlterations.Algebra.CompletionRegularityAscent
import DeJongAlterations.Algebra.NoetherianCompletion
import DeJongAlterations.Geometry.CompletedLocalRegularity

/-!
# Local models of a flat family of curves over a normal crossings base

Let `f : X → S` be flat and locally of finite presentation, `S` locally Noetherian, `x ∈ X`,
`s = f(x)`, and write `Â = Ô_{S,s}`, `Ĉ = Ô_{X,x}` (completions at the maximal ideals of the
stalks). This file assembles the algebra of `LocalMonomial`, `LocalNode`, `LocalSmooth` and
`LocalRegular` with Codex's completed-local machinery into the local description of de Jong
1996, 3.1, 3.3, 3.5 and 4.25 (`references/dejong96-alterations/tex/page-0013.tex`,
`page-0014.tex`, `page-0015.tex`, `page-0026.tex`):

* `completedSingularIdeal f x`: the trace on `Ĉ` of `Sing(f)`, the closed subscheme cut out by
  the first Fitting ideal of `Ω_{X/S}` (de Jong 2.21; Codex's
  `Algebra.NodeFittingOmegaGluing.idealSheaf f 1`).
* `completedSingularIdeal_map_splitNode`: every split presentation `Ĉ ≃ₐ[Â] Â[[u,v]]/(uv - h)`
  carries it onto `(u, v)` (Codex's `globalStalkIdeal_eq_gradient`; de Jong 2.23, 3.3: the trace of
  `Sing(f)` on `Spec B` is given by the ideal `(u,v)`).
* `exists_completed_monomial_normal_form` (**de Jong 3.3, split case**): if the closed fibre
  `Ĉ/𝔪_Â Ĉ` is the split node over `Â/𝔪_Â`, `Â` is a domain, the `t_i ∈ 𝒪_{S,s}` have prime
  images in `Â`, and `f^*(t_1 ⋯ t_r)` vanishes on `Sing(f)` near `x` (it lies in the radical of the
  stalk of the Fitting ideal), then `Ĉ ≃ₐ[Â] Â[[u,v]]/(uv - t_1^{n_1} ⋯ t_r^{n_r})`,
  `∑ n_i ≥ 1`, carrying `Sing(f)` onto `(u, v)`.
* `exists_completed_monomial_normal_form_of_regular`: the same for a regular base, with
  `t_i ∈ 𝔪_s ∖ 𝔪_s²` (local equations of the components of a strict normal crossings divisor
  through `s`); and `two_le_sum_of_not_isRegularLocalRing_stalk`: if `X` is singular at `x`, then
  `∑ n_i ≥ 2` (de Jong 3.3: "if `∑ n_i = 1`, then the point `x` is regular on `X`").
* `exists_completed_smooth_normal_form`, `exists_completed_smooth_normal_form_of_retraction`
  (**de Jong 4.25 (i)**): if the closed fibre is `κ[[w]]`, then `Ĉ ≃ₐ[Â] Â[[w]]`; a retraction
  `Ĉ → Â` (the completed local ring of a section through `x`) can be made `w = 0`.
* `isRegularLocalRing_stalk_of_smooth_closedFiber` (**de Jong 3.1, `Sing(X) ⊆ Sing(f)`**): over
  a regular base, such a point is a regular point of `X`.

What is *not* proved here (it is geometric input, stated as hypotheses): the closed-fibre models
(from the ordinary-double-point/smoothness condition on the fibre `X_s` at a `k`-point), the
radical condition (from `f` being smooth over `S ∖ D`) and the local equations `t_i` (from the
strict normal crossings condition on `D`).
-/

noncomputable section

namespace DeJongAlterations.StableModification.Resolution

open AlgebraicGeometry CategoryTheory IsLocalRing MvPowerSeries
open Geometry.NodeCompletedLocalMap Algebra.NodeFittingIdealSheaf Algebra.NodeFlatPresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

section Singular

variable [LocallyOfFinitePresentation f]

/-- The trace on the completed local ring `Ô_{X,x}` of the singular locus `Sing(f)`, the closed
subscheme defined by the first Fitting ideal of `Ω_{X/S}` (de Jong 2.21). -/
def completedSingularIdeal : Ideal (X.completedLocalRing x) :=
  (stalkIdeal (Algebra.NodeFittingOmegaGluing.idealSheaf f 1) x).map (X.toCompletedLocalRing x)

variable [IsLocallyNoetherian S]

attribute [local instance] completedAlgebra

local instance completedLocalHom :
    IsLocalHom (algebraMap (S.completedLocalRing (f x)) (X.completedLocalRing x)) :=
  completedMap_isLocalHom f x

/-- **de Jong 2.23, 3.3: the trace of `Sing(f)` is `(u, v)`.** Every split presentation
`Ô_{X,x} ≃ₐ[Ô_{S,s}] Ô_{S,s}[[u,v]]/(uv - h)` carries the trace of the singular locus onto the
coordinate ideal `(u, v)`. -/
theorem completedSingularIdeal_map_splitNode (h : S.completedLocalRing (f x))
    (φ : X.completedLocalRing x ≃ₐ[S.completedLocalRing (f x)]
      SplitNodeRing (S.completedLocalRing (f x)) h) :
    (completedSingularIdeal f x).map φ =
      splitCoordinateIdeal (S.completedLocalRing (f x)) h := by
  have key := Algebra.NodeFittingRelativeSchemeTrace.globalStalkIdeal_eq_gradient f x
    (S.completedLocalRing (f x)) (MvPowerSeries.X 0 * MvPowerSeries.X 1 - C h) φ
  have hcomp : φ.toRingEquiv.toRingHom.comp (X.toCompletedLocalRing x) =
      (φ : X.completedLocalRing x →+* SplitNodeRing (S.completedLocalRing (f x)) h).comp
        (X.toCompletedLocalRing x) := RingHom.ext fun _ => rfl
  have h0 : pderiv (S.completedLocalRing (f x)) 0
      (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 - C h) = MvPowerSeries.X 1 := by
    simp [Derivation.leibniz]
  have h1 : pderiv (S.completedLocalRing (f x)) 1
      (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 - C h) = MvPowerSeries.X 0 := by
    simp [Derivation.leibniz]
  rw [hcomp, ← Ideal.map_map, h0, h1] at key
  rw [completedSingularIdeal, ← Ideal.map_coe, key, splitCoordinateIdeal, Set.pair_comm]
  rfl

variable [IsLocallyNoetherian X]

omit [IsLocallyNoetherian S] [IsLocallyNoetherian X] in
/-- A germ on the base whose pullback vanishes on `Sing(f)` near `x` has completed image in the
radical of the trace of `Sing(f)`. -/
theorem algebraMap_mem_radical_completedSingularIdeal
    {a : S.presheaf.stalk (f x)}
    (ha : f.stalkMap x a ∈
      (stalkIdeal (Algebra.NodeFittingOmegaGluing.idealSheaf f 1) x).radical) :
    algebraMap (S.completedLocalRing (f x)) (X.completedLocalRing x)
        (S.toCompletedLocalRing (f x) a) ∈ (completedSingularIdeal f x).radical := by
  obtain ⟨N, hN⟩ := ha
  refine ⟨N, ?_⟩
  change (completedMap f x (S.toCompletedLocalRing (f x) a)) ^ N ∈ _
  rw [completedMap_coefficient, ← map_pow]
  exact Ideal.mem_map_of_mem _ hN

variable [Flat f]

local instance completedFlat :
    Module.Flat (S.completedLocalRing (f x)) (X.completedLocalRing x) :=
  (completedAlgebra_faithfullyFlat f x).toFlat

/-- **de Jong 3.3 (split case), on completed local rings.** Let `f : X → S` be flat and locally
of finite presentation over a locally Noetherian `S`, and `x ∈ X` a point whose completed closed
fibre `Ô_{X,x}/𝔪_s Ô_{X,x}` is the split node over `κ = Ô_{S,s}/𝔪`. Assume `Ô_{S,s}` is a domain,
`t_i ∈ 𝒪_{S,s}` have prime images in `Ô_{S,s}`, and `f^*(t_1 ⋯ t_r)` vanishes on `Sing(f)` near
`x`. Then `Ô_{X,x} ≃ₐ[Ô_{S,s}] Ô_{S,s}[[u,v]]/(uv - t_1^{n_1} ⋯ t_r^{n_r})` with `∑ n_i ≥ 1`,
carrying the trace of `Sing(f)` onto `(u, v)`. -/
theorem exists_completed_monomial_normal_form [IsDomain (S.completedLocalRing (f x))]
    (e : SplitNode (CoefficientResidue (S.completedLocalRing (f x))) ≃ₐ[CoefficientResidue
      (S.completedLocalRing (f x))] ClosedFiber (S.completedLocalRing (f x)) (X.completedLocalRing x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → S.presheaf.stalk (f x))
    (ht : ∀ i, Prime (S.toCompletedLocalRing (f x) (t i)))
    (hsing : f.stalkMap x (∏ i, t i) ∈
      (stalkIdeal (Algebra.NodeFittingOmegaGluing.idealSheaf f 1) x).radical) :
    ∃ n : ι → ℕ, 1 ≤ ∑ i, n i ∧
      ∃ φ : X.completedLocalRing x ≃ₐ[S.completedLocalRing (f x)]
          SplitNodeRing (S.completedLocalRing (f x))
            (∏ i, S.toCompletedLocalRing (f x) (t i) ^ n i),
        (completedSingularIdeal f x).map φ =
          splitCoordinateIdeal (S.completedLocalRing (f x))
            (∏ i, S.toCompletedLocalRing (f x) (t i) ^ n i) := by
  have hsing' := algebraMap_mem_radical_completedSingularIdeal f x hsing
  rw [map_prod] at hsing'
  exact exists_split_monomial_normal_form_of_closedFiber (fun i => S.toCompletedLocalRing (f x) (t i))
    ht (X.completedLocalRing x) e (completedSingularIdeal f x)
    (completedSingularIdeal_map_splitNode f x) hsing'

/-- **de Jong 3.3 over a regular base.** If `𝒪_{S,s}` is regular and the `t_i ∈ 𝔪_s ∖ 𝔪_s²`
(e.g. local equations at `s` of the components through `s` of a strict normal crossings divisor),
then `Ô_{X,x} ≃ₐ[Ô_{S,s}] Ô_{S,s}[[u,v]]/(uv - ∏ t_i^{n_i})` with `∑ n_i ≥ 1`, carrying `Sing(f)`
onto `(u, v)`; and if `X` is singular at `x`, then `∑ n_i ≥ 2`. -/
theorem exists_completed_monomial_normal_form_of_regular
    [IsRegularLocalRing (S.presheaf.stalk (f x))]
    (e : SplitNode (CoefficientResidue (S.completedLocalRing (f x))) ≃ₐ[CoefficientResidue
      (S.completedLocalRing (f x))] ClosedFiber (S.completedLocalRing (f x)) (X.completedLocalRing x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → S.presheaf.stalk (f x))
    (ht : ∀ i, t i ∈ maximalIdeal (S.presheaf.stalk (f x)))
    (ht2 : ∀ i, t i ∉ maximalIdeal (S.presheaf.stalk (f x)) ^ 2)
    (hsing : f.stalkMap x (∏ i, t i) ∈
      (stalkIdeal (Algebra.NodeFittingOmegaGluing.idealSheaf f 1) x).radical) :
    ∃ n : ι → ℕ, 1 ≤ ∑ i, n i ∧
      (¬ IsRegularLocalRing (X.presheaf.stalk x) → 2 ≤ ∑ i, n i) ∧
      ∃ φ : X.completedLocalRing x ≃ₐ[S.completedLocalRing (f x)]
          SplitNodeRing (S.completedLocalRing (f x))
            (∏ i, S.toCompletedLocalRing (f x) (t i) ^ n i),
        (completedSingularIdeal f x).map φ =
          splitCoordinateIdeal (S.completedLocalRing (f x))
            (∏ i, S.toCompletedLocalRing (f x) (t i) ^ n i) := by
  let : IsRegularLocalRing (S.completedLocalRing (f x)) :=
    Algebra.CompletionRegularityAscent.isRegularLocalRing_completion _
  let : IsDomain (S.completedLocalRing (f x)) :=
    Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing _
  have hmem : ∀ i, S.toCompletedLocalRing (f x) (t i) ∈
      maximalIdeal (S.completedLocalRing (f x)) := fun i =>
    map_nonunit (algebraMap (S.presheaf.stalk (f x)) (S.completedLocalRing (f x))) _ (ht i)
  have hsq : ∀ i, S.toCompletedLocalRing (f x) (t i) ∉
      maximalIdeal (S.completedLocalRing (f x)) ^ 2 := fun i hi =>
    ht2 i ((Algebra.CompletionRegularityBasics.mem_maximalIdeal_sq_iff _ (t i)).mp hi)
  obtain ⟨n, hn, φ, hφ⟩ := exists_completed_monomial_normal_form f x e t
    (fun i => prime_of_mem_maximalIdeal_of_not_mem_sq (hmem i) (hsq i)) hsing
  refine ⟨n, hn, fun hX => ?_, φ, hφ⟩
  apply two_le_sum_of_not_isRegularLocalRing _ hmem hsq n hn
  intro hreg
  let : IsRegularLocalRing (X.completedLocalRing x) := IsRegularLocalRing.of_ringEquiv
    φ.symm.toRingEquiv
  exact hX (Geometry.CompletedLocalRegularity.isRegularLocalRing_stalk_of_completedLocalRing X x)

/-- **de Jong 4.25 (i), on completed local rings.** If the completed closed fibre at `x` is
`κ[[w]]`, then `Ô_{X,x} ≃ₐ[Ô_{S,s}] Ô_{S,s}[[w]]`. -/
theorem exists_completed_smooth_normal_form
    (e : PowerSeries (CoefficientResidue (S.completedLocalRing (f x))) ≃ₐ[CoefficientResidue
      (S.completedLocalRing (f x))] ClosedFiber (S.completedLocalRing (f x)) (X.completedLocalRing x)) :
    Nonempty (X.completedLocalRing x ≃ₐ[S.completedLocalRing (f x)]
      PowerSeries (S.completedLocalRing (f x))) :=
  exists_smooth_normal_form _ _ e

/-- **de Jong 4.23, 4.25 (i), with a section.** If the completed closed fibre at `x` is `κ[[w]]`
and `ρ : Ô_{X,x} → Ô_{S,s}` is a retraction (the completed local ring of a section of `f`
through `x`), then there is `Ô_{X,x} ≃ₐ[Ô_{S,s}] Ô_{S,s}[[w]]` carrying `ker ρ` onto `(w)`. -/
theorem exists_completed_smooth_normal_form_of_retraction
    (e : PowerSeries (CoefficientResidue (S.completedLocalRing (f x))) ≃ₐ[CoefficientResidue
      (S.completedLocalRing (f x))] ClosedFiber (S.completedLocalRing (f x)) (X.completedLocalRing x))
    (ρ : X.completedLocalRing x →ₐ[S.completedLocalRing (f x)] S.completedLocalRing (f x)) :
    ∃ φ : X.completedLocalRing x ≃ₐ[S.completedLocalRing (f x)]
        PowerSeries (S.completedLocalRing (f x)),
      (RingHom.ker ρ.toRingHom).map φ = Ideal.span {PowerSeries.X} :=
  exists_smooth_normal_form_of_retraction _ _ e ρ

/-- **de Jong 3.1, `Sing(X) ⊆ Sing(f)`, at a point with smooth closed fibre.** Over a regular
base point, a point whose completed closed fibre is `κ[[w]]` is a regular point of `X`. -/
theorem isRegularLocalRing_stalk_of_smooth_closedFiber
    [IsRegularLocalRing (S.presheaf.stalk (f x))]
    (e : PowerSeries (CoefficientResidue (S.completedLocalRing (f x))) ≃ₐ[CoefficientResidue
      (S.completedLocalRing (f x))] ClosedFiber (S.completedLocalRing (f x)) (X.completedLocalRing x)) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  let : IsRegularLocalRing (S.completedLocalRing (f x)) :=
    Algebra.CompletionRegularityAscent.isRegularLocalRing_completion _
  obtain ⟨φ⟩ := exists_completed_smooth_normal_form f x e
  let : IsRegularLocalRing (PowerSeries (S.completedLocalRing (f x))) :=
    isRegularLocalRing_powerSeries
  let : IsRegularLocalRing (X.completedLocalRing x) :=
    IsRegularLocalRing.of_ringEquiv φ.symm.toRingEquiv
  exact Geometry.CompletedLocalRegularity.isRegularLocalRing_stalk_of_completedLocalRing X x

end Singular

end DeJongAlterations.StableModification.Resolution
