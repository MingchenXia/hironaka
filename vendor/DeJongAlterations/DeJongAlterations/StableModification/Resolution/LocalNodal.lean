import DeJongAlterations.StableModification.Resolution.LocalFiber
import DeJongAlterations.StableModification.Resolution.LocalSingular
import DeJongAlterations.StableModification.Resolution.LocalSNC

/-!
# Local models of a nodal curve over a strict normal crossings base

This file assembles de Jong's local description (de Jong 1996, 3.3, 3.5, 4.23–4.25,
`references/dejong96-alterations/tex/page-0014.tex`, `page-0015.tex`, `page-0026.tex`) for a nodal
curve `g : C → Y` (`DeJong.IsNodalCurve`) over a Noetherian base with a strict normal crossings
divisor `B`, smooth over `Y ∖ B`, at a closed point `x ∈ C` whose image `y = g(x)` has
algebraically closed residue field (a closed point of a variety over `k = k̄`).

* `isGeometricOrdinaryDoublePoint_of_not_mem_smoothLocus`: the point `x_y` of the fibre `C_y` over
  `x` is closed, and (`κ(y)` being algebraically closed, so that `C_y` is a geometric fibre) it is an
  ordinary double point of `C_y` unless it is a smooth point of `C_y`.
* `exists_node_local_model` (**de Jong 3.3 + 4.25 (ii)**): if `x_y` is not a smooth point of
  `C_y` and `𝒪_{Y,y}` is regular, there are local equations `t_1, …, t_r ∈ 𝔪_y ∖ 𝔪_y²` of the
  components of `B` through `y`, with `B = (t_1 ⋯ t_r)` at `y`, and exponents `n_i` with
  `∑ n_i ≥ 1` (so `r ≥ 1`: there is no node over `Y ∖ B`), `∑ n_i ≥ 2` if `C` is singular at `x`,
  and `Ô_{C,x} ≅ Ô_{Y,y}[[u,v]]/(uv - t_1^{n_1} ⋯ t_r^{n_r})` over `Ô_{Y,y}`, carrying the trace of
  `Sing(g)` onto `(u, v)`.
* `exists_smooth_local_model` (**de Jong 4.25 (i)**): if `Ô_{C_y,x_y} ≅ κ(y)[[w]]`, then
  `Ô_{C,x} ≅ Ô_{Y,y}[[w]]` and `C` is regular at `x` when `𝒪_{Y,y}` is; a ring retraction of
  `𝒪_{Y,y} → 𝒪_{C,x}` (the stalk of a section `τ` through `x`) can be made `w = 0`.
-/

noncomputable section

namespace DeJongAlterations.StableModification.Resolution

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open Geometry.NodeCompletedLocalMap Algebra.NodeFlatPresentation Algebra.NodeFittingIdealSheaf DeJong

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {C Y : Scheme.{u}} (g : C ⟶ Y)

/-- The scheme-theoretic fibre `C_y → Spec κ(y)` of a morphism locally of finite presentation is
locally of finite presentation (base change). -/
instance fiberToSpecResidueField_locallyOfFinitePresentation [LocallyOfFinitePresentation g]
    (y : Y) : LocallyOfFinitePresentation (g.fiberToSpecResidueField y) :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd g (Y.fromSpecResidueField y)))

/-- The point of the fibre `C_{g(x)}` over a closed point `x` is a closed point of the fibre. -/
theorem isClosed_originalFiberPoint (x : C) (hx : IsClosed ({x} : Set C)) :
    IsClosed ({originalFiberPoint g x} : Set (g.fiber (g x))) := by
  have hpre : (g.fiberι (g x)) ⁻¹' {x} = {originalFiberPoint g x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      apply (g.fiberι (g x)).isEmbedding.injective
      rw [hz, originalFiberPoint_source]
    · rintro rfl
      exact originalFiberPoint_source g x
  rw [← hpre]
  exact hx.preimage (g.fiberι (g x)).continuous

/-- **The fibre at a closed point is split (de Jong 4.24, 4.25).** If `κ(g(x))` is algebraically
closed, the fibre `C_{g(x)}` is a geometric fibre of the nodal curve `g`, so its closed point over a
closed point `x` is a smooth point or an ordinary double point. -/
theorem isGeometricOrdinaryDoublePoint_of_not_mem_smoothLocus [IsNodalCurve g] (x : C)
    (hx : IsClosed ({x} : Set C)) [IsAlgClosed (Y.residueField (g x))]
    (hns : originalFiberPoint g x ∉ (g.fiberToSpecResidueField (g x)).smoothLocus) :
    Geometry.IsGeometricOrdinaryDoublePoint (K := Y.residueField (g x))
      (g.fiberToSpecResidueField (g x)) (originalFiberPoint g x) :=
  (IsNodalCurve.geometricNodes (Y.residueField (g x)) (Y.fromSpecResidueField (g x))
    (originalFiberPoint g x) (isClosed_originalFiberPoint g x hx)).resolve_left hns

attribute [local instance] completedAlgebra

local instance completedLocalHom'' [LocallyOfFiniteType g] [IsLocallyNoetherian Y] (x : C) :
    IsLocalHom (algebraMap (Y.completedLocalRing (g x)) (C.completedLocalRing x)) :=
  completedMap_isLocalHom g x

/-- **Local model at a node (de Jong 3.3, 3.5, 4.25 (ii)).** Let `g : C → Y` be a nodal curve over a
Noetherian scheme with a strict normal crossings divisor `B`, smooth over `Y ∖ B`, and `x ∈ C` a
closed point with `κ(g(x))` algebraically closed and `𝒪_{Y,g(x)}` regular, whose point on the fibre
is not smooth. Then there are local equations `t_i ∈ 𝔪 ∖ 𝔪²` of the components of `B` through
`g(x)`, with `B = (t_1 ⋯ t_r)` at `g(x)`, and exponents with `∑ n_i ≥ 1` (`∑ n_i ≥ 2` if `C` is
singular at `x`) such that `Ô_{C,x} ≃ Ô_{Y,g(x)}[[u,v]]/(uv - ∏ t_i^{n_i})` over `Ô_{Y,g(x)}`,
carrying the trace of `Sing(g)` onto `(u, v)`. -/
theorem exists_node_local_model [IsNodalCurve g] [IsNoetherian Y] [IsLocallyNoetherian C]
    (B : Y.IdealSheafData) (hB : IsStrictNormalCrossings B)
    (hsm : ∀ x' : C, g x' ∉ (B.support : Set Y) → IsSmoothAt g x')
    (x : C) (hx : IsClosed ({x} : Set C)) [IsAlgClosed (Y.residueField (g x))]
    [IsRegularLocalRing (Y.presheaf.stalk (g x))]
    (hns : originalFiberPoint g x ∉ (g.fiberToSpecResidueField (g x)).smoothLocus) :
    ∃ (r : ℕ) (t : Fin r → Y.presheaf.stalk (g x)),
      (∀ i, t i ∈ maximalIdeal (Y.presheaf.stalk (g x))) ∧
      (∀ i, t i ∉ maximalIdeal (Y.presheaf.stalk (g x)) ^ 2) ∧
      stalkIdeal B (g x) = Ideal.span {∏ i, t i} ∧
      ∃ n : Fin r → ℕ, 1 ≤ ∑ i, n i ∧
        (¬ IsRegularLocalRing (C.presheaf.stalk x) → 2 ≤ ∑ i, n i) ∧
        ∃ φ : C.completedLocalRing x ≃ₐ[Y.completedLocalRing (g x)]
            SplitNodeRing (Y.completedLocalRing (g x))
              (∏ i, Y.toCompletedLocalRing (g x) (t i) ^ n i),
          (completedSingularIdeal g x).map φ =
            splitCoordinateIdeal (Y.completedLocalRing (g x))
              (∏ i, Y.toCompletedLocalRing (g x) (t i) ^ n i) := by
  obtain ⟨r, t, ht, ht2, hspan⟩ := exists_snc_local_equations B hB (g x)
  have hnode := isGeometricOrdinaryDoublePoint_of_not_mem_smoothLocus g x hx hns
  obtain ⟨e⟩ := nonempty_splitNode_closedFiber_of_isGeometricOrdinaryDoublePoint g x hnode
  have hb : ∏ i, t i ∈ stalkIdeal B (g x) := by
    rw [hspan]
    exact Ideal.mem_span_singleton_self _
  have hsing := stalkMap_mem_radical_stalkIdeal_of_isSmoothAt g B hsm x hb
  obtain ⟨n, hn, hreg, φ, hφ⟩ :=
    exists_completed_monomial_normal_form_of_regular g x e t ht ht2 hsing
  exact ⟨r, t, ht, ht2, hspan, n, hn, hreg, φ, hφ⟩

/-- A ring retraction `ρ` of the stalk map `𝒪_{Y,g(x)} → 𝒪_{C,x}` (for instance the stalk map of a
section through `x`) induces an `Ô_{Y,g(x)}`-algebra retraction of the completed map. -/
def completedRetraction [LocallyOfFiniteType g] [IsLocallyNoetherian Y] [IsLocallyNoetherian C]
    (x : C) (ρ : C.presheaf.stalk x →+* Y.presheaf.stalk (g x))
    (hρ : ∀ a, ρ (g.stalkMap x a) = a) :
    C.completedLocalRing x →ₐ[Y.completedLocalRing (g x)] Y.completedLocalRing (g x) :=
  letI : IsLocalHom ρ := IsLocalHom.of_surjective ρ (fun a => ⟨g.stalkMap x a, hρ a⟩)
  { toRingHom := Algebra.CompletionLocalMap.completionMap ρ
    commutes' := fun a => by
      change Algebra.CompletionLocalMap.completionMap ρ (completedMap g x a) = a
      have hcomp : (Algebra.CompletionLocalMap.completionMap ρ).comp (completedMap g x) =
          RingHom.id _ := by
        rw [completedMap]
        rw [← Algebra.CompletionLocalMap.completionMap_comp]
        exact Algebra.CompletionLocalMap.completionMap_eq_id_of _ hρ
      exact RingHom.congr_fun hcomp a }

/-- **Local model at a smooth point (de Jong 3.1, 4.25 (i)).** If the completed local ring of the
fibre `C_{g(x)}` at the point over `x` is `κ(g(x))[[w]]`, then `Ô_{C,x} ≃ Ô_{Y,g(x)}[[w]]` over
`Ô_{Y,g(x)}`; if `𝒪_{Y,g(x)}` is regular, `C` is regular at `x`; and for a ring retraction `ρ` of
`𝒪_{Y,g(x)} → 𝒪_{C,x}` (a section through `x`) the isomorphism can be chosen to carry the kernel of
the completed retraction (the trace of the section) onto `(w)`. -/
theorem exists_smooth_local_model [IsNodalCurve g] [IsLocallyNoetherian Y] [IsLocallyNoetherian C]
    (x : C)
    (hfib : letI := fiberCompletedAlgebra g x
      Nonempty ((g.fiber (g x)).completedLocalRing (originalFiberPoint g x) ≃ₐ[Y.residueField (g x)]
        PowerSeries (Y.residueField (g x)))) :
    Nonempty (C.completedLocalRing x ≃ₐ[Y.completedLocalRing (g x)]
        PowerSeries (Y.completedLocalRing (g x))) ∧
      (IsRegularLocalRing (Y.presheaf.stalk (g x)) → IsRegularLocalRing (C.presheaf.stalk x)) ∧
      ∀ (ρ : C.presheaf.stalk x →+* Y.presheaf.stalk (g x)) (hρ : ∀ a, ρ (g.stalkMap x a) = a),
        ∃ φ : C.completedLocalRing x ≃ₐ[Y.completedLocalRing (g x)]
            PowerSeries (Y.completedLocalRing (g x)),
          (RingHom.ker (completedRetraction g x ρ hρ).toRingHom).map φ =
            Ideal.span {PowerSeries.X} := by
  obtain ⟨e⟩ := nonempty_powerSeries_closedFiber_of_fiber g x hfib
  refine ⟨exists_completed_smooth_normal_form g x e, fun hreg => ?_, fun ρ hρ =>
    exists_completed_smooth_normal_form_of_retraction g x e (completedRetraction g x ρ hρ)⟩
  let := hreg
  exact isRegularLocalRing_stalk_of_smooth_closedFiber g x e

end DeJongAlterations.StableModification.Resolution
