import DeJongAlterations.StableModification.Resolution.LocalSmoothPoint

/-!
# Local models of nodal curves over a normal crossings base (de Jong 3.3, 4.25)

This is the umbrella module of the local part of the resolution endgame
(`StableModification/Resolution/Local*`), and states the local model in one theorem
`exists_local_model` (blueprint `lem:sm-dj-local-model`):

Let `g : C → Y` be a nodal curve (`DeJong.IsNodalCurve`), `Y` Noetherian, `C` locally Noetherian,
`B ⊆ Y` a strict normal crossings divisor, `g` smooth over `Y ∖ B`, and `x ∈ C` a closed point
such that `κ(g(x))` is algebraically closed and `𝒪_{Y,g(x)}` is regular (de Jong 4.23: `Y`
nonsingular over `k = k̄`). Then either

1. the point of the fibre over `x` is smooth, `Ô_{C,x} ≅ Ô_{Y,g(x)}[[w]]`, `C` is regular at `x`,
   and a section of `g` through `x` can be made `w = 0`; or
2. there are local equations `t_i ∈ 𝔪 ∖ 𝔪²` of the components of `B` through `g(x)` with
   `B = (t_1 ⋯ t_r)` at `g(x)`, and exponents with `∑ n_i ≥ 1` (`≥ 2` if `C` is singular at `x`)
   such that `Ô_{C,x} ≅ Ô_{Y,g(x)}[[u,v]]/(uv - t_1^{n_1} ⋯ t_r^{n_r})`, with `Sing(g) ↦ (u, v)`.

The module also provides `sectionStalkRetraction`, the stalk retraction of a section, which feeds
the section statement of case 1.

Sources: de Jong 1996, 3.1, 3.3, 3.5, 4.23–4.25 (`references/dejong96-alterations/tex/page-0013.tex`,
`page-0014.tex`, `page-0015.tex`, `page-0026.tex`).
-/

noncomputable section

namespace DeJongAlterations.StableModification.Resolution

open AlgebraicGeometry CategoryTheory IsLocalRing
open Geometry.NodeCompletedLocalMap Algebra.NodeFittingIdealSheaf DeJong

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {C Y : Scheme.{u}} (g : C ⟶ Y)

/-- The stalk retraction `𝒪_{C,τ(y)} → 𝒪_{Y,g(τ(y))}` of a section `τ` of `g`: the stalk map of `τ`
followed by the identification `𝒪_{Y,y} = 𝒪_{Y,g(τ(y))}`. -/
def sectionStalkRetraction (τ : Y ⟶ C) (hτ : τ ≫ g = 𝟙 Y) (y : Y) :
    C.presheaf.stalk (τ y) →+* Y.presheaf.stalk (g (τ y)) :=
  (τ.stalkMap y ≫ (Y.presheaf.stalkCongr (.of_eq (show y = g (τ y) by
    rw [← Scheme.Hom.comp_apply, hτ]; rfl))).hom).hom

/-- The stalk retraction of a section is a retraction of the stalk map of `g`. -/
theorem sectionStalkRetraction_stalkMap (τ : Y ⟶ C) (hτ : τ ≫ g = 𝟙 Y) (y : Y)
    (a : Y.presheaf.stalk (g (τ y))) :
    sectionStalkRetraction g τ hτ y (g.stalkMap (τ y) a) = a := by
  have h1 : g.stalkMap (τ y) ≫ τ.stalkMap y = (τ ≫ g).stalkMap y :=
    (Scheme.Hom.stalkMap_comp τ g y).symm
  have h2 := Scheme.Hom.stalkMap_congr_hom (τ ≫ g) (𝟙 Y) hτ y
  have h3 : g.stalkMap (τ y) ≫ τ.stalkMap y ≫ (Y.presheaf.stalkCongr (.of_eq (show y = g (τ y) by
      rw [← Scheme.Hom.comp_apply, hτ]; rfl))).hom = 𝟙 _ := by
    rw [← Category.assoc, h1, h2, Scheme.Hom.stalkMap_id]
    simp only [TopCat.Presheaf.stalkCongr_hom]
    erw [Category.comp_id, TopCat.Presheaf.stalkSpecializes_comp,
      TopCat.Presheaf.stalkSpecializes_refl]
  exact congrArg (fun φ => φ.hom a) h3

attribute [local instance] completedAlgebra

/-- **Local model of a nodal curve over a normal crossings base (de Jong 3.3, 4.25).** At a closed
point `x` with `κ(g(x))` algebraically closed and `𝒪_{Y,g(x)}` regular, either the fibre point is
smooth and `Ô_{C,x} ≅ Ô_{Y,g(x)}[[w]]` (with `C` regular at `x` and sections through `x` made
`w = 0`), or `Ô_{C,x} ≅ Ô_{Y,g(x)}[[u,v]]/(uv - ∏ t_i^{n_i})` for local equations `t_i ∈ 𝔪 ∖ 𝔪²`
of the components of `B` through `g(x)`, with `B = (∏ t_i)`, `∑ n_i ≥ 1`, `∑ n_i ≥ 2` if `C` is
singular at `x`, and `Sing(g) ↦ (u, v)`. -/
theorem exists_local_model [IsNodalCurve g] [IsNoetherian Y] [IsLocallyNoetherian C]
    (B : Y.IdealSheafData) (hB : IsStrictNormalCrossings B)
    (hsm : ∀ x' : C, g x' ∉ (B.support : Set Y) → IsSmoothAt g x')
    (x : C) (hx : IsClosed ({x} : Set C)) [IsAlgClosed (Y.residueField (g x))]
    [IsRegularLocalRing (Y.presheaf.stalk (g x))] :
    (originalFiberPoint g x ∈ (g.fiberToSpecResidueField (g x)).smoothLocus ∧
      Nonempty (C.completedLocalRing x ≃ₐ[Y.completedLocalRing (g x)]
        PowerSeries (Y.completedLocalRing (g x))) ∧
      IsRegularLocalRing (C.presheaf.stalk x) ∧
      ∀ (ρ : C.presheaf.stalk x →+* Y.presheaf.stalk (g x)) (hρ : ∀ a, ρ (g.stalkMap x a) = a),
        ∃ φ : C.completedLocalRing x ≃ₐ[Y.completedLocalRing (g x)]
            PowerSeries (Y.completedLocalRing (g x)),
          (RingHom.ker (completedRetraction g x ρ hρ).toRingHom).map φ =
            Ideal.span {PowerSeries.X}) ∨
    (originalFiberPoint g x ∉ (g.fiberToSpecResidueField (g x)).smoothLocus ∧
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
                (∏ i, Y.toCompletedLocalRing (g x) (t i) ^ n i)) := by
  by_cases hfib : originalFiberPoint g x ∈ (g.fiberToSpecResidueField (g x)).smoothLocus
  · obtain ⟨h1, h2, h3⟩ := exists_smooth_local_model_of_mem_smoothLocus g x hx hfib
    exact Or.inl ⟨hfib, h1, h2 inferInstance, h3⟩
  · exact Or.inr ⟨hfib, exists_node_local_model g B hB hsm x hx hfib⟩

end DeJongAlterations.StableModification.Resolution
