import DeJongAlterations.StableModification.Resolution.LocalModel
import DeJongAlterations.StableModification.DeJong.Interface
import DeJongAlterations.Algebra.NodeFittingSupportPullback
import DeJongAlterations.Geometry.FiberDimensionUpperSemicontinuityClosedCover

/-!
# The singular locus of a nodal curve lies over the degeneration divisor

Let `g : C → Y` be a nodal curve (`DeJong.IsNodalCurve`) and `Sing(g)` the closed subscheme cut out
by the first Fitting ideal of `Ω_{C/Y}` (de Jong 1996, 2.21,
`references/dejong96-alterations/tex/page-0012.tex`; Codex's
`Algebra.NodeFittingOmegaGluing.idealSheaf g 1`).

* `not_mem_fittingSupport_of_mem_smoothLocus`: a smooth point of `g` is not in `Sing(g)`.
  Over an algebraic closure `K` of `κ(g(x))` the geometric fibre has dimension at most one and the
  point stays smooth (`mem_smoothLocus_pullback_snd`), so Codex's field-case computation
  (`Algebra.NodeFittingGeometricIdealSheaf.not_mem_originalPullback_support_of_mem_smoothLocus`)
  applies to the pulled-back Fitting ideal.
* `stalkMap_mem_radical_stalkIdeal_of_support_subset`: if `Sing(g) ⊆ g⁻¹(Supp B)` for an ideal
  sheaf `B` on `Y`, then `g^♯` maps the stalk of `B` at `g(x)` into the radical of the stalk of the
  Fitting ideal at `x` (a local Nullstellensatz on an affine chart).
* `stalkMap_mem_radical_stalkIdeal_of_isSmoothAt`: hence, if `g` is smooth over `Y ∖ Supp B`
  (de Jong 3.1, 4.23), the local equations of `B` at `g(x)` pull back into the radical of the
  trace of `Sing(g)`, the radical hypothesis of `exists_completed_monomial_normal_form`
  (de Jong 3.3: "By assumption we have `V(h) ⊂ V(t_1 ⋯ t_r)`").
-/

noncomputable section

namespace DeJongAlterations.StableModification.Resolution

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open Algebra.NodeFittingIdealSheaf DeJong

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {C Y : Scheme.{u}} (g : C ⟶ Y)

/-- The geometric fibres of a nodal curve have dimension at most one. -/
theorem geometricFiber_dimension_le_one [IsNodalCurve g] (K : Type u) [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ Y) : topologicalKrullDim (pullback (C := Scheme.{u}) g a) ≤ 1 := by
  rw [Geometry.FiberDimensionUpperSemicontinuityClosedCover.topologicalKrullDim_eq_iSup_componentDimension]
  exact iSup_le fun Z => (IsNodalCurve.pureGeometricFibers K a Z.val Z.property).le

/-- Smoothness at a point is stable under base change: a point of `C ×_Y T` over a smooth point of
`g` is a smooth point of the projection to `T`. -/
theorem mem_smoothLocus_pullback_snd [LocallyOfFinitePresentation g] {T : Scheme.{u}}
    (a : T ⟶ Y) (z : pullback (C := Scheme.{u}) g a) (hz : pullback.fst g a z ∈ g.smoothLocus) :
    z ∈ (pullback.snd g a).smoothLocus := by
  let U := g.smoothLocus
  have hsm : Smooth (U.ι ≫ g) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      Scheme.Opens.ι_preimage_self]
  have sq := (IsPullback.of_hasPullback U.ι (pullback.fst g a)).paste_vert
    (IsPullback.of_hasPullback g a)
  have hsm' : Smooth (pullback.snd U.ι (pullback.fst g a) ≫ pullback.snd g a) :=
    MorphismProperty.of_isPullback (P := @Smooth) sq hsm
  have htop := Scheme.Hom.smoothLocus_eq_top
    (pullback.snd U.ι (pullback.fst g a) ≫ pullback.snd g a)
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at htop
  obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := U.ι) (g := pullback.fst g a) (⟨pullback.fst g a z, hz⟩ : U) z rfl
  have hmem : p ∈ pullback.snd U.ι (pullback.fst g a) ⁻¹ᵁ (pullback.snd g a).smoothLocus := by
    rw [htop]
    trivial
  rw [← hp]
  exact hmem

/-- **Smooth points are not singular.** A point of the smooth locus of a nodal curve lies outside
`Sing(g)`, the support of the first Fitting ideal of `Ω_{C/Y}`. -/
theorem not_mem_fittingSupport_of_mem_smoothLocus [IsNodalCurve g] (x : C)
    (hx : x ∈ g.smoothLocus) :
    x ∉ (Algebra.NodeFittingOmegaGluing.idealSheaf g 1).support := by
  intro hxs
  let K := AlgebraicClosure (Y.residueField (g x))
  let a := Geometry.NodeCompletedLocalGeometricChart.originalFieldMap (g x) K
  let pt : Spec (.of K) := ⟨⊥, Ideal.isPrime_bot⟩
  have hpt : a pt = g x := by
    change (Y.fromSpecResidueField (g x)) _ = g x
    exact Scheme.fromSpecResidueField_apply _ _
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := g) (g := a) x pt hpt.symm
  have hzs : z ∈ (pullback.snd g a).smoothLocus :=
    mem_smoothLocus_pullback_snd g a z (by rw [hz1]; exact hx)
  exact Algebra.NodeFittingGeometricIdealSheaf.not_mem_originalPullback_support_of_mem_smoothLocus
    g (g x) K (geometricFiber_dimension_le_one g K a) z hzs
    (Algebra.NodeFittingSupportPullback.mem_comap_support_of_mem_support _ _ z
      (by rw [hz1]; exact hxs))

/-- The germ at `x` of the restriction to an affine `U ⊆ g⁻¹V` of a pulled-back section is the
image of its germ under the stalk map. -/
theorem germ_res_app_eq_stalkMap {V : Y.Opens} {U : C.Opens} (hUV : U ≤ g ⁻¹ᵁ V) (x : C)
    (hx : x ∈ U) (β : Γ(Y, V)) :
    C.presheaf.germ U x hx (C.presheaf.map (homOfLE hUV).op (g.app V β)) =
      g.stalkMap x (Y.presheaf.germ V (g x) (hUV hx) β) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact TopCat.Presheaf.germ_res_apply C.presheaf (homOfLE hUV) x hx _

/-- **`Sing(g) ⊆ g⁻¹(Supp B)` on stalks.** If every point of `Sing(g)` maps into the support of an
ideal sheaf `B`, then `g^♯` maps the stalk of `B` at `g(x)` into the radical of the stalk at `x`
of the first Fitting ideal of `Ω_{C/Y}`. -/
theorem stalkMap_mem_radical_stalkIdeal_of_support_subset [LocallyOfFinitePresentation g]
    (B : Y.IdealSheafData)
    (hB : ∀ x' : C, x' ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf g 1).support →
      g x' ∈ B.support)
    (x : C) {b : Y.presheaf.stalk (g x)} (hb : b ∈ stalkIdeal B (g x)) :
    g.stalkMap x b ∈ (stalkIdeal (Algebra.NodeFittingOmegaGluing.idealSheaf g 1) x).radical := by
  set I := Algebra.NodeFittingOmegaGluing.idealSheaf g 1
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV0⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ g ⁻¹ᵁ V from hxV)
      (g ⁻¹ᵁ V).isOpen
  have hUV : U ≤ g ⁻¹ᵁ V := hUV0
  have hU' : IsAffineOpen U := hU
  have hV' : IsAffineOpen V := hV
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro P ⟨hIP, hP⟩
  -- the generization `x'` of `x` corresponding to `P`
  let Q : Ideal Γ(C, U) := P.comap (C.presheaf.germ U x hxU).hom
  have hQ : Q.IsPrime := Ideal.comap_isPrime _ P
  let y : Spec Γ(C, U) := ⟨Q, hQ⟩
  have hx'U : hU'.fromSpec y ∈ U := by
    show hU'.fromSpec y ∈ (U : Set C)
    rw [← hU'.range_fromSpec]
    exact ⟨y, rfl⟩
  set x' := hU'.fromSpec y
  let := TopCat.Presheaf.algebra_section_stalk C.presheaf ⟨x', hx'U⟩
  have hloc := hU'.isLocalization_stalk' y hx'U
  have hunder : ∀ r : Γ(C, U), C.presheaf.germ U x' hx'U r ∈ maximalIdeal (C.presheaf.stalk x') ↔
      r ∈ Q := fun r => IsLocalization.AtPrime.to_map_mem_maximal_iff (C.presheaf.stalk x') Q r
  -- `x'` lies in `Sing(g)`
  have hx'I : x' ∈ I.support := by
    rw [Algebra.NodeFittingGeometricNodeSupport.mem_support_iff_stalkIdeal_le_maximalIdeal,
      stalkIdeal_eq_map_germ I ⟨U, hU⟩ hx'U, Ideal.map_le_iff_le_comap]
    intro j hj
    rw [Ideal.mem_comap, hunder]
    apply hIP
    rw [stalkIdeal_eq_map_germ I ⟨U, hU⟩ hxU]
    exact Ideal.mem_map_of_mem _ hj
  have hgx' : g x' ∈ B.support := hB x' hx'I
  have hBle := (Algebra.NodeFittingGeometricNodeSupport.mem_support_iff_stalkIdeal_le_maximalIdeal
    B (g x')).mp hgx'
  -- every local equation of `B` on `V` vanishes at `x'`
  have key : ∀ β ∈ B.ideal ⟨V, hV⟩,
      g.stalkMap x (Y.presheaf.germ V (g x) hxV β) ∈ P := by
    intro β hβ
    have hmem : Y.presheaf.germ V (g x') (hUV hx'U) β ∈ maximalIdeal (Y.presheaf.stalk (g x')) := by
      apply hBle
      rw [stalkIdeal_eq_map_germ B ⟨V, hV⟩ (hUV hx'U)]
      exact Ideal.mem_map_of_mem _ hβ
    have h1 : C.presheaf.germ U x' hx'U (C.presheaf.map (homOfLE hUV).op (g.app V β)) ∈
        maximalIdeal (C.presheaf.stalk x') := by
      rw [germ_res_app_eq_stalkMap g hUV x' hx'U β]
      intro hu
      exact hmem (isUnit_of_map_unit (g.stalkMap x').hom _ hu)
    have h3 : C.presheaf.germ U x hxU (C.presheaf.map (homOfLE hUV).op (g.app V β)) ∈ P :=
      (hunder _).mp h1
    rwa [germ_res_app_eq_stalkMap g hUV x hxU β] at h3
  rw [stalkIdeal_eq_map_germ B ⟨V, hV⟩ hxV] at hb
  have hle : (B.ideal ⟨V, hV⟩).map (Y.presheaf.germ V (g x) hxV).hom ≤
      P.comap (g.stalkMap x).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro β hβ
    exact key β hβ
  exact hle hb

/-- **De Jong 3.1/3.3: `Sing(g) ⊆ g⁻¹(D)`.** If the nodal curve `g` is smooth at every point
over `Y ∖ Supp B`, then `g^♯` maps the stalk of `B` at `g(x)` into the radical of the stalk at `x`
of the first Fitting ideal of `Ω_{C/Y}`. -/
theorem stalkMap_mem_radical_stalkIdeal_of_isSmoothAt [IsNodalCurve g] (B : Y.IdealSheafData)
    (hsm : ∀ x' : C, g x' ∉ (B.support : Set Y) → IsSmoothAt g x')
    (x : C) {b : Y.presheaf.stalk (g x)} (hb : b ∈ stalkIdeal B (g x)) :
    g.stalkMap x b ∈ (stalkIdeal (Algebra.NodeFittingOmegaGluing.idealSheaf g 1) x).radical := by
  refine stalkMap_mem_radical_stalkIdeal_of_support_subset g B (fun x' hx' => ?_) x hb
  by_contra hnot
  exact not_mem_fittingSupport_of_mem_smoothLocus g x'
    ((isSmoothAt_iff_mem_smoothLocus g x').mp (hsm x' hnot)) hx'

end DeJongAlterations.StableModification.Resolution
