import DeJongAlterations.StableModification.Resolution.GlobalInitial
import DeJongAlterations.StableModification.DeJong.BaseStepSections
import DeJongAlterations.StableModification.Curves.Basic

/-!
# De Jong's resolution of a nodal curve over a strict normal crossings base

This file proves the interface statement `DeJong.SemistableResolution k`
(`semistableResolution`; de Jong 1996, 3.4–3.6 and 4.24–4.28,
`references/dejong96-alterations/tex/page-0013.tex`–`page-0015.tex`, `page-0026.tex`,
`page-0027.tex`; blueprint chapter `sm-dj-resolution-global.tex`,
`thm:sm-dj-semistable-resolution`).

Let `Y` be a regular projective variety over `k = k̄` with a strict normal crossings divisor `B`,
`g : C → Y` a projective nodal curve smooth over `Y ∖ B`, and `τ_1, …, τ_n` disjoint sections of
`g` into its smooth locus. On `C` we take

* the singular-locus ideal `N = Fitt_1(Ω_{C/Y})` (`Algebra.NodeFittingOmegaGluing.idealSheaf`),
* the boundary ideals `initialBoundary`: the unit ideal, the pullbacks of the reduced components
  of `B`, and the reduced images of the sections (`BoundaryIndex B n` indexes them).

At every closed point `x ∈ C` there is an initial chart (`goodAt_initial`): a formal regular chart
(`regChart_core`) if the fibre point of `x` is smooth — the coordinates are the section coordinate
`w` of `Ô_{C,x} ≅ Ô_{Y,g x}[[w]]` and a regular system of parameters of `𝒪_{Y,g x}` adapted to `B`
(`exists_adapted_parameters`) — and a formal node chart (`nodeChart_core`) with the stage-one
invariant if it is a node, from `Ô_{C,x} ≅ Ô_{Y,g x}[[u, v]]/(uv - ∏ t_D^{n_D})` (lane END-LOC,
`exists_completed_monomial_normal_form_of_regular`). The uniform bound of the exponents comes from
the stabilization of the iterated colons `(N : E_D^L)` (`exists_colonIter_stable`). The dimension
of `C` is `dim Y + 1` (`topologicalKrullDim_eq_succ`).

The two stages of blowups (`exists_regChart_modification`, `GlobalStages`) give an integral
projective modification with formal regular charts at all closed points, and the assembly with the
strictification of lane END-SNC (`exists_alterationWithBoundary_of_regChart`, `GlobalFinal`) gives
the alteration with boundary.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace DeJongAlterations.StableModification.Resolution.Global

set_option backward.isDefEq.respectTransparency false

open Strictify Algebra.NodeFittingIdealSheaf Geometry.NodeCompletedLocalMap
open DeJong (IsNodalCurve IsSmoothAt)

universe u

section Boundary

variable {C Y : Scheme.{u}}

/-- The boundary members on `C`: a unit member, the components of `B`, and the sections. -/
abbrev BoundaryIndex (B : Y.IdealSheafData) (n : ℕ) : Type u :=
  Option (DivisorComponent B ⊕ Fin n)

/-- **The initial boundary ideal sheaves** on `C` (blueprint `lem:sm-dj-initial-charts`): the unit
ideal, the pullbacks of the reduced components `D` of `B`, and the reduced images of the
sections `τ_i`. -/
def initialBoundary (g : C ⟶ Y) (B : Y.IdealSheafData) {n : ℕ} (τ : Fin n → (Y ⟶ C))
    (hτ : ∀ i, IsClosedImmersion (τ i)) : BoundaryIndex B n → C.IdealSheafData
  | none => ⊤
  | some (.inl D) => (Scheme.IdealSheafData.vanishingIdeal D.1).comap g
  | some (.inr i) => Scheme.IdealSheafData.vanishingIdeal (@rangeCloseds _ _ (τ i) (hτ i))

/-- The stalks of the unit ideal sheaf are the unit ideal. -/
theorem stalkIdeal_top' {X : Scheme.{u}} (x : X) : stalkIdeal (⊤ : X.IdealSheafData) x = ⊤ := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ _ U hxU]
  exact Ideal.map_top _

/-- Away from a closed subset its vanishing ideal is trivial. -/
theorem stalkIdeal_vanishingIdeal_eq_top {X : Scheme.{u}} (F : Closeds X) {x : X} (hx : x ∉ F) :
    stalkIdeal (Scheme.IdealSheafData.vanishingIdeal F) x = ⊤ := by
  by_contra h
  exact hx ((localIdeal_ne_top_iff F x).mp h)

/-- **The support of the initial boundary** is the union of the sections and of `g⁻¹ B`. -/
theorem exists_mem_support_initialBoundary_iff (g : C ⟶ Y) (B : Y.IdealSheafData) {n : ℕ}
    (τ : Fin n → (Y ⟶ C)) (hτ : ∀ i, IsClosedImmersion (τ i)) (x : C) :
    (∃ β, x ∈ (initialBoundary g B τ hτ β).support) ↔
      x ∈ (⋃ i, Set.range (τ i)) ∪ g ⁻¹' (B.support : Set Y) := by
  constructor
  · rintro ⟨β, hβ⟩
    rcases β with _ | D | i
    · rw [mem_support_iff_stalkIdeal_ne_top] at hβ
      exact absurd (stalkIdeal_top' x) hβ
    · right
      change x ∈ ((Scheme.IdealSheafData.vanishingIdeal D.1).comap g).support at hβ
      rw [Scheme.IdealSheafData.support_comap] at hβ
      change g x ∈ (Scheme.IdealSheafData.vanishingIdeal D.1).support at hβ
      rw [Geometry.ReducedClosedSubscheme.support_vanishingIdeal] at hβ
      exact Geometry.SNCSubdivisorComponent.component_le_support B D hβ
    · left
      change x ∈ (Scheme.IdealSheafData.vanishingIdeal (@rangeCloseds _ _ (τ i) (hτ i))).support
        at hβ
      rw [Geometry.ReducedClosedSubscheme.support_vanishingIdeal] at hβ
      exact Set.mem_iUnion.mpr ⟨i, hβ⟩
  · rintro (h | h)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
      refine ⟨some (.inr i), ?_⟩
      change x ∈ (Scheme.IdealSheafData.vanishingIdeal (@rangeCloseds _ _ (τ i) (hτ i))).support
      rw [Geometry.ReducedClosedSubscheme.support_vanishingIdeal]
      exact hi
    · let V := irreducibleComponent (⟨g x, h⟩ : B.support)
      let D := divisorComponentOf B V (irreducibleComponent_mem_irreducibleComponents _)
      have hxD : g x ∈ (D.val : Set Y) := ⟨⟨g x, h⟩, mem_irreducibleComponent, rfl⟩
      refine ⟨some (.inl D), ?_⟩
      change x ∈ ((Scheme.IdealSheafData.vanishingIdeal D.1).comap g).support
      rw [Scheme.IdealSheafData.support_comap]
      change g x ∈ (Scheme.IdealSheafData.vanishingIdeal D.1).support
      rw [Geometry.ReducedClosedSubscheme.support_vanishingIdeal]
      exact hxD

end Boundary

section Charts

variable {C Y : Scheme.{u}} (g : C ⟶ Y) [IsLocallyNoetherian Y]
  [IsLocallyNoetherian C] (B : Y.IdealSheafData) {n : ℕ} (τ : Fin n → (Y ⟶ C))
  (hτc : ∀ i, IsClosedImmersion (τ i))

attribute [local instance] completedAlgebra

/-- A product of coordinates with exponent `e_a` is the coordinate `T_a`. -/
theorem prod_pow_single {R κ : Type*} [CommMonoid R] [Fintype κ] [DecidableEq κ] (T : κ → R)
    (a : κ) : ∏ l, T l ^ (Pi.single a 1 : κ → ℕ) l = T a := by
  rw [Finset.prod_eq_single a (fun l _ hl ↦ by simp [hl]) (by simp)]
  simp

/-- **The initial regular chart** at a point whose fibre point is smooth: given
`φ : Ô_{C,x} ≃ Ô_{Y,y}[[w]]` over `Ô_{Y,y}` and a regular system of parameters `z` of `𝒪_{Y,y}`
adapted to `B`, the coordinates `w, z_1, …, z_m` form a formal regular chart for the initial
boundary, provided the sections through `x` have trace `(w)` with a generator from `𝒪_{C,x}`. -/
theorem regChart_core {m : ℕ} (x : C) (z : Fin m → Y.presheaf.stalk (g x))
    (j : {D : DivisorComponent B // g x ∈ D.val} → Fin m)
    (hz : Ideal.span (Set.range z) = maximalIdeal (Y.presheaf.stalk (g x)))
    (hzD : ∀ D, stalkIdeal (Scheme.IdealSheafData.vanishingIdeal D.1.val) (g x) =
      Ideal.span {z (j D)})
    (φ : C.completedLocalRing x ≃ₐ[Y.completedLocalRing (g x)]
      PowerSeries (Y.completedLocalRing (g x)))
    (hsec : ∀ i, stalkIdeal (initialBoundary g B τ hτc (some (.inr i))) x = ⊤ ∨
      ((stalkIdeal (initialBoundary g B τ hτc (some (.inr i))) x).map
          (C.toCompletedLocalRing x) = Ideal.span {φ.symm PowerSeries.X} ∧
        ∃ s, Ideal.span {C.toCompletedLocalRing x s} = Ideal.span {φ.symm PowerSeries.X})) :
    Nonempty (RegChart (C.presheaf.stalk x) m
      fun β ↦ stalkIdeal (initialBoundary g B τ hτc β) x) := by
  classical
  set E := initialBoundary g B τ hτc with hE
  let T : Fin (m + 1) → C.completedLocalRing x :=
    Fin.cons (φ.symm PowerSeries.X) fun l ↦ algebraMap _ _ (g.stalkMap x (z l))
  have hT0 : T 0 = φ.symm PowerSeries.X := rfl
  have hTs : ∀ l, T l.succ = algebraMap _ _ (g.stalkMap x (z l)) := fun l ↦ rfl
  have hspan : Ideal.span (Set.range T) = maximalIdeal (C.completedLocalRing x) :=
    span_regCoords_eq (g.stalkMap x).hom z hz φ.toRingEquiv (fun a ↦ φ.commutes a)
  let exp : BoundaryIndex B n → Fin (m + 1) → ℕ := fun β ↦ match β with
    | none => 0
    | some (.inl D) => if h : g x ∈ D.1 then Pi.single (j ⟨D, h⟩).succ 1 else 0
    | some (.inr i) => if stalkIdeal (E (some (.inr i))) x = ⊤ then 0 else Pi.single 0 1
  refine ⟨⟨T, hspan, exp, fun β ↦ ?_, ?_⟩⟩
  · rcases β with _ | D | i
    · change (stalkIdeal (⊤ : C.IdealSheafData) x).map _ = Ideal.span {∏ l, T l ^ (0 : Fin (m + 1) → ℕ) l}
      rw [stalkIdeal_top', Ideal.map_top]
      simp
    · by_cases h : g x ∈ D.1
      · change (stalkIdeal ((Scheme.IdealSheafData.vanishingIdeal D.1).comap g) x).map _ =
          Ideal.span {∏ l, T l ^ (if h : g x ∈ D.1 then Pi.single (j ⟨D, h⟩).succ 1 else 0) l}
        rw [dif_pos h, prod_pow_single, hTs, stalkIdeal_comap, hzD ⟨D, h⟩, Ideal.map_span,
          Set.image_singleton, Ideal.map_span, Set.image_singleton]
      · change (stalkIdeal ((Scheme.IdealSheafData.vanishingIdeal D.1).comap g) x).map _ =
          Ideal.span {∏ l, T l ^ (if h : g x ∈ D.1 then Pi.single (j ⟨D, h⟩).succ 1 else 0) l}
        rw [dif_neg h, stalkIdeal_comap, stalkIdeal_vanishingIdeal_eq_top _ h, Ideal.map_top,
          Ideal.map_top]
        simp
    · by_cases ht : stalkIdeal (E (some (.inr i))) x = ⊤
      · change (stalkIdeal (E (some (.inr i))) x).map _ = Ideal.span {∏ l, T l ^
          (if stalkIdeal (E (some (.inr i))) x = ⊤ then 0 else Pi.single 0 1 : Fin (m + 1) → ℕ) l}
        rw [if_pos ht, ht, Ideal.map_top]
        simp
      · change (stalkIdeal (E (some (.inr i))) x).map _ = Ideal.span {∏ l, T l ^
          (if stalkIdeal (E (some (.inr i))) x = ⊤ then 0 else Pi.single 0 1 : Fin (m + 1) → ℕ) l}
        rw [if_neg ht, prod_pow_single, hT0]
        exact ((hsec i).resolve_left ht).1
  · refine rad_of_coord (algebraMap _ _) exp fun l hl ↦ ?_
    cases l using Fin.cases with
    | zero =>
      obtain ⟨β, hβ⟩ := hl
      rcases β with _ | D | i
      · exact absurd rfl hβ
      · exfalso
        apply hβ
        change (if h : g x ∈ D.1 then Pi.single (j ⟨D, h⟩).succ 1 else 0 : Fin (m + 1) → ℕ) 0 = 0
        split_ifs
        · exact Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm _
        · rfl
      · by_cases ht : stalkIdeal (E (some (.inr i))) x = ⊤
        · exfalso
          apply hβ
          change (if stalkIdeal (E (some (.inr i))) x = ⊤ then 0 else Pi.single 0 1 :
            Fin (m + 1) → ℕ) 0 = 0
          rw [if_pos ht]
          rfl
        · obtain ⟨s, hs⟩ := ((hsec i).resolve_left ht).2
          exact ⟨s, hs⟩
    | succ l => exact ⟨g.stalkMap x (z l), rfl⟩

/-- Kernels are unchanged by composing with an isomorphism. -/
theorem ker_comp_iso_hom {A A' A'' : CommRingCat.{u}} (f : A ⟶ A') (e : A' ≅ A'') :
    RingHom.ker (f ≫ e.hom).hom = RingHom.ker f.hom := by
  rw [CommRingCat.hom_comp]
  exact RingHom.ker_comp_of_injective _ e.commRingCatIsoToRingEquiv.injective

/-- **The initial node chart** at a closed point whose fibre point is a node (de Jong 3.3, 3.5,
4.25 (ii)): with a regular system of parameters `z` of `𝒪_{Y,g x}` adapted to `B`, the local
model `Ô_{C,x} ≅ Ô_{Y,g x}[[u, v]]/(uv - ∏ t_D^{n_D})` of lane END-LOC is a formal node chart for
the singular-locus ideal and the initial boundary, with the stage-one invariant for any bound `L`
at which the iterated colons `(N : E_β^L)` are stable. -/
theorem nodeChart_core {k : Type u} [Field k] [IsAlgClosed k] (pC : C ⟶ Spec (.of k))
    [LocallyOfFiniteType pC] [IsNodalCurve g] [NoetherianSpace Y]
    (hsm : ∀ x' : C, g x' ∉ (B.support : Set Y) → IsSmoothAt g x')
    (hτsm : ∀ i (y : Y), IsSmoothAt g (τ i y)) {m : ℕ} (x : C) (hx : IsClosed ({x} : Set C))
    [IsAlgClosed (Y.residueField (g x))] [IsRegularLocalRing (Y.presheaf.stalk (g x))]
    (hdimx : (m + 1 : WithBot ℕ∞) ≤ ringKrullDim (C.presheaf.stalk x))
    (z : Fin m → Y.presheaf.stalk (g x)) (j : {D : DivisorComponent B // g x ∈ D.val} → Fin m)
    (hj : Function.Injective j)
    (hz : Ideal.span (Set.range z) = maximalIdeal (Y.presheaf.stalk (g x)))
    (hz2 : ∀ l, z l ∉ maximalIdeal (Y.presheaf.stalk (g x)) ^ 2)
    (hzD : ∀ D, stalkIdeal (Scheme.IdealSheafData.vanishingIdeal D.1.val) (g x) =
      Ideal.span {z (j D)})
    (hzB : stalkIdeal B (g x) = Ideal.span {∏ᶠ D, z (j D)})
    (hns : originalFiberPoint g x ∉ (g.fiberToSpecResidueField (g x)).smoothLocus) (L : ℕ)
    (hL : ∀ β, stalkIdeal (colonIter (Algebra.NodeFittingOmegaGluing.idealSheaf g 1)
        (initialBoundary g B τ hτc β) L) x =
      stalkIdeal (colonIter (Algebra.NodeFittingOmegaGluing.idealSheaf g 1)
        (initialBoundary g B τ hτc β) (L + 1)) x) :
    ∃ c : NodeChart k (C.presheaf.stalk x) m
        (stalkIdeal (Algebra.NodeFittingOmegaGluing.idealSheaf g 1) x)
        (fun β ↦ stalkIdeal (initialBoundary g B τ hτc β) x),
      Stage1Inv L ∅ none (L + 1) c.n c.exp := by
  classical
  set E := initialBoundary g B τ hτc with hE
  let K := {D : DivisorComponent B // g x ∈ D.val}
  let : Fintype K := Fintype.ofFinite K
  have hnode := isGeometricOrdinaryDoublePoint_of_not_mem_smoothLocus g x hx hns
  obtain ⟨e⟩ := nonempty_splitNode_closedFiber_of_isGeometricOrdinaryDoublePoint g x hnode
  let t : K → Y.presheaf.stalk (g x) := fun D ↦ z (j D)
  have hzm : ∀ l, z l ∈ maximalIdeal (Y.presheaf.stalk (g x)) :=
    fun l ↦ hz ▸ Ideal.subset_span ⟨l, rfl⟩
  have hb : ∏ D, t D ∈ stalkIdeal B (g x) := by
    rw [hzB, finprod_eq_prod_of_fintype]
    exact Ideal.mem_span_singleton_self _
  have hsing := stalkMap_mem_radical_stalkIdeal_of_isSmoothAt g B hsm x hb
  obtain ⟨n', hn', -, φ, hφ⟩ := exists_completed_monomial_normal_form_of_regular g x e t
    (fun D ↦ hzm _) (fun D ↦ hz2 _) hsing
  -- the exponents on `Fin m`
  let nn : Fin m → ℕ := Function.extend j n' 0
  have hnj : ∀ D, nn (j D) = n' D := fun D ↦ hj.extend_apply n' 0 D
  have hnz : ∀ l, (¬ ∃ D, j D = l) → nn l = 0 := fun l hl ↦ by
    simp only [nn, Function.extend_apply' _ _ _ hl, Pi.zero_apply]
  have hprod : ∀ w : Fin m → Y.completedLocalRing (g x),
      ∏ l, w l ^ nn l = ∏ D, w (j D) ^ n' D := by
    intro w
    rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image j)), Finset.prod_image
      (fun D _ D' _ h ↦ hj h)]
    · simp only [hnj]
    · intro l _ hl
      rw [hnz l (fun ⟨D, hD⟩ ↦ hl (Finset.mem_image.mpr ⟨D, Finset.mem_univ _, hD⟩)), pow_zero]
  have hsum : ∑ l, nn l = ∑ D, n' D := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image j)), Finset.sum_image
      (fun D _ D' _ h ↦ hj h)]
    · exact Finset.sum_congr rfl fun D _ ↦ hnj D
    · intro l _ hl
      exact hnz l (fun ⟨D, hD⟩ ↦ hl (Finset.mem_image.mpr ⟨D, Finset.mem_univ _, hD⟩))
  have hn : ∑ l, nn l ≠ 0 := by omega
  -- the `k`-algebra structure and the recognition of the node model
  let : Algebra k (C.presheaf.stalk x) := (Scheme.baseToStalk pC x).hom.toAlgebra
  have hresP : Function.Bijective (algebraMap k (ResidueField (C.presheaf.stalk x))) :=
    ⟨(algebraMap k _).injective, residue_comp_baseToStalk_surjective' pC x hx⟩
  let : Algebra k (C.completedLocalRing x) :=
    ((algebraMap (C.presheaf.stalk x) (C.completedLocalRing x)).comp
      (algebraMap k (C.presheaf.stalk x))).toAlgebra
  have hres : Function.Surjective (algebraMap k (ResidueField (C.completedLocalRing x))) :=
    (bijective_constQ_residue (k := k) hresP).2
  have hdimO : (m + 1 : WithBot ℕ∞) ≤ ringKrullDim (C.completedLocalRing x) :=
    hdimx.trans (Algebra.CompletionRegularityAscent.ringKrullDim_le_completion _)
  have hh : (∏ D, Y.toCompletedLocalRing (g x) (t D) ^ n' D) =
      ∏ l, algebraMap _ (Y.completedLocalRing (g x)) (z l) ^ nn l :=
    (hprod fun l ↦ algebraMap _ (Y.completedLocalRing (g x)) (z l)).symm
  obtain ⟨eN, heU, heV, heZ⟩ := exists_nodeModel_ringEquiv (k := k) (g.stalkMap x).hom hres z hz
    nn hn _ hh φ.toRingEquiv (fun a ↦ φ.commutes a) hdimO
  -- the traces
  have htN : (stalkIdeal (Algebra.NodeFittingOmegaGluing.idealSheaf g 1) x).map
      (algebraMap _ (C.completedLocalRing x)) =
        Ideal.span {eN (nodeU k nn), eN (nodeV k nn)} := by
    rw [heU, heV]
    have h1 : completedSingularIdeal g x = (splitCoordinateIdeal _ _).map φ.toRingEquiv.symm := by
      rw [← hφ, Ideal.map_symm]
      exact (Ideal.comap_map_of_bijective _ φ.bijective).symm
    change completedSingularIdeal g x = _
    rw [h1, splitCoordinateIdeal, Ideal.map_span, Set.image_pair]
  have hxτ : ∀ i, x ∉ Set.range (τ i) := by
    rintro i ⟨y', rfl⟩
    exact hns (fiberPoint_mem_smoothLocus_of_isSmoothAt g _ (hτsm i y'))
  have hZ0 : nodeZMon k nn 0 = 1 := by simp
  let exp : BoundaryIndex B n → Fin m → ℕ := fun β ↦ match β with
    | none => 0
    | some (.inl D) => if h : g x ∈ D.1 then Pi.single (j ⟨D, h⟩) 1 else 0
    | some (.inr _) => 0
  have htE : ∀ β, (stalkIdeal (E β) x).map (algebraMap _ (C.completedLocalRing x)) =
      Ideal.span {eN (nodeZMon k nn (exp β))} := by
    intro β
    rcases β with _ | D | i
    · change (stalkIdeal (⊤ : C.IdealSheafData) x).map _ = Ideal.span {eN (nodeZMon k nn 0)}
      rw [stalkIdeal_top', Ideal.map_top, hZ0, map_one, Ideal.span_singleton_one]
    · change (stalkIdeal ((Scheme.IdealSheafData.vanishingIdeal D.1).comap g) x).map _ =
        Ideal.span {eN (nodeZMon k nn (if h : g x ∈ D.1 then Pi.single (j ⟨D, h⟩) 1 else 0))}
      by_cases h : g x ∈ D.1
      · rw [dif_pos h, nodeZMon_single, heZ, stalkIdeal_comap, hzD ⟨D, h⟩, Ideal.map_span,
          Set.image_singleton, Ideal.map_span, Set.image_singleton]
      · rw [dif_neg h, hZ0, map_one, Ideal.span_singleton_one, stalkIdeal_comap,
          stalkIdeal_vanishingIdeal_eq_top _ h, Ideal.map_top, Ideal.map_top]
    · change (stalkIdeal (Scheme.IdealSheafData.vanishingIdeal
          (@rangeCloseds _ _ (τ i) (hτc i))) x).map _ = Ideal.span {eN (nodeZMon k nn 0)}
      rw [stalkIdeal_vanishingIdeal_eq_top _ (hxτ i), Ideal.map_top, hZ0, map_one,
        Ideal.span_singleton_one]
  let c : NodeChart k (C.presheaf.stalk x) m
      (stalkIdeal (Algebra.NodeFittingOmegaGluing.idealSheaf g 1) x)
      (fun β ↦ stalkIdeal (E β) x) :=
    { n := nn
      pos := hn
      e := eN
      trace_N := htN
      exp := exp
      trace_E := htE
      coord := fun l _ ↦ ⟨g.stalkMap x (z l), by rw [heZ]⟩ }
  refine ⟨c, ?_⟩
  -- the stage-one invariant
  have hsingle : ∀ β i, exp β = Pi.single i 1 →
      ∃ (D : DivisorComponent B) (h : g x ∈ D.1), β = some (.inl D) ∧ j ⟨D, h⟩ = i := by
    intro β i hβ
    have hne : exp β ≠ 0 := by
      rw [hβ]
      intro h0
      have := congrFun h0 i
      simp at this
    rcases β with _ | D | i'
    · exact absurd rfl hne
    · by_cases h : g x ∈ D.1
      · refine ⟨D, h, rfl, ?_⟩
        change (if h : g x ∈ D.1 then Pi.single (j ⟨D, h⟩) 1 else 0 : Fin m → ℕ) = _ at hβ
        rw [dif_pos h] at hβ
        by_contra hji
        have := congrFun hβ (j ⟨D, h⟩)
        rw [Pi.single_eq_same, Pi.single_eq_of_ne hji] at this
        exact one_ne_zero this
      · exfalso
        apply hne
        change (if h : g x ∈ D.1 then Pi.single (j ⟨D, h⟩) 1 else 0 : Fin m → ℕ) = 0
        rw [dif_neg h]
    · exact absurd rfl hne
  have hcov : ∀ i, nn i ≠ 0 → ∃ β, exp β = Pi.single i 1 := by
    intro i hi
    by_cases hD : ∃ D, j D = i
    · obtain ⟨⟨D, h⟩, rfl⟩ := hD
      refine ⟨some (.inl D), ?_⟩
      change (if h : g x ∈ D.1 then Pi.single (j ⟨D, h⟩) 1 else 0 : Fin m → ℕ) = _
      rw [dif_pos h]
    · exact absurd (hnz i hD) hi
  have hbound : ∀ i, nn i ≤ L := by
    intro i
    by_cases hi : nn i = 0
    · omega
    obtain ⟨β, hβ⟩ := hcov i hi
    refine c.n_le_of_iterColon_eq β i hβ L ?_
    have := hL β
    rwa [stalkIdeal_colonIter, stalkIdeal_colonIter] at this
  refine ⟨fun β ↦ ?_, fun β β' i hβ hβ' ↦ ?_, hcov, hbound, fun β hβ ↦ absurd hβ
    (Set.notMem_empty β), fun i _ ↦ (hbound i).trans (Nat.le_succ _)⟩
  · rcases β with _ | D | i
    · exact Or.inl rfl
    · change (if h : g x ∈ D.1 then Pi.single (j ⟨D, h⟩) 1 else 0 : Fin m → ℕ) = 0 ∨
        ∃ i, (if h : g x ∈ D.1 then Pi.single (j ⟨D, h⟩) 1 else 0 : Fin m → ℕ) = Pi.single i 1
      by_cases h : g x ∈ D.1
      · rw [dif_pos h]; exact Or.inr ⟨_, rfl⟩
      · rw [dif_neg h]; exact Or.inl rfl
    · exact Or.inl rfl
  · obtain ⟨D, h, rfl, hD⟩ := hsingle β i hβ
    obtain ⟨D', h', rfl, hD'⟩ := hsingle β' i hβ'
    have := hj (hD.trans hD'.symm)
    simp only [Subtype.mk.injEq] at this
    rw [this]

end Charts

section ClosedPoints

variable {k : Type u} [Field k] [IsAlgClosed k] {C Y : Scheme.{u}} (pY : Y ⟶ Spec (.of k))
  (g : C ⟶ Y) [IsIntegral Y] [LocallyOfFiniteType pY] [LocallyOfFiniteType (g ≫ pY)]

include pY

/-- The closed-point data on `Y` below a closed point of `C`: `g x` is closed, its residue field
is algebraically closed and its local ring has dimension `dim Y`. -/
theorem closedPoint_data {m : ℕ} (hdimY : topologicalKrullDim Y = m) (x : C)
    (hx : IsClosed ({x} : Set C)) :
    IsClosed ({g x} : Set Y) ∧ IsAlgClosed (Y.residueField (g x)) ∧
      ringKrullDim (Y.presheaf.stalk (g x)) = m := by
  have hy : IsClosed ({g x} : Set Y) :=
    Curves.isClosed_image_of_isClosed (q := g ≫ pY) (q' := pY) g rfl hx
  refine ⟨hy, IsAlgClosed.of_ringEquiv k _
    (residueFieldIsoBase pY (g x) hy).symm.commRingCatIsoToRingEquiv, ?_⟩
  rw [ringKrullDim_stalk_eq_of_isClosed pY (g x) hy, hdimY]

omit pY in
/-- A section through `τ i y'` has trace given by the kernel of its stalk retraction. -/
theorem ker_sectionStalkRetraction (B : Y.IdealSheafData) {n : ℕ} (τ : Fin n → (Y ⟶ C)) (hτ : ∀ i, τ i ≫ g = 𝟙 Y)
    (hτc : ∀ i, IsClosedImmersion (τ i)) (i : Fin n) (y' : Y) :
    RingHom.ker (sectionStalkRetraction g (τ i) (hτ i) y') =
      stalkIdeal (initialBoundary g B τ hτc (some (.inr i))) (τ i y') := by
  have := hτc i
  change _ = localIdeal (rangeCloseds (τ i)) (τ i y')
  rw [localIdeal_rangeCloseds]
  exact ker_comp_iso_hom _ _

end ClosedPoints

section Initial

variable {k : Type u} [Field k] [IsAlgClosed k] {C Y : Scheme.{u}} (pY : Y ⟶ Spec (.of k))
  (g : C ⟶ Y) [IsIntegral Y] [IsNoetherian Y] [IsIntegral C] [IsLocallyNoetherian C]
  [LocallyOfFiniteType pY] [LocallyOfFiniteType (g ≫ pY)] [IsNodalCurve g]
  (B : Y.IdealSheafData) (hB : IsStrictNormalCrossings B) (hreg : IsRegularScheme Y)
  (hsm : ∀ x : C, g x ∉ (B.support : Set Y) → IsSmoothAt g x)

attribute [local instance] completedAlgebra

include pY hB hreg hsm

/-- **Initial charts** (blueprint `lem:sm-dj-initial-charts`; de Jong 3.3–3.5, 4.23–4.25). At
every closed point of `C` there is a formal node chart with the stage-one invariant for the
uniform bound `L`, or a formal regular chart at which the singular-locus ideal is trivial. -/
theorem goodAt_initial {n : ℕ} (τ : Fin n → (Y ⟶ C)) (hτ : ∀ i, τ i ≫ g = 𝟙 Y)
    (hτc : ∀ i, IsClosedImmersion (τ i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (τ i)) (Set.range (τ j)))
    (hτsm : ∀ i (y : Y), IsSmoothAt g (τ i y)) {m : ℕ} (hdimY : topologicalKrullDim Y = m)
    (hdimC : topologicalKrullDim C = (m + 1 : ℕ)) (L : ℕ)
    (hL : ∀ β x, stalkIdeal (colonIter (Algebra.NodeFittingOmegaGluing.idealSheaf g 1)
        (initialBoundary g B τ hτc β) L) x =
      stalkIdeal (colonIter (Algebra.NodeFittingOmegaGluing.idealSheaf g 1)
        (initialBoundary g B τ hτc β) (L + 1)) x)
    (x : C) (hx : IsClosed ({x} : Set C)) :
    GoodAt k m (Algebra.NodeFittingOmegaGluing.idealSheaf g 1) (initialBoundary g B τ hτc)
      (Stage1Inv L ∅ none (L + 1)) x := by
  obtain ⟨hy, hac, hmY⟩ := closedPoint_data pY g hdimY x hx
  have : IsRegularLocalRing (Y.presheaf.stalk (g x)) := hreg (g x)
  obtain ⟨z, j, hj, hz, hz2, hzD, hzB⟩ := exists_adapted_parameters B hB (g x) hmY
  by_cases hfib : originalFiberPoint g x ∈ (g.fiberToSpecResidueField (g x)).smoothLocus
  · refine Or.inr ⟨?_, stalkIdeal_fitting_eq_top_of_fiberSmooth g x hfib⟩
    rcases exists_local_model g B hB hsm x hx with ⟨-, ⟨φ₀⟩, -, hret⟩ | ⟨hns, -⟩
    · by_cases hsec : ∃ i y', τ i y' = x
      · obtain ⟨i, y', rfl⟩ := hsec
        let ρ := sectionStalkRetraction g (τ i) (hτ i) y'
        have hρ := sectionStalkRetraction_stalkMap g (τ i) (hτ i) y'
        obtain ⟨φ, hφ⟩ := hret ρ hρ
        obtain ⟨hker, s, -, hs⟩ := section_coordinate g (τ i y') ρ hρ φ hφ
        refine regChart_core g B τ hτc (τ i y') z j hz hzD φ fun i' ↦ ?_
        by_cases hii : i' = i
        · subst hii
          exact Or.inr ⟨by rw [← ker_sectionStalkRetraction g B τ hτ hτc]; exact hker, s, hs⟩
        · left
          refine stalkIdeal_vanishingIdeal_eq_top _ fun ⟨y'', hy''⟩ ↦ ?_
          exact Set.disjoint_left.mp (hdisj i' i hii) ⟨y'', hy''⟩ ⟨y', rfl⟩
      · exact regChart_core g B τ hτc x z j hz hzD φ₀ fun i ↦ Or.inl
          (stalkIdeal_vanishingIdeal_eq_top _ fun ⟨y', hy'⟩ ↦ hsec ⟨i, y', hy'⟩)
    · exact absurd hfib hns
  · have hdimx : (m + 1 : WithBot ℕ∞) ≤ ringKrullDim (C.presheaf.stalk x) := by
      rw [ringKrullDim_stalk_eq_of_isClosed (g ≫ pY) x hx, hdimC]
      simp
    exact Or.inl (nodeChart_core g B τ hτc (g ≫ pY) hsm hτsm x hx hdimx z j hj hz hz2 hzD hzB
      hfib L fun β ↦ hL β x)

/-- **The dimension of `C`**: `dim C = dim Y + 1`, computed on the completed local ring at a
closed point (lane END-LOC's local models, `ringKrullDim_powerSeries_eq`,
`ringKrullDim_splitNodeRing_eq`). -/
theorem topologicalKrullDim_eq_succ {m : ℕ} (hdimY : topologicalKrullDim Y = m) :
    topologicalKrullDim C = (m + 1 : ℕ) := by
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace (g ≫ pY)
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := C))
    isClosed_univ.isLocallyClosed
  obtain ⟨hy, hac, hmY⟩ := closedPoint_data pY g hdimY x hx
  have : IsRegularLocalRing (Y.presheaf.stalk (g x)) := hreg (g x)
  have : IsRegularLocalRing (Y.completedLocalRing (g x)) :=
    Algebra.CompletionRegularityAscent.isRegularLocalRing_completion _
  have hmY' : ringKrullDim (Y.completedLocalRing (g x)) = m := by
    rw [ringKrullDim_completion_eq, hmY]
  rw [← ringKrullDim_stalk_eq_of_isClosed (g ≫ pY) x hx, ← ringKrullDim_completion_eq]
  rcases exists_local_model g B hB hsm x hx with ⟨-, ⟨φ₀⟩, -, -⟩ |
      ⟨-, r, t, ht, -, -, n', hn', -, φ, -⟩
  · rw [ringKrullDim_eq_of_ringEquiv φ₀.toRingEquiv]
    exact ringKrullDim_powerSeries_eq hmY'
  · rw [ringKrullDim_eq_of_ringEquiv φ.toRingEquiv]
    refine ringKrullDim_splitNodeRing_eq hmY' ?_
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : ∑ i, n' i ≠ 0)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ?_ _ (Nat.pos_of_ne_zero hi))
    exact map_nonunit (algebraMap (Y.presheaf.stalk (g x)) (Y.completedLocalRing (g x))) _ (ht i)

end Initial

/-- **De Jong's semistable resolution** (de Jong 1996, 3.4–3.6 with 4.26–4.27; blueprint
`thm:sm-dj-semistable-resolution`). Let `Y` be a regular projective variety over an
algebraically closed field with a strict normal crossings divisor `B`, `g : C → Y` a projective
nodal curve smooth over `Y ∖ B`, and `τ_i` disjoint sections into the smooth locus of `g`. Then
there is a projective modification `C' → C` with `C'` regular, such that the preimage of the
sections and of `g⁻¹ B` is (after the strictification of lane END-SNC) a strict normal crossings
divisor: an alteration with boundary which is a modification. -/
theorem semistableResolution (k : Type u) [Field k] [IsAlgClosed k] :
    DeJong.SemistableResolution.{u} k := by
  intro Y pY hY hpY hreg B hB C g hC hpC hnod hsm n τ hτ hdisj hτsm
  classical
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace pY
  have : IsNoetherian Y := {}
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (g ≫ pY)
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (g ≫ pY)
  have : IsSeparated g := IsSeparated.of_comp g pY
  have hτc : ∀ i, IsClosedImmersion (τ i) :=
    fun i ↦ DeJong.isClosedImmersion_of_comp_eq_id g (τ i) (hτ i)
  let : Fintype (DivisorComponent B) := Fintype.ofFinite _
  obtain ⟨m, hm⟩ := DeJong.exists_nat_topologicalKrullDim_eq pY
  have hdimC := topologicalKrullDim_eq_succ pY g B hB hreg hsm hm
  obtain ⟨L, hL⟩ := exists_colonIter_stable (Algebra.NodeFittingOmegaGluing.idealSheaf g 1)
    (initialBoundary g B τ hτc)
  have hgood := goodAt_initial pY g B hB hreg hsm τ hτ hτc hdisj hτsm hm hdimC L hL
  exact exists_alterationWithBoundary_of_regChart (g ≫ pY) hdimC (initialBoundary g B τ hτc) _
    (fun x ↦ (exists_mem_support_initialBoundary_iff g B τ hτc x).symm)
    (exists_regChart_modification (g ≫ pY) hpC hdimC _ _ L none hgood)

end DeJongAlterations.StableModification.Resolution.Global
