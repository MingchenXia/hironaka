/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.Graph

/-!
# The graph of two coordinate systems: the point `(p, p)`

Kollár's point `(p, p) ∈ U_2(p)` of the graph ([Kol07, 95], the proof of Theorem 92); Włodarczyk's
component "whose images `φ_u(U)` and `φ_v(U)` contain `x`" (the proof of [Wlo05, Lemma 2.9.5]).
For two coordinate systems `u, v` on `U` whose coordinates all vanish at `p` (so that
`φ_u(p) = φ_v(p) = 0`, `Origin.lean`), the canonical morphism `s : Spec κ(p) ⟶ U` (through the
stalk, `Opens.fromSpecStalkOfMem`) has `s ≫ φ_u = s ≫ φ_v`: both are `Spec` of the ring map
`k[t] → κ(p)` sending every `t_i` to `0` and the constants to the `k`-structure of `κ(p)`
(`MvPolynomial.ringHom_ext`). The induced `Spec κ(p) ⟶ W = U ×_{𝔸ⁿ} U` sends the point of
`Spec κ(p)` to a point `q` over `p` for both projections; `s` is a preimmersion, so its stalk map
is surjective, its residue field map `κ(p) → κ(p)` is surjective, and both `κ(p) → κ(q)` are
isomorphisms (`isIso_residueFieldMap_of_comp`). The morphism `Spec κ(p) ⟶ W` itself is named
`graphPoint` in `GraphFormal.lean`; `GraphComponent.lean` and `GraphDiagonalPair.lean` build the
neighbourhood pair at this point.
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

/-! ### Residue field maps -/

section ResidueField

variable {Y Z : Scheme.{u}}

/-- The residue field map of a morphism surjective on stalks is surjective. -/
theorem residueFieldMap_surjective_of_surjectiveOnStalks (g : Y ⟶ Z) [SurjectiveOnStalks g]
    (y : Y) : Function.Surjective (g.residueFieldMap y) := by
  intro b
  obtain ⟨a, rfl⟩ := Y.residue_surjective y b
  obtain ⟨a', rfl⟩ := g.stalkMap_surjective y a
  refine ⟨Z.residue (g.base y) a', ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]

/-- A surjective residue field map is an isomorphism (a homomorphism of fields is injective). -/
theorem isIso_residueFieldMap_of_surjective (g : Y ⟶ Z) (y : Y)
    (h : Function.Surjective (g.residueFieldMap y)) : IsIso (g.residueFieldMap y) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(g.residueFieldMap y).hom.injective, h⟩

/-- If `g ≫ h` is surjective on stalks, `h` has trivial residue field extension at the image
points of `g`: `κ(h (g t)) → κ(g t)` is an isomorphism. -/
theorem isIso_residueFieldMap_of_comp {T W V : Scheme.{u}} (g : T ⟶ W) (h : W ⟶ V)
    [SurjectiveOnStalks (g ≫ h)] (t : T) : IsIso (h.residueFieldMap (g.base t)) := by
  have hs := residueFieldMap_surjective_of_surjectiveOnStalks (g ≫ h) t
  rw [Scheme.residueFieldMap_comp] at hs
  have hg : Function.Surjective (g.residueFieldMap t) := by
    intro b
    obtain ⟨a, ha⟩ := hs b
    exact ⟨h.residueFieldMap (g.base t) a, ha⟩
  have h1 : IsIso (g.residueFieldMap t) := isIso_residueFieldMap_of_surjective g t hg
  have h2 : IsIso (h.residueFieldMap (g.base t) ≫ g.residueFieldMap t) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(h.residueFieldMap (g.base t) ≫ g.residueFieldMap t).hom.injective, hs⟩
  exact IsIso.of_isIso_comp_right _ (g.residueFieldMap t)

end ResidueField

/-! ### The canonical morphism `Spec κ(p) ⟶ U` and its image in `𝔸ⁿ_k` -/

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {n : ℕ} {U : X.affineOpens}

/-- The canonical morphism `Spec κ(p) ⟶ U` for `p ∈ U`: `Spec` of the residue map followed by
`Spec 𝒪_{X,p} ⟶ U`. -/
noncomputable def specResidueFieldToOpens {p : X} (hpU : p ∈ U.1) :
    Spec (X.residueField p) ⟶ (U.1 : Scheme.{u}) :=
  Spec.map (X.residue p) ≫ U.1.fromSpecStalkOfMem p hpU

theorem specResidueFieldToOpens_ι {p : X} (hpU : p ∈ U.1) :
    specResidueFieldToOpens (U := U) hpU ≫ U.1.ι = X.fromSpecResidueField p := by
  rw [specResidueFieldToOpens, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  rfl

instance isPreimmersion_specResidueFieldToOpens {p : X} (hpU : p ∈ U.1) :
    IsPreimmersion (specResidueFieldToOpens (U := U) hpU) := by
  have : IsPreimmersion (specResidueFieldToOpens (U := U) hpU ≫ U.1.ι) := by
    rw [specResidueFieldToOpens_ι]; infer_instance
  exact IsPreimmersion.of_comp _ U.1.ι

theorem specResidueFieldToOpens_apply {p : X} (hpU : p ∈ U.1) (s : Spec (X.residueField p)) :
    (specResidueFieldToOpens (U := U) hpU).base s = ⟨p, hpU⟩ := by
  apply Subtype.ext
  have h := congrArg (fun g : Spec (X.residueField p) ⟶ X => g.base s)
    (specResidueFieldToOpens_ι (U := U) hpU)
  simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at h
  exact (Scheme.Opens.ι_apply U.1 _).symm.trans h

/-- The composite `Spec κ(p) ⟶ U ⟶ 𝔸ⁿ_k` is `Spec` of `k[t] → κ(p)`, `t_i ↦ v_i(p)`. -/
theorem specResidueFieldToOpens_toAffineSpace {p : X} (hpU : p ∈ U.1) (v : Fin n → Γ(X, U.1)) :
    specResidueFieldToOpens (U := U) hpU ≫ toAffineSpace f U.1 v =
      Spec.map (letI := f.sectionsAlgebra U.1
        CommRingCat.ofHom (MvPolynomial.aeval (R := k) v).toRingHom ≫
          X.presheaf.germ U.1 p hpU ≫ X.residue p) := by
  let _ := f.sectionsAlgebra U.1
  change Spec.map (X.residue p) ≫ U.1.fromSpecStalkOfMem p hpU ≫ (U.1.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) v).toRingHom)) = _
  rw [← Category.assoc (U.1.fromSpecStalkOfMem p hpU), Scheme.Opens.fromSpecStalkOfMem_toSpecΓ,
    Spec.map_comp, Spec.map_comp, Category.assoc]

/-- If all coordinates of `v` and `v'` vanish at `p`, the two composites `Spec κ(p) ⟶ 𝔸ⁿ_k`
agree: both send every `t_i` to `0`. -/
theorem specResidueFieldToOpens_toAffineSpace_eq {p : X} (hpU : p ∈ U.1)
    (v v' : Fin n → Γ(X, U.1))
    (hv : ∀ i, X.presheaf.germ U.1 p hpU (v i) ∈ maximalIdeal (X.presheaf.stalk p))
    (hv' : ∀ i, X.presheaf.germ U.1 p hpU (v' i) ∈ maximalIdeal (X.presheaf.stalk p)) :
    specResidueFieldToOpens (U := U) hpU ≫ toAffineSpace f U.1 v =
      specResidueFieldToOpens (U := U) hpU ≫ toAffineSpace f U.1 v' := by
  let _ := f.sectionsAlgebra U.1
  rw [specResidueFieldToOpens_toAffineSpace, specResidueFieldToOpens_toAffineSpace]
  congr 1
  ext1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
  · have hz : ∀ (w : Fin n → Γ(X, U.1)),
        (∀ j, X.presheaf.germ U.1 p hpU (w j) ∈ maximalIdeal (X.presheaf.stalk p)) →
        (CommRingCat.ofHom (MvPolynomial.aeval (R := k) w).toRingHom ≫
          X.presheaf.germ U.1 p hpU ≫ X.residue p).hom (MvPolynomial.X i) = 0 := by
      intro w hw
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr (hw i)
    rw [hz v hv, hz v' hv']

/-! ### The point `(p, p)` of the graph -/

namespace EtaleCoordinates

variable {f} (c c' : EtaleCoordinates f n U)

/-- If all coordinates of both systems vanish at `p`, there is a point `q` of `W` over `p` for both
projections, with `κ(q) = κ(p)` (Kollár's "`(p, p) ∈ U_2(p)`", [Kol07, 95]). -/
theorem exists_graph_point {p : X} (hpU : p ∈ U.1)
    (hc : ∀ i, X.presheaf.germ U.1 p hpU (c.v i) ∈ maximalIdeal (X.presheaf.stalk p))
    (hc' : ∀ i, X.presheaf.germ U.1 p hpU (c'.v i) ∈ maximalIdeal (X.presheaf.stalk p)) :
    ∃ q : c.graph c', (c.graphFst c').base q = ⟨p, hpU⟩ ∧ (c.graphSnd c').base q = ⟨p, hpU⟩ ∧
      IsIso ((c.graphFst c').residueFieldMap q) ∧ IsIso ((c.graphSnd c').residueFieldMap q) := by
  have hcomm := specResidueFieldToOpens_toAffineSpace_eq f hpU c.v c'.v hc hc'
  let q₀ : Spec (X.residueField p) ⟶ c.graph c' := pullback.lift _ _ hcomm
  have h1 : q₀ ≫ c.graphFst c' = specResidueFieldToOpens hpU := pullback.lift_fst _ _ _
  have h2 : q₀ ≫ c.graphSnd c' = specResidueFieldToOpens hpU := pullback.lift_snd _ _ _
  refine ⟨q₀.base default, ?_, ?_, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, h1, specResidueFieldToOpens_apply]
  · rw [← Scheme.Hom.comp_apply, h2, specResidueFieldToOpens_apply]
  · have : SurjectiveOnStalks (q₀ ≫ c.graphFst c') := by rw [h1]; infer_instance
    exact isIso_residueFieldMap_of_comp q₀ (c.graphFst c') default
  · have : SurjectiveOnStalks (q₀ ≫ c.graphSnd c') := by rw [h2]; infer_instance
    exact isIso_residueFieldMap_of_comp q₀ (c.graphSnd c') default

end EtaleCoordinates

end AlgebraicGeometry
