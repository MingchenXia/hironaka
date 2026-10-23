import DeJongAlterations.StableModification.Resolution.LocalDVR
import DeJongAlterations.StableModification.Resolution.LocalNodal
import DeJongAlterations.Geometry.RegularSmooth
import DeJongAlterations.Geometry.CurveBoundaryBasic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Completed local rings at smooth closed points of curves over an algebraically closed field

Let `K` be algebraically closed and `Z` a scheme locally of finite presentation over `K` all of
whose irreducible components have dimension one (a geometric fibre of a nodal curve). At a closed
smooth point `z`, `Ô_{Z,z} ≅ K[[w]]` as `K`-algebras (`nonempty_completedLocalRing_algEquiv_powerSeries`):
`𝒪_{Z,z}` is regular (Codex's `Geometry.RegularSmooth.isRegularLocalRing_of_mem_smoothLocus`), of
dimension one (`ringKrullDim_stalk_eq_one_of_isClosed`), with residue field `K`
(`residue_comp_baseToStalk_surjective`, the Nullstellensatz in the form of Mathlib's
`residueFieldIsoBase`), so its completion is `K[[w]]` (`LocalDVR`).

Consequently, for a nodal curve `g : C → Y` and a closed point `x` with `κ(g(x))` algebraically
closed, a point of `C` whose fibre point is smooth has `Ô_{C,x} ≅ Ô_{Y,g(x)}[[w]]`
(`exists_smooth_local_model_of_mem_smoothLocus`, de Jong 1996, 4.25 (i),
`references/dejong96-alterations/tex/page-0026.tex`); this applies in particular when `g` is
smooth at `x` (`fiberPoint_mem_smoothLocus_of_isSmoothAt`).
-/

noncomputable section

namespace DeJongAlterations.StableModification.Resolution

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open Geometry.NodeCompletedLocalMap DeJong

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

section Field

variable {Z : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K] (p : Z ⟶ Spec (.of K))

/-- **Nullstellensatz at a closed point.** If `Z` is locally of finite type over an algebraically
closed field `K`, then for every closed point `z` the map `K → 𝒪_{Z,z} → κ(z)` is surjective. -/
theorem residue_comp_baseToStalk_surjective [LocallyOfFiniteType p] (z : Z)
    (hz : IsClosed ({z} : Set Z)) :
    Function.Surjective ((Z.residue z).hom.comp (Scheme.baseToStalk p z).hom) := by
  let q := Z.fromSpecResidueField z
  let e := residueFieldIsoBase p z hz
  have h : q ≫ p = Spec.map e.inv := (SpecMap_residueFieldIsoBase_inv p z hz).symm
  have key := baseToStalk_stalkClosedPointTo q p e.inv h
  have hw : q (closedPoint (Z.residueField z)) = z := Scheme.fromSpecResidueField_apply z _
  suffices H : Function.Surjective ((Z.residue (q (closedPoint (Z.residueField z)))).hom.comp
      (Scheme.baseToStalk p (q (closedPoint (Z.residueField z)))).hom) by
    rw [hw] at H
    exact H
  intro c
  have : IsLocalHom (Scheme.stalkClosedPointTo q).hom := Scheme.isLocalHom_stalkClosedPointTo q
  let d := Z.descResidueField (Scheme.stalkClosedPointTo q)
  have hd : Z.residue _ ≫ d = Scheme.stalkClosedPointTo q :=
    Z.residue_descResidueField (Scheme.stalkClosedPointTo q)
  have hsurj : Function.Surjective e.inv.hom :=
    (ConcreteCategory.bijective_of_isIso e.inv).2
  obtain ⟨k, hk⟩ := hsurj (d.hom c)
  refine ⟨k, d.hom.injective ?_⟩
  rw [← hk, ← key, ← hd]
  rfl

/-- A closed point of a scheme all of whose irreducible components have dimension one has a
one-dimensional local ring. -/
theorem ringKrullDim_stalk_eq_one_of_isClosed
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1) (z : Z)
    (hz : IsClosed ({z} : Set Z)) : ringKrullDim (Z.presheaf.stalk z) = 1 := by
  rw [ringKrullDim_stalk_eq_coheight]
  have hZ : topologicalKrullDim Z ≤ 1 := by
    rw [Geometry.FiberDimensionUpperSemicontinuityClosedCover.topologicalKrullDim_eq_iSup_componentDimension]
    exact iSup_le fun W => (hdim W.val W.property).le
  apply le_antisymm
  · exact_mod_cast Geometry.CurveBoundary.coheight_le_one hZ z
  obtain ⟨W, hW, hzW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({z} : Set Z) isIrreducible_singleton
  have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
  let η := hW.1.genericPoint
  have hη : IsGenericPoint η W := by
    have := hW.1.isGenericPoint_genericPoint_closure
    rwa [hWc.closure_eq] at this
  have hηz : η ⤳ z := hη.specializes (hzW rfl)
  have hne : η ≠ z := by
    intro heq
    have hWz : W = {z} := by
      rw [← hη.def, heq, hz.closure_eq]
    have h1 := hdim W hW
    rw [hWz] at h1
    have h0 := topologicalKrullDim_zero_of_discreteTopology ({z} : Set Z)
    rw [h1] at h0
    exact absurd h0 (by norm_num)
  have hlt : z < η := lt_iff_le_not_ge.mpr ⟨hηz, fun h => hne (hηz.antisymm h).eq⟩
  have H := Order.coheight_add_one_le hlt
  have : (1 : ℕ∞) ≤ Order.coheight z := le_trans (by simp) H
  exact_mod_cast this

/-- **Smooth closed points of curves over an algebraically closed field.** If `Z` is locally of
finite presentation over an algebraically closed field `K` with all irreducible components of
dimension one, then at a closed smooth point `z`, `Ô_{Z,z} ≅ K[[w]]` as `K`-algebras. -/
theorem nonempty_completedLocalRing_algEquiv_powerSeries [LocallyOfFinitePresentation p]
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1) (z : Z)
    (hz : IsClosed ({z} : Set Z)) (hsm : z ∈ p.smoothLocus) :
    letI := Scheme.completedLocalRingAlgebra p z
    Nonempty (Z.completedLocalRing z ≃ₐ[K] PowerSeries K) := by
  let := Scheme.completedLocalRingAlgebra p z
  let : IsRegularLocalRing (Z.presheaf.stalk z) :=
    Geometry.RegularSmooth.isRegularLocalRing_of_mem_smoothLocus p z hsm
  have hdO := ringKrullDim_stalk_eq_one_of_isClosed hdim z hz
  let : IsRegularLocalRing (Z.completedLocalRing z) :=
    Algebra.CompletionRegularityAscent.isRegularLocalRing_completion _
  have hdR : ringKrullDim (Z.completedLocalRing z) = 1 := by
    rw [← (isRegularLocalRing_iff (Z.completedLocalRing z)).mp inferInstance,
      AdicCompletion.spanFinrank_maximalIdeal_eq, (isRegularLocalRing_iff _).mp inferInstance,
      hdO]
  have hres : Function.Surjective ((residue (Z.completedLocalRing z)).comp
      (algebraMap K (Z.completedLocalRing z))) := by
    intro c
    obtain ⟨c', rfl⟩ := (AdicCompletion.residueField_map_bijective (Z.presheaf.stalk z)).2 c
    obtain ⟨k, hk⟩ := residue_comp_baseToStalk_surjective p z hz c'
    refine ⟨k, ?_⟩
    rw [← hk]
    change residue _ (algebraMap (Z.presheaf.stalk z) (Z.completedLocalRing z)
      (Scheme.baseToStalk p z k)) = _
    rw [← ResidueField.map_residue]
    rfl
  obtain ⟨φ⟩ := nonempty_powerSeries_algEquiv_of_ringKrullDim_eq_one hdR hres
  exact ⟨φ.symm⟩

end Field

section Nodal

variable {C Y : Scheme.{u}} (g : C ⟶ Y)

/-- The fibre point over a point where `g` is smooth is a smooth point of the fibre. -/
theorem fiberPoint_mem_smoothLocus_of_isSmoothAt [LocallyOfFinitePresentation g] (x : C)
    (hx : IsSmoothAt g x) :
    originalFiberPoint g x ∈ (g.fiberToSpecResidueField (g x)).smoothLocus :=
  mem_smoothLocus_pullback_snd g (Y.fromSpecResidueField (g x)) (originalFiberPoint g x)
    (by
      change g.fiberι (g x) (originalFiberPoint g x) ∈ g.smoothLocus
      rw [originalFiberPoint_source]
      exact (isSmoothAt_iff_mem_smoothLocus g x).mp hx)

attribute [local instance] completedAlgebra

/-- **Local model at a smooth point (de Jong 4.25 (i)).** Let `g : C → Y` be a nodal curve, `x ∈ C`
a closed point with `κ(g(x))` algebraically closed, whose fibre point is smooth (e.g. `g` smooth at
`x`). Then `Ô_{C,x} ≃ Ô_{Y,g(x)}[[w]]`; `C` is regular at `x` if `𝒪_{Y,g(x)}` is; and for a ring
retraction `ρ` of `𝒪_{Y,g(x)} → 𝒪_{C,x}` (a section through `x`) the isomorphism can be chosen to
carry the kernel of the completed retraction onto `(w)`. -/
theorem exists_smooth_local_model_of_mem_smoothLocus [IsNodalCurve g] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian C] (x : C) (hx : IsClosed ({x} : Set C))
    [IsAlgClosed (Y.residueField (g x))]
    (hsm : originalFiberPoint g x ∈ (g.fiberToSpecResidueField (g x)).smoothLocus) :
    Nonempty (C.completedLocalRing x ≃ₐ[Y.completedLocalRing (g x)]
        PowerSeries (Y.completedLocalRing (g x))) ∧
      (IsRegularLocalRing (Y.presheaf.stalk (g x)) → IsRegularLocalRing (C.presheaf.stalk x)) ∧
      ∀ (ρ : C.presheaf.stalk x →+* Y.presheaf.stalk (g x)) (hρ : ∀ a, ρ (g.stalkMap x a) = a),
        ∃ φ : C.completedLocalRing x ≃ₐ[Y.completedLocalRing (g x)]
            PowerSeries (Y.completedLocalRing (g x)),
          (RingHom.ker (completedRetraction g x ρ hρ).toRingHom).map φ =
            Ideal.span {PowerSeries.X} := by
  have hdim : ∀ W ∈ irreducibleComponents (g.fiber (g x)), topologicalKrullDim W = 1 :=
    fun W hW => IsNodalCurve.pureGeometricFibers (Y.residueField (g x))
      (Y.fromSpecResidueField (g x)) W hW
  exact exists_smooth_local_model g x
    (nonempty_completedLocalRing_algEquiv_powerSeries (K := Y.residueField (g x))
      (g.fiberToSpecResidueField (g x)) hdim
      (originalFiberPoint g x) (isClosed_originalFiberPoint g x hx) hsm)

end Nodal

end DeJongAlterations.StableModification.Resolution
