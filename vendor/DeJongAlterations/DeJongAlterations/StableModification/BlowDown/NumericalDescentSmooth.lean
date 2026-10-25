/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.NumericalDescentEuler
import DeJongAlterations.StableModification.Curves.SemistableOpen

/-!
# Smoothness descends at closed points along an extension of algebraically closed fields

Let `k ⊆ K` be algebraically closed fields, `Y` a scheme locally of finite type over `k` and
`π : Y_K → Y` the base change. If `x ∈ Y_K` lies over a closed point `y = π(x)` of `Y` and
`Y_K → Spec K` is smooth at `x`, then `Y → Spec k` is smooth at `y`
(`isSmoothAt_of_isSmoothAt_bcSnd`, and `isSmoothAt_of_isPullback` for an arbitrary pullback
square). Over a perfect field smoothness at a point is regularity of the local ring
(`Geometry.RegularSmoothConverse.mem_smoothLocus_iff_isRegularLocalRing`); on an affine chart
`Spec (K ⊗_k B) ⊆ Y_K` over `Spec B ⊆ Y` (`Curves.SemistableOpen.tensorChart`) regularity of
`(K ⊗_k B)_z` descends to `B_𝔪` for `𝔪 = z ∩ B` maximal
(`isRegularLocalRing_of_tensor_left`).

This is the smoothness clause of `BlowDown.NoClosedExc.NumericalDescent` (Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010), §1.2: the special points of the
fibres are compatible with extension of the algebraically closed ground field).

Blueprint: `sm-blow-down-unconditional.tex`, `lem:sm-bdu-smooth-descent`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct

namespace DeJongAlterations.StableModification.BlowDown.NumericalDescent

universe u

open Cohomology Curves.SemistableOpen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Smooth

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Curves.SemistableOpen.locallyOfFinitePresentation_spec

variable {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] (ψ : k →+* K)
  {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q]

omit [IsAlgClosed k] [LocallyOfFiniteType q] in
/-- The square `Spec B → Y → Spec k` of an affine open `U = Spec B` of `Y`, in the form of
`Curves.SemistableOpen.tensorChart`. -/
theorem fromSpec_comp_eq {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra q U
    hU.fromSpec ≫ q = Spec.map (CommRingCat.ofHom (algebraMap k Γ(Y, U))) ≫ 𝟙 _ := by
  let := sectionsAlgebra q U
  rw [Category.comp_id, ← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- **Smoothness descends at closed points along `K / k`** (blueprint
`lem:sm-bdu-smooth-descent`): if `Y_K → Spec K` is smooth at `x` and `π(x)` is a closed point of
`Y`, then `Y → Spec k` is smooth at `π(x)`. -/
theorem isSmoothAt_of_isSmoothAt_bcSnd
    (x : pullback (C := Scheme.{u}) q (Spec.map (CommRingCat.ofHom ψ)))
    (hy : IsClosed ({bcFst ψ q x} : Set Y)) (h : DeJong.IsSmoothAt (bcSnd ψ q) x) :
    DeJong.IsSmoothAt q (bcFst ψ q x) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := bcFst ψ q x) (U := ⊤) trivial
  let := sectionsAlgebra q U
  let := ψ.toAlgebra
  have : Algebra.FiniteType k Γ(Y, U) := finiteType_sections q hU
  have hsq := fromSpec_comp_eq q hU
  have ha : Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom ψ) := by
    rw [Category.comp_id]
    rfl
  obtain ⟨z, rfl⟩ : x ∈ Set.range (tensorChart q hsq ha) := by
    rw [range_tensorChart, IsAffineOpen.range_fromSpec]
    exact hxU
  -- the closed point `𝔪 = z ∩ B` of `Spec B`
  set p := PrimeSpectrum.comap (algebraMap Γ(Y, U) (K ⊗[k] Γ(Y, U))) z with hpdef
  have hp : hU.fromSpec p = bcFst ψ q (tensorChart q hsq ha z) := jB_comap_eq q hsq ha z
  have hpc : IsClosed ({p} : Set (Spec (CommRingCat.of Γ(Y, U)))) := by
    have : ({p} : Set (Spec (CommRingCat.of Γ(Y, U)))) = hU.fromSpec ⁻¹' {hU.fromSpec p} := by
      ext w
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ rfl, fun h => hU.fromSpec.isOpenEmbedding.injective h⟩
    rw [this, hp]
    exact hy.preimage hU.fromSpec.continuous
  have hmax : p.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hpc
  -- regularity at `z`
  have hz : z ∈ (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] Γ(Y, U))))).smoothLocus :=
    mem_smoothLocus_of_tensorChart q hsq ha z h
  have hzreg := (Geometry.RegularSmoothConverse.mem_smoothLocus_iff_isRegularLocalRing
    (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] Γ(Y, U))))) z).mp hz
  have : IsRegularLocalRing (Localization.AtPrime z.asIdeal) :=
    letI := Scheme.stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] Γ(Y, U))))) z
    IsRegularLocalRing.of_ringEquiv
      (Geometry.NodeCompletedLocalSpecLocalization.stalkEquiv K (K ⊗[k] Γ(Y, U)) z).toRingEquiv
  -- descent to `𝔪`
  have : IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
    isRegularLocalRing_of_tensor_left (k := k) (K := K) z.asIdeal p.asIdeal rfl hmax
  have hpreg : IsRegularLocalRing ((Spec (CommRingCat.of Γ(Y, U))).presheaf.stalk p) :=
    letI := Scheme.stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k Γ(Y, U)))) p
    IsRegularLocalRing.of_ringEquiv
      (Geometry.NodeCompletedLocalSpecLocalization.stalkEquiv k Γ(Y, U) p).toRingEquiv.symm
  have hps := (Geometry.RegularSmoothConverse.mem_smoothLocus_iff_isRegularLocalRing
    (Spec.map (CommRingCat.ofHom (algebraMap k Γ(Y, U)))) p).mpr hpreg
  have hps' : DeJong.IsSmoothAt (hU.fromSpec ≫ q) p := by
    rw [hsq, Category.comp_id]
    exact hps
  rw [← hp]
  exact Curves.isSmoothAt_of_isOpenImmersion_comp hU.fromSpec hps'

/-- **Smoothness descends at closed points along `K / k`**, for an arbitrary pullback square
`P → Y`, `P → Spec K` of `Y → Spec k` along `Spec K → Spec k`. -/
theorem isSmoothAt_of_isPullback {P : Scheme.{u}} {π : P ⟶ Y} {snd : P ⟶ Spec (CommRingCat.of K)}
    (H : IsPullback π snd q (Spec.map (CommRingCat.ofHom ψ))) (x : P)
    (hy : IsClosed ({π x} : Set Y)) (h : DeJong.IsSmoothAt snd x) : DeJong.IsSmoothAt q (π x) := by
  have hfst : π x = bcFst ψ q (H.isoPullback.hom x) := by
    change π x = (H.isoPullback.hom ≫ pullback.fst _ _) x
    rw [H.isoPullback_hom_fst]
  have h' : DeJong.IsSmoothAt (H.isoPullback.hom ≫ bcSnd ψ q) x := by
    rw [H.isoPullback_hom_snd]
    exact h
  rw [hfst] at hy ⊢
  exact isSmoothAt_of_isSmoothAt_bcSnd ψ q _ hy
    (Curves.isSmoothAt_of_isOpenImmersion_comp H.isoPullback.hom h')

end Smooth

end DeJongAlterations.StableModification.BlowDown.NumericalDescent
