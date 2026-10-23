/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Omega.PoleChart
import DeJongAlterations.Geometry.RegularSmoothConverse
import DeJongAlterations.Geometry.CurveBoundaryBasic
import DeJongAlterations.Algebra.RegularSmoothConverseResidue

/-!
# A normal curve over an algebraically closed field is smooth of relative dimension one

Let `Y` be an integral normal scheme of dimension at most one, locally of finite type over an
algebraically closed field `k`, and not a point. Then `Y → Spec k` is smooth of relative
dimension one (`smoothOfRelativeDimension_one`): `Y` is regular (a normal Noetherian local
domain of dimension `≤ 1` is regular), hence smooth over the perfect field `k`; on a standard
smooth chart `A = Γ(V, 𝒪_Y)` the module `Ω_{A/k}` is free, and its rank is computed at a closed
point `y ∈ V`: `κ(y) ⊗ Ω_{𝒪_{Y,y}/k}` has dimension `dim 𝒪_{Y,y} + dim Ω_{κ(y)/k} = 1 + 0`.

This is the smoothness hypothesis of the degree formula for `ν^* ω` on the normalization of a
component (blueprint `sm-omega-component-degree.tex`, `lem:sm-omega-cd-normalization`;
Temkin, `semi-stable.tex`, App. B, l. 4384–4433: the normalization `C̃_η` of a curve over
`k = k̄` is a smooth curve).
-/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

noncomputable section

namespace DeJongAlterations.StableModification.Omega.ComponentNormalization

section Residue

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type u} [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A] (m : Ideal A) [m.IsMaximal] (S : Type u) [CommRing S] [Algebra A S]
  [IsLocalization.AtPrime S m] [IsLocalRing S] [Algebra k S] [IsScalarTower k A S]

include m in
/-- **The residue field at a closed point is `k`**: for `A` of finite type over `k = k̄`, `m`
maximal and `S = A_m`, the map `k → S/𝔪_S` is surjective. -/
theorem surjective_algebraMap_residueField :
    Function.Surjective (algebraMap k (ResidueField S)) := by
  have hq := (PoleChart.bijective_algebraMap_quotient (K := k) m).2
  have hc : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ m := fun a => by
    obtain ⟨c, hc⟩ := hq (Ideal.Quotient.mk m a)
    refine ⟨c, ?_⟩
    rw [← Ideal.Quotient.eq, ← hc]
    rfl
  have hres : ∀ a : A, ∃ c : k, residue S (algebraMap A S a) = algebraMap k (ResidueField S) c :=
    fun a => by
      obtain ⟨c, hc⟩ := hc a
      refine ⟨c, ?_⟩
      rw [IsScalarTower.algebraMap_apply k S (ResidueField S), IsScalarTower.algebraMap_apply k A S,
        ResidueField.algebraMap_eq, ← sub_eq_zero, ← map_sub, ← map_sub, residue_eq_zero_iff,
        IsLocalization.AtPrime.to_map_mem_maximal_iff S m]
      exact hc
  intro z
  obtain ⟨s, rfl⟩ := residue_surjective z
  obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl s
  obtain ⟨ca, hca⟩ := hres a
  obtain ⟨ct, hct⟩ := hres t
  have ht : residue S (algebraMap A S t) ≠ 0 := by
    rw [Ne, residue_eq_zero_iff, IsLocalization.AtPrime.to_map_mem_maximal_iff S m]
    exact t.2
  have hct0 : ct ≠ 0 := by
    rintro rfl
    rw [map_zero] at hct
    exact ht hct
  refine ⟨ca * ct⁻¹, ?_⟩
  apply mul_right_cancel₀ ht
  rw [← map_mul, IsLocalization.mk'_spec, hca, hct, ← map_mul, inv_mul_cancel_right₀ hct0]

end Residue

section Smooth

variable {Y : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]

set_option backward.isDefEq.respectTransparency false in
/-- **A normal curve over `k = k̄` is smooth of relative dimension one.** Let `Y` be integral,
normal, of dimension at most one, locally of finite type over `k`, and not a point. Then
`Y → Spec k` is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_one (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType q] [IsIntegral Y]
    (hnormal : IsNormalScheme Y) (hdim : topologicalKrullDim Y ≤ 1)
    (hpt : ∃ y : Y, y ≠ genericPoint Y) : SmoothOfRelativeDimension 1 q := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have hreg := isRegularScheme_of_isNormalScheme_of_topologicalKrullDim_le_one Y hnormal hdim
  have hsm : Smooth q := Geometry.RegularSmoothConverse.smooth_of_isRegularScheme q hreg
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace q
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := (Smooth.iff_forall_exists_isStandardSmooth q).mp hsm x
  refine ⟨U, hU, V, hV, hxV, e, ?_⟩
  -- `U = ⊤`
  have hUtop : U = ⊤ := by
    refine top_unique fun z _ => ?_
    have hz : z = q x := Subsingleton.elim _ _
    rw [hz]
    exact e hxV
  subst hUtop
  -- a closed point of `V` other than the generic point
  obtain ⟨y, hyV, hyc⟩ : ∃ y ∈ V, IsClosed ({y} : Set Y) :=
    nonempty_inter_closedPoints ⟨x, hxV⟩ V.isOpen.isLocallyClosed
  have hyg : y ≠ genericPoint Y := by
    intro hyg
    obtain ⟨z, hz⟩ := hpt
    have h1 : z ∈ closure ({genericPoint Y} : Set Y) := by
      rw [genericPoint_closure]; trivial
    rw [← hyg, hyc.closure_eq, Set.mem_singleton_iff] at h1
    exact hz (h1.trans hyg)
  -- the algebras
  let : Algebra Γ(Spec (.of k), ⊤) Γ(Y, V) := (q.appLE ⊤ V e).hom.toAlgebra
  have : Algebra.IsStandardSmooth Γ(Spec (.of k), ⊤) Γ(Y, V) := hstd
  let : Algebra k Γ(Spec (.of k), ⊤) := (Scheme.ΓSpecIso (.of k)).inv.hom.toAlgebra
  let : Algebra k Γ(Y, V) :=
    ((algebraMap Γ(Spec (.of k), ⊤) Γ(Y, V)).comp (algebraMap k Γ(Spec (.of k), ⊤))).toAlgebra
  have : IsScalarTower k Γ(Spec (.of k), ⊤) Γ(Y, V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hsurj : Function.Surjective (algebraMap k Γ(Spec (.of k), ⊤)) :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2
  let eΩ : Ω[Γ(Y, V)⁄k] ≃ₗ[Γ(Y, V)] Ω[Γ(Y, V)⁄Γ(Spec (.of k), ⊤)] :=
    LinearEquiv.ofBijective (KaehlerDifferential.map k Γ(Spec (.of k), ⊤) Γ(Y, V) Γ(Y, V))
      (PoleChart.bijective_map_of_surjective hsurj)
  have : Module.Free Γ(Y, V) Ω[Γ(Y, V)⁄k] := Module.Free.of_equiv eΩ.symm
  have : Module.Finite Γ(Y, V) Ω[Γ(Y, V)⁄k] := Module.Finite.equiv eΩ.symm
  have : Algebra.FiniteType k Γ(Spec (.of k), ⊤) :=
    Algebra.FiniteType.of_surjective (Algebra.ofId k _) hsurj
  have : Algebra.FiniteType k Γ(Y, V) := Algebra.FiniteType.trans (S := Γ(Spec (.of k), ⊤))
    inferInstance inferInstance
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : IsDomain Γ(Y, V) := IsIntegral.component_integral V
  -- the local ring at `y`
  let m := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
  have : m.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed ⟨y, hyV⟩ hyc
  let := Y.presheaf.algebra_section_stalk (⟨y, hyV⟩ : V)
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) m := hV.isLocalization_stalk ⟨y, hyV⟩
  let : Algebra k (Y.presheaf.stalk y) :=
    ((algebraMap Γ(Y, V) (Y.presheaf.stalk y)).comp (algebraMap k Γ(Y, V))).toAlgebra
  have : IsScalarTower k Γ(Y, V) (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FormallyEtale Γ(Y, V) (Y.presheaf.stalk y) :=
    Algebra.FormallyEtale.of_isLocalization m.primeCompl
  have : Algebra.EssFiniteType Γ(Y, V) (Y.presheaf.stalk y) :=
    Algebra.EssFiniteType.of_isLocalization _ m.primeCompl
  have : Algebra.EssFiniteType k (Y.presheaf.stalk y) :=
    Algebra.EssFiniteType.comp k Γ(Y, V) (Y.presheaf.stalk y)
  have : IsRegularLocalRing (Y.presheaf.stalk y) := hreg y
  let eS := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k Γ(Y, V) (Y.presheaf.stalk y)
  have : Module.Free (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k] := Module.Free.of_equiv eS
  have hrank : Module.finrank (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k] =
      Module.finrank Γ(Y, V) Ω[Γ(Y, V)⁄k] :=
    (LinearEquiv.finrank_eq eS).symm.trans Module.finrank_baseChange
  have hres : Module.finrank (ResidueField (Y.presheaf.stalk y))
      (TensorProduct (Y.presheaf.stalk y) (ResidueField (Y.presheaf.stalk y))
        Ω[Y.presheaf.stalk y⁄k]) = Module.finrank Γ(Y, V) Ω[Γ(Y, V)⁄k] :=
    Module.finrank_baseChange.trans hrank
  -- the residue field is `k`, so `Ω_{κ/k} = 0`
  have hκ : Function.Surjective (algebraMap k (ResidueField (Y.presheaf.stalk y))) :=
    surjective_algebraMap_residueField (k := k) m (Y.presheaf.stalk y)
  have : Algebra.FormallyUnramified k (ResidueField (Y.presheaf.stalk y)) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId k _) hκ
  have hzero : Module.finrank (ResidueField (Y.presheaf.stalk y))
      Ω[ResidueField (Y.presheaf.stalk y)⁄k] = 0 := Module.finrank_zero_of_subsingleton
  have key := Algebra.RegularSmoothConverseResidue.finrank_residueTensorKaehler_eq_of_isRegularLocalRing
    k (Y.presheaf.stalk y)
  rw [hres, hzero, Geometry.CurveBoundary.ringKrullDim_stalk_eq_one hdim y hyg] at key
  have h1 : Module.finrank Γ(Y, V) Ω[Γ(Y, V)⁄k] = 1 := by
    have : ((Module.finrank Γ(Y, V) Ω[Γ(Y, V)⁄k] : ℕ) : WithBot ℕ∞) = ((1 : ℕ) : WithBot ℕ∞) := by
      rw [key]; rfl
    exact_mod_cast this
  -- conclusion
  change Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Spec (.of k), ⊤) Γ(Y, V)
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth 1,
    ← LinearEquiv.rank_eq eΩ, ← Module.finrank_eq_rank, h1]

end Smooth

end DeJongAlterations.StableModification.Omega.ComponentNormalization
