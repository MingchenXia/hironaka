/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaHolomorphicJetChartInvariance
import Mathlib.RingTheory.Finiteness.Basic

/-! # Entire original smooth coordinate-plane relative ideal powers

Genuine coordinate projection and inclusion internally construct an entire
holomorphic germ algebra retraction. Actual coordinate-plane Hadamard division
identifies its WHOLE trace kernel with the reduced normal-coordinate ideal.
Iterated real normal-word representatives with whole tangential holomorphic
germ coefficients prove finite base-ring modules for EVERY actual relative
normal-power quotient and for the quotient by any original ideal plus that
power. No kernel, power, finite-generation or frame certificate is an input.
Finite generation does not assert flatness/freeness or a normal-flat centre.
General higher-HS transformation/descent and G8 termination remain OPEN.
Blueprint: `hironaka-relative-normal-ideal-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalIdeal
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetChartInvariance
open Hironaka

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass

noncomputable section

/-- Actual first-coordinate projection of the original ambient model. -/
def tangentProjection (d t : ℕ) : ComplexModel (d+t) →L[ℂ] ComplexModel d :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin d => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin d => EuclideanSpace.proj (i.castAdd t))

/-- Actual original coordinate-plane inclusion. -/
def tangentInclusion (d t : ℕ) : ComplexModel d →L[ℂ] ComplexModel (d+t) :=
  ∑ i : Fin d, (EuclideanSpace.proj i).smulRight
    (EuclideanSpace.single (i.castAdd t) (1 : ℂ))

@[simp] theorem tangentProjection_apply (d t : ℕ) (z : ComplexModel (d+t)) (i : Fin d) :
    tangentProjection d t z i = z (i.castAdd t) := rfl

@[simp] theorem tangentInclusion_tangent (d t : ℕ) (z : ComplexModel d) (i : Fin d) :
    tangentInclusion d t z (i.castAdd t) = z i := by
  simp [tangentInclusion, sum_apply, ContinuousLinearMap.smulRight_apply,
    Pi.single_apply, Fin.castAdd_inj]

@[simp] theorem tangentInclusion_normal (d t : ℕ) (z : ComplexModel d) (i : Fin t) :
    tangentInclusion d t z (i.natAdd d) = 0 := by
  have hne : ∀ j : Fin d, i.natAdd d ≠ j.castAdd t := by
    intro j h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  simp [tangentInclusion, sum_apply, ContinuousLinearMap.smulRight_apply,
    hne]

/-- Actual projection/inclusion retraction, not a supplied splitting. -/
theorem tangentProjection_tangentInclusion (d t : ℕ) (z : ComplexModel d) :
    tangentProjection d t (tangentInclusion d t z) = z := by
  ext i
  simp

/-- The actual inclusion lands in the original smooth coordinate plane. -/
theorem tangentInclusion_mem_plane (d t : ℕ) (z : ComplexModel d) :
    tangentInclusion d t z ∈ complexCoordinatePlane (d+t) d := by
  intro i hi
  let j : Fin t := ⟨i.val-d, by omega⟩
  have he : i = j.natAdd d := Fin.ext (by dsimp [j]; omega)
  rw [he]
  exact tangentInclusion_normal d t z j

/-- Genuine plane points are precisely fixed by the actual ambient retraction. -/
theorem tangentInclusion_projection_eq_of_mem_plane (d t : ℕ)
    {z : ComplexModel (d+t)} (hz : z ∈ complexCoordinatePlane (d+t) d) :
    tangentInclusion d t (tangentProjection d t z) = z := by
  ext i
  by_cases hi : i.val < d
  · let j : Fin d := ⟨i.val, hi⟩
    have he : i = j.castAdd t := Fin.ext rfl
    rw [he]
    simp
  · let j : Fin t := ⟨i.val-d, by omega⟩
    have he : i = j.natAdd d := Fin.ext (by dsimp [j]; omega)
    rw [he, tangentInclusion_normal]
    exact (hz _ (by simp)).symm

/-- Entire tangential holomorphic germ pullback by the actual projection. -/
def tangentPullback (d t : ℕ) : HolGerm (ComplexModel d) →ₐ[ℂ] HolGerm (ComplexModel (d+t)) :=
  compAlgHom (tangentProjection d t)
    (Eventually.of_forall fun _ => (tangentProjection d t).differentiableAt) (map_zero _)

/-- Entire ambient germ trace to the original smooth plane. -/
def planeTrace (d t : ℕ) : HolGerm (ComplexModel (d+t)) →ₐ[ℂ] HolGerm (ComplexModel d) :=
  compAlgHom (tangentInclusion d t)
    (Eventually.of_forall fun _ => (tangentInclusion d t).differentiableAt) (map_zero _)

/-- The actual whole germ maps themselves form a retraction. -/
theorem planeTrace_tangentPullback (d t : ℕ) (g : HolGerm (ComplexModel d)) :
    planeTrace d t (tangentPullback d t g) = g := by
  induction g using HolGerm.induction_on with
  | h F hF =>
    unfold planeTrace tangentPullback
    rw [compAlgHom_mk, compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => congrArg F (tangentProjection_tangentInclusion d t z)

theorem planeTrace_surjective (d t : ℕ) : Function.Surjective (planeTrace d t) :=
  fun g => ⟨tangentPullback d t g, planeTrace_tangentPullback d t g⟩

theorem tangentPullback_injective (d t : ℕ) : Function.Injective (tangentPullback d t) := by
  intro g h he
  have hh := congrArg (planeTrace d t) he
  simpa only [planeTrace_tangentPullback] using hh

/-- The genuine relative algebra action uses whole tangential holomorphic germs. -/
@[instance_reducible] def tangentAlgebra (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  (tangentPullback d t).toRingHom.toAlgebra

/-- A genuine original normal coordinate, as an entire holomorphic germ. -/
def normalCoordinate (d t : ℕ) (i : Fin t) : HolGerm (ComplexModel (d+t)) :=
  coordinateGerm (i.natAdd d)

/-- The entire ideal generated by all actual original normal coordinates. -/
def normalIdeal (d t : ℕ) : Ideal (HolGerm (ComplexModel (d+t))) :=
  Ideal.span (range (normalCoordinate d t))

/-- Original normal coordinates have actual zero whole trace. -/
theorem planeTrace_normalCoordinate (d t : ℕ) (i : Fin t) :
    planeTrace d t (normalCoordinate d t i) = 0 := by
  unfold planeTrace normalCoordinate coordinateGerm
  rw [compAlgHom_mk, ← HolGerm.mk_zero]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => tangentInclusion_normal d t z i

/-- Actual relative Hadamard coefficients for every entire original germ. -/
theorem exists_relative_decomposition (d t : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    ∃ h : Fin t → HolGerm (ComplexModel (d+t)),
      g = tangentPullback d t (planeTrace d t g) + ∑ i : Fin t, normalCoordinate d t i * h i := by
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
  let η := (tangentInclusion d t).comp (tangentProjection d t)
  have hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)), DifferentiableAt ℂ η z :=
    Eventually.of_forall fun _ => η.differentiableAt
  have hη0 : η 0 = 0 := map_zero _
  let F := f - f ∘ η
  have hcomp := holomorphic_comp η hη hη0 hf
  have hF := eventually_differentiableAt_sub hf hcomp
  have hvan : ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)),
      z ∈ complexCoordinatePlane (d+t) d → F z = 0 := by
    filter_upwards [] with z hz
    have he := tangentInclusion_projection_eq_of_mem_plane d t hz
    simp only [F, Pi.sub_apply, Function.comp_apply, η, ContinuousLinearMap.comp_apply, he, sub_self]
  obtain ⟨H, hH0, hH, heq⟩ := CoordinatePlaneDivision.exists_eq_sum_coord_mul
    t d (by omega) (fun _ _ => rfl) hF hvan
  refine ⟨fun i => HolGerm.mk (H (i.natAdd d)) (hH _), ?_⟩
  have hsum := eventually_differentiableAt_sum Finset.univ fun i =>
    eventually_differentiableAt_mul
      (Eventually.of_forall fun _ => (EuclideanSpace.proj i : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt)
      (hH i)
  have he : HolGerm.mk F hF = ∑ i : Fin (d+t), coordinateGerm i * HolGerm.mk (H i) (hH i) := by
    calc
      HolGerm.mk F hF = HolGerm.mk (fun z => ∑ i : Fin (d+t), z i * H i z) hsum :=
        HolGerm.mk_eq_mk_iff.mpr heq
      _ = _ := by
        rw [HolGerm.mk_sum Finset.univ (fun i z => z i * H i z)
          (fun i => eventually_differentiableAt_mul
            (Eventually.of_forall fun _ => (EuclideanSpace.proj i : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt)
            (hH i))]
        exact Finset.sum_congr rfl fun i _ => HolGerm.mk_mul _ _ _ _
  rw [Fin.sum_univ_add] at he
  have hzero : ∑ i : Fin d, coordinateGerm (i.castAdd t) * HolGerm.mk (H (i.castAdd t)) (hH _) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hz := hH0 (i.castAdd t) i.isLt
    simp only [hz, HolGerm.mk_zero, mul_zero]
  rw [hzero, zero_add] at he
  have hbase : HolGerm.mk (f ∘ η) hcomp = tangentPullback d t (planeTrace d t (HolGerm.mk f hf)) := by
    unfold tangentPullback planeTrace
    rw [compAlgHom_mk, compAlgHom_mk]
    rfl
  have hsub : HolGerm.mk F hF = HolGerm.mk f hf - HolGerm.mk (f ∘ η) hcomp := rfl
  rw [hsub, hbase] at he
  dsimp only [normalCoordinate]
  rw [← he]
  ring

/-- The entire original normal ideal equals the actual whole trace kernel. -/
theorem normalIdeal_eq_ker_planeTrace (d t : ℕ) :
    normalIdeal d t = RingHom.ker (planeTrace d t).toRingHom := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨i, rfl⟩
    exact planeTrace_normalCoordinate d t i
  · intro g hg
    obtain ⟨h, he⟩ := exists_relative_decomposition d t g
    have hzero : planeTrace d t g = 0 := hg
    rw [hzero, map_zero, zero_add] at he
    rw [he]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)


/-- Exact geometric dictionary for ALL original representative germs on the actual plane. -/
theorem mk_mem_normalIdeal_iff (d t : ℕ) (F : ComplexModel (d+t) → ℂ)
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)), DifferentiableAt ℂ F z) :
    HolGerm.mk F hF ∈ normalIdeal d t ↔
      ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)), z ∈ complexCoordinatePlane (d+t) d → F z = 0 := by
  rw [normalIdeal_eq_ker_planeTrace]
  change planeTrace d t (HolGerm.mk F hF) = 0 ↔ _
  unfold planeTrace
  rw [compAlgHom_mk, ← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff]
  constructor
  · intro h
    have ht := (tangentProjection d t).continuous.tendsto (0 : ComplexModel (d+t))
    simp only [map_zero] at ht
    filter_upwards [ht.eventually h] with z hz hplane
    change F (tangentInclusion d t (tangentProjection d t z)) = 0 at hz
    rwa [tangentInclusion_projection_eq_of_mem_plane d t hplane] at hz
  · intro h
    have ht := (tangentInclusion d t).continuous.tendsto (0 : ComplexModel d)
    simp only [map_zero] at ht
    filter_upwards [ht.eventually h] with z hz
    exact hz (tangentInclusion_mem_plane d t z)

/-- The literal entire reduced plane quotient, internally induced by its true trace. -/
def planeQuotientAlgEquiv (d t : ℕ) :
    (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) ≃ₐ[ℂ] HolGerm (ComplexModel d) := by
  rw [normalIdeal_eq_ker_planeTrace]
  exact Ideal.quotientKerAlgEquivOfSurjective (planeTrace_surjective d t)

/-- The actual product of normal coordinates indexed by a finite original word. -/
def normalWord (d t : ℕ) {q : ℕ} (w : monomialIndex t q) : HolGerm (ComplexModel (d+t)) :=
  ∏ i : Fin w.1.val, normalCoordinate d t (w.2 i)

/-- True finite span with ENTIRE tangential holomorphic germ coefficients. -/
def normalWordSpan (d t q : ℕ) :
    let := tangentAlgebra d t
    Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  let := tangentAlgebra d t
  Submodule.span (HolGerm (ComplexModel d)) (range (normalWord d t (q := q)))

/-- The actual empty normal word generates the entire base term. -/
theorem one_mem_normalWordSpan (d t q : ℕ) :
    let := tangentAlgebra d t
    (1 : HolGerm (ComplexModel (d+t))) ∈ normalWordSpan d t (q+1) := by
  dsimp only
  let := tangentAlgebra d t
  apply Submodule.subset_span
  refine ⟨⟨⟨0, by omega⟩, Fin.elim0⟩, ?_⟩
  simp [normalWord]

/-- Prefixing a true original normal word raises the actual relative span by one. -/
theorem normalCoordinate_mul_mem_normalWordSpan (d t q : ℕ) (i : Fin t)
    {p : HolGerm (ComplexModel (d+t))} :
    let := tangentAlgebra d t
    p ∈ normalWordSpan d t q → normalCoordinate d t i * p ∈ normalWordSpan d t (q+1) := by
  dsimp only
  let := tangentAlgebra d t
  intro hp
  apply Submodule.span_induction (p := fun p _ => normalCoordinate d t i * p ∈ normalWordSpan d t (q+1))
    ?_ ?_ ?_ ?_ hp
  · rintro p ⟨⟨j, w⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨⟨j.val+1, by omega⟩, Fin.cons i w⟩, ?_⟩
    simp [normalWord, Fin.prod_univ_succ]
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro a p _ hp
    have he : normalCoordinate d t i * (a • p) = a • (normalCoordinate d t i * p) := by
      simp only [Algebra.smul_def]
      ring
    rw [he]
    exact Submodule.smul_mem _ _ hp

/-- Actual all-power relative representatives, with whole tangential coefficients. -/
theorem exists_normalWord_representative (d t q : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    ∃ p ∈ normalWordSpan d t q, g-p ∈ normalIdeal d t ^ q := by
  dsimp only
  let := tangentAlgebra d t
  induction q generalizing g with
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | succ q ih =>
    obtain ⟨h, hg⟩ := exists_relative_decomposition d t g
    choose p hp hrem using fun i => ih (h i)
    let P := tangentPullback d t (planeTrace d t g) + ∑ i : Fin t, normalCoordinate d t i * p i
    refine ⟨P, ?_, ?_⟩
    · apply Submodule.add_mem
      · have he : tangentPullback d t (planeTrace d t g) =
            (planeTrace d t g) • (1 : HolGerm (ComplexModel (d+t))) := by
          rw [Algebra.smul_def]
          change tangentPullback d t (planeTrace d t g) = tangentPullback d t (planeTrace d t g) * 1
          exact (mul_one _).symm
        rw [he]
        exact Submodule.smul_mem _ _ (one_mem_normalWordSpan d t q)
      · exact Submodule.sum_mem _ fun i _ => normalCoordinate_mul_mem_normalWordSpan d t q i (hp i)
    · have he : g-P = ∑ i : Fin t, normalCoordinate d t i * (h i-p i) := by
        rw [hg]
        dsimp only [P]
        rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => (mul_sub _ _ _).symm
      rw [he, pow_succ']
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (hrem i)

/-- The genuine relative normal-word span is finitely generated over the entire base germ ring. -/
theorem normalWordSpan_fg (d t q : ℕ) :
    let := tangentAlgebra d t
    (normalWordSpan d t q).FG := by
  dsimp only
  let := tangentAlgebra d t
  exact Submodule.fg_span (Set.finite_range _)

/-- The literal entire quotient by any original ideal plus a real normal power is a finite base module. -/
theorem finite_quotient_sup_normalIdeal_pow (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let := tangentAlgebra d t
    Module.Finite (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q)) := by
  dsimp only
  let := tangentAlgebra d t
  let J := I ⊔ normalIdeal d t ^ q
  let Q := (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) J).toLinearMap
  have he : (normalWordSpan d t q).map Q = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hp, hrem⟩ := exists_normalWord_representative d t q g
    apply Submodule.mem_map.mpr
    refine ⟨p, hp, ?_⟩
    change Ideal.Quotient.mk J p = Ideal.Quotient.mk J g
    exact (Ideal.Quotient.eq.mpr ((show normalIdeal d t ^ q ≤ J from le_sup_right) hrem)).symm
  apply Module.Finite.of_fg_top
  rw [← he]
  exact (normalWordSpan_fg d t q).map Q

/-- All actual relative normal-power quotients are finite whole tangential germ modules. -/
theorem finite_quotient_normalIdeal_pow (d t q : ℕ) :
    letI := tangentAlgebra d t
    Module.Finite (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t ^ q) := by
  let := tangentAlgebra d t
  let J := normalIdeal d t ^ q
  let Q := (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) J).toLinearMap
  have he : (normalWordSpan d t q).map Q = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hp, hrem⟩ := exists_normalWord_representative d t q g
    apply Submodule.mem_map.mpr
    refine ⟨p, hp, ?_⟩
    change Ideal.Quotient.mk J p = Ideal.Quotient.mk J g
    exact (Ideal.Quotient.eq.mpr hrem).symm
  apply Module.Finite.of_fg_top
  rw [← he]
  exact (normalWordSpan_fg d t q).map Q

end
end Hironaka.HironakaRelativeNormalIdeal
