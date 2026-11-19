import Hironaka.Resolution.HironakaChowPureTransformMatrix
import Hironaka.Analytic.CauchyBinet
import Mathlib.RingTheory.Localization.Ideal

/-!
# An original regular power in the internally constructed full minor ideal

Actual source generators, their GIVEN native principal-localization trivialization,
and literal cleared coordinate equations produce a power in the SAME full original
minor ideal. The endpoint constructs its matrix internally from the original finite
module. No regular minor, pivot, right inverse or ideal unit certificate is supplied.

The existing native TN CauchyBinet.det_mul_eq_sum_fun is reused directly.
No rectangular expansion, coefficient-change API or determinantal-ideal
definition is reintroduced.
Blueprint: `hironaka-g10-pure-transform-minor-density.tex`.
-/

set_option autoImplicit false

open Set Module
open scoped BigOperators

namespace Hironaka.HironakaChowPureTransformMinorDensity

noncomputable section

open HironakaChowDeterminantalImage HironakaChowPureTransformMatrix

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private theorem one_mem_map_minorIdeal_of_span {r q : ℕ} (d : R)
    (A : Matrix (Fin r) (Fin q) R)
    (hspan : Submodule.span (Localization.Away d)
      (range (A.map (algebraMap R (Localization.Away d))).col) = ⊤) :
    (1 : Localization.Away d) ∈ Ideal.map (algebraMap R (Localization.Away d)) (minorIdeal A r) := by
  classical
  let T := Localization.Away d
  let a := algebraMap R T
  let C := A.map a
  let J := Ideal.map a (minorIdeal A r)
  have hsurj : (Matrix.toLin' C).range = ⊤ := by
    rw [Matrix.range_toLin']
    exact hspan
  obtain ⟨s, hs⟩ := (Matrix.toLin' C).exists_rightInverse_of_surjective hsurj
  let B := LinearMap.toMatrix' s
  have hCB : C * B = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    exact hs
  have hminor (t : Fin r → Fin q) : (C.submatrix id t).det ∈ J := by
    have hmem : (A.submatrix id t).det ∈ minorIdeal A r :=
      Ideal.subset_span ⟨(id, t), rfl⟩
    have hm := Ideal.mem_map_of_mem a hmem
    rw [a.map_det] at hm
    exact hm
  have hsum : (C * B).det ∈ J := by
    rw [CauchyBinet.det_mul_eq_sum_fun]
    exact J.sum_mem fun t _ => J.mul_mem_right _ (hminor t)
  rw [hCB, Matrix.det_one] at hsum
  exact hsum

/-- The actual source generator coordinates, with the SAME native localized module,
internally force an original power into the SAME full original minor ideal. -/
theorem exists_pow_mem_minorIdeal_of_coordinates {r q : ℕ}
    (d : R) (g : Fin q → M) (hg : Submodule.span R (range g) = ⊤)
    (e : LocalizedModule (Submonoid.powers d) M ≃ₗ[Localization.Away d]
      (Fin r → Localization.Away d)) (N : ℕ) (A : Matrix (Fin r) (Fin q) R)
    (hA : ∀ i j, algebraMap R (Localization.Away d) (A i j) =
      d ^ N • e (LocalizedModule.mkLinearMap (Submonoid.powers d) M (g j)) i) :
    ∃ K : ℕ, d ^ K ∈ minorIdeal A r := by
  classical
  let T := Localization.Away d
  let a := algebraMap R T
  let l := LocalizedModule.mkLinearMap (Submonoid.powers d) M
  let C := A.map a
  have hlspan : Submodule.span T (l '' range g) = ⊤ :=
    span_eq_top_of_isLocalizedModule T (Submonoid.powers d) l hg
  have hespan : Submodule.span T (range fun j => e (l (g j))) = ⊤ := by
    have h := congrArg (Submodule.map e.toLinearMap) hlspan
    rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective] at h
    simpa only [T, LinearEquiv.coe_coe, image_image, ← range_comp, Function.comp_def] using h
  have hunit : IsUnit (a (d ^ N)) := IsLocalization.map_units (M := Submonoid.powers d) T ⟨d ^ N, N, rfl⟩
  have hcol (j : Fin q) : C.col j = a (d ^ N) • e (l (g j)) := by
    ext i
    change algebraMap R T (A i j) = a (d ^ N) * e (l (g j)) i
    simpa only [Algebra.smul_def] using hA i j
  have hsub : Submodule.span T (range fun j => e (l (g j))) ≤
      Submodule.span T (range C.col) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    apply (Submodule.smul_mem_iff_of_isUnit _ hunit).mp
    rw [← hcol]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hspan : Submodule.span T (range C.col) = ⊤ := by
    apply top_unique
    rw [← hespan]
    exact hsub
  have hone := one_mem_map_minorIdeal_of_span d A hspan
  have hmap : algebraMap R T (1 : R) ∈ Ideal.map (algebraMap R T) (minorIdeal A r) := by
    simpa only [map_one] using hone
  obtain ⟨_, ⟨K, rfl⟩, hK⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers d) T (minorIdeal A r) 1).mp hmap
  exact ⟨K, by simpa only [mul_one] using hK⟩

/-- Original finite-module data INTERNALLY produce the SAME quotient-image matrix,
whose actual full minor ideal contains an ORIGINAL regular denominator power. -/
theorem exists_pure_transform_matrix_with_regular_minor_power [Module.Finite R M]
    (d : R) (hd : IsRegular d) (r : ℕ)
    (e : LocalizedModule (Submonoid.powers d) M ≃ₗ[Localization.Away d]
      (Fin r → Localization.Away d)) :
    ∃ (N q : ℕ) (g : Fin q → M) (f : M →ₗ[R] (Fin r → R))
      (A : Matrix (Fin r) (Fin q) R)
      (E : (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) M))
        ≃ₗ[R] (Matrix.toLin' A).range) (K : ℕ),
      Submodule.span R (range g) = ⊤ ∧
      (∀ m i, algebraMap R (Localization.Away d) (f m i) =
        d ^ N • e (LocalizedModule.mkLinearMap (Submonoid.powers d) M m) i) ∧
      (∀ j, A.col j = f (g j)) ∧ f.range = (Matrix.toLin' A).range ∧
      LinearMap.ker f = LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) M) ∧
      (∀ m, (E (Submodule.Quotient.mk m)).val = f m) ∧
      (minorIdeal A r).FG ∧ d ^ K ∈ minorIdeal A r ∧ IsRegular (d ^ K) := by
  obtain ⟨N, q, g, f, A, E, hg, hclear, hcols, hrange, hker, hE⟩ :=
    exists_pure_transform_matrix d hd r e
  have hA (i : Fin r) (j : Fin q) : algebraMap R (Localization.Away d) (A i j) =
      d ^ N • e (LocalizedModule.mkLinearMap (Submonoid.powers d) M (g j)) i := by
    change algebraMap R (Localization.Away d) (A.col j i) = _
    rw [hcols]
    exact hclear (g j) i
  obtain ⟨K, hK⟩ := exists_pow_mem_minorIdeal_of_coordinates d g hg e N A hA
  have hfg : (minorIdeal A r).FG := Submodule.fg_span (finite_range _)
  exact ⟨N, q, g, f, A, E, K, hg, hclear, hcols, hrange, hker, hE, hfg, hK, hd.pow K⟩

open HironakaActualAnalyticSubspace

/-- The regular-power minor ideal is produced on the literal ORIGINAL singular
quotient stalk, keeping its original finite module, localization and native quotient. -/
theorem actual_stalk_exists_pure_transform_matrix_with_regular_minor_power
    {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (S : Set Y) (x : S) (F : Type*) [AddCommGroup F]
    [Module ((actualSubspaceSheaf (n := n) S).presheaf.stalk x).carrier F]
    [Module.Finite ((actualSubspaceSheaf (n := n) S).presheaf.stalk x).carrier F]
    (d : ((actualSubspaceSheaf (n := n) S).presheaf.stalk x).carrier)
    (hd : IsRegular d) (r : ℕ)
    (e : LocalizedModule (Submonoid.powers d) F ≃ₗ[Localization.Away d]
      (Fin r → Localization.Away d)) :
    ∃ (N q : ℕ) (g : Fin q → F)
      (f : F →ₗ[((actualSubspaceSheaf (n := n) S).presheaf.stalk x).carrier]
        (Fin r → ((actualSubspaceSheaf (n := n) S).presheaf.stalk x).carrier))
      (A : Matrix (Fin r) (Fin q)
        ((actualSubspaceSheaf (n := n) S).presheaf.stalk x).carrier)
      (E : (F ⧸ LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) F))
        ≃ₗ[((actualSubspaceSheaf (n := n) S).presheaf.stalk x).carrier]
          (Matrix.toLin' A).range) (K : ℕ),
      Submodule.span ((actualSubspaceSheaf (n := n) S).presheaf.stalk x).carrier
        (range g) = ⊤ ∧
      (∀ m i, algebraMap ((actualSubspaceSheaf (n := n) S).presheaf.stalk x).carrier
        (Localization.Away d) (f m i) =
          d ^ N • e (LocalizedModule.mkLinearMap (Submonoid.powers d) F m) i) ∧
      (∀ j, A.col j = f (g j)) ∧ f.range = (Matrix.toLin' A).range ∧
      LinearMap.ker f = LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) F) ∧
      (∀ m, (E (Submodule.Quotient.mk m)).val = f m) ∧
      (minorIdeal A r).FG ∧ d ^ K ∈ minorIdeal A r ∧ IsRegular (d ^ K) :=
  exists_pure_transform_matrix_with_regular_minor_power d hd r e

end

end Hironaka.HironakaChowPureTransformMinorDensity
