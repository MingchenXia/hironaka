import Hironaka.Resolution.HironakaChowDeterminantalImage
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Integer
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The original localization-kernel quotient as an actual finite matrix image

Only finite generation, a regular original element, and an actual generic
trivialization of the ORIGINAL localized module are inputs. Common powers,
original module generators, the cleared map, its actual finite matrix, the
whole native kernel equality, and the original quotient dictionary are outputs.
No domain/field or desired pure-transform freeness is assumed.

Blueprint: `hironaka-g10-pure-transform-matrix.tex`.
-/

set_option autoImplicit false

open Set Module

namespace Hironaka.HironakaChowPureTransformMatrix

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private def coordinateLocalizationMap (d : R) (r : ℕ) :
    (Fin r → R) →ₗ[R] (Fin r → Localization.Away d) :=
  LinearMap.pi fun i => (Algebra.linearMap R (Localization.Away d)).comp (LinearMap.proj i)

private theorem localization_injective (d : R) (hd : IsRegular d) :
    Function.Injective (algebraMap R (Localization.Away d)) := by
  apply IsLocalization.injectiveₛ (M := Submonoid.powers d) (Localization.Away d)
  rintro _ ⟨n, rfl⟩
  exact hd.pow n

private theorem coordinateLocalizationMap_injective (d : R) (hd : IsRegular d) (r : ℕ) :
    Function.Injective (coordinateLocalizationMap d r) := by
  intro v w hvw
  ext i
  exact localization_injective d hd (congrFun hvw i)

/-- Native finite denominator clearing and range lifting internally construct one
linear map with a common original denominator power on the ENTIRE original module. -/
theorem exists_cleared_linearMap [Module.Finite R M]
    (d : R) (hd : IsRegular d) (r : ℕ)
    (h : M →ₗ[R] (Fin r → Localization.Away d)) :
    ∃ (N : ℕ) (f : M →ₗ[R] (Fin r → R)),
      ∀ m i, algebraMap R (Localization.Away d) (f m i) = d ^ N • h m i := by
  classical
  obtain ⟨q, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M)
  obtain ⟨⟨_, N, rfl⟩, hden⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers d) (fun p : Fin r × Fin q => h (g p.2) p.1)
  choose a ha using hden
  let J := coordinateLocalizationMap d r
  let H : M →ₗ[R] (Fin r → Localization.Away d) := d ^ N • h
  have hspan : Submodule.span R (range g) ≤ J.range.comap H := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨fun i => a (i, j), ?_⟩
    ext i
    exact ha (i, j)
  have hland (m : M) : H m ∈ J.range := by
    apply hspan
    rw [hg]
    trivial
  let f := H.codRestrictOfInjective J (coordinateLocalizationMap_injective d hd r) hland
  refine ⟨N, f, ?_⟩
  intro m i
  exact congrFun (LinearMap.codRestrictOfInjective_comp_apply H J
    (coordinateLocalizationMap_injective d hd r) hland m) i

/-- The ordinary original principal-open trivialization internally produces the
actual matrix and SAME localization-kernel quotient with its whole class dictionary. -/
theorem exists_pure_transform_matrix [Module.Finite R M]
    (d : R) (hd : IsRegular d) (r : ℕ)
    (e : LocalizedModule (Submonoid.powers d) M ≃ₗ[Localization.Away d]
      (Fin r → Localization.Away d)) :
    ∃ (N q : ℕ) (g : Fin q → M) (f : M →ₗ[R] (Fin r → R))
      (A : Matrix (Fin r) (Fin q) R)
      (E : (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) M))
        ≃ₗ[R] (Matrix.toLin' A).range),
      Submodule.span R (range g) = ⊤ ∧
      (∀ m i, algebraMap R (Localization.Away d) (f m i) =
        d ^ N • e (LocalizedModule.mkLinearMap (Submonoid.powers d) M m) i) ∧
      (∀ j, A.col j = f (g j)) ∧ f.range = (Matrix.toLin' A).range ∧
      LinearMap.ker f = LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) M) ∧
      ∀ m, (E (Submodule.Quotient.mk m)).val = f m := by
  classical
  let l := LocalizedModule.mkLinearMap (Submonoid.powers d) M
  let h : M →ₗ[R] (Fin r → Localization.Away d) :=
    (e.restrictScalars R).toLinearMap.comp l
  obtain ⟨N, f, hf⟩ := exists_cleared_linearMap d hd r h
  obtain ⟨q, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let A : Matrix (Fin r) (Fin q) R := fun i j => f (g j) i
  have hcols (j : Fin q) : A.col j = f (g j) := rfl
  have hrange : f.range = (Matrix.toLin' A).range := by
    rw [Matrix.range_toLin', ← Submodule.map_top f, ← hg, Submodule.map_span,
      ← range_comp]
    rfl
  have hker : LinearMap.ker f = LinearMap.ker l := by
    ext m
    simp only [LinearMap.mem_ker]
    constructor
    · intro hm
      have hpow : d ^ N • e (l m) = 0 := by
        ext i
        have hi := (hf m i).symm
        simpa only [h, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.restrictScalars_apply, hm, Pi.zero_apply, map_zero, Pi.smul_apply] using hi
      have he : (e.restrictScalars R) (d ^ N • l m) = (e.restrictScalars R) 0 := by
        rw [map_smul, map_zero]
        exact hpow
      exact LocalizedModule.eq_zero_of_smul_eq_zero (S := Submonoid.powers d) (d ^ N)
        ⟨N, rfl⟩ (l m) (e.injective he)
    · intro hm
      ext i
      apply localization_injective d hd
      simp only [hf m i, h, LinearMap.comp_apply, hm, map_zero, Pi.zero_apply, smul_zero]
  let E := (Submodule.quotEquivOfEq (LinearMap.ker l) (LinearMap.ker f) hker.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))
  refine ⟨N, q, g, f, A, E, hg, hf, hcols, hrange, hker, ?_⟩
  intro m
  rfl

private theorem higher_minor_zero {r q : ℕ} (A : Matrix (Fin r) (Fin q) R)
    (rows : Fin (r+1) → Fin r) (cols : Fin (r+1) → Fin q) :
    (A.submatrix rows cols).det = 0 := by
  classical
  have hn : ¬ Function.Injective rows := by
    intro hi
    have hcard := Fintype.card_le_of_injective rows hi
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hn
  apply Matrix.det_zero_of_row_eq hne
  ext k
  exact congrArg (fun a => A a (cols k)) hij

/-- The internally constructed SAME original matrix feeds the accepted full-minor
image theorem, yielding literal original-generator basis classes of the native quotient. -/
theorem exists_pure_transform_matrix_with_basis [Module.Finite R M] [IsLocalRing R]
    (d : R) (hd : IsRegular d) (r : ℕ)
    (e : LocalizedModule (Submonoid.powers d) M ≃ₗ[Localization.Away d]
      (Fin r → Localization.Away d)) :
    ∃ (N q : ℕ) (g : Fin q → M) (f : M →ₗ[R] (Fin r → R))
      (A : Matrix (Fin r) (Fin q) R)
      (E : (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) M))
        ≃ₗ[R] (Matrix.toLin' A).range),
      Submodule.span R (range g) = ⊤ ∧
      (∀ m i, algebraMap R (Localization.Away d) (f m i) =
        d ^ N • e (LocalizedModule.mkLinearMap (Submonoid.powers d) M m) i) ∧
      (∀ j, A.col j = f (g j)) ∧ f.range = (Matrix.toLin' A).range ∧
      LinearMap.ker f = LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) M) ∧
      (∀ m, (E (Submodule.Quotient.mk m)).val = f m) ∧
      (Module.Invertible R (HironakaChowDeterminantalImage.minorIdeal A r) →
        ∃ (cols : Fin r → Fin q)
          (b : Basis (Fin r) R
            (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) M))),
          ∀ i, b i = Submodule.Quotient.mk (g (cols i))) := by
  obtain ⟨N, q, g, f, A, E, hg, hclear, hcols, hrange, hker, hE⟩ :=
    exists_pure_transform_matrix d hd r e
  refine ⟨N, q, g, f, A, E, hg, hclear, hcols, hrange, hker, hE, ?_⟩
  intro hInv
  obtain ⟨cols, _Ec, _hEc, b, hb⟩ :=
    HironakaChowDeterminantalImage.exists_column_equiv A r hInv (higher_minor_zero A)
  let B := b.map E.symm
  refine ⟨cols, B, ?_⟩
  intro i
  apply E.injective
  change E (E.symm (b i)) = E (Submodule.Quotient.mk (g (cols i)))
  rw [E.apply_symm_apply]
  apply Subtype.ext
  rw [hb, hcols, hE]

open HironakaActualAnalyticSubspace

/-- The SAME source finite module and ORIGINAL localization-kernel quotient at a
literal singular quotient-sheaf stalk, with no domain/component replacement. -/
theorem actual_stalk_exists_pure_transform_matrix
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
          (Matrix.toLin' A).range),
      Submodule.span ((actualSubspaceSheaf (n := n) S).presheaf.stalk x).carrier
        (range g) = ⊤ ∧
      (∀ m i, algebraMap ((actualSubspaceSheaf (n := n) S).presheaf.stalk x).carrier
        (Localization.Away d) (f m i) =
          d ^ N • e (LocalizedModule.mkLinearMap (Submonoid.powers d) F m) i) ∧
      (∀ j, A.col j = f (g j)) ∧ f.range = (Matrix.toLin' A).range ∧
      LinearMap.ker f = LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) F) ∧
      ∀ m, (E (Submodule.Quotient.mk m)).val = f m :=
  exists_pure_transform_matrix d hd r e

end

end Hironaka.HironakaChowPureTransformMatrix
