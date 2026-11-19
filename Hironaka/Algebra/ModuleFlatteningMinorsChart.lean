import Hironaka.Algebra.ModuleFlatteningMinorsCoordinates
import Hironaka.Algebra.ModuleFlatteningMinorsPureTransform
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Actual free pure transforms on original maximal-minor blowup charts

Cramer expansion is transported through the actual generic basis and original
common coordinate denominator. The pure transform is the actual canonical
tensor image, and its basis consists of the selected original module images.
-/

noncomputable section

open Module TensorProduct
open scoped BigOperators TensorProduct

namespace Hironaka.Algebra.ModuleFlatteningMinorsChart

open ModuleFlatteningMinors ModuleFlatteningMinorsPureTransform

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R M : Type u} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

/-- The actual matrix Cramer identity is an identity of the original generic module generators. -/
theorem genericGenerator_eq_sum
    {n r : ℕ} (m : Fin n → M)
    (b : Basis (Fin r) (FractionRing R) (FractionRing R ⊗[R] M))
    (δ : R) (A : Matrix (Fin r) (Fin n) R) (hδ : δ ≠ 0)
    (hcoord : ∀ i j, algebraMap R (FractionRing R) (A i j) =
      algebraMap R (FractionRing R) δ * b.repr ((1 : FractionRing R) ⊗ₜ[R] m j) i)
    (s : Fin r → Fin n) (hs : columnMinor A s ≠ 0) (a : Fin n) :
    (1 : FractionRing R) ⊗ₜ[R] m a = ∑ j,
      chartCoefficient A s a j • ((1 : FractionRing R) ⊗ₜ[R] m (s j)) := by
  have hsmul (j : Fin r) :
      chartCoefficient A s a j • ((1 : FractionRing R) ⊗ₜ[R] m (s j)) =
      (chartCoefficient A s a j : FractionRing R) • ((1 : FractionRing R) ⊗ₜ[R] m (s j)) :=
    (IsScalarTower.algebraMap_smul (FractionRing R) _ _).symm
  simp_rw [hsmul]
  apply b.repr.injective
  ext i
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  have hc := column_eq_sum_chartCoefficient A s hs a i
  simp_rw [hcoord] at hc
  have hδK : algebraMap R (FractionRing R) δ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hδ
  apply mul_left_cancel₀ hδK
  rw [Finset.mul_sum]
  exact hc.trans (Finset.sum_congr rfl fun j _ ↦ by ring)

/-- The actual original canonical image equals the span of the original selected generators. -/
theorem pureTransform_eq_span_selected
    {n r : ℕ} (m : Fin n → M) (hm : Submodule.span R (Set.range m) = ⊤)
    (b : Basis (Fin r) (FractionRing R) (FractionRing R ⊗[R] M))
    (δ : R) (A : Matrix (Fin r) (Fin n) R) (hδ : δ ≠ 0)
    (hcoord : ∀ i j, algebraMap R (FractionRing R) (A i j) =
      algebraMap R (FractionRing R) δ * b.repr ((1 : FractionRing R) ⊗ₜ[R] m j) i)
    (s : Fin r → Fin n) (hs : columnMinor A s ≠ 0) :
    pureTransform R M (affineBlowupFractionChart (minorIdeal A) (columnMinor A s)) =
      Submodule.span (affineBlowupFractionChart (minorIdeal A) (columnMinor A s))
        (Set.range fun j ↦ (1 : FractionRing R) ⊗ₜ[R] m (s j)) := by
  rw [pureTransform_eq_span R M _ m hm]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, rfl⟩
    change ((1 : FractionRing R) ⊗ₜ[R] m a) ∈ _
    rw [genericGenerator_eq_sum m b δ A hδ hcoord s hs a]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · apply Submodule.span_mono
    rintro x ⟨j, rfl⟩
    exact ⟨s j, rfl⟩

/-- The original selected generic generators are independent over the actual chart. -/
theorem selected_generic_linearIndependent
    {n r : ℕ} (m : Fin n → M) (hm : Submodule.span R (Set.range m) = ⊤)
    (b : Basis (Fin r) (FractionRing R) (FractionRing R ⊗[R] M))
    (δ : R) (A : Matrix (Fin r) (Fin n) R) (hδ : δ ≠ 0)
    (hcoord : ∀ i j, algebraMap R (FractionRing R) (A i j) =
      algebraMap R (FractionRing R) δ * b.repr ((1 : FractionRing R) ⊗ₜ[R] m j) i)
    (s : Fin r → Fin n) (hs : columnMinor A s ≠ 0) :
    LinearIndependent (affineBlowupFractionChart (minorIdeal A) (columnMinor A s))
      (fun j ↦ (1 : FractionRing R) ⊗ₜ[R] m (s j)) := by
  let K := FractionRing R
  let S := affineBlowupFractionChart (minorIdeal A) (columnMinor A s)
  have hall : Submodule.span K (Set.range fun j ↦ (1 : K) ⊗ₜ[R] m j) = ⊤ := by
    have h := congrArg (fun p : Submodule R M ↦ p.baseChange K) hm
    simpa only [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp,
      Function.comp_def, TensorProduct.mk_apply] using h
  have hspan : ⊤ ≤ Submodule.span K (Set.range fun j ↦ (1 : K) ⊗ₜ[R] m (s j)) := by
    rw [← hall]
    apply Submodule.span_le.mpr
    rintro x ⟨a, rfl⟩
    change ((1 : FractionRing R) ⊗ₜ[R] m a) ∈ _
    rw [genericGenerator_eq_sum m b δ A hδ hcoord s hs a]
    apply Submodule.sum_mem
    intro j _
    rw [← IsScalarTower.algebraMap_smul K]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hcard : Fintype.card (Fin r) = Module.finrank K (K ⊗[R] M) :=
    (Module.finrank_eq_card_basis b).symm
  have hK : LinearIndependent K (fun j ↦ (1 : K) ⊗ₜ[R] m (s j)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard
  apply hK.restrict_scalars
  intro x y hxy
  exact (IsFractionRing.injective S K) (by
    simpa only [Algebra.smul_def, mul_one] using hxy)

/-- The actual canonical pure transform on a nonzero original minor chart has a native
basis consisting literally of the selected original module-generator images. -/
theorem exists_basis_pureTransform_minorChart
    {n r : ℕ} (m : Fin n → M) (hm : Submodule.span R (Set.range m) = ⊤)
    (b : Basis (Fin r) (FractionRing R) (FractionRing R ⊗[R] M))
    (δ : R) (A : Matrix (Fin r) (Fin n) R) (hδ : δ ≠ 0)
    (hcoord : ∀ i j, algebraMap R (FractionRing R) (A i j) =
      algebraMap R (FractionRing R) δ * b.repr ((1 : FractionRing R) ⊗ₜ[R] m j) i)
    (s : Fin r → Fin n) (hs : columnMinor A s ≠ 0) :
    ∃ B : Basis (Fin r) (affineBlowupFractionChart (minorIdeal A) (columnMinor A s))
      (pureTransform R M (affineBlowupFractionChart (minorIdeal A) (columnMinor A s))),
      ∀ j, (B j : FractionRing R ⊗[R] M) = (1 : FractionRing R) ⊗ₜ[R] m (s j) := by
  let hli := selected_generic_linearIndependent m hm b δ A hδ hcoord s hs
  let hEq := (pureTransform_eq_span_selected m hm b δ A hδ hcoord s hs).symm
  let B := (Basis.span hli).map (LinearEquiv.ofEq _ _ hEq)
  refine ⟨B, fun j ↦ ?_⟩
  simp [B, Basis.map_apply]

end Hironaka.Algebra.ModuleFlatteningMinorsChart
