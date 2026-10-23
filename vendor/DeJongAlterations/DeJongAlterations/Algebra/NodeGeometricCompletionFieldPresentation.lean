import DeJongAlterations.Algebra.NodeFlatPresentationEvaluation
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Actual coefficient-preserving complete field-series presentations.
Only the original coefficient residue surjectivity and actual maximal-ideal
generators are input; no hypersurface or geometric-node classification is assumed. -/

noncomputable section

open IsLocalRing MvPowerSeries

namespace DeJongAlterations.Algebra.NodeGeometricCompletionFieldPresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable (K : Type u) [CommRing K] (B : Type v) [CommRing B] [IsLocalRing B]
  [Algebra K B] [IsAdicComplete (maximalIdeal B) B] {σ : Type w} [Finite σ]
  (b : σ → B) (hb : Ideal.span (Set.range b) = maximalIdeal B)

omit [IsAdicComplete (maximalIdeal B) B] [Finite σ] in
include hb in
/-- Every specified actual generator belongs to the original maximal ideal. -/
theorem generator_mem (i : σ) : b i ∈ maximalIdeal B := by
  rw [← hb]
  exact Ideal.subset_span (Set.mem_range_self i)

/-- Actual native complete evaluation, retaining exactly the original coefficient map. -/
def evaluation : MvPowerSeries σ K →ₐ[K] B :=
  NodeFlatPresentation.evaluation (maximalIdeal B) b (generator_mem B b hb)

/-- Every original coefficient retains its literal original image. -/
theorem evaluation_C (a : K) : evaluation K B b hb (C a) = algebraMap K B a :=
  NodeFlatPresentation.evaluation_C _ _ _ a

/-- Every variable has exactly its specified original generator image. -/
theorem evaluation_X (i : σ) : evaluation K B b hb (X i) = b i :=
  NodeFlatPresentation.evaluation_X _ _ _ i

/-- The WHOLE actual variable ideal maps exactly to the original maximal ideal. -/
theorem variableIdeal_image :
    (Ideal.span (Set.range (fun i : σ => (X i : MvPowerSeries σ K)))).map
      (evaluation K B b hb).toRingHom = maximalIdeal B := by
  rw [Ideal.map_span, ← Set.range_comp]
  have h : (evaluation K B b hb).toRingHom ∘
      (fun i : σ => (X i : MvPowerSeries σ K)) = b := by
    funext i
    exact evaluation_X K B b hb i
  rw [h, hb]

/-- Every actual variable-ideal power has exactly the original maximal-ideal-power image. -/
theorem variableIdeal_pow_image (n : ℕ) :
    ((Ideal.span (Set.range (fun i : σ => (X i : MvPowerSeries σ K)))) ^ n).map
      (evaluation K B b hb).toRingHom = maximalIdeal B ^ n := by
  rw [Ideal.map_pow, variableIdeal_image]

/-- Native complete-source surjectivity produces a genuine series presentation from
actual generators and coefficient residue surjectivity, without any model premise. -/
theorem evaluation_surjective
    (hres : Function.Surjective ((residue B).comp (algebraMap K B))) :
    Function.Surjective (evaluation K B b hb) := by
  let V : Ideal (MvPowerSeries σ K) := Ideal.span (Set.range X)
  let : IsPrecomplete V (MvPowerSeries σ K) := inferInstance
  have hv : V.map (evaluation K B b hb).toRingHom = maximalIdeal B :=
    variableIdeal_image K B b hb
  let : IsHausdorff (V.map (evaluation K B b hb).toRingHom) B := by
    rw [hv]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (I := V) (evaluation K B b hb).toRingHom
  rw [hv]
  intro y
  obtain ⟨a, ha⟩ := hres y
  refine ⟨C a, ?_⟩
  change residue B (evaluation K B b hb (C a)) = y
  rw [evaluation_C]
  exact ha

/-- The actual kernel quotient presents this SAME original target over its actual K-map. -/
def quotientEquiv (hres : Function.Surjective ((residue B).comp (algebraMap K B))) :
    (MvPowerSeries σ K ⧸ RingHom.ker (evaluation K B b hb).toRingHom) ≃ₐ[K] B :=
  Ideal.quotientKerAlgEquivOfSurjective (evaluation_surjective K B b hb hres)

/-- EVERY series representative retains its canonical actual evaluation image. -/
theorem quotientEquiv_mk (hres : Function.Surjective ((residue B).comp (algebraMap K B)))
    (g : MvPowerSeries σ K) :
    quotientEquiv K B b hb hres (Ideal.Quotient.mk _ g) = evaluation K B b hb g :=
  Ideal.quotientKerAlgEquivOfSurjective_mk _ g

/-- The quotient presentation retains EVERY original coefficient. -/
theorem quotientEquiv_C (hres : Function.Surjective ((residue B).comp (algebraMap K B)))
    (a : K) :
    quotientEquiv K B b hb hres (Ideal.Quotient.mk _ (C a)) = algebraMap K B a := by
  rw [quotientEquiv_mk, evaluation_C]

/-- The quotient presentation retains EVERY specified actual coordinate. -/
theorem quotientEquiv_X (hres : Function.Surjective ((residue B).comp (algebraMap K B)))
    (i : σ) :
    quotientEquiv K B b hb hres (Ideal.Quotient.mk _ (X i)) = b i := by
  rw [quotientEquiv_mk, evaluation_X]

end DeJongAlterations.Algebra.NodeGeometricCompletionFieldPresentation
