import DeJongAlterations.Geometry.ProperSteinProjectiveCechGradedPresentation
import Mathlib.LinearAlgebra.Pi

/-! # Finite shifted free graded presentations

A finite family of actual homogeneous module generators is presented by the
actual finite free coefficient module. Its internal decomposition is derived
from the actual ring decomposition, and its syzygies are actual homogeneous
kernels.
-/

/-!
Adapted from the same workspace `BingWangEntropy/FiniteShiftedGradedPresentation.lean`,
SHA256 9e9427dd244ca605651ef7722b31965dcc637e719ae448856346b80e66054cc9.
Only native Mathlib and owned DeJongAlterations modules are imported.
-/

universe u

open DirectSum

namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section ShiftedFree

variable {K R I : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [Fintype I] [DecidableEq I]
  (𝒜 : ℤ → Submodule K R) [GradedRing 𝒜] (δ : I → ℤ)

/-- The literal degree piece of a finite shifted free coefficient module. -/
def finiteShiftedFreePiece (d : ℤ) : Submodule K (I → R) where
  carrier := {a | ∀ i, a i ∈ 𝒜 (d - δ i)}
  zero_mem' _i := (𝒜 _).zero_mem
  add_mem' ha hb i := (𝒜 _).add_mem (ha i) (hb i)
  smul_mem' c _a ha i := (𝒜 _).smul_mem c (ha i)

/-- The literal finite shifted free grading is compatible with true homogeneous multiplication. -/
instance finiteShiftedFreeGradedSMul :
    SetLike.GradedSMul 𝒜 (finiteShiftedFreePiece 𝒜 δ) where
  smul_mem := by
    intro d e r a hr ha i
    change r * a i ∈ 𝒜 ((d +ᵥ e) - δ i)
    convert SetLike.mul_mem_graded hr (ha i) using 1
    congr 1
    simp only [vadd_eq_add]
    omega

/-- Insert an actual ring component as one actual free coefficient. -/
def finiteShiftedFreeInsert (i : I) (j : ℤ) :
    𝒜 j →ₗ[K] finiteShiftedFreePiece 𝒜 δ (j + δ i) :=
  ((LinearMap.single K (fun _ : I => R) i).comp (𝒜 j).subtype).codRestrict _ (by
    intro r t
    by_cases h : t = i
    · subst t
      simp [r.property]
    · simpa only [LinearMap.comp_apply, LinearMap.single_apply, Pi.single_eq_of_ne h] using
        (𝒜 (j + δ i - δ t)).zero_mem)

/-- The actual homogeneous decomposition of one actual coefficient in its shifted position. -/
def finiteShiftedFreeCoefficientDecompose (i : I) :
    R →ₗ[K] ⨁ d, finiteShiftedFreePiece 𝒜 δ d :=
  (DirectSum.toModule K ℤ (⨁ d, finiteShiftedFreePiece 𝒜 δ d)
    (fun j => (DirectSum.lof K ℤ (fun d => finiteShiftedFreePiece 𝒜 δ d)
      (j + δ i)).comp (finiteShiftedFreeInsert 𝒜 δ i j))).comp
      (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

omit [Fintype I] in
/-- Recombining a coefficient's actual homogeneous pieces restores its literal position. -/
theorem finiteShiftedFreeCoefficientDecompose_recompose (i : I) :
    (DirectSum.coeLinearMap (finiteShiftedFreePiece 𝒜 δ)).comp
      (finiteShiftedFreeCoefficientDecompose 𝒜 δ i) =
        LinearMap.single K (fun _ : I => R) i := by
  apply DirectSum.decompose_lhom_ext 𝒜
  intro j
  ext r t
  change (DirectSum.coeLinearMap (finiteShiftedFreePiece 𝒜 δ))
    ((DirectSum.toModule K ℤ (⨁ d, finiteShiftedFreePiece 𝒜 δ d) _)
      ((DirectSum.decomposeLinearEquiv 𝒜) (r : R))) t = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof,
    LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
  rfl

/-- The true decomposition map of the actual finite shifted coefficient module. -/
def finiteShiftedFreeDecomposeMap :
    (I → R) →ₗ[K] ⨁ d, finiteShiftedFreePiece 𝒜 δ d :=
  ∑ i : I, (finiteShiftedFreeCoefficientDecompose 𝒜 δ i).comp
    (LinearMap.proj i)

omit [Fintype I] [GradedRing 𝒜] in
/-- Equal literal degrees identify the true homogeneous coefficient insertions. -/
theorem finiteShiftedFreeInsert_degree_congr (i : I) (j d : ℤ) (h : j + δ i = d)
    (r : 𝒜 j) (a : finiteShiftedFreePiece 𝒜 δ d)
    (ha : a.val = Pi.single i (r : R)) :
    DirectSum.lof K ℤ (fun d => finiteShiftedFreePiece 𝒜 δ d) (j + δ i)
      (finiteShiftedFreeInsert 𝒜 δ i j r) =
        DirectSum.lof K ℤ (fun d => finiteShiftedFreePiece 𝒜 δ d) d a := by
  subst d
  congr 1
  apply Subtype.ext
  exact ha.symm

/-- Recombining all true homogeneous free components restores the original coefficient vector. -/
theorem finiteShiftedFreeDecomposeMap_recompose :
    (DirectSum.coeLinearMap (finiteShiftedFreePiece 𝒜 δ)).comp
      (finiteShiftedFreeDecomposeMap 𝒜 δ) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  funext i
  simp only [finiteShiftedFreeDecomposeMap, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.proj_apply]
  change (DirectSum.coeLinearMap (finiteShiftedFreePiece 𝒜 δ))
    (∑ t : I, finiteShiftedFreeCoefficientDecompose 𝒜 δ t (a t)) i = a i
  rw [map_sum]
  simp_rw [← LinearMap.comp_apply,
    finiteShiftedFreeCoefficientDecompose_recompose, LinearMap.single_apply]
  exact congrFun (Finset.univ_sum_single a) i

/-- A true homogeneous coefficient vector decomposes in its literal shifted degree. -/
theorem finiteShiftedFreeDecomposeMap_homogeneous (d : ℤ)
    (a : finiteShiftedFreePiece 𝒜 δ d) :
    finiteShiftedFreeDecomposeMap 𝒜 δ (a : I → R) =
      DirectSum.lof K ℤ (fun d => finiteShiftedFreePiece 𝒜 δ d) d a := by
  have h (i : I) :
      finiteShiftedFreeCoefficientDecompose 𝒜 δ i (a.val i) =
        DirectSum.lof K ℤ (fun d => finiteShiftedFreePiece 𝒜 δ d) d
          ⟨Pi.single i (a.val i), by
            intro t
            by_cases ht : t = i
            · subst t
              simpa using a.property i
            · simpa only [Pi.single_eq_of_ne ht] using (𝒜 (d - δ t)).zero_mem⟩ := by
    unfold finiteShiftedFreeCoefficientDecompose
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem 𝒜 (a.property i)]
    change (DirectSum.toModule K ℤ (⨁ d, finiteShiftedFreePiece 𝒜 δ d) _)
      (DirectSum.lof K ℤ (fun j => 𝒜 j) (d - δ i) ⟨a.val i, a.property i⟩) = _
    rw [DirectSum.toModule_lof, LinearMap.comp_apply]
    exact finiteShiftedFreeInsert_degree_congr 𝒜 δ i (d - δ i) d
      (sub_add_cancel d (δ i)) ⟨a.val i, a.property i⟩ _ rfl
  simp only [finiteShiftedFreeDecomposeMap, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  simp_rw [h]
  rw [← map_sum]
  congr 1
  apply Subtype.ext
  simpa only [Submodule.coe_sum] using Finset.univ_sum_single a.val

/-- The actual finite shifted free module has its actual internal decomposition. -/
instance finiteShiftedFreeDecomposition :
    DirectSum.Decomposition (finiteShiftedFreePiece 𝒜 δ) := by
  refine DirectSum.Decomposition.ofLinearMap (finiteShiftedFreePiece 𝒜 δ)
    (finiteShiftedFreeDecomposeMap 𝒜 δ) (finiteShiftedFreeDecomposeMap_recompose 𝒜 δ) ?_
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro a
  simpa only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply] using
    finiteShiftedFreeDecomposeMap_homogeneous 𝒜 δ d a

end ShiftedFree

section Presentations

variable {K R I M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [Fintype I] [DecidableEq I] [AddCommGroup M]
  [Module K M] [Module R M] [IsScalarTower K R M]
  (𝒜 : ℤ → Submodule K R) [GradedRing 𝒜]
  (ℳ : ℤ → Submodule K M) [SetLike.GradedSMul 𝒜 ℳ]
  (δ : I → ℤ) (g : I → M)

/-- The actual finite free summation map attached to actual module generators. -/
def finiteHomogeneousPresentationMap : (I → R) →ₗ[R] M where
  toFun a := ∑ i, a i • g i
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [Pi.smul_apply, smul_eq_mul, smul_smul, RingHom.id_apply, Finset.smul_sum]

omit [DecidableEq I] [IsScalarTower K R M] [GradedRing 𝒜] in
/-- True homogeneous generators make the actual summation map genuinely homogeneous. -/
theorem finiteHomogeneousPresentationMap_homogeneous
    (hg : ∀ i, g i ∈ ℳ (δ i)) (d : ℤ) (a : I → R)
    (ha : a ∈ finiteShiftedFreePiece 𝒜 δ d) :
    finiteHomogeneousPresentationMap (R := R) g a ∈ ℳ d := by
  apply Submodule.sum_mem
  intro i _
  have h := SetLike.GradedSMul.smul_mem (ha i) (hg i)
  simpa only [vadd_eq_add, sub_add_cancel] using h

omit [DecidableEq I] [Module K M] [IsScalarTower K R M] in
/-- Actual spanning by the true finite generators makes their literal summation map surjective. -/
theorem finiteHomogeneousPresentationMap_surjective
    (hs : Submodule.span R (Set.range g) = ⊤) :
    Function.Surjective (finiteHomogeneousPresentationMap (R := R) g) := by
  intro m
  have hm : m ∈ Submodule.span R (Set.range g) := hs ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hm
  exact ⟨a, ha⟩

omit [IsScalarTower K R M] in
/-- The actual syzygies of a finite homogeneous presentation form a true homogeneous submodule. -/
theorem finiteHomogeneousPresentationMap_kernel [DirectSum.Decomposition ℳ]
    (hg : ∀ i, g i ∈ ℳ (δ i)) :
    (LinearMap.ker (finiteHomogeneousPresentationMap (R := R) g)).IsHomogeneous
      (finiteShiftedFreePiece 𝒜 δ) :=
  homogeneousMap_kernel (finiteShiftedFreePiece 𝒜 δ) ℳ
    (finiteHomogeneousPresentationMap (R := R) g)
    (finiteHomogeneousPresentationMap_homogeneous 𝒜 ℳ δ g hg)

omit [IsScalarTower K R M] in
/-- The actual syzygies of a finite homogeneous presentation have actual finite homogeneous generators. -/
theorem finiteHomogeneousPresentationMap_kernel_finiteGenerators
    [IsNoetherianRing R] [DirectSum.Decomposition ℳ]
    (hg : ∀ i, g i ∈ ℳ (δ i)) :
    ∃ s : Finset (I → R),
      (∀ a ∈ s, finiteHomogeneousPresentationMap (R := R) g a = 0 ∧
        ∃ d, a ∈ finiteShiftedFreePiece 𝒜 δ d) ∧
      Submodule.span R (s : Set (I → R)) =
        LinearMap.ker (finiteHomogeneousPresentationMap (R := R) g) :=
  homogeneousMap_kernel_finiteGenerators (finiteShiftedFreePiece 𝒜 δ) ℳ
    (finiteHomogeneousPresentationMap (R := R) g)
    (finiteHomogeneousPresentationMap_homogeneous 𝒜 ℳ δ g hg)

end Presentations

section PresentationProducer

variable {K R M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  (𝒜 : ℤ → Submodule K R) [GradedRing 𝒜]
  (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul 𝒜 ℳ] [IsNoetherianRing R] [Module.Finite R M]

omit [IsScalarTower K R M] in
/-- Every actual finite graded module over a true Noetherian graded ring has
an actual finite shifted free homogeneous surjection with actual finite homogeneous syzygies. -/
theorem finiteShiftedGradedPresentation_exists :
    ∃ s : Finset M, ∃ δ : s → ℤ,
      (∀ i : s, (i : M) ∈ ℳ (δ i)) ∧
      Function.Surjective (finiteHomogeneousPresentationMap (R := R) (fun i : s => (i : M))) ∧
      ∃ t : Finset (s → R),
        (∀ a ∈ t, finiteHomogeneousPresentationMap (R := R) (fun i : s => (i : M)) a = 0 ∧
          ∃ d, a ∈ finiteShiftedFreePiece 𝒜 δ d) ∧
        Submodule.span R (t : Set (s → R)) =
          LinearMap.ker (finiteHomogeneousPresentationMap (R := R) (fun i : s => (i : M))) := by
  classical
  have htop : (⊤ : Submodule R M).IsHomogeneous ℳ := fun _ _ _ => Submodule.mem_top
  obtain ⟨s, hs, heq⟩ := homogeneousModule_finiteGenerators ℳ (⊤ : Submodule R M) htop
  choose δ hδ using fun i : s => (hs i i.property).2
  have hrange : Set.range (fun i : s => (i : M)) = (s : Set M) := by
    ext m
    constructor
    · rintro ⟨i, rfl⟩
      exact i.property
    · intro hm
      exact ⟨⟨m, hm⟩, rfl⟩
  refine ⟨s, δ, hδ, finiteHomogeneousPresentationMap_surjective (R := R) _ ?_, ?_⟩
  · rw [hrange, heq]
  · exact finiteHomogeneousPresentationMap_kernel_finiteGenerators 𝒜 ℳ δ _ hδ

end PresentationProducer

end

end DeJongAlterations.Geometry.ProperSteinProjectiveCech
