/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSmoothSubmersionJacobian
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothSubmersionDerivativeEquality
open Hironaka.HolomorphicIdealSheaves
open DerivativeIdeal GermIdealOrder OrderInvariance InvertibleIdealQuotient HadamardBridge
open HironakaSmoothPullbackDerivatives HironakaSmoothSubmersionJacobian
open Hironaka

noncomputable section
variable {n m : ℕ} {X Y : Type*} [TopologicalSpace X]
 [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
 [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

private theorem holomorphicAt_adjugate_entry
 (A : Y → Matrix (Fin n) (Fin n) ℂ) (y : Y)
 (hA : ∀ i j, HolomorphicAt m (fun p => A p i j) y) (i j : Fin n) :
 HolomorphicAt m (fun p => (A p).adjugate i j) y := by
 classical
 simp_rw [Matrix.adjugate_apply]
 apply holomorphicAt_matrix_det
 intro k l
 by_cases hk : k = j
 · subst k
   simpa [Matrix.updateRow, Function.update] using
     (holomorphicAt_const (n := m) (x := y) ((Pi.single i (1 : ℂ) : Fin n → ℂ) l))
 · simpa [Matrix.updateRow, Function.update, hk] using hA k l

theorem holomorphicAt_cramer_entry
 (A : Y → Matrix (Fin n) (Fin n) ℂ) (y : Y)
 (hA : ∀ i j, HolomorphicAt m (fun p => A p i j) y)
 (hd : (A y).det ≠ 0) (i j : Fin n) :
 HolomorphicAt m (fun p => (A p).det⁻¹ * (A p).adjugate i j) y :=
 (RelativePrincipalizationSpan.holomorphicAt_inv
   (holomorphicAt_matrix_det A y hA) hd).mul
   (holomorphicAt_adjugate_entry A y hA i j)

theorem cramer_matrix_rightInverse (A : Matrix (Fin n) (Fin n) ℂ)
 (hd : A.det ≠ 0) : A * (A.det⁻¹ • A.adjugate) = 1 := by
 rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem exists_coordinate_derivative_recovery
 {f : Y → X} {y : Y}
 (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
 (hh : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f p)
 (e : ComplexChart n X) (e' : ComplexChart m Y)
 (hy : y ∈ e'.val.source) (hfy : f y ∈ e.val.source)
 {a : X → ℂ} (ha : HolomorphicAt n a (f y)) :
 ∃ (cols : Fin n → Fin m) (B : Fin n → Fin n → Y → ℂ),
   (∀ i j, HolomorphicAt m (B i j) y) ∧ ∀ j,
   chartDeriv e (EuclideanSpace.single j 1) a ∘ f =ᶠ[𝓝 y]
     fun p => ∑ i, B i j p * chartDeriv e' (EuclideanSpace.single (cols i) 1) (a ∘ f) p := by
 classical
 obtain ⟨cols, hd, -, hdn⟩ := exists_holomorphic_nonzero_chartJacobian_minor hf hh e e' hy hfy
 let A : Y → Matrix (Fin n) (Fin n) ℂ := fun p => Matrix.of fun k i =>
   chainCoeff e e' f (EuclideanSpace.single (cols i) 1) k p
 let B : Fin n → Fin n → Y → ℂ := fun i j p => (A p).det⁻¹ * (A p).adjugate i j
 have hA : ∀ k i, HolomorphicAt m (fun p => A p k i) y := fun k i =>
   holomorphicAt_chainCoeff e e' hh hy hfy _ _
 have hB : ∀ i j, HolomorphicAt m (B i j) y := fun i j =>
   holomorphicAt_cramer_entry A y hA hd i j
 have hchain : ∀ i, chartDeriv e' (EuclideanSpace.single (cols i) 1) (a ∘ f) =ᶠ[𝓝 y]
     fun p => ∑ k, A p k i * chartDeriv e (EuclideanSpace.single k 1) a (f p) :=
   fun i => chartDeriv_comp_eventuallyEq_sum e e' hh hy hfy ha _
 refine ⟨cols, B, hB, fun j => ?_⟩
 filter_upwards [hdn, eventually_all.2 hchain] with p hp hc
 have hAB : A p * Matrix.of (fun i j => B i j p) = 1 :=
   cramer_matrix_rightInverse (A p) hp
 have hentry (k : Fin n) : (∑ i, A p k i * B i j p) = if k = j then 1 else 0 := by
   simpa only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] using
     congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M k j) hAB
 simp only [Function.comp_apply]
 calc
   chartDeriv e (EuclideanSpace.single j 1) a (f p) =
       ∑ k, (∑ i, A p k i * B i j p) * chartDeriv e (EuclideanSpace.single k 1) a (f p) := by
         simp [hentry]
   _ = ∑ i, B i j p * chartDeriv e' (EuclideanSpace.single (cols i) 1) (a ∘ f) p := by
     simp_rw [hc, Finset.mul_sum, Finset.sum_mul]
     rw [Finset.sum_comm]
     apply Finset.sum_congr rfl
     intro i _
     apply Finset.sum_congr rfl
     intro k _
     ring

omit [IsComplexManifold n X] in
private theorem chartDeriv_eq_coordinate_sum (e : ComplexChart n X)
 (v : ComplexModel n) (a : X → ℂ) :
 chartDeriv e v a = fun p => ∑ j, v j * chartDeriv e (EuclideanSpace.single j 1) a p := by
 funext p
 simp only [chartDeriv]
 conv_lhs => rw [← sum_smul_single v]
 rw [map_sum]
 exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]

theorem pulled_chartDeriv_mem_derivIdeal
 {f : Y → X} {I : GermIdeal n X} {y : Y}
 (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
 (hh : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f p)
 (hI : ∀ x a, I.mem x a → HolomorphicAt n a x)
 (e : ComplexChart n X) (hfy : f y ∈ e.val.source)
 (v : ComplexModel n) {a : X → ℂ} (ha : I.mem (f y) a) :
 (derivIdeal (GermIdeal.pullback (m := m) f I)).mem y (chartDeriv e v a ∘ f) := by
 let e' := complexChartAt (n := m) y
 have hy : y ∈ e'.val.source := mem_complexChartAt_source y
 obtain ⟨cols, B, hB, he⟩ := exists_coordinate_derivative_recovery hf hh e e' hy hfy (hI _ _ ha)
 have hap : (GermIdeal.pullback (m := m) f I).mem y (a ∘ f) :=
   RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr <|
   InvertibleIdealQuotient.isInSpanAt_self ⟨a, ha, rfl⟩
     (holomorphicAt_comp_map (Eventually.of_forall hh) (hI _ _ ha))
 have hcoord (j : Fin n) :
     (derivIdeal (GermIdeal.pullback (m := m) f I)).mem y
       (chartDeriv e (EuclideanSpace.single j 1) a ∘ f) := by
   apply isInSpanAt_congr (RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ
     (fun i _ => RelativePrincipalizationSpan.IsInSpanAt.mul_left (hB i j)
       (chartDeriv_mem_derivIdeal (𝔞 := GermIdeal.pullback (m := m) f I)
          (fun _ _ hg => (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg).1) hy hap)))
   exact (he j).symm
 rw [chartDeriv_eq_coordinate_sum e v a]
 exact RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun j _ =>
   RelativePrincipalizationSpan.IsInSpanAt.mul_left (holomorphicAt_const (v j)) (hcoord j)

theorem pullback_derivIdeal_le
 {f : Y → X} {I : GermIdeal n X}
 (hf : ∀ y, Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
 (hh : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f p)
 (hI : ∀ x a, I.mem x a → HolomorphicAt n a x) :
 (GermIdeal.pullback (m := m) f (derivIdeal I)).Le (derivIdeal (GermIdeal.pullback (m := m) f I)) := by
 intro y g hg
 change IsInSpanAt (n := m) (DerivGen (GermIdeal.pullback (m := m) f I) y) y g
 refine RelativePrincipalizationSpan.IsInSpanAt.trans ?_
   (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg)
 rintro _ ⟨a, ha, rfl⟩
 obtain ⟨_, N, s, c, hs, hc, he⟩ := ha
 have hsp (i : Fin N) : (derivIdeal (GermIdeal.pullback (m := m) f I)).mem y (s i ∘ f) := by
   rcases hs i with hi | ⟨e, v, b, hfy, hb, heq⟩
   · apply le_derivIdeal (fun _ _ hg => (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg).1)
     apply RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
     exact InvertibleIdealQuotient.isInSpanAt_self ⟨s i, hi, rfl⟩
       (holomorphicAt_comp_map (Eventually.of_forall hh) (hI _ _ hi))
   · rw [heq]
     exact pulled_chartDeriv_mem_derivIdeal (hf y) hh hI e hfy v hb
 have hsum := RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun i _ =>
   RelativePrincipalizationSpan.IsInSpanAt.mul_left
     (holomorphicAt_comp_map (Eventually.of_forall hh) (hc i)) (hsp i)
 apply isInSpanAt_congr hsum
 have hcomp : a ∘ f =ᶠ[𝓝 y] fun p => ∑ i, c i (f p) * s i (f p) :=
   ((hh y).continuousAt.tendsto).eventually he
 exact hcomp.symm

theorem derivIdeal_pullback_eq
 {f : Y → X} {I : GermIdeal n X}
 (hf : ∀ y, Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
 (hh : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f p)
 (hI : ∀ x a, I.mem x a → HolomorphicAt n a x) :
 derivIdeal (GermIdeal.pullback (m := m) f I) = GermIdeal.pullback (m := m) f (derivIdeal I) := by
 ext y g
 exact ⟨derivIdeal_pullback_le hh hI y g, pullback_derivIdeal_le hf hh hI y g⟩

theorem iterDerivIdeal_pullback_eq
 {f : Y → X} {I : GermIdeal n X}
 (hf : ∀ y, Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
 (hh : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f p)
 (hI : ∀ x a, I.mem x a → HolomorphicAt n a x) :
 ∀ r, iterDerivIdeal (GermIdeal.pullback (m := m) f I) r =
   GermIdeal.pullback (m := m) f (iterDerivIdeal I r)
 | 0 => rfl
 | r+1 => by
   rw [iterDerivIdeal_succ, iterDerivIdeal_pullback_eq hf hh hI r,
     derivIdeal_pullback_eq hf hh (holomorphicAt_of_mem_iterDerivIdeal hI r), iterDerivIdeal_succ]
end
end Hironaka.HironakaSmoothSubmersionDerivativeEquality
