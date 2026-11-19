import Hironaka.Analytic.Unibranch.HironakaG10BilinearJetTaylorReduction
import Hironaka.Analytic.Unibranch.HironakaG10BanachTaylorCoordinates
import Hironaka.Analytic.Unibranch.HironakaG10FiniteRankBilinearJet
import Hironaka.Analytic.Unibranch.HironakaG10TensorBilinearExtension

/-! # Bilinear naturality of the actual Banach parameter jet -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10BanachBilinearJetNaturality
open Hironaka Hironaka
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10NormalizedBanachTaylor
  Hironaka.Analytic.Unibranch.HironakaG10BanachTaylorRemainder
  Hironaka.Analytic.Unibranch.HironakaG10BilinearTaylorReduction
  Hironaka.Analytic.Unibranch.HironakaG10BilinearJetTaylorReduction
  Hironaka.Analytic.Unibranch.HironakaG10BanachTaylorCoordinates
  Hironaka.Analytic.Unibranch.HironakaG10BanachJetFiniteSum
  Hironaka.Analytic.Unibranch.HironakaG10FiniteRankBilinearJet
  Hironaka.Analytic.Unibranch.HironakaG10TensorBilinearExtension

private theorem wordScalar_holomorphic (d N : ℕ) (w : TaylorWord d N) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (wordScalar w) z := by
  apply Eventually.of_forall
  intro z
  unfold wordScalar
  exact (HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ =>
    (EuclideanSpace.proj (w.2 i) : ComplexModel d →L[ℂ] ℂ).hasFDerivAt)).differentiableAt

private theorem banachJet_eq_taylorPartial
    {Γ E : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (f : ComplexModel d → E)
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z) :
    banachJet d q φ f = banachJet d q φ (taylorPartial f (q+1)) := by
  classical
  have hfc : ContDiffAt ℂ ⊤ f 0 := (has_normalized_powerSeriesAt f hf).analyticAt.contDiffAt
  have hpc : ContDiffAt ℂ ⊤ (taylorPartial f (q+1)) 0 := taylorPartial_contDiffAt f (q+1)
  simp only [banachJet]
  apply Finset.sum_congr rfl
  intro k hk
  have he := iteratedFDeriv_sub_taylorPartial_eq_zero f hf (q+1) k (Finset.mem_range.mp hk)
  rw [iteratedFDeriv_sub_apply (hfc.of_le (by simp)) (hpc.of_le (by simp)), sub_eq_zero] at he
  rw [he]

/-- Whole parameter jets commute with an arbitrary continuous complex-bilinear
operation on actual holomorphic Banach-valued families. -/
theorem banachJet_bilinear
    {Γ E F G : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (B : E →L[ℂ] F →L[ℂ] G) (f : ComplexModel d → E) (g : ComplexModel d → F)
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ g z) :
    banachJet d q φ (fun z => B (f z) (g z)) =
      tensorBilinear B (banachJet d q φ f) (banachJet d q φ g) := by
  classical
  let W := TaylorWord d (q+1)
  have hw : ∀ w : W, ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (wordScalar w) z :=
    wordScalar_holomorphic d (q+1)
  have hPf : taylorPartial f (q+1) = fun z => ∑ w : W, wordScalar w z • wordCoefficient f w :=
    funext (taylorPartial_eq_word_sum d (q+1) f)
  have hPg : taylorPartial g (q+1) = fun z => ∑ w : W, wordScalar w z • wordCoefficient g w :=
    funext (taylorPartial_eq_word_sum d (q+1) g)
  have hjf : banachJet d q φ (taylorPartial f (q+1)) =
      ∑ w : W, φ (HolGerm.mk (wordScalar w) (hw w)) ⊗ₜ[ℂ] wordCoefficient f w := by
    rw [hPf]
    simpa using banachJet_finite_rank_sum d q φ hφ Finset.univ wordScalar (wordCoefficient f) hw
  have hjg : banachJet d q φ (taylorPartial g (q+1)) =
      ∑ w : W, φ (HolGerm.mk (wordScalar w) (hw w)) ⊗ₜ[ℂ] wordCoefficient g w := by
    rw [hPg]
    simpa using banachJet_finite_rank_sum d q φ hφ Finset.univ wordScalar (wordCoefficient g) hw
  calc
    banachJet d q φ (fun z => B (f z) (g z)) =
        banachJet d q φ (fun z => B (taylorPartial f (q+1) z) (taylorPartial g (q+1) z)) :=
      banachJet_bilinear_taylorPartial d q φ B f g hf hg
    _ = ∑ i : W, ∑ j : W,
        (φ (HolGerm.mk (wordScalar i) (hw i)) * φ (HolGerm.mk (wordScalar j) (hw j))) ⊗ₜ[ℂ]
          B (wordCoefficient f i) (wordCoefficient g j) := by
      rw [hPf,hPg]
      exact banachJet_bilinear_finite_rank d q φ hφ B wordScalar wordScalar
        (wordCoefficient f) (wordCoefficient g) hw hw
    _ = tensorBilinear B (banachJet d q φ (taylorPartial f (q+1)))
        (banachJet d q φ (taylorPartial g (q+1))) := by
      rw [hjf,hjg]
      simp only [map_sum, LinearMap.sum_apply, tensorBilinear_tmul]
      exact Finset.sum_comm
    _ = tensorBilinear B (banachJet d q φ f) (banachJet d q φ g) := by
      rw [← banachJet_eq_taylorPartial d q φ f hf, ← banachJet_eq_taylorPartial d q φ g hg]

end Hironaka.Analytic.Unibranch.HironakaG10BanachBilinearJetNaturality
