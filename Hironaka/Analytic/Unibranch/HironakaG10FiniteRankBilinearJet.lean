import Hironaka.Analytic.Unibranch.HironakaG10BanachJetFiniteSum

/-! # Exact bilinear jet formula for actual finite-rank families -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10FiniteRankBilinearJet
open Hironaka Hironaka
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10BanachJetFiniteSum

/-- A continuous bilinear operation on actual finite-rank holomorphic
families has the exact double-sum parameter jet, with the scalar factors
the images of their original holomorphic germs. -/
theorem banachJet_bilinear_finite_rank
    {Γ E F G ι κ : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    [Fintype ι] [Fintype κ]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (B : E →L[ℂ] F →L[ℂ] G)
    (f : ι → ComplexModel d → ℂ) (g : κ → ComplexModel d → ℂ)
    (v : ι → E) (w : κ → F)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (f i) z)
    (hg : ∀ j, ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (g j) z) :
    banachJet d q φ (fun z => B (∑ i, f i z • v i) (∑ j, g j z • w j)) =
      ∑ i, ∑ j, (φ (HolGerm.mk (f i) (hf i)) * φ (HolGerm.mk (g j) (hg j))) ⊗ₜ[ℂ]
        B (v i) (w j) := by
  classical
  let h : ι × κ → ComplexModel d → ℂ := fun p z => f p.1 z * g p.2 z
  let u : ι × κ → G := fun p => B (v p.1) (w p.2)
  have hh : ∀ p, ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (h p) z := by
    intro p
    exact (hf p.1).and (hg p.2) |>.mono fun _ hz => hz.1.mul hz.2
  have hfun : (fun z => B (∑ i, f i z • v i) (∑ j, g j z • w j)) =
      (fun z => ∑ p : ι × κ, h p z • u p) := by
    funext z
    simp only [h,u,Fintype.sum_prod_type, map_sum, sum_apply, map_smul, smul_apply]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_comm]
  rw [hfun, banachJet_finite_rank_sum d q φ hφ Finset.univ h u hh]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change φ (HolGerm.mk (fun z => f i z * g j z) _) ⊗ₜ[ℂ] B (v i) (w j) = _
  rw [HolGerm.mk_mul, map_mul]

end Hironaka.Analytic.Unibranch.HironakaG10FiniteRankBilinearJet
