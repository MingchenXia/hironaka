import Hironaka.Analytic.Unibranch.HironakaG10SameWindowSupportNecessity
import Hironaka.Analytic.Unibranch.HironakaG10NativeFixedSchurNearbySufficiency
import Hironaka.Analytic.Unibranch.HironakaG10SchurSectionStalk
import Hironaka.Analytic.Unibranch.HironakaG10ActualSchurScalarSections
import Hironaka.Analytic.Unibranch.HironakaG10ScalarGermSupport
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10SameWindowOneFamily
open Hironaka Hironaka
  HolGerm OkaGermBridge OkaRelationSheaf HironakaRelativeNormalIdeal
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatPrivilegedEuclidean HironakaG10FlatResolutionStart
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus HironakaG10LocSectionNoether
  HironakaSmoothCentreRealDomainActualSheafStalk
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur
  Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm Hironaka.Analytic.Unibranch.HironakaG10ActualSchurHolomorphic
  Hironaka.Analytic.Unibranch.HironakaG10ActualSchurScalarSections Hironaka.Analytic.Unibranch.HironakaG10SchurSectionStalk
  Hironaka.Analytic.Unibranch.HironakaG10NativeFixedSchurNearbySufficiency
  Hironaka.Analytic.Unibranch.HironakaG10ScalarGermSupport
  Hironaka.Analytic.Unibranch.HironakaG10SameWindowSupportNecessity
noncomputable section
local instance (d : ℕ) : Algebra ℂ (HolGerm (ComplexModel d)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel d)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (basePullback d t).toAlgebra

theorem original_one_schur_section_family_necessary_and_sufficient_near_support
    (d t : ℕ) {a b c : ℕ}
    {K₀ K₁ : Set (ComplexModel t)} [CompactSpace K₀] [CompactSpace K₁]
    (hK₁ : K₁ ∈ closedPolydiscs t) (hK₁₀ : K₁ ⊆ interior K₀)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK₀ : ∀ z ∈ K₀, (0,z) ∈ O)
    (G₀ : Fin b → Fin c → ComplexModel t → ℂ)
    (hG₀ : ∀ j l, DifferentiableOn ℂ (G₀ j l) (interior K₀))
    (hex : DirectExact (restrictMatrix K₁ hK₁₀ G₀ hG₀)
      (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x)) (zeroFibre_holomorphic d t hO hF hK₀))) :
    let f₀ := matrixOperator (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
      (zeroFibre_holomorphic d t hO hF hK₀))
    let g₀ := matrixOperator (restrictMatrix K₁ hK₁₀ G₀ hG₀)
    let f := sourceOperator d t (K₁ := K₁) hF
    ∃ (R₀ : (Fin b → holSubalgebra K₁) →L[ℂ] (Fin c → holSubalgebra K₁))
      (S₀ : (Fin a → holSubalgebra K₁) →L[ℂ] (Fin b → holSubalgebra K₁)),
      ∃ (U : Opens (ComplexModel d)) (_h0 : (0 : ComplexModel d) ∈ U)
        (hSU : DifferentiableOn ℂ (fun p => schurOp (g₀.comp R₀) (f₀.comp S₀) S₀ (f p)) U),
        let S := fun p => schurOp (g₀.comp R₀) (f₀.comp S₀) S₀ (f p)
        let X := ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) U
        let s : (Fin b → holSubalgebra K₁) × ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ) → X.presheaf.obj (op ⊤) :=
          fun q => operatorScalarSection d U S hSU q.1 q.2
        (∀ p : U, ∃ T : Finset ((Fin b → holSubalgebra K₁) × ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ)),
          ∀ᶠ y in 𝓝 p, spanFamily s univ y = spanFamily s (T : Set _) y) ∧
        (Ideal.map (actualStalkChartEquiv (n := d) (⟨0,_h0⟩ : U)).toRingHom
          (spanFamily s univ (⟨0,_h0⟩ : U)) ≠ ⊤) ∧
        (∀ p : U, Ideal.map (actualStalkChartEquiv (n := d) p).toRingHom (spanFamily s univ p) ≠ ⊤ → ∀ I : Ideal (HolGerm (ComplexModel d)),
          (∀ z ∈ K₁, Module.Flat (HolGerm (ComplexModel d) ⧸ I)
            ((HolGerm (ComplexModel d) ⧸ I) ⊗[HolGerm (ComplexModel d)]
              ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
                (Matrix.mulVecLin (fun i j => germAt (p.val,z) (F i j)))))) →
          Ideal.map (actualStalkChartEquiv (n := d) p).toRingHom (spanFamily s univ p) ≤ I) ∧
        (∀ p : U, Ideal.map (actualStalkChartEquiv (n := d) p).toRingHom (spanFamily s univ p) ≠ ⊤ → ∀ I : Ideal (HolGerm (ComplexModel d)),
          Ideal.map (actualStalkChartEquiv (n := d) p).toRingHom (spanFamily s univ p) ≤ I →
          ∀ z ∈ interior K₁, Module.Flat (HolGerm (ComplexModel d) ⧸ I)
            ((HolGerm (ComplexModel d) ⧸ I) ⊗[HolGerm (ComplexModel d)]
              ((Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸ LinearMap.range
                (Matrix.mulVecLin (fun i j => germAt (p.val,z) (F i j)))))) := by
  let f₀ := matrixOperator (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
    (zeroFibre_holomorphic d t hO hF hK₀))
  let g₀ := matrixOperator (restrictMatrix K₁ hK₁₀ G₀ hG₀)
  let f := sourceOperator d t (K₁ := K₁) hF
  obtain ⟨S₀,hS⟩ := hex.exists_generalizedInverse_f
  obtain ⟨R₀,hR⟩ := hex.exists_generalizedInverse_g
  let S := fun p => schurOp (g₀.comp R₀) (f₀.comp S₀) S₀ (f p)
  have hK₁O : ∀ z ∈ K₁, (0,z) ∈ O := fun z hz => hK₀ z (interior_subset (hK₁₀ hz))
  have hf : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f s :=
    sourceOperator_holomorphic d t hO hF hK₁O
  have hf0 : f 0 = f₀ := sourceOperator_zero d t hK₁₀ hO hF hK₀
  have hcomp : ∀ e, f₀ (g₀ e) = 0 := matrixOperator_comp_apply _ _ hex.comp
  have hC0 : opC (g₀.comp R₀) (f₀.comp S₀) S₀ (f 0) = ContinuousLinearMap.id ℂ _ := by
    rw [hf0]
    exact opC_self hcomp
  have hSnear : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ S s :=
    actual_schur_holomorphic d (g₀.comp R₀) (f₀.comp S₀) S₀ f hf hC0
  have hFlat := original_fixed_schur_ideal_suffices_near_support d t hK₁ hK₁₀ hO hF hK₀ G₀ hG₀ hex R₀ hR S₀ hS
  have hNec := native_scalar_ideal_necessary_near_same_support d t hK₁ hK₁₀ hO hF hK₀ G₀ hG₀ hex R₀ hR S₀ hS
  obtain ⟨V,hVsub,hVopen,h0V⟩ := eventually_nhds_iff.mp (hSnear.and (hFlat.and hNec))
  let U : Opens (ComplexModel d) := ⟨V,hVopen⟩
  have hSU : DifferentiableOn ℂ S U := fun p hp => (hVsub p hp).1.differentiableWithinAt
  refine ⟨R₀,S₀,U,h0V,hSU,?_,?_,?_,?_⟩
  · intro p
    exact scalarOperatorSections_finite_near d U S hSU p
  · have hmap := map_scalarOperatorSection_stalk_ideal d U S hSU ⟨0,h0V⟩
    change Ideal.map (actualStalkChartEquiv (n := d) (⟨0,h0V⟩ : U)).toRingHom
      (spanFamily (X := ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) U)
        (fun q : (Fin b → holSubalgebra K₁) ×
        ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ) => operatorScalarSection d U S hSU q.1 q.2) univ ⟨0,h0V⟩) =
      Ideal.span (Set.range fun q : (Fin b → holSubalgebra K₁) ×
        ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ) =>
        let L := q.2.comp (ContinuousLinearMap.apply ℂ (Fin a → holSubalgebra K₁) q.1)
        germAt (0 : ComplexModel d) (L ∘ S)) at hmap
    rw [hmap]
    apply (scalar_germ_ideal_ne_top_iff_operator_zero d 0 S hSnear).mpr
    change schurOp (g₀.comp R₀) (f₀.comp S₀) S₀ (f 0) = 0
    rw [hf0]
    exact schurOp_self hS hcomp
  · intro p hpProper I hpflat
    have hmap := map_scalarOperatorSection_stalk_ideal d U S hSU p
    change Ideal.map (actualStalkChartEquiv (n := d) p).toRingHom
      (spanFamily (X := ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) U)
        (fun q : (Fin b → holSubalgebra K₁) ×
        ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ) => operatorScalarSection d U S hSU q.1 q.2) univ p) =
      Ideal.span (Set.range fun q : (Fin b → holSubalgebra K₁) ×
        ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ) =>
        let L := q.2.comp (ContinuousLinearMap.apply ℂ (Fin a → holSubalgebra K₁) q.1)
        germAt p.val (L ∘ S)) at hmap
    have hhol : ∀ᶠ y in 𝓝 p.val, DifferentiableAt ℂ S y := by
      filter_upwards [hVopen.mem_nhds p.property] with y hy
      exact (hVsub y hy).1
    have hpProper' : (Ideal.span (Set.range fun q : (Fin b → holSubalgebra K₁) ×
        ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ) =>
        let L := q.2.comp (ContinuousLinearMap.apply ℂ (Fin a → holSubalgebra K₁) q.1)
        germAt p.val (L ∘ S)) : Ideal (HolGerm (ComplexModel d))) ≠ ⊤ := hmap ▸ hpProper
    have hpS : S p = 0 := (scalar_germ_ideal_ne_top_iff_operator_zero d p.val S hhol).mp hpProper'
    exact hmap.le.trans ((hVsub p.val p.property).2.2 hpS I hpflat)
  · intro p hpProper I hpI z hz
    have hmap := map_scalarOperatorSection_stalk_ideal d U S hSU p
    change Ideal.map (actualStalkChartEquiv (n := d) p).toRingHom
      (spanFamily (X := ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) U)
        (fun q : (Fin b → holSubalgebra K₁) ×
        ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ) => operatorScalarSection d U S hSU q.1 q.2) univ p) =
      Ideal.span (Set.range fun q : (Fin b → holSubalgebra K₁) ×
        ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ) =>
        let L := q.2.comp (ContinuousLinearMap.apply ℂ (Fin a → holSubalgebra K₁) q.1)
        germAt p.val (L ∘ S)) at hmap
    have hscalar : Ideal.span (Set.range fun q : (Fin b → holSubalgebra K₁) ×
        ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ) =>
        let L := q.2.comp (ContinuousLinearMap.apply ℂ (Fin a → holSubalgebra K₁) q.1)
        germAt p.val (L ∘ S)) ≤ I := by
      exact hmap.symm.le.trans hpI
    have hhol : ∀ᶠ y in 𝓝 p.val, DifferentiableAt ℂ S y := by
      filter_upwards [hVopen.mem_nhds p.property] with y hy
      exact (hVsub y hy).1
    have hpProper' : (Ideal.span (Set.range fun q : (Fin b → holSubalgebra K₁) ×
        ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ) =>
        let L := q.2.comp (ContinuousLinearMap.apply ℂ (Fin a → holSubalgebra K₁) q.1)
        germAt p.val (L ∘ S)) : Ideal (HolGerm (ComplexModel d))) ≠ ⊤ := by
      exact hmap ▸ hpProper
    have hpS : S p = 0 := (scalar_germ_ideal_ne_top_iff_operator_zero d p.val S hhol).mp hpProper'
    exact (hVsub p.val p.property).2.1 I hpS hscalar z hz
end
end Hironaka.Analytic.Unibranch.HironakaG10SameWindowOneFamily
