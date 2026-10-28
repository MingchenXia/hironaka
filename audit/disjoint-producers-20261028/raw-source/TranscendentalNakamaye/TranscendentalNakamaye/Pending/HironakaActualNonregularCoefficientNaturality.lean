import TranscendentalNakamaye.Pending.HomogenizedIdealAlong

set_option autoImplicit false
/-! Whole étale coefficient records on arbitrary carriers, using holomorphic members only. -/
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace TranscendentalNakamaye.Pending.HironakaActualNonregularCoefficientNaturality
open FirstPass FirstPass.HolomorphicIdealSheaves
open GermIdealOrder IdealWeightPowers GermIdealPullbackCalculus InvertibleIdealQuotient
open RelativePrincipalizationSpan HomogenizedGlueing CoefficientIdeal
open MarkedIdealBiholomorphism HomogenizedEquivalence DerivativeIdealAlong
open MarkedIdeals HomogenizedIdealAlong DerivativeIdealAlongEtale GiraudAlong
noncomputable section
variable {n m : ℕ} {X Y : Type u} [TopologicalSpace X]
 [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
 [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
variable {f : Y → X}

theorem pullback_mul
 (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
 {I J : GermIdeal n X}
 (hholI : ∀ {x g}, I.mem x g → HolomorphicAt n g x)
 (hholJ : ∀ {x g}, J.mem x g → HolomorphicAt n g x) :
 GermIdeal.pullback (m := m) f (I.mul J) =
   (GermIdeal.pullback (m := m) f I).mul (GermIdeal.pullback (m := m) f J) := by
 refine GermIdeal.ext (funext fun y => funext fun g => propext
   ⟨fun hg => pullback_mul_le hf hholI hholJ y g hg, fun hg => ?_⟩)
 have hfat : ∀ᶠ z in 𝓝 y, ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f z :=
   Eventually.of_forall fun z => hf.contMDiffAt
 refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_ (mem_mul_iff.mp hg))
 rintro _ ⟨p, q, hp, hq, rfl⟩
 obtain ⟨-, K, s, γ, hs, hγ, hsum⟩ := GermIdeal.mem_pullback_iff.mp hp
 obtain ⟨-, L, s', δ, hs', hδ, hsum'⟩ := GermIdeal.mem_pullback_iff.mp hq
 choose a ha hsa using hs
 choose b hb hsb using hs'
 have hterm : ∀ r : Fin K × Fin L,
     IsInSpanAt (n := m) (fun u => ∃ c, (I.mul J).mem (f y) c ∧ u = c ∘ f) y
       (fun z => γ r.1 z * δ r.2 z * (s r.1 z * s' r.2 z)) := by
   rintro ⟨i, j⟩
   have hab : (I.mul J).mem (f y) (fun x => a i x * b j x) :=
     mem_mul_iff.mpr (isInSpanAt_self ⟨a i, b j, ha i, hb j, rfl⟩
       ((hholI (ha i)).mul (hholJ (hb j))))
   have heq : (fun z => s i z * s' j z) = (fun x => a i x * b j x) ∘ f := by
     funext z
     rw [hsa i, hsb j]
     rfl
   have hhol : HolomorphicAt m (fun z => s i z * s' j z) y := by
     rw [heq]
     exact ((hholI (ha i)).mul (hholJ (hb j))).comp_contMDiff hfat
   exact IsInSpanAt.mul_left ((hγ i).mul (hδ j)) (isInSpanAt_self ⟨_, hab, heq⟩ hhol)
 refine IsInSpanAt.congr' (IsInSpanAt.sum Finset.univ fun r _ => hterm r) ?_
 filter_upwards [hsum, hsum'] with z hz hz'
 show (∑ r : Fin K × Fin L, γ r.1 z * δ r.2 z * (s r.1 z * s' r.2 z)) = p z * q z
 rw [hz, hz', Finset.sum_mul_sum, Fintype.sum_prod_type]
 exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [IsComplexManifold n X] [IsComplexManifold m Y] in
theorem pullback_unitIdeal : GermIdeal.pullback (m := m) f (unitIdeal n X) = unitIdeal m Y := by
 ext y g
 constructor
 · intro hg
   exact (GermIdeal.mem_pullback_iff.mp hg).1
 · intro hg
   apply GermIdeal.mem_pullback_iff.mpr
   exact isInSpanAt_of_eq_mul ⟨(fun _ => 1), holomorphicAt_const 1, rfl⟩ hg hg
     (Eventually.of_forall fun _ => (mul_one _).symm)

theorem pullback_idealPow
 (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
 {I : GermIdeal n X} (hI : ∀ {x g}, I.mem x g → HolomorphicAt n g x) :
 ∀ q, GermIdeal.pullback (m := m) f (idealPow I q) =
   idealPow (GermIdeal.pullback (m := m) f I) q
 | 0 => pullback_unitIdeal
 | q+1 => by
   rw [idealPow_succ,
     pullback_mul hf
       (fun {_ _} hg => holomorphicAt_of_mem_idealPow hg) hI,
     pullback_idealPow hf hI q, idealPow_succ]

theorem pullback_finSumIdeal
 (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
 (J : ℕ → GermIdeal n X) (r : ℕ) (hJ : ∀ i < r, ∀ {x g}, (J i).mem x g → HolomorphicAt n g x) :
 GermIdeal.pullback (m := m) f (finSumIdeal J r) =
   finSumIdeal (fun i => GermIdeal.pullback (m := m) f (J i)) r := by
 ext y g
 constructor
 · intro hg
   change IsInSpanAt (n := m) (fun s => ∃ i, i < r ∧ (GermIdeal.pullback (m := m) f (J i)).mem y s) y g
   refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
   rintro _ ⟨a, ha, rfl⟩
   change IsInSpanAt (n := n) (fun b => ∃ i, i < r ∧ (J i).mem (f y) b) (f y) a at ha
   refine IsInSpanAt.trans ?_ (GermIdealPullbackCalculus.isInSpanAt_comp hf ha)
   rintro _ ⟨b, ⟨i, hi, hb⟩, rfl⟩
   exact isInSpanAt_self ⟨i, hi, GermIdeal.mem_pullback_iff.mpr
     (isInSpanAt_self ⟨b, hb, rfl⟩
       ((hJ i hi hb).comp_contMDiff
         (Eventually.of_forall fun _ => hf.contMDiffAt)))⟩
     ((hJ i hi hb).comp_contMDiff
         (Eventually.of_forall fun _ => hf.contMDiffAt))
 · intro hg
   apply GermIdeal.mem_pullback_iff.mpr
   change IsInSpanAt (n := m) (fun s => ∃ i, i < r ∧ (GermIdeal.pullback (m := m) f (J i)).mem y s) y g at hg
   refine IsInSpanAt.trans ?_ hg
   rintro a ⟨i, hi, ha⟩
   have hm : ∀ s, (∃ b, (J i).mem (f y) b ∧ s = b ∘ f) →
       (∃ b, (finSumIdeal J r).mem (f y) b ∧ s = b ∘ f) := by
     rintro _ ⟨b, hb, rfl⟩
     refine ⟨b, ?_, rfl⟩
     change IsInSpanAt (n := n) (fun c => ∃ j, j < r ∧ (J j).mem (f y) c) (f y) b
     exact isInSpanAt_self ⟨i, hi, hb⟩ (hJ i hi hb)
   exact IsInSpanAt.mono hm (GermIdeal.mem_pullback_iff.mp ha)

theorem pullback_homSum
 (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
 (A : ℕ → GermIdeal n X) (B : GermIdeal n X) (r : ℕ)
 (hA : ∀ i < r, ∀ {x g}, (A i).mem x g → HolomorphicAt n g x)
 (hB : ∀ {x g}, B.mem x g → HolomorphicAt n g x) :
 GermIdeal.pullback (m := m) f (homSum A B r) =
   homSum (fun i => GermIdeal.pullback (m := m) f (A i))
     (GermIdeal.pullback (m := m) f B) r := by
 unfold homSum
 rw [pullback_finSumIdeal hf (fun i => (A i).mul (idealPow B i)) r
   (fun _ _ {_ _} hg => (mem_mul_iff.mp hg).1)]
 apply finSumIdeal_congr
 intro i hi
 rw [pullback_mul hf
   (hA i hi) (fun {_ _} hg => holomorphicAt_of_mem_idealPow hg), pullback_idealPow hf hB]

section SameDimension
variable {Z : Type u} [TopologicalSpace Z]
 [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
variable {f : Z → X}

theorem pullback_homogenizedIdealAlong
 (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
 (hloc : ∀ y : Z, ∃ ψ : X → Z, IsLocalInverseAt n f ψ y)
 {N : Set X} {I : GermIdeal n X}
 (hI : ∀ x g, I.mem x g → HolomorphicAt n g x) (d : ℕ) :
 GermIdeal.pullback (m := n) f (homogenizedIdealAlong N I d) =
   homogenizedIdealAlong (f ⁻¹' N) (GermIdeal.pullback (m := n) f I) d := by
 unfold homogenizedIdealAlong
 rw [pullback_homSum hf (fun i => iterDerivIdealAlong N I i) (tangentIdealAlong N I d) d
   (fun i _ {_ _} hg => holomorphicAt_of_mem_iterDerivIdealAlong hI i _ _ hg)
   (fun {_ _} hg => holomorphicAt_of_mem_iterDerivIdealAlong (N := N) hI (d-1) _ _ hg)]
 exact homSum_congr (fun i _ => pullback_iterDerivIdealAlong hloc hI i)
   (HomogenizedIdealAlong.pullback_tangentIdealAlong hloc hI d)

theorem pullback_homMarkedAlong
 (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
 (hloc : ∀ y : Z, ∃ ψ : X → Z, IsLocalInverseAt n f ψ y)
 (M : MarkedIdeal n X) (hI : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x) :
 MarkedIdeal.pullback f (homMarkedAlong M) =
   homMarkedAlong (MarkedIdeal.pullback f M) :=
 MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl
   (pullback_homogenizedIdealAlong hf hloc hI M.d) rfl

theorem pullback_coeffMarkedAlong
 (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
 (hloc : ∀ y : Z, ∃ ψ : X → Z, IsLocalInverseAt n f ψ y)
 (M : MarkedIdeal n X) (hI : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x) :
 MarkedIdeal.pullback f (coeffMarkedAlong M) =
   coeffMarkedAlong (MarkedIdeal.pullback f M) := by
 refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
 show GermIdeal.pullback (m := n) f (finSumIdeal
     (fun i => idealPow (iterDerivIdealAlong M.N M.ideal i)
       (sumExp (fun j => M.d-j) M.d i)) M.d) =
   finSumIdeal (fun i => idealPow
     (iterDerivIdealAlong (f ⁻¹' M.N) (GermIdeal.pullback (m := n) f M.ideal) i)
     (sumExp (fun j => M.d-j) M.d i)) M.d
 rw [pullback_finSumIdeal hf _ _ (fun _ _ {_ _} hg => holomorphicAt_of_mem_idealPow hg)]
 refine finSumIdeal_congr fun i _ => ?_
 rw [pullback_idealPow hf
   (fun {_ _} hg => holomorphicAt_of_mem_iterDerivIdealAlong hI i _ _ hg),
   pullback_iterDerivIdealAlong hloc hI i]

theorem pullback_coeff_homMarkedAlong
 (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
 (hloc : ∀ y : Z, ∃ ψ : X → Z, IsLocalInverseAt n f ψ y)
 (M : MarkedIdeal n X) (hI : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x) :
 MarkedIdeal.pullback f (coeffMarkedAlong (homMarkedAlong M)) =
   coeffMarkedAlong (homMarkedAlong (MarkedIdeal.pullback f M)) := by
 rw [pullback_coeffMarkedAlong hf hloc (homMarkedAlong M) (fun _ _ hg => hg.1),
   pullback_homMarkedAlong hf hloc M hI]

end SameDimension
end
end TranscendentalNakamaye.Pending.HironakaActualNonregularCoefficientNaturality
