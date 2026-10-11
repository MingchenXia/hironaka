/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaHolomorphicJetRankLoci
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Entire nonlinear chart germ algebras and intrinsic Hilbert--Samuel superlevels

Actual nonlinear holomorphic composition acts on the entire germ complex algebra.
True local inverse coordinate identities internally construct an algebra equivalence;
it preserves the actual maximal ideal, every genuine point power and entire original
point quotient. Original translated chart overlap geometry carries ALL original
membership germs to their identical original functions in the other chart.

This gives one intrinsic whole-ideal Hilbert--Samuel point function. The final
coherence-only producer proves each of its finite-value superlevels globally complex
analytic using the actual original Cartan/Macaulay minor equations.
No chart-HS equality, germ algebra equivalence, whole ideal-map equality or analytic
locus certificate is supplied by the final manifold producers. Normal-flat smooth
centres, actual HS transformation, higher-entry descent and general G8 termination
remain subsequent obligations.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaHolomorphicJetChartInvariance
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
open Hironaka
noncomputable section
variable {n : ℕ}

/-- Actual nonlinear original composition preserves true holomorphicity near zero. -/
theorem holomorphic_comp {m n : ℕ} (η : ComplexModel m → ComplexModel n)
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ η z)
    (hη0 : η 0 = 0) {F : ComplexModel n → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ (F ∘ η) z := by
  have ht : Tendsto η (𝓝 0) (𝓝 0) := by
    simpa only [hη0] using hη.self_of_nhds.continuousAt.tendsto
  filter_upwards [hη, ht.eventually hF] with z hz hFz
  exact hFz.comp z hz

/-- The genuine nonlinear composition homomorphism on the entire complex germ algebra. -/
def compAlgHom {m n : ℕ} (η : ComplexModel m → ComplexModel n)
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ η z)
    (hη0 : η 0 = 0) : HolGerm (ComplexModel n) →ₐ[ℂ] HolGerm (ComplexModel m) where
  toFun g := ⟨(g : Germ (𝓝 (0 : ComplexModel n)) ℂ).compTendsto η
    (by simpa only [hη0] using hη.self_of_nhds.continuousAt.tendsto), by
      obtain ⟨_, F, hF, rfl⟩ := g
      exact ⟨F ∘ η, holomorphic_comp η hη hη0 hF, rfl⟩⟩
  map_one' := rfl
  map_mul' g h := by
    induction g using HolGerm.induction_on with
    | h F hF =>
      induction h using HolGerm.induction_on with
      | h G hG => rfl
  map_zero' := rfl
  map_add' g h := by
    induction g using HolGerm.induction_on with
    | h F hF =>
      induction h using HolGerm.induction_on with
      | h G hG => rfl
  commutes' _ := rfl

/-- Whole original holomorphic representatives are carried to their actual original composites. -/
theorem compAlgHom_mk {m n : ℕ} (η : ComplexModel m → ComplexModel n)
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ η z)
    (hη0 : η 0 = 0) (F : ComplexModel n → ℂ)
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z) :
    compAlgHom η hη hη0 (HolGerm.mk F hF) =
      HolGerm.mk (F ∘ η) (holomorphic_comp η hη hη0 hF) := rfl

/-- The actual forward coordinate function is genuinely holomorphic near its original zero centre. -/
theorem local_toFun_holomorphic (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ Φ.toFun z :=
  (show ∀ᶠ z in 𝓝 0, z ∈ Φ.source from Φ.isOpen_source.mem_nhds Φ.center_mem_source).mono
    fun _z hz => Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hz)

/-- The actual inverse coordinate function is genuinely holomorphic near zero. -/
theorem local_invFun_holomorphic (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
    (h0 : Φ.toFun 0 = 0) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ Φ.invFun z := by
  have htar : (0 : ComplexModel n) ∈ Φ.target := by
    simpa only [h0] using Φ.mapsTo_toFun Φ.center_mem_source
  exact (show ∀ᶠ z in 𝓝 0, z ∈ Φ.target from Φ.isOpen_target.mem_nhds htar).mono
    fun _z hz => Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz)

/-- The original inverse identity itself forces the actual inverse coordinate map to fix zero. -/
theorem local_invFun_zero (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
    (h0 : Φ.toFun 0 = 0) : Φ.invFun 0 = 0 := by
  simpa only [h0] using Φ.left_inv 0 Φ.center_mem_source

/-- A genuine original nonlinear local coordinate equivalence internally induces
an isomorphism of the entire holomorphic germ complex algebras. -/
def localGermAlgEquiv (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
    (h0 : Φ.toFun 0 = 0) : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) := by
  let f := compAlgHom Φ.toFun (local_toFun_holomorphic Φ) h0
  let g := compAlgHom Φ.invFun (local_invFun_holomorphic Φ h0) (local_invFun_zero Φ h0)
  apply AlgEquiv.ofAlgHom f g
  · apply AlgHom.ext
    intro a
    induction a using HolGerm.induction_on with
    | h F hF =>
      change f (g (HolGerm.mk F hF)) = HolGerm.mk F hF
      dsimp only [f, g]
      rw [compAlgHom_mk, compAlgHom_mk]
      apply HolGerm.mk_eq_mk_iff.mpr
      filter_upwards [Φ.isOpen_source.mem_nhds Φ.center_mem_source] with z hz
      exact congrArg F (Φ.left_inv z hz)
  · apply AlgHom.ext
    intro a
    induction a using HolGerm.induction_on with
    | h F hF =>
      change g (f (HolGerm.mk F hF)) = HolGerm.mk F hF
      dsimp only [f, g]
      rw [compAlgHom_mk, compAlgHom_mk]
      apply HolGerm.mk_eq_mk_iff.mpr
      have htar : (0 : ComplexModel n) ∈ Φ.target := by
        simpa only [h0] using Φ.mapsTo_toFun Φ.center_mem_source
      filter_upwards [Φ.isOpen_target.mem_nhds htar] with z hz
      exact congrArg F (Φ.right_inv z hz)

/-- The internally constructed algebra isomorphism acts by the actual original nonlinear function. -/
theorem localGermAlgEquiv_mk (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
    (h0 : Φ.toFun 0 = 0) (F : ComplexModel n → ℂ)
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z) :
    localGermAlgEquiv Φ h0 (HolGerm.mk F hF) =
      HolGerm.mk (F ∘ Φ.toFun) (holomorphic_comp Φ.toFun (local_toFun_holomorphic Φ) h0 hF) := rfl

/-- The actual internally constructed nonlinear algebra map preserves every genuine point power. -/
theorem map_maximalIdeal_pow (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
    (h0 : Φ.toFun 0 = 0) (q : ℕ) :
    Ideal.map (localGermAlgEquiv Φ h0).toRingEquiv.toRingHom
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q) =
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
  rw [Ideal.map_pow]
  exact congrArg (fun J : Ideal (HolGerm (ComplexModel n)) => J ^ q)
    (IsLocalRing.map_ringEquiv_maximalIdeal (localGermAlgEquiv Φ h0).toRingEquiv)

/-- Entire actual point quotients, rather than a selected jet subspace, are genuinely equivalent. -/
def quotientAlgEquiv (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
    (h0 : Φ.toFun 0 = 0) (I : Ideal (HolGerm (ComplexModel n))) (q : ℕ) :
    (HolGerm (ComplexModel n) ⧸ (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)) ≃ₐ[ℂ]
      (HolGerm (ComplexModel n) ⧸
        (Ideal.map (localGermAlgEquiv Φ h0).toRingEquiv.toRingHom I ⊔
          IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)) :=
  Ideal.quotientEquivAlg _ _ (localGermAlgEquiv Φ h0) (by
    rw [Ideal.map_sup]
    change Ideal.map (localGermAlgEquiv Φ h0).toRingEquiv.toRingHom I ⊔
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q =
      Ideal.map (localGermAlgEquiv Φ h0).toRingEquiv.toRingHom I ⊔
        Ideal.map (localGermAlgEquiv Φ h0).toRingEquiv.toRingHom
          (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)
    rw [map_maximalIdeal_pow])

/-- Literal whole-ideal Hilbert--Samuel point values are preserved by the actual nonlinear coordinate map. -/
theorem hilbertSamuelValue_map_eq (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
    (h0 : Φ.toFun 0 = 0) (I : Ideal (HolGerm (ComplexModel n))) (ℓ : ℕ) :
    hilbertSamuelValue (Ideal.map (localGermAlgEquiv Φ h0).toRingEquiv.toRingHom I) ℓ =
      hilbertSamuelValue I ℓ :=
  (quotientAlgEquiv Φ h0 I (ℓ + 1)).toLinearEquiv.finrank_eq.symm


section Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
open HolomorphicIdealSheaves

/-- The actual nonlinear transition of two original charts at one common original point,
with both actual coordinates translated to zero and genuine open overlap domains. -/
def translatedChartTransition (x x' y : M)
    (hy : y ∈ (chartAt (ComplexModel n) x).source)
    (hy' : y ∈ (chartAt (ComplexModel n) x').source) :
    LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) := by
  let e := chartAt (ComplexModel n) x
  let e' := chartAt (ComplexModel n) x'
  let S : Set (ComplexModel n) := {z | z + e y ∈ e.target ∧ e.symm (z + e y) ∈ e'.source}
  let T : Set (ComplexModel n) := {w | w + e' y ∈ e'.target ∧ e'.symm (w + e' y) ∈ e.source}
  let η : ComplexModel n → ComplexModel n := fun z => e' (e.symm (z + e y)) - e' y
  let θ : ComplexModel n → ComplexModel n := fun w => e (e'.symm (w + e' y)) - e y
  refine {
    source := S
    target := T
    isOpen_source := (e.isOpen_inter_preimage_symm e'.open_source).preimage
      (continuous_id.add continuous_const)
    isOpen_target := (e'.isOpen_inter_preimage_symm e.open_source).preimage
      (continuous_id.add continuous_const)
    center_mem_source := ?_
    toFun := η
    invFun := θ
    toFun_holomorphic := ?_
    invFun_holomorphic := ?_
    mapsTo_toFun := ?_
    mapsTo_invFun := ?_
    left_inv := ?_
    right_inv := ?_ }
  · change 0 + e y ∈ e.target ∧ e.symm (0 + e y) ∈ e'.source
    simpa only [zero_add, e.left_inv hy] using And.intro (e.map_source hy) hy'
  · intro z hz
    have hχ : DifferentiableAt ℂ (fun w => e' (e.symm w)) (z + e y) :=
      mdifferentiableAt_iff_differentiableAt.mp
        ((HolomorphicBoundedQuotient.mdifferentiableAt_chartAt hz.2).comp _
          (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt_symm hz.1))
    exact ((hχ.comp z (differentiableAt_id.add_const (e y))).sub_const (e' y)).differentiableWithinAt
  · intro w hw
    have hχ : DifferentiableAt ℂ (fun z => e (e'.symm z)) (w + e' y) :=
      mdifferentiableAt_iff_differentiableAt.mp
        ((HolomorphicBoundedQuotient.mdifferentiableAt_chartAt hw.2).comp _
          (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt_symm hw.1))
    exact ((hχ.comp w (differentiableAt_id.add_const (e' y))).sub_const (e y)).differentiableWithinAt
  · intro z hz
    change η z + e' y ∈ e'.target ∧ e'.symm (η z + e' y) ∈ e.source
    dsimp only [η]
    rw [sub_add_cancel]
    exact ⟨e'.map_source hz.2, by rw [e'.left_inv hz.2]; exact e.map_target hz.1⟩
  · intro w hw
    change θ w + e y ∈ e.target ∧ e.symm (θ w + e y) ∈ e'.source
    dsimp only [θ]
    rw [sub_add_cancel]
    exact ⟨e.map_source hw.2, by rw [e.left_inv hw.2]; exact e'.map_target hw.1⟩
  · intro z hz
    change e (e'.symm ((e' (e.symm (z + e y)) - e' y) + e' y)) - e y = z
    rw [sub_add_cancel, e'.left_inv hz.2, e.right_inv hz.1, add_sub_cancel_right]
  · intro w hw
    change e' (e.symm ((e (e'.symm (w + e' y)) - e y) + e y)) - e' y = w
    rw [sub_add_cancel, e.left_inv hw.2, e'.right_inv hw.1, add_sub_cancel_right]

/-- The actual original transition fixes zero by the actual original chart inverse identities. -/
theorem translatedChartTransition_zero (x x' y : M)
    (hy : y ∈ (chartAt (ComplexModel n) x).source)
    (hy' : y ∈ (chartAt (ComplexModel n) x').source) :
    (translatedChartTransition x x' y hy hy').toFun 0 = 0 := by
  change (chartAt (ComplexModel n) x')
    ((chartAt (ComplexModel n) x).symm (0 + (chartAt (ComplexModel n) x) y)) -
      (chartAt (ComplexModel n) x') y = 0
  rw [zero_add, (chartAt (ComplexModel n) x).left_inv hy, sub_self]


/-- Every entire original membership germ is carried to its same original function
in the other actual translated chart, using the genuine inverse identity on its real overlap. -/
theorem chartTranslatedGerm_transition (x x' y : M)
    (hy : y ∈ (chartAt (ComplexModel n) x).source)
    (hy' : y ∈ (chartAt (ComplexModel n) x').source)
    (f : M → ℂ) (hf : HolomorphicAt n f y) :
    localGermAlgEquiv (translatedChartTransition x x' y hy hy')
        (translatedChartTransition_zero x x' y hy hy')
      (chartTranslatedGerm x' y hy' f hf) = chartTranslatedGerm x y hy f hf := by
  simp only [chartTranslatedGerm, translatedGerm]
  rw [localGermAlgEquiv_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  let Φ := translatedChartTransition x x' y hy hy'
  filter_upwards [Φ.isOpen_source.mem_nhds Φ.center_mem_source] with z hz
  have hz' : z + (chartAt (ComplexModel n) x) y ∈ (chartAt (ComplexModel n) x).target ∧
      (chartAt (ComplexModel n) x).symm (z + (chartAt (ComplexModel n) x) y) ∈
        (chartAt (ComplexModel n) x').source := hz
  change f ((chartAt (ComplexModel n) x').symm
    (((chartAt (ComplexModel n) x')
      ((chartAt (ComplexModel n) x).symm (z + (chartAt (ComplexModel n) x) y)) -
        (chartAt (ComplexModel n) x') y) + (chartAt (ComplexModel n) x') y)) = _
  rw [sub_add_cancel, (chartAt (ComplexModel n) x').left_inv hz'.2]

/-- The genuine nonlinear coordinate algebra map preserves the ENTIRE original membership ideal,
formed from all original functions, without a caller supplied ideal-map dictionary. -/
theorem map_wholeChartStalkIdeal (𝔞 : GermIdeal n M) (x x' y : M)
    (hy : y ∈ (chartAt (ComplexModel n) x).source)
    (hy' : y ∈ (chartAt (ComplexModel n) x').source) :
    Ideal.map (localGermAlgEquiv (translatedChartTransition x x' y hy hy')
        (translatedChartTransition_zero x x' y hy hy')).toRingEquiv.toRingHom
      (wholeChartStalkIdeal 𝔞 x' y hy') = wholeChartStalkIdeal 𝔞 x y hy := by
  simp only [wholeChartStalkIdeal, Ideal.map_span]
  congr 1
  ext a
  constructor
  · rintro ⟨_, ⟨f, hf, hmem, rfl⟩, rfl⟩
    exact ⟨f, hf, hmem, chartTranslatedGerm_transition x x' y hy hy' f hf⟩
  · rintro ⟨f, hf, hmem, rfl⟩
    exact ⟨chartTranslatedGerm x' y hy' f hf, ⟨f, hf, hmem, rfl⟩,
      chartTranslatedGerm_transition x x' y hy hy' f hf⟩

/-- The single actual Hilbert--Samuel point function of the ENTIRE original stalk ideal. -/
def hilbertSamuelAt (𝔞 : GermIdeal n M) (y : M) (ℓ : ℕ) : ℕ :=
  hilbertSamuelValue (wholeChartStalkIdeal 𝔞 y y (mem_chart_source (ComplexModel n) y)) ℓ

/-- The same intrinsic whole-ideal point function is computed in any actual original chart,
by an internally constructed nonlinear entire germ algebra isomorphism. -/
theorem hilbertSamuelAt_eq_fixedChart (𝔞 : GermIdeal n M) (x y : M)
    (hy : y ∈ (chartAt (ComplexModel n) x).source) (ℓ : ℕ) :
    hilbertSamuelAt 𝔞 y ℓ = hilbertSamuelValue (wholeChartStalkIdeal 𝔞 x y hy) ℓ := by
  let hy' := mem_chart_source (ComplexModel n) y
  have hEq := hilbertSamuelValue_map_eq (translatedChartTransition x y y hy hy')
    (translatedChartTransition_zero x y y hy hy') (wholeChartStalkIdeal 𝔞 y y hy') ℓ
  rw [map_wholeChartStalkIdeal] at hEq
  exact hEq.symm

/-- Every actual finite-value superlevel of the SAME intrinsic entire coherent stalk
Hilbert--Samuel point function is a genuine global complex analytic subset. -/
theorem isComplexAnalyticSubset_hilbertSamuelAt_superlevel (𝔞 : GermIdeal n M)
    (h𝔞 : 𝔞.IsCoherent) (ℓ r : ℕ) :
    IsComplexAnalyticSubset (n := n) {y | r ≤ hilbertSamuelAt 𝔞 y ℓ} := by
  intro x
  obtain ⟨U, hU, hx, hsource, N, F, hF, hEq⟩ :=
    exists_coherent_whole_stalk_superlevel_equations 𝔞 h𝔞 x ℓ r
  let e := chartAt (ComplexModel n) x
  let V := e.target ∩ e.symm ⁻¹' U
  refine ⟨{
    generatorCount := N
    generator := F
    coordinateNeighborhood := V
    isOpen_coordinateNeighborhood := e.isOpen_inter_preimage_symm hU
    center_mem_coordinateNeighborhood := ?_
    coordinateNeighborhood_subset_target := inter_subset_left
    generator_holomorphic := hF
    zeroLocus := ?_ }⟩
  · refine ⟨e.map_source (mem_chart_source (ComplexModel n) x), ?_⟩
    change e.symm (e x) ∈ U
    simpa only [e.left_inv (mem_chart_source (ComplexModel n) x)] using hx
  · intro y hy hyV
    have hyU : y ∈ U := by
      have hh := hyV.2
      change e.symm (e y) ∈ U at hh
      simpa only [e.left_inv hy] using hh
    change r ≤ hilbertSamuelAt 𝔞 y ℓ ↔ _
    rw [hilbertSamuelAt_eq_fixedChart 𝔞 x y hy ℓ]
    exact hEq y hyU

end Manifold
end
end Hironaka.HironakaHolomorphicJetChartInvariance
