import Hironaka.Resolution.HironakaG1UniformVertexReduction
import Hironaka.Resolution.HironakaActualCoherentWeightedCoefficientMarked
import Hironaka.Resolution.HironakaActualPowerBoundaryExponents
import Hironaka.Resolution.HironakaG8LocalStable
import Hironaka.Resolution.HironakaSmoothSubmersionCoefficientIdeals
import Hironaka.MarkedIdeal.DerivativeIdealTower

/-! The common marked threshold furnished by a two-generator compression
reduction identity, including along an actual proper carrier. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1TwoVertexWeakClass

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealOrder IdealWeightPowers IdealOrderArithmetic
  HironakaActualPowerBoundaryExponents BlowupTowers

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A compression reduction (JI=I^3), with (Jsubseteq I^2), gives the
same normalized order threshold on a closed source submanifold. -/
theorem cosupport_eq_of_quadratic_reduction {N : Set M} (hN : IsClosedSubmanifold n N)
    {I J : GermIdeal n M} (hI : I.IsCoherent)
    (hsub : J.Le (idealPow I 2)) (hprod : J.mul I = idealPow I 3) (d : ℕ) :
    cosupport n N J (2 * d) = cosupport n N I d := by
  have hOne := FactorizationFromResolution.idealPow_one_of_isCoherent hI
  exact HironakaG1UniformVertexReduction.cosupport_eq_of_power_reduction hN hI
    (e := 2) (r := 1) (by decide) hsub (by rw [hOne]; exact hprod) d

/-- Two square compressions with the same reduction ideal have identical
marked centre conditions on the same carrier and with the same ordered boundary. -/
theorem admissibleCentre_iff_of_common_quadratic_reduction
    {N : Set M} (hN : IsClosedSubmanifold n N) (E : List (Set M))
    {I J K : GermIdeal n M} (hI : I.IsCoherent)
    (hJs : J.Le (idealPow I 2)) (hJp : J.mul I = idealPow I 3)
    (hKs : K.Le (idealPow I 2)) (hKp : K.mul I = idealPow I 3)
    (d : ℕ) (C : Set M) :
    (⟨N, E, J, 2 * d⟩ : MarkedIdeals.MarkedIdeal n M).IsAdmissibleCentre C ↔
      (⟨N, E, K, 2 * d⟩ : MarkedIdeals.MarkedIdeal n M).IsAdmissibleCentre C := by
  have hJ := cosupport_eq_of_quadratic_reduction hN hI hJs hJp d
  have hK := cosupport_eq_of_quadratic_reduction hN hI hKs hKp d
  change (IsClosedSubmanifold n C ∧ C ⊆ cosupport n N J (2 * d) ∧ _) ↔
    (IsClosedSubmanifold n C ∧ C ⊆ cosupport n N K (2 * d) ∧ _)
  rw [hJ, hK]


section Ambient
open scoped ProductComplexManifold

open MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealOperationsTransform.MarkedIdeal HironakaG8LocalHistory HironakaG8LocalStable
  HironakaActualProjectionTestRecord GermIdealPullbackCalculus BlowupControlledTransform
  MarkedIdealOperationsTransform HadamardBridge

/-- A coherent quadratic reduction with equal ordered boundary on the full
ambient carriers. The first record has twice the source mark. -/
structure AmbientQuadraticReduction {m : ℕ} {X : CMfd.{0} m} (P Q : MarkedIdeal m X) : Prop where
  leftCarrier : P.N = univ
  rightCarrier : Q.N = univ
  boundary : Q.E = P.E
  mark : P.d = 2 * Q.d
  leftCoherent : P.ideal.IsCoherent
  rightCoherent : Q.ideal.IsCoherent
  inclusion : P.ideal.Le (idealPow Q.ideal 2)
  product : P.ideal.mul Q.ideal = idealPow Q.ideal 3

private theorem AmbientQuadraticReduction.cosupp_eq {m : ℕ} {X : CMfd.{0} m}
    {P Q : MarkedIdeal m X} (h : AmbientQuadraticReduction P Q) : P.cosupp = Q.cosupp := by
  change cosupport m P.N P.ideal P.d = cosupport m Q.N Q.ideal Q.d
  rw [h.leftCarrier, h.rightCarrier, h.mark]
  exact cosupport_eq_of_quadratic_reduction
    (HomogenizedGlueingTower.isClosedSubmanifold_univ (n := m) (M := X))
    h.rightCoherent h.inclusion h.product Q.d

private theorem AmbientQuadraticReduction.pullback {m r : ℕ} {X : CMfd.{0} m} {Y : CMfd.{0} r}
    {P Q : MarkedIdeal m X} (h : AmbientQuadraticReduction P Q)
    {φ : Y → X} (hφ : ContMDiff 𝓘(ℂ, ComplexModel r) 𝓘(ℂ, ComplexModel m) ∞ φ)
    (E : List (Set Y)) :
    AmbientQuadraticReduction
      ⟨univ, E, GermIdeal.pullback (m := r) φ P.ideal, P.d⟩
      ⟨univ, E, GermIdeal.pullback (m := r) φ Q.ideal, Q.d⟩ := by
  refine ⟨rfl, rfl, rfl, h.mark, isCoherent_pullback hφ h.leftCoherent,
    isCoherent_pullback hφ h.rightCoherent, ?_, ?_⟩
  · rw [← HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hφ h.rightCoherent]
    exact pullback_le_pullback h.inclusion
  · rw [← HironakaSmoothSubmersionCoefficientIdeals.pullback_mul hφ h.leftCoherent h.rightCoherent,
      h.product, HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hφ h.rightCoherent]

/-- The exact quadratic reduction identity is stable under all ordinary
local weak projection tests on full ambient carriers. -/
theorem isLocStable_ambientQuadraticReduction : IsLocStable.{0} Kinds.wp
    (fun {m} {X} P Q => AmbientQuadraticReduction (m := m) (X := X) P Q) where
  E_eq h := h.boundary
  cosupp_eq h := h.cosupp_eq
  controlled := by
    intro m X P Q h C Z π hπ hCP
    have hCQ : Q.IsAdmissibleCentre C :=
      (HironakaG8MixedEquiv.isAdmissibleCentre_congr h.boundary.symm h.cosupp_eq C).mp hCP
    have hLP := ideal_le_idealPow_of_isAdmissibleCentre h.leftCarrier h.leftCoherent hCP
    have hLQ := ideal_le_idealPow_of_isAdmissibleCentre h.rightCarrier h.rightCoherent hCQ
    have hPI := geoTransform_ideal_eq_controlledTransform h.leftCarrier h.leftCoherent hπ
    have hQI := geoTransform_ideal_eq_controlledTransform h.rightCarrier h.rightCoherent hπ
    refine ⟨geoTransform_N_eq_univ h.leftCarrier hπ, geoTransform_N_eq_univ h.rightCarrier hπ,
      by simp only [geoTransform_E, h.boundary], h.mark, ?_, ?_, ?_, ?_⟩
    · rw [hPI]
      exact isCoherent_controlledTransform hπ h.leftCoherent hLP
    · rw [hQI]
      exact isCoherent_controlledTransform hπ h.rightCoherent hLQ
    · rw [hPI, hQI, ← controlledTransform_idealPow hπ h.rightCoherent hLQ 2, h.mark, Nat.mul_comm 2]
      exact DerivativeIdealTower.controlledTransform_le_of_le hπ h.inclusion _
    · rw [hPI, hQI, ← controlledTransform_mul hπ h.leftCoherent h.rightCoherent hLP hLQ,
        h.product, ← controlledTransform_idealPow hπ h.rightCoherent hLQ 3, h.mark]
      congr 1
      omega
  projection := by
    intro _ m X P Q h
    have hf := ProductComplexManifold.contMDiff_fst (n := m) (m := 1)
      (X := X) (Y := ComplexModel 1)
    have ht := h.pullback (Y := projectionAmbient X) hf (projectionTest P).E
    have hE : (projectionTest Q).E = (projectionTest P).E := by
      simp only [projectionTest, h.boundary]
    have hP : (projectionTest P).N = univ := by
      change Prod.fst ⁻¹' P.N = _
      rw [h.leftCarrier, preimage_univ]
    have hQ : (projectionTest Q).N = univ := by
      change Prod.fst ⁻¹' Q.N = _
      rw [h.rightCarrier, preimage_univ]
    have hrecP : projectionTest P = ⟨univ, (projectionTest P).E, _, P.d⟩ :=
      MarkedIdealOperationsTransform.MarkedIdeal.ext_of hP rfl rfl rfl
    have hrecQ : projectionTest Q = ⟨univ, (projectionTest P).E, _, Q.d⟩ :=
      MarkedIdealOperationsTransform.MarkedIdeal.ext_of hQ hE rfl rfl
    rw [hrecP, hrecQ]
    exact ht
  restrict := by
    intro m X P Q h U
    let φ : U → X := Subtype.val
    have ht := h.pullback (Y := CMfd.of (n := m) U) (φ := φ) contMDiff_subtype_val (P.E.map (φ ⁻¹' ·))
    have hrecP : MarkedIdeal.pullback φ P = ⟨univ, P.E.map (φ ⁻¹' ·), _, P.d⟩ :=
      MarkedIdealOperationsTransform.MarkedIdeal.ext_of (by simp [MarkedIdeal.pullback, h.leftCarrier])
        rfl rfl rfl
    have hrecQ : MarkedIdeal.pullback φ Q = ⟨univ, P.E.map (φ ⁻¹' ·), _, Q.d⟩ :=
      MarkedIdealOperationsTransform.MarkedIdeal.ext_of (by simp [MarkedIdeal.pullback, h.rightCarrier])
        (by simp [MarkedIdeal.pullback, h.boundary]) rfl rfl
    rw [hrecP, hrecQ]
    exact ht

/-- A quadratic compression and its source have the same weak projection
test class, including all stage cosupports on their whole ambient carriers. -/
theorem locWPEquiv_of_ambientQuadraticReduction {m : ℕ} {X : CMfd.{0} m}
    {P Q : MarkedIdeal m X} (h : AmbientQuadraticReduction P Q) : LocWPEquiv P Q :=
  LocEquiv.of_isLocStable isLocStable_ambientQuadraticReduction rfl h


open HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression IdealWeightProducts

private theorem finiteFunctionIdeal_mulFamily {m a b : ℕ} {X : CMfd.{0} m}
    (c : Fin a → X → ℂ) (d : Fin b → X → ℂ)
    (hc : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) (c i))
    (hd : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) (d i)) :
    (finiteFunctionIdeal (n := m) c).mul (finiteFunctionIdeal d) =
      finiteFunctionIdeal (mulFamily c d) := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ?_)
  exact mem_mul_iff_isInSpanAt_mulFamily isOpen_univ
    (fun i => (hc i).mdifferentiableOn) (fun i => (hd i).mdifferentiableOn)
    (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl) (mem_univ x) g

private theorem holomorphic_mulFamily {m a b : ℕ} {X : CMfd.{0} m}
    {c : Fin a → X → ℂ} {d : Fin b → X → ℂ}
    (hc : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) (c i))
    (hd : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) (d i)) :
    ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) (mulFamily c d i) := by
  intro i
  exact (hc (finProdFinEquiv.symm i).1).mul (hd (finProdFinEquiv.symm i).2)

private theorem range_quadratic_reduction {A : Type*} (c : Fin 2 → A → ℂ) :
    range (mulFamily (fun i x => c i x ^ 2) c) = range (mulFamily (mulFamily c c) c) := by
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    let a := (finProdFinEquiv.symm i).1
    let b := (finProdFinEquiv.symm i).2
    refine ⟨finProdFinEquiv (finProdFinEquiv (a, a), b), ?_⟩
    funext x
    have hi : finProdFinEquiv (a, b) = i := finProdFinEquiv.apply_symm_apply i
    conv_rhs => rw [← hi]
    rw [mulFamily_apply, mulFamily_apply, mulFamily_apply, pow_two]
  · rintro ⟨i, rfl⟩
    let p := (finProdFinEquiv.symm i).1
    let k := (finProdFinEquiv.symm i).2
    let a := (finProdFinEquiv.symm p).1
    let b := (finProdFinEquiv.symm p).2
    have hi : finProdFinEquiv (p, k) = i := finProdFinEquiv.apply_symm_apply i
    have hp : finProdFinEquiv (a, b) = p := finProdFinEquiv.apply_symm_apply p
    have hg (u v : Fin 2) (heq : ∀ x, c u x ^ 2 * c v x = c a x * c b x * c k x) :
        mulFamily (mulFamily c c) c i ∈ range (mulFamily (fun i x => c i x ^ 2) c) := by
      refine ⟨finProdFinEquiv (u, v), ?_⟩
      funext x
      conv_rhs => rw [← hi, ← hp]
      rw [mulFamily_apply, mulFamily_apply, mulFamily_apply]
      exact heq x
    by_cases hab : a = b
    · exact hg a k (fun x => by rw [← hab, pow_two])
    by_cases hak : a = k
    · exact hg a b (fun x => by rw [← hak]; ring)
    have hbk : b = k := by omega
    exact hg b a (fun x => by rw [← hbk]; ring)

/-- The exact quadratic reduction holds for the whole coherent ideals
generated by two holomorphic functions and their squares. -/
theorem quadratic_reduction_of_two_functions {m : ℕ} {X : CMfd.{0} m}
    (c : Fin 2 → X → ℂ) (hc : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) (c i)) :
    let I := finiteFunctionIdeal (n := m) c
    let J := weightedFunctionIdeal (n := m) (fun _ => 2) c
    J.Le (idealPow I 2) ∧ J.mul I = idealPow I 3 := by
  let sq : Fin 2 → X → ℂ := fun i x => c i x ^ 2
  have hs (i : Fin 2) := (hc i).pow 2
  have hI := isCoherent_finiteFunctionIdeal (n := m) c hc
  have hMark : weightedCommonMark (fun _ : Fin 2 => 2) = 4 := by
    norm_num [weightedCommonMark, Fin.prod_univ_two]
  dsimp only [weightedFunctionIdeal]
  rw [hMark]
  change (finiteFunctionIdeal (n := m) sq).Le (idealPow (finiteFunctionIdeal c) 2) ∧
    (finiteFunctionIdeal sq).mul (finiteFunctionIdeal c) = idealPow (finiteFunctionIdeal c) 3
  have hOne := FactorizationFromResolution.idealPow_one_of_isCoherent hI
  have hTwo : idealPow (finiteFunctionIdeal (n := m) c) 2 =
      finiteFunctionIdeal (mulFamily c c) := by
    change (idealPow (finiteFunctionIdeal (n := m) c) 1).mul (finiteFunctionIdeal c) = _
    rw [hOne, finiteFunctionIdeal_mulFamily c c hc hc]
  refine ⟨?_, ?_⟩
  · rw [hTwo]
    intro x f hf
    apply IsInSpanAt.mono ?_ hf
    rintro _ ⟨i, rfl⟩
    exact ⟨finProdFinEquiv (i, i), funext fun x => by rw [mulFamily_apply]; simp only [sq, pow_two]⟩
  · change _ = (idealPow (finiteFunctionIdeal (n := m) c) 2).mul (finiteFunctionIdeal c)
    rw [hTwo,
      finiteFunctionIdeal_mulFamily sq c hs hc,
      finiteFunctionIdeal_mulFamily (mulFamily c c) c (holomorphic_mulFamily hc hc) hc]
    exact GermIdeal.ext (funext fun x => funext fun f => propext (by
      change IsInSpanAt (· ∈ range (mulFamily sq c)) x f ↔
        IsInSpanAt (· ∈ range (mulFamily (mulFamily c c) c)) x f
      rw [range_quadratic_reduction c]))

/-- Two actual holomorphic generator pairs with the same whole source ideal
give the same weak projection test class at their literal common mark four. -/
theorem locWPEquiv_two_weight_two_functions {m : ℕ} {X : CMfd.{0} m}
    (c d : Fin 2 → X → ℂ)
    (hc : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) (c i))
    (hd : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) (d i))
    (hSpan : finiteFunctionIdeal (n := m) c = finiteFunctionIdeal d)
    (E : List (Set X)) :
    LocWPEquiv (X := X) ⟨univ, E, weightedFunctionIdeal (fun _ => 2) c, 4⟩
      ⟨univ, E, weightedFunctionIdeal (fun _ => 2) d, 4⟩ := by
  have hcR := quadratic_reduction_of_two_functions c hc
  have hdR := quadratic_reduction_of_two_functions d hd
  let Q : MarkedIdeal m X := ⟨univ, E, finiteFunctionIdeal c, 2⟩
  have hQ := isCoherent_finiteFunctionIdeal (n := m) c hc
  have hLc : AmbientQuadraticReduction ⟨univ, E, weightedFunctionIdeal (fun _ => 2) c, 4⟩ Q :=
    ⟨rfl, rfl, rfl, rfl, isCoherent_weightedFunctionIdeal _ c hc, hQ, hcR.1, hcR.2⟩
  rw [← hSpan] at hdR
  have hLd : AmbientQuadraticReduction ⟨univ, E, weightedFunctionIdeal (fun _ => 2) d, 4⟩ Q :=
    ⟨rfl, rfl, rfl, rfl, isCoherent_weightedFunctionIdeal _ d hd, hQ, hdR.1, hdR.2⟩
  exact (locWPEquiv_of_ambientQuadraticReduction hLc).trans
    (locWPEquiv_of_ambientQuadraticReduction hLd).symm

end Ambient

end

end Hironaka.HironakaG1TwoVertexWeakClass
