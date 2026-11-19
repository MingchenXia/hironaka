import Hironaka.Resolution.HironakaG8MarkTwoNormalGeometry
import Hironaka.Resolution.HironakaG8NativeCuspFullTrace
import Hironaka.Resolution.HironakaG8OddCuspPrescribedNative

/-! Exact original initial values of the genuine degree-(1,2)
weighted records for odd embedded cusps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace Filter
open scoped Topology Manifold ContDiff ENat
namespace Hironaka.HironakaG8NativeCuspOriginalValue
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres InvDomainTowerAlong
  HironakaG8MarkTwoNormalOriginalValue HironakaG8MarkTwoNormalGeometry
  HironakaActualNormalPaddingNativeCompanion HironakaActualWeightedNormalAmbientDerivatives
  HironakaActualOpenZeroSectionDifferentials HironakaActualWeightedNormalPadding
  HironakaActualRelativeNormalGeometry HironakaActualZeroCoordinateContactSeed
  HironakaActualWeightedCoefficientCompression HironakaActualCoherentWeightedCoefficientMarked
  HironakaG8InitialExactContactValue HironakaG8NativeCuspFullTrace HironakaG8CuspDerivativeTrace
  HironakaActualFiniteCoefficientIdeals HironakaG8OddCuspPrescribedNative
  HironakaG8OddCuspPrescribedFamily HironakaG8OddCuspVanishingStalk
  HironakaRelativeNormalMonomialBasis HironakaG8NativeCuspDiagram
  HomogenizedGlueingTower AnalyticIrreducibleComponents NormalCrossings
  InvertibleIdealQuotient RelativePrincipalizationSpan HironakaSmoothSubmersionGermIdealColon

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev Z : CMfd.{0} 2 := CMfd.of (n := 2) (ComplexModel 2)
private abbrev X : CMfd.{0} 3 := CMfd.of (n := 3) (productOpen U)
private abbrev x : U := ⟨0,trivial⟩
private abbrev M (p : ℕ) : MarkedIdeal 2 Z := ⟨univ,[],cuspIdeal p,2⟩

private theorem differentiable_cusp (p : ℕ) : Differentiable ℂ (cuspFunction p) :=
  ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).differentiable.pow 2).sub
    ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).differentiable.pow p)

private theorem plane_domain (p : ℕ) (hp : 2 ≤ p) : IsInvDomain 2 (M p) := by
  refine ⟨⟨isClosedSubmanifold_univ,cuspIdeal_coherent p,
    isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold isClosedSubmanifold_univ⟩,
    fun z _ => ⟨2,le_rfl,regularAtDim_univ z⟩,by change 1 ≤ 2; decide,?_⟩
  intro z _
  have hc : HolomorphicAt 2 (cuspFunction p) z :=
    holomorphicAt_of_mdifferentiableOn isOpen_univ (differentiable_cusp p).mdifferentiable.mdifferentiableOn
      (mem_univ _)
  refine ⟨cuspFunction p,?_,?_⟩
  · change IsInSpanAt (fun g => g = cuspFunction p) z (cuspFunction p)
    exact isInSpanAt_self rfl hc
  · apply Frequently.mono (p := fun y => cuspFunction p y ≠ 0) _ (fun y hy => ⟨mem_univ y,hy⟩)
    by_contra hn
    have hEq : cuspFunction p =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
      change ∀ᶠ y in 𝓝 z, cuspFunction p y = 0
      simpa using hn
    have hAnal : AnalyticOnNhd ℂ (cuspFunction p) univ := by
      intro y _
      exact (((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).analyticAt y |>.pow 2).sub
        ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).analyticAt y |>.pow p))
    have hAll := hAnal.eq_of_eventuallyEq analyticOnNhd_const hEq
    have hP := congrFun hAll (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))
    have hp0 : p ≠ 0 := by omega
    simp [cuspFunction,zero_pow hp0] at hP

private theorem cuspFunction_finite_ideal (p : ℕ) :
    finiteFunctionIdeal (n := 2) (fun _ : Unit => cuspFunction p) = cuspIdeal p := by
  apply GermIdeal.ext
  funext z f
  apply propext
  change IsInSpanAt (fun g => ∃ _ : Unit, cuspFunction p = g) z f ↔
    IsInSpanAt (· = cuspFunction p) z f
  exact ⟨fun h => h.mono (by rintro _ ⟨_,rfl⟩; rfl),
    fun h => h.mono (by rintro _ rfl; exact ⟨(),rfl⟩)⟩

private abbrev Q (p : ℕ) : MarkedIdeal 2 U := MarkedIdeal.pullback (Subtype.val : U → ComplexModel 2) (M p)

private theorem base_order_record (p : ℕ) :
    Q p = (⟨univ,[],finiteFunctionIdeal (fun _ : Unit => fun z : U => cuspFunction p z.val),2⟩ :
      MarkedIdeal 2 U) := by
  have h := finiteFunctionIdeal_pullback (n := 2) (fun _ : Unit => cuspFunction p)
    (fun _ => (differentiable_cusp p).mdifferentiable)
    (Subtype.val : U → ComplexModel 2) contMDiff_subtype_val
  rw [cuspFunction_finite_ideal] at h
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of preimage_univ rfl h rfl

private theorem weighted_eq_normal (p : ℕ) : nativeWeightedCusp p = normalMarked (Q p) := by
  let w : Unit → ℕ := fun _ => 2
  let c : Unit → U → ℂ := fun _ z => cuspFunction p z.val
  have hw : weightedCommonMark w = 2 := by decide
  have hI : weightedFunctionIdeal (n := 2) w c = finiteFunctionIdeal c := by
    unfold weightedFunctionIdeal
    rw [hw]
    simp [w]
  have hf : ∀ i, MDifferentiable 𝓘(ℂ,ComplexModel 2) 𝓘(ℂ,ℂ) (c i) :=
    fun _ => (differentiable_cusp p).mdifferentiable.comp
      ((contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiable (by simp))
  change paddingMarked U w c [] = normalMarked (Q p)
  rw [entire_padding_record U w c hf, hw,hI,base_order_record]
  rfl

/-- Exact initial canonical value on the literal native weighted normal
padding. The two recursive coefficient operations retain the raw cusp class. -/
theorem native_weighted_cusp_original_initial_formula (p : ℕ) (hp : 2 ≤ p) :
    (canonicalInvariant 3).inv (X := X) (nativeWeightedCusp p) .refl (zeroSection U x) =
      initialContactValue 2 2 ((canonicalInvariant 2).inv (X := Z) (M p) .refl 0) := by
  have hM := plane_domain p hp
  have hC : (0 : Z) ∈ (M p).cosupp := by
    change (0 : ComplexModel 2) ∈ GermIdealOrder.cosupport 2 univ (cuspIdeal p) 2
    rw [cusp_cosupport_two p hp]
    simp
  have hQ : IsInvDomain 2 (Q p) := isInvDomain_pullback_val U hM
  have hx : x ∈ (Q p).cosupp := by
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val _ (fun _ _ hg =>
      GermIdeal.IsCoherent.holomorphicAt_mem (cuspIdeal_coherent p) hg)]
    exact hC
  have hV := (canonicalInvariant 2).isInvValue.restrictOpen (X := Z) (M p) hM U
    (.refl : BlowupTower Z Z) trivial x hC
  rw [weighted_eq_normal,mark_two_normal_original_initial_value_full (by decide : 0 < 2)
    (Q p) hQ rfl preimage_univ rfl x hx]
  exact congrArg (initialContactValue 2 2) hV

/-- Genuine original values strictly distinguish the native weighted cubic
and quintic cusps. -/
theorem native_weighted_cubic_lt_quintic_original_initial :
    (canonicalInvariant 3).inv (X := X) (nativeWeightedCusp 3) .refl (zeroSection U x) <
      (canonicalInvariant 3).inv (X := X) (nativeWeightedCusp 5) .refl (zeroSection U x) := by
  rw [native_weighted_cusp_original_initial_formula 3 (by decide),
    native_weighted_cusp_original_initial_formula 5 (by decide)]
  apply initialContactValue_strictMono
  exact cusp_original_initial_value_lt 3 5 (by decide) (by decide)


private theorem cuspPowerRange (p : ℕ) (hp : 2 < p) {Y : Type}
    (f : Y → ComplexModel 3) :
    range (fun (a : cuspV p) (z : Y) => cuspRepresentative p a (f z) ^
      (weightedCommonMark (fun b : cuspV p => normalExponentDegree b.val) / normalExponentDegree a.val)) =
      {embeddedCuspEquations p 0 ∘ f, fun z => embeddedCuspEquations p 1 (f z)^2} := by
  rw [embedded_cusp_native_mark p hp]
  have hne : zExp ≠ yExp := by
    intro h
    have he := congrArg (fun a : Fin 3 →₀ ℕ => a 1) h
    simp at he
  have hFirst (a : cuspV p) (ha : a.val = yExp) :
      (fun z => cuspRepresentative p a (f z) ^ (2 / normalExponentDegree a.val)) =
        embeddedCuspEquations p 0 ∘ f := by
    funext z
    simp [cuspRepresentative,ha,normalExponentDegree,Finsupp.single_apply]
  have hSecond (a : cuspV p) (ha : a.val = zExp) :
      (fun z => cuspRepresentative p a (f z) ^ (2 / normalExponentDegree a.val)) =
        (fun z => embeddedCuspEquations p 1 (f z)^2) := by
    funext z
    simp [cuspRepresentative,ha,hne,normalExponentDegree,Finsupp.single_apply]
  apply Set.ext
  intro g
  constructor
  · rintro ⟨a,rfl⟩
    rcases cuspV_cases hp a with h | h
    · exact Or.inl (hFirst a h)
    · exact Or.inr (hSecond a h)
  · simp only [mem_insert_iff,mem_singleton_iff]
    rintro (rfl | rfl)
    · let a : cuspV p := ⟨yExp,by simp [cuspV_eq p hp]⟩
      exact ⟨a,hFirst a rfl⟩
    · let a : cuspV p := ⟨zExp,by simp [cuspV_eq p hp]⟩
      exact ⟨a,hSecond a rfl⟩

/-- The prescribed historical polynomial record and the normal padding
are literally the same entire marked record on the product open. -/
theorem polynomialCuspRecord_eq_nativeWeightedCusp (p : ℕ) (hp : 2 < p) :
    polynomialCuspRecord p (Subtype.val : productOpen U → ComplexModel 3) = nativeWeightedCusp p := by
  let w : Unit → ℕ := fun _ => 2
  let c : Unit → U → ℂ := fun _ z => cuspFunction p z.val
  have hw : weightedCommonMark (paddingWeight w) = 2 := by
    rw [padding_common_mark]
    decide
  change polynomialCuspRecord p (Subtype.val : productOpen U → ComplexModel 3) =
    paddingMarked U w c []
  unfold polynomialCuspRecord paddingMarked
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ hw.symm
  apply GermIdeal.ext
  funext z g
  apply propext
  let f := (Subtype.val : productOpen U → ComplexModel 3)
  change IsInSpanAt (range (fun (a : cuspV p) (y : productOpen U) =>
      cuspRepresentative p a (f y) ^ (weightedCommonMark (fun b : cuspV p =>
        normalExponentDegree b.val) / normalExponentDegree a.val))) z g ↔
    IsInSpanAt (range (fun i y => paddingFunction U c i y ^
      (weightedCommonMark (paddingWeight w) / paddingWeight w i))) z g
  rw [cuspPowerRange p hp f,hw]
  have hf : (fun y : productOpen U => c () (projection U y)) = embeddedCuspEquations p 0 ∘ f := by
    funext y
    rfl
  have hz : relativeNormalCoordinate U = embeddedCuspEquations p 1 ∘ f := by
    funext y
    change addedCoordinate 2 y.val = y.val.ofLp 2
    simp [addedCoordinate,HironakaActualGraphFunctionalIdeal.graphFunction,zeroFunction]
  have hRange :
      range (fun i y => paddingFunction U c i y ^ (2 / paddingWeight w i)) =
      {embeddedCuspEquations p 0 ∘ f, fun y => embeddedCuspEquations p 1 (f y)^2} := by
    apply Set.ext
    intro g
    constructor
    · rintro ⟨a,rfl⟩
      cases a with
      | inl i =>
        cases i
        exact Or.inl (by simpa [paddingFunction,paddingWeight,w] using hf)
      | inr i =>
        exact Or.inr (by simp [paddingFunction,paddingWeight,hz,Function.comp_def])
    · simp only [mem_insert_iff,mem_singleton_iff]
      rintro (rfl | rfl)
      · exact ⟨Sum.inl (),by simpa [paddingFunction,paddingWeight,w] using hf⟩
      · exact ⟨Sum.inr (),by simp [paddingFunction,paddingWeight,hz,Function.comp_def]⟩
  rw [hRange]


open BlowupTowerIsomorphism

private abbrev Z3 : CMfd.{0} 3 := CMfd.of (n := 3) (ComplexModel 3)

private def globalToProduct :
    Z3 ≃ₘ⟮𝓘(ℂ,ComplexModel 3),𝓘(ℂ,ComplexModel 3)⟯ X where
  toFun := fun z => ⟨z,trivial⟩
  invFun := Subtype.val
  left_inv := fun _ => rfl
  right_inv := fun _ => Subtype.ext rfl
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff (productOpen U) _).mp contMDiff_id
  contMDiff_invFun := contMDiff_subtype_val

private theorem polynomial_cusp_record_pullback
    {A B : CMfd.{0} 3} (p : ℕ) (g : B → ComplexModel 3) (f : A → B)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ComplexModel 3) ∞ g)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ComplexModel 3) ∞ f) :
    MarkedIdeal.pullback f (polynomialCuspRecord p g) =
      polynomialCuspRecord p (g ∘ f) := by
  let μ := fun a : cuspV p => normalExponentDegree a.val
  let c := fun (a : cuspV p) (z : B) =>
    cuspRepresentative p a (g z) ^ (weightedCommonMark μ / μ a)
  have hc (a : cuspV p) : MDifferentiable 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ℂ) (c a) :=
    ((cuspRepresentative_differentiable p a).mdifferentiable.comp
      (hg.mdifferentiable (by simp))).pow _
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of preimage_univ rfl
    (finiteFunctionIdeal_pullback c hc f hf) rfl

/-- Every physical polynomial cusp restriction keeps the exact initial
value computed by the mark-two normal-contact formula. -/
theorem physical_polynomial_cusp_original_initial_value (p : ℕ) (hp : 2 < p)
    (D : Opens (ComplexModel 3)) (hD : (0 : ComplexModel 3) ∈ D) :
    (canonicalInvariant 3).inv (X := CMfd.of (n := 3) D)
      (polynomialCuspRecord p (Subtype.val : D → ComplexModel 3)) .refl ⟨0,hD⟩ =
      initialContactValue 2 2 ((canonicalInvariant 2).inv (X := Z) (M p) .refl 0) := by
  let P := (nativeWeightedCusp p : MarkedIdeal 3 X)
  let G := polynomialCuspRecord p (id : Z3 → ComplexModel 3)
  have hQ : IsInvDomain 2 (Q p) := isInvDomain_pullback_val U (plane_domain p hp.le)
  have hP : IsInvDomain 3 P := by
    change IsInvDomain 3 (nativeWeightedCusp p)
    rw [weighted_eq_normal]
    exact normalMarked_original_domain (Q p) hQ preimage_univ
  have hFull : MarkedIdeal.pullback globalToProduct P = G := by
    change MarkedIdeal.pullback globalToProduct (nativeWeightedCusp p) = _
    rw [← polynomialCuspRecord_eq_nativeWeightedCusp p hp,
      polynomial_cusp_record_pullback (A := Z3) (B := X) p _ _
        contMDiff_subtype_val globalToProduct.contMDiff]
    rfl
  have hG : IsInvDomain 3 G := hFull ▸ isInvDomain_pullback globalToProduct hP
  have hQzero : x ∈ (Q p).cosupp := by
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val _ (fun _ _ hg =>
      GermIdeal.IsCoherent.holomorphicAt_mem (cuspIdeal_coherent p) hg)]
    change (0 : ComplexModel 2) ∈ GermIdealOrder.cosupport 2 univ (cuspIdeal p) 2
    rw [cusp_cosupport_two p hp.le]
    simp
  have hPzero : zeroSection U x ∈ P.cosupp := by
    change zeroSection U x ∈ (nativeWeightedCusp p).cosupp
    rw [weighted_eq_normal,mark_two_normal_cosupport (Q p) hQ preimage_univ rfl]
    refine ⟨?_,by ext j; exact HironakaRelativeNormalIdeal.tangentInclusion_normal 2 1 (0 : ComplexModel 2) j⟩
    have hpr : projection U (zeroSection U x) = x := Subtype.ext
      (HironakaRelativeNormalIdeal.tangentProjection_tangentInclusion 2 1 x.val)
    rwa [hpr]
  have he : globalToProduct (0 : Z3) = zeroSection U x := by
    apply Subtype.ext
    change (0 : ComplexModel 3) = HironakaRelativeNormalIdeal.tangentInclusion 2 1 0
    rw [map_zero]
  have hGzero : (0 : Z3) ∈ G.cosupp := by
    rw [← hFull, MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback
      globalToProduct.contMDiff globalToProduct.symm.contMDiff globalToProduct.apply_symm_apply
      globalToProduct.symm_apply_apply P
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP.isWellFormed.isCoherent hg)]
    change globalToProduct (0 : Z3) ∈ P.cosupp
    rwa [he]
  have hIso := (canonicalInvariant 3).isInvValue.towerIso (X := X) (X' := Z3)
    globalToProduct P hP .refl .refl globalToProduct (.refl) trivial 0 (by rw [he]; exact hPzero)
  rw [hFull,he] at hIso
  have hOpen := (canonicalInvariant 3).isInvValue.restrictOpen (X := Z3) G hG D
    (.refl : BlowupTower Z3 Z3) trivial ⟨0,hD⟩ hGzero
  rw [polynomial_cusp_record_pullback (A := CMfd.of (n := 3) D) (B := Z3) p _ _
    contMDiff_id contMDiff_subtype_val] at hOpen
  exact hOpen.trans (hIso.trans (native_weighted_cusp_original_initial_formula p hp.le))


open HironakaActualIntrinsicStableAmbientIso HironakaRelativeNormalIdeal

/-- Each individual polynomial history has exactly its origin as the
retained local cosupport. -/
theorem physical_polynomial_cusp_cosupport (p : ℕ) (hp : 2 < p)
    (D : Opens (ComplexModel 3)) (hD : (0 : ComplexModel 3) ∈ D) :
    (polynomialCuspRecord p (Subtype.val : D → ComplexModel 3)).cosupp = {⟨0,hD⟩} := by
  let P := (nativeWeightedCusp p : MarkedIdeal 3 X)
  let G := polynomialCuspRecord p (id : Z3 → ComplexModel 3)
  have hQ : IsInvDomain 2 (Q p) := isInvDomain_pullback_val U (plane_domain p hp.le)
  have hP : IsInvDomain 3 P := by
    change IsInvDomain 3 (nativeWeightedCusp p)
    rw [weighted_eq_normal]
    exact normalMarked_original_domain (Q p) hQ preimage_univ
  have hFull : MarkedIdeal.pullback globalToProduct P = G := by
    change MarkedIdeal.pullback globalToProduct (nativeWeightedCusp p) = _
    rw [← polynomialCuspRecord_eq_nativeWeightedCusp p hp,
      polynomial_cusp_record_pullback (A := Z3) (B := X) p _ _
        contMDiff_subtype_val globalToProduct.contMDiff]
    rfl
  have hG : IsInvDomain 3 G := hFull ▸ isInvDomain_pullback globalToProduct hP
  have hQCos : (Q p).cosupp = {x} := by
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val _ (fun _ _ hg =>
      GermIdeal.IsCoherent.holomorphicAt_mem (cuspIdeal_coherent p) hg)]
    change (Subtype.val : U → ComplexModel 2) ⁻¹' GermIdealOrder.cosupport 2 univ (cuspIdeal p) 2 = _
    rw [cusp_cosupport_two p hp.le]
    ext z
    exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
  have hPCos : P.cosupp = {zeroSection U x} := by
    change (nativeWeightedCusp p).cosupp = _
    rw [weighted_eq_normal,mark_two_normal_cosupport (Q p) hQ preimage_univ rfl,hQCos]
    ext z
    constructor
    · intro hz
      have hzProjection : projection U z = x := hz.1
      have hzSection : zeroSection U (projection U z) = z := by
        apply Subtype.ext
        change tangentInclusion 2 1 (tangentProjection 2 1 z.val) = z.val
        have hzN : HironakaActualCentreJointJets.actualJointNormalProjection 2 1 z.val = 0 := hz.2
        simpa only [HironakaActualIntrinsicStableAmbientIso.join,hzN,map_zero,add_zero] using
          join_projections (n := 2) (m := 1) z.val
      rw [hzProjection] at hzSection
      exact hzSection.symm
    · rintro rfl
      refine ⟨?_,by ext j; exact tangentInclusion_normal 2 1 (0 : ComplexModel 2) j⟩
      exact Subtype.ext (tangentProjection_tangentInclusion 2 1 x.val)
  have hGCos : G.cosupp = {(0 : ComplexModel 3)} := by
    rw [← hFull, MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback
      globalToProduct.contMDiff globalToProduct.symm.contMDiff globalToProduct.apply_symm_apply
      globalToProduct.symm_apply_apply P
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP.isWellFormed.isCoherent hg),hPCos]
    have he : globalToProduct (0 : Z3) = zeroSection U x := by
      apply Subtype.ext
      change (0 : ComplexModel 3) = tangentInclusion 2 1 0
      rw [map_zero]
    rw [← he]
    ext z
    exact ⟨fun h => globalToProduct.injective h,fun h => congrArg globalToProduct h⟩
  have hDrec := polynomial_cusp_record_pullback (A := CMfd.of (n := 3) D) (B := Z3) p
    (id : Z3 → ComplexModel 3) (Subtype.val : D → ComplexModel 3) contMDiff_id contMDiff_subtype_val
  change MarkedIdeal.pullback (Subtype.val : D → ComplexModel 3) G =
    polynomialCuspRecord p (Subtype.val : D → ComplexModel 3) at hDrec
  rw [← hDrec, MarkedIdealRestrictOpen.cosupp_pullback_val G (fun _ _ hg =>
    GermIdeal.IsCoherent.holomorphicAt_mem hG.isWellFormed.isCoherent hg), hGCos]
  ext z
  exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩


/-- On the disjoint collection of the two actual local cosupports, only
the quintic origin attains the original simultaneous maximum. -/
theorem physical_cubic_quintic_simultaneous_max_is_quintic
    (D₃ D₅ : Opens (ComplexModel 3))
    (h₃ : (0 : ComplexModel 3) ∈ D₃) (h₅ : (0 : ComplexModel 3) ∈ D₅) :
    let P₃ := polynomialCuspRecord 3 (Subtype.val : D₃ → ComplexModel 3)
    let P₅ := polynomialCuspRecord 5 (Subtype.val : D₅ → ComplexModel 3)
    let v₃ := (canonicalInvariant 3).inv (X := CMfd.of (n := 3) D₃) P₃ .refl
    let v₅ := (canonicalInvariant 3).inv (X := CMfd.of (n := 3) D₅) P₅ .refl
    ResolutionDriver.maxLocus (Sum.elim v₃ v₅)
      (Sum.inl '' P₃.cosupp ∪ Sum.inr '' P₅.cosupp) =
      {Sum.inr (⟨0,h₅⟩ : D₅)} := by
  intro P₃ P₅ v₃ v₅
  let a : D₃ := ⟨0,h₃⟩
  let b : D₅ := ⟨0,h₅⟩
  have hStrict : v₃ a < v₅ b := by
    change (canonicalInvariant 3).inv (X := CMfd.of (n := 3) D₃) P₃ .refl a <
      (canonicalInvariant 3).inv (X := CMfd.of (n := 3) D₅) P₅ .refl b
    dsimp only [P₃,P₅,a,b]
    rw [physical_polynomial_cusp_original_initial_value 3 (by decide) D₃ h₃,
      physical_polynomial_cusp_original_initial_value 5 (by decide) D₅ h₅]
    exact initialContactValue_strictMono 2 2 (cusp_original_initial_value_lt 3 5 (by decide) (by decide))
  change ResolutionDriver.maxLocus (Sum.elim v₃ v₅)
    (Sum.inl '' P₃.cosupp ∪ Sum.inr '' P₅.cosupp) = {Sum.inr b}
  rw [show P₃.cosupp = {a} from physical_polynomial_cusp_cosupport 3 (by decide) D₃ h₃,
    show P₅.cosupp = {b} from physical_polynomial_cusp_cosupport 5 (by decide) D₅ h₅,
    image_singleton,image_singleton]
  apply Set.ext
  intro z
  simp only [ResolutionDriver.maxLocus,mem_ofPred_eq,mem_union,mem_singleton_iff]
  constructor
  · rintro ⟨rfl | hr,hm⟩
    · exact (not_le_of_gt hStrict (hm (Sum.inr b) (Or.inr rfl))).elim
    · exact hr
  · rintro rfl
    refine ⟨Or.inr rfl,?_⟩
    rintro y (rfl | rfl)
    · exact hStrict.le
    · exact le_rfl

end
end Hironaka.HironakaG8NativeCuspOriginalValue
