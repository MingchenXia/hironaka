import Hironaka.Resolution.HironakaG8MarkTwoNormalOriginalValue
import Hironaka.Resolution.HironakaSmoothSubmersionOrder

/-! Intrinsic maximal-order and nonspecial geometry of the literal
degree-two normal padding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace Filter
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8MarkTwoNormalGeometry
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HomogenizedIdealAlong StepOneValue StepOneRegime StepOneLowerDomain
  HironakaG8MarkTwoNormalOriginalValue HironakaActualNormalPaddingNativeCompanion
  HironakaActualWeightedNormalAmbientDerivatives HironakaActualWeightedNormalContact
  HironakaActualRelativeNormalGeometry HironakaActualOpenZeroSectionDifferentials
  HironakaActualZeroCoordinateContactSeed HironakaActualWeightedNormalPadding
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualSectionBoundaryGeometry
  HironakaActualCentreJointJets HironakaActualGraphFunctionalIdeal
  HironakaRelativeNormalIdeal RestrictedIdealExtension GermIdealPullbackCalculus
  GermIdealOrder IdealOrderArithmetic IdealWeightPowers OrderTaylor DerivativeIdeal
  BlowupDerivativeIdeal InvertibleIdealQuotient RelativePrincipalizationSpan
  CodimOneSupportAlong AnalyticIrreducibleComponents NormalCrossings RegularPointDimension
  OrderMultiplicativity TangentDirectionAlong BoundaryCount

variable {n : ℕ} {U : Opens (ComplexModel n)}

private abbrev padCoordIdeal (U : Opens (ComplexModel n)) :=
  finiteFunctionIdeal (n := n+1) (fun _ : Unit => fun z : productOpen U => relativeNormalCoordinate U z ^ 2)

private theorem coordIdeal_coherent (U : Opens (ComplexModel n)) : (padCoordIdeal U).IsCoherent :=
  isCoherent_finiteFunctionIdeal _ (fun _ => (normalCoordinate_mdifferentiable U).pow _)

private theorem normalSet_eq :
    {z : productOpen U | relativeNormalCoordinate U z = 0} = liftedCarrier (univ : Set U) := by
  ext z
  simp only [mem_ofPred_eq,relativeNormalCoordinate,addedCoordinate,graphFunction,zeroFunction,
    Function.comp_apply,liftedCarrier,mem_univ,true_and]
  rw [show WithLp.ofLp (0 : ComplexModel 1) 0 = 0 from rfl, sub_zero]
  change actualJointNormalProjection n 1 z.val 0 = 0 ↔ actualJointNormalProjection n 1 z.val = 0
  constructor
  · intro h
    ext j
    have hj := Subsingleton.elim j (0 : Fin 1)
    subst j
    exact h
  · intro h
    rw [h]
    rfl

private theorem coord_square_cosupport (U : Opens (ComplexModel n)) :
    cosupport (n+1) univ (padCoordIdeal U) 2 = liftedCarrier (univ : Set U) := by
  rw [← normalSet_eq]
  ext z
  have hHol := holomorphicAt_of_mdifferentiableOn isOpen_univ
    (normalCoordinate_mdifferentiable U).mdifferentiableOn (mem_univ z)
  rw [mem_cosupport_finiteFunctionIdeal_iff _ _ _ (fun _ => holomorphicAt_pow hHol _)]
  change (∀ _ : Unit, VanishesToOrderOn (n+1) univ z 2
    (fun y => relativeNormalCoordinate U y ^ 2)) ↔ relativeNormalCoordinate U z = 0
  constructor
  · intro h
    have hz := (vanishesToOrderOn_one_iff (mem_univ z) (holomorphicAt_pow hHol 2)).mp
      ((h ()).mono (by decide))
    by_contra hn
    exact (pow_ne_zero 2 hn) hz
  · intro hz _
    have h1 : (pointIdeal (n+1) z).mem z (relativeNormalCoordinate U) :=
      ⟨hHol,Eventually.of_forall fun y hy => (mem_singleton_iff.mp hy).symm ▸ hz⟩
    exact ⟨_,pow_mem_idealPow h1 hHol 2,
      Eventually.of_forall fun _ _ => rfl⟩

/-- Exact whole padded cosupport is the lift of the actual base cosupport. -/
theorem mark_two_normal_cosupport (Q : MarkedIdeal n U)
    (hQ : IsInvDomain n Q) (hN : Q.N = univ) (hMark : Q.d = 2) :
    (normalMarked Q).cosupp = liftedCarrier Q.cosupp := by
  let I := GermIdeal.pullback (m := n+1) (projection U) Q.ideal
  have hI := isCoherent_pullback (projection_contMDiff U) hQ.isWellFormed.isCoherent
  change cosupport (n+1) univ (normalPaddingIdeal Q.ideal Q.d) Q.d = _
  rw [hMark]
  change cosupport (n+1) univ (sumIdeal I (padCoordIdeal U)) 2 = _
  rw [cosupport_sumIdeal (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg)
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (coordIdeal_coherent U) hg)]
  rw [HironakaSmoothSubmersionOrder.cosupport_pullback_eq
    (projection_isSubmersion (U := U)) hQ.isWellFormed.isCoherent,coord_square_cosupport]
  ext z
  change (projection U z ∈ cosupport n univ Q.ideal 2 ∧
    (projection U z ∈ univ ∧ actualJointNormalProjection n 1 z.val = 0)) ↔
    projection U z ∈ cosupport n Q.N Q.ideal Q.d ∧ actualJointNormalProjection n 1 z.val = 0
  simp [hN,hMark]

private theorem coordinate_mdifferentiable (n : ℕ) :
    MDifferentiable 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ℂ) (addedCoordinate n) := by
  intro x
  have h := (zero_coordinate_tangent (univ : Set (ComplexModel n))).mem x (mem_univ x)
  exact h.1.self_of_nhds

/-- The added normal square forces maximal order on the full ambient carrier. -/
theorem mark_two_normal_maximal_order (Q : MarkedIdeal n U)
    (hQ : IsInvDomain n Q) (hN : Q.N = univ) (hMark : Q.d = 2) :
    IsMaximalOrderAlong (normalMarked Q).N (normalMarked Q).ideal (normalMarked Q).d := by
  let J := (normalMarked Q : MarkedIdeal (n+1) (ambient (U := U)))
  have hJ : IsInvDomain (n+1) J := normalMarked_original_domain Q hQ hN
  have hHol : ∀ x g, J.ideal.mem x g → HolomorphicAt (n+1) g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ.isWellFormed.isCoherent hg
  intro z hz
  change z ∈ cosupport (n+1) univ J.ideal (Q.d+1) at hz
  rw [hMark,show 2+1 = 1+2 from rfl,cosupport_add_eq_cosupport_iterDerivIdeal hHol 2 le_rfl] at hz
  let K := finiteFunctionIdeal (n := n+1)
    (fun _ : Unit => fun z : ComplexModel (n+1) => addedCoordinate n z ^ 2)
  have hK : K.IsCoherent :=
    isCoherent_finiteFunctionIdeal _ (fun _ => (coordinate_mdifferentiable n).pow 2)
  have hInc : (GermIdeal.pullback (m := n+1) (Subtype.val : productOpen U → ComplexModel (n+1)) K).Le J.ideal := by
    have hPb : GermIdeal.pullback (m := n+1) (Subtype.val : productOpen U → ComplexModel (n+1)) K =
        padCoordIdeal U := by
      exact finiteFunctionIdeal_pullback _ (fun _ => (coordinate_mdifferentiable n).pow 2)
        _ contMDiff_subtype_val
    rw [hPb]
    change (padCoordIdeal U).Le (normalPaddingIdeal Q.ideal Q.d)
    rw [hMark]
    exact le_sumIdeal_right (coordIdeal_coherent U)
  have hOne : (iterDerivIdeal K 2).mem z.val (1 : ComplexModel (n+1) → ℂ) := by
    simpa only [K,zero_add,pow_zero,Pi.one_def] using coordinate_power_derivative_member n 0 2 z.val
  have hp : (GermIdeal.pullback (m := n+1) (Subtype.val : productOpen U → ComplexModel (n+1))
      (iterDerivIdeal K 2)).mem z (1 : productOpen U → ℂ) :=
    GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨1,hOne,rfl⟩ (holomorphicAt_const 1))
  rw [HomogenizedEtale.pullback_val_iterDerivIdeal (productOpen U)
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hK hg) 2] at hp
  have hm := iterDerivIdeal_mono hInc 2 z _ hp
  exact one_ne_zero ((vanishesToOrderOn_one_iff (mem_univ z) (holomorphicAt_const 1)).mp
    (hz.2 _ hm))


open HironakaActualSectionInitialValues ResolutionInvariantDriver CanonicalCentres

/-- The actual normal trace is nonspecial: a codimension-one special locus
would make the original base cosupport contain an open neighbourhood. -/
theorem mark_two_normal_not_special (Q : MarkedIdeal n U)
    (hQ : IsInvDomain n Q) (hE : Q.E = []) (hN : Q.N = univ) (hMark : Q.d = 2)
    (x : U) (hx : x ∈ Q.cosupp) :
    ¬ IsSpecial (X := ambient (U := U)) (normalMarked Q) .refl (zeroSection U x) := by
  let J := (normalMarked Q : MarkedIdeal (n+1) (ambient (U := U)))
  have hJ := normalMarked_original_domain Q hQ hN
  have hJE : J.E = [] := by change Q.E.map (projection U ⁻¹' ·) = []; rw [hE]; rfl
  rintro (⟨_, hCodim⟩ | ⟨hLevel,_⟩)
  · let K := barMarked (X := ambient (U := U)) J
    rw [geoTransformAlong_refl] at hCodim
    change zeroSection U x ∈ codimOnePartAlong K.N K.ideal K.d at hCodim
    obtain ⟨k,hFull,hPart⟩ := hCodim
    change RegularAtDim (n := n+1) (univ : Set (productOpen U)) (zeroSection U x) (k+1) at hFull
    have hDim := eq_of_regularAtDim hFull (regularAtDim_univ (n := n+1) (zeroSection U x))
    have hk : k = n := by omega
    change RegularAtDim (n := n+1) K.cosupp (zeroSection U x) k at hPart
    have hK : K.cosupp = liftedCarrier Q.cosupp := by
      change (barMarked (X := ambient (U := U)) J).cosupp = _
      rw [cosupp_barMarked (X := ambient (U := U)) J hJ.isWellFormed hJ.one_le_d]
      exact mark_two_normal_cosupport Q hQ hN hMark
    rw [hK,hk] at hPart
    have hb := (regularAtDim_actual_section_iff Q.cosupp x hx n).mp hPart
    have hNb := EmbeddedFromResolution.mem_nhds_of_regularAtDim_self hb
    have hIn := mem_interior_iff_mem_nhds.mpr hNb
    rw [interior_cosupp_eq_empty (M := base (U := U)) hQ] at hIn
    exact hIn
  · have hZero : level (X := ambient (U := U)) J .refl (zeroSection U x) = 0 := by
      have hm : origMembers (X := ambient (U := U)) J .refl = [] := by
        simp [origMembers,hJE]
      rw [level,hm]
      rfl
    change 1 ≤ level (X := ambient (U := U)) J .refl (zeroSection U x) at hLevel
    omega

/-- The literal padded mark-two record has a complete original initial
formula with every contact-domain and regime obligation discharged. -/
theorem mark_two_normal_original_initial_value_full (hn : 0 < n)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q) (hE : Q.E = [])
    (hN : Q.N = univ) (hMark : Q.d = 2) (x : U) (hx : x ∈ Q.cosupp) :
    (canonicalInvariant (n+1)).inv (X := ambient (U := U)) (normalMarked Q) .refl (zeroSection U x) =
      HironakaG8InitialExactContactValue.initialContactValue n 2
        ((canonicalInvariant n).inv (X := base (U := U)) Q .refl x) := by
  apply mark_two_normal_original_initial_value hn Q hQ hE hN hMark x hx
    (mark_two_normal_maximal_order Q hQ hN hMark) _
    (mark_two_normal_not_special Q hQ hE hN hMark x hx)
  rw [mark_two_normal_cosupport Q hQ hN hMark]
  refine ⟨?_,?_⟩
  · have hProj : projection U (zeroSection U x) = x :=
      Subtype.ext (tangentProjection_tangentInclusion n 1 x.val)
    rwa [hProj]
  · ext j
    exact tangentInclusion_normal n 1 x.val j

end
end Hironaka.HironakaG8MarkTwoNormalGeometry
